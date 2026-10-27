module

public import CFSG.LocalAnalysis.RankFourTheoremC.PPointP.Exclusion
public import CFSG.LocalAnalysis.RankFourTheoremC.PPointP.ExcLines
public import CFSG.LocalAnalysis.RankFourTheoremC.PPointP.ExcBurnside
import CFSG.GroupTheory.ElemAbelianClosure

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PPointP

open CFSG.Open CFSG.LocalAnalysis.RankFourTheoremC Subgroup

namespace ExcEndgame

variable {G : Type} [Group G] {p : ℕ}

theorem elemAbelian_comm {E : Subgroup G} (h : IsElemAbelian p E) {a b : G} (ha : a ∈ E)
    (hb : b ∈ E) : a * b = b * a := CFSG.Open.IsElemAbelian.comm h ha hb

theorem elemAbelian_mono {B E : Subgroup G} (hBE : B ≤ E) (h : IsElemAbelian p E) :
    IsElemAbelian p B := CFSG.Open.IsElemAbelian.mono h hBE

theorem elemAbelian_closure {S : Set G} (hc : ∀ x ∈ S, ∀ y ∈ S, Commute x y)
    (hp : ∀ x ∈ S, x ^ p = 1) : IsElemAbelian p (Subgroup.closure S) := by
  have hcomm : IsMulCommutative (Subgroup.closure S) :=
    Subgroup.isMulCommutative_closure fun x hx y hy _ => hc x hx y hy
  refine ⟨hcomm, fun x hx => ?_⟩
  induction hx using Subgroup.closure_induction with
  | mem x hx => exact hp x hx
  | one => exact one_pow p
  | mul x y hx hy ihx ihy =>
    have hxy : Commute x y := by
      have := hcomm.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩
      exact congrArg Subtype.val this
    rw [hxy.mul_pow, ihx, ihy, one_mul]
  | inv x hx ihx => rw [inv_pow, ihx, inv_one]

variable [Finite G]

theorem mem_normalizer_of_conj_mem {D : Subgroup G} {g : G}
    (h : ∀ d ∈ D, g * d * g⁻¹ ∈ D) : g ∈ normalizer (D : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro d
  refine ⟨fun hd => h d hd, fun hd => ?_⟩
  have hf : Function.Injective (fun e : D => (⟨g * e * g⁻¹, h e e.2⟩ : D)) := fun a b hab => by
    apply Subtype.ext
    have := congrArg Subtype.val hab
    simpa using this
  obtain ⟨e, he⟩ := Finite.injective_iff_surjective.mp hf ⟨g * d * g⁻¹, hd⟩
  have h1 : g * (e : G) * g⁻¹ = g * d * g⁻¹ := congrArg Subtype.val he
  have h2 : (e : G) = d := by simpa using h1
  rw [← h2]
  exact e.2

theorem exists_mem_normalizer_not_mem [Fact p.Prime] {P H : Subgroup G}
    (hP : IsPGroup p P) (hHP : H ≤ P) (hne : H ≠ P) :
    ∃ w ∈ P, w ∈ normalizer (H : Set G) ∧ w ∉ H := by
  have : Group.IsNilpotent P := hP.isNilpotent
  have hlt : H.subgroupOf P < ⊤ := by
    refine lt_top_iff_ne_top.mpr fun h => hne ?_
    exact le_antisymm hHP (Subgroup.subgroupOf_eq_top.mp h)
  have h := Group.normalizerCondition_of_isNilpotent (H.subgroupOf P) hlt
  obtain ⟨_, w, hw, hwn⟩ := (IsConcreteLE.lt_iff_le_and_exists).mp h
  refine ⟨w, w.2, ?_, hwn⟩
  have h1 : w ∈ (normalizer (H : Set G)).subgroupOf P := by
    rw [Subgroup.subgroupOf_normalizer_eq hHP]
    exact hw
  exact h1

theorem card_fix_ge {N E : Type} [Group N] [Finite N] [Group E] [Finite E] [Fact p.Prime]
    (hN : IsPGroup p N) (hE : Nat.card E = p ^ 3) (φ : N →* MulAut E) (g : N) :
    p ≤ Nat.card {e : E // φ g e = e} := by
  let _ : MulAction N E := MulAction.compHom E φ
  have hmod := hN.card_modEq_card_fixedPoints E
  have hdvd : p ∣ Nat.card (MulAction.fixedPoints N E) := by
    have h1 : p ∣ Nat.card E := by rw [hE]; exact dvd_pow_self p (by norm_num)
    exact (Nat.modEq_zero_iff_dvd.mp (hmod.symm.trans (Nat.modEq_zero_iff_dvd.mpr h1)))
  have hpos : 0 < Nat.card (MulAction.fixedPoints N E) := by
    have : Nonempty (MulAction.fixedPoints N E) :=
      ⟨⟨1, fun m => by show φ m 1 = 1; exact map_one _⟩⟩
    exact Nat.card_pos
  refine (Nat.le_of_dvd hpos hdvd).trans ?_
  have hsub : MulAction.fixedPoints N E ⊆ {e : E | φ g e = e} := fun e he => he g
  exact Nat.card_mono (Set.toFinite _) hsub

theorem exists_invariant_plane {A : Type} [CommGroup A] [Finite A] [Fact p.Prime]
    (hA : Nat.card A = p ^ 3) (a : MulAut A) {x : A} (hx : orderOf x = p) (hax : a x ≠ x)
    (hα : ∀ c : A, orderOf c = p → a c ∈ zpowers c → a c = c)
    (hfix : p < Nat.card {e : A // a e = e}) :
    ∃ D : Subgroup A, Nat.card D = p ^ 2 ∧ x ∈ D ∧ ∀ d ∈ D, a d ∈ D := by
  have hp : p.Prime := Fact.out
  have hp2 := hp.two_le
  set f : A →* A := a.toMonoidHom / MonoidHom.id A with hf
  have hfe : ∀ e, f e = a e / e := fun e => rfl
  have hker : ∀ e, e ∈ f.ker ↔ a e = e := by
    intro e
    rw [MonoidHom.mem_ker, hfe, div_eq_one]
  have hkcard : Nat.card f.ker = Nat.card {e : A // a e = e} :=
    Nat.card_congr (Equiv.subtypeEquivRight hker)
  have hkr := Subgroup.card_ker_mul_card_range f
  rw [hA, hkcard] at hkr
  have hr_dvd : Nat.card f.range ∣ p ^ 3 := ⟨Nat.card {e : A // a e = e}, by rw [← hkr]; ring⟩
  obtain ⟨i, hi, hri⟩ := (Nat.dvd_prime_pow hp).mp hr_dvd
  have hr_lt : Nat.card f.range < p ^ 2 := by
    by_contra h
    replace h := not_lt.mp h
    have h1 : (p + 1) * p ^ 2 ≤ Nat.card {e : A // a e = e} * Nat.card f.range :=
      Nat.mul_le_mul hfix h
    rw [hkr] at h1
    have : 0 < p ^ 2 := by positivity
    nlinarith
  have hi1 : i ≤ 1 := by
    by_contra h
    replace h := not_le.mp h
    have : p ^ 2 ≤ p ^ i := Nat.pow_le_pow_right hp.pos h
    omega
  set c := f x with hc
  have hc1 : c ≠ 1 := by
    rw [hc, hfe]
    exact fun h => hax (div_eq_one.mp h)
  have hcR : c ∈ f.range := ⟨x, rfl⟩
  have hR : Nat.card f.range = p := by
    interval_cases i
    · exfalso
      rw [pow_zero] at hri
      have := Subgroup.card_eq_one.mp hri
      rw [this] at hcR
      exact hc1 ((Subgroup.mem_bot).mp hcR)
    · rw [hri, pow_one]
  have hco : orderOf c = p := by
    have hd : orderOf c ∣ p := hR ▸ Subgroup.orderOf_dvd_natCard f.range hcR
    rcases (Nat.dvd_prime hp).mp hd with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hc1
    · exact h
  have hzR : zpowers c = f.range :=
    Subgroup.eq_of_le_of_card_ge (zpowers_le.mpr hcR) (by rw [Nat.card_zpowers, hco, hR])
  have hac : a c = c := by
    apply hα c hco
    rw [hzR]
    refine ⟨a x, ?_⟩
    simp [hfe, hc, map_div]
  have hax' : a x = c * x := by
    rw [hc, hfe, div_mul_cancel]
  have hcx : c ∉ zpowers x := by
    intro h
    apply hax
    apply hα x hx
    rw [hax']
    exact mul_mem h (mem_zpowers x)
  refine ⟨zpowers x ⊔ zpowers c, ?_, Subgroup.mem_sup_left (mem_zpowers x), ?_⟩
  · have hle : Nat.card (zpowers x ⊔ zpowers c : Subgroup A) ≤ p * p := by
      have hsurj : Function.Surjective (fun q : zpowers x × zpowers c =>
          (⟨q.1 * q.2, mul_mem (Subgroup.mem_sup_left q.1.2) (Subgroup.mem_sup_right q.2.2)⟩ :
            (zpowers x ⊔ zpowers c : Subgroup A))) := by
        rintro ⟨d, hd⟩
        obtain ⟨u, hu, v, hv, huv⟩ := Subgroup.mem_sup.mp hd
        exact ⟨(⟨u, hu⟩, ⟨v, hv⟩), Subtype.ext huv⟩
      have := Nat.card_le_card_of_surjective _ hsurj
      rwa [Nat.card_prod, Nat.card_zpowers, Nat.card_zpowers, hx, hco] at this
    have hgt : p < Nat.card (zpowers x ⊔ zpowers c : Subgroup A) := by
      by_contra h
      replace h := not_lt.mp h
      have heq : zpowers x = zpowers x ⊔ zpowers c :=
        Subgroup.eq_of_le_of_card_ge le_sup_left (by rw [Nat.card_zpowers, hx]; exact h)
      exact hcx (heq ▸ Subgroup.mem_sup_right (mem_zpowers c))
    have hdvd : Nat.card (zpowers x ⊔ zpowers c : Subgroup A) ∣ p ^ 3 :=
      hA ▸ Subgroup.card_subgroup_dvd_card _
    obtain ⟨j, hj, hjd⟩ := (Nat.dvd_prime_pow hp).mp hdvd
    rw [hjd] at hle hgt ⊢
    interval_cases j
    · simp at hgt; omega
    · simp at hgt
    · rfl
    · nlinarith
  · have hmap : (zpowers x ⊔ zpowers c).map a.toMonoidHom ≤ zpowers x ⊔ zpowers c := by
      rw [Subgroup.map_sup, MonoidHom.map_zpowers, MonoidHom.map_zpowers]
      refine sup_le (zpowers_le.mpr ?_) (zpowers_le.mpr ?_)
      · show a x ∈ _
        rw [hax']
        exact mul_mem (Subgroup.mem_sup_right (mem_zpowers c))
          (Subgroup.mem_sup_left (mem_zpowers x))
      · show a c ∈ _
        rw [hac]
        exact Subgroup.mem_sup_right (mem_zpowers c)
    exact fun d hd => hmap (Subgroup.mem_map_of_mem _ hd)

end ExcEndgame

open ExcEndgame

theorem pGroupEndgame : PGroupEndgame := by
  intro G _ _ p _ P hP x y0 hx hxP hy0Q hy0c hy0o hy0x hA hQ3 hL33
  obtain ⟨A, hAP, hAe, hAc⟩ := hA
  have hp : p.Prime := Fact.out
  set Q : Subgroup G := P ⊓ centralizer ({x} : Set G) with hQ
  set E : Subgroup G := omegaCenter p Q with hE
  have hxQ : x ∈ Q := ⟨hxP, mem_centralizer_singleton_iff.2 rfl⟩
  have hxp : x ^ p = 1 := by rw [← hx]; exact pow_orderOf_eq_one x
  have hxE : x ∈ E := ⟨hxQ, fun q hq => mem_centralizer_singleton_iff.1 hq.2, hxp⟩
  have hy0E : y0 ∈ E := ⟨hy0Q, hy0c, by rw [← hy0o]; exact pow_orderOf_eq_one y0⟩
  have hEe : IsElemAbelian p E := isElemAbelian_omegaCenter p Q
  have hEQ : E ≤ Q := omegaCenter_le p Q
  have hQP : Q ≤ P := inf_le_left
  have hEP : IsPGroup p E := hP.to_le (hEQ.trans hQP)
  have hnoplane : ∀ D : Subgroup G, D ≤ Q → IsElemAbelian p D → Nat.card D = p ^ 2 → x ∈ D →
      ∀ y ∈ P, (∀ i : ℕ, y ^ i ∈ normalizer (D : Set G)) → y * x ≠ x * y → False :=
    fun D hDQ hDe hDc hxD y hyP hyD hyx =>
      hL33 D hDQ hDe hDc (exists_lines_of_invariant_plane hx hxD hyD
        (hP.to_le (zpowers_le.2 hyP)) hyx)
  have hcentQ : ∀ g ∈ P, g * x = x * g → g ∈ Q := fun g hg hgx =>
    ⟨hg, mem_centralizer_singleton_iff.2 hgx⟩
  obtain ⟨k, hk⟩ := hEP.exists_card_eq
  have hEle : Nat.card E ≤ p ^ 3 := hQ3 E hEQ hEe
  have hk2 : 2 ≤ k := by
    by_contra hk2
    have hzx : zpowers x ≤ E := zpowers_le.2 hxE
    have hpE : p ∣ Nat.card E := by
      have := Subgroup.card_dvd_of_le hzx
      rwa [Nat.card_zpowers, hx] at this
    rcases (by omega : k = 0 ∨ k = 1) with rfl | rfl
    · rw [hk, pow_zero] at hpE
      exact hp.one_lt.ne' (Nat.dvd_one.1 hpE)
    · have heq : zpowers x = E :=
        Subgroup.eq_of_le_of_card_ge hzx (by rw [hk, Nat.card_zpowers, hx, pow_one])
      exact hy0x (heq ▸ hy0E)
  have hk3 : k ≤ 3 := by
    by_contra hk3
    rw [hk] at hEle
    exact absurd hEle (not_le.2 (Nat.pow_lt_pow_right hp.one_lt (by omega)))
  have hQne : Q ≠ P := by
    intro h
    have := hQ3 A (h ▸ hAP) hAe
    rw [hAc] at this
    exact absurd this (not_le.2 (Nat.pow_lt_pow_right hp.one_lt (by norm_num)))
  obtain ⟨y, hyP, hyN, hyQ⟩ := exists_mem_normalizer_not_mem hP hQP hQne
  have hyx : y * x ≠ x * y := fun h => hyQ (hcentQ y hyP h)
  have hyE : y ∈ normalizer (E : Set G) := mem_normalizer_omegaCenter hyN
  rcases (by omega : k = 2 ∨ k = 3) with rfl | rfl
  ·
    exact hnoplane E hEQ hEe hk hxE y hyP (fun i => pow_mem hyE i) hyx
  ·
    set N1 : Subgroup G := P ⊓ normalizer (E : Set G) with hN1
    have hN1P : N1 ≤ P := inf_le_left
    have hN1p : IsPGroup p N1 := hP.to_le hN1P
    have hQN1 : Q ≤ N1 := by
      intro q hq
      refine ⟨hq.1, mem_normalizer_of_conj_mem fun e he => ?_⟩
      rw [he.2.1 q hq, mul_inv_cancel_right]
      exact he
    have hEN1 : E ≤ N1 := hEQ.trans hQN1
    let _ : CommGroup E := { (inferInstance : Group E) with
      mul_comm := fun a b => hEe.1.is_comm.comm a b }
    let φ : N1 →* MulAut E :=
      E.normalizerMonoidHom.comp (Subgroup.inclusion (inf_le_right : N1 ≤ _))
    have hφ : ∀ (g : N1) (e : E), ((φ g e : E) : G) = (g : G) * (e : G) * (g : G)⁻¹ :=
      fun g e => by
      simp [φ, Subgroup.normalizerMonoidHom_apply_apply_coe]
    have hEcard : Nat.card E = p ^ 3 := hk
    have hφ1 : ∀ g : N1, φ g ≠ 1 → (g : G) * x ≠ x * g := by
      intro g hg hgx
      apply hg
      ext e
      rw [hφ, MulAut.one_apply]
      have hgQ : (g : G) ∈ Q := hcentQ g (hN1P g.2) hgx
      rw [e.2.2.1 g hgQ, mul_inv_cancel_right]
    have hfix : ∀ g : N1, φ g ≠ 1 → Nat.card {e : E // φ g e = e} = p := by
      intro g hg
      have hgx := hφ1 g hg
      refine le_antisymm ?_ (card_fix_ge hN1p hEcard φ g)
      by_contra hlt
      replace hlt := not_le.1 hlt
      have hgp : IsPGroup p (zpowers (g : G)) := hP.to_le (zpowers_le.2 (hN1P g.2))
      have hxo : orderOf (⟨x, hxE⟩ : E) = p := by rw [Subgroup.orderOf_mk, hx]
      have hax : φ g ⟨x, hxE⟩ ≠ ⟨x, hxE⟩ := fun h => hgx (by
        have h' : (g : G) * x * (g : G)⁻¹ = x := by
          have := congrArg Subtype.val h
          rw [hφ] at this
          exact this
        calc (g : G) * x = ((g : G) * x * (g : G)⁻¹) * g := by group
          _ = x * g := by rw [h'])
      have hα : ∀ c : E, orderOf c = p → φ g c ∈ zpowers c → φ g c = c := by
        intro c hc hcz
        have hc' : orderOf (c : G) = p := by rw [Subgroup.orderOf_coe, hc]
        have hcz' : (g : G) * c * (g : G)⁻¹ ∈ zpowers (c : G) := by
          rw [← hφ]
          obtain ⟨n, hn⟩ := hcz
          exact ⟨n, by rw [← hn]; simp⟩
        have hcomm := commute_of_normalizes_prime_order hgp hc' hcz'
        apply Subtype.ext
        rw [hφ, hcomm, mul_inv_cancel_right]
      obtain ⟨D, hDc, hxD, hDinv⟩ := exists_invariant_plane hEcard (φ g) hxo hax hα hlt
      refine hnoplane (D.map E.subtype) ((Subgroup.map_subtype_le D).trans hEQ) ?_ ?_
        ⟨⟨x, hxE⟩, hxD, rfl⟩ g (hN1P g.2) (fun i => ?_) hgx
      · exact elemAbelian_mono (Subgroup.map_subtype_le D) hEe
      · rw [Subgroup.card_map_of_injective E.subtype_injective, hDc]
      · refine pow_mem (mem_normalizer_of_conj_mem fun d hd => ?_) i
        obtain ⟨d', hd', rfl⟩ := hd
        refine ⟨φ g d', hDinv d' hd', ?_⟩
        simp [hφ]
    have hker : Nat.card φ.ker = Nat.card Q := by
      have hkerQ : φ.ker = Q.subgroupOf N1 := by
        ext g
        rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
        constructor
        · intro hg
          apply hcentQ g (hN1P g.2)
          have h1 := congrArg (fun σ : MulAut E => ((σ ⟨x, hxE⟩ : E) : G)) hg
          have h2 : (g : G) * x * (g : G)⁻¹ = x := by
            simp only [hφ, MulAut.one_apply] at h1
            exact h1
          calc (g : G) * x = ((g : G) * x * (g : G)⁻¹) * g := by group
            _ = x * g := by rw [h2]
        · intro hgQ
          ext e
          rw [hφ, MulAut.one_apply, e.2.2.1 g hgQ, mul_inv_cancel_right]
      rw [hkerQ]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQN1).toEquiv
    have hN1Q : Nat.card N1 ≤ p * Nat.card Q :=
      (card_le_prime_mul_ker hN1p hEcard φ hfix).trans_eq (by rw [hker])
    have hS : ∀ B : Subgroup G, B ≤ Q → IsElemAbelian p B → B ≤ E := by
      intro B hBQ hBe
      have hcl : IsElemAbelian p (Subgroup.closure ((B : Set G) ∪ E)) := by
        refine elemAbelian_closure (fun u hu v hv => ?_) fun u hu => ?_
        · rcases hu with hu | hu <;> rcases hv with hv | hv
          · exact elemAbelian_comm hBe hu hv
          · exact hv.2.1 u (hBQ hu)
          · exact (hu.2.1 v (hBQ hv)).symm
          · exact elemAbelian_comm hEe hu hv
        · rcases hu with hu | hu
          · exact hBe.2 u hu
          · exact hEe.2 u hu
      have hclQ : Subgroup.closure ((B : Set G) ∪ E) ≤ Q :=
        (Subgroup.closure_le _).2 (Set.union_subset hBQ hEQ)
      have hEcl : E ≤ Subgroup.closure ((B : Set G) ∪ E) :=
        fun e he => Subgroup.subset_closure (Or.inr he)
      have heq : E = Subgroup.closure ((B : Set G) ∪ E) :=
        Subgroup.eq_of_le_of_card_ge hEcl (by rw [hEcard]; exact hQ3 _ hclQ hcl)
      exact fun b hb => heq ▸ Subgroup.subset_closure (Or.inl hb)
    have hU : ∀ A' : Subgroup G, A' ≤ N1 → IsElemAbelian p A' → p ^ 3 ≤ Nat.card A' →
        A' ≤ Q := by
      intro A' hA'N hA'e hA'c
      by_contra hA'Q
      obtain ⟨g, hgA, hgQ⟩ := Set.not_subset.1 hA'Q
      set g' : N1 := ⟨g, hA'N hgA⟩ with hg'
      have hg1 : φ g' ≠ 1 := by
        intro h
        apply hgQ
        apply hcentQ g (hN1P (hA'N hgA))
        have := congrArg (fun σ : MulAut E => ((σ ⟨x, hxE⟩ : E) : G)) h
        have h2 : g * x * g⁻¹ = x := by
          simp only [hφ, MulAut.one_apply] at this
          exact this
        calc g * x = (g * x * g⁻¹) * g := by group
          _ = x * g := by rw [h2]
      have hAQE : A' ⊓ Q ≤ E := hS _ inf_le_right (elemAbelian_mono inf_le_left hA'e)
      have hcardAQ : Nat.card (A' ⊓ Q : Subgroup G) ≤ p := by
        rw [← hfix g' hg1]
        refine Nat.card_le_card_of_injective (fun a => ⟨⟨a, hAQE a.2⟩, ?_⟩) fun a b h => ?_
        · apply Subtype.ext
          rw [hφ]
          show g * a * g⁻¹ = a
          rw [elemAbelian_comm hA'e hgA a.2.1, mul_inv_cancel_right]
        · exact Subtype.ext (congrArg (fun z : {e : E // φ g' e = e} => ((z.1 : E) : G)) h)
      have hrel : Q.relIndex A' ≤ Q.relIndex N1 :=
        Subgroup.relIndex_le_of_le_right hA'N (by
          have := Subgroup.relIndex_mul_card Q N1
          intro h0
          rw [h0, zero_mul] at this
          exact Nat.card_pos.ne' this.symm)
      have h1 := Subgroup.relIndex_mul_card Q A'
      have h2 := Subgroup.relIndex_mul_card Q N1
      rw [inf_eq_left.2 hQN1] at h2
      have hQpos : 0 < Nat.card Q := Nat.card_pos
      have hrelN : Q.relIndex N1 ≤ p := by
        by_contra h
        replace h := not_le.1 h
        have : p * Nat.card Q < Q.relIndex N1 * Nat.card Q := Nat.mul_lt_mul_of_pos_right h hQpos
        omega
      have hA'le : Nat.card A' ≤ p * p := by
        rw [← h1, inf_comm]
        exact Nat.mul_le_mul (hrel.trans hrelN) hcardAQ
      have : p * p < p ^ 3 := by
        rw [← sq]
        exact Nat.pow_lt_pow_right hp.one_lt (by norm_num)
      omega
    have hN1eq : N1 = P := by
      by_contra hne
      obtain ⟨z, hzP, hzN, hzN1⟩ := exists_mem_normalizer_not_mem hP hN1P hne
      apply hzN1
      refine ⟨hzP, mem_normalizer_of_conj_mem fun e he => ?_⟩
      set E' : Subgroup G := E.map (MulAut.conj z).toMonoidHom with hE'
      have hE'N1 : E' ≤ N1 := by
        rintro _ ⟨e', he', rfl⟩
        exact (Subgroup.mem_normalizer_iff.mp hzN e').mp (hEN1 he')
      have hE'e : IsElemAbelian p E' :=
        CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_map p hEe _
      have hE'c : Nat.card E' = p ^ 3 := by
        rw [hE', Subgroup.card_map_of_injective (MulAut.conj z).injective, hEcard]
      have hE'E : E' ≤ E := hS E' (hU E' hE'N1 hE'e hE'c.ge) hE'e
      exact hE'E ⟨e, he, rfl⟩
    have hAQ : A ≤ Q := hU A (hN1eq ▸ hAP) hAe (by
      rw [hAc]
      exact Nat.pow_le_pow_right hp.pos (by norm_num))
    have := hQ3 A hAQ hAe
    rw [hAc] at this
    exact absurd this (not_le.2 (Nat.pow_lt_pow_right hp.one_lt (by norm_num)))

theorem pPointExclusionFive_of_kFacts' (h243 : GL83ComponentPCoreTrivial)
    (h244 : GL83NongenerationList) (hsig : GL83SignalizerAut) (hKR : KFactExcludedRank)
    (hKI : KFactExcludedInner) : PPointExclusionFive :=
  pPointExclusionFive_of_kFacts h243 h244 hsig hKR hKI pGroupEndgame

end CFSG.LocalAnalysis.RankFourTheoremC.PPointP
