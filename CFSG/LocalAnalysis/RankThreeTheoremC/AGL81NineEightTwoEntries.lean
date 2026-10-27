module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81NineEightTwoProof
public import CFSG.LocalAnalysis.GLTheoremB.UniqInputs
import CFSG.HardMathSupport.Solomon.Coordinator.I271HoldsAltDiv
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.CaseTwoNoTwo
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.CaseTwoSylow
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81RankOneSylow
import CFSG.Quasithin.H13.A7BlkAct
import CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I542.S6Aut
import CFSG.Adapters.LinearCatalogStated
import CFSG.LargeExtraspecial.Bender
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2RootSylowUnique

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111

open CFSG.Open CFSG.AGLEmbedding Equiv Equiv.Perm

@[expose] def KFactNineThreeNoTwoAt (p : ℕ) (i : TauCeti.CFSGIndex) : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (K : Subgroup X), K.Normal → Nonempty (K ≃* i.Group) →
    ¬ (p = 3 ∧ IsLinThreeFour K) → ∀ T : Sylow p K, ∀ S : Subgroup X, IsPGroup 2 S →
      (T : Subgroup K).map K.subtype ≤ Subgroup.normalizer (S : Set X) →
      S ≤ Subgroup.centralizer (K : Set X)

theorem kFactNineThreeNoTwo_of_at
    (h : ∀ p, p.Prime → p ≠ 2 → ∀ i, IsNineThreeIndex p i → KFactNineThreeNoTwoAt p i) :
    KFactNineThreeNoTwo :=
  fun p X _ _ K hK hp hp2 ⟨i, hi, hiso⟩ hL34 T S hS hTS =>
    h p hp hp2 i hi X K hK hiso hL34 T S hS hTS

theorem kFactNineThreeNoTwoAt_caseTwo
    {p : ℕ} {d : TauCeti.ValidLieTypeIndex} (hd : IsCaseTwoIndex p d) :
    KFactNineThreeNoTwoAt p (.lie d) := by
  intro X _ _ K hK ⟨e⟩ _ T S hS hTS
  have hKc : IsCaseTwoGroup p K := ⟨d, hd, ⟨e⟩⟩
  have hp : p.Prime := by
    rcases RankOneSylow.eq_three_or_five_of_isCaseTwoGroup hKc with rfl | rfl
    · exact Nat.prime_three
    · exact Nat.prime_five
  haveI : Fact p.Prime := ⟨hp⟩
  have hdvd : p ∣ Nat.card T := by
    have hle := kFactCaseTwoSylow p K hKc T
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp T.isPGroup'
    rw [hk] at hle ⊢
    rcases k with _ | k
    · simp at hle
      have := hp.two_le
      nlinarith
    · exact dvd_pow_self p (Nat.succ_ne_zero k)
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' (G := T) p hdvd
  refine le_centralizer_of_noTwo_of_normal kFactCaseTwoNoTwo hKc hS (t := ((t : K) : X)) (t : K).2
    ?_ (hTS ⟨t, t.2, rfl⟩)
  rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, ht]

section Sylow

variable {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]

theorem exists_isSCp_le_sylow (P : Sylow p G) :
    ∃ A : Subgroup G, A ≤ (P : Subgroup G) ∧ CFSG.LocalAnalysis.GLTheoremB.IsSCp p ⊤ A := by
  classical
  obtain ⟨E, hE, hmax⟩ : ∃ E : Subgroup G, IsElemAbelian p E ∧
      ∀ F : Subgroup G, IsElemAbelian p F → Nat.card F ≤ Nat.card E := by
    obtain ⟨E, hE, hEmax⟩ := Set.exists_max_image {E : Subgroup G | IsElemAbelian p E}
      (fun E : Subgroup G => Nat.card E) (Set.toFinite _) ⟨⊥, isElemAbelian_bot p⟩
    exact ⟨E, hE, fun F hF => hEmax F hF⟩
  obtain ⟨Q, hEQ⟩ := hE.isPGroup.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G Q P
  refine ⟨E.map (MulAut.conj g).toMonoidHom, ?_, le_top, hE.map _, fun F _ hF hle => ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    rw [← hg, Sylow.coe_subgroup_smul]
    exact Subgroup.smul_mem_pointwise_smul x (MulAut.conj g) (Q : Subgroup G) (hEQ hx)
  · have hcard : Nat.card (E.map (MulAut.conj g).toMonoidHom) = Nat.card E :=
      Subgroup.card_map_of_injective (MulAut.conj g).injective
    exact (Subgroup.eq_of_le_of_card_ge hle (by rw [hcard]; exact hmax F hF)).symm

end Sylow

theorem le_centralizer_of_alt {X : Type} [Group X] [Finite X] {K : Subgroup X} [K.Normal]
    {n p : ℕ} [Fact p.Prime] (hn : 5 ≤ n) (hn6 : n ≠ 6) (hp2 : p ≠ 2) (hpn : p ∣ n)
    (e : K ≃* alternatingGroup (Fin n)) (T : Sylow p K) {S : Subgroup X} (hS : IsPGroup 2 S)
    (hTS : (T : Subgroup K).map K.subtype ≤ Subgroup.normalizer (S : Set X)) :
    S ≤ Subgroup.centralizer (K : Set X) := by
  classical
  set β := CFSG.Quasithin.H13.A7Blk.permAutEquiv hn hn6
  let ψ : X →* Perm (Fin n) :=
    β.symm.toMonoidHom.comp ((MulAut.congr e).toMonoidHom.comp (MulAut.conjNormal (H := K)))
  have hψK : ∀ k : K, ψ k = ((e k : alternatingGroup (Fin n)) : Perm (Fin n)) := by
    intro k
    change β.symm ((MulAut.congr e) (MulAut.conjNormal (H := K) (k : X))) = _
    rw [MulEquiv.symm_apply_eq]
    refine MulEquiv.ext fun a => Subtype.ext ?_
    rw [CFSG.Quasithin.H13.A7Blk.coe_permAutEquiv_apply]
    change ((e ((MulAut.conjNormal (H := K) (k : X)) (e.symm a)) : alternatingGroup (Fin n)) :
      Perm (Fin n)) = _
    rw [MulAut.conjNormal_val, MulAut.conj_apply, map_mul, map_mul, map_inv,
      MulEquiv.apply_symm_apply]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  have hψ1 : ∀ x : X, ψ x = 1 → x ∈ Subgroup.centralizer (K : Set X) := by
    intro x hx
    have h1 : MulAut.conjNormal (H := K) x = 1 := by
      have h2 : (MulAut.congr e) (MulAut.conjNormal (H := K) x) = 1 := by
        have h3 := congrArg β hx
        simpa [ψ] using h3
      exact (MulAut.congr e).injective (h2.trans (map_one _).symm)
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    have h4 := congrArg (fun f : MulAut K => ((f ⟨k, hk⟩ : K) : X)) h1
    simp only [MulAut.conjNormal_apply, MulAut.one_apply] at h4
    calc k * x = (x * k * x⁻¹) * x := by rw [h4]
      _ = x * k := by group
  set W : Subgroup (Perm (Fin n)) := S.map ψ with hW
  have hWcop : Nat.Coprime p (Nat.card W) := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp (hS.map ψ)
    rw [hk]
    exact ((Nat.coprime_primes Fact.out Nat.prime_two).mpr hp2).pow_right k
  set A : Subgroup (Perm (Fin n)) := (T : Subgroup K).map (ψ.comp K.subtype) with hA
  have hAW : A ≤ Subgroup.normalizer (W : Set (Perm (Fin n))) := by
    rintro _ ⟨t, ht, rfl⟩
    have htn := hTS ⟨t, ht, rfl⟩
    rw [Subgroup.mem_normalizer_iff] at htn ⊢
    intro w
    constructor
    · rintro ⟨s, hs, rfl⟩
      refine ⟨(t : X) * s * (t : X)⁻¹, (htn s).mp hs, ?_⟩
      simp
    · rintro ⟨s, hs, hse⟩
      refine ⟨(t : X)⁻¹ * s * (t : X), ?_, ?_⟩
      · have := (htn ((t : X)⁻¹ * s * (t : X))).mpr (by simpa [mul_assoc] using hs)
        exact this
      · have hw : w = (ψ (t : X))⁻¹ * ψ s * ψ (t : X) := by
          rw [hse]
          simp only [MonoidHom.coe_comp, Subgroup.coe_subtype, Function.comp_apply]
          group
        rw [hw]
        simp
  have hinj : Function.Injective (ψ.comp K.subtype) := by
    intro a b hab
    have h1 : ((e a : alternatingGroup (Fin n)) : Perm (Fin n)) = (e b : Perm (Fin n)) := by
      rw [← hψK, ← hψK]
      exact hab
    exact e.injective (Subtype.ext h1)
  have hn1 : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr (by omega)
  have hAcard : Nat.card A = p ^ (Nat.card (Perm (Fin n))).factorization p := by
    rw [hA, Subgroup.card_map_of_injective hinj, Sylow.card_eq_multiplicity,
      Nat.card_congr e.toEquiv, ← two_mul_nat_card_alternatingGroup,
      Nat.factorization_mul two_ne_zero Nat.card_pos.ne']
    simp [Nat.Prime.factorization Nat.prime_two, Finsupp.single_apply, Ne.symm hp2]
  let AS : Sylow p (Perm (Fin n)) := Sylow.ofCard A hAcard
  obtain ⟨A', hA'A, hA'⟩ := exists_isSCp_le_sylow AS
  have hWbot : W = ⊥ :=
    CFSG.HardMathSupport.Solomon.Coordinator.i271h_perm_coprime_normalized_eq_bot hA'
      (by simpa using hpn) hWcop (hA'A.trans hAW)
  intro s hs
  apply hψ1
  have : ψ s ∈ W := ⟨s, hs, rfl⟩
  rw [hWbot] at this
  exact this

theorem kFactNineThreeNoTwoAt_alt {p n : ℕ} (hn : 5 ≤ n) (hpn : (p = 3 ∧ n = 9) ∨ (p = 5 ∧ n = 10)) :
    KFactNineThreeNoTwoAt p (.alternating n hn) := by
  intro X _ _ K hK ⟨e⟩ _ T S hS hTS
  have hp : p.Prime := by rcases hpn with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> norm_num
  haveI : Fact p.Prime := ⟨hp⟩
  exact le_centralizer_of_alt hn (by omega) (by omega) (by rcases hpn with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> norm_num) e T hS hTS

theorem factorization_three_perm_six : (Nat.card (Perm (Fin 6))).factorization 3 = 2 := by
  rw [Nat.card_perm, Nat.card_fin, show Nat.factorial 6 = 3 ^ 2 * 80 by decide,
    Nat.factorization_mul (by norm_num) (by norm_num), Nat.Prime.factorization_pow Nat.prime_three,
    Finsupp.add_apply, Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ 3 ∣ 80)]
  simp

theorem le_centralizer_of_alt6 {X : Type} [Group X] [Finite X] {K : Subgroup X} [K.Normal]
    (e : K ≃* alternatingGroup (Fin 6)) (T : Sylow 3 K) {S : Subgroup X} (hS : IsPGroup 2 S)
    (hTS : (T : Subgroup K).map K.subtype ≤ Subgroup.normalizer (S : Set X)) :
    S ≤ Subgroup.centralizer (K : Set X) := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let φ : X →* MulAut (alternatingGroup (Fin 6)) :=
    (MulAut.congr e).toMonoidHom.comp (MulAut.conjNormal (H := K))
  have hφK : ∀ k : K, φ k = MulAut.conj (e k) := by
    intro k
    refine MulEquiv.ext fun a => ?_
    change e ((MulAut.conjNormal (H := K) (k : X)) (e.symm a)) = _
    rw [MulAut.conjNormal_val, MulAut.conj_apply, map_mul, map_mul, map_inv,
      MulEquiv.apply_symm_apply, MulAut.conj_apply]
  have hφ1 : ∀ x : X, φ x = 1 → x ∈ Subgroup.centralizer (K : Set X) := by
    intro x hx
    have h1 : MulAut.conjNormal (H := K) x = 1 :=
      (MulAut.congr e).injective (hx.trans (map_one _).symm)
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    have h4 := congrArg (fun f : MulAut K => ((f ⟨k, hk⟩ : K) : X)) h1
    simp only [MulAut.conjNormal_apply, MulAut.one_apply] at h4
    calc k * x = (x * k * x⁻¹) * x := by rw [h4]
      _ = x * k := by group
  set W : Subgroup (MulAut (alternatingGroup (Fin 6))) := S.map φ with hW
  have hTW : ∀ t ∈ (T : Subgroup K),
      MulAut.conj (e t) ∈ Subgroup.normalizer (W : Set (MulAut (alternatingGroup (Fin 6)))) := by
    intro t ht
    rw [← hφK]
    have htn := hTS ⟨t, ht, rfl⟩
    rw [Subgroup.mem_normalizer_iff] at htn ⊢
    intro w
    constructor
    · rintro ⟨s, hs, rfl⟩
      exact ⟨(t : X) * s * (t : X)⁻¹, (htn s).mp hs, by simp⟩
    · rintro ⟨s, hs, hse⟩
      refine ⟨(t : X)⁻¹ * s * (t : X), (htn ((t : X)⁻¹ * s * (t : X))).mpr
        (by simpa [mul_assoc] using hs), ?_⟩
      have hw : w = (φ (t : X))⁻¹ * φ s * φ (t : X) := by rw [hse]; group
      rw [hw]
      simp
  let cn : Perm (Fin 6) →* MulAut (alternatingGroup (Fin 6)) := MulAut.conjNormal
  have hcn : ∀ a : alternatingGroup (Fin 6), cn (a : Perm (Fin 6)) = MulAut.conj a :=
    fun a => MulAut.conjNormal_val
  set W₀ : Subgroup (Perm (Fin 6)) := W.comap cn with hW₀
  have hW₀cop : Nat.Coprime 3 (Nat.card W₀) := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp ((hS.map φ).comap_of_injective cn
      CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I542.conjNormal_injective_alt6)
    rw [hk]
    exact (Nat.coprime_primes Nat.prime_three Nat.prime_two |>.mpr (by norm_num)).pow_right k
  set A : Subgroup (Perm (Fin 6)) :=
    (T : Subgroup K).map ((alternatingGroup (Fin 6)).subtype.comp e.toMonoidHom) with hA
  have hAW₀ : A ≤ Subgroup.normalizer (W₀ : Set (Perm (Fin 6))) := by
    rintro _ ⟨t, ht, rfl⟩
    have hn := hTW t ht
    rw [Subgroup.mem_normalizer_iff] at hn ⊢
    intro g
    simp only [hW₀, Subgroup.mem_comap, map_mul, map_inv, MonoidHom.coe_comp,
      Subgroup.coe_subtype, Function.comp_apply, MulEquiv.coe_toMonoidHom]
    rw [hcn]
    exact hn (cn g)
  have hinj : Function.Injective ((alternatingGroup (Fin 6)).subtype.comp e.toMonoidHom) :=
    (Subgroup.subtype_injective _).comp e.injective
  have hAcard : Nat.card A = 3 ^ (Nat.card (Perm (Fin 6))).factorization 3 := by
    rw [hA, Subgroup.card_map_of_injective hinj, Sylow.card_eq_multiplicity,
      Nat.card_congr e.toEquiv, factorization_three_perm_six, nat_card_alternatingGroup,
      Nat.card_fin, show Nat.factorial 6 / 2 = 3 ^ 2 * 40 by decide,
      Nat.factorization_mul (by norm_num) (by norm_num), Nat.Prime.factorization_pow Nat.prime_three,
      Finsupp.add_apply, Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ 3 ∣ 40)]
    simp
  obtain ⟨A', hA'A, hA'⟩ := exists_isSCp_le_sylow (Sylow.ofCard A hAcard)
  have hW₀bot : W₀ = ⊥ :=
    CFSG.HardMathSupport.Solomon.Coordinator.i271h_perm_coprime_normalized_eq_bot hA'
      (by simp) hW₀cop (hA'A.trans hAW₀)
  have hfix : ∀ w ∈ W, ∀ t ∈ (T : Subgroup K), w (e t) = e t := by
    intro w hw t ht
    have hmem : w * MulAut.conj (e t) * w⁻¹ * (MulAut.conj (e t))⁻¹ ∈ W := by
      have h1 : MulAut.conj (e t) * w⁻¹ * (MulAut.conj (e t))⁻¹ ∈ W :=
        (Subgroup.mem_normalizer_iff.mp (hTW t ht) w⁻¹).mp (W.inv_mem hw)
      have e1 : w * MulAut.conj (e t) * w⁻¹ * (MulAut.conj (e t))⁻¹ =
          w * (MulAut.conj (e t) * w⁻¹ * (MulAut.conj (e t))⁻¹) := by group
      rw [e1]
      exact W.mul_mem hw h1
    have heq : w * MulAut.conj (e t) * w⁻¹ * (MulAut.conj (e t))⁻¹ =
        cn ((w (e t) * (e t)⁻¹ : alternatingGroup (Fin 6)) : Perm (Fin 6)) := by
      rw [hcn, map_mul, map_inv]
      congr 1
      refine MulEquiv.ext fun a => ?_
      simp [MulAut.conj_apply]
    have h0 : ((w (e t) * (e t)⁻¹ : alternatingGroup (Fin 6)) : Perm (Fin 6)) ∈ W₀ := by
      rw [hW₀, Subgroup.mem_comap, ← heq]
      exact hmem
    rw [hW₀bot, Subgroup.mem_bot] at h0
    exact mul_inv_eq_one.mp (Subtype.ext h0)
  obtain ⟨t₀, ht₀, h3⟩ : ∃ t ∈ (T : Subgroup K),
      ((e t : alternatingGroup (Fin 6)) : Perm (Fin 6)).IsThreeCycle := by
    have hA9 : Nat.card A = 9 := by rw [hAcard, factorization_three_perm_six]; norm_num
    let St : Subgroup (Perm (Fin 6)) := A ⊓ MulAction.stabilizer (Perm (Fin 6)) (0 : Fin 6)
    have hSt : 3 ∣ Nat.card St := by
      have horb := MulAction.card_orbit_mul_card_stabilizer_eq_card_group A (0 : Fin 6)
      simp only [← Nat.card_eq_fintype_card] at horb
      have hle : Nat.card (MulAction.orbit A (0 : Fin 6)) ≤ 6 := by
        calc Nat.card (MulAction.orbit A (0 : Fin 6)) ≤ Nat.card (Fin 6) :=
              Nat.card_le_card_of_injective _ Subtype.val_injective
          _ = 6 := Nat.card_fin 6
      have hstab : Nat.card (MulAction.stabilizer A (0 : Fin 6)) = Nat.card St := by
        refine Nat.card_congr ?_
        exact
          { toFun := fun x => ⟨x.1.1, x.1.2, x.2⟩
            invFun := fun x => ⟨⟨x.1, x.2.1⟩, x.2.2⟩
            left_inv := fun x => rfl
            right_inv := fun x => rfl }
      rw [hA9, hstab] at horb
      have hd : Nat.card St ∣ 9 := Dvd.intro_left _ horb
      have hcases : Nat.card St = 1 ∨ Nat.card St = 3 ∨ Nat.card St = 9 := by
        have : Nat.card St ∈ Nat.divisors 9 := Nat.mem_divisors.mpr ⟨hd, by norm_num⟩
        simpa [show Nat.divisors 9 = {1, 3, 9} by decide] using this
      rcases hcases with h | h | h
      · rw [h] at horb; omega
      · rw [h]
      · rw [h]; norm_num
    obtain ⟨b, hb⟩ := exists_prime_orderOf_dvd_card' (G := St) 3 hSt
    have hbA : (b : Perm (Fin 6)) ∈ A := b.2.1
    have hb0 : (b : Perm (Fin 6)) 0 = 0 := b.2.2
    have hbo : orderOf (b : Perm (Fin 6)) = 3 := by rw [Subgroup.orderOf_coe]; exact hb
    obtain ⟨n, hn⟩ := Equiv.Perm.cycleType_prime_order (σ := (b : Perm (Fin 6)))
      (by rw [hbo]; exact Nat.prime_three)
    have hsupp : ((b : Perm (Fin 6)).support).card = 3 * (n + 1) := by
      rw [← Equiv.Perm.sum_cycleType, hn, hbo, Multiset.sum_replicate, smul_eq_mul, mul_comm]
    have hsupp5 : ((b : Perm (Fin 6)).support).card ≤ 5 := by
      have h1 : (b : Perm (Fin 6)).support ⊆ Finset.univ.erase 0 := by
        intro x hx
        refine Finset.mem_erase.mpr ⟨?_, Finset.mem_univ _⟩
        rintro rfl
        exact (Equiv.Perm.mem_support.mp hx) hb0
      calc ((b : Perm (Fin 6)).support).card ≤ (Finset.univ.erase (0 : Fin 6)).card :=
            Finset.card_le_card h1
        _ = 5 := by simp
    have hn0 : n = 0 := by omega
    obtain ⟨t, ht, hte⟩ := hbA
    refine ⟨t, ht, ?_⟩
    rw [← card_support_eq_three_iff]
    have : ((e t : alternatingGroup (Fin 6)) : Perm (Fin 6)) = b := hte
    rw [this, hsupp, hn0]
  have hs6 : ∀ w ∈ W, w ∈ CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I542.s6Aut := by
    intro w hw
    by_contra hnot
    obtain ⟨k, hk⟩ := CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I542.conj_c3_of_not_mem_s6Aut hnot
    have hc3 : (CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I542.c3A6 :
        Perm (Fin 6)).IsThreeCycle := by
      rw [← card_support_eq_three_iff]
      decide
    obtain ⟨h, hh⟩ := isConj_iff.mp (alternatingGroup.isThreeCycle_isConj (by simp) hc3 h3)
    have hw0 := hfix w hw t₀ ht₀
    have hconj : e t₀ = (w h * k) * CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I542.c33A6 *
        (w h * k)⁻¹ := by
      calc e t₀ = w (e t₀) := hw0.symm
        _ = w (h * CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I542.c3A6 * h⁻¹) := by rw [hh]
        _ = w h * w CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I542.c3A6 * (w h)⁻¹ := by
              rw [map_mul, map_mul, map_inv]
        _ = _ := by rw [hk]; group
    have hcard := congrArg (fun a : alternatingGroup (Fin 6) => ((a : Perm (Fin 6)).support).card)
      hconj
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, Equiv.Perm.card_support_conj] at hcard
    rw [h3.card_support] at hcard
    revert hcard
    decide
  intro s hs
  apply hφ1
  have hw : φ s ∈ W := ⟨s, hs, rfl⟩
  obtain ⟨g, hg⟩ := (CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I542.mem_s6Aut_iff _).mp
    (hs6 _ hw)
  have hgW₀ : g ∈ W₀ := by
    rw [hW₀, Subgroup.mem_comap]
    change MulAut.conjNormal g ∈ W
    rw [hg]
    exact hw
  rw [hW₀bot, Subgroup.mem_bot] at hgW₀
  rw [← hg, hgW₀, map_one]

theorem kFactNineThreeNoTwoAt_alt6 (hn : 5 ≤ 6) : KFactNineThreeNoTwoAt 3 (.alternating 6 hn) := by
  intro X _ _ K hK ⟨e⟩ _ T S hS hTS
  exact le_centralizer_of_alt6 e T hS hTS

theorem le_centralizer_of_ti {X : Type} [Group X] [Finite X] {K : Subgroup X} [K.Normal]
    [IsSimpleGroup K] {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (T : Sylow p K)
    (hTI : ∀ Q : Sylow p K, Q ≠ T → (T : Subgroup K) ⊓ Q = ⊥)
    (hcount : Nat.card (Sylow p K) = Nat.card T + 1) (hpow : ∀ a : ℕ, Nat.card T + 1 ≠ 2 ^ a)
    {S : Subgroup X} (hS : IsPGroup 2 S)
    (hTS : (T : Subgroup K).map K.subtype ≤ Subgroup.normalizer (S : Set X)) :
    S ≤ Subgroup.centralizer (K : Set X) := by
  classical
  let ρ : X →* MulAut K := MulAut.conjNormal
  have hρ1 : ∀ x : X, ρ x = 1 → x ∈ Subgroup.centralizer (K : Set X) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    have h4 := congrArg (fun f : MulAut K => ((f ⟨k, hk⟩ : K) : X)) hx
    simp only [ρ, MulAut.conjNormal_apply, MulAut.one_apply] at h4
    calc k * x = (x * k * x⁻¹) * x := by rw [h4]
      _ = x * k := by group
  set V : Subgroup (MulAut K) := S.map ρ with hV
  have hV2 : IsPGroup 2 V := hS.map ρ
  have hTV : ∀ t ∈ (T : Subgroup K), MulAut.conj t ∈ Subgroup.normalizer (V : Set (MulAut K)) := by
    intro t ht
    have hc : MulAut.conj t = ρ (t : X) := by
      ext k
      simp [ρ, MulAut.conjNormal_apply]
    rw [hc]
    have htn := hTS ⟨t, ht, rfl⟩
    rw [Subgroup.mem_normalizer_iff] at htn ⊢
    intro w
    constructor
    · rintro ⟨s, hs, rfl⟩
      exact ⟨(t : X) * s * (t : X)⁻¹, (htn s).mp hs, by simp⟩
    · rintro ⟨s, hs, hse⟩
      refine ⟨(t : X)⁻¹ * s * (t : X), (htn ((t : X)⁻¹ * s * (t : X))).mpr
        (by simpa [mul_assoc] using hs), ?_⟩
      have hw : w = (ρ (t : X))⁻¹ * ρ s * ρ (t : X) := by rw [hse]; group
      rw [hw]
      simp
  have hconjV : ∀ t ∈ (T : Subgroup K), ∀ v ∈ V,
      (MulAut.conj t)⁻¹ * v * MulAut.conj t ∈ V := by
    intro t ht v hv
    have := (Subgroup.mem_normalizer_iff.mp (hTV t⁻¹ (inv_mem ht)) v).mp hv
    simpa [map_inv] using this
  have hconjV' : ∀ t ∈ (T : Subgroup K), ∀ v ∈ V,
      MulAut.conj t * v * (MulAut.conj t)⁻¹ ∈ V := fun t ht v hv =>
    (Subgroup.mem_normalizer_iff.mp (hTV t ht) v).mp hv
  have hreg : ∀ Q Q' : Sylow p K, Q ≠ T → Q' ≠ T → ∃ u ∈ (T : Subgroup K), u • Q = Q' := by
    intro Q Q' hQ hQ'
    obtain ⟨u, hu, -⟩ :=
      CFSG.Permutation.SylowTrivialIntersection.existsUnique_smul_eq hTI hcount hQ hQ'
    exact ⟨u, u.2, hu⟩
  have hTfix : ∀ u ∈ (T : Subgroup K), u • T = T := fun u hu =>
    CFSG.Permutation.SylowTrivialIntersection.smul_self_of_mem hu
  have hTodd : Odd (Nat.card T) := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp T.isPGroup'
    rw [hk]
    exact Odd.pow (Nat.Prime.odd_of_ne_two Fact.out hp2)
  have hΩeven : 2 ∣ Nat.card (Sylow p K) := by
    rw [hcount]
    exact (Nat.even_add_one.mpr (Nat.not_even_iff_odd.mpr hTodd)).two_dvd
  have hfixT : ∀ v ∈ V, v • T = T := by
    by_contra hno
    push Not at hno
    obtain ⟨v₀, hv₀, hv₀T⟩ := hno
    have horb : ∀ Q : Sylow p K, Q ∈ MulAction.orbit V T := by
      intro Q
      by_cases hQ : Q = T
      · rw [hQ]; exact MulAction.mem_orbit_self T
      · obtain ⟨u, hu, huQ⟩ := hreg (v₀ • T) Q hv₀T hQ
        refine ⟨⟨MulAut.conj u * v₀ * (MulAut.conj u)⁻¹, hconjV' u hu v₀ hv₀⟩, ?_⟩
        change (MulAut.conj u * v₀ * (MulAut.conj u)⁻¹) • T = Q
        have hinvT : (MulAut.conj u)⁻¹ • T = T := by
          rw [← map_inv]
          exact hTfix u⁻¹ (inv_mem hu)
        rw [mul_smul, mul_smul, hinvT]
        exact huQ
    have hcardO : (MulAction.orbit V T).ncard = Nat.card (Sylow p K) := by
      have : MulAction.orbit V T = Set.univ := Set.eq_univ_of_forall horb
      rw [this, Set.ncard_univ]
    have hdvd : Nat.card (Sylow p K) ∣ Nat.card V := by
      rw [← hcardO, ← MulAction.index_stabilizer]
      exact Subgroup.index_dvd_card _
    obtain ⟨a, ha⟩ := IsPGroup.iff_card.mp hV2
    rw [ha, hcount] at hdvd
    obtain ⟨b, -, hb⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
    exact hpow b hb
  have hfixAll : ∀ v ∈ V, ∀ Q : Sylow p K, v • Q = Q := by
    have hmod := hV2.card_modEq_card_fixedPoints (Sylow p K)
    by_contra hno
    push Not at hno
    obtain ⟨v₀, hv₀, Q₀, hQ₀⟩ := hno
    have hnone : ∀ Q : Sylow p K, Q ≠ T → ¬ ∀ v ∈ V, v • Q = Q := by
      intro Q hQ hfix
      apply hQ₀
      have hQ₀T : Q₀ ≠ T := by
        rintro rfl
        exact hQ₀ (hfixT v₀ hv₀)
      obtain ⟨u, hu, huQ⟩ := hreg Q Q₀ hQ hQ₀T
      rw [← huQ, Sylow.smul_def, ← mul_smul]
      have h1 : v₀ * MulAut.conj u = MulAut.conj u * ((MulAut.conj u)⁻¹ * v₀ * MulAut.conj u) := by
        group
      rw [h1, mul_smul, hfix _ (hconjV u hu v₀ hv₀)]
    have hfp : Nat.card (MulAction.fixedPoints V (Sylow p K)) = 1 := by
      rw [Nat.card_eq_one_iff_exists]
      refine ⟨⟨T, fun v => hfixT v v.2⟩, fun x => Subtype.ext ?_⟩
      by_contra hxT
      exact hnone x.1 hxT fun v hv => x.2 ⟨v, hv⟩
    rw [hfp] at hmod
    obtain ⟨c, hc⟩ := hΩeven
    unfold Nat.ModEq at hmod
    rw [hc] at hmod
    omega
  have hker : ∀ k : K, (∀ Q : Sylow p K, k • Q = Q) → k = 1 := by
    intro k hk
    let N₀ : Subgroup K :=
      { carrier := {g | ∀ Q : Sylow p K, g • Q = Q}
        mul_mem' := fun {a b} ha hb Q => by rw [mul_smul, hb Q, ha Q]
        one_mem' := fun Q => one_smul K Q
        inv_mem' := fun {a} ha Q => by rw [inv_smul_eq_iff, ha Q] }
    have hN₀ : N₀.Normal := ⟨fun g hg x Q => by
      have h1 : (x * g * x⁻¹) • Q = x • (g • (x⁻¹ • Q)) := by rw [mul_smul, mul_smul]
      rw [h1, hg (x⁻¹ • Q), smul_inv_smul]⟩
    rcases hN₀.eq_bot_or_eq_top with hb | ht
    · have : k ∈ N₀ := hk
      rw [hb] at this
      exact this
    · exfalso
      have hTn : (T : Subgroup K).Normal := ⟨fun t _ g => by
        have hg : g ∈ N₀ := by rw [ht]; exact Subgroup.mem_top g
        have := Sylow.smul_eq_iff_mem_normalizer.mp (hg T)
        exact (Subgroup.mem_normalizer_iff.mp this t).mp ‹_›⟩
      haveI := Sylow.unique_of_normal T hTn
      have h1 : Nat.card (Sylow p K) = 1 := Nat.card_unique
      rw [hcount] at h1
      have := Nat.card_pos (α := (T : Subgroup K))
      omega
  intro s hs
  apply hρ1
  have hv : ρ s ∈ V := ⟨s, hs, rfl⟩
  refine MulEquiv.ext fun k => ?_
  have hk : k⁻¹ * (ρ s) k = 1 := by
    apply hker
    intro Q
    have e1 : (ρ s) • (k • Q) = k • Q := hfixAll _ hv _
    have e2 : (ρ s) • (k • Q) = ((ρ s) k) • Q := by
      rw [Sylow.smul_def, Sylow.smul_def, ← mul_smul]
      have : ρ s * MulAut.conj k = MulAut.conj ((ρ s) k) * ρ s := by
        rw [← mul_conj_mul_inv]
        group
      rw [this, mul_smul, hfixAll _ hv Q]
    rw [mul_smul, ← e2, e1, inv_smul_smul]
  rw [MulAut.one_apply]
  exact (inv_mul_eq_one.mp hk).symm

theorem pow_add_one_ne_two_pow {p n : ℕ} (hp : Odd p) (hp1 : 1 < p) (hn : 2 ≤ n) (a : ℕ) :
    p ^ n + 1 ≠ 2 ^ a := by
  intro h
  rcases Nat.even_or_odd n with ⟨m, rfl⟩ | ⟨m, rfl⟩
  · obtain ⟨k, hk⟩ := hp.pow (n := m)
    have hsq : p ^ (m + m) = 4 * (k * k + k) + 1 := by
      rw [← two_mul, pow_mul', hk]; ring
    rw [hsq] at h
    rcases a with _ | _ | a
    · simp at h
    · have h' : 4 * (k * k + k) + 1 + 1 = 2 := by simpa using h
      have hk0 : k * k + k = 0 := by omega
      have hk0' : k = 0 := by nlinarith
      subst hk0'
      have h1 : p ^ m = 1 := by simpa using hk
      rcases Nat.pow_eq_one.mp h1 with h2 | h2 <;> omega
    · rw [pow_succ, pow_succ] at h
      omega
  · have hdvd : p + 1 ∣ p ^ (2 * m + 1) + 1 := by
      have := Odd.nat_add_dvd_pow_add_pow p 1 (odd_two_mul_add_one m)
      simpa using this
    rw [h] at hdvd
    obtain ⟨b, -, hb⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
    obtain ⟨e, he⟩ : ∃ e, p = 4 * e + 3 := by
      have hb2 : 2 ≤ b := by
        by_contra hlt
        interval_cases b <;> simp at hb <;> omega
      have h4 : 4 ∣ p + 1 := by
        rw [hb]
        exact (pow_dvd_pow 2 hb2)
      obtain ⟨c, hc⟩ := h4
      exact ⟨c - 1, by omega⟩
    have hsq : p ^ 2 % (2 * (p + 1)) = 1 := by
      have : p ^ 2 = 2 * (p + 1) * (2 * e + 1) + 1 := by rw [he]; ring
      rw [this, Nat.mul_add_mod]
      exact Nat.mod_eq_of_lt (by omega)
    have hpow : p ^ (2 * m + 1) % (2 * (p + 1)) = p := by
      rw [pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod, hsq, one_pow, Nat.one_mod_eq_one.mpr (by omega),
        one_mul, Nat.mod_mod, Nat.mod_eq_of_lt (by omega)]
    have hab : b < a := by
      have hlt : 2 ^ b < 2 ^ a := by
        rw [← hb, ← h]
        have : p < p ^ (2 * m + 1) := by
          simpa using Nat.pow_lt_pow_right hp1 (show 1 < 2 * m + 1 by omega)
        omega
      exact (Nat.pow_lt_pow_iff_right (by norm_num)).mp hlt
    have h0 : 2 ^ a % (2 * (p + 1)) = 0 := by
      rw [hb, ← pow_succ']
      exact Nat.mod_eq_zero_of_dvd (pow_dvd_pow 2 hab)
    rw [← h, Nat.add_mod, hpow] at h0
    have h1 : 1 % (2 * (p + 1)) = 1 := Nat.mod_eq_of_lt (by omega)
    rw [h1, Nat.mod_eq_of_lt (by omega)] at h0
    omega

open scoped MatrixGroups in
theorem kFactNineThreeNoTwoAt_linTwo {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {d : TauCeti.ValidLieTypeIndex}
    (hd : ∃ q : TauCeti.PrimePower, q.p = p ∧ 2 ≤ q.exponent ∧ d.1 = .A 1 q) :
    KFactNineThreeNoTwoAt p (.lie d) := by
  intro X _ _ K hK ⟨eK⟩ _ T S hS hTS
  obtain ⟨q, hqp, hqe, hdq⟩ := hd
  obtain ⟨x, hv⟩ := d
  simp only at hdq
  subst hdq
  haveI : Fact p.Prime := ⟨hp⟩
  have hst : StatedClassicalModel K .PSL (1 + 1) q.p q.exponent :=
    CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv_typeA hv eK
  rw [hqp] at hst
  haveI : IsSimpleGroup K := (CFSG.LieType.Simplicity.fam_PSL_simplicity K _ _ _ hst).2
  have hcount := CFSG.LargeExtraspecial.Bender.card_sylow_of_psl2 K p q.exponent hst
  obtain ⟨-, F, _, _, hF, ⟨e⟩⟩ := hst
  let e' : K ≃* PSL(2, F) :=
    e.trans (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 F).symm
  have hmapinj : ∀ Q₁ Q₂ : Sylow p K, Q₁.mapSurjective (f := e'.toMonoidHom) e'.surjective =
      Q₂.mapSurjective (f := e'.toMonoidHom) e'.surjective → Q₁ = Q₂ := by
    intro Q₁ Q₂ h
    have h' : (Q₁ : Subgroup K).map e'.toMonoidHom = (Q₂ : Subgroup K).map e'.toMonoidHom :=
      congrArg (fun Q : Sylow p (PSL(2, F)) => (Q : Subgroup (PSL(2, F)))) h
    exact Sylow.ext (Subgroup.map_injective e'.injective h')
  have hTcard : Nat.card T = p ^ q.exponent := by
    have h1 := CFSG.Walter.JT.psl2_card_sylow_p hF hp2 (by omega)
      (T.mapSurjective (f := e'.toMonoidHom) e'.surjective)
    rw [← h1]
    change Nat.card (T : Subgroup K) = Nat.card ((T : Subgroup K).map e'.toMonoidHom)
    rw [Subgroup.card_map_of_injective e'.injective]
  have hTI : ∀ Q : Sylow p K, Q ≠ T → (T : Subgroup K) ⊓ Q = ⊥ := by
    intro Q hQ
    rw [eq_bot_iff]
    rintro g ⟨hgT, hgQ⟩
    by_contra hg1
    apply hQ
    refine hmapinj _ _ (CFSG.GorensteinWalter.psl2_sylow_eq_of_mem_nontrivial F hF
      (Q.mapSurjective (f := e'.toMonoidHom) e'.surjective)
      (T.mapSurjective (f := e'.toMonoidHom) e'.surjective) (e' g) ⟨g, hgQ, rfl⟩ ?_
      ⟨g, hgT, rfl⟩)
    intro h1
    exact hg1 (by rw [Subgroup.mem_bot]; exact e'.injective (h1.trans (map_one e').symm))
  exact le_centralizer_of_ti hp2 T hTI (by rw [hcount, hTcard])
    (by rw [hTcard]; exact pow_add_one_ne_two_pow (hp.odd_of_ne_two hp2) hp.one_lt hqe) hS hTS

@[expose] def KFactNineThreeNoTwoRest : Prop :=
  ∀ p, p.Prime → p ≠ 2 → ∀ i, IsNineThreeIndex p i →
    (¬ ∃ d : TauCeti.ValidLieTypeIndex, i = .lie d ∧ IsCaseTwoIndex p d) →
    (¬ ∃ (n : ℕ) (hn : 5 ≤ n), i = .alternating n hn) →
    (¬ ∃ d : TauCeti.ValidLieTypeIndex, i = .lie d ∧
      ∃ q : TauCeti.PrimePower, q.p = p ∧ 2 ≤ q.exponent ∧ d.1 = .A 1 q) →
    KFactNineThreeNoTwoAt p i

theorem kFactNineThreeNoTwo_of_rest
    (h : KFactNineThreeNoTwoRest) : KFactNineThreeNoTwo := by
  refine kFactNineThreeNoTwo_of_at fun p hp hp2 i hi => ?_
  by_cases h2 : ∃ d : TauCeti.ValidLieTypeIndex, i = .lie d ∧ IsCaseTwoIndex p d
  · obtain ⟨d, rfl, hd⟩ := h2
    exact kFactNineThreeNoTwoAt_caseTwo hd
  by_cases h3 : ∃ (n : ℕ) (hn : 5 ≤ n), i = .alternating n hn
  · obtain ⟨n, hn, rfl⟩ := h3
    rcases hi with ⟨rfl, rfl | rfl⟩ | ⟨rfl, rfl⟩
    · exact kFactNineThreeNoTwoAt_alt6 hn
    · exact kFactNineThreeNoTwoAt_alt hn (Or.inl ⟨rfl, rfl⟩)
    · exact kFactNineThreeNoTwoAt_alt hn (Or.inr ⟨rfl, rfl⟩)
  by_cases h4 : ∃ d : TauCeti.ValidLieTypeIndex, i = .lie d ∧
      ∃ q : TauCeti.PrimePower, q.p = p ∧ 2 ≤ q.exponent ∧ d.1 = .A 1 q
  · obtain ⟨d, rfl, hd⟩ := h4
    exact kFactNineThreeNoTwoAt_linTwo hp hp2 hd
  exact h p hp hp2 i hi h2 h3 h4

end CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111
