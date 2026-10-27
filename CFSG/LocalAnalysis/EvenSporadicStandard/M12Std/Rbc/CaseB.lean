module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.Rbc.Lemma36Top
public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.Rbc.Cor14G

public section

namespace CFSG.EvenSporadicStandard.M12Std.Rbc

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.NativeSporadic
open CFSG.EvenSporadicStandard.Solomon78 CFSG.EvenSporadicStandard.Induction
open CFSG.EvenSporadicStandard.M12Std

section Append

variable {G : Type} [Group G] {a m n : ℕ} {U T V TV Tl : ℕ → Subgroup G} {s sV sl : ℕ → G}
  {M : Subgroup G}

theorem TLinks.exists_append_link (hU : TLinks G a U T s)
    (hlink : TLinks G 1 (seq2 (U a) M) Tl sl) (hV : TLinks G m V TV sV) (hV0 : V 0 = M) :
    ∃ (W TW : ℕ → Subgroup G) (sW : ℕ → G), TLinks G (a + 1 + m) W TW sW ∧
      (∀ i ≤ a, W i = U i ∧ TW i = T i) ∧ (∀ j ≤ m, W (a + 1 + j) = V j) ∧
      TW (a + 1) = Tl 1 ∧ (∀ j, 1 ≤ j → j ≤ m → TW (a + 1 + j) = TV j) := by
  have hjoin₁ : seq2 (U a) M 0 = U a := seq2_zero (U a) M
  have hjoin₂ : V 0 = concat a U (seq2 (U a) M) (a + 1) :=
    hV0.trans (concat_add_succ a U (seq2 (U a) M) 0).symm
  have h2 := (hU.append hlink hjoin₁).append hV hjoin₂
  refine ⟨concat (a + 1) (concat a U (seq2 (U a) M)) V,
    concat (a + 1) (concat a T Tl) TV, concat (a + 1) (concat a s sl) sV, h2, ?_, ?_, ?_, ?_⟩
  · intro i hi
    exact ⟨by rw [concat_of_le (by omega : i ≤ a + 1), concat_of_le hi],
      by rw [concat_of_le (by omega : i ≤ a + 1), concat_of_le hi]⟩
  · intro j hj
    exact concat_add hjoin₂ j
  · rw [concat_of_le le_rfl]
    simpa using concat_add_succ a T Tl 0
  · intro j hj1 hjm
    obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
    exact concat_add_succ (a + 1) (concat a T Tl) TV k

variable [Finite G]

theorem InCGb.exists_append_link (hC : InCGb G n U T s) (ha : a ≤ n)
    (hlink : TLinks G 1 (seq2 (U a) M) Tl sl) (hV : InCG G m V TV sV) (hV0 : V 0 = M)
    (hdisj : ∀ i ≤ a, ∀ j ≤ m, U i ≠ V j) :
    ∃ (W TW : ℕ → Subgroup G) (sW : ℕ → G), InCGb G (a + 1 + m) W TW sW ∧
      (∀ i ≤ a, W i = U i) ∧ (∀ j ≤ m, W (a + 1 + j) = V j) := by
  obtain ⟨W, TW, sW, hW, hWi, hWj, _, _⟩ :=
    TLinks.exists_append_link (hC.1.links.mono ha) hlink hV.links hV0
  refine ⟨W, TW, sW, ⟨⟨by omega, ?_, ?_, hW, ?_⟩, ?_⟩,
    fun i hi => (hWi i hi).1, hWj⟩
  · exact (hWj m le_rfl).trans hV.last
  · intro i hi j hj hij
    by_cases hia : i ≤ a <;> by_cases hja : j ≤ a
    · exact hC.1.inj i (by omega) j (by omega)
        ((hWi i hia).1.symm.trans (hij.trans (hWi j hja).1))
    · obtain ⟨j', rfl⟩ : ∃ j', j = a + 1 + j' := ⟨j - (a + 1), by omega⟩
      have hj' : j' ≤ m := by omega
      exact absurd ((hWi i hia).1.symm.trans (hij.trans (hWj j' hj')))
        (hdisj i hia j' hj')
    · obtain ⟨i', rfl⟩ : ∃ i', i = a + 1 + i' := ⟨i - (a + 1), by omega⟩
      have hi' : i' ≤ m := by omega
      exact absurd ((hWj i' hi').symm.trans (hij.trans (hWi j hja).1)).symm
        (hdisj j hja i' hi')
    · obtain ⟨i', rfl⟩ : ∃ i', i = a + 1 + i' := ⟨i - (a + 1), by omega⟩
      obtain ⟨j', rfl⟩ : ∃ j', j = a + 1 + j' := ⟨j - (a + 1), by omega⟩
      have hi' : i' ≤ m := by omega
      have hj' : j' ≤ m := by omega
      have h1 : V i' = V j' := (hWj i' hi').symm.trans (hij.trans (hWj j' hj'))
      have := hV.inj i' hi' j' hj' h1
      omega
  · have hm : 1 ≤ m := hV.one_le
    have h1 : a + 1 + m - 1 = a + 1 + (m - 1) := by omega
    rw [h1, hWj (m - 1) (by omega)]
    exact hV.top
  · rw [(hWi 0 (Nat.zero_le a)).1]
    exact hC.2

end Append

section Normalizer

variable {G : Type} [Group G] [Finite G] {n : ℕ} {U T : ℕ → Subgroup G} {s : ℕ → G} {u x : G}

theorem TopData.le_normalizer_of_isCompIn (hD : TopData G n U T s u x) {K₀ : Subgroup G}
    (hK₀ : IsCompIn K₀ (centralizer ((zpowers x : Subgroup G) : Set G)))
    (hle : U (n - 2) ≤ K₀) :
    centralizer ({x} : Set G) ⊓ centralizer ({u} : Set G) ≤ normalizer (K₀ : Set G) := by
  intro h hh
  rw [Subgroup.mem_inf] at hh
  obtain ⟨hhx, hhu⟩ := hh
  have hzx : centralizer ((zpowers x : Subgroup G) : Set G) = centralizer ({x} : Set G) := by
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  have hJle : jOf (U (n - 1)) x ≤ K₀ := by
    rw [← hD.jstar]
    exact hle
  have hJn : h ∈ normalizer (jOf (U (n - 1)) x : Set G) := by
    have hm : h ∈ centralizer ({u} : Set G) ⊓
        normalizer (jOf (U (n - 1)) x : Set G) := by
      rw [hD.rbc.normalizer_J]
      exact ⟨hhx, hhu⟩
    exact hm.2
  rw [Solomon78.mem_normalizer_iff_map_conj_eq]
  by_contra hne
  have hmem : h ∈ centralizer ((zpowers x : Subgroup G) : Set G) := by
    rw [hzx]
    exact hhx
  have hK₀' : IsCompIn (K₀.map (MulAut.conj h).toMonoidHom)
      (centralizer ((zpowers x : Subgroup G) : Set G)) := hK₀.map_conj hmem
  have hneK : K₀ ≠ K₀.map (MulAut.conj h).toMonoidHom := fun heq => hne heq.symm
  have hJle' : jOf (U (n - 1)) x ≤ K₀.map (MulAut.conj h).toMonoidHom := by
    intro j hj
    have hjh : h⁻¹ * j * h ∈ jOf (U (n - 1)) x :=
      (Subgroup.mem_normalizer_iff''.1 hJn j).1 hj
    exact ⟨h⁻¹ * j * h, hJle hjh,
      by simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]; group⟩
  have hcomm : ∀ j ∈ jOf (U (n - 1)) x, ∀ j' ∈ jOf (U (n - 1)) x, j * j' = j' * j :=
    fun j hj j' hj' =>
      IsCompIn.commute_of_ne hK₀ hK₀' hneK j (hJle hj) j' (hJle' hj')
  have hle_bot : jOf (U (n - 1)) x ≤ ⊥ := by
    intro j hj
    rw [Subgroup.mem_bot]
    exact hD.facts.J_center j hj (hcomm j hj)
  have hcard_le : Nat.card ↥(jOf (U (n - 1)) x) ≤ 1 := by
    have hle' : Nat.card ↥(jOf (U (n - 1)) x) ≤ Nat.card ↥(⊥ : Subgroup G) :=
      Subgroup.card_le_of_le hle_bot
    simpa [Subgroup.card_bot] using hle'
  rw [hD.facts.card_J] at hcard_le
  omega

end Normalizer

section Pure

variable {G : Type*} [Group G]

private theorem mem_or_mul_mem_of_mem_sup_zpowers_of_mem_normalizer {R : Subgroup G} {t : G}
    (ht : t * t = 1) (htN : t ∈ Subgroup.normalizer (R : Set G)) {x : G}
    (hx : x ∈ R ⊔ Subgroup.zpowers t) : x ∈ R ∨ x * t ∈ R := by
  have hle : Subgroup.zpowers t ≤ Subgroup.normalizer (R : Set G) :=
    Subgroup.zpowers_le.mpr htN
  have hx' : x ∈ ((R ⊔ Subgroup.zpowers t : Subgroup G) : Set G) := hx
  rw [Subgroup.coe_mul_of_right_le_normalizer_left R _ hle] at hx'
  obtain ⟨r, hr, s, hs, rfl⟩ := Set.mem_mul.mp hx'
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hs
  have h2 : t ^ (2 : ℤ) = 1 := by rw [zpow_two]; exact ht
  rcases Int.even_or_odd k with ⟨m, rfl⟩ | ⟨m, rfl⟩
  · left
    rwa [← two_mul, zpow_mul, h2, one_zpow, mul_one]
  · right
    rwa [zpow_add_one, zpow_mul, h2, one_zpow, one_mul, mul_assoc, ht, mul_one]

theorem relIndex_sup_zpowers_dvd_two {K : Subgroup G} {x : G} (hx2 : x * x = 1)
    (hx : x ∈ centralizer (K : Set G)) : K.relIndex (K ⊔ zpowers x) ∣ 2 := by
  rw [Subgroup.relIndex_dvd_two_iff]
  refine ⟨x, Subgroup.mem_sup_right (Subgroup.mem_zpowers x), fun b hb => ?_⟩
  exact (mem_or_mul_mem_of_mem_sup_zpowers_of_mem_normalizer hx2
    (Subgroup.centralizer_le_normalizer (K : Set G) hx) hb).elim Or.inr Or.inl

end Pure

section Certified

open _root_.Certificates


variable {G : Type} [Group G] [Finite G] {K : Subgroup G}

theorem _root_.CFSG.EvenSporadicStandard.StdHyp.relIndex_sup_zpowers_dvd_two_m12
    (h : StdHyp G K) (hK : IsSporadic K .M12) {x : G} (hx : x ∈ centralizer (K : Set G))
    (hx2 : orderOf x = 2) :
    (K ⊔ zpowers x).relIndex (centralizer ({x} : Set G)) ∣ 2 := by
  have hZ : center K = ⊥ := center_eq_bot_of_isSporadic_m12 hK
  have hKq : IsSporadic (K ⧸ center K) .M12 := by
    obtain ⟨e⟩ := hK
    exact ⟨((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).trans e⟩
  exact (h.relIndex_sup_zpowers_dvd (h.card_sylow_eq_two_m12 hK) hx hx2).trans
    (index_dvd_two_of_isSporadic_m12 hKq)

theorem _root_.CFSG.EvenSporadicStandard.StdHyp.card_le_four_mul_card_inf_m12
    (h : StdHyp G K) (hK : IsSporadic K .M12) {x : G} (hx : x ∈ centralizer (K : Set G))
    (hx2 : orderOf x = 2) {H : Subgroup G} (hH : H ≤ centralizer ({x} : Set G)) :
    Nat.card ↥H ≤ 4 * Nat.card ↥(K ⊓ H) := by
  have hx2' : x * x = 1 := by
    rw [← pow_two, ← hx2]
    exact pow_orderOf_eq_one x
  have hKC : K ≤ centralizer ({x} : Set G) := fun k hk =>
    Subgroup.mem_centralizer_singleton_iff.2 (Subgroup.mem_centralizer_iff.1 hx k hk)
  have hxC : zpowers x ≤ centralizer ({x} : Set G) :=
    Subgroup.zpowers_le.2 (Subgroup.mem_centralizer_singleton_iff.2 rfl)
  have hKM : K ≤ K ⊔ zpowers x := le_sup_left
  have hMC : K ⊔ zpowers x ≤ centralizer ({x} : Set G) := sup_le hKC hxC
  have hprod : K.relIndex (K ⊔ zpowers x) *
      (K ⊔ zpowers x).relIndex (centralizer ({x} : Set G)) =
      K.relIndex (centralizer ({x} : Set G)) :=
    Subgroup.relIndex_mul_relIndex K (K ⊔ zpowers x) (centralizer ({x} : Set G)) hKM hMC
  have hKM2 : K.relIndex (K ⊔ zpowers x) ∣ 2 := relIndex_sup_zpowers_dvd_two hx2' hx
  have hMC2 : (K ⊔ zpowers x).relIndex (centralizer ({x} : Set G)) ∣ 2 :=
    h.relIndex_sup_zpowers_dvd_two_m12 hK hx hx2
  have hC4 : K.relIndex (centralizer ({x} : Set G)) ≤ 4 := by
    rw [← hprod]
    calc K.relIndex (K ⊔ zpowers x) * (K ⊔ zpowers x).relIndex (centralizer ({x} : Set G))
        ≤ 2 * 2 := Nat.mul_le_mul (Nat.le_of_dvd (by norm_num) hKM2)
          (Nat.le_of_dvd (by norm_num) hMC2)
      _ = 4 := by norm_num
  have hne : K.relIndex (centralizer ({x} : Set G)) ≠ 0 := by
    intro h0
    have hcard := Subgroup.relIndex_mul_card (H := K) (K := centralizer ({x} : Set G))
    rw [h0, zero_mul] at hcard
    exact Nat.card_pos.ne' hcard.symm
  have hKH4 : K.relIndex H ≤ 4 :=
    (Subgroup.relIndex_le_of_le_right (H := K) (K := H)
      (L := centralizer ({x} : Set G)) hH hne).trans hC4
  calc Nat.card ↥H = K.relIndex H * Nat.card ↥(K ⊓ H) :=
        (Subgroup.relIndex_mul_card (H := K) (K := H)).symm
    _ ≤ 4 * Nat.card ↥(K ⊓ H) := Nat.mul_le_mul_right _ hKH4

end Certified

section Certified

open _root_.Certificates


variable {G : Type} [Group G] [Finite G] {n : ℕ} {U T : ℕ → Subgroup G} {s : ℕ → G} {u x : G}

theorem TopData.false_caseB (hUG : Induction.Balance.UHered G)
    (hCIT : CFSG.ComponentClassification.StandardRecognition.ClassicalInvolutionTheoremModels)
    (hMcard : Nat.card MonsterY443Derived = monsterOrder) (htop : TopIsM12 G)
    (hD : TopData G n U T s u x) {K₀ : Subgroup G}
    (hK₀ : IsCompIn K₀ (centralizer ((zpowers x : Subgroup G) : Set G)))
    (hne : K₀ ≠ U (n - 2)) (hinv : K₀ = K₀.map (MulAut.conj u).toMonoidHom)
    (hle : U (n - 2) ≤ K₀)
    (hcl : K₀ = conjClosure (U (n - 2))
      (layerIn (centralizer ((zpowers x : Subgroup G) : Set G)))) : False := by
  have hOu := hD.out
  have hxt : x ∈ centralizer ({u} : Set G) :=
    mem_centralizer_singleton_iff.2 (mem_centralizer_iff.1 hOu.mem x hD.xmem)
  have hzx : centralizer ((zpowers x : Subgroup G) : Set G) = centralizer ({x} : Set G) := by
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  have hux' : u ∈ centralizer ({x} : Set G) :=
    mem_centralizer_singleton_iff.2 (mem_centralizer_singleton_iff.1 hxt).symm
  have hux : u ∈ normalizer ((zpowers x : Subgroup G) : Set G) :=
    Subgroup.centralizer_le_normalizer _ (by rw [hzx]; exact hux')
  have hu2 : u ^ 2 ∈ zpowers x := by
    rw [sq_eq_one_of_orderOf_eq_two hOu.inv]
    exact one_mem _
  have hKc : IsCompIn (U (n - 2))
      (centralizer ((zpowers x ⊔ zpowers u : Subgroup G) : Set G)) := by
    rw [sup_comm, hD.jstar]
    exact isCompIn_jOf hD.facts hxt hD.xinv
  have hx2 : IsPGroup 2 ↥(zpowers x) := isPGroup_zpowers_of_orderOf_eq_two hD.xinv
  have hlink : TLinks G 1 (seq2 (U (n - 2)) K₀) (seq2 (zpowers x ⊔ zpowers u) (zpowers x))
      (seq2 1 u) :=
    tLinks_single hx2 hux hu2 hKc hK₀ (Or.inl hinv) (by rw [← hinv, sup_idem]; exact hle)
      (by rw [← hinv, sup_idem]; exact hcl)
  have hx1 : zpowers x ≠ ⊥ := by
    intro h
    have h1 := Subgroup.zpowers_eq_bot.1 h
    have h2 := hD.xinv
    rw [h1, orderOf_one] at h2
    omega
  obtain ⟨m, V, TV, sV, hV, hV0⟩ := exists_inCG_of_isCompIn hUG hCIT hMcard hOu hx2 hx1 hK₀
  have hdisj : ∀ i ≤ n - 2, ∀ j ≤ m, U i ≠ V j := by
    intro i hi j hj heq
    have h1 : cqOrd (U i) ≤ cqOrd (U (n - 2)) := hD.chain.1.links.cqOrd_mono hi (by omega)
    have h2 : cqOrd (U (n - 2)) < cqOrd K₀ := by
      have := hlink.cqOrd_lt_succ_of_inv (i := 1) le_rfl le_rfl (by simpa using hinv)
        (by simpa using hne.symm)
      simpa using this
    have h3 : cqOrd K₀ ≤ cqOrd (V j) := by
      have := hV.links.cqOrd_mono (Nat.zero_le j) hj
      rwa [hV0] at this
    rw [heq] at h1
    omega
  obtain ⟨W, TW, sW, hW, hWi, hWj⟩ :=
    InCGb.exists_append_link hD.chain (a := n - 2) (by omega) hlink hV hV0 hdisj
  have hm : m = 1 := by
    have h1 := hD.maximal _ W TW sW hW (hWi 0 (Nat.zero_le _))
    have h2 := hD.two_le
    have h3 := hV.one_le
    omega
  subst hm
  have hWtop : W (n - 2 + 1 + 1 - 1) = K₀ := by
    have h1 : W (n - 2 + 1 + 0) = V 0 := hWj 0 (Nat.zero_le _)
    rw [hV0] at h1
    rw [show n - 2 + 1 + 1 - 1 = n - 2 + 1 + 0 by omega]
    exact h1
  have hstd : StdHyp G K₀ := by
    have := InCG.stdHyp_top hMcard (citPart2_of_cit hCIT) hOu hW.1
    rwa [hWtop] at this
  have hM12 : IsSporadic K₀ .M12 := by
    have h1 := InCGb.notF3Five_top hW
    have h2 := InCG.stdHyp_top hMcard (citPart2_of_cit hCIT) hOu hW.1
    rw [hWtop] at h1 h2
    exact htop _ h2 h1
  have hxC : x ∈ centralizer (K₀ : Set G) := by
    rw [mem_centralizer_iff]
    intro g hg
    exact (mem_centralizer_iff.1 (hK₀.1 hg) x (mem_zpowers x)).symm
  have hxK₀ : x ∉ K₀ := by
    intro hx
    have hZ : Subgroup.center ↥K₀ = ⊥ := center_eq_bot_of_isSporadic_m12 hM12
    have hmem : (⟨x, hx⟩ : ↥K₀) ∈ Subgroup.center ↥K₀ := by
      rw [Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext ((mem_centralizer_iff.1 hxC g g.2))
    rw [hZ, Subgroup.mem_bot] at hmem
    have h1 : x = 1 := congrArg Subtype.val hmem
    have h2 := hD.xinv
    rw [h1, orderOf_one] at h2
    omega
  set H : Subgroup G := centralizer ({x} : Set G) ⊓ centralizer ({u} : Set G)
  have hcard : Nat.card ↥H = 960 := hD.facts.card_Cx
  have hcount : Nat.card ↥H ≤ 4 * Nat.card ↥(K₀ ⊓ H) :=
    hstd.card_le_four_mul_card_inf_m12 hM12 hxC hD.xinv inf_le_left
  have hnorm : H ≤ normalizer (K₀ : Set G) := hD.le_normalizer_of_isCompIn hK₀ hle
  have hN : ((K₀ ⊓ H).subgroupOf H).Normal := by
    rw [Subgroup.inf_subgroupOf_right]
    exact Subgroup.normal_subgroupOf_of_le_normalizer hnorm
  have hJ : jOf (U (n - 1)) x ≤ K₀ ⊓ H :=
    le_inf (by rw [← hD.jstar]; exact hle) hD.facts.J_le
  have hsmall : Nat.card ↥(K₀ ⊓ H) ≤ 120 :=
    hD.rbc.normal_small (K₀ ⊓ H) inf_le_right hN hJ (fun hx => hxK₀ (Subgroup.mem_inf.1 hx).1)
  omega

end Certified

end CFSG.EvenSporadicStandard.M12Std.Rbc
