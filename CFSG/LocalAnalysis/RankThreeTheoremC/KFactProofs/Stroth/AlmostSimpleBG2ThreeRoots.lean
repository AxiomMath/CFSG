module

public import CFSG.RankThree.Chevalley.SteinbergCEG2EvenSplitCentralizers

public section

namespace CFSG.RankThree.Chevalley

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.ComponentClassification.UnbalancedCatalog CFSG.Timmesfeld.ExceptionalOrders
open scoped Pointwise commutatorElement

variable {K : Type} [Field K]

theorem rootChar_g2a_eq_one_of_det_three {a : Fin Tag.G2.rank → Kˣ}
    {X Y : Fin Tag.G2.rank → ℤ}
    (hdet : X g2ia * Y g2ir - X g2ir * Y g2ia = 3 ∨ X g2ia * Y g2ir - X g2ir * Y g2ia = -3)
    (h3X : (3 : ℤ) ∣ X g2ir) (h3Y : (3 : ℤ) ∣ Y g2ir) (hX : rootChar a X = 1)
    (hY : rootChar a Y = 1) : rootChar a g2a = 1 := by
  obtain ⟨k₁, hk₁⟩ := h3X
  obtain ⟨k₂, hk₂⟩ := h3Y
  have hε : ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧ X g2ia * k₂ - k₁ * Y g2ia = ε := by
    rcases hdet with h | h
    · refine ⟨1, Or.inl rfl, ?_⟩
      rw [hk₁, hk₂] at h
      linarith
    · refine ⟨-1, Or.inr rfl, ?_⟩
      rw [hk₁, hk₂] at h
      linarith
  obtain ⟨ε, hε1, hε⟩ := hε
  have hg : g2a = (ε * k₂) • X + (-(ε * k₁)) • Y := by
    funext j
    rcases fin_G2_cases j with rfl | rfl
    · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      have : (g2a : Fin Tag.G2.rank → ℤ) g2ia = 1 := by decide
      rw [this]
      rcases hε1 with rfl | rfl <;> linarith
    · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      have : (g2a : Fin Tag.G2.rank → ℤ) g2ir = 0 := by decide
      rw [this, hk₁, hk₂]
      ring
  rw [hg, rootChar_add, rootChar_zsmul, rootChar_zsmul, hX, hY, one_zpow, one_zpow, mul_one]

theorem g2_det_three_dvd : ∀ u ∈ g2RootPairs, ∀ v ∈ g2RootPairs,
    (u.1 * v.2 - u.2 * v.1 = 3 ∨ u.1 * v.2 - u.2 * v.1 = -3) →
      (3 : ℤ) ∣ u.2 ∧ (3 : ℤ) ∣ v.2 := by
  decide


theorem rootCharKernel_G2_cases_three {a : Fin Tag.G2.rank → Kˣ} (hap : a ^ 3 = 1) (ha1 : a ≠ 1)
    (ha0 : rootChar a g2a ≠ 1) :
    rootCharKernel a = ∅ ∨ ∃ α, IsRoot .G2 α ∧ rootCharKernel a = {α, -α} := by
  have key : ∀ α ∈ rootCharKernel a, ∀ β ∈ rootCharKernel a, β = α ∨ β = -α := by
    intro α hα β hβ
    rcases G2_roots_eq_or_det hα.1 hβ.1 with h | h | hdet
    · exact Or.inl h
    · exact Or.inr h
    · exfalso
      have hd3 : (α g2ia * β g2ir - α g2ir * β g2ia = 3 ∨
          α g2ia * β g2ir - α g2ir * β g2ia = -3) → False := by
        intro h3
        have hdvd := g2_det_three_dvd (g2Pair α) (g2Pair_mem_of_isRoot hα.1) (g2Pair β)
          (g2Pair_mem_of_isRoot hβ.1) h3
        exact ha0 (rootChar_g2a_eq_one_of_det_three h3 hdvd.1 hdvd.2 hα.2 hβ.2)
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hdet
      rcases hdet with h | h | h | h | h | h
      · exact ha1 (eq_one_of_rootChar_det Nat.prime_three hap hα.2 hβ.2 (by rw [h]; decide))
      · exact ha1 (eq_one_of_rootChar_det Nat.prime_three hap hα.2 hβ.2 (by rw [h]; decide))
      · exact hd3 (Or.inl h)
      · exact ha1 (eq_one_of_rootChar_det Nat.prime_three hap hα.2 hβ.2 (by rw [h]; decide))
      · exact ha1 (eq_one_of_rootChar_det Nat.prime_three hap hα.2 hβ.2 (by rw [h]; decide))
      · exact hd3 (Or.inr h)
  by_cases hne : (rootCharKernel a).Nonempty
  · obtain ⟨α, hα⟩ := hne
    refine Or.inr ⟨α, hα.1, ?_⟩
    have hneg : -α ∈ rootCharKernel a :=
      ⟨IsRoot.neg hα.1, by rw [rootChar_neg_eq_inv, hα.2, inv_one]⟩
    ext β
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · exact key α hα β
    · rintro (rfl | rfl)
      · exact hα
      · exact hneg
  · exact Or.inl (Set.not_nonempty_iff_eq_empty.1 hne)

theorem rootCharStabilizer_le_kernelReflectionGroup_G2_three
    {a : Fin Tag.G2.rank → Kˣ} (hap : a ^ 3 = 1) (ha1 : a ≠ 1)
    (ha0 : rootChar a g2a ≠ 1) :
    rootCharStabilizerSubgroup a ≤ kernelReflectionGroup a := by
  intro w hw
  have hw' : ∀ v, rootChar a (w • v) = rootChar a v := hw
  have hrot : ∀ X Y : Fin Tag.G2.rank → ℤ, w • g2a = X → w • g2r = Y →
      ¬ ((3 : ℕ) : ℤ) ∣ ((X - g2a) g2ia * (Y - g2r) g2ir - (X - g2a) g2ir * (Y - g2r) g2ia) →
        w ∈ kernelReflectionGroup a := by
    intro X Y hX hY hd
    refine absurd (eq_one_of_rootChar_det Nat.prime_three hap ?_ ?_ hd) ha1
    · rw [rootChar_sub, ← hX, hw', mul_inv_cancel]
    · rw [rootChar_sub, ← hY, hw', mul_inv_cancel]
  have hrot3 : ∀ X Y : Fin Tag.G2.rank → ℤ, w • g2a = X → w • g2r = Y →
      ((X - g2a) g2ia * (Y - g2r) g2ir - (X - g2a) g2ir * (Y - g2r) g2ia = 3 ∨
        (X - g2a) g2ia * (Y - g2r) g2ir - (X - g2a) g2ir * (Y - g2r) g2ia = -3) →
      (3 : ℤ) ∣ (X - g2a) g2ir → (3 : ℤ) ∣ (Y - g2r) g2ir → w ∈ kernelReflectionGroup a := by
    intro X Y hX hY hd h3X h3Y
    exfalso
    refine ha0 (rootChar_g2a_eq_one_of_det_three hd h3X h3Y ?_ ?_)
    · rw [rootChar_sub, ← hX, hw', mul_inv_cancel]
    · rw [rootChar_sub, ← hY, hw', mul_inv_cancel]
  have hrefl : ∀ (g : WeylGroup .G2) (i : Fin Tag.G2.rank), w = g * simple .G2 i * g⁻¹ →
      w ∈ kernelReflectionGroup a := by
    intro g i hwg
    refine Subgroup.subset_closure ⟨g, i, ⟨IsRoot.smul (isRoot_single _ i) g, ?_⟩, hwg⟩
    have hwα : w • (g • (Pi.single i 1 : Fin Tag.G2.rank → ℤ)) =
        -(g • (Pi.single i 1 : Fin Tag.G2.rank → ℤ)) := by
      rw [hwg, mul_smul, mul_smul, inv_smul_smul, simple_smul, reflect_single_self, smul_neg]
    have h1 : (rootChar a (g • (Pi.single i 1 : Fin Tag.G2.rank → ℤ)))⁻¹ =
        rootChar a (g • (Pi.single i 1 : Fin Tag.G2.rank → ℤ)) := by
      rw [← rootChar_neg_eq_inv, ← hwα, hw']
    have h2 : rootChar a (g • (Pi.single i 1 : Fin Tag.G2.rank → ℤ)) ^ (2 : ℤ) = 1 := by
      rw [zpow_two]
      calc _ = (rootChar a (g • (Pi.single i 1 : Fin Tag.G2.rank → ℤ)))⁻¹ *
            rootChar a (g • (Pi.single i 1 : Fin Tag.G2.rank → ℤ)) := by rw [h1]
        _ = 1 := inv_mul_cancel _
    exact eq_one_of_pow_prime_of_zpow Nat.prime_three (rootChar_pow_of_pow_eq_one hap _) h2
      (not_dvd_of_natAbs_lt (by norm_num) (by norm_num))
  have hinv : ∀ i : Fin Tag.G2.rank, (simple .G2 i)⁻¹ = simple .G2 i :=
    (coxeterSystem .G2).inv_simple
  rcases g2_weyl_cases w with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ |
    ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
  ·
    have hw1 : w = 1 := weyl_G2_ext (by rw [h1, one_smul]) (by rw [h2, one_smul])
    rw [hw1]
    exact one_mem _
  ·
    refine hrefl 1 g2ia (weyl_G2_ext ?_ ?_)
    · rw [h1, one_mul, inv_one, mul_one, simple_smul]
      exact List.ofFn_injective (by decide +kernel)
    · rw [h2, one_mul, inv_one, mul_one, simple_smul]
      exact List.ofFn_injective (by decide +kernel)
  ·
    refine hrefl 1 g2ir (weyl_G2_ext ?_ ?_)
    · rw [h1, one_mul, inv_one, mul_one, simple_smul]
      exact List.ofFn_injective (by decide +kernel)
    · rw [h2, one_mul, inv_one, mul_one, simple_smul]
      exact List.ofFn_injective (by decide +kernel)
  · exact hrot _ _ h1 h2 (by
      rw [show (g2c - g2a) g2ia * (-g2u - g2r) g2ir - (g2c - g2a) g2ir * (-g2u - g2r) g2ia = 1
        by decide]
      norm_num)
  · exact hrot _ _ h1 h2 (by
      rw [show (-g2b - g2a) g2ia * (g2v - g2r) g2ir - (-g2b - g2a) g2ir * (g2v - g2r) g2ia = 1
        by decide]
      norm_num)
  ·
    refine hrefl (simple .G2 g2ia) g2ir (weyl_G2_ext ?_ ?_)
    · rw [h1, hinv, mul_smul, mul_smul, simple_smul, simple_smul, simple_smul]
      exact List.ofFn_injective (by decide +kernel)
    · rw [h2, hinv, mul_smul, mul_smul, simple_smul, simple_smul, simple_smul]
      exact List.ofFn_injective (by decide +kernel)
  ·
    refine hrefl (simple .G2 g2ir) g2ia (weyl_G2_ext ?_ ?_)
    · rw [h1, hinv, mul_smul, mul_smul, simple_smul, simple_smul, simple_smul]
      exact List.ofFn_injective (by decide +kernel)
    · rw [h2, hinv, mul_smul, mul_smul, simple_smul, simple_smul, simple_smul]
      exact List.ofFn_injective (by decide +kernel)
  · exact hrot3 _ _ h1 h2 (Or.inl (by decide)) (by decide) (by decide)
  · exact hrot3 _ _ h1 h2 (Or.inl (by decide)) (by decide) (by decide)
  ·
    refine hrefl (simple .G2 g2ia * simple .G2 g2ir) g2ia (weyl_G2_ext ?_ ?_)
    · rw [h1]
      simp only [mul_inv_rev, hinv, mul_smul, simple_smul]
      exact List.ofFn_injective (by decide +kernel)
    · rw [h2]
      simp only [mul_inv_rev, hinv, mul_smul, simple_smul]
      exact List.ofFn_injective (by decide +kernel)
  ·
    refine hrefl (simple .G2 g2ir * simple .G2 g2ia) g2ir (weyl_G2_ext ?_ ?_)
    · rw [h1]
      simp only [mul_inv_rev, hinv, mul_smul, simple_smul]
      exact List.ofFn_injective (by decide +kernel)
    · rw [h2]
      simp only [mul_inv_rev, hinv, mul_smul, simple_smul]
      exact List.ofFn_injective (by decide +kernel)
  · exact hrot _ _ h1 h2 (by
      rw [show (-g2a - g2a) g2ia * (-g2r - g2r) g2ir - (-g2a - g2a) g2ir * (-g2r - g2r) g2ia = 4
        by decide]
      norm_num)


namespace EvenG2


theorem toral_centralizer_cases_G2_three (K : Type) [Field K] [Finite K] [CharP K 2]
    (h4 : 4 ≤ Nat.card K) (a : Fin Tag.G2.rank → Kˣ) (hap : a ^ 3 = 1) (ha1 : a ≠ 1)
    (ha0 : rootChar a g2a ≠ 1) :
    (rootCharKernel a = ∅ ∧ toralCentralizer .G2 K a = torusGroup .G2 K) ∨
    (∃ α : Fin Tag.G2.rank → ℤ, IsRoot .G2 α ∧ rootCharKernel a = {α, -α} ∧
      toralCentralizer .G2 K a =
        torusGroup .G2 K ⊔ (rootSubgroup .G2 K α ⊔ rootSubgroup .G2 K (-α)) ∧
      (toralCentralizer .G2 K a : Set (ModGL .G2 K)) =
        (torusGroup .G2 K : Set (ModGL .G2 K)) *
          ((rootSubgroup .G2 K α ⊔ rootSubgroup .G2 K (-α) : Subgroup (ModGL .G2 K)) :
            Set (ModGL .G2 K)) ∧
      ⁅toralCentralizer .G2 K a, toralCentralizer .G2 K a⁆ =
        rootSubgroup .G2 K α ⊔ rootSubgroup .G2 K (-α) ∧
      toralCentralizer .G2 K a ⊓ Subgroup.centralizer
          ((rootSubgroup .G2 K α ⊔ rootSubgroup .G2 K (-α) : Subgroup (ModGL .G2 K)) :
            Set (ModGL .G2 K)) =
        (Subgroup.center (toralCentralizer .G2 K a)).map (toralCentralizer .G2 K a).subtype ∧
      (Subgroup.center (toralCentralizer .G2 K a)).map (toralCentralizer .G2 K a).subtype ≤
        torusGroup .G2 K) := by
  classical
  have hTcomm := (triangular_borel_structure.{0, 0} .G2 K).1
  have hX := toralCentralizer_eq_toralRootGroup_of_le (K := K)
    (rootCharStabilizer_le_kernelReflectionGroup_G2_three hap ha1 ha0)
  set X := toralCentralizer .G2 K a with hXdef
  rcases rootCharKernel_G2_cases_three hap ha1 ha0 with hker | ⟨α, hα, hker⟩
  ·
    refine Or.inl ⟨hker, ?_⟩
    rw [hX, toralRootGroup, hker]
    simp [rootSpan]
  ·
    set Q : Subgroup (ModGL .G2 K) := rootSubgroup .G2 K α ⊔ rootSubgroup .G2 K (-α) with hQdef
    have hXQ : X = torusGroup .G2 K ⊔ Q := by
      rw [hX, toralRootGroup, hker, rootSpan, iSup_insert, iSup_singleton]
    have hXset : (X : Set (ModGL .G2 K)) = (torusGroup .G2 K : Set (ModGL .G2 K)) * Q := by
      rw [hXQ]
      exact Subgroup.coe_mul_of_left_le_normalizer_right _ _ (torusGroup_le_normalizer_rootPair hα)
    have hQX : Q ≤ X := hXQ ▸ le_sup_right
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hfin⟩ := even_Chevalley_pinned_root_SL2_maps .G2 K hα
    have hperf : ⁅Q, Q⁆ = Q :=
      Subgroup.isPerfect_iff.1 (hfin inferInstance h4).2.1
    have hcomm : ⁅X, X⁆ = Q := by
      refine le_antisymm ?_ (hperf ▸ Subgroup.commutator_mono hQX hQX)
      rw [Subgroup.commutator_le]
      intro x hx y hy
      rw [← SetLike.mem_coe, hXset] at hx hy
      obtain ⟨h, hh, q, hq, rfl⟩ := hx
      obtain ⟨h', hh', q', hq', rfl⟩ := hy
      have e1 : ⁅h * q, h' * q'⁆ = (h * h') * (h'⁻¹ * q * h' * (q' * q⁻¹)) * (h' * h)⁻¹ *
          (h' * q'⁻¹ * h'⁻¹) := by
        rw [commutatorElement_def]
        group
      rw [e1, ← hTcomm h hh h' hh']
      refine mul_mem (conj_mem_rootPair_of_mem_torusGroup (mul_mem hh hh') hα (mul_mem ?_
        (mul_mem hq' (inv_mem hq)))) (conj_mem_rootPair_of_mem_torusGroup hh' hα (inv_mem hq'))
      have := conj_mem_rootPair_of_mem_torusGroup (inv_mem hh') hα hq
      rwa [inv_inv] at this
    have hCT : X ⊓ Subgroup.centralizer (Q : Set (ModGL .G2 K)) ≤ torusGroup .G2 K := by
      intro z hz
      obtain ⟨hzX, hzC⟩ := Subgroup.mem_inf.1 hz
      have hzX' : z ∈ (X : Set (ModGL .G2 K)) := hzX
      rw [hXset] at hzX'
      obtain ⟨h, hh, u, hu, rfl⟩ := hzX'
      have hcz : ∀ x ∈ Q, (h * u) * x * (h * u)⁻¹ = x := fun x hx => by
        rw [← Subgroup.mem_centralizer_iff.1 hzC x hx, mul_inv_cancel_right]
      have hconj : ∀ x ∈ Q, u * x * u⁻¹ = h⁻¹ * x * h⁻¹⁻¹ := fun x hx => by
        have e2 : u * x * u⁻¹ = h⁻¹ * ((h * u) * x * (h * u)⁻¹) * h⁻¹⁻¹ := by group
        rw [e2, hcz x hx]
      have hup : ∀ x ∈ rootSubgroup .G2 K α, u * x * u⁻¹ ∈ rootSubgroup .G2 K α := fun x hx => by
        rw [hconj x (Subgroup.mem_sup_left hx)]
        exact conj_mem_rootSubgroup_of_mem_torusGroup (inv_mem hh) hα hx
      have hdown : ∀ x ∈ rootSubgroup .G2 K (-α), u * x * u⁻¹ ∈ rootSubgroup .G2 K (-α) :=
        fun x hx => by
          rw [hconj x (Subgroup.mem_sup_right hx)]
          exact conj_mem_rootSubgroup_of_mem_torusGroup (inv_mem hh) (IsRoot.neg hα) hx
      exact mul_mem hh (mem_torusGroup_of_conj_rootSubgroups_of_charTwo hα hu hup hdown)
    have hZ : X ⊓ Subgroup.centralizer (Q : Set (ModGL .G2 K)) =
        (Subgroup.center X).map X.subtype := by
      refine le_antisymm ?_ ?_
      · intro z hz
        obtain ⟨hzX, hzC⟩ := Subgroup.mem_inf.1 hz
        have hzT := hCT hz
        have hle : X ≤ Subgroup.centralizer {z} := by
          rw [hXQ]
          refine sup_le (fun t ht => ?_) (fun x hx => ?_)
          · rw [Subgroup.mem_centralizer_singleton_iff]
            exact (hTcomm z hzT t ht).symm
          · rw [Subgroup.mem_centralizer_singleton_iff]
            exact Subgroup.mem_centralizer_iff.1 hzC x hx
        refine ⟨⟨z, hzX⟩, Subgroup.mem_center_iff.2 fun g => Subtype.ext ?_, rfl⟩
        exact Subgroup.mem_centralizer_singleton_iff.1 (hle g.2)
      · rintro _ ⟨z, hz, rfl⟩
        refine ⟨z.2, Subgroup.mem_centralizer_iff.2 fun x hx => ?_⟩
        exact congrArg Subtype.val (Subgroup.mem_center_iff.1 hz ⟨x, hQX hx⟩)
    exact Or.inr ⟨α, hα, hker, hXQ, hXset, hcomm, hZ, hZ ▸ hCT⟩


end EvenG2

end CFSG.RankThree.Chevalley
