module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofUCommute
public import CFSG.LieType.Universal.Unitary.Clause0
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofUBlocks

public section

namespace CFSG.ComponentClassification.RankTwoClassical

open Matrix Subgroup CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open scoped MatrixGroups commutatorElement

section SUTwo

variable {K : Type} [Field K] [Finite K] [CharP K 2] {f : ℕ}

theorem nonempty_SL2_equiv_statedSU_two (hK : Nat.card K = (2 ^ f) ^ 2) :
    Nonempty (SL(2, CFSG.LieType.Steinberg.fixedSubfield K 2 f) ≃* StatedSU 2 (2 ^ f) K) := by
  obtain ⟨ζ, hζ0, hζ⟩ := CFSG.LieType.BorelTits.exists_unitaryInvolution_eq_neg hK
  obtain ⟨P, hP⟩ := CFSG.LieType.Universal.Unitary.exists_wittMatrix hK 2
  exact ⟨((CFSG.LieType.Steinberg.hypEquiv hζ0 hζ).trans
    (CFSG.LieType.Universal.Unitary.conjEquiv P hP)).trans
      (MulEquiv.subgroupCongr (CFSG.LieType.Universal.Unitary.SUid_eq_statedSU hK 2))⟩

theorem exists_finset_fixedSubfield (hK : Nat.card K = (2 ^ f) ^ 2) (hf : 2 ≤ f) :
    ∃ s : Finset (CFSG.LieType.Steinberg.fixedSubfield K 2 f), s.card = 4 := by
  classical
  have : Fintype (CFSG.LieType.Steinberg.fixedSubfield K 2 f) := Fintype.ofFinite _
  obtain ⟨s, -, hs⟩ := Finset.exists_subset_card_eq
    (s := (Finset.univ : Finset (CFSG.LieType.Steinberg.fixedSubfield K 2 f))) (n := 4) (by
      rw [Finset.card_univ, ← Nat.card_eq_fintype_card,
        CFSG.LieType.Steinberg.card_fixedSubfield hK]
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf)
  exact ⟨s, hs⟩

theorem charP_fixedSubfield (hK : Nat.card K = (2 ^ f) ^ 2) :
    CharP (CFSG.LieType.Steinberg.fixedSubfield K 2 f) 2 := by
  have : Fintype (CFSG.LieType.Steinberg.fixedSubfield K 2 f) := Fintype.ofFinite _
  exact charP_of_card_eq_prime_pow
    (by rw [← Nat.card_eq_fintype_card, CFSG.LieType.Steinberg.card_fixedSubfield hK])

theorem exists_norm_one_ne_one (hK : Nat.card K = (2 ^ f) ^ 2) :
    ∃ ζ : K, ζ ^ 2 ^ f * ζ = 1 ∧ ζ ≠ 1 := by
  obtain ⟨ζ, hζ, hζ1⟩ := CFSG.LieType.Universal.Unitary.exists_norm_eq_one_ne_one hK
  refine ⟨ζ, ?_, hζ1⟩
  rwa [CFSG.LieType.BorelTits.unitaryInvolution_apply] at hζ

theorem commutator_statedSU_two (hK : Nat.card K = (2 ^ f) ^ 2) (hf : 2 ≤ f) :
    commutator (StatedSU 2 (2 ^ f) K) = ⊤ := by
  obtain ⟨e⟩ := nonempty_SL2_equiv_statedSU_two hK
  have : Group.IsPerfect SL(2, CFSG.LieType.Steinberg.fixedSubfield K 2 f) :=
    CFSG.LinearGroups.special_linear_dimension_two_perfect (exists_finset_fixedSubfield hK hf)
  exact (Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective).commutator_eq_top

theorem ne_three_two_of_two_le {k : ℕ} (hf : 2 ≤ f) : (k, 2 ^ f) ≠ (3, 2) := by
  intro h
  have h2 : 2 ^ f = 2 := (Prod.mk.inj h).2
  have : 2 ^ 2 ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  omega

theorem commutator_statedSU (hK : Nat.card K = (2 ^ f) ^ 2) (hf : 2 ≤ f) {k : ℕ} (hk : 2 ≤ k) :
    commutator (StatedSU k (2 ^ f) K) = ⊤ := by
  rcases (show k = 2 ∨ 3 ≤ k by omega) with rfl | hk3
  · exact commutator_statedSU_two hK hf
  · exact (CFSG.ClassicalGroups.Unitary.isPerfect_statedSU hK hk3
      (ne_three_two_of_two_le hf)).commutator_eq_top

theorem isQuasisimple_statedSU_of_two_le (hK : Nat.card K = (2 ^ f) ^ 2) (hf : 2 ≤ f) {k : ℕ}
    (hk : 2 ≤ k) : CFSG.IsQuasisimple (StatedSU k (2 ^ f) K) := by
  rcases (show k = 2 ∨ 3 ≤ k by omega) with rfl | hk3
  · obtain ⟨e⟩ := nonempty_SL2_equiv_statedSU_two hK
    exact CFSG.LocalCores.isQuasisimple_of_mulEquiv e
      (isQuasisimple_SL le_rfl (exists_finset_fixedSubfield hK hf))
  · exact (CFSG.LieType.Universal.Unitary.isQuasisimple_statedSU_of_card hK hk3
      (ne_three_two_of_two_le hf)).1

theorem center_statedSU_two_eq_bot (hK : Nat.card K = (2 ^ f) ^ 2) :
    center (StatedSU 2 (2 ^ f) K) = ⊥ := by
  obtain ⟨e⟩ := nonempty_SL2_equiv_statedSU_two hK
  have := charP_fixedSubfield hK
  rw [← Subgroup.map_center_eq e, center_SL2_eq_bot', Subgroup.map_bot]

theorem odd_card_center_statedSU (hK : Nat.card K = (2 ^ f) ^ 2) (hf : 2 ≤ f) {k : ℕ}
    (hk : 2 ≤ k) : Odd (Nat.card (center (StatedSU k (2 ^ f) K))) := by
  rcases (show k = 2 ∨ 3 ≤ k by omega) with rfl | hk3
  · rw [center_statedSU_two_eq_bot hK, Subgroup.card_bot]
    exact odd_one
  · rw [(CFSG.LieType.Universal.Unitary.isQuasisimple_statedSU_of_card hK hk3
      (ne_three_two_of_two_le hf)).2,
      (CFSG.LinearGroups.unitary_scalar_kernel Nat.prime_two hK (by omega)).2.2]
    have hodd : Odd (2 ^ f + 1) := (Nat.even_pow.mpr ⟨even_two, by omega⟩).add_one
    exact Odd.of_dvd_nat hodd (Nat.gcd_dvd_right _ _)

end SUTwo

section Bar

variable {K : Type} [Field K] [Finite K] [CharP K 2] {k f : ℕ}

theorem commutator_uBarW (hK : Nat.card K = (2 ^ f) ^ 2) (hf : 2 ≤ f) :
    ⁅uBarW K k f, uBarW K k f⁆ = uBarW K k f :=
  commutator_range_of_perfect _ (commutator_statedSU_two hK hf)

theorem commutator_uBarL (hK : Nat.card K = (2 ^ f) ^ 2) (hf : 2 ≤ f) (hk : 2 ≤ k) :
    ⁅uBarL K k f, uBarL K k f⁆ = uBarL K k f :=
  commutator_range_of_perfect _ (commutator_statedSU hK hf hk)

theorem isQuasisimple_uBarW (hK : Nat.card K = (2 ^ f) ^ 2) (hf : 2 ≤ f) (hk : 1 ≤ k) :
    CFSG.IsQuasisimple ↥(uBarW K k f) :=
  CFSG.LocalCores.isQuasisimple_of_mulEquiv (uBarWEquiv K k f hk)
    (isQuasisimple_statedSU_of_two_le hK hf le_rfl)

theorem isQuasisimple_uBarL (hK : Nat.card K = (2 ^ f) ^ 2) (hf : 2 ≤ f) (hk : 2 ≤ k) :
    CFSG.IsQuasisimple ↥(uBarL K k f) :=
  CFSG.LocalCores.isQuasisimple_of_mulEquiv (uBarLEquiv K k f)
    (isQuasisimple_statedSU_of_two_le hK hf hk)

theorem odd_card_center_uBarL (hK : Nat.card K = (2 ^ f) ^ 2) (hf : 2 ≤ f) (hk : 2 ≤ k) :
    Odd (Nat.card (center ↥(uBarL K k f))) := by
  rw [← card_center_congr (uBarLEquiv K k f)]
  exact odd_card_center_statedSU hK hf hk

end Bar

section Centralizer

variable {K : Type} [Field K] [CharP K 2] {k f : ℕ}

omit [CharP K 2] in
theorem unitaryFieldData_of_card (hK : Nat.card K = (2 ^ f) ^ 2) (hf : 1 ≤ f) :
    UnitaryFieldData 2 f K :=
  ⟨Nat.prime_two, hf, by rw [hK, ← pow_mul, mul_comm]⟩

theorem commute_of_uProj_commute {n : ℕ} (hn : 1 ≤ n) {g x : StatedSU n (2 ^ f) K}
    (hx : x * x = 1) (h : uProj K n f g * uProj K n f x = uProj K n f x * uProj K n f g) :
    g * x = x * g := by
  have h2 : uProj K n f (g * x * g⁻¹) = uProj K n f x := by
    rw [map_mul, map_mul, map_inv, h, mul_inv_cancel_right]
  have h3 := eq_of_uProj_eq_of_mul_self hn h2 (by
    calc g * x * g⁻¹ * (g * x * g⁻¹) = g * (x * x) * g⁻¹ := by group
      _ = 1 := by rw [hx, mul_one, mul_inv_cancel]) hx
  calc g * x = g * x * g⁻¹ * g := by group
    _ = x * g := by rw [h3]

omit [CharP K 2] in
theorem mul_self_eq_one_of_val {n : ℕ} {x : StatedSU n (2 ^ f) K}
    {M : Matrix (Fin n) (Fin n) K} (hx : (x : GL (Fin n) K).val = M) (hM : M * M = 1) :
    x * x = 1 :=
  Subtype.ext (Units.ext (by rw [Subgroup.coe_mul, Units.val_mul, hx, hM]; rfl))

theorem exists_blk_of_commute_uBarW (hk : 1 ≤ k) {ζ : K} (hζ : ζ ^ 2 ^ f * ζ = 1)
    (hζ1 : ζ ≠ 1) {x : StatedProj (StatedSU (2 + k) (2 ^ f) K)}
    (hx : ∀ w ∈ uBarW K k f, x * w = w * x) :
    ∃ g : StatedSU (2 + k) (2 ^ f) K, uProj K (2 + k) f g = x ∧
      ∃ (a : K) (D : Matrix (Fin k) (Fin k) K), (g : GL (Fin (2 + k)) K).val = blk (a • 1) D := by
  have hζ0 : ζ ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hζ
    exact zero_ne_one hζ
  obtain ⟨g, rfl⟩ := uProj_surjective (K := K) (f := f) (2 + k) x
  refine ⟨g, rfl, ?_⟩
  obtain ⟨J, hJ⟩ := exists_swapM_mem (K := K) f
  obtain ⟨J', hJ'⟩ := exists_twJ_mem hζ
  have hc : ∀ X : StatedSU 2 (2 ^ f) K, X * X = 1 →
      (g : GL (Fin (2 + k)) K).val * blk (X : GL (Fin 2) K).val 1 =
        blk (X : GL (Fin 2) K).val 1 * (g : GL (Fin (2 + k)) K).val := by
    intro X hX
    have h1 := commute_of_uProj_commute (by omega)
      (show uW K k f X * uW K k f X = 1 by rw [← map_mul, hX, map_one]) (hx _ ⟨X, rfl⟩)
    have h2 := congrArg (fun y : StatedSU (2 + k) (2 ^ f) K => (y : GL (Fin (2 + k)) K).val) h1
    simpa only [Subgroup.coe_mul, Units.val_mul, coe_uW] using h2
  have e1 := hc J (mul_self_eq_one_of_val hJ swapM_mul_swapM)
  have e2 := hc J' (mul_self_eq_one_of_val hJ' (twJ_mul_twJ hζ0))
  rw [hJ] at e1
  rw [hJ'] at e2
  obtain ⟨M₁, D, hgM⟩ := eq_blk_of_mul_eq e1 e2 (det_swapM_sub_twJ hζ1) (det_swapM_sub_twJ hζ1)
  rw [hgM, blk_mul, blk_mul] at e1 e2
  refine ⟨M₁ 0 0, D, ?_⟩
  rw [hgM, ← eq_smul_one_of_commute_twJ hζ0 hζ1 (blk_injective e1).1 (blk_injective e2).1]

variable (h : UnitaryFieldData 2 f K)
include h

omit [CharP K 2] in
theorem conj_mem_range_uL {g : StatedSU (2 + k) (2 ^ f) K} {X : Matrix (Fin 2) (Fin 2) K}
    {D : Matrix (Fin k) (Fin k) K} (hg : (g : GL (Fin (2 + k)) K).val = blk X D)
    (S : StatedSU k (2 ^ f) K) : g * uL K k f S * g⁻¹ ∈ (uL K k f).range := by
  obtain ⟨hgi, hX, -, -, -⟩ := inv_val_of_blk hg
  refine mem_range_uL_of h (S := D * (S : GL (Fin k) K).val * D⁻¹) ?_
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul, Units.val_mul, hg, hgi,
    coe_uL, blk_mul, blk_mul, Matrix.mul_one, hX]

omit [CharP K 2] in
theorem conj_mem_range_uW {g : StatedSU (2 + k) (2 ^ f) K} {X : Matrix (Fin 2) (Fin 2) K}
    {D : Matrix (Fin k) (Fin k) K} (hg : (g : GL (Fin (2 + k)) K).val = blk X D)
    (S : StatedSU 2 (2 ^ f) K) : g * uW K k f S * g⁻¹ ∈ (uW K k f).range := by
  obtain ⟨hgi, -, -, hD, -⟩ := inv_val_of_blk hg
  refine mem_range_uW_of h (X := X * (S : GL (Fin 2) K).val * X⁻¹) ?_
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul, Units.val_mul, hg, hgi,
    coe_uW, blk_mul, blk_mul, Matrix.mul_one, hD]

omit [CharP K 2] in
theorem uProj_mem_normalizer_uBarL {g : StatedSU (2 + k) (2 ^ f) K} {X : Matrix (Fin 2) (Fin 2) K}
    {D : Matrix (Fin k) (Fin k) K} (hg : (g : GL (Fin (2 + k)) K).val = blk X D) :
    uProj K (2 + k) f g ∈
      normalizer (uBarL K k f : Set (StatedProj (StatedSU (2 + k) (2 ^ f) K))) := by
  have key : ∀ {g' : StatedSU (2 + k) (2 ^ f) K} {X' : Matrix (Fin 2) (Fin 2) K}
      {D' : Matrix (Fin k) (Fin k) K}, (g' : GL (Fin (2 + k)) K).val = blk X' D' →
      ∀ y ∈ uBarL K k f, uProj K (2 + k) f g' * y * (uProj K (2 + k) f g')⁻¹ ∈ uBarL K k f := by
    rintro g' X' D' hg' _ ⟨S, rfl⟩
    obtain ⟨S', hS'⟩ := conj_mem_range_uL h hg' S
    refine ⟨S', ?_⟩
    simp only [MonoidHom.comp_apply]
    rw [hS', map_mul, map_mul, map_inv]
  obtain ⟨hgi, -⟩ := inv_val_of_blk hg
  refine mem_normalizer_iff.mpr fun y => ⟨key hg y, fun hy => ?_⟩
  have h1 := key (g' := g⁻¹) (by rw [Subgroup.coe_inv]; exact hgi) _ hy
  rwa [map_inv, inv_inv, show (uProj K (2 + k) f g)⁻¹ * (uProj K (2 + k) f g * y *
    (uProj K (2 + k) f g)⁻¹) * uProj K (2 + k) f g = y by group] at h1

omit [CharP K 2] in
theorem uProj_mem_normalizer_uBarW {g : StatedSU (2 + k) (2 ^ f) K} {X : Matrix (Fin 2) (Fin 2) K}
    {D : Matrix (Fin k) (Fin k) K} (hg : (g : GL (Fin (2 + k)) K).val = blk X D) :
    uProj K (2 + k) f g ∈
      normalizer (uBarW K k f : Set (StatedProj (StatedSU (2 + k) (2 ^ f) K))) := by
  have key : ∀ {g' : StatedSU (2 + k) (2 ^ f) K} {X' : Matrix (Fin 2) (Fin 2) K}
      {D' : Matrix (Fin k) (Fin k) K}, (g' : GL (Fin (2 + k)) K).val = blk X' D' →
      ∀ y ∈ uBarW K k f, uProj K (2 + k) f g' * y * (uProj K (2 + k) f g')⁻¹ ∈ uBarW K k f := by
    rintro g' X' D' hg' _ ⟨S, rfl⟩
    obtain ⟨S', hS'⟩ := conj_mem_range_uW h hg' S
    refine ⟨S', ?_⟩
    simp only [MonoidHom.comp_apply]
    rw [hS', map_mul, map_mul, map_inv]
  obtain ⟨hgi, -⟩ := inv_val_of_blk hg
  refine mem_normalizer_iff.mpr fun y => ⟨key hg y, fun hy => ?_⟩
  have h1 := key (g' := g⁻¹) (by rw [Subgroup.coe_inv]; exact hgi) _ hy
  rwa [map_inv, inv_inv, show (uProj K (2 + k) f g)⁻¹ * (uProj K (2 + k) f g * y *
    (uProj K (2 + k) f g)⁻¹) * uProj K (2 + k) f g = y by group] at h1

omit [CharP K 2] in
theorem commutatorElement_mem_range_uL {g g' : StatedSU (2 + k) (2 ^ f) K}
    {X X' : Matrix (Fin 2) (Fin 2) K} {D D' : Matrix (Fin k) (Fin k) K}
    (hg : (g : GL (Fin (2 + k)) K).val = blk X D) (hg' : (g' : GL (Fin (2 + k)) K).val = blk X' D')
    (hXX : X * X' = X' * X) : ⁅g, g'⁆ ∈ (uL K k f).range := by
  obtain ⟨hgi, hX, -, -, -⟩ := inv_val_of_blk hg
  obtain ⟨hgi', hX', -, -, -⟩ := inv_val_of_blk hg'
  refine mem_range_uL_of h (S := D * D' * D⁻¹ * D'⁻¹) ?_
  rw [commutatorElement_def, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_mul,
    Subgroup.coe_inv, Subgroup.coe_inv, Units.val_mul, Units.val_mul, Units.val_mul, hg, hg', hgi,
    hgi', blk_mul, blk_mul, blk_mul, hXX, Matrix.mul_assoc X' X X⁻¹, hX, Matrix.mul_one, hX']

omit [CharP K 2] in
theorem commutatorElement_mem_range_uW {g g' : StatedSU (2 + k) (2 ^ f) K}
    {X X' : Matrix (Fin 2) (Fin 2) K} {D D' : Matrix (Fin k) (Fin k) K}
    (hg : (g : GL (Fin (2 + k)) K).val = blk X D) (hg' : (g' : GL (Fin (2 + k)) K).val = blk X' D')
    (hDD : D * D' = D' * D) : ⁅g, g'⁆ ∈ (uW K k f).range := by
  obtain ⟨hgi, -, -, hD, -⟩ := inv_val_of_blk hg
  obtain ⟨hgi', -, -, hD', -⟩ := inv_val_of_blk hg'
  refine mem_range_uW_of h (X := X * X' * X⁻¹ * X'⁻¹) ?_
  rw [commutatorElement_def, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_mul,
    Subgroup.coe_inv, Subgroup.coe_inv, Units.val_mul, Units.val_mul, Units.val_mul, hg, hg', hgi,
    hgi', blk_mul, blk_mul, blk_mul, hDD, Matrix.mul_assoc D' D D⁻¹, hD, Matrix.mul_one, hD']

end Centralizer

end CFSG.ComponentClassification.RankTwoClassical
