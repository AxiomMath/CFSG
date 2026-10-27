module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4PSpTU4
public import CFSG.LocalAnalysis.ComponentInitial.OddUnitaryInvolutionSylowInner
public import CFSG.ClassicalInvolution.Q3.TA3LeafQ5Cent

public section

namespace CFSG.ClassicalInvolution.Q3.TA3.Q5U4

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.ComponentClassification.CatFactsL4U4
  CFSG.Assembly.LowTwoRank StabU HBlocks TBlocks PSpL Subgroup UnitaryOut
open scoped commutatorElement

variable {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K)

@[expose] def dOne (t c : K) : Matrix (Fin 2) (Fin 2) K := !![2, t; 2 * c, -(t * c)]

theorem uStar_dOne_mul {t c : K} (hN : h.bar c * c = -1) (ht : h.bar t = -t) :
    ((dOne t c).map h.bar)ᵀ * dOne t c = (4 * t) • jj := by
  have h2' : h.bar 2 = 2 := map_ofNat h.bar 2
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [dOne, jj, Matrix.mul_apply, Fin.sum_univ_two, ht, h2'] <;>
    first
      | linear_combination 4 * hN
      | linear_combination (-2 * t) * hN
      | linear_combination (2 * t) * hN
      | linear_combination (-t ^ 2) * hN

theorem uStar_bd_dOne {t c : K} (hN : h.bar c * c = -1) (ht : h.bar t = -t) :
    uStar h (bd (dOne t c) (dOne t c)) * bd (dOne t c) (dOne t c) = (4 * t) • bJ 1 1 := by
  have hb : (4 * t) • bJ (1 : K) 1 = bJ (4 * t) (4 * t) := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [bJ]
  rw [uStar, map_bd, transpose_bd, bd_mul, uStar_dOne_mul h hN ht, bd_eq_bJ, hb]

include h in
theorem exists_frame_t2 (hp2 : p ≠ 2) (X : unitarySU p f K 4)
    (hXX : ((X : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) * (X : GL (Fin 4) K) = 1)
    (h1 : ((X : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) ≠ 1)
    (hm1 : ((X : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) ≠ -1) :
    ∃ (R : GL (Fin 4) K) (t : K), t ≠ 0 ∧ h.bar t = -t ∧
      uStar h (R : Matrix (Fin 4) (Fin 4) K) * (R : Matrix (Fin 4) (Fin 4) K) = t • bJ 1 1 ∧
      ((X : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) * (R : Matrix (Fin 4) (Fin 4) K) =
        (R : Matrix (Fin 4) (Fin 4) K) * X1 (1 : K) := by
  classical
  have : Finite K := h.finite
  have h2K : (2 : K) ≠ 0 := two_ne_zero_of_odd h hp2
  obtain ⟨Q, hQu, hXQ⟩ := exists_orthonormal_eigenframe h hp2 X hXX h1 hm1
  obtain ⟨c, hc⟩ := OddUnitaryInvolutionSylow.exists_norm_eq_neg_one h
  have hN : h.bar c * c = -1 := by rw [mul_comm]; exact hc
  obtain ⟨μ, hμ⟩ := IsCyclic.exists_generator (α := Kˣ)
  set t : K := (μ : K) - h.bar μ with htdef
  have ht : h.bar t = -t := by
    rw [htdef, map_sub, h.bar_bar]
    ring
  have ht0 : t ≠ 0 := sub_ne_zero.2 (Ne.symm (bar_ne_of_generator h hμ))
  have h4K : (4 : K) ≠ 0 := by
    rw [show (4 : K) = 2 * 2 by norm_num]
    exact mul_ne_zero h2K h2K
  have ht4 : h.bar (4 * t) = -(4 * t) := by
    rw [map_mul, map_ofNat, ht, mul_neg]
  have ht40 : 4 * t ≠ 0 := mul_ne_zero h4K ht0
  set D := bd (dOne t c) (dOne t c) with hD
  have hDD := uStar_bd_dOne h hN ht
  have hR1 : uStar h (Q * D) * (Q * D) = (4 * t) • bJ 1 1 := by
    rw [uStar_mul]
    calc uStar h D * uStar h Q * (Q * D) = uStar h D * (uStar h Q * Q) * D := by
          simp only [Matrix.mul_assoc]
      _ = (4 * t) • bJ 1 1 := by rw [hQu, Matrix.mul_one, hDD]
  have hdet : (Q * D).det ≠ 0 := by
    intro h0
    have := congrArg Matrix.det hR1
    rw [det_mul, h0, mul_zero, det_smul, det_bJ, Fintype.card_fin] at this
    simp at this
    exact ht40 (pow_eq_zero_iff (by norm_num) |>.1 this.symm)
  refine ⟨GeneralLinearGroup.mkOfDetNeZero (Q * D) hdet, 4 * t, ht40, ht4, ?_, ?_⟩
  · rw [GeneralLinearGroup.val_mkOfDetNeZero]
    exact hR1
  · rw [GeneralLinearGroup.val_mkOfDetNeZero, ← Matrix.mul_assoc, hXQ, Matrix.mul_assoc,
      Matrix.mul_assoc, ← bd_comm_X1]

variable {R : GL (Fin 4) K} {t : K}
  (hR : uStar h (R : Matrix (Fin 4) (Fin 4) K) * (R : Matrix (Fin 4) (Fin 4) K) = t • bJ 1 1)

theorem range_bdHomU_le_centralizer {X : unitarySU p f K 4}
    (hXR : ((X : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) * (R : Matrix (Fin 4) (Fin 4) K) =
      (R : Matrix (Fin 4) (Fin 4) K) * X1 (1 : K)) :
    ((QuotientGroup.mk' (scal p f K)).comp (bdHomU h hR)).range ≤
      centralizer {QuotientGroup.mk' (scal p f K) X} := by
  rintro _ ⟨x, rfl⟩
  rw [mem_centralizer_singleton_iff, MonoidHom.comp_apply, ← map_mul, ← map_mul,
    bdHomU_comm h hR hXR x]

theorem isPerfect_range_bdHomU (h4 : 4 ≤ p ^ f) :
    Group.IsPerfect ((QuotientGroup.mk' (scal p f K)).comp (bdHomU h hR)).range := by
  classical
  have : Finite K := h.finite
  let := Fintype.ofFinite h.fixedField
  have hc : 4 ≤ Fintype.card h.fixedField := by
    rw [← Nat.card_eq_fintype_card, h.card_fixedField]
    exact h4
  rw [Subgroup.isPerfect_iff, MonoidHom.range_eq_map, ← map_commutator, commutator_top_prod hc]

theorem le_map_range_of_blockDet {L A : Type*} [Group L] [CommGroup A]
    (ψ : L →* unitarySU p f K 4) {X : unitarySU p f K 4}
    (δ : centralizer ({X} : Set (unitarySU p f K 4)) →* A)
    (hδ : ∀ c, δ c = 1 → (c : unitarySU p f K 4) ∈ ψ.range)
    {M : Subgroup (StatedProj (StatedSU 4 (p ^ f) K))}
    (hM : M ≤ centralizer {QuotientGroup.mk' (scal p f K) X}) (hMp : ⁅M, M⁆ = M) :
    M ≤ ((QuotientGroup.mk' (scal p f K)).comp ψ).range := by
  classical
  set θ := QuotientGroup.mk' (scal p f K) with hθ
  have hrange : (θ.comp ψ).range = ψ.range.map θ := by
    rw [MonoidHom.range_comp]
  have hsc : scal p f K ≤ center (unitarySU p f K 4) := fun z hz => mem_center_of_mem_scal hz
  have hC1 : ⁅centralizer {θ X}, centralizer {θ X}⁆ ≤
      (centralizer ({X} : Set (unitarySU p f K 4))).map θ := by
    rw [commutator_le]
    intro u hu v hv
    obtain ⟨U, rfl⟩ := QuotientGroup.mk'_surjective (scal p f K) u
    obtain ⟨V, rfl⟩ := QuotientGroup.mk'_surjective (scal p f K) v
    refine ⟨⁅U, V⁆, ?_, by rw [map_commutatorElement]⟩
    have hmem : ∀ Z : unitarySU p f K 4, θ Z ∈ centralizer {θ X} →
        Z * X * Z⁻¹ * X⁻¹ ∈ scal p f K := by
      intro Z hZ
      rw [mem_centralizer_singleton_iff] at hZ
      have h1 : θ (Z * X * Z⁻¹ * X⁻¹) = 1 := by
        rw [map_mul, map_mul, map_mul, map_inv, map_inv, hZ]
        group
      rwa [hθ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    rw [SetLike.mem_coe, mem_centralizer_singleton_iff]
    exact commutator_comm_of_comm_mod hsc (hmem U hu) (hmem V hv)
  have hC2 : ⁅centralizer ({X} : Set (unitarySU p f K 4)),
      centralizer ({X} : Set (unitarySU p f K 4))⁆ ≤ ψ.range := by
    rw [commutator_le]
    intro a ha b hb
    have : δ ⁅(⟨a, ha⟩ : centralizer ({X} : Set (unitarySU p f K 4))), ⟨b, hb⟩⁆ = 1 := by
      rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
      exact mul_comm _ _
    exact hδ _ this
  have hM2 : M = ⁅⁅M, M⁆, ⁅M, M⁆⁆ := by rw [hMp, hMp]
  rw [hM2, hrange]
  calc ⁅⁅M, M⁆, ⁅M, M⁆⁆ ≤ ⁅⁅centralizer {θ X}, centralizer {θ X}⁆,
        ⁅centralizer {θ X}, centralizer {θ X}⁆⁆ :=
        commutator_mono (commutator_mono hM hM) (commutator_mono hM hM)
    _ ≤ ⁅(centralizer ({X} : Set (unitarySU p f K 4))).map θ,
        (centralizer ({X} : Set (unitarySU p f K 4))).map θ⁆ := commutator_mono hC1 hC1
    _ = (⁅centralizer ({X} : Set (unitarySU p f K 4)),
        centralizer ({X} : Set (unitarySU p f K 4))⁆).map θ := (map_commutator _ _ _).symm
    _ ≤ ψ.range.map θ := map_mono hC2

include h in
theorem le_range_bdHomU_of_perfect (hp2 : p ≠ 2) (ht0 : t ≠ 0) {X : unitarySU p f K 4}
    (hXR : ((X : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) * (R : Matrix (Fin 4) (Fin 4) K) =
      (R : Matrix (Fin 4) (Fin 4) K) * X1 (1 : K))
    {M : Subgroup (StatedProj (StatedSU 4 (p ^ f) K))}
    (hM : M ≤ centralizer {QuotientGroup.mk' (scal p f K) X}) (hMp : ⁅M, M⁆ = M) :
    M ≤ ((QuotientGroup.mk' (scal p f K)).comp (bdHomU h hR)).range := by
  obtain ⟨δ, hδ⟩ := exists_blockDetU h hp2 ht0 hR hXR
  exact le_map_range_of_blockDet (bdHomU h hR) δ hδ hM hMp

include h in
theorem noOddNormal_range_bdHomU (hp2 : p ≠ 2) :
    NoOddNormal ((QuotientGroup.mk' (scal p f K)).comp (bdHomU h hR)).range := by
  classical
  have : Finite K := h.finite
  have hK : GorensteinWalter.IsOddPrimePower (Nat.card h.fixedField) :=
    ⟨p, f, h.prime, h.prime.odd_of_ne_two hp2, h.one_le, h.card_fixedField⟩
  intro M hMH hMn hMo
  refine eq_bot_of_odd_block hK ((QuotientGroup.mk' (scal p f K)).comp (bdHomU h hR))
    (fun x hx => mem_center_of_ker_bdHomU h hR hx) M hMH (fun g hg r hr => ?_) hMo
  have := hMn.conj_mem ⟨r, hMH hr⟩ (Subgroup.mem_subgroupOf.mpr hr) ⟨g, hg⟩
  rw [Subgroup.mem_subgroupOf] at this
  simpa using this

end CFSG.ClassicalInvolution.Q3.TA3.Q5U4
