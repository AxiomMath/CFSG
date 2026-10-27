module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveWModel

public section

namespace CFSG.SeitzReduction.LinearPilot

open Matrix Subgroup CFSG.LocalAnalysis.ComponentInitial

variable {n : ℕ} {K : Type*} [Field K]

theorem pointRadElem_update_eq (c : Fin n) (r : Fin n → K) (a : K) :
    pointRadElem c (Function.update r c a) = pointRadElem c r := by
  apply Subtype.ext
  rw [coe_pointRadElem, coe_pointRadElem, pointRadMat, pointRadMat, Function.update_idem]

theorem pointRadElem_eq_of_update_eq {c : Fin n} {r s : Fin n → K}
    (h : Function.update r c 0 = Function.update s c 0) : pointRadElem c r = pointRadElem c s := by
  rw [← pointRadElem_update_eq c r 0, h, pointRadElem_update_eq]

theorem pointRadMat_apply_row_of_ne (c : Fin n) (r : Fin n → K) {j : Fin n} (hj : j ≠ c) :
    pointRadMat c r c j = r j := by
  rw [pointRadMat_apply, one_apply_ne (Ne.symm hj), ite_eq_left ⟨rfl, hj⟩, zero_add]

theorem update_eq_update_of_pointRadElem_eq {c : Fin n} {r s : Fin n → K}
    (h : pointRadElem c r = pointRadElem c s) :
    Function.update r c 0 = Function.update s c 0 := by
  funext j
  by_cases hj : j = c
  · subst hj
    simp
  · have h1 := congrArg
      (fun A : SpecialLinearGroup (Fin n) K => (A : Matrix (Fin n) (Fin n) K) c j) h
    simp only [coe_pointRadElem] at h1
    rw [pointRadMat_apply_row_of_ne c r hj, pointRadMat_apply_row_of_ne c s hj] at h1
    rw [Function.update_of_ne hj, Function.update_of_ne hj, h1]

theorem proj_pointRadElem_mem_pointRadical (c : Fin n) (r : Fin n → K) :
    LinearFlag.proj n K (pointRadElem c r) ∈ pointRadical (K := K) c := by
  refine ⟨pointRadElem c r, ⟨Function.update r c 0, fun j hj => ?_,
    pointRadElem_update_eq c r 0⟩, rfl⟩
  rw [Finset.mem_compl, Finset.mem_singleton, not_not] at hj
  rw [hj, Function.update_self]

theorem mem_pointRadical_iff_exists_pointRadElem {c : Fin n} {v : LinearFlag.projectiveSL n K} :
    v ∈ pointRadical (K := K) c ↔
      ∃ r : Fin n → K, r c = 0 ∧ LinearFlag.proj n K (pointRadElem c r) = v := by
  constructor
  · rintro ⟨_, ⟨r, hr, rfl⟩, rfl⟩
    exact ⟨r, hr c (by simp), rfl⟩
  · rintro ⟨r, -, rfl⟩
    exact proj_pointRadElem_mem_pointRadical c r

theorem col_eq_single_of_forall_apply_eq_one_apply {c : Fin n} {M : Matrix (Fin n) (Fin n) K}
    (hM : ∀ i, M i c = (1 : Matrix (Fin n) (Fin n) K) i c) : M.col c = Pi.single c 1 := by
  funext i
  change M i c = _
  rw [hM i, one_eq_pi_single, Pi.single_comm]

theorem mul_pointRadMat_mul_of_col_eq {c : Fin n} {B B' : Matrix (Fin n) (Fin n) K}
    (h : B * B' = 1) (hB : ∀ i, B i c = (1 : Matrix (Fin n) (Fin n) K) i c)
    (hB' : ∀ i, B' i c = (1 : Matrix (Fin n) (Fin n) K) i c) (r : Fin n → K) :
    B * pointRadMat c r * B' = pointRadMat c (Function.update r c 0 ᵥ* B') := by
  have hBc : B *ᵥ Pi.single c 1 = Pi.single c 1 := by
    rw [mulVec_single_one, col_eq_single_of_forall_apply_eq_one_apply hB]
  have hc : (Function.update r c 0 ᵥ* B') c = 0 := by
    rw [vecMul_apply, col_eq_single_of_forall_apply_eq_one_apply hB', dotProduct_single,
      Function.update_self, zero_mul]
  have hupd : Function.update (Function.update r c 0 ᵥ* B') c 0 = Function.update r c 0 ᵥ* B' :=
    Function.update_eq_self_iff.2 hc.symm
  unfold pointRadMat
  rw [hupd, Matrix.mul_add, Matrix.mul_one, Matrix.add_mul, h, mul_vecMulVec, hBc, vecMulVec_mul]

theorem conj_pointRadElem_of_mem_blockSpecialLinear {c : Fin n} {B : SpecialLinearGroup (Fin n) K}
    (hB : B ∈ blockSpecialLinear ({c}ᶜ : Finset (Fin n))) (r : Fin n → K) :
    B * pointRadElem c r * B⁻¹ = pointRadElem c (Function.update r c 0 ᵥ*
      ((B⁻¹ : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K)) := by
  have hcol : ∀ A ∈ blockSpecialLinear (K := K) ({c}ᶜ : Finset (Fin n)), ∀ i,
      (A : Matrix (Fin n) (Fin n) K) i c = (1 : Matrix (Fin n) (Fin n) K) i c :=
    fun A hA i => hA i c (Or.inr (by simp))
  apply Subtype.ext
  rw [SpecialLinearGroup.coe_mul, SpecialLinearGroup.coe_mul, coe_pointRadElem, coe_pointRadElem]
  exact mul_pointRadMat_mul_of_col_eq
    (by rw [← SpecialLinearGroup.coe_mul, mul_inv_cancel, SpecialLinearGroup.coe_one])
    (hcol B hB) (hcol _ (inv_mem hB)) r

theorem blockSL_compl_le_normalizer_pointRadical (c : Fin n) :
    blockSL (K := K) ({c}ᶜ : Finset (Fin n)) ≤
      normalizer (pointRadical (K := K) c : Set (LinearFlag.projectiveSL n K)) := by
  rw [le_normalizer_iff]
  rintro _ hl v hv
  obtain ⟨B, hB, rfl⟩ := mem_blockSL.1 hl
  obtain ⟨r, -, rfl⟩ := mem_pointRadical_iff_exists_pointRadElem.1 hv
  rw [← map_inv (LinearFlag.proj n K), ← map_mul, ← map_mul,
    conj_pointRadElem_of_mem_blockSpecialLinear hB]
  exact proj_pointRadElem_mem_pointRadical c _

theorem exists_mem_blockSL_conj_proj_pointRadElem {c : Fin n} {N : Matrix (Fin n) (Fin n) K}
    (hdet : N.det = 1) (hcol : ∀ i, N i c = (1 : Matrix (Fin n) (Fin n) K) i c)
    (hrow : ∀ j, N c j = (1 : Matrix (Fin n) (Fin n) K) c j) :
    ∃ l ∈ blockSL (K := K) ({c}ᶜ : Finset (Fin n)), ∀ r : Fin n → K,
      l * LinearFlag.proj n K (pointRadElem c r) * l⁻¹ =
        LinearFlag.proj n K (pointRadElem c (Function.update r c 0 ᵥ* N)) := by
  set A : SpecialLinearGroup (Fin n) K := ⟨N, hdet⟩ with hA
  have hAmem : A ∈ blockSpecialLinear (K := K) ({c}ᶜ : Finset (Fin n)) := by
    intro i j hij
    simp only [Finset.mem_compl, Finset.mem_singleton, not_not] at hij
    rcases hij with rfl | rfl
    · exact hrow j
    · exact hcol i
  refine ⟨LinearFlag.proj n K A⁻¹, proj_mem_blockSL (inv_mem hAmem), fun r => ?_⟩
  rw [← map_inv (LinearFlag.proj n K), ← map_mul, ← map_mul,
    conj_pointRadElem_of_mem_blockSpecialLinear (inv_mem hAmem), inv_inv]

theorem exists_dotProduct_eq_one_and_eq_one_of_natCard_eq_two (hK : Nat.card K = 2) {c : Fin n}
    {r s : Fin n → K} (hr : r ≠ 0) (hs : s ≠ 0) (hrc : r c = 0) (hsc : s c = 0) :
    ∃ a : Fin n → K, a c = 0 ∧ r ⬝ᵥ a = 1 ∧ s ⬝ᵥ a = 1 := by
  have h01 := eq_zero_or_eq_one_of_natCard_eq_two hK
  obtain ⟨i, hi⟩ := Function.ne_iff.1 hr
  obtain ⟨j, hj⟩ := Function.ne_iff.1 hs
  have hri : r i = 1 := (h01 (r i)).resolve_left hi
  have hsj : s j = 1 := (h01 (s j)).resolve_left hj
  have hic : c ≠ i := by
    rintro rfl
    exact hi hrc
  have hjc : c ≠ j := by
    rintro rfl
    exact hj hsc
  by_cases hsi : s i = 1
  · exact ⟨Pi.single i 1, Pi.single_eq_of_ne hic 1, by rw [dotProduct_single, hri, mul_one],
      by rw [dotProduct_single, hsi, mul_one]⟩
  have hsi0 : s i = 0 := (h01 (s i)).resolve_right hsi
  by_cases hrj : r j = 1
  · exact ⟨Pi.single j 1, Pi.single_eq_of_ne hjc 1, by rw [dotProduct_single, hrj, mul_one],
      by rw [dotProduct_single, hsj, mul_one]⟩
  have hrj0 : r j = 0 := (h01 (r j)).resolve_right hrj
  refine ⟨Pi.single i 1 + Pi.single j 1, ?_, ?_, ?_⟩
  · rw [Pi.add_apply, Pi.single_eq_of_ne hic, Pi.single_eq_of_ne hjc, add_zero]
  · rw [dotProduct_add, dotProduct_single, dotProduct_single, hri, hrj0, mul_one, zero_mul,
      add_zero]
  · rw [dotProduct_add, dotProduct_single, dotProduct_single, hsi0, hsj, zero_mul, one_mul,
      zero_add]

theorem exists_det_eq_one_vecMul_eq_of_natCard_eq_two (hK : Nat.card K = 2) {c : Fin n}
    {r s : Fin n → K} (hr : r ≠ 0) (hs : s ≠ 0) (hrc : r c = 0) (hsc : s c = 0) :
    ∃ N : Matrix (Fin n) (Fin n) K, N.det = 1 ∧
      (∀ i, N i c = (1 : Matrix (Fin n) (Fin n) K) i c) ∧
      (∀ j, N c j = (1 : Matrix (Fin n) (Fin n) K) c j) ∧ r ᵥ* N = s := by
  obtain ⟨a, hac, hra, hsa⟩ :=
    exists_dotProduct_eq_one_and_eq_one_of_natCard_eq_two hK hr hs hrc hsc
  refine ⟨1 + vecMulVec a (s - r), ?_, fun i => ?_, fun j => ?_, ?_⟩
  · rw [vecMulVec_eq Unit, det_one_add_replicateCol_mul_replicateRow, sub_dotProduct, hsa, hra,
      sub_self, add_zero]
  · rw [Matrix.add_apply, vecMulVec_apply, Pi.sub_apply, hsc, hrc, sub_self, mul_zero, add_zero]
  · rw [Matrix.add_apply, vecMulVec_apply, hac, zero_mul, add_zero]
  · rw [vecMul_add, vecMul_one, vecMul_vecMulVec, hra, one_smul, add_sub_cancel]

theorem exists_mem_blockSL_conj_eq_of_mem_pointRadical (hK : Nat.card K = 2) (c : Fin n)
    {v w : LinearFlag.projectiveSL n K} (hv : v ∈ pointRadical (K := K) c)
    (hw : w ∈ pointRadical (K := K) c) (hv1 : v ≠ 1) (hw1 : w ≠ 1) :
    ∃ l ∈ blockSL (K := K) ({c}ᶜ : Finset (Fin n)), l * v * l⁻¹ = w := by
  obtain ⟨r, hrc, rfl⟩ := mem_pointRadical_iff_exists_pointRadElem.1 hv
  obtain ⟨s, hsc, rfl⟩ := mem_pointRadical_iff_exists_pointRadElem.1 hw
  have hr : r ≠ 0 := by
    rintro rfl
    exact hv1 (by rw [pointRadElem_zero, map_one])
  have hs : s ≠ 0 := by
    rintro rfl
    exact hw1 (by rw [pointRadElem_zero, map_one])
  obtain ⟨N, hdet, hcol, hrow, hrN⟩ :=
    exists_det_eq_one_vecMul_eq_of_natCard_eq_two hK hr hs hrc hsc
  obtain ⟨l, hl, hlr⟩ := exists_mem_blockSL_conj_proj_pointRadElem hdet hcol hrow
  exact ⟨l, hl, by rw [hlr, Function.update_eq_self_iff.2 hrc.symm, hrN]⟩

theorem exists_matrix_vecMul_of_monoidHom_pointRadical (hK : Nat.card K = 2) (c : Fin n)
    (f : pointRadical (K := K) c →* pointRadical (K := K) c) :
    ∃ N : Matrix (Fin n) (Fin n) K, (∀ i, N i c = (1 : Matrix (Fin n) (Fin n) K) i c) ∧
      (∀ j, N c j = (1 : Matrix (Fin n) (Fin n) K) c j) ∧
      ∀ r : Fin n → K, r c = 0 →
        LinearFlag.proj n K (pointRadElem c (r ᵥ* N)) =
          (f ⟨_, proj_pointRadElem_mem_pointRadical c r⟩ : LinearFlag.projectiveSL n K) := by
  classical
  set ψ : (Fin n → K) → pointRadical (K := K) c :=
    fun r => ⟨_, proj_pointRadElem_mem_pointRadical c r⟩ with hψ
  have hψmul : ∀ r s, ψ (r + s) = ψ r * ψ s := fun r s =>
    Subtype.ext (by simp only [hψ, Subgroup.coe_mul, ← map_mul, pointRadElem_mul])
  have hψupd : ∀ r s, Function.update r c 0 = Function.update s c 0 → ψ r = ψ s := fun r s h =>
    Subtype.ext (by simp only [hψ, pointRadElem_eq_of_update_eq h])
  have hψ0 : ψ 0 = 1 := Subtype.ext (by
    show LinearFlag.proj n K (pointRadElem c 0) = 1
    rw [pointRadElem_zero, map_one])
  set coord : LinearFlag.projectiveSL n K → Fin n → K := fun v =>
    Function.update (((Function.surjInv (LinearFlag.proj_surjective n K) v :
      SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) c) c 0 with hcoord
  have hcoordc : ∀ v, coord v c = 0 := fun v => Function.update_self _ _ _
  have hcoordψ : ∀ r, coord (ψ r) = Function.update r c 0 := by
    intro r
    have hlift : Function.surjInv (LinearFlag.proj_surjective n K)
        (LinearFlag.proj n K (pointRadElem c r)) = pointRadElem c r :=
      proj_injective_of_natCard_eq_two hK (Function.surjInv_eq _ _)
    simp only [hcoord, hψ, hlift, coe_pointRadElem]
    funext j
    by_cases hj : j = c
    · rw [hj, Function.update_self, Function.update_self]
    · rw [Function.update_of_ne hj, Function.update_of_ne hj, pointRadMat_apply_row_of_ne c r hj]
  have hψcoord : ∀ v : pointRadical (K := K) c, ψ (coord v) = v := by
    intro v
    obtain ⟨r, -, hr⟩ := mem_pointRadical_iff_exists_pointRadElem.1 v.2
    have hv : ψ r = v := Subtype.ext hr
    rw [← hv, hcoordψ]
    exact hψupd _ _ (Function.update_idem _ _ _)
  have hcoordmul : ∀ x y : pointRadical (K := K) c,
      coord ((x * y : pointRadical (K := K) c) : LinearFlag.projectiveSL n K) =
        coord x + coord y := by
    intro x y
    obtain ⟨a, rfl⟩ : ∃ a, ψ a = x := ⟨_, hψcoord x⟩
    obtain ⟨b, rfl⟩ : ∃ b, ψ b = y := ⟨_, hψcoord y⟩
    rw [← hψmul, hcoordψ, hcoordψ, hcoordψ]
    funext j
    by_cases hj : j = c
    · rw [hj, Pi.add_apply, Function.update_self, Function.update_self, Function.update_self,
        add_zero]
    · rw [Pi.add_apply, Function.update_of_ne hj, Function.update_of_ne hj,
        Function.update_of_ne hj, Pi.add_apply]
  let φ₀ : (Fin n → K) →+ (Fin n → K) :=
    AddMonoidHom.mk' (fun r => coord (f (ψ r)) + r c • Pi.single c 1) (by
      intro r s
      simp only [hψmul, map_mul, hcoordmul, Pi.add_apply, add_smul]
      abel)
  have hφ₀ : ∀ r, φ₀ r = coord (f (ψ r)) + r c • Pi.single c 1 := fun r => rfl
  let φ : (Fin n → K) →ₗ[K] (Fin n → K) :=
    { toFun := φ₀
      map_add' := φ₀.map_add
      map_smul' := fun a r => by
        rcases eq_zero_or_eq_one_of_natCard_eq_two hK a with rfl | rfl
        · simp
        · simp }
  set N : Matrix (Fin n) (Fin n) K := (LinearMap.toMatrix' φ)ᵀ with hN
  have hNφ : ∀ r, r ᵥ* N = φ₀ r := fun r => by
    rw [hN, vecMul_transpose, LinearMap.toMatrix'_mulVec]
    rfl
  have hNe : ∀ i j, N i j = φ₀ (Pi.single i 1) j := fun i j => by
    rw [← hNφ, single_one_vecMul]
    rfl
  refine ⟨N, fun i => ?_, fun j => ?_, fun r hr => ?_⟩
  · rw [hNe, hφ₀, Pi.add_apply, hcoordc, zero_add, Pi.smul_apply, Pi.single_eq_same, smul_eq_mul,
      mul_one, one_eq_pi_single]
  · have h1 : ψ (Pi.single c 1) = 1 := by
      rw [← hψ0]
      refine hψupd _ _ ?_
      funext k
      by_cases hk : k = c
      · rw [hk, Function.update_self, Function.update_self]
      · rw [Function.update_of_ne hk, Function.update_of_ne hk, Pi.single_eq_of_ne hk,
          Pi.zero_apply]
    have h2 : coord ((1 : pointRadical (K := K) c) : LinearFlag.projectiveSL n K) = 0 := by
      rw [← hψ0, hcoordψ]
      exact Function.update_eq_self c 0
    rw [hNe, hφ₀, h1, map_one, h2, Pi.single_eq_same, one_smul, zero_add, one_eq_pi_single]
  · rw [hNφ, hφ₀, hr, zero_smul, add_zero]
    exact congrArg Subtype.val (hψcoord (f (ψ r)))

theorem exists_mem_blockSL_of_mulEquiv_pointRadical (hK : Nat.card K = 2) (c : Fin n)
    (f : pointRadical (K := K) c ≃* pointRadical (K := K) c) :
    ∃ l ∈ blockSL (K := K) ({c}ᶜ : Finset (Fin n)), ∀ v : pointRadical (K := K) c,
      ((f v : pointRadical (K := K) c) : LinearFlag.projectiveSL n K) = l * v * l⁻¹ := by
  obtain ⟨N, hcol, hrow, hN⟩ :=
    exists_matrix_vecMul_of_monoidHom_pointRadical hK c f.toMonoidHom
  have hinj : Function.Injective N.vecMul := by
    intro r s hrs
    have hrs' : r ᵥ* N = s ᵥ* N := hrs
    have hd : (r - s) ᵥ* N = 0 := by
      rw [sub_vecMul]
      exact sub_eq_zero.2 hrs'
    have hdc : (r - s) c = 0 := by
      have h := congrFun hd c
      rwa [vecMul_apply, col_eq_single_of_forall_apply_eq_one_apply hcol, dotProduct_single,
        mul_one] at h
    have h1 := hN (r - s) hdc
    rw [hd, pointRadElem_zero, map_one] at h1
    have h2 : (⟨_, proj_pointRadElem_mem_pointRadical c (r - s)⟩ : pointRadical (K := K) c) = 1 :=
      f.injective (Subtype.ext (by rw [map_one]; exact h1.symm))
    have h3 : pointRadElem c (r - s) = pointRadElem c 0 :=
      proj_injective_of_natCard_eq_two hK (by
        rw [pointRadElem_zero, map_one]
        exact congrArg Subtype.val h2)
    have h4 := update_eq_update_of_pointRadElem_eq h3
    rw [Function.update_eq_self_iff.2 hdc.symm,
      show Function.update (0 : Fin n → K) c 0 = 0 from Function.update_eq_self c 0] at h4
    exact sub_eq_zero.1 h4
  have hdet : N.det = 1 := by
    have hu : IsUnit N.det := (isUnit_iff_isUnit_det N).1 (vecMul_injective_iff_isUnit.1 hinj)
    exact (eq_zero_or_eq_one_of_natCard_eq_two hK _).resolve_left hu.ne_zero
  obtain ⟨l, hl, hlr⟩ := exists_mem_blockSL_conj_proj_pointRadElem hdet hcol hrow
  refine ⟨l, hl, fun v => ?_⟩
  rcases v with ⟨_, hv⟩
  obtain ⟨r, hrc, rfl⟩ := mem_pointRadical_iff_exists_pointRadElem.1 hv
  show _ = l * LinearFlag.proj n K (pointRadElem c r) * l⁻¹
  rw [hlr, Function.update_eq_self_iff.2 hrc.symm, hN r hrc]
  rfl

theorem eq_one_of_mem_blockSL_of_forall_conj_pointRadical (hK : Nat.card K = 2) (c : Fin n)
    {l : LinearFlag.projectiveSL n K} (hl : l ∈ blockSL (K := K) ({c}ᶜ : Finset (Fin n)))
    (hlv : ∀ v ∈ pointRadical (K := K) c, l * v * l⁻¹ = v) : l = 1 := by
  obtain ⟨B, hB, rfl⟩ := mem_blockSL.1 hl
  have hB' := inv_mem hB
  suffices h : ((B⁻¹ : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1 by
    have h1 : B⁻¹ = 1 := Subtype.ext (h.trans SpecialLinearGroup.coe_one.symm)
    rw [inv_eq_one.1 h1, map_one]
  ext i j
  by_cases hi : i = c
  · exact hB' i j (Or.inl (by simp [hi]))
  by_cases hj : j = c
  · exact hB' i j (Or.inr (by simp [hj]))
  have h1 := hlv _ (proj_pointRadElem_mem_pointRadical c (Pi.single i 1))
  rw [← map_inv (LinearFlag.proj n K), ← map_mul, ← map_mul,
    conj_pointRadElem_of_mem_blockSpecialLinear hB] at h1
  have h2 := congrFun
    (update_eq_update_of_pointRadElem_eq (proj_injective_of_natCard_eq_two hK h1)) j
  have hic : (Pi.single i 1 : Fin n → K) c = 0 := Pi.single_eq_of_ne (Ne.symm hi) 1
  have hupd : Function.update (Pi.single i 1 : Fin n → K) c 0 = Pi.single i 1 :=
    Function.update_eq_self_iff.2 hic.symm
  rw [Function.update_of_ne hj, Function.update_of_ne hj, hupd, single_one_vecMul] at h2
  rw [one_eq_pi_single]
  exact h2

end CFSG.SeitzReduction.LinearPilot
