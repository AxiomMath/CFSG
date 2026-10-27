module

public import CFSG.Fischer.Classification.Unitary.Coords

public section

namespace CFSG.LargeExtraspecial.AS35QTh

open Matrix CFSG.LieType.Universal.Unitary CFSG.ClassicalGroups.Unitary
  CFSG.Fischer.Classification.Unitary
open CFSG.Blueprint.Fischer (K)

@[expose] noncomputable def uLin (d : Fin 3 → K) (β : K) :
    (Fin (3 + 2) → K) →ₗ[K] (Fin (3 + 2) → K) :=
  LinearMap.id + (β • hermL frob (v₀ 3) + hermL frob (ι 3 d)).smulRight (v₀ 3) +
    (hermL frob (v₀ 3)).smulRight (ι 3 d)

theorem uLin_apply (d : Fin 3 → K) (β : K) (x : Fin (3 + 2) → K) :
    uLin d β x = x + (β * herm frob (v₀ 3) x + herm frob (ι 3 d) x) • v₀ 3 +
      herm frob (v₀ 3) x • ι 3 d := by
  simp only [uLin, LinearMap.add_apply, LinearMap.id_apply, LinearMap.smulRight_apply,
    LinearMap.smul_apply, hermL_apply, smul_eq_mul]

theorem herm_v₀_uLin (d : Fin 3 → K) (β : K) (x : Fin (3 + 2) → K) :
    herm frob (v₀ 3) (uLin d β x) = herm frob (v₀ 3) x := by
  rw [uLin_apply, herm_add_right, herm_add_right, herm_smul_right, herm_smul_right, herm_v₀_v₀,
    herm_v₀_ι, mul_zero, mul_zero, add_zero, add_zero]

theorem herm_ι_uLin (e d : Fin 3 → K) (β : K) (x : Fin (3 + 2) → K) :
    herm frob (ι 3 e) (uLin d β x) =
      herm frob (ι 3 e) x + herm frob (v₀ 3) x * herm frob e d := by
  rw [uLin_apply, herm_add_right, herm_add_right, herm_smul_right, herm_smul_right, herm_ι_v₀,
    herm_ι_ι, mul_zero, add_zero]

theorem uLin_comp (d d' : Fin 3 → K) (β β' : K) :
    (uLin d β).comp (uLin d' β') = uLin (d + d') (β + β' + herm frob d d') := by
  refine LinearMap.ext fun x => ?_
  rw [LinearMap.comp_apply, uLin_apply d β, herm_v₀_uLin, herm_ι_uLin, uLin_apply d' β',
    uLin_apply, map_add, herm_add_left]
  module

theorem uLin_zero : uLin 0 0 = LinearMap.id := by
  refine LinearMap.ext fun x => ?_
  rw [uLin_apply, map_zero, herm_zero_left, zero_mul, add_zero, zero_smul, add_zero, smul_zero,
    add_zero, LinearMap.id_apply]

theorem two_smul_vec {m : ℕ} (v : Fin m → K) : v + v = 0 := by
  funext i
  exact add_self_K _

theorem herm_uLin {d : Fin 3 → K} {β : K} (hβ : β + frob β = herm frob d d)
    (x y : Fin (3 + 2) → K) : herm frob (uLin d β x) (uLin d β y) = herm frob x y := by
  rw [uLin_apply, uLin_apply]
  simp only [herm_add_left, herm_add_right, herm_smul_left, herm_smul_right, herm_v₀_v₀,
    herm_v₀_ι, herm_ι_v₀, herm_ι_ι, map_add, map_mul]
  rw [herm_conj frob frob_frob (v₀ 3) x, herm_conj frob frob_frob (ι 3 d) x]
  linear_combination (frob (herm frob (v₀ 3) x) * herm frob (v₀ 3) y) * hβ +
    (frob (herm frob (v₀ 3) x) * herm frob (ι 3 d) y +
      herm frob (v₀ 3) y * frob (herm frob (ι 3 d) x) +
      frob (herm frob (v₀ 3) x) * herm frob (v₀ 3) y * herm frob d d) * two_eq_zero

@[expose] noncomputable def Umat (d : Fin 3 → K) (β : K) : Matrix (Fin (3 + 2)) (Fin (3 + 2)) K :=
  LinearMap.toMatrix' (uLin d β)

theorem Umat_mulVec (d : Fin 3 → K) (β : K) (x : Fin (3 + 2) → K) :
    Umat d β *ᵥ x = uLin d β x :=
  LinearMap.toMatrix'_mulVec _ _

theorem Umat_mul (d d' : Fin 3 → K) (β β' : K) :
    Umat d β * Umat d' β' = Umat (d + d') (β + β' + herm frob d d') := by
  rw [Umat, Umat, Umat, ← LinearMap.toMatrix'_comp, uLin_comp]

theorem Umat_zero : Umat 0 0 = 1 := by
  rw [Umat, uLin_zero, LinearMap.toMatrix'_id]

theorem Umat_sq (d : Fin 3 → K) (β : K) : Umat d β * Umat d β = Umat 0 (herm frob d d) := by
  rw [Umat_mul, two_smul_vec, add_self_K, zero_add]

theorem Umat_pow_four (d : Fin 3 → K) (β : K) : Umat d β ^ 4 = 1 := by
  rw [show Umat d β ^ 4 = (Umat d β * Umat d β) * (Umat d β * Umat d β) by
    rw [pow_succ, pow_succ, pow_succ, pow_one, Matrix.mul_assoc, Matrix.mul_assoc],
    Umat_sq, Umat_mul, add_zero, add_self_K, herm_zero_left, add_zero, Umat_zero]

theorem pow_four_K (c : K) : c ^ 4 = c := by
  classical
  have := Fintype.ofFinite K
  have hc : Fintype.card K = 4 := by
    rw [← Nat.card_eq_fintype_card, card_K]
    norm_num
  rw [← hc]
  exact FiniteField.pow_card c

theorem det_Umat (d : Fin 3 → K) (β : K) : (Umat d β).det = 1 := by
  have h := congrArg Matrix.det (Umat_pow_four d β)
  rw [Matrix.det_pow, Matrix.det_one, pow_four_K] at h
  exact h

@[expose] noncomputable def Usu (d : Fin 3 → K) (β : K) (hβ : β + frob β = herm frob d d) :
    SUid frob (3 + 2) :=
  mkSU frob (Umat d β) (det_Umat d β) (fun x y => by
    rw [Umat_mulVec, Umat_mulVec]
    exact herm_uLin hβ x y)

theorem Usu_smul (d : Fin 3 → K) (β : K) (hβ : β + frob β = herm frob d d)
    (x : Fin (3 + 2) → K) : Usu d β hβ • x = uLin d β x := by
  rw [Usu, mkSU_smul, Umat_mulVec]

theorem coe_Usu (d : Fin 3 → K) (β : K) (hβ : β + frob β = herm frob d d) :
    (((Usu d β hβ : SUid frob (3 + 2)) : GL (Fin (3 + 2)) K) :
      Matrix (Fin (3 + 2)) (Fin (3 + 2)) K) = Umat d β := rfl

theorem Usu_mul (d d' : Fin 3 → K) (β β' : K) (hβ : β + frob β = herm frob d d)
    (hβ' : β' + frob β' = herm frob d' d')
    (h'' : β + β' + herm frob d d' + frob (β + β' + herm frob d d') =
      herm frob (d + d') (d + d')) :
    Usu d β hβ * Usu d' β' hβ' = Usu (d + d') (β + β' + herm frob d d') h'' := by
  refine ext_smul _ fun x => ?_
  rw [mul_smul, Usu_smul, Usu_smul, Usu_smul, ← LinearMap.comp_apply, uLin_comp]

theorem herm_one_zero : (1 : K) + frob 1 = herm frob (0 : Fin 3 → K) 0 := by
  rw [herm_zero_left, map_one, add_self_K]

theorem Usu_zero_one : Usu 0 1 herm_one_zero = tvU (v₀ 3) := by
  refine ext_smul _ fun x => ?_
  rw [Usu_smul, uLin_apply, tvU_smul herm_v₀_v₀, map_zero, herm_zero_left, add_zero, one_mul,
    smul_zero, add_zero]

theorem eq_Umat_of_fix {M : Matrix (Fin (3 + 2)) (Fin (3 + 2)) K}
    (hiso : ∀ x y, herm frob (M *ᵥ x) (M *ᵥ y) = herm frob x y) (hv : M *ᵥ v₀ 3 = v₀ 3)
    (hπ : ∀ z, π 3 (M *ᵥ ι 3 z) = z) :
    M = Umat (π 3 (M *ᵥ u₀ 3)) (herm frob (u₀ 3) (M *ᵥ u₀ 3)) := by
  set d := π 3 (M *ᵥ u₀ 3) with hd
  set β := herm frob (u₀ 3) (M *ᵥ u₀ 3) with hβ
  have hvu : herm frob (v₀ 3) (M *ᵥ u₀ 3) = 1 := by
    rw [← hv, hiso, herm_v₀_u₀]
  have hMu : M *ᵥ u₀ 3 = β • v₀ 3 + u₀ 3 + ι 3 d := by
    conv_lhs => rw [decomp (M *ᵥ u₀ 3)]
    rw [hvu, one_smul]
  have hMι : ∀ z, M *ᵥ ι 3 z = herm frob d z • v₀ 3 + ι 3 z := by
    intro z
    have h1 : herm frob (v₀ 3) (M *ᵥ ι 3 z) = 0 := by
      rw [← hv, hiso, herm_v₀_ι]
    have h2 : herm frob (M *ᵥ u₀ 3) (M *ᵥ ι 3 z) = 0 := by
      rw [hiso, herm_u₀_ι]
    have h3 := decomp_of_perp h1
    rw [hπ z] at h3
    rw [h3] at h2
    rw [hMu] at h2
    simp only [herm_add_left, herm_add_right, herm_smul_left, herm_smul_right, herm_v₀_v₀,
      herm_v₀_ι, herm_u₀_v₀, herm_u₀_ι, herm_ι_v₀, herm_ι_ι, mul_zero, mul_one, add_zero,
      zero_add] at h2
    rw [h3]
    congr 1
    have h4 : herm frob (u₀ 3) (M *ᵥ ι 3 z) = -herm frob d z := by
      linear_combination h2
    rw [h4, neg_K]
  refine Matrix.ext_of_mulVec_single fun j => ?_
  set x : Fin (3 + 2) → K := Pi.single j 1
  rw [Umat_mulVec, uLin_apply]
  conv_lhs => rw [decomp x]
  rw [Matrix.mulVec_add, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul, hv, hMu,
    hMι, herm_ι_left]
  conv_rhs => enter [1, 1]; rw [decomp x]
  module

theorem det_eq_one_of_fix {M : Matrix (Fin (3 + 2)) (Fin (3 + 2)) K}
    (hiso : ∀ x y, herm frob (M *ᵥ x) (M *ᵥ y) = herm frob x y) (hv : M *ᵥ v₀ 3 = v₀ 3)
    (hπ : ∀ z, π 3 (M *ᵥ ι 3 z) = z) : M.det = 1 := by
  rw [eq_Umat_of_fix hiso hv hπ, det_Umat]

end CFSG.LargeExtraspecial.AS35QTh
