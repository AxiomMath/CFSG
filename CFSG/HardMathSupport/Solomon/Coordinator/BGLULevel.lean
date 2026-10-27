module

public import CFSG.HardMathSupport.Solomon.Coordinator.BGLUEich

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.BGL

open Matrix CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary

variable {K : Type*} [Field K] {σ : K ≃+* K} {n : ℕ}

theorem eichler_rescale (hσ : ∀ c, σ (σ c) = c) {e e' y : Fin n → K} {c : K} (t : K)
    (ht : e' = t • e) (he' : herm σ e' e' = 0) (hey' : herm σ e' y = 0)
    (hc : c + σ c = -herm σ y y) (he0 : herm σ e e = 0) (hey0 : herm σ e (σ t • y) = 0)
    (hc0 : σ t * t * c + σ (σ t * t * c) = -herm σ (σ t • y) (σ t • y)) :
    eichler hσ he' hey' hc = eichler hσ he0 hey0 hc0 := by
  subst ht
  exact eichler_smul_left hσ t he' hey' hc he0 hey0 hc0

theorem eichler_mul_tv (hσ : ∀ c, σ (σ c) = c) {e y : Fin n → K} (he : herm σ e e = 0)
    (hey : herm σ e y = 0) {c d c' : K} (hc : c + σ c = -herm σ y y) (hd : d + σ d = 0)
    (hc' : c' + σ c' = -herm σ y y) (hcd : c' = c + d) :
    eichler hσ he hey hc * tv hσ he hd = eichler hσ he hey hc' := by
  have hye : herm σ y e = 0 := herm_eq_zero_comm σ hσ hey
  apply ext_smul
  intro x
  rw [mul_smul, tv_smul, eichler_smul, eichler_smul]
  simp only [herm_add_right, herm_smul_right, he, hye, mul_zero, add_zero, hcd]
  match_scalars <;> ring

variable (hσ : ∀ c, σ (σ c) = c) (H : Subgroup (SUid σ n)) {a : Fin n → K}
  (ha : herm σ a a = 0)

variable (σ) in
include hσ in
@[expose] def EichSet : Set (Fin n → K) :=
  {y | ∃ (hey : herm σ a y = 0) (c : K) (hc : c + σ c = -herm σ y y),
    eichler hσ ha hey hc ∈ H}

variable {H} {ha} in
theorem EichSet.mem_all (hXa : ∀ (c : K) (hc : c + σ c = 0), tv hσ ha hc ∈ H) {y : Fin n → K}
    (hy : y ∈ EichSet σ hσ H ha) (hey : herm σ a y = 0) (c' : K)
    (hc' : c' + σ c' = -herm σ y y) : eichler hσ ha hey hc' ∈ H := by
  obtain ⟨hey0, c, hc, hH⟩ := hy
  have hd : (c' - c) + σ (c' - c) = 0 := by
    rw [map_sub]
    linear_combination hc' - hc
  have := eichler_mul_tv hσ ha hey0 hc hd hc' (by ring)
  rw [← this]
  exact H.mul_mem hH (hXa _ hd)

variable {H} {ha} in
theorem EichSet.smul_a_mem (hXa : ∀ (c : K) (hc : c + σ c = 0), tv hσ ha hc ∈ H) (ν : K) :
    ν • a ∈ EichSet σ hσ H ha := by
  have hey : herm σ a (ν • a) = 0 := by rw [herm_smul_right, ha, mul_zero]
  have hc : (0 : K) + σ 0 = -herm σ (ν • a) (ν • a) := by
    rw [herm_smul_left, herm_smul_right, ha, map_zero]
    ring
  have h0 : ((0 : K) + ν - σ ν) + σ ((0 : K) + ν - σ ν) = 0 := by
    rw [map_sub, map_add, map_zero, hσ]
    ring
  refine ⟨hey, 0, hc, ?_⟩
  rw [eichler_self_eq_tv hσ ha ν hey hc h0]
  exact hXa _ h0

variable {H} {ha} in
theorem EichSet.add_mem {y y' : Fin n → K}
    (hy : y ∈ EichSet σ hσ H ha) (hy' : y' ∈ EichSet σ hσ H ha) :
    y + y' ∈ EichSet σ hσ H ha := by
  obtain ⟨hey, c, hc, hH⟩ := hy
  obtain ⟨hey', c', hc', hH'⟩ := hy'
  have hey'' : herm σ a (y + y') = 0 := by rw [herm_add_right, hey, hey', add_zero]
  have hc'' : (c + c' - herm σ y y') + σ (c + c' - herm σ y y') =
      -herm σ (y + y') (y + y') := by
    have e : σ (herm σ y y') = herm σ y' y := (herm_conj σ hσ y y').symm
    rw [map_sub, map_add, e, herm_add_left, herm_add_right, herm_add_right]
    linear_combination hc + hc'
  refine ⟨hey'', c + c' - herm σ y y', hc'', ?_⟩
  rw [← eichler_mul_eichler_add hσ ha hey hey' hey'' hc hc' hc'' rfl]
  exact H.mul_mem hH hH'

variable {H} {ha} in
theorem EichSet.neg_mem {y : Fin n → K}
    (hy : y ∈ EichSet σ hσ H ha) : -y ∈ EichSet σ hσ H ha := by
  obtain ⟨hey, c, hc, hH⟩ := hy
  have hey' : herm σ a (-y) = 0 := by rw [herm_neg_right, hey, neg_zero]
  have hyy : σ (herm σ y y) = herm σ y y := herm_self_fixed σ hσ y
  have hc' : (-c - herm σ y y) + σ (-c - herm σ y y) = -herm σ (-y) (-y) := by
    rw [map_sub, map_neg, hyy, herm_neg_left, herm_neg_right]
    linear_combination -hc
  have hye : herm σ y a = 0 := herm_eq_zero_comm σ hσ hey
  have h1 : eichler hσ ha hey hc * eichler hσ ha hey' hc' = 1 := by
    apply ext_smul
    intro x
    rw [mul_smul, eichler_smul, eichler_smul, one_smul]
    simp only [herm_add_right, herm_sub_right, herm_neg_right, herm_neg_left, herm_smul_right,
      ha, hey, hye, mul_zero, add_zero, sub_zero, neg_zero]
    match_scalars <;> ring
  refine ⟨hey', -c - herm σ y y, hc', ?_⟩
  have : eichler hσ ha hey' hc' = (eichler hσ ha hey hc)⁻¹ := eq_inv_of_mul_eq_one_right h1
  rw [this]
  exact H.inv_mem hH

variable {H} {ha} in
theorem EichSet.conj_mem {g : SUid σ n} (hg : g ∈ H) {t : K} (ht0 : t ≠ 0) (hga : g • a = t • a)
    {y : Fin n → K} (hy : y ∈ EichSet σ hσ H ha) : σ t • (g • y) ∈ EichSet σ hσ H ha := by
  obtain ⟨hey, c, hc, hH⟩ := hy
  have he' : herm σ (g • a) (g • a) = 0 := by rw [herm_smul_smul, ha]
  have hey' : herm σ (g • a) (g • y) = 0 := by rw [herm_smul_smul, hey]
  have hc' : c + σ c = -herm σ (g • y) (g • y) := by rw [herm_smul_smul]; exact hc
  have hconj := mul_eichler_mul_inv hσ g ha hey hc he' hey' hc'
  have hgy : herm σ a (g • y) = 0 := by
    rw [hga, herm_smul_left] at hey'
    exact (mul_eq_zero.mp hey').resolve_left ((map_ne_zero σ).mpr ht0)
  have hey0 : herm σ a (σ t • g • y) = 0 := by rw [herm_smul_right, hgy, mul_zero]
  have hc0 : σ t * t * c + σ (σ t * t * c) =
      -herm σ (σ t • g • y) (σ t • g • y) := by
    rw [herm_smul_left, herm_smul_right, hσ, herm_smul_smul, map_mul, map_mul, hσ]
    linear_combination (σ t * t) * hc
  refine ⟨hey0, σ t * t * c, hc0, ?_⟩
  rw [← eichler_rescale hσ t hga he' hey' hc' ha hey0 hc0, ← hconj]
  exact H.mul_mem (H.mul_mem hg hH) (H.inv_mem hg)

end CFSG.HardMathSupport.Solomon.Coordinator.BGL
