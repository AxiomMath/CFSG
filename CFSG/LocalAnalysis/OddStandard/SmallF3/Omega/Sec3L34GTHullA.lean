module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3L34GTOdd
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3L34GTGen

public section

namespace CFSG.OddStandard.SmallF3.Omega

@[expose] def l34g_oddHull {A C : Type} [Group A] [Group C] (φ : A →* C) (B : Subgroup C) :
    Subgroup A :=
  Subgroup.closure {a : A | φ a ∈ B ∧ Odd (orderOf a)}

theorem l34g_oddHull_le {A C : Type} [Group A] [Group C] (φ : A →* C) (B : Subgroup C) :
    l34g_oddHull φ B ≤ B.comap φ := by
  rw [l34g_oddHull, Subgroup.closure_le]
  intro a ha
  exact ha.1

theorem l34g_oddHull_conj {A C : Type} [Group A] [Group C] (φ : A →* C) (B : Subgroup C) {g : A}
    (hg : φ g ∈ B) {a : A} (ha : a ∈ l34g_oddHull φ B) : g * a * g⁻¹ ∈ l34g_oddHull φ B := by
  induction ha using Subgroup.closure_induction with
  | mem x hx =>
      apply Subgroup.subset_closure
      refine ⟨?_, ?_⟩
      · rw [map_mul, map_mul, map_inv]
        exact B.mul_mem (B.mul_mem hg hx.1) (B.inv_mem hg)
      · have hconj : orderOf (g * x * g⁻¹) = orderOf x :=
          (SemiconjBy.orderOf_eq g (x := x) (y := g * x * g⁻¹) (by
            unfold SemiconjBy; group)).symm
        rw [hconj]
        exact hx.2
  | one => simp
  | mul x y hx hy ihx ihy =>
      convert mul_mem ihx ihy using 1
      group
  | inv x hx ih =>
      convert inv_mem ih using 1
      group

theorem l34g_map_oddHull {A C : Type} [Group A] [Group C] [Finite A] (φ : A →* C)
    (hφ : Function.Surjective φ) {B : Subgroup C} (hB : IsSL23Mod ↥B) :
    (l34g_oddHull φ B).map φ = B := by
  haveI : Finite C := Finite.of_surjective φ hφ
  refine le_antisymm ?_ ?_
  · rw [Subgroup.map_le_iff_le_comap]
    exact l34g_oddHull_le φ B
  · refine (l34g_le_closure_odd hB).trans ?_
    rw [Subgroup.closure_le]
    rintro c ⟨hcB, hcodd⟩
    obtain ⟨a, ha, haodd⟩ := l34g_exists_odd_lift φ hφ hcodd
    exact Subgroup.mem_map.mpr
      ⟨a, Subgroup.subset_closure ⟨by rw [ha]; exact hcB, haodd⟩, ha⟩

theorem l34g_oddHull_le_centralizer {A C : Type} [Group A] [Group C] [Finite A] (φ : A →* C)
    (hker : φ.ker ≤ Subgroup.center A) {B : Subgroup C} {b : C}
    (hBb : B ≤ Subgroup.centralizer ({b} : Set C)) {b₁ : A} (hb₁ : b₁ * b₁ = 1)
    (hφb₁ : φ b₁ = b) : l34g_oddHull φ B ≤ Subgroup.centralizer ({b₁} : Set A) := by
  rw [l34g_oddHull, Subgroup.closure_le]
  rintro g ⟨hgB, hodd⟩
  refine Subgroup.mem_centralizer_iff.mpr ?_
  intro h hh
  rw [Set.mem_singleton_iff] at hh
  subst h
  set k : A := g * b₁ * g⁻¹ * b₁⁻¹ with hk_def
  have hb₁inv : b₁⁻¹ = b₁ := inv_eq_of_mul_eq_one_right hb₁
  have hcomm : b * φ g = φ g * b :=
    (Subgroup.mem_centralizer_iff.mp (hBb hgB)) b (Set.mem_singleton b)
  have hk_ker : k ∈ φ.ker := by
    rw [MonoidHom.mem_ker, hk_def]
    simp only [map_mul, map_inv, hφb₁]
    rw [← hcomm]
    group
  have hk_center : k ∈ Subgroup.center A := hker hk_ker
  have hk_comm : ∀ x : A, x * k = k * x := Subgroup.mem_center_iff.mp hk_center
  have hk_eq : g * b₁ * g⁻¹ = k * b₁ := by
    rw [hk_def, hb₁inv]
    rw [mul_assoc (g * b₁ * g⁻¹) b₁ b₁, hb₁, mul_one]
  have hu2 : (g * b₁ * g⁻¹) * (g * b₁ * g⁻¹) = 1 := by
    have h1 : (g * b₁ * g⁻¹) * (g * b₁ * g⁻¹) = g * (b₁ * b₁) * g⁻¹ := by group
    rw [h1, hb₁]; group
  have hk2 : k ^ 2 = 1 := by
    have hB : (k * b₁) * (k * b₁) = 1 := by
      rw [← hk_eq]; exact hu2
    have hexp : (k * b₁) * (k * b₁) = (k * k) * (b₁ * b₁) := by
      rw [show (k * b₁) * (k * b₁) = k * (b₁ * k) * b₁ by group, hk_comm b₁]
      group
    rw [pow_two]
    rw [hexp] at hB
    rw [hb₁, mul_one] at hB
    exact hB
  have hgm : ∀ m : ℕ, g * k ^ m * g⁻¹ = k ^ m := by
    intro m
    have hc : g * k ^ m = k ^ m * g :=
      Subgroup.mem_center_iff.mp ((Subgroup.center A).pow_mem hk_center m) g
    rw [hc, mul_assoc, mul_inv_cancel, mul_one]
  have hpow : ∀ m : ℕ, g ^ m * b₁ * (g⁻¹) ^ m = k ^ m * b₁ := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
        calc g ^ (m + 1) * b₁ * (g⁻¹) ^ (m + 1)
            = g * (g ^ m * b₁ * (g⁻¹) ^ m) * g⁻¹ := by
                rw [pow_succ', pow_succ']; group
          _ = g * (k ^ m * b₁) * g⁻¹ := by rw [ih]
          _ = (g * k ^ m * g⁻¹) * (g * b₁ * g⁻¹) := by group
          _ = k ^ m * (k * b₁) := by rw [hgm m, hk_eq]
          _ = k ^ (m + 1) * b₁ := by rw [← mul_assoc, ← pow_succ]
  have hnk : k ^ orderOf g = 1 := by
    have h := hpow (orderOf g)
    have hinv : (g⁻¹) ^ orderOf g = 1 := by
      rw [← orderOf_inv g]; exact pow_orderOf_eq_one g⁻¹
    rw [pow_orderOf_eq_one g, hinv, mul_one, one_mul] at h
    exact mul_right_cancel (by rw [← h, one_mul])
  have hk1 : k = 1 := by
    obtain ⟨r, hr⟩ := hodd
    have hkpow : k ^ orderOf g = k := by
      rw [hr, pow_succ, pow_mul, hk2, one_pow, one_mul]
    rw [← hkpow]; exact hnk
  have hgb : g * b₁ * g⁻¹ = b₁ := by rw [hk_eq, hk1, one_mul]
  calc b₁ * g = (g * b₁ * g⁻¹) * g := by rw [hgb]
    _ = g * b₁ := by group

end CFSG.OddStandard.SmallF3.Omega
