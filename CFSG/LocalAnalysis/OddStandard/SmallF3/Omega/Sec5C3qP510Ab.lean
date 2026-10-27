module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5C3qP510Tr

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

@[expose] def sec5p510_Vs (i j : Fin 6) : Finset (Fin 6 → ZMod 2) :=
  {0, 1, Pi.single i 1, Pi.single j 1, 1 + Pi.single i 1, 1 + Pi.single j 1,
    Pi.single i 1 + Pi.single j 1, 1 + Pi.single i 1 + Pi.single j 1}

theorem sec5p510_vec_add_self (v : Fin 6 → ZMod 2) : v + v = 0 := by
  revert v
  decide +kernel

private theorem sec5p510_Vs_add_aux :
    ∀ i j : Fin 6, ∀ v ∈ sec5p510_Vs i j, ∀ w ∈ sec5p510_Vs i j, v + w ∈ sec5p510_Vs i j := by
  decide +kernel

theorem sec5p510_Vs_add {i j : Fin 6} {v w : Fin 6 → ZMod 2} (hv : v ∈ sec5p510_Vs i j)
    (hw : w ∈ sec5p510_Vs i j) : v + w ∈ sec5p510_Vs i j :=
  sec5p510_Vs_add_aux i j v hv w hw

private theorem sec5p510_Vs_card_aux :
    ∀ i j : Fin 6, i ≠ j → (sec5p510_Vs i j).card = 8 := by
  decide +kernel

theorem sec5p510_Vs_card {i j : Fin 6} (hij : i ≠ j) : (sec5p510_Vs i j).card = 8 :=
  sec5p510_Vs_card_aux i j hij

private theorem sec5p510_Vs_delta_aux : ∀ i j : Fin 6, ∀ v ∈ sec5p510_Vs i j,
    (vecWeight v = 6 ∨ vecWeight v = 1) →
      v = 1 ∨ v = Pi.single i 1 ∨ v = Pi.single j 1 := by
  decide +kernel

theorem sec5p510_Vs_delta {i j : Fin 6} {v : Fin 6 → ZMod 2} (hv : v ∈ sec5p510_Vs i j)
    (hw : vecWeight v = 6 ∨ vecWeight v = 1) : v = 1 ∨ v = Pi.single i 1 ∨ v = Pi.single j 1 :=
  sec5p510_Vs_delta_aux i j v hv hw

theorem sec5p510_exists_single_of_weight_one {v : Fin 6 → ZMod 2} (hv : vecWeight v = 1) :
    ∃ i : Fin 6, v = Pi.single i 1 := by
  revert v
  decide +kernel

structure Sec510Ab {G : Type} [Group G] (t z a b : G) (φ : (Fin 6 → ZMod 2) → G)
    (A : Subgroup G) : Prop where
  mem₁ : a ∈ wclass φ 1
  mem₂ : b ∈ wclass φ 1
  ne : a ≠ b
  prod : t * a * b = z
  cyc : ∃ c ∈ normalizer (A : Set G), c * t * c⁻¹ = a ∧ c * a * c⁻¹ = b ∧ c * b * c⁻¹ = t

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {z r ρ : G}
  {B A : Subgroup G} {φ : (Fin 6 → ZMod 2) → G} {Q₁ Q₂ : Subgroup G} {a b : G}

theorem sec5p510_exists_ab (h : Sec510Ctx G t L S z r ρ B A φ) :
    ∃ a b : G, Sec510Ab t z a b φ A := by
  obtain ⟨a, b, ha, hb, hab, hz, hc⟩ := sec5p510_exists_cycle h
  exact ⟨a, b, ha, hb, hab, hz, hc⟩

theorem sec5p510_phi_one (h : Sec510Ctx G t L S z r ρ B A φ) : φ (1 : Fin 6 → ZMod 2) = t := by
  rw [Pi.one_def]
  exact h.model.map_one

theorem sec5p510_A_comm (h : Sec510Ctx G t L S z r ρ B A φ) {x y : G} (hx : x ∈ A)
    (hy : y ∈ A) : x * y = y * x := by
  obtain ⟨v, rfl⟩ := (h.model.perm.mem_iff x).mp hx
  obtain ⟨w, rfl⟩ := (h.model.perm.mem_iff y).mp hy
  rw [← h.model.perm.map_add, ← h.model.perm.map_add, add_comm]

theorem sec5p510_A_sq (h : Sec510Ctx G t L S z r ρ B A φ) {x : G} (hx : x ∈ A) : x * x = 1 := by
  obtain ⟨v, rfl⟩ := (h.model.perm.mem_iff x).mp hx
  rw [← h.model.perm.map_add, sec5p510_vec_add_self, h.model.perm.map_zero]

theorem sec5p510_t_mem_A (h : Sec510Ctx G t L S z r ρ B A φ) : t ∈ A := h.model.mem_A.1

theorem sec5p510_z_mem_A (h : Sec510Ctx G t L S z r ρ B A φ) : z ∈ A := h.model.mem_A.2.2

theorem Sec510Ab.a_mem_A (hab : Sec510Ab t z a b φ A) (h : Sec510Ctx G t L S z r ρ B A φ) :
    a ∈ A :=
  h.model.perm.wclass_subset 1 hab.mem₁

theorem Sec510Ab.b_mem_A (hab : Sec510Ab t z a b φ A) (h : Sec510Ctx G t L S z r ρ B A φ) :
    b ∈ A :=
  h.model.perm.wclass_subset 1 hab.mem₂

theorem Sec510Ab.az (hab : Sec510Ab t z a b φ A) (h : Sec510Ctx G t L S z r ρ B A φ) :
    a * z = t * b := by
  have hat : a * t = t * a := sec5p510_A_comm h (hab.a_mem_A h) (sec5p510_t_mem_A h)
  have ha2 : a * a = 1 := sec5p510_A_sq h (hab.a_mem_A h)
  rw [← hab.prod]
  calc a * (t * a * b) = (a * t) * a * b := by simp only [mul_assoc]
    _ = (t * a) * a * b := by rw [hat]
    _ = t * (a * a) * b := by simp only [mul_assoc]
    _ = t * b := by rw [ha2, mul_one]

theorem Sec510Ab.bz (hab : Sec510Ab t z a b φ A) (h : Sec510Ctx G t L S z r ρ B A φ) :
    b * z = t * a := by
  have hab' : a * b = b * a := sec5p510_A_comm h (hab.a_mem_A h) (hab.b_mem_A h)
  have hbt : b * t = t * b := sec5p510_A_comm h (hab.b_mem_A h) (sec5p510_t_mem_A h)
  have hb2 : b * b = 1 := sec5p510_A_sq h (hab.b_mem_A h)
  rw [← hab.prod]
  calc b * (t * a * b) = (b * t) * a * b := by simp only [mul_assoc]
    _ = (t * b) * a * b := by rw [hbt]
    _ = t * (b * a) * b := by simp only [mul_assoc]
    _ = t * (a * b) * b := by rw [hab']
    _ = t * a * (b * b) := by simp only [mul_assoc]
    _ = t * a := by rw [hb2, mul_one]

theorem Sec510Ab.ab_eq (hab : Sec510Ab t z a b φ A) (h : Sec510Ctx G t L S z r ρ B A φ) :
    a * b = t * z := by
  have ht2 : t * t = 1 := sec5p510_A_sq h (sec5p510_t_mem_A h)
  rw [← hab.prod]
  calc a * b = (t * t) * (a * b) := by rw [ht2, one_mul]
    _ = t * (t * a * b) := by simp only [mul_assoc]

theorem Sec510Ab.tb_mem (hab : Sec510Ab t z a b φ A) (h : Sec510Ctx G t L S z r ρ B A φ) :
    t * b ∈ wclass φ 5 := by
  have := h.model.perm.mul_mem_wclass (k := 1) (by norm_num) hab.mem₂
  rwa [sec5p510_phi_one h] at this

theorem Sec510Ab.ta_mem (hab : Sec510Ab t z a b φ A) (h : Sec510Ctx G t L S z r ρ B A φ) :
    t * a ∈ wclass φ 5 := by
  have := h.model.perm.mul_mem_wclass (k := 1) (by norm_num) hab.mem₁
  rwa [sec5p510_phi_one h] at this

theorem Sec510Ab.cyc_z (hab : Sec510Ab t z a b φ A) (h : Sec510Ctx G t L S z r ρ B A φ) :
    ∃ c ∈ normalizer (A : Set G), c * t * c⁻¹ = a ∧ c * a * c⁻¹ = b ∧ c * z * c⁻¹ = z := by
  obtain ⟨c, hc, h1, h2, h3⟩ := hab.cyc
  refine ⟨c, hc, h1, h2, ?_⟩
  have hab' : a * b = b * a := sec5p510_A_comm h (hab.a_mem_A h) (hab.b_mem_A h)
  have hat : a * t = t * a := sec5p510_A_comm h (hab.a_mem_A h) (sec5p510_t_mem_A h)
  have hbt : b * t = t * b := sec5p510_A_comm h (hab.b_mem_A h) (sec5p510_t_mem_A h)
  calc c * z * c⁻¹ = (c * t * c⁻¹) * (c * a * c⁻¹) * (c * b * c⁻¹) := by
        rw [← hab.prod]
        group
    _ = a * b * t := by rw [h1, h2, h3]
    _ = t * a * b := by
        calc a * b * t = a * (b * t) := by rw [mul_assoc]
          _ = a * (t * b) := by rw [hbt]
          _ = (a * t) * b := by rw [mul_assoc]
          _ = t * a * b := by rw [hat]
    _ = z := hab.prod


theorem sec5p510_ab_coords (hab : Sec510Ab t z a b φ A) :
    ∃ i j : Fin 6, i ≠ j ∧ φ (Pi.single i 1) = a ∧ φ (Pi.single j 1) = b := by
  obtain ⟨u, hu, hua⟩ := hab.mem₁
  obtain ⟨w, hw, hwb⟩ := hab.mem₂
  obtain ⟨i, rfl⟩ := sec5p510_exists_single_of_weight_one hu
  obtain ⟨j, rfl⟩ := sec5p510_exists_single_of_weight_one hw
  refine ⟨i, j, ?_, hua, hwb⟩
  rintro rfl
  exact hab.ne (hua.symm.trans hwb)

end CFSG.OddStandard.SmallF3.Omega
