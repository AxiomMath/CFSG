module

public import CFSG.GH74.E2.Cl2Rank

public section

namespace CFSG.GH74.E2

open Subgroup

theorem exists_cube_root_exp {D : Type*} [Group D] [Finite D] (hD : IsPGroup 2 D) :
    ∃ m : ℕ, ∀ x : D, (x ^ m) ^ 3 = x := by
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card).mp hD
  by_cases hn0 : n = 0
  · subst hn0
    have h1 : Nat.card D = 1 := by simpa using hn
    have : Subsingleton D := (Nat.card_eq_one_iff_unique.mp h1).1
    exact ⟨0, fun x => by rw [Subsingleton.elim x 1]; simp⟩
  · have hlt : 1 < 2 ^ n := Nat.one_lt_two_pow hn0
    have hcop : Nat.Coprime 3 (2 ^ n) :=
      Nat.Coprime.pow_right n (by norm_num)
    obtain ⟨m, -, hm⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop hlt
    refine ⟨m, fun x => ?_⟩
    have hx : x ^ (2 ^ n) = 1 := by rw [← hn]; exact pow_card_eq_one'
    rw [← pow_mul, pow_eq_pow_mod (m * 3) hx, mul_comm m 3, hm, pow_one]


theorem eps_mul_of_central {G : Type*} [Group G] (b : MulAut G) (x : G) {y : G}
    (hy : y ∈ Subgroup.center G) (hby : b y ∈ Subgroup.center G) :
    eps b (x * y) = eps b x * eps b y := by
  have h1 : y * b x = b x * y := (Subgroup.mem_center_iff.1 hy (b x)).symm
  have h2 : y * b (b x) = b (b x) * y := (Subgroup.mem_center_iff.1 hy (b (b x))).symm
  have h3 : b y * b (b x) = b (b x) * b y := (Subgroup.mem_center_iff.1 hby (b (b x))).symm
  unfold eps
  simp only [map_mul]
  calc x * y * (b x * b y) * (b (b x) * b (b y))
      = x * (y * b x) * (b y * b (b x)) * b (b y) := by group
    _ = x * (b x * y) * (b (b x) * b y) * b (b y) := by rw [h1, h3]
    _ = x * b x * (y * b (b x)) * b y * b (b y) := by group
    _ = x * b x * (b (b x) * y) * b y * b (b y) := by rw [h2]
    _ = x * b x * b (b x) * (y * b y * b (b y)) := by group

theorem e2_alg {G : Type*} [Group G] [Finite G] (hG : IsPGroup 2 G) {a b : MulAut G}
    (D : Subgroup G) (hDz : D ≤ Subgroup.center G) (hDb : ∀ x ∈ D, b x ∈ D)
    (ex ey : G) (z : Fin 2 → Fin 2 → G)
    (hgen : Subgroup.closure (({ex, ey} : Set G) ∪
      Set.range (fun p : Fin 2 × Fin 2 => z p.1 p.2)) = D)
    (hexa : a ex = ex) (hexb : b ex = ex) (heya : a ey = ey) (heyb : b ey = ey)
    (hbz0 : ∀ i, b (z i 0) = z i 1) (hbz1 : ∀ i, b (z i 1) = (z i 0 * z i 1)⁻¹)
    {u : G} (hu : u ∈ D) (hbu : b u = u) (hnu : eps a u = 1) : u = 1 := by
  classical
  obtain ⟨m, hm⟩ := exists_cube_root_exp hG
  have hcube : ∀ x : G, x ^ 3 = 1 → x = 1 := fun x hx => by
    calc x = (x ^ m) ^ 3 := (hm x).symm
      _ = (x ^ 3) ^ m := by rw [← pow_mul, ← pow_mul, mul_comm]
      _ = 1 := by rw [hx, one_pow]
  set X := Subgroup.closure ({ex, ey} : Set G) with hX
  set Z := Subgroup.closure (Set.range (fun p : Fin 2 × Fin 2 => z p.1 p.2)) with hZ
  have hXZ : X ⊔ Z = D := by rw [hX, hZ, ← Subgroup.closure_union]; exact hgen
  have hXD : X ≤ D := by rw [← hXZ]; exact le_sup_left
  have hZD : Z ≤ D := by rw [← hXZ]; exact le_sup_right
  have hXle : X ≤ fixSub a ⊓ fixSub b := by
    rw [hX, Subgroup.closure_le]
    intro t ht
    rcases ht with rfl | ht
    · exact ⟨hexa, hexb⟩
    · rw [Set.mem_singleton_iff] at ht
      subst ht
      exact ⟨heya, heyb⟩
  let K : Subgroup G :=
    { carrier := {x | x ∈ D ∧ eps b x = 1}
      mul_mem' := fun {x y} hx hy => by
        have hx' : x ∈ D ∧ eps b x = 1 := hx
        have hy' : y ∈ D ∧ eps b y = 1 := hy
        refine ⟨D.mul_mem hx'.1 hy'.1, ?_⟩
        rw [eps_mul_of_central b x (hDz hy'.1) (hDz (hDb y hy'.1)), hx'.2, hy'.2, one_mul]
      one_mem' := ⟨D.one_mem, by simp [eps]⟩
      inv_mem' := fun {x} hx => by
        have hx' : x ∈ D ∧ eps b x = 1 := hx
        have hxi : x⁻¹ ∈ D := D.inv_mem hx'.1
        refine ⟨hxi, ?_⟩
        have h1 : eps b x * eps b x⁻¹ = 1 := by
          rw [← eps_mul_of_central b x (hDz hxi) (hDz (hDb _ hxi)), mul_inv_cancel]
          simp [eps]
        rw [hx'.2, one_mul] at h1
        exact h1 }
  have hZK : Z ≤ K := by
    rw [hZ, Subgroup.closure_le]
    rintro t ⟨⟨i, j⟩, rfl⟩
    have hmemD : z i j ∈ D := hZD (Subgroup.subset_closure ⟨(i, j), rfl⟩)
    show z i j ∈ D ∧ eps b (z i j) = 1
    refine ⟨hmemD, ?_⟩
    fin_cases j
    · show eps b (z i 0) = 1
      unfold eps
      rw [hbz0 i, hbz1 i, mul_inv_cancel]
    · show eps b (z i 1) = 1
      unfold eps
      rw [hbz1 i, map_inv, map_mul, hbz0 i, hbz1 i]
      simp
  have hu' : u ∈ X ⊔ Z := by rw [hXZ]; exact hu
  have hcomm : ∀ x ∈ X, ∀ y ∈ Z, x * y = y * x := fun x hx y _ =>
    (Subgroup.mem_center_iff.1 (hDz (hXD hx)) y).symm
  obtain ⟨χ, hχ, ζ, hζ, rfl⟩ := (mem_sup_iff_of_commute hcomm).mp hu'
  have hχa : a χ = χ := (hXle hχ).1
  have hχb : b χ = χ := (hXle hχ).2
  have hbζ : b ζ = ζ := by
    have h := hbu
    rw [map_mul, hχb] at h
    exact mul_left_cancel h
  have hζ3 : ζ ^ 3 = 1 := by
    have h1 : eps b ζ = 1 := (hZK hζ).2
    have h2 : eps b ζ = ζ ^ 3 := by
      unfold eps
      rw [hbζ, hbζ, pow_three']
    rw [← h2]; exact h1
  have hζ1 : ζ = 1 := hcube ζ hζ3
  subst hζ1
  rw [mul_one] at hnu ⊢
  have hu3 : χ ^ 3 = 1 := by
    have : eps a χ = χ ^ 3 := by
      unfold eps
      rw [hχa, hχa, pow_three']
    rw [← this]; exact hnu
  exact hcube χ hu3

end CFSG.GH74.E2
