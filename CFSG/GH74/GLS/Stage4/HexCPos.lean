module

public import CFSG.GH74.GLS.Stage4.HexCOct
public import CFSG.GH74.GLS.Stage4.HexCRoots

public section

open CFSG.GH74.BNPair CFSG.GH74.GLS.SP
open scoped commutatorElement

namespace CFSG.GH74.GLS.Stage4.Hex

variable {G : Type} [Group G] {H : Subgroup G} {r₁ r₂ : G} {U : Subgroup G}
  {root : ℤ → Subgroup G}

theorem comm_via (m : G) {x y : G}
    (h : (m⁻¹ * x * m) * (m⁻¹ * y * m) = (m⁻¹ * y * m) * (m⁻¹ * x * m)) : x * y = y * x := by
  have := congrArg (fun z => m * z * m⁻¹) h
  simpa [mul_assoc] using this

theorem rgd2_comm_adj (R : RGD2 6 H r₁ r₂ U root) {a : ℤ} (ha : 1 ≤ a) (ha6 : a + 1 ≤ 6) {x y : G}
    (hx : x ∈ root a) (hy : y ∈ root (a + 1)) : x * y = y * x := by
  have h := rgd2_octComm R a (a + 1) ha (by omega) (by exact_mod_cast ha6) x hx y hy
  have hemp : (⨆ c ∈ Set.Ioo a (a + 1), root c : Subgroup G) = ⊥ := by
    have : Set.Ioo a (a + 1) = (∅ : Set ℤ) := by
      ext c; simp only [Set.mem_Ioo, Set.mem_empty_iff_false, iff_false]; omega
    simp [this]
  rw [hemp, Subgroup.mem_bot] at h
  exact (commutatorElement_eq_one_iff_mul_comm.1 h)

structure Hex6Comm (root : ℤ → Subgroup G) : Prop where
  ab : ∀ i : ℤ, 1 ≤ i → i ≤ 6 → ∀ x ∈ root i, ∀ y ∈ root i, x * y = y * x
  adj : ∀ a : ℤ, 1 ≤ a → a + 1 ≤ 6 → ∀ x ∈ root a, ∀ y ∈ root (a + 1), x * y = y * x
  o14 : ∀ x ∈ root 1, ∀ y ∈ root 4, x * y = y * x
  o25 : ∀ x ∈ root 2, ∀ y ∈ root 5, x * y = y * x
  o36 : ∀ x ∈ root 3, ∀ y ∈ root 6, x * y = y * x
  l24 : ∀ x ∈ root 2, ∀ y ∈ root 4, x * y = y * x
  l46 : ∀ x ∈ root 4, ∀ y ∈ root 6, x * y = y * x
  l26 : ∀ x ∈ root 2, ∀ y ∈ root 6, ⁅x, y⁆ ∈ root 4

theorem mem_iff_r12_one (R : RGD2 6 H r₁ r₂ U root) (x : G) :
    x ∈ root 1 ↔ (r₁ * r₂) * x * (r₁ * r₂)⁻¹ ∈ root 3 := by
  have h2 := RGD2.mem_iff_r₂ R (i := 1) (by norm_num) (by norm_num) x
  have h1 := RGD2.mem_iff_r₁ R (i := 5) (by norm_num) (by norm_num) (r₂ * x * r₂⁻¹)
  norm_num at h2 h1
  have e : r₁ * (r₂ * x * r₂⁻¹) * r₁⁻¹ = (r₁ * r₂) * x * (r₁ * r₂)⁻¹ := by group
  rw [e] at h1
  exact h2.trans h1

theorem Hex6Comm.of_data (R : RGD2 6 H r₁ r₂ U root)
    (hO : ∀ a ∈ root 1 ⊔ root (-1), ∀ b ∈ root 4 ⊔ root (-4), a * b = b * a)
    (hc24 : ∀ x ∈ root 2, ∀ y ∈ root 4, x * y = y * x)
    (hc46 : ∀ x ∈ root 4, ∀ y ∈ root 6, x * y = y * x)
    (hc26 : ∀ x ∈ root 2, ∀ y ∈ root 6, ⁅x, y⁆ ∈ root 4)
    (hab : ∀ i : ℤ, 1 ≤ i → i ≤ 6 → ∀ x ∈ root i, ∀ y ∈ root i, x * y = y * x) :
    Hex6Comm root := by
  have o14 : ∀ x ∈ root 1, ∀ y ∈ root 4, x * y = y * x := fun x hx y hy =>
    hO x (Subgroup.mem_sup_left hx) y (Subgroup.mem_sup_left hy)
  refine ⟨hab, fun a ha ha6 x hx y hy => rgd2_comm_adj R ha ha6 hx hy, o14, ?_, ?_, hc24, hc46, hc26⟩
  · intro x hx y hy
    have hx' : r₂ * x * r₂⁻¹ ∈ root 4 := by
      have := (RGD2.mem_iff_r₂ R (i := 2) (by norm_num) (by norm_num) x).1 hx
      norm_num at this; exact this
    have hy' : r₂ * y * r₂⁻¹ ∈ root 1 := by
      have := (RGD2.mem_iff_r₂ R (i := 5) (by norm_num) (by norm_num) y).1 hy
      norm_num at this; exact this
    refine comm_via r₂⁻¹ ?_
    simpa using (o14 _ hy' _ hx').symm
  · intro x hx y hy
    set m := r₁ * r₂ with hm
    have hx' : m⁻¹ * x * m ∈ root 1 := by
      rw [mem_iff_r12_one R]
      simpa [hm, mul_assoc] using hx
    have hy' : m⁻¹ * y * m ∈ root 4 := by
      rw [mem_iff_r12 R]
      simpa [hm, mul_assoc] using hy
    exact comm_via m (o14 _ hx' _ hy')

end CFSG.GH74.GLS.Stage4.Hex
