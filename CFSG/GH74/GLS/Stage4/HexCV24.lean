module

public import CFSG.GH74.GLS.Stage4.HexCSub

public section

open CFSG.GH74.BNPair CFSG.GH74.GLS.SP
open scoped commutatorElement

namespace CFSG.GH74.GLS.Stage4.Hex

variable {G : Type} [Group G] {H : Subgroup G} {r₁ r₂ : G} {U : Subgroup G}
  {root : ℤ → Subgroup G}

namespace Hex6Comm

variable {root : ℤ → Subgroup G} (hC : Hex6Comm root)

include hC in
theorem c12 : ∀ x ∈ root 1, ∀ y ∈ root 2, x * y = y * x := fun x hx y hy =>
  hC.adj 1 (by norm_num) (by norm_num) x hx y (by simpa using hy)

include hC in
theorem c23 : ∀ x ∈ root 2, ∀ y ∈ root 3, x * y = y * x := fun x hx y hy =>
  hC.adj 2 (by norm_num) (by norm_num) x hx y (by simpa using hy)

include hC in
theorem c34 : ∀ x ∈ root 3, ∀ y ∈ root 4, x * y = y * x := fun x hx y hy =>
  hC.adj 3 (by norm_num) (by norm_num) x hx y (by simpa using hy)

include hC in
theorem c45 : ∀ x ∈ root 4, ∀ y ∈ root 5, x * y = y * x := fun x hx y hy =>
  hC.adj 4 (by norm_num) (by norm_num) x hx y (by simpa using hy)

include hC in
theorem c56 : ∀ x ∈ root 5, ∀ y ∈ root 6, x * y = y * x := fun x hx y hy =>
  hC.adj 5 (by norm_num) (by norm_num) x hx y (by simpa using hy)

end Hex6Comm

theorem V24_decomp (R : RGD2 6 H r₁ r₂ U root) {n : G} (hn : n ∈ Vsub root 2 4) :
    ∃ a ∈ root 2, ∃ u ∈ root 3, ∃ b ∈ root 4, n = a * u * b := by
  have hc : n ∈ chainProd root (intList 2 4) := by
    have : n ∈ ((Vsub root 2 4 : Subgroup G) : Set G) := hn
    rwa [Vsub_carrier R (by norm_num) (by norm_num)] at this
  have hl : intList 2 4 = [2, 3, 4] := by decide
  rw [hl] at hc
  simp only [chainProd, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, Set.mem_mul,
    Set.mem_one, SetLike.mem_coe] at hc
  obtain ⟨a, ha, _, ⟨u, hu, _, ⟨b, hb, _, rfl, rfl⟩, rfl⟩, rfl⟩ := hc
  exact ⟨a, ha, u, hu, b, hb, by simp [mul_assoc]⟩

theorem mem_V24_of {a u b : G} (ha : a ∈ root 2) (hu : u ∈ root 3) (hb : b ∈ root 4) :
    a * u * b ∈ Vsub root 2 4 :=
  (Vsub root 2 4).mul_mem ((Vsub root 2 4).mul_mem (root_le_Vsub (by norm_num) (by norm_num) ha)
    (root_le_Vsub (by norm_num) (by norm_num) hu)) (root_le_Vsub (by norm_num) (by norm_num) hb)

theorem rgd2_unique_234 (R : RGD2 6 H r₁ r₂ U root) {a a' u u' b b' : G} (ha : a ∈ root 2)
    (ha' : a' ∈ root 2) (hu : u ∈ root 3) (hu' : u' ∈ root 3) (hb : b ∈ root 4)
    (hb' : b' ∈ root 4) (h : a * u * b = a' * u' * b') : a = a' ∧ u = u' ∧ b = b' := by
  have hl : intList 1 ((6 : ℕ) : ℤ) = [1, 2, 3, 4, 5, 6] := by decide
  have key := R.unique (fun k => if k = 2 then a else if k = 3 then u else if k = 4 then b else 1)
    (fun k => if k = 2 then a' else if k = 3 then u' else if k = 4 then b' else 1)
    (fun k hk => by
      rw [hl] at hk
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [ha, hu, hb, (root _).one_mem])
    (fun k hk => by
      rw [hl] at hk
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [ha', hu', hb', (root _).one_mem])
    (by rw [hl]; simpa [mul_assoc] using h)
  have h2 := key 2 (by rw [hl]; simp)
  have h3 := key 3 (by rw [hl]; simp)
  have h4 := key 4 (by rw [hl]; simp)
  simp at h2 h3 h4
  exact ⟨h2, h3, h4⟩

theorem V24_comm (R : RGD2 6 H r₁ r₂ U root) (hC : Hex6Comm root) {x y : G}
    (hx : x ∈ Vsub root 2 4) (hy : y ∈ Vsub root 2 4) : x * y = y * x := by
  obtain ⟨a, ha, u, hu, b, hb, rfl⟩ := V24_decomp R hx
  obtain ⟨a', ha', u', hu', b', hb', rfl⟩ := V24_decomp R hy
  have h1 : Commute a a' := hC.ab 2 (by norm_num) (by norm_num) a ha a' ha'
  have h2 : Commute a u' := hC.c23 a ha u' hu'
  have h3 : Commute a b' := hC.l24 a ha b' hb'
  have h4 : Commute u a' := (hC.c23 a' ha' u hu).symm
  have h5 : Commute u u' := hC.ab 3 (by norm_num) (by norm_num) u hu u' hu'
  have h6 : Commute u b' := hC.c34 u hu b' hb'
  have h7 : Commute b a' := (hC.l24 a' ha' b hb).symm
  have h8 : Commute b u' := (hC.c34 u' hu' b hb).symm
  have h9 : Commute b b' := hC.ab 4 (by norm_num) (by norm_num) b hb b' hb'
  have A : Commute a (a' * u' * b') := (h1.mul_right h2).mul_right h3
  have B : Commute u (a' * u' * b') := (h4.mul_right h5).mul_right h6
  have C : Commute b (a' * u' * b') := (h7.mul_right h8).mul_right h9
  exact ((A.mul_left B).mul_left C).eq

end CFSG.GH74.GLS.Stage4.Hex
