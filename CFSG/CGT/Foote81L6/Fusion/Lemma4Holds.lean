module

public import CFSG.CGT.Foote81L6.Fusion.Lemma4
public import CFSG.CGT.Foote81L6.MainL6Inputs

public section

namespace CFSG.CGT.Foote81L6

open Subgroup

namespace FooteCore

variable {G : Type*} [Group G] {T : Subgroup G} {m n : ℕ} (D : FooteCore G T m n)

private theorem not_mem_B_of_mem_A {x : G} (hx : x ∈ D.A) (hx1 : x ≠ 1) : x ∉ D.B := fun h =>
  hx1 (by
    have := mem_inf.2 ⟨hx, h⟩
    rwa [D.A_inf_B, mem_bot] at this)

private theorem eq_b_of_isConj_b
    (hL3 : ∀ x ∈ D.Zab, ∀ y ∈ D.Zab, IsConj x y → x = y ∨ (x = D.b₀ ∧ y = D.b₁) ∨
      (x = D.b₁ ∧ y = D.b₀) ∨ (x = D.a * D.b₀ ∧ y = D.a * D.b₁) ∨
      (x = D.a * D.b₁ ∧ y = D.a * D.b₀)) :
    ∀ y ∈ D.Zab, IsConj D.b y → y = D.b := by
  intro y hy hby
  have hb₀ : D.b₀ ∈ D.Zab := subset_closure (Set.mem_insert_of_mem _ (Set.mem_insert _ _))
  have hb₁ : D.b₁ ∈ D.Zab :=
    subset_closure (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_singleton _)))
  have hbZ : D.b ∈ D.Zab := mul_mem hb₀ hb₁
  have hab₀ : D.a * D.b₀ = D.b₀ * D.a := D.A_comm_B D.a D.a_mem D.b₀ D.b₀_mem_B
  rcases hL3 D.b hbZ y hy hby with h | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩
  · exact h.symm
  · exact absurd (mul_left_cancel (h.trans (mul_one _).symm)) D.b₁_ne_one
  · exact absurd (mul_right_cancel (h.trans (one_mul _).symm)) D.b₀_ne_one
  ·
    have h' : D.b₀ * D.b₁ = D.b₀ * D.a := h.trans hab₀
    exact (D.not_mem_B_of_mem_A D.a_mem D.a_ne_one (mul_left_cancel h' ▸ D.b₁_mem_B)).elim
  · have h' : D.b₀ * D.b₁ = D.a * D.b₁ := h
    exact (D.not_mem_B_of_mem_A D.a_mem D.a_ne_one (mul_right_cancel h' ▸ D.b₀_mem_B)).elim

end FooteCore

theorem footeLemma4OneLarge_holds (h3 : FooteLemma3One) : FooteLemma4OneLarge := by
  intro G _ _ T m n D hn g hgT
  exact D.lemma4_one_large (D.eq_b_of_isConj_b (h3 G T m n D))
    (footeNotConjAB_of_one h3 G T m n D) hn g hgT

theorem footeLemma4Two_holds (h3 : FooteLemma3One) (h3t : FooteLemma3Two) : FooteLemma4Two := by
  intro G _ _ T n D hcen a₁ ha₁ ha₁1 ha₁a g hgT
  exact D.lemma4_two (D.eq_b_of_isConj_b (h3 G T 2 n D))
    (fun ha ha1 haa => (h3t G T n D hcen ha ha1 haa).1) hcen ha₁ ha₁1 ha₁a g hgT

end CFSG.CGT.Foote81L6
