module

public import CFSG.Certificates.Kernel.SporCov.Words
public import CFSG.Certificates.Kernel.SporCov.P3Group
public import CFSG.LocalAnalysis.StandardType.GGSporKRestDefs

public section

namespace CFSG.KD.SporCov

open CFSG.KC.SporCov CFSG.StandardType.SporadicShape

variable {G : Type} [Group G]

theorem conj_ne_one {g v : G} (hv : v ≠ 1) : g * v * g⁻¹ ≠ 1 := by
  intro e
  apply hv
  rw [mul_inv_eq_one] at e
  exact mul_eq_left.1 e

theorem ne_one_of_not_mem {z v : G} (hv : v ∉ Subgroup.zpowers z) : v ≠ 1 := by
  rintro rfl
  exact hv (Subgroup.one_mem _)

theorem P3Rel.sporKRest_cover [Finite G] {p : ℕ} (hp : p.Prime)
    (hval : (Nat.card G).factorization p = 3) {g₁ g₂ z : G} (hR : P3Rel p g₁ g₂ z) (hz : z ≠ 1)
    (hgen : (∀ y, IsConj z y → SporKRestGenerating p y) ∨
      ((∀ y, IsConj g₂ y → SporKRestGenerating p y) ∧
        ∀ i < p, ∀ y, IsConj (g₁ * g₂ ^ i) y → SporKRestGenerating p y)) :
    SporKRestCover p G := by
  have : Fact p.Prime := ⟨hp⟩
  intro E hE hcard
  have hEc : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hE.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  obtain ⟨g, hzE, hl⟩ := hR.exists_conj_lines hp hz hval (IsPGroup.of_card hcard) hEc hcard
  rcases hgen with hzg | ⟨h₂, hi⟩
  · exact ⟨_, hzE, conj_ne_one hz, hzg _ (isConj_iff.2 ⟨g, rfl⟩)⟩
  · rcases hl with h2 | ⟨i, hip, h3⟩
    · exact ⟨_, h2, conj_ne_one (ne_one_of_not_mem (hR.g₂_not_mem hz)),
        h₂ _ (isConj_iff.2 ⟨g, rfl⟩)⟩
    · exact ⟨_, h3, conj_ne_one (ne_one_of_not_mem (hR.line_not_mem hz i)),
        hi i hip _ (isConj_iff.2 ⟨g, rfl⟩)⟩

namespace Model

variable {L : ℕ → Bool} {E : List ℕ → List ℕ → Bool} {ev : List ℕ → G} (hM : Model L E ev)
include hM

theorem p3Rel {p e₁ e₂ : ℕ} {g₁ g₂ z : List ℕ} (h : p3OK E L p g₁ g₂ z e₁ e₂ = true) :
    P3Rel p (ev g₁) (ev g₂) (ev z) := by
  obtain ⟨-, -, -, -, hzp, c₁, c₂, hrel, hp₁, hp₂⟩ := hM.p3OK_facts h
  exact ⟨hzp, c₁, c₂, hrel, ⟨e₁, hp₁⟩, ⟨e₂, hp₂⟩⟩

theorem cover_of_p3_center [Finite G] {p e₁ e₂ : ℕ} (hp : p.Prime)
    (hval : (Nat.card G).factorization p = 3)
    (hc : ∀ u, chW L u = true → ev u = 1 → E u [] = true) {g₁ g₂ z : List ℕ}
    (h : p3OK E L p g₁ g₂ z e₁ e₂ = true)
    (hgen : ∀ y, IsConj (ev z) y → SporKRestGenerating p y) : SporKRestCover p G := by
  obtain ⟨-, -, oz, hne, -⟩ := hM.p3OK_facts h
  exact (hM.p3Rel h).sporKRest_cover hp hval (hM.ne_one hc oz hne) (Or.inl hgen)

theorem cover_of_p3_lines [Finite G] {p e₁ e₂ : ℕ} (hp : p.Prime)
    (hval : (Nat.card G).factorization p = 3)
    (hc : ∀ u, chW L u = true → ev u = 1 → E u [] = true) {g₁ g₂ z : List ℕ}
    (h : p3OK E L p g₁ g₂ z e₁ e₂ = true) (t : ℕ → List ℕ)
    (hl : ∀ i < p, lineOK E L g₁ g₂ i (t i) = true)
    (h₂ : ∀ y, IsConj (ev g₂) y → SporKRestGenerating p y)
    (ht : ∀ i < p, ∀ y, IsConj (ev (t i)) y → SporKRestGenerating p y) : SporKRestCover p G := by
  obtain ⟨o₁, o₂, oz, hne, -⟩ := hM.p3OK_facts h
  refine (hM.p3Rel h).sporKRest_cover hp hval (hM.ne_one hc oz hne) (Or.inr ⟨h₂, ?_⟩)
  intro i hi y hy
  rw [← (hM.lineOK_eq o₁ o₂ (hl i hi)).2] at hy
  exact ht i hi y hy

end Model

end CFSG.KD.SporCov

end
