module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.SpBranchL2D
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.SpBranchKillD

public section

namespace CFSG.EvenSmallLie.OmegaEight.SpBranch

open Subgroup

variable {G : Type*} [Group G] {T₁ : Subgroup G} {N : ℕ} {mul : ℕ → ℕ → ℕ}
  (Φ : CodeIso T₁ N mul) {inv : ℕ → ℕ} {gens : List ℕ} (h0 : mul 0 0 = 0)
  (hinv : invOK mul inv N = true) (hgens : ∀ g ∈ gens, g < N) (hG : Gen mul gens N)

include Φ h0 hinv hgens hG in
theorem like_two {t : G} (ht : t ∈ T₁) {C : List (ℕ × ℕ)} (hcls : kClassOK mul inv gens N C = true)
    {m : ℕ} (hm : 1 < m)
    (htO : orbOK mul inv N (Φ.f ⟨t, ht⟩) (kRec mul inv gens m (Φ.f ⟨t, ht⟩)) = true)
    (htC : orbClosed mul inv gens (Φ.f ⟨t, ht⟩) (kRec mul inv gens m (Φ.f ⟨t, ht⟩)) = true)
    (htl : (kRec mul inv gens m (Φ.f ⟨t, ht⟩)).length = m) {a b : ℕ}
    (hX : ∀ r ∈ kRepsC C m, kCount mul (kInv mul N) r = kCount mul (kInv mul N) (Φ.f ⟨t, ht⟩) →
      kCount mul (kOrd4 mul N) r = kCount mul (kOrd4 mul N) (Φ.f ⟨t, ht⟩) → r = a ∨ r = b) :
    ∀ u, Like T₁ t u → ∃ r ∈ ({eltT Φ a, eltT Φ b} : Set G), ∃ g ∈ T₁, g * r * g⁻¹ = u := by
  intro u hu
  have huT : u ∈ T₁ := hu.1
  have hl := (like_iff ht huT).1 hu
  obtain ⟨hnd, hrecC, hsumC⟩ := classOK_parts hcls
  obtain ⟨r, hr, g, hg⟩ := like_rep_gen Φ h0 hinv hgens hG (recM mul inv gens) hnd hrecC hsumC
    htO htC htl hm (ti := (kCount mul (kInv mul N) (Φ.f ⟨t, ht⟩),
      kCount mul (kOrd4 mul N) (Φ.f ⟨t, ht⟩))) rfl rfl hl
  unfold kX at hr
  rw [List.mem_filter, Bool.and_eq_true, beq_iff_eq, beq_iff_eq] at hr
  obtain ⟨hrR, h1, h2⟩ := hr
  have hab := hX r hrR h1 h2
  refine ⟨eltT Φ r, ?_, g, g.2, ?_⟩
  · rcases hab with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
  · have := congrArg Subtype.val hg
    simpa [eltT] using this

end CFSG.EvenSmallLie.OmegaEight.SpBranch

end
