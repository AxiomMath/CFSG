module

public import CFSG.ClassicalInvolution.Q3.Q3MTModel1

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3MT

open CFSG.Open hiding StatedLieTag
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Disconnected


section Graph

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {t : StatedLieTag} {k e : ℕ}
  (M : Ih8Model 3 1 Ω t k e) (hΩ : HypOmegaModU (.sl2 3 1) Ω) (hG2 : t ≠ .G2)
  (hD4 : t ≠ .trialityD4)

include M hΩ hG2 hD4

theorem noTriangle3
    (hNT : ∀ A ∈ M.cls, ∀ B ∈ M.cls, ∀ S ∈ M.cls, A ≠ B → A ≠ S → B ≠ S → Commutes A B →
      Commutes A S → Commutes B S → False) :
    ∀ K ∈ Ω, ∀ J ∈ omegaNbr Ω K, ∀ L ∈ omegaNbr Ω K, L ∈ omegaNbr Ω J → False := by
  intro K hK J hJ L hL hLJ
  obtain ⟨A, hA, rfl⟩ := (M.mem_iff K).mp hK
  obtain ⟨B, hB, rfl⟩ := (M.mem_iff J).mp hJ.1
  obtain ⟨S, hS, rfl⟩ := (M.mem_iff L).mp hL.1
  obtain ⟨hAB, cAB⟩ := (omegaNbr_iff3 M hΩ hG2 hD4 hA hB).mp hJ
  obtain ⟨hAS, cAS⟩ := (omegaNbr_iff3 M hΩ hG2 hD4 hA hS).mp hL
  obtain ⟨hBS, cBS⟩ := (omegaNbr_iff3 M hΩ hG2 hD4 hB hS).mp hLJ
  exact hNT A hA B hB S hS hAB hAS hBS cAB cAS cBS

theorem matching3
    (hMatch : ∀ A ∈ M.cls, ∀ B ∈ M.cls, ∀ S ∈ M.cls, A ≠ B → A ≠ S → B ≠ S → Commutes A B →
      Commutes A S → False) :
    ∀ K ∈ Ω, ∀ J ∈ omegaNbr Ω K, ∀ L ∈ omegaNbr Ω K, J = L := by
  intro K hK J hJ L hL
  obtain ⟨A, hA, rfl⟩ := (M.mem_iff K).mp hK
  obtain ⟨B, hB, rfl⟩ := (M.mem_iff J).mp hJ.1
  obtain ⟨S, hS, rfl⟩ := (M.mem_iff L).mp hL.1
  obtain ⟨hAB, cAB⟩ := (omegaNbr_iff3 M hΩ hG2 hD4 hA hB).mp hJ
  obtain ⟨hAS, cAS⟩ := (omegaNbr_iff3 M hΩ hG2 hD4 hA hS).mp hL
  by_cases hBS : B = S
  · rw [hBS]
  · exact (hMatch A hA B hB S hS hAB hAS hBS cAB cAS).elim

theorem edge3 (hc : ∃ R ∈ M.cls, ∃ S ∈ M.cls, R ≠ S ∧ Commutes R S) :
    ∃ K ∈ Ω, (omegaNbr Ω K).Nonempty := by
  obtain ⟨R, hR, S, hS, hRS, hc⟩ := hc
  exact ⟨R.map M.ψ, M.map_mem hR, S.map M.ψ,
    (omegaNbr_iff3 M hΩ hG2 hD4 hR hS).mpr ⟨hRS, hc⟩⟩

theorem dAdj_iff3 {A B : Subgroup (modelUniv t k 3 e Fact.out).K} (hA : A ∈ M.cls)
    (hB : B ∈ M.cls) : dAdj Ω (A.map M.ψ) (B.map M.ψ) ↔ A ≠ B ∧ Commutes A B := by
  unfold dAdj
  rw [omegaNbr_iff3 M hΩ hG2 hD4 hA hB, omegaNbr_iff3 M hΩ hG2 hD4 hB hA]
  constructor
  · rintro (h | ⟨h, hc⟩)
    · exact h
    · exact ⟨h.symm, hc.symm⟩
  · exact Or.inl

theorem dComp_ne3
    (hMatch : ∀ A ∈ M.cls, ∀ B ∈ M.cls, ∀ S ∈ M.cls, A ≠ B → A ≠ S → B ≠ S → Commutes A B →
      Commutes A S → False)
    {R₀ S₀ : Subgroup (modelUniv t k 3 e Fact.out).K} (hR₀ : R₀ ∈ M.cls) (hS₀ : S₀ ∈ M.cls)
    (hnc : ¬ Commutes R₀ S₀) (hstar : dstarAdj Ω (R₀.map M.ψ) (S₀.map M.ψ)) :
    dComp Ω (R₀.map M.ψ) ≠ dstarComp Ω (R₀.map M.ψ) := by
  have hne : R₀.map M.ψ ≠ S₀.map M.ψ := by
    rcases hstar.2 with h | h
    · exact h.2.1.symm
    · exact h.2.1
  intro heq
  have h1 : S₀.map M.ψ ∈ dComp Ω (R₀.map M.ψ) := by
    rw [heq]
    exact Relation.ReflTransGen.single hstar
  have key : ∀ J, Relation.ReflTransGen (fun X Y : Subgroup G => Y ∈ Ω ∧ dAdj Ω X Y)
      (R₀.map M.ψ) J → J = R₀.map M.ψ ∨ ∃ T ∈ M.cls, T ≠ R₀ ∧ Commutes R₀ T ∧ J = T.map M.ψ := by
    intro J hJ
    induction hJ with
    | refl => exact Or.inl rfl
    | @tail b c _ hbc ih =>
      obtain ⟨B', hB', rfl⟩ := (M.mem_iff c).mp hbc.1
      rcases ih with rfl | ⟨T, hT, hTR, hRT, rfl⟩
      · obtain ⟨hne', hc'⟩ := (dAdj_iff3 M hΩ hG2 hD4 hR₀ hB').mp hbc.2
        exact Or.inr ⟨B', hB', hne'.symm, hc', rfl⟩
      · obtain ⟨hTB, hcTB⟩ := (dAdj_iff3 M hΩ hG2 hD4 hT hB').mp hbc.2
        by_cases hBR : B' = R₀
        · exact Or.inl (by rw [hBR])
        · exact (hMatch T hT R₀ hR₀ B' hB' hTR hTB (Ne.symm hBR) hRT.symm hcTB).elim
  rcases key _ h1 with h | ⟨T, hT, hTR, hRT, hS⟩
  · exact hne h.symm
  · have := map_inj3 M hG2 hD4 hS₀ hT hS
    exact hnc (this ▸ hRT)

theorem starSubset3
    (hcomm : ∀ R ∈ M.cls, ∀ S ∈ M.cls, S.map M.ψ ∈ omegaStarNbr Ω (R.map M.ψ) → Commutes R S) :
    ∀ K ∈ Ω, omegaStarNbr Ω K ⊆ omegaNbr Ω K := by
  intro K hK J hJ
  obtain ⟨R, hR, rfl⟩ := (M.mem_iff K).mp hK
  obtain ⟨S, hS, rfl⟩ := (M.mem_iff J).mp hJ.1
  refine (omegaNbr_iff3 M hΩ hG2 hD4 hR hS).mpr ⟨fun h => hJ.2.1 (by rw [h]),
    hcomm R hR S hS hJ⟩

end Graph

end CFSG.ClassicalInvolution.Q3.Q3MT
