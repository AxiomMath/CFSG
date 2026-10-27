module

public import CFSG.ClassicalInvolution.Asc77.AscMuTabNonab
public import CFSG.ClassicalInvolution.Asc77.AscIHSectD

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank
  CFSG.ClassicalInvolution.RouteD CFSG.ClassicalInvolution.Disconnected

namespace Ih8Model

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {t : StatedLieTag} {k e : ℕ} (M : Ih8Model p f Ω t k e)

include M

theorem muTab_omegaNbr_iff (hΩ : HypOmegaMod p f Ω) (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f)
    (hG2 : t ≠ .G2) (hD4 : t ≠ .trialityD4) {R S : Subgroup (modelUniv t k p e Fact.out).K}
    (hR : R ∈ M.cls) (hS : S ∈ M.cls) :
    S.map M.ψ ∈ omegaNbr Ω (R.map M.ψ) ↔ R ≠ S ∧ Commutes R S := by
  constructor
  · intro hJ
    exact ⟨fun h => hJ.2.1 (by rw [h]), M.commutes_of_omegaNbr_sect hΩ hp2 hq hG2 hD4 hR hS hJ⟩
  · rintro ⟨hne, hc⟩
    refine MuTab.mem_omegaNbr_of_commutes (M.map_mem hS) (fun h => hne ?_)
      (ih8_commutes_map M.ψ hc)
    exact ih8_eq_of_map_eq M.ψ M.ker_le_center (M.cls_perfect hp2 hD4 hq hR)
      (M.cls_perfect hp2 hD4 hq hS) h.symm

theorem muTab_noTriangle (hΩ : HypOmegaMod p f Ω) (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f)
    (hG2 : t ≠ .G2) (hD4 : t ≠ .trialityD4)
    (hNT : ∀ A ∈ M.cls, ∀ B ∈ M.cls, ∀ S ∈ M.cls, A ≠ B → A ≠ S → B ≠ S → Commutes A B →
      Commutes A S → Commutes B S → False) :
    ∀ K ∈ Ω, ∀ J ∈ omegaNbr Ω K, ∀ L ∈ omegaNbr Ω K, L ∈ omegaNbr Ω J → False := by
  intro K hK J hJ L hL hLJ
  obtain ⟨A, hA, rfl⟩ := (M.mem_iff K).mp hK
  obtain ⟨B, hB, rfl⟩ := (M.mem_iff J).mp hJ.1
  obtain ⟨S, hS, rfl⟩ := (M.mem_iff L).mp hL.1
  obtain ⟨hAB, cAB⟩ := (M.muTab_omegaNbr_iff hΩ hp2 hq hG2 hD4 hA hB).mp hJ
  obtain ⟨hAS, cAS⟩ := (M.muTab_omegaNbr_iff hΩ hp2 hq hG2 hD4 hA hS).mp hL
  obtain ⟨hBS, cBS⟩ := (M.muTab_omegaNbr_iff hΩ hp2 hq hG2 hD4 hB hS).mp hLJ
  exact hNT A hA B hB S hS hAB hAS hBS cAB cAS cBS

theorem muTab_matching (hΩ : HypOmegaMod p f Ω) (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f)
    (hG2 : t ≠ .G2) (hD4 : t ≠ .trialityD4)
    (hMatch : ∀ A ∈ M.cls, ∀ B ∈ M.cls, ∀ S ∈ M.cls, A ≠ B → A ≠ S → B ≠ S → Commutes A B →
      Commutes A S → False) :
    ∀ K ∈ Ω, ∀ J ∈ omegaNbr Ω K, ∀ L ∈ omegaNbr Ω K, J = L := by
  intro K hK J hJ L hL
  obtain ⟨A, hA, rfl⟩ := (M.mem_iff K).mp hK
  obtain ⟨B, hB, rfl⟩ := (M.mem_iff J).mp hJ.1
  obtain ⟨S, hS, rfl⟩ := (M.mem_iff L).mp hL.1
  obtain ⟨hAB, cAB⟩ := (M.muTab_omegaNbr_iff hΩ hp2 hq hG2 hD4 hA hB).mp hJ
  obtain ⟨hAS, cAS⟩ := (M.muTab_omegaNbr_iff hΩ hp2 hq hG2 hD4 hA hS).mp hL
  by_cases hBS : B = S
  · rw [hBS]
  · exact (hMatch A hA B hB S hS hAB hAS hBS cAB cAS).elim

theorem muTab_edge (hΩ : HypOmegaMod p f Ω) (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f)
    (hG2 : t ≠ .G2) (hD4 : t ≠ .trialityD4)
    (hc : ∃ R ∈ M.cls, ∃ S ∈ M.cls, R ≠ S ∧ Commutes R S) :
    ∃ K ∈ Ω, (omegaNbr Ω K).Nonempty := by
  obtain ⟨R, hR, S, hS, hRS, hc⟩ := hc
  exact ⟨R.map M.ψ, M.map_mem hR, S.map M.ψ,
    (M.muTab_omegaNbr_iff hΩ hp2 hq hG2 hD4 hR hS).mpr ⟨hRS, hc⟩⟩

omit [Finite G] in
theorem muTab_map_inj (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) (hD4 : t ≠ .trialityD4)
    {R S : Subgroup (modelUniv t k p e Fact.out).K} (hR : R ∈ M.cls) (hS : S ∈ M.cls)
    (h : R.map M.ψ = S.map M.ψ) : R = S :=
  ih8_eq_of_map_eq M.ψ M.ker_le_center (M.cls_perfect hp2 hD4 hq hR)
    (M.cls_perfect hp2 hD4 hq hS) h

theorem muTab_dAdj_iff (hΩ : HypOmegaMod p f Ω) (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f)
    (hG2 : t ≠ .G2) (hD4 : t ≠ .trialityD4) {A B : Subgroup (modelUniv t k p e Fact.out).K}
    (hA : A ∈ M.cls) (hB : B ∈ M.cls) :
    dAdj Ω (A.map M.ψ) (B.map M.ψ) ↔ A ≠ B ∧ Commutes A B := by
  unfold dAdj
  rw [M.muTab_omegaNbr_iff hΩ hp2 hq hG2 hD4 hA hB, M.muTab_omegaNbr_iff hΩ hp2 hq hG2 hD4 hB hA]
  constructor
  · rintro (h | ⟨h, hc⟩)
    · exact h
    · exact ⟨h.symm, hc.symm⟩
  · exact Or.inl

theorem muTab_dComp_ne (hΩ : HypOmegaMod p f Ω) (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f)
    (hG2 : t ≠ .G2) (hD4 : t ≠ .trialityD4)
    (hMatch : ∀ A ∈ M.cls, ∀ B ∈ M.cls, ∀ S ∈ M.cls, A ≠ B → A ≠ S → B ≠ S → Commutes A B →
      Commutes A S → False)
    {R₀ S₀ : Subgroup (modelUniv t k p e Fact.out).K} (hR₀ : R₀ ∈ M.cls) (hS₀ : S₀ ∈ M.cls)
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
      · obtain ⟨hne', hc'⟩ := (M.muTab_dAdj_iff hΩ hp2 hq hG2 hD4 hR₀ hB').mp hbc.2
        exact Or.inr ⟨B', hB', hne'.symm, hc', rfl⟩
      · obtain ⟨hTB, hcTB⟩ := (M.muTab_dAdj_iff hΩ hp2 hq hG2 hD4 hT hB').mp hbc.2
        by_cases hBR : B' = R₀
        · exact Or.inl (by rw [hBR])
        · exact (hMatch T hT R₀ hR₀ B' hB' hTR hTB (Ne.symm hBR) hRT.symm hcTB).elim
  rcases key _ h1 with h | ⟨T, hT, hTR, hRT, hS⟩
  · exact hne h.symm
  · have := M.muTab_map_inj hp2 hq hD4 hS₀ hT hS
    exact hnc (this ▸ hRT)

end Ih8Model

end CFSG.ClassicalInvolution.Asc77
