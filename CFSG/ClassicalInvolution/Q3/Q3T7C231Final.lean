module

public import CFSG.ClassicalInvolution.Q3.Q3T7Stmt
public import CFSG.ClassicalInvolution.Q3.Q3T7C231Clique

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T7

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.Thompson

section Glue

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {W : Subgroup G}

theorem c231_mu_iso_of_clique (hP : Q3CL.PartIHypG Ω) (hW : W ∈ WSet Ω)
    (hclique : (muDelta Ω W).Nonempty ∧
      ∀ d ∈ muDelta Ω W, (Star3T.cent (muDelta Ω W) d).ncard = 2) :
    MuIsoE4 Ω W ∨ MuIsoS4 Ω W := by
  obtain ⟨⟨d₀, hd₀⟩, hcl⟩ := hclique
  have hTT : Star3T.IsTT (muDelta Ω W) := Q3T6.Mu.isTT_muDelta hP hW
  have hS : Star3T.IsStar (muDelta Ω W) := Q3T6.Mu.isStar_muDelta (Q3CL.T8.ctxOf hP hW)
  by_cases hconn : ∀ d ∈ muDelta Ω W, ∀ a ∈ muDelta Ω W, Star3T.Conn (muDelta Ω W) d a
  · left
    set Δ := muDelta Ω W
    obtain ⟨d', hne, hcent⟩ : ∃ d', d₀ ≠ d' ∧ Star3T.cent Δ d₀ = {d₀, d'} := by
      obtain ⟨x, y, hxy, hxy'⟩ := Set.ncard_eq_two.mp (hcl d₀ hd₀)
      have hdx : d₀ ∈ ({x, y} : Set _) := hxy' ▸ Star3T.self_mem_cent hd₀
      rcases hdx with rfl | hdy
      · exact ⟨y, hxy, hxy'⟩
      · rw [Set.mem_singleton_iff] at hdy
        subst hdy
        exact ⟨x, fun e => hxy e.symm, by rw [hxy', Set.pair_comm]⟩
    have hd'c : d' ∈ Star3T.cent Δ d₀ := by rw [hcent]; exact Or.inr rfl
    have hd'Δ : d' ∈ Δ := hd'c.1
    have hcomm : d₀ * d' = d' * d₀ := hd'c.2.symm
    have hcent' : Star3T.cent Δ d' = {d₀, d'} := by
      have hsub : ({d₀, d'} : Set _) ⊆ Star3T.cent Δ d' := by
        intro x hx
        rcases hx with rfl | rfl
        · exact ⟨hd₀, hcomm⟩
        · exact Star3T.self_mem_cent hd'Δ
      exact (Set.eq_of_subset_of_ncard_le hsub
        (by rw [hcl d' hd'Δ, Set.ncard_pair hne]) (Set.toFinite _)).symm
    have hall : ∀ a, Relation.ReflTransGen (Star3T.Adj Δ) d₀ a → a = d₀ ∨ a = d' := by
      intro a hb
      induction hb with
      | refl => exact Or.inl rfl
      | @tail b c _ hbc ih =>
        obtain ⟨-, hc, hbc⟩ := hbc
        rcases ih with rfl | rfl
        · have : c ∈ Star3T.cent Δ b := ⟨hc, hbc.symm⟩
          rw [hcent] at this
          exact this
        · have : c ∈ Star3T.cent Δ b := ⟨hc, hbc.symm⟩
          rw [hcent'] at this
          exact this
    have hΔeq : Δ = {d₀, d'} := by
      ext a
      constructor
      · exact fun ha => hall a (hconn d₀ hd₀ a ha)
      · rintro (rfl | rfl)
        · exact hd₀
        · exact hd'Δ
    have hgen : Subgroup.closure ({d₀, d'} : Set ↥(muGroup Ω W)) = ⊤ := by
      rw [← hΔeq]
      exact hTT.closure_eq_top
    exact MuTab.nonempty_mulEquiv_klein (hTT.mul_self d₀ hd₀) (hTT.mul_self d' hd'Δ) hcomm
      (hTT.ne_one d₀ hd₀) (hTT.ne_one d' hd'Δ) hne hgen
  · right
    push Not at hconn
    obtain ⟨d, hd, a, ha, hnc⟩ := hconn
    obtain ⟨e, -⟩ := Star3T.exists_mulEquiv_perm_four hTT hS hd ha hnc (hcl d hd)
    exact ⟨e⟩

end Glue

section Final


theorem c23_1_clique3 {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
    {K K' : Subgroup G} {z : G} (h : Hyp23Three Ω K K' z) {W : Subgroup G} (hW : W ∈ WSet Ω) :
    (muDelta Ω W).Nonempty ∧
      ∀ d ∈ muDelta Ω W, (Star3T.cent (muDelta Ω W) d).ncard = 2 := by
  have hs := h.1.stand
  exact c231_clique (Q3CL.partIHypG_of_modU hs.hyp hs.aEmpty) hs.mem hs.trans h.1.hz h.1.hK'
    h.1.hne h.2 hW

theorem c23_1_proved3 : C23_1Three := by
  intro G _ _ _ Ω K K' z h W hW
  have hs := h.1.stand
  exact c231_mu_iso_of_clique (Q3CL.partIHypG_of_modU hs.hyp hs.aEmpty) hW (c23_1_clique3 h hW)

end Final

end CFSG.ClassicalInvolution.Q3.Q3T7
