module

public import CFSG.ClassicalInvolution.Balance.QNineShape
public import CFSG.ClassicalInvolution.ModelFacts.StandardPairChevalley
public import CFSG.ClassicalInvolution.ModelFacts.StandardPairTwisted

public section

namespace CFSG.ClassicalInvolution.Balance

open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD
open CFSG.Assembly.LowTwoRank (StatedLieTag StatedLieAdmissible)

@[expose] def HasA2Pairs (t : StatedLieTag) : Prop :=
  t = .POmegaOdd ∨ t = .POmegaPlus ∨ t = .POmegaMinus ∨ t = .E6 ∨ t = .E7 ∨ t = .E8 ∨ t = .F4

theorem HasA2Pairs.ne_trialityD4 {t : StatedLieTag} (h : HasA2Pairs t) : t ≠ .trialityD4 := by
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

section Models

variable {p : ℕ} [Fact p.Prime]

theorem fundamental_leviBlockImage_of_hasA2Pairs (hp2 : p ≠ 2) {t : StatedLieTag} {n e : ℕ}
    (hadm : StatedLieAdmissible t n p e) (h : HasA2Pairs t) :
    ∀ R ∈ fundamentalSubgroups t (modelUniv t n p e Fact.out).D, LeviBlockImage p e R := by
  intro R hR
  obtain ⟨g, γ, hγ, rfl⟩ := hR
  have hlong : IsLongestRoot (modelUniv t n p e Fact.out).D γ := by
    refine hγ.resolve_right ?_
    rintro (⟨h1, -⟩ | ⟨h1, -⟩)
    · rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> cases h1
    · exact h.ne_trialityD4 h1
  have key : ∀ (δ : Fin (modelUniv t n p e Fact.out).D.rank → ℤ)
      (W : Subgroup (modelUniv t n p e Fact.out).K),
      WeakCT.LinearBlockStandardPair (GaloisField p e) W
        ((modelUniv t n p e Fact.out).D.rootGroup γ ⊔
          (modelUniv t n p e Fact.out).D.rootGroup (-γ))
        ((modelUniv t n p e Fact.out).D.rootGroup δ ⊔
          (modelUniv t n p e Fact.out).D.rootGroup (-δ)) →
      LeviBlockImage p e (conjSub g ((modelUniv t n p e Fact.out).D.rootGroup γ ⊔
        (modelUniv t n p e Fact.out).D.rootGroup (-γ))) := fun δ W hW =>
    Or.inl ⟨_, _, ModelFacts.linearBlockStandardPair_map_conj hW g⟩
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · obtain ⟨δ, -, -, W, hW⟩ := ModelFacts.exists_standardPair_partner_POmegaOdd p e n hadm hlong
    exact key δ W hW
  · obtain ⟨δ, -, -, W, hW⟩ := ModelFacts.exists_standardPair_partner_POmegaPlus p e n hadm hlong
    exact key δ W hW
  · obtain ⟨δ, -, -, W, hW⟩ :=
      ModelFacts.exists_standardPair_partner_POmegaMinus n p e hp2 hadm hlong
    exact key δ W hW
  · obtain rfl : n = 0 := hadm.2.2
    obtain ⟨δ, -, -, W, hW⟩ := ModelFacts.exists_standardPair_partner_E6 p e hadm hlong
    exact key δ W hW
  · obtain rfl : n = 0 := hadm.2.2
    obtain ⟨δ, -, -, W, hW⟩ := ModelFacts.exists_standardPair_partner_E7 p e hadm hlong
    exact key δ W hW
  · obtain rfl : n = 0 := hadm.2.2
    obtain ⟨δ, -, -, W, hW⟩ := ModelFacts.exists_standardPair_partner_E8 p e hadm hlong
    exact key δ W hW
  · obtain rfl : n = 0 := hadm.2.2
    obtain ⟨δ, -, -, W, hW⟩ := ModelFacts.exists_standardPair_partner_F4 p e hadm hlong
    exact key δ W hW

end Models

section Component

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] {Ω : Set (Subgroup G)} {x : G}

theorem exists_member_leviBlockImage_of_a2Tag (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f)
    (D : LieSystemData p f (locQuot Ω x) (locFamily Ω x)) (i : Fin D.card)
    (h : HasA2Pairs (D.tag i)) :
    ∃ L ∈ centralizingMembers Ω {x}, LeviBlockImage p f (locImg Ω x L) := by
  have hexp : D.exp i = f := by
    rcases D.exp_eq i with h' | ⟨h', -⟩
    · exact h'
    · exact absurd h' h.ne_trialityD4
  exact exists_member_leviBlockImage_of_model hq D i hexp
    (fundamental_leviBlockImage_of_hasA2Pairs hp2 (D.admissible i) h)

end Component

end CFSG.ClassicalInvolution.Balance
