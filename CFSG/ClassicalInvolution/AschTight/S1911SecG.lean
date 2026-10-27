module

public import CFSG.ClassicalInvolution.AschTight.S1911SecF

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.S1911

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.RankThreeCoreUniqueness CFSG.RankThreeCoreUniqueness.Helpers

@[expose] def SectionThm6Stmt (p : ℕ) [Fact p.Prime] : Prop :=
  ∀ e : ℕ, p ≠ 2 → 5 ≤ p ^ e → ∀ n : ℕ, CITBelowU p e n →
    ∀ (Y₀ : Type) [Group Y₀] [Finite Y₀], Nat.card Y₀ < n →
      ∀ Λ₀ : Set (Subgroup Y₀), HypOmegaMod p e Λ₀ → Λ₀.Nonempty → Disconnected.DEdgeless Λ₀ →
        SectionLieType p e Λ₀ (omegaGen Λ₀) .PSL 3 ∨ SectionLieType p e Λ₀ (omegaGen Λ₀) .PSU 3 ∨
          SectionLieType p e Λ₀ (omegaGen Λ₀) .G2 0 ∨
            SectionLieType p e Λ₀ (omegaGen Λ₀) .trialityD4 0

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
  {K : Subgroup G} {z : G} {S : Sylow 2 G} {W : Subgroup G}

theorem sectionLieType_fieldInvolution (hT6 : SectionThm6Stmt p) (hd : Sec19Data p f K z S W)
    (h9 : p ^ f ≠ 9) {a : G} (haS : a ∈ (S : Subgroup G)) (ha2 : a * a = 1)
    (haX : a ∉ sec19X K z ⊔ centralizerModOdd ⊤ K) :
    ∃ e₀ : ℕ, f = 2 * e₀ ∧ 5 ≤ p ^ e₀ ∧ ∃ hzA : z ∈ Subgroup.centralizer ({a} : Set G),
      IsClassicalMember p e₀ (perfectCoreIn K a) ⟨z, hzA⟩ ∧
      (SectionLieType p e₀ (conjFamily (perfectCoreIn K a)) (conjGen (perfectCoreIn K a)) .PSL 3 ∨
        SectionLieType p e₀ (conjFamily (perfectCoreIn K a)) (conjGen (perfectCoreIn K a)) .PSU 3 ∨
        SectionLieType p e₀ (conjFamily (perfectCoreIn K a)) (conjGen (perfectCoreIn K a)) .G2 0 ∨
        SectionLieType p e₀ (conjFamily (perfectCoreIn K a)) (conjGen (perfectCoreIn K a))
          .trialityD4 0) := by
  obtain ⟨e₀, hf, h5, hzA, hmem, hΩ, hDE, hlt, hIH, -⟩ :=
    sectionData_fieldInvolution hd h9 haS ha2 haX
  exact ⟨e₀, hf, h5, hzA, hmem, hT6 e₀ hd.tight.branch.odd h5 _ hIH _ hlt _ hΩ
    ⟨_, ⟨1, conjSub_one _⟩⟩ hDE⟩

end CFSG.ClassicalInvolution.Disconnected.AschTight.S1911
