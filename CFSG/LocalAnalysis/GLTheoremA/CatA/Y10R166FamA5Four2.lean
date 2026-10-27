module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R166FamA5Four4
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GU64Glue
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R166Cases

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F

open CFSG.Open CFSG.Assembly CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag

theorem exists_mulEquiv_projectiveSL_six_of_hasLabel {K : Type} [Group K] [Finite K]
    (hK : HasLabel K (· = ⟨.A, 5, 2⟩)) (hZ : Subgroup.center K = ⊥) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 4 ∧
      Nonempty (K ≃* LinearFlag.projectiveSL 6 F) := by
  obtain ⟨F, hField, hFinite, hCard, ⟨e⟩⟩ := model_A hZ hK rfl
  have hCard' : Nat.card F = 4 := by
    simpa using hCard
  have e' : K ≃* LinearFlag.projectiveSL 6 F := by
    rw [CFSG.Assembly.largeEvenSLGroup_eq_statedSL 6] at e
    exact e.trans (CFSG.CGT.Timmesfeld75.projectiveSLMulEquivStatedProj 6 F).symm
  exact ⟨F, hField, hFinite, hCard', ⟨e'⟩⟩

section Certificates


theorem i166On_famA5Four_of_transport
    (htr : ∀ {K R : Type} [Group K] [Finite K] [Group R] [Finite R], (K ≃* R) → ∀ {p : ℕ},
      (∃ (q : ℕ) (B' : Subgroup R) (x' : R) (J : Subgroup R), Concl166S R p q B' x' J) →
      ∃ (q : ℕ) (B' : Subgroup K) (x' : K) (J : Subgroup K), Concl166S K p q B' x' J) :
    I166On i166FamA5Four := by
  intro K _ _ lab p hK hfam hp hp2 hns he hr
  obtain ⟨hlab, hz, hp5⟩ := hfam
  subst hlab
  subst hp5
  obtain ⟨F, hField, hFinite, hCard, ⟨e⟩⟩ :=
    exists_mulEquiv_projectiveSL_six_of_hasLabel hK hz
  letI : Field F := hField
  letI : Finite F := hFinite
  have hmodel : ∃ q B' x' J, Concl166S (LinearFlag.projectiveSL 6 F) 5 q B' x' J :=
    exists_concl166S_projectiveSL_six (F := F) hCard
  exact htr e hmodel

end Certificates

end CFSG.LocalAnalysis.GLTheoremA.Y10F
