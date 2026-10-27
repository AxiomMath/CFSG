module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Hyp.Step
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Hyp.Thm24ThreeSimpleCore
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Stage3Defs

public section

namespace CFSG.EvenSporadicStandard.Induction.Fi

open Subgroup CFSG.Blueprint.NativeSporadic CFSG.EvenSporadicStandard.Solomon78

export Hyp (Fi23Excl NotExc SporadicNotExc)

@[expose] def Link5bSection : Prop :=
  ∀ (H : Type) [Group H] [Finite H] (N : Subgroup H), FStarSimple N → N.index ≤ 2 →
    CFSG.Assembly.KProper CFSG.Blueprint.Catalog H → ∀ (P Q : Subgroup H),
      CFSG.IsQuasisimple ↥Q → Q ≠ N → CFSG.IsQuasisimple ↥P → P ≠ Q →
      ∀ (T : Subgroup H) (s : H), IsCompIn Q (centralizer (T : Set H)) → s ^ 2 ∈ T →
        IsCompIn P (centralizer ((T ⊔ zpowers s : Subgroup H) : Set H)) →
        P ≤ Q ⊔ Q.map (MulAut.conj s).toMonoidHom → Sol78Link5b Q P s →
          ∃ (Y : Type) (_ : Group Y) (_ : Finite Y) (N' P' : Subgroup Y),
            Nat.card Y < Nat.card H ∧ CFSG.SignalizerFunctorTheorem.IsSectionOf Y H ∧
            FStarSimple N' ∧ N'.index ≤ 2 ∧
            CFSG.Assembly.KProper CFSG.Blueprint.Catalog Y ∧ SolStd P' ∧
            CFSG.IsQuasisimple ↥P' ∧ Nonempty ((↥P ⧸ center ↥P) ≃* (↥P' ⧸ center ↥P')) ∧
            Nonempty ((↥Q ⧸ center ↥Q) ≃* ↥N')

variable {H : Type} [Group H] [Finite H] {N : Subgroup H}

omit [Finite H] in
theorem lt_inL_left' {P Q : Subgroup H} (h : Lt P Q) : InL P := by
  obtain ⟨S₁, T₁, hS₁, -, hS₁p, -, -, hP, -, -⟩ := h
  exact ⟨S₁, hS₁, hS₁p, hP⟩

omit [Finite H] in
theorem lt_inL_right' {P Q : Subgroup H} (h : Lt P Q) : InL Q := by
  obtain ⟨S₁, T₁, -, hT₁, -, hT₁p, -, -, hQ, -⟩ := h
  exact ⟨T₁, hT₁, hT₁p, hQ⟩

theorem inL_ne_of_fStarSimple' (hN : FStarSimple N) {Q : Subgroup H} (hQ : InL Q) : Q ≠ N := by
  rintro rfl
  obtain ⟨T', hT', -, hc⟩ := hQ
  exact hT' (hN.eq_bot_of_isCompIn hc)

theorem fiStdBare_of_maximal (thm22 : Sol78Thm22At H)
    (hkp : CFSG.Assembly.KProper CFSG.Blueprint.Catalog H) (hN : FStarSimple N)
    (hidx : N.index ≤ 2) {M : Subgroup H}
    (hmax : Maximal M) (_hMN : M ≠ N) (hrank : 3 ≤ CFSG.pRank 2 ↥M) : StdBare M :=
  thm22 hkp N hN hidx M hmax hrank

end CFSG.EvenSporadicStandard.Induction.Fi
