module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.BMTypeGen3
public import CFSG.LocalAnalysis.GLTheoremA.CatA.BMTypeRows

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H1420

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA.BMType
open CFSG.HardMathSupport.Solomon.Coordinator (SporadicOrdersTable sporOrd)
open CFSG.HardMathSupport.Timmesfeld.Coordinator (SporadicOuterLeTwo)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)

theorem typeHyp3_mcl (hOrd : SporadicOrdersTable) (hOut : SporadicOuterLeTwo)
    (hsimple : IsSimpleGroup (TauCeti.CFSGIndex.sporadic .McL).Group) :
    TypeHyp3 (S8.sporIs .McL) 898128000 where
  card T _ _ h := by
    obtain ⟨i, hi, ⟨e⟩⟩ := h
    simp only [S8.sporIs] at hi
    subst hi
    rw [Nat.card_congr e.toEquiv, hOrd .McL]
    rfl
  aut T _ _ h := by
    obtain ⟨i, hi, ⟨e⟩⟩ := h
    simp only [S8.sporIs] at hi
    subst hi
    haveI : IsSimpleGroup T := (MulEquiv.isSimpleGroup_congr e).2 hsimple
    have hcard : Nat.card T = 898128000 := by
      rw [Nat.card_congr e.toEquiv, hOrd .McL]
      rfl
    have hnab : ∃ a b : T, a * b ≠ b * a :=
      S8.HNRows.exists_noncomm_of_simple (by rw [hcard]; norm_num)
    have h2 : Nat.card (Outer T) ≤ 2 := hOut T inferInstance hnab .McL ⟨e⟩
    have hpos : 0 < Nat.card (Outer T) := by
      haveI : Finite (MulAut T) :=
        Finite.of_injective (fun f : MulAut T => (f : T → T)) fun _ _ h =>
          MulEquiv.ext (congrFun h)
      haveI : Finite (Outer T) :=
        Finite.of_surjective _ (QuotientGroup.mk'_surjective _ : Function.Surjective
          (QuotientGroup.mk' (inner T)))
      exact Nat.card_pos
    rcases (by omega : Nat.card (Outer T) = 1 ∨ Nat.card (Outer T) = 2) with h | h <;>
      rw [h] <;> norm_num
  big := by norm_num
  nine := by norm_num

theorem typeRow_mcl_of_cardRow (hOrd : SporadicOrdersTable) {t : TauCeti.SporadicName}
    (h : K14Spor.CardRow 898128000 t) : TypeRow (S8.sporIs .McL) t := by
  intro S _ _ e β hβ hβ1 J hJ hT
  obtain ⟨i, hi, ⟨f⟩⟩ := hT
  simp only [S8.sporIs] at hi
  subst hi
  exact h S e β hβ hβ1 J hJ ((Nat.card_congr f.toEquiv).trans (hOrd .McL))

end CFSG.LocalAnalysis.GLTheoremA.H1420

end
