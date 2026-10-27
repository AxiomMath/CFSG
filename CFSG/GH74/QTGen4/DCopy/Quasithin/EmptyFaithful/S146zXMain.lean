module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.EmptyFaithful.S14612DC
public import CFSG.GH74.QTGen4.DCopy.Quasithin.EmptyFaithful.S146zQLists
public import CFSG.Quasithin.Background.C2A3Orbits
public import CFSG.Quasithin.EmptyFaithful.S146zXCore

public section

namespace CFSG.Quasithin.S146zX

open CFSG.Open hiding StatedClassicalModel StatedSL StatedLieTag
open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank


theorem input14614Lists_of_prop134_F4
    (h12 : Stage14612PartP_F4) (hA37 : A37ForSQTK) (hA38 : A38ForSQTK) (hD36 : D36) (hD37 : D37)
    (hD321 : D321) (hI5 : Insp5a) (hD310 : D310) (hD391 : D391) (hI4 : Insp4)
    (h134E9 : EmptyFaithfulMultiple.Prop134E9He) (h134Five : Prop134Five) :
    Input14614Lists_F4 := by
  intro G _ _ T M S H PQ p hred hmax hne
  classical
  have hA3 : A3Orbits G := a3Orbits_of_a37_a38 hA37 hA38
  obtain ⟨hp, H₀, H₁, H₂, t₀, hdec⟩ := h12 G T M S H PQ p hred hmax
  have : Fact p.Prime := ⟨hred.prime⟩
  have hp2 : p ≠ 2 := hred.odd
  have hTMc : T ≤ mcOf T := S.isHTM_mcOf.1.1
  have hsylMc : IsSylowTwoOf T (mcOf T) := isSylowTwoOf_of_quasithinIsSylowTwo S.hyp.sylow hTMc
  have hKMc : oTwoUpper H ≤ mcOf T := (oTwoUpper_le H).trans (S.le_mcOf hred.isHTM)
  have hX : IsXi T (oTwoUpper H) := isXi_oTwoUpper S hred hdec
  have hi : (pCoreOf 2 (oTwoUpper H)).relIndex (oTwoUpper H) = p ^ 2 :=
    relIndex_pCoreOf_oTwoUpper_of_isDecP S hred hdec
  have hpX : p ∣ Nat.card (oTwoUpper H) := by
    rw [card_eq_card_pCoreOf_mul_relIndex, hi]
    exact Dvd.dvd.mul_left (dvd_pow_self p two_ne_zero) _
  obtain ⟨P, hP, -⟩ := exists_isSylowIn_ge p (bot_le : ⊥ ≤ oTwoUpper H) IsPGroup.of_bot
  have hPc : Nat.card P = p ^ 2 := by rw [hX.card_sylow hp2 hpX hP, hi]
  have hPMc : pCoreOf 2 (mcOf T) ≠ ⊥ := S.isHTM_mcOf.1.2
  have := S.hyp.simple
  have hsq : CFSG.SectionRank.IsSQTKCat ↥(mcOf T) :=
    (qtkeCore_of_cat S.hyp.nonabelian S.hyp.qtke).1 (mcOf T) hPMc
  have hout : Out134 p T (mcOf T) (oTwoUpper H) P := by
    rcases hp with hp | hp
    · subst hp
      exact out134_of_three h134E9 hsq hPMc hsylMc hKMc hX (by simpa using hi) hP.le
        hP.isPGroup (by simpa using hPc)
    · exact out134_of_five h134Five hp hsq hPMc hsylMc hKMc hX hi hP.le hP.isPGroup hPc
  exact lists_of_out134 hA37 hA38 hD36 hD37 hD321 hI5 hD310 hD391 hI4 hA3 S hred hp hdec hne hX hP
    hPc hout

end CFSG.Quasithin.S146zX
