module

public import CFSG.Quasithin.EmptyFaithful.SzC4S8DMain
public import CFSG.GH74.QTGen4.DCopy.Quasithin.EmptyFaithful.S153H31
public import CFSG.GH74.QTGen4.DCopy.Quasithin.EmptyFaithful.SzMSWC134
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch11StatementsInputsAS
public import CFSG.Quasithin.EmptyFaithful.SBc11Case45
public import CFSG.Quasithin.EmptyFaithful.SBc11Hat

public section

namespace CFSG.Quasithin.SzC4

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.SBc11
open scoped commutatorElement Pointwise

theorem input31MSOutcome_of_c132_corrW_F4 (h113 : StageLemma14113) (hC132 : ASInputs.AS_C_1_32_F4)
    (hC134 : SzMSW.AS_C_1_34_corrW_F4) : Input31MSOutcome_F4 := by
  intro G _ _ T Mc M V₁ V₂ Yp I L t c hlist _
  have hMS := isMSPair_of_ctx c hlist
  have hLc : L ∈ cComp I := (ctx_basic c).1
  have hset := coe_eq_mul_of_ctx c
  unfold Outcome31
  rcases hC132 G I (Sgp153 T V₁) L hMS hLc hset with
    hg2 | halt | hsp4 | hhat | ⟨n, F, hF, hFin, α, hcard, hmod⟩
  · exact ⟨Or.inr (Or.inl hg2), centralizer_UI_eq_pCoreOf_of_g2Block c hg2⟩
  · exact ⟨Or.inl halt, centralizer_UI_eq_pCoreOf_of_altBlock c halt⟩
  · exact (not_isSp4Block c hlist hsp4).elim
  · exact (not_isHatA6Block c hlist hhat).elim
  · obtain ⟨hn, hpsl⟩ := sl3_case c hlist hcard hmod
    subst hn
    have hF2 : Fintype.card F = 2 := by simpa using hcard
    refine ⟨Or.inr (Or.inr ⟨hpsl, ?_⟩), sl3_centralizer c hlist hF2 hmod⟩
    obtain ⟨i, hi⟩ := hC134 G I (Sgp153 T V₁) L hMS hLc hset ⟨1, F, hF, hFin, α, hcard, hmod⟩
    match i, hi with
    | 0, h => exact False.elim h
    | 1, h => exact Or.inl h
    | 2, h => exact Or.inr (Or.inl h)
    | 3, h => exact Or.inr (Or.inr h)
    | 4, h => exact (s8_case4_false_of_rigidAt h113 c hlist h.1 fun hn1 =>
        c134Case4RigidAt_of_zq2 hset h.1 hn1 (zq2_of_abW h.1 hn1 h.2)).elim
    | 5, h => exact (not_isC134Case5 h113 c h).elim
    | _ + 6, h => exact False.elim h

end CFSG.Quasithin.SzC4
