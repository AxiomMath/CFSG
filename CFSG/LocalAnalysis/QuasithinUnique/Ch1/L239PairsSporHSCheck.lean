module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatHS
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsSporLatWit
public meta import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatHS
public meta import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsSporLatWit
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsSporHSCheckInputs
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsSporLatWitLit
public import Certificates.Certificate4089
public import Certificates.Certificate4102
public import Certificates.Certificate4140
public import Certificates.Certificate3167

public section

namespace CFSG.QuasithinUnique.Vol2Native.L239.HSPairs

open CFSG.QuasithinUnique CFSG.QuasithinUnique.Ch1.SporLat CFSG.QuasithinUnique.Ch1.SporLat.HS
  CFSG.QuasithinUnique.K1.SporadicPerm CFSG.Sporadic.SmallF2 CFSG.Blueprint
open CFSG.Sporadic.HS.Native (hsData)

theorem hs_wit_cert :
    (OmegaSpec ptAct hsL1.toArray hsDelta hsOm1 ∧ hsOm1.lbl.size = 15 ∧
      Wit3Ok hsData.n ptAct hsL1 hsOm1.lbl.toList b31 q31a q31b ∧
      WitPOk hsData.n ptAct hsL1 hsOm1.lbl.toList 5 b51 q51) ∧
    (OmegaSpec ptAct hsL2.toArray hsDelta hsOm2 ∧ hsOm2.lbl.size = 21 ∧
      Wit3Ok hsData.n ptAct hsL2 hsOm2.lbl.toList b32 q32a q32b ∧
      WitPOk hsData.n ptAct hsL2 hsOm2.lbl.toList 7 b72 q72) :=
  Certificates.certificate4089

theorem hs_J1 : 1 < hsCtx.J := by rw [hs_J]; norm_num

theorem hs_J2 : 2 < hsCtx.J := by rw [hs_J]; norm_num

theorem hs_lbl1 : hsLatK.Om[1]!.lbl.size = 15 := (hs_Om_size 1 (by norm_num)).trans rfl

theorem hs_lbl2 : hsLatK.Om[2]!.lbl.size = 21 := (hs_Om_size 2 (by norm_num)).trans rfl

theorem hs_odd1 : hsCtx.D.Om[1]!.lbl.size % 2 = 1 := by
  have h : hsLatK.Om[1]!.lbl.size = 15 := hs_lbl1
  show hsLatK.Om[1]!.lbl.size % 2 = 1
  omega

theorem hs_odd2 : hsCtx.D.Om[2]!.lbl.size % 2 = 1 := by
  have h : hsLatK.Om[2]!.lbl.size = 21 := hs_lbl2
  show hsLatK.Om[2]!.lbl.size % 2 = 1
  omega

theorem hs_sTabs : hsCtx.D.sTabs = hsSTabs :=
  rfl

theorem hs_member_eq {wg : List ℕ} (hw : ∀ l ∈ wg, l < 2)
    {Ω : OmegaData (List ℕ)}
    (hΩ : OmegaSpec ptAct (hsSTabs ++ [wordTabA #[hsTa, hsTb] hsData.n wg]).toArray hsDelta Ω)
    {j : ℕ} (hj : j < 5) (hsz : Ω.lbl.size = #[1, 15, 21, 3, 3][j]!)
    (huniq : ∀ i < 5, #[1, 15, 21, 3, 3][i]! = #[1, 15, 21, 3, 3][j]! → i = j) :
    hsCtx.litGrp wg = hsCtx.Y j := by
  have hΩ' : OmegaSpec hsCtx.A.act
      (hsCtx.D.sTabs ++ [wordTabA #[hsCtx.ta, hsCtx.tb] hsData.n wg]).toArray hsCtx.Δ Ω := by
    rw [hs_sTabs]
    exact hΩ
  have hc : Nat.card (hsCtx.litGrp wg) = #[1, 15, 21, 3, 3][j]! * 512 := by
    rw [hsCtx.litGrp_card hw hΩ', hsz]
    rfl
  obtain ⟨i, hi, hZ⟩ := hs_complete _ (hsCtx.S_le_litGrp wg)
  rcases Nat.lt_or_ge i 5 with hi5 | hi5
  · have e : memberOrTop 5 hsCtx.Y i = hsCtx.Y i := by simp [memberOrTop, hi5]
    rw [e] at hZ
    have h2 := hs_member_card i hi5
    rw [← hZ, hc] at h2
    rw [hZ, huniq i hi5 (by omega)]
  · have e : memberOrTop 5 hsCtx.Y i = ⊤ := by
      simp only [memberOrTop]
      rw [if_neg (by omega)]
    rw [e] at hZ
    have h2 : Nat.card (hsCtx.litGrp wg) = 2 ^ 9 * 86625 := by
      rw [hZ, Subgroup.card_top, hs_card]
    rw [hc] at h2
    exfalso
    interval_cases j <;> simp at h2

theorem hs_goodLocal_Y1 : GoodLocal (hsCtx.Y 1) := by
  obtain ⟨⟨hΩ, hsz, h3, hP⟩, -⟩ := hs_wit_cert
  have hw : ∀ l ∈ hsW1, l < 2 := by decide
  have hZ := hs_member_eq hw hΩ (j := 1) (by norm_num) hsz (by decide)
  refine hsCtx.goodLocal_of_lit hs_J1 hs_odd1 (base_lt hs_facts) (base_property hs_facts) hw ?_ hZ
    Nat.prime_five le_rfl hsz (b := b31) (q₁ := q31a) (q₂ := q31b) (b' := b51) (q' := q51) ?_ ?_
  · rw [hs_sTabs]
    exact hΩ
  · rw [hs_sTabs]
    exact h3
  · rw [hs_sTabs]
    exact hP

theorem hs_goodLocal_Y2 : GoodLocal (hsCtx.Y 2) := by
  obtain ⟨-, ⟨hΩ, hsz, h3, hP⟩⟩ := hs_wit_cert
  have hw : ∀ l ∈ hsW2, l < 2 := by decide
  have hZ := hs_member_eq hw hΩ (j := 2) (by norm_num) hsz (by decide)
  refine hsCtx.goodLocal_of_lit hs_J2 hs_odd2 (base_lt hs_facts) (base_property hs_facts) hw ?_ hZ
    (p := 7) (by norm_num) (by norm_num) hsz (b := b32) (q₁ := q32a) (q₂ := q32b) (b' := b72)
    (q' := q72) ?_ ?_
  · rw [hs_sTabs]
    exact hΩ
  · rw [hs_sTabs]
    exact h3
  · rw [hs_sTabs]
    exact hP

end CFSG.QuasithinUnique.Vol2Native.L239.HSPairs
