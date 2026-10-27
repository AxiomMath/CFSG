module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatRows
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatOfFacts
import all CFSG.LocalAnalysis.QuasithinUnique.K1.SporadicHS
public import CFSG.Blueprint.NativeSporadic
import all CFSG.Blueprint.NativeSporadic
public import Certificates.Data.CFSGNative.SporLat.Build
public meta import CFSG.LocalAnalysis.QuasithinUnique.K1.SporadicHS
public meta import Certificates.Data.CFSGNative.SporLat.Build
public meta import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatPt
public meta import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatQuot
public meta import Certificates.Data.CFSGNative.HS.Data
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatHSInputs
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatHSDcInputs
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtA312HsInputs
public import CFSG.Quasithin.Background.A312SporHSInputs
public import CFSG.Quasithin.Background.A312SporE8
public import CFSG.Quasithin.Background.A3Structure312Defs
public import Certificates.Certificate3167
public import Certificates.Certificate4140

public section

namespace CFSG.QuasithinUnique.Ch1.SporLat.HS

open CFSG.QuasithinUnique.K1.SporadicPerm CFSG.Sporadic.SmallF2
open CFSG.Sporadic.HS.Native (hsData)
open CFSG.Open (pCoreOf)

theorem hs_delta_valid : PtValid hsData.n hsDelta := by decide

theorem hs_facts : Facts hsData 3 := CFSG.Sporadic.HS.hsFacts

theorem hs_ta : (tab hsData.n (a hsData)).toArray = hsTa := by
  have : tab hsData.n (a hsData) = hsTa.toList := by
    rw [tab_eq_of_rep (n := hsData.n) _ (a hsData) (rep_a hs_facts.toBaseFacts)]
    simp [hsTa]
  rw [this, Array.toArray_toList]

theorem hs_tb : (tab hsData.n (b hsData)).toArray = hsTb := by
  have : tab hsData.n (b hsData) = hsTb.toList := by
    rw [tab_eq_of_rep (n := hsData.n) _ (b hsData) (rep_b hs_facts.toBaseFacts)]
    simp [hsTb]
  rw [this, Array.toArray_toList]

theorem hs_card : Nat.card (J hsData) = 2 ^ 9 * 86625 := by
  have hcard0 : Nat.card (J hsData) = 44352000 :=
    (Nat.card_congr (seedEquiv hs_facts.toBaseFacts).toEquiv).symm.trans CFSG.Sporadic.HS.card_HS
  rw [hcard0]; norm_num

theorem hs_cert' :
    BaseCertS hsData.n hsB
    (slpTabsA (tab hsData.n (a hsData)).toArray (tab hsData.n (b hsData)).toArray hsProg) hsQp
    164 202 206 204 208 hsEnum.1 hsEnum.2.1 hsEnum.2.2 9 := by
  rw [hs_ta, hs_tb]
  have : slpTabsA hsTa hsTb hsProg = hsSLP := by simp [hsSLP]
  rw [this]
  exact hs_cert

@[expose] noncomputable def hsSg : List (J hsData) :=
  hsQp.map fun p => (slpElts (a hsData) (b hsData) hsProg).getD p.1 1

theorem hs_sGens :
    genTabs hsData.n hsSg = hsSTabs ∧ Nat.card (Subgroup.closure {x | x ∈ hsSg}) = 2 ^ 9 := by
  have := sGens_of_baseCertS (n := hsData.n) hsB (base_lt hs_facts) (base_property hs_facts)
    (a hsData) (b hsData) hsProg hs_valid hsQp 164 202 206 204 208 hsEnum.1 hsEnum.2.1 hsEnum.2.2
    9 hs_cert'
  refine ⟨?_, this.2⟩
  rw [hsSg, this.1, hs_ta, hs_tb]
  have : slpTabsA hsTa hsTb hsProg = hsSLP := by simp [hsSLP]
  rw [this]
  rfl

@[expose] def HSLatSpec : Prop :=
  MembersOK ptAct hsData.n hsTa hsTb hsDelta hsLatK ∧
    (∀ g : J hsData, lab hsData.n ptLab hsDelta g = hsDelta ↔
      g ∈ Subgroup.closure {x | x ∈ hsSg}) ∧
    (∀ Z : Subgroup (J hsData), Subgroup.closure {x | x ∈ hsSg} ≤ Z → ∃ j ≤ hsLatK.mw.size,
      Z = memberOrTop hsLatK.mw.size (fun j => Subgroup.closure {x | x ∈ hsSg ++
        (hsLatK.mw[j]!).map (wordElt (a hsData) (b hsData))}) j) ∧
    O2OK ptAct hsLatK hsOtK ∧
    hsLatK.Om.map (fun o => o.lbl.size) = #[1, 15, 21, 3, 3] ∧
    hsOtK.map (fun o => o.lbl.size) = #[1, 8, 8, 2, 2]

class HSLat : Prop where
  spec : HSLatSpec

@[expose] noncomputable def hsCtx
    [HSLat] : LatCtx (J hsData) hsData.n (List ℕ) :=
  LatCtx.ofFacts ptLab (PtValid hsData.n) ptLab_lawful hsDelta hs_delta_valid (a hsData)
    (b hsData) hsTa hsTb hs_ta hs_tb (closure_ab hsData) hsLatK hsSg 9 hs_sGens.1
    hs_sGens.2 86625 (by rw [hs_card, mul_comm]) HSLat.spec.1 HSLat.spec.2.1 HSLat.spec.2.2.1

end CFSG.QuasithinUnique.Ch1.SporLat.HS

namespace CFSG.Quasithin.A312S

open CFSG.QuasithinUnique.K1.SporadicPerm CFSG.QuasithinUnique.Ch1.SporLat
open CFSG.QuasithinUnique.Ch1.SporLat.HS
open CFSG.Sporadic.SmallF2 CFSG.Quasithin.A312S.HS
open CFSG.Sporadic.HS.Native (hsData)
open Matrix

section Elts

variable [HSLat]

@[expose] noncomputable def hsE1 : List (J hsData) := hsCtx.sg ++ hsCtx.gens 1

@[expose] noncomputable def hsZ4Elt : J hsData := evalElt hsE1.toArray hsZ4Word

@[expose] noncomputable def hsEElts : List (J hsData) := hsEWords.map (evalElt hsE1.toArray)

@[expose] noncomputable def hsE2 : List (J hsData) := hsCtx.sg ++ hsCtx.gens 2

@[expose] noncomputable def hsLetter (l : ℕ) : J hsData := hsE2.toArray.getD l 1

@[expose] noncomputable def hsV (i : Fin 3) : J hsData :=
  evalElt hsE2.toArray (hsVWords.getD i [])

@[expose] noncomputable def hsWElts : List (J hsData) := hsWWords.map (evalElt hsE2.toArray)

end Elts

@[expose] def hsMat : ℕ → Matrix (Fin 3) (Fin 3) (ZMod 2)
  | 0 => !![1, 0, 0; 1, 1, 0; 1, 0, 1]
  | 1 => !![1, 1, 1; 0, 0, 1; 0, 1, 0]
  | 2 => !![1, 0, 0; 1, 0, 1; 1, 1, 0]
  | 3 => !![1, 0, 1; 1, 0, 0; 0, 1, 0]
  | _ => 1

section Facts


@[expose] def HSQuot1Fact : Prop :=
  ∀ [HSLat], ∀ (N : Subgroup ↥(hsCtx.Y 1)) [N.Normal], IsPGroup 2 (↥(hsCtx.Y 1) ⧸ N) →
    Nat.card (↥(hsCtx.Y 1) ⧸ N) ≤ 2

@[expose] def HSInclFact : Prop :=
  ∀ [HSLat], ∀ j < 5, ∀ jj < 5,
    (hsCtx.Y j ≤ hsCtx.Y jj ↔ jj ∈ CFSG.Quasithin.A312Hs.hsIncl[j]!)

@[expose] def HSStructFact : Prop :=
  ∀ [HSLat], CFSG.Quasithin.IsZ4StarExtra2 ↥(CFSG.pCore 2 ↥(hsCtx.Y 1)) ∧
    CFSG.Quasithin.IsZ4Cubed ↥(CFSG.pCore 2 ↥(hsCtx.Y 2)) ∧
    ∀ (N : Subgroup ↥(hsCtx.Y 2)) [N.Normal], IsPGroup 2 (↥(hsCtx.Y 2) ⧸ N) →
      Nat.card (↥(hsCtx.Y 2) ⧸ N) ≤ 1

@[expose] def HSA1Fact : Prop :=
  ∀ [HSLat], CFSG.Quasithin.IsZ4StarExtra2 ↥(Subgroup.closure {x | x ∈ hsZ4Elt :: hsEElts}) ∧
    Nat.card (Subgroup.closure {x | x ∈ hsZ4Elt :: hsEElts}) = 64 ∧
    CFSG.Open.pCoreOf 2 (hsCtx.Y 1) = Subgroup.closure {x | x ∈ hsZ4Elt :: hsEElts}

@[expose] def HSA2Fact : Prop :=
  ∀ [HSLat], hsE2.length = 4 ∧ E8Basis hsV ∧
    (∀ l < 4, ∀ i : Fin 3, hsLetter l * hsV i * (hsLetter l)⁻¹ = e8Elt hsV fun r => hsMat l r i) ∧
    CFSG.Quasithin.IsZ4Cubed ↥(Subgroup.closure {x | x ∈ hsWElts}) ∧
    Nat.card (Subgroup.closure {x | x ∈ hsWElts}) = 64 ∧
    CFSG.Open.pCoreOf 2 (hsCtx.Y 2) = Subgroup.closure {x | x ∈ hsWElts}

end Facts

end CFSG.Quasithin.A312S
