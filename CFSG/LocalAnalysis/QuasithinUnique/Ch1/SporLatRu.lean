module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatRows
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatIncl
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatRuCertificate
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatOfFacts
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatRuKInputs
public import CFSG.LocalAnalysis.QuasithinUnique.K1.SporadicRu
import all CFSG.LocalAnalysis.QuasithinUnique.K1.SporadicRu
public import CFSG.Blueprint.NativeSporadic
import all CFSG.Blueprint.NativeSporadic
public import Certificates.Data.CFSGNative.SporLat.Build
public meta import CFSG.LocalAnalysis.QuasithinUnique.K1.SporadicRu
public meta import Certificates.Data.CFSGNative.SporLat.Build
public meta import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatPt
public meta import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatQuot
public meta import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatRuCertificate
public meta import Certificates.Data.CFSGNative.Ru.Data
public import Certificates.Certificate4034
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatRuInputs
public import Certificates.Certificate4080
public import Certificates.Certificate4143
public import Certificates.Certificate3172

public section

namespace CFSG.QuasithinUnique.Ch1.SporLat.Ru

open CFSG.QuasithinUnique.K1.SporadicPerm CFSG.Sporadic.SmallF2
open CFSG.Sporadic.Ru.Native (ruData)
open CFSG.Open (pCoreOf)
open CFSG.QuasithinUnique.Ch1.SporLat.RuCert

theorem ru_facts : Facts ruData 3 := CFSG.Sporadic.Ru.ruFacts

theorem ru_ta : (tab ruData.n (a ruData)).toArray = ruTa := by
  have : tab ruData.n (a ruData) = ruTa.toList := by
    rw [tab_eq_of_rep (n := ruData.n) _ (a ruData) (rep_a ru_facts.toBaseFacts)]
    simp [ruTa]
  rw [this, Array.toArray_toList]

theorem ru_tb : (tab ruData.n (b ruData)).toArray = ruTb := by
  have : tab ruData.n (b ruData) = ruTb.toList := by
    rw [tab_eq_of_rep (n := ruData.n) _ (b ruData) (rep_b ru_facts.toBaseFacts)]
    simp [ruTb]
  rw [this, Array.toArray_toList]

theorem ru_taL : (tab ruData.n (a ruData)).toArray = ruTaL := ru_ta

theorem ru_tbL : (tab ruData.n (b ruData)).toArray = ruTbL := ru_tb

theorem ru_card : Nat.card (J ruData) = 2 ^ 14 * 8906625 := by
  have hcard0 : Nat.card (J ruData) = 145926144000 :=
    (Nat.card_congr (seedEquiv ru_facts.toBaseFacts).toEquiv).symm.trans CFSG.Sporadic.Ru.card_Ru
  rw [hcard0]; norm_num

theorem ru_cert' : BaseCertS ruData.n ruB
    (slpTabsA (tab ruData.n (a ruData)).toArray (tab ruData.n (b ruData)).toArray ruProg) ruQp
    154 187 191 189 193 ruEnum.1 ruEnum.2.1 ruEnum.2.2 14 := by
  rw [ru_ta, ru_tb]
  have : slpTabsA ruTa ruTb ruProg = ruSLP := by simp [ruSLP]
  rw [this]
  exact ru_cert

@[expose] noncomputable def ruSg : List (J ruData) :=
  ruQp.map fun p => (slpElts (a ruData) (b ruData) ruProg).getD p.1 1

theorem ru_sGens :
    genTabs ruData.n ruSg = ruSTabsL ∧ Nat.card (Subgroup.closure {x | x ∈ ruSg}) = 2 ^ 14 := by
  have := sGens_of_baseCertS (n := ruData.n) ruB (base_lt ru_facts) (base_property ru_facts)
    (a ruData) (b ruData) ruProg ru_valid ruQp 154 187 191 189 193 ruEnum.1 ruEnum.2.1 ruEnum.2.2
    14 ru_cert'
  refine ⟨?_, this.2⟩
  rw [ruSg, this.1, ru_ta, ru_tb]
  have : slpTabsA ruTa ruTb ruProg = ruSLP := by simp [ruSLP]
  rw [this]
  rfl

theorem ru_delta_valid : PtValid ruData.n ruDelta := by decide

theorem ruSg_eq : ruSg = ruSgK := rfl

theorem ru_mw_size : ruMw.size = 5 := rfl

@[expose] noncomputable def ruCtx : LatCtx (J ruData) ruData.n (List ℕ) :=
  LatCtx.ofFacts ptLab (PtValid ruData.n) ptLab_lawful ruDelta ru_delta_valid (a ruData)
    (b ruData) ruTaL ruTbL ru_taL ru_tbL (closure_ab ruData) ruLatK ruSg 14 ru_sGens.1 ru_sGens.2
    8906625 (by rw [ru_card, mul_comm]) ru_lat_cert.1 (by rw [ruSg_eq]; exact ru_lat_cert.2.2.2.1)
    (fun Z hZ => by
      rw [ruSg_eq] at hZ ⊢
      obtain ⟨j, hj, e⟩ := ru_lat_cert.2.2.2.2 Z hZ
      exact ⟨j, by rw [show ruLatK.mw = ruMw from rfl, ru_mw_size]; exact hj, e⟩)

section Ctx


theorem ru_D_Om : ruCtx.D.Om = ruLatK.Om := rfl

theorem ru_D_mw : ruCtx.D.mw = ruMw := rfl

theorem ru_D_sTabs : ruCtx.D.sTabs = ruSTabsL := rfl

theorem ru_Om_map : ruCtx.D.Om.map (fun o => o.lbl.size) = #[1, 15, 21, 3, 3] := by
  rw [ru_D_Om]
  simp only [ruLatK, List.map_toArray, List.map_cons, List.map_nil]
  rfl

theorem ru_mt_get {j : ℕ} (hj : j < 5) :
    ruCtx.D.mt[j]! = (ruMw[j]!).map (wordTabA #[ruTaL, ruTbL] ruData.n) := by
  change (ruMw.map _)[j]! = (ruMw[j]!).map _
  rw [getElem!_pos _ j (by rw [Array.size_map, ru_mw_size]; exact hj),
    getElem!_pos ruMw j (by rw [ru_mw_size]; exact hj)]
  simp

end Ctx

theorem ru_ctx_sg :
    ruCtx.sg = ruQp.map fun p => (slpElts (a ruData) (b ruData) ruProg).getD p.1 1 :=
  rfl

theorem ru_orbit_card : ruCtx.D.O.lbl.size = 8906625 :=
  LatCtx.ofFacts_O_size ..

theorem ru_J : ruCtx.J = 5 := by
  unfold LatCtx.J
  rw [ru_D_mw, ru_mw_size]

theorem ru_complete : ∀ Z : Subgroup (J ruData), ruCtx.S ≤ Z →
    ∃ j ≤ 5, Z = memberOrTop 5 ruCtx.Y j := by
  intro Z hZ
  obtain ⟨j, hj, rfl⟩ := ruCtx.complete Z hZ
  rw [ru_J] at hj ⊢
  exact ⟨j, hj, rfl⟩

theorem ru_card_S : Nat.card ruCtx.S = 16384 := by
  rw [ruCtx.S_card]; rfl

theorem ru_Om_size (j : ℕ) (hj : j < 5) : ruCtx.D.Om[j]!.lbl.size = #[1, 15, 21, 3, 3][j]! := by
  rw [ru_D_Om]
  interval_cases j <;> rfl

theorem ru_member_card (j : ℕ) (hj : j < 5) :
    Nat.card (ruCtx.Y j) = #[1, 15, 21, 3, 3][j]! * 16384 := by
  have h1 : j < ruCtx.J := by rw [ru_J]; exact hj
  rw [ruCtx.Y_card h1, ru_Om_size j hj]
  rfl

theorem ru_Y_le_iff {j jj : ℕ} (hj : j < 5) (hjj : jj < 5) :
    ruCtx.Y j ≤ ruCtx.Y jj ↔ jj ∈ ruIncl[j]! := by
  rw [ruCtx.Y_le_iff (by rw [ru_J]; exact hj) (by rw [ru_J]; exact hjj)]
  exact ru_lat_cert.2.2.1 j hj jj hjj

theorem ru_quot_cert :
    QuotOK ruData.n ruB ruQuotL1 ruQuot1 ruQuotEnum.1 ruQuotEnum.2.1 ruQuotEnum.2.2 122880 :=
  Certificates.certificate4080

theorem ru_quotL1 : ruCtx.D.sTabs ++ ruCtx.D.mt[1]! = ruQuotL1 :=
  congrArg (ruLatK.sTabs ++ ·) (ru_mt_get (by decide))

theorem ru_letters2 :
    ruCtx.D.sTabs ++ ruCtx.D.mt[2]! =
      ruSTabsL ++ (ruMw[2]!).map (wordTabA #[ruTaL, ruTbL] ruData.n) :=
  congrArg (ruLatK.sTabs ++ ·) (ru_mt_get (by decide))

def ruMems : List Mem :=
  [⟨16384, 16384, 16384⟩, ⟨245760, 2048, 2⟩, ⟨344064, 2048, 344064⟩, ⟨49152, 8192, 49152⟩,
    ⟨49152, 8192, 49152⟩]

theorem ru_Ot_size (j : ℕ) (hj : j < 5) : ruOtK[j]!.lbl.size = #[1, 8, 8, 2, 2][j]! := by
  interval_cases j <;> rfl

theorem ru_row (j : ℕ) (hj : j < 5) : ∃ m ∈ ruMems, MemStmt (ruCtx.Y j) m := by
  have hjJ : j < ruCtx.J := by rw [ru_J]; exact hj
  have hO2 : O2OK ruCtx.A.act ruCtx.D ruOtK := ru_lat_cert.2.1
  have hom := ru_Om_size j hj
  have hot := ru_Ot_size j hj
  interval_cases j
  · refine ⟨⟨16384, 16384, 16384⟩, by simp [ruMems], ruCtx.memStmt_of_O2 hO2 hjJ _ ?_ ?_ ?_⟩
    · show ruCtx.D.Om[0]!.lbl.size * 2 ^ 14 = 16384
      rw [hom]; rfl
    · show ruOtK[0]!.lbl.size * 16384 = 2 ^ 14
      rw [hot]; rfl
    · intro N _ _
      exact (quot_le_order _ N).trans (by rw [ru_member_card 0 (by norm_num)]; rfl)
  · refine ⟨⟨245760, 2048, 2⟩, by simp [ruMems], ruCtx.memStmt_of_O2 hO2 hjJ _ ?_ ?_ ?_⟩
    · show ruCtx.D.Om[1]!.lbl.size * 2 ^ 14 = 245760
      rw [hom]; rfl
    · show ruOtK[1]!.lbl.size * 2048 = 2 ^ 14
      rw [hot]; rfl
    · intro N _ hp
      have h1 := ruCtx.quot_bound hjJ ruB (base_lt ru_facts) (base_property ru_facts) ruQuot1
        ruQuotEnum.1 ruQuotEnum.2.1 ruQuotEnum.2.2 122880 (by rw [ru_quotL1]; exact ru_quot_cert)
        N hp
      have h2 : Nat.card (ruCtx.Y 1) = 245760 := by
        rw [ru_member_card 1 (by norm_num)]; rfl
      show Nat.card ((ruCtx.Y 1) ⧸ N) ≤ 2
      omega
  · refine ⟨⟨344064, 2048, 344064⟩, by simp [ruMems], ruCtx.memStmt_of_O2 hO2 hjJ _ ?_ ?_ ?_⟩
    · show ruCtx.D.Om[2]!.lbl.size * 2 ^ 14 = 344064
      rw [hom]; rfl
    · show ruOtK[2]!.lbl.size * 2048 = 2 ^ 14
      rw [hot]; rfl
    · intro N _ _
      exact (quot_le_order _ N).trans (by rw [ru_member_card 2 (by norm_num)]; rfl)
  · refine ⟨⟨49152, 8192, 49152⟩, by simp [ruMems], ruCtx.memStmt_of_O2 hO2 hjJ _ ?_ ?_ ?_⟩
    · show ruCtx.D.Om[3]!.lbl.size * 2 ^ 14 = 49152
      rw [hom]; rfl
    · show ruOtK[3]!.lbl.size * 8192 = 2 ^ 14
      rw [hot]; rfl
    · intro N _ _
      exact (quot_le_order _ N).trans (by rw [ru_member_card 3 (by norm_num)]; rfl)
  · refine ⟨⟨49152, 8192, 49152⟩, by simp [ruMems], ruCtx.memStmt_of_O2 hO2 hjJ _ ?_ ?_ ?_⟩
    · show ruCtx.D.Om[4]!.lbl.size * 2 ^ 14 = 49152
      rw [hom]; rfl
    · show ruOtK[4]!.lbl.size * 8192 = 2 ^ 14
      rw [hot]; rfl
    · intro N _ _
      exact (quot_le_order _ N).trans (by rw [ru_member_card 4 (by norm_num)]; rfl)

theorem ru_S_sylow : IsSylowTwoOf ruCtx.S ⊤ := by
  refine K1.isSylowTwoOf_top_iff.mpr ⟨ruCtx.S_isPGroup, ?_⟩
  have h1 := Subgroup.card_mul_index ruCtx.S
  rw [ru_card_S, ru_card] at h1
  have h2 : ruCtx.S.index = 8906625 := by omega
  rw [h2]
  norm_num

open CFSG.Blueprint.NativeSporadic in
theorem ru_overgroups {X : Type} [Group X] [Finite X] (hX : Nonempty (X ≃* Carrier .Ru))
    {T Y : Subgroup X} (hT : IsSylowTwoOf T ⊤) (hTY : T ≤ Y) :
    Y = ⊤ ∨ ∃ m ∈ ruMems, Nat.card Y = m.order ∧ Nat.card (pCoreOf 2 Y) = m.o2 ∧
      ∀ (N : Subgroup Y) [N.Normal], IsPGroup 2 (Y ⧸ N) → Nat.card (Y ⧸ N) ≤ m.quot2 := by
  obtain ⟨e⟩ := hX
  have hX' : Nonempty (X ≃* J ruData) :=
    ⟨e.trans (seedEquiv ru_facts.toBaseFacts)⟩
  have hall : ∀ Z : Subgroup (J ruData), ruCtx.S ≤ Z → ∃ j ≤ 5, Z = memberOrTop 5 ruCtx.Y j :=
    ru_complete
  exact overgroups_of_lattice ruCtx.S ru_S_sylow 5 ruCtx.Y ruMems hall (fun j hj => ru_row j hj)
    hX' hT hTY

end CFSG.QuasithinUnique.Ch1.SporLat.Ru
