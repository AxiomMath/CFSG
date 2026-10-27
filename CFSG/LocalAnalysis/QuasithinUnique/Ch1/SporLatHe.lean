
module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatRows
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatIncl
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatOfFacts
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatHeCertificateBase
public import CFSG.LocalAnalysis.QuasithinUnique.K1.SporadicHe
import all CFSG.LocalAnalysis.QuasithinUnique.K1.SporadicHe
public import CFSG.Blueprint.NativeSporadic
import all CFSG.Blueprint.NativeSporadic
public import Certificates.Data.CFSGNative.He.Certificate
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatHeKInputs
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatCore
public import CFSG.Quasithin.EmptyFaithful.S151S9TThreeDFact
public import Certificates.Certificate4141
public import CFSG.LocalAnalysis.QuasithinUnique.K1.SporadicBase
public import CFSG.LocalAnalysis.QuasithinUnique.K1.SporadicRep
public import CFSG.Sporadic.He
public import CFSG.LocalAnalysis.QuasithinUnique.K1.SporadicHeInputs

public section

namespace CFSG.QuasithinUnique.Ch1.SporLat.He

open CFSG.QuasithinUnique.K1.SporadicPerm
open CFSG.Open (pCoreOf)

theorem he_delta_valid : PtValid 8330 heDelta := by decide

theorem he_ta
    : (tab 8330 (CFSG.Sporadic.He.a : CFSG.Sporadic.He.J)).toArray = heTa := by
  have : tab 8330 (CFSG.Sporadic.He.a : CFSG.Sporadic.He.J) = heTa.toList := by
    rw [tab_eq_of_rep (n := 8330) _ (CFSG.Sporadic.He.a : CFSG.Sporadic.He.J)
      CFSG.Sporadic.He.rep_alpha]
    simp [heTa, CFSG.Sporadic.He.orb]
  rw [this, Array.toArray_toList]

theorem he_tb
    : (tab 8330 (CFSG.Sporadic.He.b : CFSG.Sporadic.He.J)).toArray = heTb := by
  have : tab 8330 (CFSG.Sporadic.He.b : CFSG.Sporadic.He.J) = heTb.toList := by
    rw [tab_eq_of_rep (n := 8330) _ (CFSG.Sporadic.He.b : CFSG.Sporadic.He.J)
      CFSG.Sporadic.He.rep_beta]
    simp [heTb, CFSG.Sporadic.He.orb]
  rw [this, Array.toArray_toList]

theorem he_card
    : Nat.card CFSG.Sporadic.He.J = 2 ^ 10 * 3935925 := by
  rw [CFSG.Sporadic.He.card_J]; norm_num

theorem he_cert' : BaseCertS 8330 heB
    (slpTabsA (tab 8330 (CFSG.Sporadic.He.a : CFSG.Sporadic.He.J)).toArray
      (tab 8330 (CFSG.Sporadic.He.b : CFSG.Sporadic.He.J)).toArray heProg) heQp
    170 249 253 251 255 heEnum.1 heEnum.2.1 heEnum.2.2 10 := by
  rw [he_ta, he_tb]
  have : slpTabsA heTa heTb heProg = heSLP := by simp [heSLP]
  rw [this]
  exact he_cert

@[expose] noncomputable def heSg : List CFSG.Sporadic.He.J :=
  heQp.map fun p => (slpElts CFSG.Sporadic.He.a CFSG.Sporadic.He.b heProg).getD p.1 1

theorem he_sGens :
    genTabs 8330 heSg = heSTabsC ∧ Nat.card (Subgroup.closure {x | x ∈ heSg}) = 2 ^ 10 := by
  have := sGens_of_baseCertS (n := 8330) heB he_base_lt he_base_property CFSG.Sporadic.He.a
    CFSG.Sporadic.He.b heProg he_valid heQp 170 249 253 251 255 heEnum.1 heEnum.2.1
    heEnum.2.2 10 he_cert'
  refine ⟨?_, this.2⟩
  rw [heSg, this.1, he_ta, he_tb]
  rfl

theorem heLatK_mw_size : heLatK.mw.size = 11 := rfl

@[expose] noncomputable def heCtx
    [HeOverFacts]
    : LatCtx CFSG.Sporadic.He.J 8330 (List ℕ) :=
  LatCtx.ofFacts ptLab (PtValid 8330) ptLab_lawful heDelta he_delta_valid CFSG.Sporadic.He.a
    CFSG.Sporadic.He.b heTa heTb he_ta he_tb CFSG.Sporadic.He.closure_ab heLatK heSg 10
    he_sGens.1 he_sGens.2 3935925 (by rw [he_card, mul_comm]) heCertC.1 heCertC.2.2.2.1
    (fun Z hZ => by
      obtain ⟨j, hj, e⟩ := heCertC.2.2.2.2 Z hZ
      exact ⟨j, by rw [heLatK_mw_size]; exact hj, e⟩)

section Cert

variable
  [HeOverFacts]

theorem he_D_Om : heCtx.D.Om = heLatK.Om := rfl

theorem he_D_mt : heCtx.D.mt = heLatK.mt := rfl

theorem he_D_mw : heCtx.D.mw = heLatK.mw := rfl

theorem he_D_sTabs : heCtx.D.sTabs = heLatK.sTabs := rfl

theorem he_orbit_card : heCtx.D.O.lbl.size = 3935925 := LatCtx.ofFacts_O_size ..

theorem he_Om_map :
    heCtx.D.Om.map (fun o => o.lbl.size) = #[1, 3, 9, 135, 135, 9, 3, 21, 3, 9, 3] := by
  rw [he_D_Om]
  simp only [heLatK, List.map_toArray, List.map_cons, List.map_nil]
  rfl

theorem he_o2OK : O2OK ptAct heCtx.D heOtK := by
  have h := heCertC.2.1
  unfold O2OK at h ⊢
  rw [he_D_mw, he_D_Om, he_D_sTabs]
  exact h

theorem he_mw_lit : heCtx.D.mw = heMwLit := rfl

theorem he_labels2 : ∀ x ∈ heCtx.D.Om[2]!.lbl.toList, x ∈ heLabels2 := by
  rw [he_D_Om]
  decide

theorem he_labels7 : ∀ x ∈ heCtx.D.Om[7]!.lbl.toList, x ∈ heLabels7 := by
  rw [he_D_Om]
  decide

end Cert

theorem he_J
    [HeOverFacts] : heCtx.J = 11 := by
  unfold LatCtx.J
  rw [he_D_mw, heLatK_mw_size]

theorem he_complete
    [HeOverFacts]
    : ∀ Z : Subgroup CFSG.Sporadic.He.J, heCtx.S ≤ Z →
    ∃ j ≤ 11, Z = memberOrTop 11 heCtx.Y j := by
  intro Z hZ
  obtain ⟨j, hj, rfl⟩ := heCtx.complete Z hZ
  rw [he_J] at hj ⊢
  exact ⟨j, hj, by simp⟩

theorem he_card_S
    [HeOverFacts]
    : Nat.card heCtx.S = 1024 := by
  rw [heCtx.S_card]; rfl

theorem he_Om_size
    [HeOverFacts]
    (j : ℕ) (hj : j < 11) :
    heCtx.D.Om[j]!.lbl.size = #[1, 3, 9, 135, 135, 9, 3, 21, 3, 9, 3][j]! := by
  rw [he_D_Om]
  interval_cases j <;> rfl

theorem he_Ot_size (j : ℕ) (hj : j < 11) :
    heOtK[j]!.lbl.size = #[1, 2, 4, 16, 16, 4, 2, 8, 2, 4, 2][j]! := by
  interval_cases j <;> rfl

theorem he_member_card
    [HeOverFacts]
    (j : ℕ) (hj : j < 11) :
    Nat.card (heCtx.Y j) = #[1, 3, 9, 135, 135, 9, 3, 21, 3, 9, 3][j]! * 1024 := by
  have h1 : j < heCtx.J := by rw [he_J]; exact hj
  rw [heCtx.Y_card h1, he_Om_size j hj]
  rfl

theorem he_Y_le_iff
    [HeOverFacts]
    {j jj : ℕ} (hj : j < 11) (hjj : jj < 11) :
    heCtx.Y j ≤ heCtx.Y jj ↔ jj ∈ heIncl[j]! :=
  heCertC.2.2.1 j hj jj hjj

def heMems : List Mem :=
  [⟨1024, 1024, 1024⟩, ⟨3072, 512, 3072⟩, ⟨9216, 256, 9216⟩, ⟨138240, 64, 138240⟩,
    ⟨138240, 64, 138240⟩, ⟨9216, 256, 9216⟩, ⟨3072, 512, 3072⟩, ⟨21504, 128, 21504⟩,
    ⟨3072, 512, 3072⟩, ⟨9216, 256, 9216⟩, ⟨3072, 512, 3072⟩]

theorem he_rows_default
    [HeOverFacts]
    : (List.range 11).map (defaultRow 10 heCtx.D heOtK) = heMems := by
  have h : (List.range 11).map (defaultRow 10 heCtx.D heOtK) =
      (List.range 11).map fun j => (⟨#[1, 3, 9, 135, 135, 9, 3, 21, 3, 9, 3][j]! * 2 ^ 10,
        2 ^ 10 / #[1, 2, 4, 16, 16, 4, 2, 8, 2, 4, 2][j]!,
        #[1, 3, 9, 135, 135, 9, 3, 21, 3, 9, 3][j]! * 2 ^ 10⟩ : Mem) := by
    apply List.map_congr_left
    intro j hj
    have hj' := List.mem_range.mp hj
    simp only [defaultRow, he_Om_size j hj', he_Ot_size j hj']
  rw [h]
  rfl

theorem he_row
    [HeOverFacts]
    (j : ℕ) (hj : j < 11) : ∃ m ∈ heMems, MemStmt (heCtx.Y j) m := by
  refine heCtx.rows_of_default (Ot := heOtK) he_o2OK heMems ?_ j (by rw [he_J]; exact hj)
  rw [he_J]
  exact he_rows_default

theorem he_S_sylow
    [HeOverFacts]
    : IsSylowTwoOf heCtx.S ⊤ := by
  refine K1.isSylowTwoOf_top_iff.mpr ⟨heCtx.S_isPGroup, ?_⟩
  have h1 := Subgroup.card_mul_index heCtx.S
  rw [heCtx.S_card, he_card] at h1
  have h2 : heCtx.S.index = 3935925 := by
    have : heCtx.k = 10 := rfl
    rw [this] at h1
    omega
  rw [h2]
  norm_num

open CFSG.Blueprint.NativeSporadic in
theorem he_overgroups
    [HeOverFacts]
    {X : Type} [Group X] [Finite X] (hX : Nonempty (X ≃* Carrier .He))
    {T Y : Subgroup X} (hT : IsSylowTwoOf T ⊤) (hTY : T ≤ Y) :
    Y = ⊤ ∨ ∃ m ∈ heMems, Nat.card Y = m.order ∧ Nat.card (pCoreOf 2 Y) = m.o2 ∧
      ∀ (N : Subgroup Y) [N.Normal], IsPGroup 2 (Y ⧸ N) → Nat.card (Y ⧸ N) ≤ m.quot2 := by
  obtain ⟨e⟩ := hX
  have hX' : Nonempty (X ≃* CFSG.Sporadic.He.J) := ⟨e.trans CFSG.Sporadic.He.heEquivJ⟩
  have hall : ∀ Z : Subgroup CFSG.Sporadic.He.J, heCtx.S ≤ Z →
      ∃ j ≤ 11, Z = memberOrTop 11 heCtx.Y j := he_complete
  exact overgroups_of_lattice heCtx.S he_S_sylow 11 heCtx.Y heMems hall
    (fun j hj => he_row j hj) hX' hT hTY

end CFSG.QuasithinUnique.Ch1.SporLat.He
