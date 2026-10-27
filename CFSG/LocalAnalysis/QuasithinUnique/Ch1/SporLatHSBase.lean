
module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatRows
import all CFSG.LocalAnalysis.QuasithinUnique.K1.SporadicHS
public import CFSG.Blueprint.NativeSporadic
import all CFSG.Blueprint.NativeSporadic
public import Certificates.Data.CFSGNative.SporLat.Build
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatHSInputs
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatHSFacts
public import CFSG.LocalAnalysis.QuasithinUnique.K1.SporadicBaseVec
public import CFSG.Sporadic.HS
public import CFSG.LocalAnalysis.QuasithinUnique.K1.SporadicHSInputs
public import Certificates.Data.CFSGNative.HS.Data

public section

namespace CFSG.QuasithinUnique.Ch1.SporLat.HS

open CFSG.QuasithinUnique.K1.SporadicPerm CFSG.Sporadic.SmallF2
open CFSG.Sporadic.HS.Native (hsData)
open CFSG.Open (pCoreOf)

section Lattice

variable [HSLat]

theorem hs_D_mw : hsCtx.D.mw = hsLatK.mw := rfl

theorem hs_O_size : hsCtx.D.O.lbl.size = 86625 := LatCtx.ofFacts_O_size ..

theorem hs_Om_map : hsCtx.D.Om.map (fun o => o.lbl.size) = #[1, 15, 21, 3, 3] :=
  HSLat.spec.2.2.2.2.1

theorem hsLatK_mw_size : hsLatK.mw.size = 5 := by
  rw [← HSLat.spec.1.2.2.2.1]
  rfl

theorem hs_J : hsCtx.J = 5 := by
  unfold LatCtx.J
  rw [hs_D_mw, hsLatK_mw_size]

end Lattice

theorem hs_complete [HSLat] :
    ∀ Z : Subgroup (J hsData), hsCtx.S ≤ Z → ∃ j ≤ 5, Z = memberOrTop 5 hsCtx.Y j := by
  intro Z hZ
  obtain ⟨j, hj, rfl⟩ := hsCtx.complete Z hZ
  rw [hs_J] at hj ⊢
  exact ⟨j, hj, by simp⟩

theorem hs_card_S [HSLat] :
    Nat.card hsCtx.S = 512 := by
  rw [hsCtx.S_card]; rfl

theorem hs_Om_size [HSLat]
    (j : ℕ) (hj : j < 5) : hsLatK.Om[j]!.lbl.size = #[1, 15, 21, 3, 3][j]! := by
  have e := HSLat.spec.2.2.2.2.1
  have hjO : j < hsLatK.Om.size := by
    have := congrArg Array.size e
    simp only [Array.size_map] at this
    rw [this]
    simpa using hj
  rw [← e, getElem!_pos _ j hjO, getElem!_pos _ j (by simpa using hjO), Array.getElem_map]

theorem hs_member_card [HSLat]
    (j : ℕ) (hj : j < 5) :
    Nat.card (hsCtx.Y j) = #[1, 15, 21, 3, 3][j]! * 512 := by
  have h1 : j < hsCtx.J := by rw [hs_J]; exact hj
  rw [hsCtx.Y_card h1]
  change hsLatK.Om[j]!.lbl.size * 2 ^ 9 = _
  rw [hs_Om_size j hj]
  norm_num

theorem hs_o2OK [HSLat] :
    O2OK ptAct hsCtx.D hsOtK :=
  HSLat.spec.2.2.2.1

theorem hs_Ot_map [HSLat] : hsOtK.map (fun o => o.lbl.size) = #[1, 8, 8, 2, 2] :=
  HSLat.spec.2.2.2.2.2

def hsMems : List Mem :=
  [⟨512, 512, 512⟩, ⟨7680, 64, 2⟩, ⟨10752, 64, 10752⟩, ⟨1536, 256, 1536⟩, ⟨1536, 256, 1536⟩]

theorem hs_Ot_size [HSLat] (j : ℕ) (hj : j < 5) :
    hsOtK[j]!.lbl.size = #[1, 8, 8, 2, 2][j]! := by
  have h2 : hsOtK.map (fun o => o.lbl.size) = #[1, 8, 8, 2, 2] := hs_Ot_map
  have hjO : j < hsOtK.size := by
    have : hsOtK.size = 5 := rfl
    omega
  rw [← h2, getElem!_pos _ j hjO, getElem!_pos _ j (by simpa using hjO)]
  simp

theorem hs_S_sylow [HSLat] :
    IsSylowTwoOf hsCtx.S ⊤ := by
  refine K1.isSylowTwoOf_top_iff.mpr ⟨hsCtx.S_isPGroup, ?_⟩
  have h1 := Subgroup.card_mul_index hsCtx.S
  rw [hs_card_S, hs_card] at h1
  have h2 : hsCtx.S.index = 86625 := by omega
  rw [h2]
  norm_num

end CFSG.QuasithinUnique.Ch1.SporLat.HS
