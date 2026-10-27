
module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatHSBase
import all CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatHSBase

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatRows
import all CFSG.LocalAnalysis.QuasithinUnique.K1.SporadicHS
public import CFSG.Blueprint.NativeSporadic
import all CFSG.Blueprint.NativeSporadic
public import Certificates.Data.CFSGNative.SporLat.Build
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatHSInputs
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatHSFacts
public import Certificates.Certificate4102
public import CFSG.LocalAnalysis.QuasithinUnique.K1.SporadicBaseVec
public import CFSG.Sporadic.HS
public import CFSG.LocalAnalysis.QuasithinUnique.K1.SporadicHSInputs
public import Certificates.Data.CFSGNative.HS.Data

public section

namespace CFSG.QuasithinUnique.Ch1.SporLat.HS

open CFSG.QuasithinUnique.K1.SporadicPerm CFSG.Sporadic.SmallF2
open CFSG.Sporadic.HS.Native (hsData)
open CFSG.Open (pCoreOf)

instance hsLat_of_cert :
    HSLat :=
  ⟨Certificates.certificate4102.1⟩

theorem hs_quot1
    (N : Subgroup ↥(hsCtx.Y 1)) [N.Normal]
    (hp : IsPGroup 2 (↥(hsCtx.Y 1) ⧸ N)) : Nat.card (↥(hsCtx.Y 1) ⧸ N) ≤ 2 :=
  Certificates.certificate4102.2.1 N hp

theorem hs_incl
    {j jj : ℕ} (hj : j < 5) (hjj : jj < 5) :
    hsCtx.Y j ≤ hsCtx.Y jj ↔ jj ∈ CFSG.Quasithin.A312Hs.hsIncl[j]! :=
  Certificates.certificate4102.2.2.1 j hj jj hjj

theorem hs_row
    (j : ℕ) (hj : j < 5) : ∃ m ∈ hsMems, MemStmt (hsCtx.Y j) m := by
  have hjJ : j < hsCtx.J := by rw [hs_J]; exact hj
  have hO2 : O2OK hsCtx.A.act hsCtx.D hsOtK := hs_o2OK
  have hom := hs_Om_size j hj
  have hot := hs_Ot_size j hj
  interval_cases j
  · refine ⟨⟨512, 512, 512⟩, by simp [hsMems], hsCtx.memStmt_of_O2 hO2 hjJ _ ?_ ?_ ?_⟩
    · change hsLatK.Om[0]!.lbl.size * 2 ^ 9 = 512
      rw [hom]; rfl
    · change hsOtK[0]!.lbl.size * 512 = 2 ^ 9
      rw [hot]; rfl
    · intro N _ _
      exact (quot_le_order _ N).trans (by rw [hs_member_card 0 (by norm_num)]; rfl)
  · refine ⟨⟨7680, 64, 2⟩, by simp [hsMems], hsCtx.memStmt_of_O2 hO2 hjJ _ ?_ ?_ ?_⟩
    · change hsLatK.Om[1]!.lbl.size * 2 ^ 9 = 7680
      rw [hom]; rfl
    · change hsOtK[1]!.lbl.size * 64 = 2 ^ 9
      rw [hot]; rfl
    · intro N _ hp
      exact hs_quot1 N hp
  · refine ⟨⟨10752, 64, 10752⟩, by simp [hsMems], hsCtx.memStmt_of_O2 hO2 hjJ _ ?_ ?_ ?_⟩
    · change hsLatK.Om[2]!.lbl.size * 2 ^ 9 = 10752
      rw [hom]; rfl
    · change hsOtK[2]!.lbl.size * 64 = 2 ^ 9
      rw [hot]; rfl
    · intro N _ _
      exact (quot_le_order _ N).trans (by rw [hs_member_card 2 (by norm_num)]; rfl)
  · refine ⟨⟨1536, 256, 1536⟩, by simp [hsMems], hsCtx.memStmt_of_O2 hO2 hjJ _ ?_ ?_ ?_⟩
    · change hsLatK.Om[3]!.lbl.size * 2 ^ 9 = 1536
      rw [hom]; rfl
    · change hsOtK[3]!.lbl.size * 256 = 2 ^ 9
      rw [hot]; rfl
    · intro N _ _
      exact (quot_le_order _ N).trans (by rw [hs_member_card 3 (by norm_num)]; rfl)
  · refine ⟨⟨1536, 256, 1536⟩, by simp [hsMems], hsCtx.memStmt_of_O2 hO2 hjJ _ ?_ ?_ ?_⟩
    · change hsLatK.Om[4]!.lbl.size * 2 ^ 9 = 1536
      rw [hom]; rfl
    · change hsOtK[4]!.lbl.size * 256 = 2 ^ 9
      rw [hot]; rfl
    · intro N _ _
      exact (quot_le_order _ N).trans (by rw [hs_member_card 4 (by norm_num)]; rfl)

open CFSG.Blueprint.NativeSporadic in
theorem hs_overgroups {X : Type} [Group X] [Finite X] (hX : Nonempty (X ≃* Carrier .HS))
    {T Y : Subgroup X} (hT : IsSylowTwoOf T ⊤) (hTY : T ≤ Y) :
    Y = ⊤ ∨ ∃ m ∈ hsMems, Nat.card Y = m.order ∧ Nat.card (pCoreOf 2 Y) = m.o2 ∧
      ∀ (N : Subgroup Y) [N.Normal], IsPGroup 2 (Y ⧸ N) → Nat.card (Y ⧸ N) ≤ m.quot2 := by
  obtain ⟨e⟩ := hX
  have hX' : Nonempty (X ≃* J hsData) :=
    ⟨e.trans (seedEquiv hs_facts.toBaseFacts)⟩
  have hall : ∀ Z : Subgroup (J hsData), hsCtx.S ≤ Z → ∃ j ≤ 5, Z = memberOrTop 5 hsCtx.Y j :=
    hs_complete
  exact overgroups_of_lattice hsCtx.S hs_S_sylow 5 hsCtx.Y hsMems hall (fun j hj => hs_row j hj)
    hX' hT hTY

end CFSG.QuasithinUnique.Ch1.SporLat.HS
