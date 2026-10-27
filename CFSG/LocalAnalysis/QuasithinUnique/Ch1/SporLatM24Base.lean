
module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatRows
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatCode
import all CFSG.LocalAnalysis.QuasithinUnique.K1.SporadicMathieu
public import CFSG.Blueprint.NativeSporadic
import all CFSG.Blueprint.NativeSporadic
public import Certificates.Data.CFSGNative.SporLat.Build
public import Certificates.Data.CFSGNative.SporLat.Code
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatM24Inputs
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatM24Facts
public import CFSG.LocalAnalysis.QuasithinUnique.K1.SporadicMathieuInputs
public import Certificates.Data.CFSGNative.Mathieu.M24

@[expose] public section

namespace CFSG.QuasithinUnique.Ch1.SporLat.M24

open CFSG.QuasithinUnique.K1.SporadicPerm
open CFSG.Sporadic.Mathieu (m24a m24b card_M24 m24_hyp)
open CFSG.Open (pCoreOf)

section Lattice

variable [M24Lat]

theorem m24_D_Om : m24Ctx.D.Om = m24LatK.Om := rfl

theorem m24_D_mw : m24Ctx.D.mw = m24LatK.mw := rfl

theorem m24_D_sTabs : m24Ctx.D.sTabs = m24LatK.sTabs := rfl

theorem m24_O_size : m24Ctx.D.O.lbl.size = 239085 := LatCtx.ofFacts_O_size ..

theorem m24_Om_map :
    m24Ctx.D.Om.map (fun o => o.lbl.size) = #[1, 315, 63, 135, 21, 9, 21, 3, 3, 3, 9, 3, 9] :=
  M24Lat.spec.2.2.2.2.1

theorem m24LatK_mw_size : m24LatK.mw.size = 13 := by
  rw [← M24Lat.spec.1.2.2.2.1]
  rfl

theorem m24_J : m24Ctx.J = 13 := by
  unfold LatCtx.J
  rw [m24_D_mw, m24LatK_mw_size]

theorem m24_complete : ∀ Z : Subgroup ↥CFSG.Blueprint.NativeSporadic.M24, m24Ctx.S ≤ Z →
    ∃ j ≤ 13, Z = memberOrTop 13 m24Ctx.Y j := by
  intro Z hZ
  obtain ⟨j, hj, rfl⟩ := m24Ctx.complete Z hZ
  rw [m24_J] at hj ⊢
  exact ⟨j, hj, rfl⟩

theorem m24_o2OK : O2OK (codeSetAct 24) m24Ctx.D m24OtK := M24Lat.spec.2.2.2.1

theorem m24_Om_size (j : ℕ) (hj : j < 13) :
    m24LatK.Om[j]!.lbl.size = #[1, 315, 63, 135, 21, 9, 21, 3, 3, 3, 9, 3, 9][j]! := by
  have e := M24Lat.spec.2.2.2.2.1
  have hjO : j < m24LatK.Om.size := by
    have := congrArg Array.size e
    simp only [Array.size_map] at this
    rw [this]
    simpa using hj
  rw [← e, getElem!_pos _ j hjO, getElem!_pos _ j (by simpa using hjO), Array.getElem_map]

theorem m24_Ot_size (j : ℕ) (hj : j < 13) :
    m24OtK[j]!.lbl.size = #[1, 64, 16, 16, 8, 4, 8, 2, 2, 2, 4, 2, 4][j]! := by
  have e := M24Lat.spec.2.2.2.2.2
  have hjO : j < m24OtK.size := by
    have := congrArg Array.size e
    simp only [Array.size_map] at this
    rw [this]
    simpa using hj
  rw [← e, getElem!_pos _ j hjO, getElem!_pos _ j (by simpa using hjO), Array.getElem_map]

theorem m24_rows : (List.range 13).map (defaultRow 10 m24Ctx.D m24OtK) = m24Mems := by
  have e : ∀ j ∈ List.range 13, defaultRow 10 m24Ctx.D m24OtK j =
      ⟨#[1, 315, 63, 135, 21, 9, 21, 3, 3, 3, 9, 3, 9][j]! * 2 ^ 10,
        2 ^ 10 / #[1, 64, 16, 16, 8, 4, 8, 2, 2, 2, 4, 2, 4][j]!,
        #[1, 315, 63, 135, 21, 9, 21, 3, 3, 3, 9, 3, 9][j]! * 2 ^ 10⟩ := by
    intro j hj
    have hj' := List.mem_range.1 hj
    unfold defaultRow
    rw [m24_D_Om, m24_Om_size j hj', m24_Ot_size j hj']
  rw [List.map_congr_left e]
  rfl

theorem m24_row (j : ℕ) (hj : j < 13) : ∃ m ∈ m24Mems, MemStmt (m24Ctx.Y j) m := by
  have hk : m24Ctx.k = 10 := rfl
  refine m24Ctx.rows_of_default (Ot := m24OtK) m24_o2OK m24Mems ?_ j (by rw [m24_J]; exact hj)
  rw [m24_J, hk]
  exact m24_rows

theorem m24_S_sylow : IsSylowTwoOf m24Ctx.S ⊤ := by
  refine K1.isSylowTwoOf_top_iff.mpr ⟨m24Ctx.S_isPGroup, ?_⟩
  have h1 := Subgroup.card_mul_index m24Ctx.S
  rw [m24Ctx.S_card, card_M24] at h1
  have h2 : m24Ctx.S.index = 239085 := by
    have : m24Ctx.k = 10 := rfl
    rw [this] at h1
    omega
  rw [h2]
  norm_num

open CFSG.Blueprint.NativeSporadic in
theorem m24_overgroups {X : Type} [Group X] [Finite X] (hX : Nonempty (X ≃* Carrier .M24))
    {T Y : Subgroup X} (hT : IsSylowTwoOf T ⊤) (hTY : T ≤ Y) :
    Y = ⊤ ∨ ∃ m ∈ m24Mems, Nat.card Y = m.order ∧ Nat.card (pCoreOf 2 Y) = m.o2 ∧
      ∀ (N : Subgroup Y) [N.Normal], IsPGroup 2 (Y ⧸ N) → Nat.card (Y ⧸ N) ≤ m.quot2 := by
  obtain ⟨e⟩ := hX
  have hX' : Nonempty (X ≃* ↥CFSG.Blueprint.NativeSporadic.M24) := ⟨e⟩
  exact overgroups_of_lattice m24Ctx.S m24_S_sylow 13 m24Ctx.Y m24Mems m24_complete
    (fun j hj => m24_row j hj) hX' hT hTY

theorem m24_member_card (j : ℕ) (hj : j < 13) :
    Nat.card (m24Ctx.Y j) = #[1, 315, 63, 135, 21, 9, 21, 3, 3, 3, 9, 3, 9][j]! * 1024 := by
  have h1 : j < m24Ctx.J := by rw [m24_J]; exact hj
  rw [m24Ctx.Y_card h1, m24_D_Om, m24_Om_size j hj]
  rfl

end Lattice

end CFSG.QuasithinUnique.Ch1.SporLat.M24
