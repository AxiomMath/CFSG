module

public import CFSG.ClassicalInvolution.RouteD.Sp3C4Block
public import CFSG.ClassicalInvolution.RouteD.TypeF4TwinPiece
public import CFSG.ClassicalInvolution.RouteD.Sp3C4Visible
public import CFSG.ClassicalInvolution.RouteD.TypeF4TwinP1

public section

namespace CFSG.ClassicalInvolution.RouteD.Sp3C4

open CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.RouteD
  CFSG.ClassicalInvolution.RouteD.NonClassical

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K : Subgroup G} {z : G}

theorem blockDataU_of_twinP1 (S : CSetup p f 3 Ω K z) (d : ShapeCDict p f 3 Ω z)
    (hnl : ¬ F4Linked p f Ω K z) (hP1 : TwinProductP1 p f Ω K z) (Fr : Frame p f 3 Ω K z) :
    BlockDataU Fr where
  p1 i j hij := by
    obtain ⟨M, w, hM, hMw, hMK, hKM, -, hx⟩ := Fr.exists_twinPair S hij
    rw [hx]
    exact Gaps.localOddCentral_conj S.conjInvariant _ _ (hP1 M hM w hMw hMK hKM)
  unl i j hij := by
    obtain ⟨M, w, hM, hMw, hMK, hKM, -, hx⟩ := Fr.exists_twinPair S hij
    have hzi : Fr.zf i = Fr.gf i * z * (Fr.gf i)⁻¹ := rfl
    have hzj : Fr.zf j = Fr.gf i * w * (Fr.gf i)⁻¹ := by
      have : Fr.zf i * Fr.zf j = Fr.zf i * (Fr.gf i * w * (Fr.gf i)⁻¹) := by
        rw [hx, hzi]
        group
      exact mul_left_cancel this
    have h := (unlinked_and_clique_of_not_f4Linked S.odd S.five S.inClass S.exact S.mem S.cls
      S.p1_z d hnl hM hMw hMK hKM).1
    rw [Fr.eq_conj i, hzj, hzi]
    exact h.conj S.conjInvariant (Fr.gf i)
  clique i j hij := by
    obtain ⟨M, w, hM, hMw, hMK, hKM, hgM, hx⟩ := Fr.exists_twinPair S hij
    have hzi : Fr.zf i = Fr.gf i * z * (Fr.gf i)⁻¹ := rfl
    have hzj : Fr.zf j = Fr.gf i * w * (Fr.gf i)⁻¹ := by
      have : Fr.zf i * Fr.zf j = Fr.zf i * (Fr.gf i * w * (Fr.gf i)⁻¹) := by
        rw [hx, hzi]
        group
      exact mul_left_cancel this
    have h := (unlinked_and_clique_of_not_f4Linked S.odd S.five S.inClass S.exact S.mem S.cls
      S.p1_z d hnl hM hMw hMK hKM).2
    rw [Fr.eq_conj i, ← hgM, hzj, hzi]
    exact h.conj S.conjInvariant (Fr.gf i)

end CFSG.ClassicalInvolution.RouteD.Sp3C4

namespace CFSG.ClassicalInvolution.Generic.CoreAssembly

open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.RouteD
  CFSG.ClassicalInvolution.RouteD.NonClassical
open CFSG.ClassicalInvolution.Balance.Theorem5 (TriangleLayers TriangleConnectedAll)

variable {p f : ℕ} [Fact p.Prime]

theorem sp3C4Layers_of_twinP1 (hP1 : Sp3TwinP1 p f) : Sp3C4Layers p f := by
  intro G _ _ _ hnab K z S hS hlink Fr
  have S' := cSetup_of_routeDSetup hnab S hS
  obtain ⟨d⟩ := LocalShapeC.nonempty_dict S.inClass (mem_conjClass_self K) S.cls
    (localShapeC_of_T hS)
  have B := Sp3C4.blockDataU_of_twinP1 S' d hlink (hP1 G hnab K z S hS) Fr
  intro i j k l hij hkl hki hkj hli hlj
  exact Sp3C4.layersCommute_of_blockDataU S' Fr B hij hkl hki hkj hli hlj

theorem sp3C4Side_of_twinP1 (hP1 : Sp3TwinP1 p f) : Sp3C4Side p f :=
  sp3C4Side_of_layers (sp3C4Layers_of_twinP1 hP1)

theorem pieceSp3_of_sp3TwinP1 (hP1 : Sp3TwinP1 p f) : PieceSp3 p f :=
  pieceSp3_of_sides (sp3F4Side_of_twinP1 hP1) (sp3C4Side_of_twinP1 hP1)

theorem pieceSp3_of_triangleLayers (hlay : TriangleLayers p f) (htri : TriangleConnectedAll p f) :
    PieceSp3 p f :=
  pieceSp3_of_sp3TwinP1 (sp3TwinP1_of_triangleInputs hlay htri)

end CFSG.ClassicalInvolution.Generic.CoreAssembly
