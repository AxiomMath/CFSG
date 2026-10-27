module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I167CDefs
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I167Defs
import CFSG.LocalAnalysis.GLTheoremA.CatA.I167CBDescent
import CFSG.LocalAnalysis.GLTheoremA.CatA.I167CTrans
import CFSG.LocalAnalysis.GLTheoremA.CatA.K1419ClsExcOut
import CFSG.LocalAnalysis.GLTheoremA.CatA.K1419ClsLabel
import CFSG.LocalAnalysis.GLTheoremA.CatA.S265SF1

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I167

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA.S10

section Certificates


theorem i167Class_of_families (hLin : I167CLin) (hUni : I167CUni) (hSymp : I167CSymp)
    (hOrth : I167COrth) : I167Class := by
  intro Ω _ _ p B X D J x hp hp2 hB hX _ hBN _ hSC _ hD hJ hDJ hTJ _ hxD hxX hDx _ hhs hinn hclass
  have hxB : x ∈ B := hD.1 hxD
  have hxp : x ^ p = 1 := hB.2 x hxB
  have hperf : Group.IsPerfect ↥X := ⟨hX.1⟩
  have hRig := CFSG.StandardType.ggLabelRigidInput_holds
  haveI := nontrivial_pSimple_of_innDiagOn hinn
  obtain ⟨eX⟩ := CFSG.LocalAnalysis.GLTheoremA.S265.SF.nonempty_centerQuot_equiv_pSimple (p := p) hX
  have hcat : catalogIs (↥X ⧸ Subgroup.center ↥X) K1419.I1419Classical2 :=
    (catalogIs_congr eX).2 hclass
  obtain ⟨labK, hlabX, hkind⟩ := i167C_innDiag hX hBN hxB hinn
  have hfam := i167C_family
    (K1419.k1419ClsExcOut_of_rigid hRig K1419.k1419ClsClassLabel_holds) hX hlabX hcat
  have hJx : GLAPComponent p (X ⊓ cx x) J := glaPComponent_inf_cx_of_eq_sup hDx hJ
  obtain ⟨hJim, ⟨eJ⟩⟩ := i167C_comp hp hBN hxB hJx
  have hJX : J ≤ X := hJ.1.trans inf_le_left
  have hJperf : ⁅J, J⁆ = J := CFSG.LocalAnalysis.GLTheoremB.glaPComponent_perfect hJ
  have key : ∀ {Fam : GLALabel → Prop}, I167CAt Fam → Fam labK → Type167 p X J := by
    intro Fam hAt hF
    exact type167_of_type167S eX eJ
      (hAt (↥X ⧸ Subgroup.center ↥X) p (normalizerToCenterQuotientAut X B hBN).range
        (normalizerToCenterQuotientAut X B hBN ⟨x, hxB⟩)
        ((J.subgroupOf X).map (QuotientGroup.mk' (Subgroup.center ↥X))) labK hp hp2 hF
        (CFSG.LocalAnalysis.GLTheoremA.Y10F.center_centerQuot_eq_bot hX)
        (isElemAbelian_rho_range hBN hB) ⟨⟨x, hxB⟩, rfl⟩
        (orderOf_rho_eq hp hperf hBN hxB hxp hxX) hkind
        (fun hPF => scpS_of_sc hp hBN (hPF ↥X hX ⟨MulEquiv.refl _⟩) hSC)
        (centJ_descent hperf hBN hxB hJX hJperf hDJ hDx)
        (i167C_halfSplitLab hRig hlabX hhs) hJim (type167J_of_equiv eJ hTJ))
  rcases hfam with h | h | h | h
  · exact key (Fam := Y10GField.FamLin) hLin h
  · exact key (Fam := Y10GField.FamUni) hUni h
  · exact key (Fam := Y10GField.FamSymp) hSymp h
  · exact key (Fam := Y10GField.FamOrth) hOrth h

end Certificates

end CFSG.LocalAnalysis.GLTheoremA.I167

end
