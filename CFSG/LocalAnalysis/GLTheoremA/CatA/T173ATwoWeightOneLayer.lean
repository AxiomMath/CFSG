module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173ATwoDefs
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S172AExistBase
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S172ALayerGL
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173XDefs

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T173A

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.Assembly CFSG.LocalAnalysis.GLTheoremA
open CFSG.LocalAnalysis.GLTheoremA.S172A.GL (fixSp comSp Nsub)
open CFSG.LocalAnalysis.GLTheoremA.T173X
  (stdLayer innerClosure stdFamily IsStdElt StdVanishes StdTyped StdExtends)

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]

theorem lin_two_weightOne_layer (hV : 5 ≤ Module.finrank (ZMod 2) V) {g : V ≃ₗ[ZMod 2] V}
    (hg3 : g ^ 3 = 1) (h2 : Module.finrank (ZMod 2) (comSp g) = 2) :
    stdLayer g = Nsub hg3 := by
  have hsum := S172A.GL.finrank_fixSp hg3
  have hc : Module.finrank (ZMod 2) (fixSp g) = Module.finrank (ZMod 2) V - 2 := by omega
  exact (S172A.layer_eq_of_normal_quasisimple (S172A.GL.Nsub_le_cent hg3)
    (S172A.GL.Nsub_normal hg3) (S172A.GL.Nsub_isQuasisimple_c (by omega) hg3 hc)
    (S172A.GL.comm_le_Nsub hg3 h2)).2

private theorem three_dvd_card_Nsub_of_two_le {e : V ≃ₗ[ZMod 2] V} {c : ℕ} (hc2 : 2 ≤ c)
    (h3 : e ^ 3 = 1) (hfix : Module.finrank (ZMod 2) (fixSp e) = c) :
    3 ∣ Nat.card (Nsub h3) := by
  obtain ⟨E0, -, hE0card⟩ :=
    CFSG.LocalAnalysis.GLTheoremA.KD264Lie.X1LinCore.Std.exists_elemAb_card (fixSp e) c hfix
  have h1 : Nat.card E0 ∣ Nat.card (fixSp e ≃ₗ[ZMod 2] fixSp e) :=
    Subgroup.card_subgroup_dvd_card E0
  have h2 : Nat.card (Nsub h3) = Nat.card (fixSp e ≃ₗ[ZMod 2] fixSp e) :=
    Nat.card_congr
      (MonoidHom.ofInjective (S172A.GL.glueHom_injective
        (S172A.GL.isCompl_fixSp_comSp h3))).symm.toEquiv
  rw [h2]
  refine dvd_trans ?_ h1
  rw [hE0card]
  exact dvd_pow_self 3 (by omega)

theorem lin_two_weightOne_layerType (hV : 7 ≤ Module.finrank (ZMod 2) V)
    {g : V ≃ₗ[ZMod 2] V} (hg3 : g ^ 3 = 1) (h2 : Module.finrank (ZMod 2) (comSp g) = 2) :
    catalogIs (PSimple 3 (stdLayer g)) (isLnA (Module.finrank (ZMod 2) V - 2) 2) := by
  have hc : Module.finrank (ZMod 2) (fixSp g) = Module.finrank (ZMod 2) V - 2 := by
    have := S172A.GL.finrank_fixSp hg3
    omega
  rw [lin_two_weightOne_layer (by omega) hg3 h2]
  have hq := S172A.GL.Nsub_isQuasisimple_c (by omega) hg3 hc
  have hZ := S172A.GL.Nsub_center_c (by omega) hg3 hc
  have h3 : 3 ∣ Nat.card (Nsub hg3) := three_dvd_card_Nsub_of_two_le (by omega) hg3 hc
  exact S172A.catalogIs_isLnA_of_vecAut (by omega)
    ((Classical.choice (S172A.pSimple_equiv hq hZ h3)).trans (S172A.GL.NsubEquivC hg3 hc))

end CFSG.LocalAnalysis.GLTheoremA.T173A

end
