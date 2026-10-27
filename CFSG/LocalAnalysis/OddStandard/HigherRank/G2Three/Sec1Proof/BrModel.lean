module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.G2Three.Sec1Proof.BrOuter
public import CFSG.LocalAnalysis.OddStandard.HigherRank.G2Three.Sec1Proof.BrRho
public import CFSG.LocalAnalysis.OddStandard.HigherRank.G2Three.Sec1Proof.BrTransport
public import CFSG.LocalAnalysis.OddStandard.HigherRank.Leaves
public import CFSG.CGT.PushingUpLit.CGT6.EmbG23.Model
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHeldSmallCoreLinear

public section

namespace CFSG.OddStandard.HigherRank.G2Three.Sec1Proof

open CFSG.OddStandard.HigherRank.G2Three.Sec1 CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.LieType.Ree CFSG.LieType.Chevalley


@[expose] noncomputable def nativeBase : G23Base (MulAut NG) where
  L := innerAut NG
  normal := normal_innerAut_NG
  card_L := card_innerAut_NG
  card_G := card_mulAut_NG
  invol_conj := invol_conj_NG
  card_cent := card_cent_NG
  cent_outer := cent_outer_NG

theorem exists_native_model : ∃ m : G23Model (MulAut NG), m.L = innerAut NG := by
  obtain ⟨ρ, hinj, hc, hφ⟩ := exists_rho
  exact ⟨⟨nativeBase, ρ, hinj, MulAut.conj (xElement ⟨0, by decide⟩ 1),
    MulAut.conj (xElement ⟨1, by decide⟩ 1), MulAut.conj (yElement ⟨0, by decide⟩ 1),
    MulAut.conj (yElement ⟨1, by decide⟩ 1), phiN, ⟨_, rfl⟩, ⟨_, rfl⟩, ⟨_, rfl⟩, ⟨_, rfl⟩,
    phiN_not_inner, phiN_mul_self,
    by rw [hc, phiN_x0, iotaN_x0, iotaN_x1]; rfl,
    by rw [hc, phiN_x1, iotaN_x1, iotaN_x0]; rfl,
    by rw [hc, phiN_y0, iotaN_y0, iotaN_y1]; rfl,
    by rw [hc, phiN_y1, iotaN_y1, iotaN_y0]; rfl,
    hφ⟩, rfl⟩

theorem g23_model_exists : ∀ (Q : Type) [Group Q] [Finite Q], HRG23 Q →
    ∃ m : G23Model (MulAut Q), m.L = innerAut Q := by
  intro Q _ _ hQ
  have hm : ChevalleyExceptionalModel Q .G2 3 1 :=
    CFSG.Blueprint.LieModel.chevalleyExceptionalModel hQ (by decide)
  obtain ⟨ε⟩ := CFSG.CGT.PushingUpLit.CGT6.EmbG23.exists_equiv_g23 hm
  obtain ⟨m, hmL⟩ := exists_native_model
  refine ⟨m.transport (MulAut.congr ε).symm, ?_⟩
  rw [G23Model.transport_L, hmL]
  exact innerAut_map_congr ε

end CFSG.OddStandard.HigherRank.G2Three.Sec1Proof
