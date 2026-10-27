module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.G2Three.Sec1Proof.LBase
public import CFSG.GH74.KGroups.L28
public import CFSG.Adapters.ProjectiveSpecialLinear

public section

namespace CFSG.OddStandard.HigherRank.G2Three.Sec1Proof.Tab

open CFSG.OddStandard.HigherRank.G2Three.Sec1 CFSG.Open Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {m : G23Model G}

set_option quotPrecheck false in
local notation "D1" => (t1G ()).tab
set_option quotPrecheck false in
local notation "I1" => idx1 (t1G ()).tab

theorem lieModel_psl_gf8 :
    CFSG.Blueprint.LieModel (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 3))
      .PSL 2 2 3 :=
  Or.inl ⟨by decide,
    CFSG.Assembly.LowTwoRank.statedClassicalModel_psl_two_of_mulEquiv
      (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 3)) 2 3 (by norm_num)
      (MulEquiv.refl _)⟩

theorem card_mulAut_psl_gf8 :
    Nat.card (MulAut (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 3))) = 1512 :=
  CFSG.GH74.KGroups.L28.card_mulAut lieModel_psl_gf8

theorem G23LCtx.card_F (X : G23LCtx m) : Nat.card (frameOf m).F = 8 := by
  rw [X.f5.F_isE.2]
  norm_num

theorem G23LCtx.F_le_centEl_sigma (X : G23LCtx m) :
    (frameOf m).F ≤ centEl m.L (frameOf m).σ := by
  intro f hf
  have hFL : f ∈ m.L := (F_le_S (frameOf m).toSFrame).trans (frame_S_le m) hf
  have hcen : f ∈ Subgroup.centralizer ({(frameOf m).σ} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr (X.f1.F_cent_sigma f hf).symm
  rw [centEl]
  exact Subgroup.mem_inf.mpr ⟨hFL, hcen⟩

theorem G23LCtx.card_centEl_sigma (m : G23Model G) :
    Nat.card (centEl m.L (frameOf m).σ) = 1512 := by
  obtain ⟨e⟩ := m.cent_outer (frameOf m).σ (frame_sigma_not_mem m) (frame_sigma_sq m)
  rw [Nat.card_congr e.toEquiv]
  exact card_mulAut_psl_gf8

theorem G23LCtx.fact17 (X : G23LCtx m) :
    (frameOf m).Fact17 m.L :=
  ⟨m.cent_outer (frameOf m).σ (frame_sigma_not_mem m) (frame_sigma_sq m),
    isSylowIn_two_of_card X.F_le_centEl_sigma (G23LCtx.card_centEl_sigma m) X.card_F⟩

end CFSG.OddStandard.HigherRank.G2Three.Sec1Proof.Tab
