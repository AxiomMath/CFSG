module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKD309ModelPkg
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesRankPLinUniMat
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKD309ModelOrd

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KD309M

open CFSG.LocalAnalysis.RankThreeUC.S15.ACore Subgroup Matrix
open CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KD309L
open CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.I292CaseA
open CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.I292CaseB
open CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.RankP.LU

variable {Y : Type} [Group Y] [Finite Y] {L : Subgroup Y} [L.Normal] [Group.IsPerfect ↥L] {x : Y}

theorem theta_injective (pkg : Pkg Y L x) (hC : centralizer (L : Set Y) = ⊥) :
    Function.Injective (thetaP L pkg.eP) := by
  rw [injective_iff_map_eq_one]
  intro y hy
  have := (thetaP_eq_one_iff L pkg.eP y).mp hy
  rw [hC] at this
  exact (Subgroup.mem_bot.mp this)

theorem exists_phi (pkg : Pkg Y L x) (hC : centralizer (L : Set Y) = ⊥) :
    ∃ Φ : M5 →* Y, KerSc Φ ∧ ∃ w : Y, w * Φ (monS (C := C5) sig5) * w⁻¹ = (Φ (mT ddv))⁻¹ := by
  set θ := thetaP L pkg.eP with hθ
  have hinj : Function.Injective θ := theta_injective pkg hC
  set M := pkg.M with hM
  let β : M5 →* ↥M.𝔾 := (monEmb pkg.e 5 : M5 →* GL (Fin 5) pkg.K).codRestrict M.𝔾 pkg.hmon
  let γ : M5 →* MulAut pkg.P' := M.c.comp β
  have hγ : ∀ m : M5, γ m ∈ θ.range := fun m => pkg.hAut.D_le ⟨β m, rfl⟩
  let Φ : M5 →* Y := ((MonoidHom.ofInjective hinj).symm : θ.range ≃* Y).toMonoidHom.comp
    (γ.codRestrict θ.range hγ)
  have hθΦ : ∀ m, θ (Φ m) = γ m := fun m => by
    change θ ((MonoidHom.ofInjective hinj).symm ⟨γ m, hγ m⟩) = γ m
    exact MonoidHom.apply_ofInjective_symm hinj ⟨γ m, hγ m⟩
  refine ⟨Φ, ?_, ?_⟩
  · intro m
    rw [← map_eq_one_iff θ hinj, hθΦ]
    constructor
    · intro h
      obtain ⟨z, hz⟩ := M.c_eq_one (β m) h
      obtain ⟨c, hc⟩ := exists_monScalar_of_emb_eq_scalar (by norm_num) pkg.he hz
      exact ⟨c, hc⟩
    · rintro ⟨c, rfl⟩
      have hs : GeneralLinearGroup.scalar (Fin 5) (pkg.e c) ∈ M.𝔾 := by
        rw [← monEmb_monScalar]
        exact pkg.hmon _
      have h1 : β (monScalar C5 5 c) = ⟨GeneralLinearGroup.scalar (Fin 5) (pkg.e c), hs⟩ :=
        Subtype.ext (monEmb_monScalar pkg.e c)
      change M.c (β (monScalar C5 5 c)) = 1
      rw [h1]
      exact c_scalar M hs
  · refine ⟨(MonoidHom.ofInjective hinj).symm ⟨M.c ⟨pkg.F, pkg.hF⟩, pkg.hAut.D_le ⟨_, rfl⟩⟩, ?_⟩
    apply hinj
    have hw : θ ((MonoidHom.ofInjective hinj).symm
        ⟨M.c ⟨pkg.F, pkg.hF⟩, pkg.hAut.D_le ⟨_, rfl⟩⟩) = M.c ⟨pkg.F, pkg.hF⟩ :=
      MonoidHom.apply_ofInjective_symm hinj ⟨M.c ⟨pkg.F, pkg.hF⟩, pkg.hAut.D_le ⟨_, rfl⟩⟩
    rw [map_mul, map_mul, map_inv, map_inv, hw, hθΦ, hθΦ]
    change M.c ⟨pkg.F, pkg.hF⟩ * M.c (β (monS sig5)) * (M.c ⟨pkg.F, pkg.hF⟩)⁻¹ =
      (M.c (β (mT ddv)))⁻¹
    rw [← map_inv, ← map_mul, ← map_mul, ← map_inv]
    congr 1
    apply Subtype.ext
    exact pkg.hFconj

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KD309M
