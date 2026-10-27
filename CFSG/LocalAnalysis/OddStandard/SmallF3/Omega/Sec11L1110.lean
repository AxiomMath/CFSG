module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec11L1110Case
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec11L1110Dih

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

theorem asc82Lemma1110_of (hp : Asc82Pre11) (r : Asc82Res11a) (h118 : Asc82Lemma118)
    (hT : Asc82Step1110Type) (hS : Asc82Step1110Single) : Asc82Lemma1110 := by
  intro G _ _ t L S z K1 K2 T R hctx
  have hsub : ∀ h ∈ centralizer ({z} : Set G), h⁻¹ * t * h ∈ R → h⁻¹ * t * h ∈ secD K1 K2 R :=
    fun h hh hR => sec11L1110_sub_D hp hT hS h118 hctx hh hR
  refine ⟨hsub, ?_⟩
  have hΘD : secTheta t z R ⊆ secD K1 K2 R := by
    rintro s ⟨hsR, h, hh, rfl⟩
    exact hsub h hh hsR
  obtain ⟨-, hz2, htz, -, hz1⟩ := sec11_invols hctx.toSec10Ctx
  exact sec11L1110_isDih2_closure (r.l114 G t L S z K1 K2 T R hctx) hΘD
    (sec11_Theta_order hctx.toSec10Ctx R) (sec11_t_mem_Theta hp hctx)
    (sec11_tz_mem_Theta hp r.l111N hctx) hz2 hz1 htz

end CFSG.OddStandard.SmallF3.Omega
