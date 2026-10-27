module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec11L114
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec11L115cD

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

theorem asc82Lemma115c_of (hp : Asc82Pre11) : Asc82Lemma115c := by
  intro G _ _ t L S z K1 K2 T R hctx
  obtain ⟨-, -, -, -, -, -, htS, hzS, -⟩ := sec11L114_data hp hctx
  obtain ⟨htQ, hzQ⟩ := sec11L114_cent_Q hp hctx
  have hS : Sec11cSplit t z K1 K2 := sec11c_split_of hp hctx.toSec10Ctx
  have hSR : S ≤ R := hctx.S_le.trans hctx.T_le
  have hD2 : IsPGroup 2 (secD K1 K2 R) := hctx.sylowR.2.1.to_le inf_le_right
  have hWD : zpowers t ⊔ zpowers z ≤ secD K1 K2 R :=
    sup_le (zpowers_le.2 ⟨htQ, hSR htS⟩) (zpowers_le.2 ⟨hzQ, hSR hzS⟩)
  have h0 : Sec11cAdm t z (secD K1 K2 R) (zpowers t ⊔ zpowers z) :=
    ⟨le_rfl, hWD, by rw [sec11c_KD_pair, sup_eq_left.2 (oddCoreIn_normal _).1]⟩
  have hmax := sec11c_adm_max hS inf_le_left hD2 _ _ rfl h0
  exact ⟨fun r hr => sec11c_normalizer_KD (sec11c_normalizer_D hctx.sylowR.1 hr), hmax.2.2⟩

end CFSG.OddStandard.SmallF3.Omega
