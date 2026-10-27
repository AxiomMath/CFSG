module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec11L117Bld
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec11L117Key
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec11L117J

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

theorem sec11c_JMod_T [Finite G] (hp : Asc82Pre11) (r : Asc82Res11a) {t : G} {L S : Subgroup G}
    {z : G} {K1 K2 T R : Subgroup G} (hctx : Sec11Ctx G t L S z K1 K2 T R) :
    JMod z T = secCTQ K1 K2 T ⊔ secQ K1 K2 := by
  obtain ⟨a, x, hax⟩ := r.l113 G t L S z K1 K2 T R hctx
  have hcnt := sec11_cnt_of_ax hp r hax
  have hQ : secQ K1 K2 = twoCoreIn K1 ⊔ twoCoreIn K2 := sec11_Q_eq_sup hp hctx.toSec10Ctx
  have hQT : secQ K1 K2 ≤ T := by
    rw [hQ]
    exact sup_le (sec11_Q1_le_T hp hctx) (sec11_Q2_le_T hp hctx)
  have hWT : secCTQ K1 K2 T ⊔ secQ K1 K2 ≤ T := sup_le inf_le_right hQT
  have hzW : z ∈ secCTQ K1 K2 T ⊔ secQ K1 K2 := Subgroup.mem_sup_left (sec11_z_mem_C hp hctx)
  have hW : IsElemAbelianMod z (secCTQ K1 K2 T ⊔ secQ K1 K2) := sec11_W_elemAb hp r hctx
  refine sec11_JMod_eq_of_key hWT hzW hW fun V hVT hV => ?_
  have hkey := sec11_key117_abstract hcnt hVT hV
  rw [← hQ] at hkey
  exact hkey

end CFSG.OddStandard.SmallF3.Omega
