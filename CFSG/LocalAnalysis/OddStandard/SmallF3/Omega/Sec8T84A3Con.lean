module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84A3Ab
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84A3Ker
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84A3Lift
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84A3Facts

public section

namespace CFSG.OddStandard.SmallF3.Omega

namespace A3

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {z g : G}
  {B K L1 : Subgroup G}

theorem case2_false (F : Sec8T84Base) (hA5 : Sec8T84FactA5) (hLift : Sec8T84FactLift)
    (hctx : Sec8Ctx G t L S z g B) (h : Sec8T84L1 G t L S z g B K L1)
    (hsq : ∀ l ∈ L1, l * l = tauFn t l) : False := by
  obtain ⟨H5, hH5, ⟨e5⟩, htr⟩ := hA5 G B hctx.B_e16 (autIn L B) (aut_B_of F hctx).1
  have hrange : H5 ≤ (fHom L B).range := by
    rw [fHom_range]
    exact hH5
  obtain ⟨H', ⟨e⟩, hlift⟩ := exists_lift_equiv (fHom L B) (gHom hctx h)
    (fun m hm => ker_f_le F hctx h m hm) (fun m hm => ker_g_le hctx h m hm) H5 hrange
  refine hLift G L1 (fun x hx y hy => ab_comm h hsq hx hy) ?_ (fun x hx => ab_pow4 h hsq hx)
    (ab_sq_card hctx h hsq) H' ⟨e.trans e5⟩ ?_
  · rw [h.card]
    norm_num
  · intro x hx1 hx2 y hy1 hy2
    have hxB : (x : G) ∈ B := (ab_sq_eq_one_iff hctx h hsq x.2).mp hx1
    have hyB : (y : G) ∈ B := (ab_sq_eq_one_iff hctx h hsq y.2).mp hy1
    have hx' : (⟨(x : G), hxB⟩ : ↥B) ≠ 1 := fun he =>
      hx2 (Subtype.ext (by simpa using congrArg Subtype.val he))
    have hy' : (⟨(y : G), hyB⟩ : ↥B) ≠ 1 := fun he =>
      hy2 (Subtype.ext (by simpa using congrArg Subtype.val he))
    obtain ⟨α, hα, hαxy⟩ := htr _ hx' _ hy'
    obtain ⟨m, hm⟩ := MonoidHom.mem_range.mp (hrange hα)
    refine ⟨gHom hctx h m, hlift m (by rw [hm]; exact hα), Subtype.ext ?_⟩
    have h1 := gHom_coe_B hctx h m (b := x) hxB
    have h2 := fHom_apply_coe L B m ⟨(x : G), hxB⟩
    rw [h1, ← h2, hm]
    exact congrArg Subtype.val hαxy

end A3

end CFSG.OddStandard.SmallF3.Omega
