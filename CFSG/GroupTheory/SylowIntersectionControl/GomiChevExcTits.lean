module

public import CFSG.GroupTheory.SylowIntersectionControl.GomiChevExcAut
public import CFSG.Quasithin.EmptyFaithful.F112SAut
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtCert4193
public import CFSG.Quasithin.Recognition.CertTwoF4AmalgamLocalFinal

public section

namespace CFSG.GroupTheory

open CFSG.Open CFSG.ABGLocalTools CFSG.Quasithin CFSG.Sporadic.Schreier.Tits Subgroup

theorem gomiExcAutFixed_titsD :
    GomiExcAutFixed titsD := by
  intro β _ hβ2 hβout _ _ _
  exfalso
  set x : twoF4M := twoF4MulEquiv titsOutBound β with hx
  have hx2 : (x : Equiv.Perm (Fin 1755)) * x = 1 := by
    have : x * x = 1 := by rw [hx, ← map_mul, hβ2, map_one]
    exact congrArg Subtype.val this
  have hxD := F112S.mem_titsD_of_sq F112S.titsRankCheck_cert x.2 hx2
  have hβx : twoF4ConjD x = β :=
    (MulEquiv.ofBijective twoF4ConjD (twoF4ConjD_bijective titsOutBound)).apply_symm_apply β
  apply hβout ⟨x, hxD⟩
  refine MulEquiv.ext fun g => Subtype.ext ?_
  rw [← hβx, twoF4ConjD_apply, MulAut.conj_apply]
  rfl

end CFSG.GroupTheory
