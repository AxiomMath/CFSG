
module

public import CFSG.Certificates.Kernel.ThDemp.OrbPtsBase

public import CFSG.Certificates.Kernel.ThDemp.OrbStab
public import CFSG.Certificates.Kernel.Th.Spec.FwdRel
public import CFSG.Certificates.Kernel.ThDemp.OrbCent
public import CFSG.Certificates.Kernel.ThDemp.OrbUnfold
public import CFSG.Certificates.Kernel.ThDemp.Sound

public section

namespace CFSG.Certificates.ThDemp.Pts

open MulAction CFSG.KC.Th CFSG.KC.Th.BigS CFSG.KC.Th.Spec CFSG.KC.ThDemp
  CFSG.Certificates.ThDemp.Act CFSG.Certificates.ThDemp.Lanes CFSG.Certificates.ThDemp.Batches
  CFSG.Certificates.ThDemp.Key CFSG.Certificates.ThDemp.Stab CFSG.Certificates.ThDemp.Rows
  CFSG.KC.Loop

set_option exponentiation.threshold 2000

variable {J : Subgroup (GL (Fin 248) (ZMod 2))} {D : DempData} {O : OrbData}

section

variable (hF : DempFacts D) (hJ : RegJ D J) (hw : wordsChk D O = true)
include hF hJ hw

local notation "𝕄" g:max =>
  ((Subtype.val g : GL (Fin 248) (ZMod 2)) : Matrix (Fin 248) (Fin 248) (ZMod 2))

theorem sp_pt_mem_orbit (i : ℕ) : sp (pt D O i) ∈ orbit J (sp (U0 D)) := by
  have hr : ∀ r ∈ lgetL O.words i, 0 < r ∧ r < D.nreg := fun r hr => by
    obtain ⟨w, hw', hrw⟩ := mem_lgetL _ _ _ hr
    exact wordsChk_sound hw w hw' r hrw
  obtain ⟨g, hg⟩ := exists_word hJ _ hr
  refine ⟨g⁻¹, ?_⟩
  change g⁻¹ • sp (U0 D) = _
  rw [inv_smul_eq, hg]
  unfold pt
  rw [Unfold.sp_wordR hF]

theorem lil_pt (hU : LIL (rowsOf (2 ^ 248 - 1) (U0 D))) (i : ℕ) :
    LIL (rowsOf (2 ^ 248 - 1) (pt D O i)) := by
  refine Unfold.lil_wordR hF _ _ (fun r hr => ?_) hU
  obtain ⟨w, hw', hrw⟩ := mem_lgetL _ _ _ hr
  obtain ⟨h1, h2⟩ := wordsChk_sound hw w hw' r hrw
  obtain ⟨x, hx⟩ := hJ r h1 h2
  exact ⟨𝕄 x⁻¹, by rw [← hx]; exact mat_mul_inv x⟩

end

namespace Ctx

variable (C : Ctx D O J) (hrm : D.rm = 2 ^ 248 - 1) (h : orbChk D O = true)
  (h9 : pt D O 9 < 2 ^ 1280) (hP9 : LIL (rowsOf (2 ^ 248 - 1) (pt D O 9)))
include hrm h h9 hP9

end Ctx

end CFSG.Certificates.ThDemp.Pts

end
