module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5Defs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4Conj

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

theorem isOm6Z2_conjugate {L : Subgroup G} (h : IsOm6Z2 L) (g : G) :
    IsOm6Z2 (CFSG.conjugate L g) := by
  have e : ↥L ≃* ↥(CFSG.conjugate L g) :=
    Subgroup.equivMapOfInjective L (MulAut.conj g⁻¹).toMonoidHom (MulAut.conj g⁻¹).injective
  obtain ⟨e'⟩ := nonempty_quotient_oddCore_mulEquiv e
  exact ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv e h.1, isTwoU43_of_mulEquiv e' h.2⟩

theorem Sec5Setting.conjugate [Finite G] {t : G} {L : Subgroup G} (h : Sec5Setting G t L)
    (g : G) : Sec5Setting G (g⁻¹ * t * g) (CFSG.conjugate L g) := by
  have e : ↥L ≃* ↥(CFSG.conjugate L g) :=
    Subgroup.equivMapOfInjective L (MulAut.conj g⁻¹).toMonoidHom (MulAut.conj g⁻¹).injective
  obtain ⟨e'⟩ := nonempty_quotient_oddCore_mulEquiv e
  exact { toSec3SettingLB := h.toSec3SettingLB.conjugate g
          twoU43 := isTwoU43_of_mulEquiv e' h.twoU43 }

theorem Sec5Ctx.conjugate [Finite G] {t : G} {L S : Subgroup G} {z : G} (h : Sec5Ctx G t L S z)
    (g : G) : Sec5Ctx G (g⁻¹ * t * g) (CFSG.conjugate L g) (CFSG.conjugate S g)
      (g⁻¹ * z * g) :=
  ⟨h.toSec5Setting.conjugate g, h.toAsc82Notation.conjugate g⟩

end CFSG.OddStandard.SmallF3.Omega
