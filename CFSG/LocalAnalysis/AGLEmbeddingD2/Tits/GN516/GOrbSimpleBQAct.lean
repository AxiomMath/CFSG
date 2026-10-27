module

public import CFSG.Quasithin.Background.B6Defs

public section

namespace CFSG.AGLEmbeddingD2.Tits.GN516.SimpleBQ

open CFSG.Quasithin

variable {Y : Type*} [Group Y]

@[expose] def conjAut (L : Subgroup Y) (r : Y) (hr : r ∈ Subgroup.normalizer (L : Set Y)) :
    MulAut ↥L where
  toFun l := ⟨r * l * r⁻¹, (Subgroup.mem_normalizer_iff.1 hr l).1 l.2⟩
  invFun l := ⟨r⁻¹ * l * r,
    (Subgroup.mem_normalizer_iff.1 hr (r⁻¹ * l * r)).2 (by simpa [mul_assoc] using l.2)⟩
  left_inv l := Subtype.ext (by simp [mul_assoc])
  right_inv l := Subtype.ext (by simp [mul_assoc])
  map_mul' a b := Subtype.ext (by simp [mul_assoc])

theorem coe_conjAut (L : Subgroup Y) {r : Y} (hr : r ∈ Subgroup.normalizer (L : Set Y)) (l : ↥L) :
    ((conjAut L r hr l : ↥L) : Y) = r * l * r⁻¹ :=
  rfl

@[expose] def actHom {L R : Subgroup Y} (hRN : R ≤ Subgroup.normalizer (L : Set Y)) :
    ↥R →* MulAut ↥L :=
  MonoidHom.mk' (fun r => conjAut L r.1 (hRN r.2)) fun a b =>
    MulEquiv.ext fun l => Subtype.ext (by simp [coe_conjAut, mul_assoc])

theorem coe_actHom {L R : Subgroup Y} (hRN : R ≤ Subgroup.normalizer (L : Set Y)) (r : ↥R)
    (l : ↥L) : ((actHom hRN r l : ↥L) : Y) = r * l * (r : Y)⁻¹ :=
  rfl

theorem map_map_subtype_eq_conjSub {L : Subgroup Y} (α : MulAut ↥L) {r : Y}
    (hα : ∀ x : ↥L, ((α x : ↥L) : Y) = r * x * r⁻¹) (A : Subgroup ↥L) :
    (A.map α.toMonoidHom).map L.subtype = B6.conjSub r (A.map L.subtype) := by
  have hcomp : L.subtype.comp α.toMonoidHom = (MulAut.conj r).toMonoidHom.comp L.subtype :=
    MonoidHom.ext fun x => by simpa using hα x
  rw [Subgroup.map_map, hcomp, ← Subgroup.map_map]
  rfl

end CFSG.AGLEmbeddingD2.Tits.GN516.SimpleBQ
