module

public import CFSG.LargeExtraspecial.A2ModSLc
public import Mathlib.FieldTheory.Finite.GaloisField

public section

namespace CFSG.LargeExtraspecial.A2Mod

open Matrix

variable {n : ℕ}

noncomputable def ringEquivZModTwo (F : Type*) [Field F] [Finite F] (hF : Nat.card F = 2) :
    F ≃+* ZMod 2 := by
  letI : Fintype F := Fintype.ofFinite F
  exact FiniteField.ringEquivOfCardEq (by rw [← Nat.card_eq_fintype_card, hF, ZMod.card])

noncomputable def galoisFieldTwoOneEquiv : GaloisField 2 1 ≃+* ZMod 2 :=
  (GaloisField.equivZmodP 2).toRingEquiv

variable {R S : Type*} [CommRing R] [CommRing S]

@[expose] noncomputable def slEquiv (e : R ≃+* S) :
    SpecialLinearGroup (Fin n) R ≃* SpecialLinearGroup (Fin n) S :=
  MonoidHom.toMulEquiv (SpecialLinearGroup.map e.toRingHom)
    (SpecialLinearGroup.map e.symm.toRingHom)
    (by
      ext g i j
      simp [SpecialLinearGroup.map_apply_coe])
    (by
      ext g i j
      simp [SpecialLinearGroup.map_apply_coe])

theorem slEquiv_symm (e : R ≃+* S) :
    (slEquiv e).symm = (slEquiv e.symm : SpecialLinearGroup (Fin n) S ≃* _) :=
  rfl

theorem slEquiv_transvection (e : R ≃+* S) {i j : Fin n} (hij : i ≠ j) (c : R) :
    slEquiv e (SpecialLinearGroup.transvection hij c) =
      SpecialLinearGroup.transvection hij (e c) :=
  SpecialLinearGroup.map_transvection e.toRingHom hij c

theorem map_slEquiv_range_transvectionHom (e : R ≃+* S) {i j : Fin n} (hij : i ≠ j) :
    (SpecialLinearGroup.transvectionHom (A := R) hij).range.map (slEquiv e).toMonoidHom =
      (SpecialLinearGroup.transvectionHom (A := S) hij).range := by
  ext b
  simp only [Subgroup.mem_map, MonoidHom.mem_range, MulEquiv.coe_toMonoidHom]
  constructor
  · rintro ⟨_, ⟨c, rfl⟩, rfl⟩
    refine ⟨Multiplicative.ofAdd (e (Multiplicative.toAdd c)), ?_⟩
    rw [SpecialLinearGroup.transvectionHom_apply, SpecialLinearGroup.transvectionHom_apply,
      slEquiv_transvection, toAdd_ofAdd]
  · rintro ⟨c, rfl⟩
    refine ⟨_, ⟨Multiplicative.ofAdd (e.symm (Multiplicative.toAdd c)), rfl⟩, ?_⟩
    rw [SpecialLinearGroup.transvectionHom_apply, SpecialLinearGroup.transvectionHom_apply,
      slEquiv_transvection, toAdd_ofAdd, RingEquiv.apply_symm_apply]

end CFSG.LargeExtraspecial.A2Mod
