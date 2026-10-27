module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.TypesOmegaProj

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open QuadraticMap

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

@[expose] noncomputable def omegaToProj (hQ : Q.Nondegenerate) : omegaGroup hQ →* omegaProj hQ :=
  ((toProj Q).domRestrict (omegaGroup hQ)).codRestrict (omegaProj hQ)
    (fun g => (mem_omegaProj_iff hQ).mpr ⟨g, g.2, rfl⟩)

theorem coe_omegaToProj (hQ : Q.Nondegenerate) (g : omegaGroup hQ) :
    ((omegaToProj hQ g : omegaProj hQ) : ProjOrth Q) = toProj Q (g : OGroup Q) := rfl

theorem omegaToProj_surjective (hQ : Q.Nondegenerate) : Function.Surjective (omegaToProj hQ) := by
  rintro ⟨x, hx⟩
  obtain ⟨g, hg, rfl⟩ := (mem_omegaProj_iff hQ).mp hx
  exact ⟨⟨g, hg⟩, Subtype.ext rfl⟩

theorem omegaToProj_eq_one_iff (hQ : Q.Nondegenerate) (g : omegaGroup hQ) :
    omegaToProj hQ g = 1 ↔ (g : OGroup Q) = 1 ∨ (g : OGroup Q) = piOrth Q := by
  constructor
  · intro hg
    have h1 : toProj Q (g : OGroup Q) = 1 := congrArg Subtype.val hg
    exact mem_piGroup_iff.mp ((QuotientGroup.eq_one_iff _).mp h1)
  · intro hg
    apply Subtype.ext
    change toProj Q (g : OGroup Q) = 1
    rcases hg with h | h
    · rw [h, map_one]
    · rw [h, toProj_piOrth]

theorem mul_piOrth_comm (g : OGroup Q) : g * piOrth Q = piOrth Q * g :=
  Subgroup.mem_center_iff.mp piOrth_mem_center g

theorem omegaToProj_eq_iff (hQ : Q.Nondegenerate) {a b : omegaGroup hQ}
    (hab : omegaToProj hQ a = omegaToProj hQ b) :
    (b : OGroup Q) = a ∨ (b : OGroup Q) = piOrth Q * a := by
  have h1 : omegaToProj hQ (a⁻¹ * b) = 1 := by rw [map_mul, map_inv, hab, inv_mul_cancel]
  rcases (omegaToProj_eq_one_iff hQ _).mp h1 with h | h
  · left
    have h' : (a : OGroup Q)⁻¹ * b = 1 := h
    exact (inv_mul_eq_one.mp h').symm
  · right
    have h' : (a : OGroup Q)⁻¹ * b = piOrth Q := h
    have hb : (b : OGroup Q) = a * piOrth Q := by rw [← h', mul_inv_cancel_left]
    rw [hb]
    exact mul_piOrth_comm (a : OGroup Q)

theorem omegaToProj_ker_central (hQ : Q.Nondegenerate) {m : omegaGroup hQ}
    (hm : omegaToProj hQ m = 1) (g : omegaGroup hQ) : g * m = m * g := by
  apply Subtype.ext
  simp only [Subgroup.coe_mul]
  rcases (omegaToProj_eq_one_iff hQ m).mp hm with h | h
  · rw [h, one_mul, mul_one]
  · rw [h]
    exact mul_piOrth_comm (g : OGroup Q)

end CFSG.OddStandard.SmallF3.Omega
