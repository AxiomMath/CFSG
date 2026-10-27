module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3Defs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3L34Q8Lin
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.TypesOmega

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

@[expose] def Asc82PocketCover : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
    (Q : QuadraticForm (ZMod 3) V) (hQ : Q.Nondegenerate) (z : omegaGroup hQ), z * z = 1 →
      invType (z : OGroup Q) = (4, 1) → IsI4PlusIn (⊤ : Subgroup (omegaGroup hQ)) z

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

theorem isI4PlusIn_top_of_quaternion_omega (hP : Asc82PocketCover) (hQ : Q.Nondegenerate)
    (hn : Module.finrank (ZMod 3) V ≤ 7 ∨
      (Module.finrank (ZMod 3) V = 8 ∧ quadSign Q = -1))
    {f : QuaternionGroup 2 →* omegaGroup hQ} (hf : Function.Injective f) :
    IsI4PlusIn (⊤ : Subgroup (omegaGroup hQ)) (f (QuaternionGroup.a 2)) := by
  classical
  let g : QuaternionGroup 2 →* OGroup Q := (omegaGroup hQ).subtype.comp f
  let q : OGroup Q := g (QuaternionGroup.a 1)
  let r : OGroup Q := g (QuaternionGroup.xa 0)
  let y0 : OGroup Q := g (QuaternionGroup.a 2)
  have ha1 : (QuaternionGroup.a 1 : QuaternionGroup 2) * QuaternionGroup.a 1 =
      QuaternionGroup.a 2 := by decide +kernel
  have hxa0 : (QuaternionGroup.xa 0 : QuaternionGroup 2) * QuaternionGroup.xa 0 =
      QuaternionGroup.a 2 := by decide +kernel
  have ha2 : (QuaternionGroup.a 2 : QuaternionGroup 2) * QuaternionGroup.a 2 = 1 := by
    decide +kernel
  have hxa1 : (QuaternionGroup.xa 0 : QuaternionGroup 2) * QuaternionGroup.a 1 =
      (QuaternionGroup.a 1)⁻¹ * QuaternionGroup.xa 0 := by decide +kernel
  have hq2 : q * q = y0 := by
    change g (QuaternionGroup.a 1) * g (QuaternionGroup.a 1) = g (QuaternionGroup.a 2)
    rw [← map_mul, ha1]
  have hr2 : r * r = y0 := by
    change g (QuaternionGroup.xa 0) * g (QuaternionGroup.xa 0) = g (QuaternionGroup.a 2)
    rw [← map_mul, hxa0]
  have hyy : y0 * y0 = 1 := by
    change g (QuaternionGroup.a 2) * g (QuaternionGroup.a 2) = 1
    rw [← map_mul, ha2, map_one]
  have hrq : r * q = q⁻¹ * r := by
    change g (QuaternionGroup.xa 0) * g (QuaternionGroup.a 1) =
      (g (QuaternionGroup.a 1))⁻¹ * g (QuaternionGroup.xa 0)
    rw [← map_mul, hxa1, map_mul, map_inv]
  have hq8 := four_dvd_invDim_of_quaternion hQ (q := q) (r := r)
    (by rw [hq2, hr2]) (by rw [hq2, hyy]) hrq
  rw [hq2] at hq8
  have hzz : f (QuaternionGroup.a 2) * f (QuaternionGroup.a 2) = 1 := by
    rw [← map_mul, ha2, map_one]
  have hz1 : f (QuaternionGroup.a 2) ≠ 1 := by
    intro h
    have h' : f (QuaternionGroup.a 2) = f 1 := by rw [map_one]; exact h
    exact (by decide +kernel : (QuaternionGroup.a 2 : QuaternionGroup 2) ≠ 1) (hf h')
  have hy1 : y0 ≠ 1 := fun h => hz1 (Subtype.ext h)
  have hpos : invDim y0 ≠ 0 := fun h => hy1 ((invDim_eq_zero_iff hyy).mp h)
  have hle := invDim_le y0
  have h4 : invDim y0 = 4 := by
    obtain ⟨k, hk⟩ := hq8.1
    rcases hn with hn | ⟨hn8, hs⟩
    · omega
    · have hk' : k = 1 ∨ k = 2 := by omega
      rcases hk' with hk1 | hk2
      · omega
      · exfalso
        have hdim8 : invDim y0 = Module.finrank (ZMod 3) V := by omega
        have hpi : y0 = piOrth Q := (invDim_eq_finrank_iff hyy).mp hdim8
        have hsign : invSign y0 = quadSign Q := by
          rw [hpi]
          exact congrArg Prod.snd (invType_piOrth hQ)
        have h1 := hq8.2
        rw [hsign, hs] at h1
        exact absurd h1 (by decide)
  exact hP V Q hQ (f (QuaternionGroup.a 2)) hzz (Prod.ext h4 hq8.2)

end CFSG.OddStandard.SmallF3.Omega
