module

public import CFSG.Adapters.TauCetiExceptional.ReeVanish

public noncomputable section

namespace CFSG.TauCetiBridge.Ree

open TauCeti TauCeti.G2ShortRoot.PrimeField

variable (a : ℕ) (hv : (LieTypeIndex.reeG2 a).Valid)

noncomputable instance algebraZModThreeOf :
    Algebra (ZMod 3) (ReeG2LieIndex.of a hv).1.Closure :=
  ReeG2LieIndex.algebraZModThree (ReeG2LieIndex.of a hv)

theorem steinberg_rootSubgroupPoints (k : Fin 2 ⊕ Fin 2)
    (u : (ReeG2LieIndex.of a hv).1.Closure) :
    (ReeG2LieIndex.of a hv).steinberg (rootSubgroupPoints k _ (Multiplicative.ofAdd u)) =
      rootSubgroupPoints (specialIsogenyRootIndex k) _
        (Multiplicative.ofAdd (u ^ (3 ^ a * specialIsogenyExponent k))) := by
  let d := ReeG2LieIndex.of a hv
  have hyy : ∀ t, d.halfFrobenius (d.halfFrobenius (rootSubgroupPoints
      (specialIsogenyRootIndex k) d.1.Closure (Multiplicative.ofAdd t))) =
        rootSubgroupPoints (specialIsogenyRootIndex k) d.1.Closure
          (Multiplicative.ofAdd (t ^ d.1.characteristic)) := fun t => by
    refine (d.halfFrobenius_halfFrobenius _).trans ?_
    rw [ReeG2LieIndex.primeFrobenius_def, frobenius_rootSubgroupPoints, toAdd_ofAdd, pow_one]
    exact congrArg (fun n => rootSubgroupPoints (specialIsogenyRootIndex k) d.1.Closure
      (Multiplicative.ofAdd (t ^ n))) d.characteristic_eq_three.symm
  have h := d.toSuzukiReeIndex.pow_fieldExponent_apply_pow (τ := d.halfFrobenius)
    (x := fun t => rootSubgroupPoints k d.1.Closure (Multiplicative.ofAdd t))
    (y := fun t => rootSubgroupPoints (specialIsogenyRootIndex k) d.1.Closure
      (Multiplicative.ofAdd t))
    (c := specialIsogenyExponent k)
    (fun t => by
      rw [ReeG2LieIndex.halfFrobenius_def]
      exact specialIsogeny_rootSubgroupPoints k t) hyy u
  rw [ReeG2LieIndex.steinberg_def]
  refine h.trans ?_
  have he : d.1.characteristic ^ d.toSuzukiReeIndex.halfExponent = 3 ^ a := by
    rw [d.characteristic_eq_three]
    exact congrArg (3 ^ ·) (SuzukiReeIndex.halfExponent_reeG2 a hv)
  exact congrArg (fun n => rootSubgroupPoints (specialIsogenyRootIndex k) d.1.Closure
    (Multiplicative.ofAdd (u ^ (n * specialIsogenyExponent k)))) he

theorem steinberg_steinberg_eq_frobenius (g : (ReeG2LieIndex.of a hv).AmbientGroup) :
    (ReeG2LieIndex.of a hv).steinberg ((ReeG2LieIndex.of a hv).steinberg g) =
      G2ShortRoot.PrimeField.frobenius (2 * a + 1) _ g := by
  rw [ReeG2LieIndex.steinberg_steinberg, ReeG2LieIndex.frobenius_def]
  exact congrArg (fun n => G2ShortRoot.PrimeField.frobenius n _ g)
    (LieTypeIndex.fieldExponent_reeG2 a)

end CFSG.TauCetiBridge.Ree
