module

public import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotSwapLiftBasic

public section

namespace CFSG.GroupTheory

open CFSG.LieType.Steinberg
open CFSG.SeitzReduction.UnitaryPilot (OddCentralSplit)

theorem exists_lift_of_oddCentralSplit {S Y Q : Type} [Group S] [Group Y] [Group Q]
    [Finite S] [Finite Y] (hS : OddCentralSplit S) {π : Y →* Q} (hπ : Function.Surjective π)
    (hcen : π.ker ≤ Subgroup.center Y) (hodd : Odd (Nat.card π.ker)) (Φ : S →* Q) :
    ∃ Ψ : S →* Y, π.comp Ψ = Φ := by
  have hodd' : Odd (Nat.card (pullbackFst Φ π).ker) := by
    let f : (pullbackFst Φ π).ker →* π.ker :=
      { toFun := fun y =>
          ⟨((y : pullback Φ π) : S × Y).2,
            (snd_mem_ker_of_mem_ker_pullbackFst y.2).2⟩
        map_one' := rfl
        map_mul' := fun _ _ => rfl }
    have hf : Function.Injective f := fun y z hyz => by
      have h2 : ((y : pullback Φ π) : S × Y).2 = ((z : pullback Φ π) : S × Y).2 :=
        congrArg Subtype.val hyz
      have h1y := (snd_mem_ker_of_mem_ker_pullbackFst y.2).1
      have h1z := (snd_mem_ker_of_mem_ker_pullbackFst z.2).1
      exact Subtype.ext (Subtype.ext (Prod.ext (h1y.trans h1z.symm) h2))
    exact hodd.of_dvd_nat (Subgroup.card_dvd_of_injective f hf)
  obtain ⟨s, hs⟩ := hS _ (pullbackFst Φ π) (pullbackFst_surjective hπ)
    (ker_pullbackFst_le_center hcen) hodd'
  refine ⟨(MonoidHom.snd S Y).comp ((pullback Φ π).subtype.comp s), ?_⟩
  ext x
  have h1 : ((s x : pullback Φ π) : S × Y).1 = x := hs x
  have h2' := mem_pullback.1 (s x).2
  rw [h1] at h2'
  exact h2'.symm

end CFSG.GroupTheory
