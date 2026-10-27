module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.HaradaModel.AParts

public section

namespace CFSG.EvenSporadicStandard.HNRecog.HaradaModel

open Subgroup CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier
  CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native
  CFSG.EvenSporadicStandard.HNRecog.HaradaLA

private theorem uWords_length : uWords.length = 6 := by decide

section Cert

theorem uElem_mul_self {i : ℕ} (hi : i < 6) : uElem i * uElem i = 1 := aFacts.u_sq i hi

theorem uElem_comm {i j : ℕ} (hi : i < 6) (hj : j < 6) : uElem i * uElem j = uElem j * uElem i :=
  aFacts.u_comm i hi j hj

private noncomputable def piPowHom {C : Type*} [CommGroup C] {r : ℕ} (c : Fin r → C)
    (hc : ∀ i, c i ^ 2 = 1) : Multiplicative (Fin r → ZMod 2) →* C where
  toFun a := ∏ i, c i ^ (Multiplicative.toAdd a i).val
  map_one' := by simp
  map_mul' a b := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [toAdd_mul, Pi.add_apply, ZMod.val_add, ← pow_eq_pow_mod _ (hc i), pow_add]

open scoped IsMulCommutative in
theorem exists_iotaP :
    ∃ ι : Multiplicative V6 →* ↥P1408, ∀ v : V6, ι (Multiplicative.ofAdd v) = iotaFun v := by
  let u : Fin 6 → ↥P1408 := fun i => uElem i
  have hcomm : ∀ i j, Commute (u i) (u j) := fun i j => uElem_comm i.isLt j.isLt
  let C := Subgroup.closure (Set.range u)
  have hCc : IsMulCommutative C := Subgroup.isMulCommutative_closure (by
    rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩ _
    exact hcomm i j)
  let c : Fin 6 → C := fun i => ⟨u i, Subgroup.subset_closure ⟨i, rfl⟩⟩
  have hc : ∀ i, c i ^ 2 = 1 := fun i => Subtype.ext (by
    rw [Subgroup.coe_pow, Subgroup.coe_one]
    show u i ^ 2 = (1 : ↥P1408)
    rw [pow_two]
    exact uElem_mul_self i.isLt)
  let ψ : Multiplicative (Fin 6 → ZMod 2) →* C := piPowHom c hc
  refine ⟨C.subtype.comp ψ, fun v => ?_⟩
  have hψ : ψ (Multiplicative.ofAdd v) =
      c 0 ^ (v 0).val * c 1 ^ (v 1).val * c 2 ^ (v 2).val * c 3 ^ (v 3).val *
        c 4 ^ (v 4).val * c 5 ^ (v 5).val := by
    show (∏ i : Fin 6, c i ^ (Multiplicative.toAdd (Multiplicative.ofAdd v) i).val) = _
    rw [Fin.prod_univ_six]
    rfl
  show ((ψ (Multiplicative.ofAdd v) : C) : ↥P1408) = iotaFun v
  rw [hψ]
  simp only [Subgroup.coe_mul, Subgroup.coe_pow]
  rfl

end Cert

end CFSG.EvenSporadicStandard.HNRecog.HaradaModel
