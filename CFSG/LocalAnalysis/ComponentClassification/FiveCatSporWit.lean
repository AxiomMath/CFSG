module

public import CFSG.Sporadic.SmallOddCore.CentSpec
public import CFSG.Sporadic.HeldB.FixedTransport
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.ComponentClassification.SolMax.FiveCat.Spor

open Subgroup CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier
open CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

variable {n : ℕ}

noncomputable def fixedSubgroupEquivInf {M : Type*} [Group M] (P : Subgroup M) (β : MulAut ↥P)
    (x : M) (hx : ∀ p : ↥P, ((β p : ↥P) : M) = x * p * x⁻¹) :
    ↥(fixedSubgroup β) ≃* ↥(P ⊓ centralizer ({x} : Set M)) :=
  have hkey : ∀ p : ↥P, β p = p ↔ (p : M) * x = x * (p : M) := by
    intro p
    have h1 := hx p
    constructor
    · intro h
      have h2 : (p : M) = x * p * x⁻¹ := by rw [← h1, h]
      calc (p : M) * x = (x * p * x⁻¹) * x := by rw [← h2]
        _ = x * p := by group
    · intro h
      apply Subtype.ext
      rw [h1, ← h]
      group
  { toFun := fun p => ⟨(p.1 : M), mem_inf.2 ⟨p.1.2,
      mem_centralizer_singleton_iff.2 ((hkey p.1).1 p.2)⟩⟩
    invFun := fun q => ⟨⟨q.1, (mem_inf.1 q.2).1⟩, (hkey _).2
      (mem_centralizer_singleton_iff.1 (mem_inf.1 q.2).2)⟩
    left_inv := fun p => rfl
    right_inv := fun q => rfl
    map_mul' := fun a b => rfl }

theorem exists_fixed_equiv {P R : Subgroup (Equiv.Perm (Fin n))} (eR : ↥R ≃* MulAut ↥P)
    (heR : ∀ (x : ↥R) (p : ↥P), ((eR x p : ↥P) : Equiv.Perm (Fin n)) =
      (x : Equiv.Perm (Fin n)) * p * (x : Equiv.Perm (Fin n))⁻¹)
    {rows : List ClassRow}
    (hcover : ∀ t ∈ R, orderOf t = 2 → ∃ r ∈ rows, ∃ g ∈ P, t = g * tp n r.rep * g⁻¹)
    {S : Type} [Group S] (θ : S ≃* ↥P) {σ : MulAut S} (hσ2 : σ * σ = 1) (hσ1 : σ ≠ 1) :
    ∃ r ∈ rows, Nonempty (↥(fixedSubgroup σ) ≃*
      ↥(P ⊓ centralizer ({tp n r.rep} : Set (Equiv.Perm (Fin n))))) := by
  set β : MulAut ↥P := MulAut.congr θ σ with hβ
  have hβ2 : β * β = 1 := by rw [hβ, ← map_mul, hσ2, map_one]
  have hβ1 : β ≠ 1 := fun h => hσ1 ((MulAut.congr θ).injective (by rw [← hβ, h, map_one]))
  obtain ⟨x, hx⟩ := eR.surjective β
  have hxx : x * x = 1 := eR.injective (by rw [map_mul, hx, hβ2, map_one])
  have hx1 : x ≠ 1 := fun h => hβ1 (by rw [← hx, h, map_one])
  have hord : orderOf (x : Equiv.Perm (Fin n)) = 2 := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    refine orderOf_eq_prime ?_ ?_
    · have h := congrArg Subtype.val hxx
      simpa [pow_two] using h
    · intro h
      exact hx1 (Subtype.ext h)
  obtain ⟨r, hr, g, hg, hxg⟩ := hcover x x.2 hord
  have hxform : ∀ p : ↥P, ((β p : ↥P) : Equiv.Perm (Fin n)) =
      (x : Equiv.Perm (Fin n)) * p * (x : Equiv.Perm (Fin n))⁻¹ := by
    intro p
    rw [← hx]
    exact heR x p
  refine ⟨r, hr, ⟨?_⟩⟩
  exact ((Sporadic.HeldB.fixedSubgroupCongr θ σ).trans (fixedSubgroupEquivInf P β x hxform)).trans
    ((MulEquiv.subgroupCongr (by rw [hxg])).trans
      (Sporadic.HeldB.infCentralizerConjEquiv hg (tp n r.rep)))

end CFSG.ComponentClassification.SolMax.FiveCat.Spor
