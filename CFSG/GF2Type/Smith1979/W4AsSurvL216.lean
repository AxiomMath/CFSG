module

public import CFSG.GF2Type.Smith1979.W4AsE11Layer

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1979.W4As

open Subgroup Module

namespace Surv

theorem card_orthogonalGroup_plus_eight {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V] {Q : QuadraticForm (ZMod 2) V}
    (hQ : Q.polarBilin.Nondegenerate) (hdim : finrank (ZMod 2) V = 8)
    (hW : ∃ W : Submodule (ZMod 2) V, finrank (ZMod 2) W = 4 ∧ ∀ v ∈ W, Q v = 0) :
    Nat.card (TauCeti.QuadraticMap.orthogonalGroup Q) = 2 ^ 13 * 3 ^ 5 * 5 ^ 2 * 7 := by
  obtain ⟨W, hW4, hW0⟩ := hW
  have hplus : CFSG.GroupTheory.WeirSylow.IsPlusType Q := ⟨W, by omega, hW0⟩
  have h := CFSG.GroupTheory.WeirSylow.natCard_orthogonalGroup_of_type hQ (m := 3)
    (by omega) (ε := 1) (Or.inl ⟨rfl, hplus⟩)
  rw [Nat.card_zmod] at h
  have h' : ((Nat.card (TauCeti.QuadraticMap.orthogonalGroup Q) : ℕ) : ℤ) =
      2 ^ 13 * 3 ^ 5 * 5 ^ 2 * 7 := by
    rw [h]
    decide
  exact_mod_cast h'

end Surv

theorem l216NoPlusEmbedding_holds : L216NoPlusEmbedding := by
  intro K _ _ ⟨e⟩ V _ _ _ Q hQ hdim hW ρ hρQ hρ
  have h17 : 17 ∣ Nat.card K := by
    have h1 : Nat.card (K ⧸ center K) = 2 ^ 4 * ((2 ^ 4) ^ 2 - 1) := by
      rw [Nat.card_congr e.toEquiv]
      exact CFSG.Walter.psl2_even_card (by norm_num)
    have h2 : 17 ∣ Nat.card (K ⧸ center K) := by
      rw [h1]
      norm_num
    exact h2.trans (Subgroup.card_quotient_dvd_card _)
  let ρ' : K →* TauCeti.QuadraticMap.orthogonalGroup Q :=
    ρ.codRestrict (TauCeti.QuadraticMap.orthogonalGroup Q) fun k =>
      TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr (hρQ k)
  have hρ' : Function.Injective ρ' := fun a b h => hρ (congrArg Subtype.val h)
  have hdvd := Subgroup.card_dvd_of_injective ρ' hρ'
  rw [Surv.card_orthogonalGroup_plus_eight hQ hdim hW] at hdvd
  have h := h17.trans hdvd
  norm_num at h

end CFSG.GF2Type.Smith1979.W4As
