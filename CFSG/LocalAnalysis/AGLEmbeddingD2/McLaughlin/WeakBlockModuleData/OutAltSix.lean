module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierAlternatingSix
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.AutAlternating

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData

open Equiv
open scoped commutatorElement
open CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.ComponentClassification.CatalogueSchreierAlternating.DegreeSix

variable {Q : Type*} [Group Q]

theorem exists_conj_eq_of_pow_eq_one_alt_six {k : ℕ} (ψ : MulAut (alternatingGroup (Fin 6)))
    (h : ψ ^ (3 ^ k) = 1) : ∃ a : alternatingGroup (Fin 6), MulAut.conj a = ψ := by
  have : Finite (MulAut (alternatingGroup (Fin 6))) :=
    Finite.of_injective _ (CFSG.ComponentClassification.CatalogueSchreierAlternating.imagePairEvaluation_injective
      x y generating_pair)
  have hq : Nat.card (MulAut (alternatingGroup (Fin 6))) =
      Nat.card (Outer (alternatingGroup (Fin 6))) * 360 := by
    have := (inner (alternatingGroup (Fin 6))).card_eq_card_quotient_mul_card_subgroup
    rw [inner_card] at this
    exact this
  have hle := outer_card_le_four
  have hdvd : Nat.card (Perm (Fin 6)) ∣ Nat.card (MulAut (alternatingGroup (Fin 6))) :=
    Subgroup.card_dvd_of_injective _
      (CFSG.GroupTheory.AutAlternating.conjNormal_injective_alternatingGroup 6 (by norm_num))
  rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin, hq] at hdvd
  have hpos : 0 < Nat.card (Outer (alternatingGroup (Fin 6))) := Nat.card_pos
  have h24 : Nat.card (Outer (alternatingGroup (Fin 6))) = 2 ∨
      Nat.card (Outer (alternatingGroup (Fin 6))) = 4 := by
    norm_num [Nat.factorial] at hdvd
    omega
  have hcop : Nat.Coprime (3 ^ k) (Nat.card (Outer (alternatingGroup (Fin 6)))) := by
    apply Nat.Coprime.pow_left
    rcases h24 with h24 | h24 <;> rw [h24] <;> decide
  have h1 : ((ψ : MulAut (alternatingGroup (Fin 6))) : Outer (alternatingGroup (Fin 6))) = 1 := by
    have e1 : ((ψ : Outer (alternatingGroup (Fin 6)))) ^ (3 ^ k) = 1 := by
      rw [← QuotientGroup.mk_pow, h]; rfl
    have e2 : ((ψ : Outer (alternatingGroup (Fin 6)))) ^
        (Nat.card (Outer (alternatingGroup (Fin 6)))) = 1 := pow_card_eq_one'
    have h3 := Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one e1) (orderOf_dvd_of_pow_eq_one e2)
    rw [hcop] at h3
    exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp h3)
  obtain ⟨a, ha⟩ := (QuotientGroup.eq_one_iff ψ).mp h1
  exact ⟨a, ha⟩

end CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData
