module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk73G4Comp
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk73G4Main
public import CFSG.GH74.GLS.IVK.Proofs2.GHInvExcShape

public section

namespace CFSG.GH74.GLS.IVK

open Subgroup CFSG CFSG.ABGLocalTools Blueprint CFSG.GH74.GLS.IVK.Proofs2.Ivk47ab
open CFSG.ComponentClassification.OuterAutomorphisms (inner Outer)


theorem chevalleyExceptionalModel_of_lieModel_G2 {X : Type} [Group X] {p f : ℕ}
    (h : LieModel X .G2 0 p f) : ChevalleyExceptionalModel X .G2 p f :=
  CFSG.Blueprint.LieModel.chevalleyExceptionalModel h (by decide)

theorem chevalleyExceptionalModel_of_lieModel_D4 {X : Type} [Group X] {p f : ℕ}
    (h : LieModel X .trialityD4 0 p f) : ChevalleyExceptionalModel X .trialityD4 p f :=
  CFSG.Blueprint.LieModel.chevalleyExceptionalModel h (by decide)

theorem exists_card_eq_two_pow_of_sq_eq_one {X : Type*} [Group X] [Finite X] (E : Subgroup X)
    (hE : ∀ e ∈ E, e * e = 1) : ∃ d : ℕ, Nat.card E = 2 ^ d := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp : IsPGroup 2 E := fun g => ⟨1, by
    rw [pow_one, pow_two]
    exact Subtype.ext (hE g g.2)⟩
  exact (IsPGroup.iff_card).1 hp

theorem ivk73_g2 :
    ∀ p f : ℕ, p.Prime → p ≠ 2 → 1 ≤ f → Ivk73Empty (fun X _ => LieModel X .G2 0 p f) := by
  intro p f hp hp2 hf N _ _ L K Q h hM
  have hOut : ∀ E : Subgroup (Outer ↥L), (∀ e ∈ E, e * e = 1) → Nat.card E ≤ 2 ^ 1 := by
    intro E hE
    obtain ⟨d, hd⟩ := exists_card_eq_two_pow_of_sq_eq_one E hE
    have hsq : ∀ x ∈ E, x ^ 2 = 1 := fun x hx => by rw [pow_two]; exact hE x hx
    have h1 := ((LieType.Chevalley.odd_exceptional_elementary_outer_two_rank ↥L .G2 p f
      (chevalleyExceptionalModel_of_lieModel_G2 hM) (hp.odd_of_ne_two hp2) E hsq d hd).1) (Or.inl rfl)
    rw [hd]
    exact Nat.pow_le_pow_right (by norm_num) h1
  refine h.false_of_comp_mem hOut fun y hy2 hy1 B hB => ?_
  exact GHInv.mem_of_isCompIn_G2 hp hp2 hM hf y (orderOf_eq_prime (by rw [pow_two]; exact hy2) hy1) hB

theorem ivk73_d4 :
    ∀ p f : ℕ, p.Prime → p ≠ 2 → 1 ≤ f → Ivk73Empty (fun X _ => LieModel X .trialityD4 0 p f) := by
  intro p f hp hp2 hf N _ _ L K Q h hM
  have hOut : ∀ E : Subgroup (Outer ↥L), (∀ e ∈ E, e * e = 1) → Nat.card E ≤ 2 ^ 1 := by
    intro E hE
    obtain ⟨d, hd⟩ := exists_card_eq_two_pow_of_sq_eq_one E hE
    have hsq : ∀ x ∈ E, x ^ 2 = 1 := fun x hx => by rw [pow_two]; exact hE x hx
    have h1 := ((LieType.Chevalley.odd_exceptional_elementary_outer_two_rank ↥L .trialityD4 p f
      (chevalleyExceptionalModel_of_lieModel_D4 hM) (hp.odd_of_ne_two hp2) E hsq d hd).1)
      (Or.inr (Or.inr (Or.inr (Or.inr rfl))))
    rw [hd]
    exact Nat.pow_le_pow_right (by norm_num) h1
  refine h.false_of_comp_mem hOut fun y hy2 hy1 B hB => ?_
  exact GHInv.mem_of_isCompIn_D4 hp hp2 hM hf y (orderOf_eq_prime (by rw [pow_two]; exact hy2) hy1) hB

end CFSG.GH74.GLS.IVK
