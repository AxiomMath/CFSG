module

public import CFSG.LargeExtraspecial.S9SevenH

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S9

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6 CFSG.LargeExtraspecial.OrthoF2

universe u

variable {G : Type u} [Group G] [Finite G]

@[expose] def IsTI97 (S : Setting G) (g : G) (k : S.M) (O : Subgroup S.O) : Prop :=
  ∀ x ∈ S.Lbar g ⊔ S.Lbar ((k : G) * g),
    (S.Lbar g ⊔ O).map (MulAut.conj x).toMonoidHom = S.Lbar g ⊔ O ∨
      (S.Lbar g ⊔ O).map (MulAut.conj x).toMonoidHom ⊓ (S.Lbar g ⊔ O) ≤ O

@[expose] def Concl97 (S : Setting G) (g : G) (k : S.M) (O : Subgroup S.O) : Prop :=
  (∃ φ : ↥(S.Lbar g ⊔ S.Lbar ((k : G) * g)) →* Equiv.Perm (Fin 3),
      Function.Surjective φ ∧ φ.ker = O.subgroupOf (S.Lbar g ⊔ S.Lbar ((k : G) * g))) ∨
    ∃ φ : ↥(S.Lbar g ⊔ S.Lbar ((k : G) * g)) →* alternatingGroup (Fin 5),
      Function.Surjective φ ∧ φ.ker = O.subgroupOf (S.Lbar g ⊔ S.Lbar ((k : G) * g))

namespace Hyp97

variable {S : Setting G} {g : G} {k : S.M} {O : Subgroup S.O} (X : Hyp97 S g k O)
include X

theorem four_mul_card_le (hLO : ¬ S.Lbar g ≤ O)
    (hidx : Nat.card (S.Lbar g) ≠ 2 * Nat.card (S.Lbar g ⊓ O : Subgroup S.O)) :
    4 * Nat.card (S.Lbar g ⊓ O : Subgroup S.O) ≤ Nat.card (S.Lbar g) := by
  set K := (S.Lbar g ⊓ O).subgroupOf (S.Lbar g) with hK
  have hKc : Nat.card K = Nat.card (S.Lbar g ⊓ O : Subgroup S.O) :=
    Nat.card_congr (subgroupOfEquivOfLe inf_le_left).toEquiv
  have hmul := K.card_mul_index
  rw [hKc] at hmul
  have hdvd : K.index ∣ 2 ^ (S.width - 1) := by
    rw [← X.cons.card_Lbar]
    exact K.index_dvd_card
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  have hj0 : j ≠ 0 := by
    rintro rfl
    apply hLO
    intro l hl
    have htop : K = ⊤ := Subgroup.index_eq_one.mp (by rw [hj, pow_zero])
    have : (⟨l, hl⟩ : S.Lbar g) ∈ K := htop ▸ mem_top _
    rw [hK, mem_subgroupOf] at this
    exact (mem_inf.mp this).2
  have hj1 : j ≠ 1 := by
    rintro rfl
    apply hidx
    rw [← hmul, hj, pow_one, mul_comm]
  have h4 : 4 ∣ K.index := by
    rw [hj]
    exact (Nat.pow_dvd_pow 2 (by omega : 2 ≤ j))
  obtain ⟨c, hc⟩ := h4
  have hpos : 0 < Nat.card (S.Lbar g ⊓ O : Subgroup S.O) := Nat.card_pos
  have hcpos : 0 < c := by
    rcases Nat.eq_zero_or_pos c with h | h
    · rw [h, mul_zero] at hc
      exact absurd hc K.index_ne_zero_of_finite
    · exact h
  rw [← hmul, hc]
  nlinarith

end Hyp97

@[expose] def Timmesfeld97Residual (S : Setting G) (g : G) (k : S.M) (O : Subgroup S.O) : Prop :=
  Hyp97 S g k O → IsTI97 S g k O → ¬ S.Lbar g ≤ O →
    Nat.card (S.Lbar g) ≠ 2 * Nat.card (S.Lbar g ⊓ O : Subgroup S.O) → Concl97 S g k O

theorem timmesfeld_9_7 {S : Setting G} {g : G} {k : S.M} {O : Subgroup S.O}
    (hRes : Timmesfeld97Residual S g k O) (X : Hyp97 S g k O) (hTI : IsTI97 S g k O)
    (hLO : ¬ S.Lbar g ≤ O) : Concl97 S g k O := by
  by_cases hidx : Nat.card (S.Lbar g) = 2 * Nat.card (S.Lbar g ⊓ O : Subgroup S.O)
  · exact Or.inl (X.exists_hom_perm_three hidx hLO)
  · exact hRes X hTI hLO hidx

end CFSG.LargeExtraspecial.S9
