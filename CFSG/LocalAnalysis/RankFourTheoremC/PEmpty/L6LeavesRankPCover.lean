module

public import Mathlib.GroupTheory.Nilpotent

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.RankP

open Subgroup

theorem exists_sylow_le_of_cover {X : Type*} [Group X] [Finite X] (p : ℕ) [Fact p.Prime]
    {O N : Subgroup X} [O.Normal] (hOp : ¬ p ∣ Nat.card O)
    (hcov : ∀ g : X, ∃ n ∈ N, ∃ o ∈ O, g = n * o) :
    ∃ P' : Sylow p X, (P' : Subgroup X) ≤ N := by
  obtain ⟨P₀⟩ := Sylow.nonempty (G := N) (p := p)
  let ψ : N →* X ⧸ O := (QuotientGroup.mk' O).comp N.subtype
  have hψ : Function.Surjective ψ := by
    intro x
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨n, hn, o, ho, rfl⟩ := hcov g
    refine ⟨⟨n, hn⟩, ?_⟩
    have h1 : (QuotientGroup.mk' O) o = 1 := (QuotientGroup.eq_one_iff o).mpr ho
    show (QuotientGroup.mk' O) n = (QuotientGroup.mk' O) (n * o)
    rw [map_mul, h1, mul_one]
  have hcard1 : Nat.card ψ.ker * Nat.card (X ⧸ O) = Nat.card N :=
    Subgroup.card_ker_mul_card_of_surjective hψ
  have hcard2 : Nat.card (X ⧸ O) * Nat.card O = Nat.card X :=
    (Subgroup.card_eq_card_quotient_mul_card_subgroup O).symm
  have hker : ¬ p ∣ Nat.card ψ.ker := by
    intro hdvd
    apply hOp
    refine hdvd.trans ?_
    have hle : (ψ.ker).map N.subtype ≤ O := by
      rintro _ ⟨k, hk, rfl⟩
      exact (QuotientGroup.eq_one_iff (k : X)).mp hk
    calc Nat.card ψ.ker = Nat.card ((ψ.ker).map N.subtype) :=
          (Subgroup.card_map_of_injective N.subtype_injective).symm
      _ ∣ Nat.card O := Subgroup.card_dvd_of_le hle
  have hker0 : Nat.card ψ.ker ≠ 0 := Nat.card_pos.ne'
  have ha0 : Nat.card (X ⧸ O) ≠ 0 := Nat.card_pos.ne'
  have hO0 : Nat.card O ≠ 0 := Nat.card_pos.ne'
  have hv1 : (Nat.card N).factorization p = (Nat.card (X ⧸ O)).factorization p := by
    rw [← hcard1, Nat.factorization_mul hker0 ha0, Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd hker, zero_add]
  have hv2 : (Nat.card X).factorization p = (Nat.card (X ⧸ O)).factorization p := by
    rw [← hcard2, Nat.factorization_mul ha0 hO0, Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd hOp, add_zero]
  have hcardP : Nat.card (P₀.map N.subtype) = p ^ (Nat.card X).factorization p := by
    rw [Subgroup.card_map_of_injective N.subtype_injective, Sylow.card_eq_multiplicity, hv1, hv2]
  exact ⟨Sylow.ofCard _ hcardP, Subgroup.map_subtype_le _⟩

theorem exists_ne_one_mem_inf_center {P : Type*} [Group P] [Finite P] {p : ℕ} [Fact p.Prime]
    (hP : IsPGroup p P) (K : Subgroup P) [K.Normal] (hK : K ≠ ⊥) :
    ∃ w : P, w ∈ K ∧ w ∈ center P ∧ w ^ p = 1 ∧ w ≠ 1 := by
  haveI : Group.IsNilpotent P := hP.isNilpotent
  have h := Group.IsNilpotent.inf_center_ne_bot_of_normal hK
  obtain ⟨w₀, hw₀⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp h
  have hw₀K : (w₀ : P) ∈ K := (Subgroup.mem_inf.mp w₀.2).1
  have hw₀Z : (w₀ : P) ∈ center P := (Subgroup.mem_inf.mp w₀.2).2
  have hne : (w₀ : P) ≠ 1 := fun h => hw₀ (Subtype.ext h)
  obtain ⟨m, hm⟩ := (IsPGroup.iff_orderOf.mp hP) (w₀ : P)
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact hne (orderOf_eq_one_iff.mp (by simpa using hm))
  have hdvd : p ^ (m - 1) ∣ orderOf (w₀ : P) := by
    rw [hm]
    exact pow_dvd_pow p (Nat.sub_le m 1)
  have hord : orderOf ((w₀ : P) ^ p ^ (m - 1)) = p := by
    rw [orderOf_pow_of_dvd (pow_ne_zero _ (Fact.out : p.Prime).ne_zero) hdvd, hm,
      Nat.pow_div (Nat.sub_le m 1) (Fact.out : p.Prime).pos]
    have : m - (m - 1) = 1 := by omega
    rw [this, pow_one]
  refine ⟨(w₀ : P) ^ p ^ (m - 1), Subgroup.pow_mem _ hw₀K _, Subgroup.pow_mem _ hw₀Z _, ?_, ?_⟩
  · have := pow_orderOf_eq_one ((w₀ : P) ^ p ^ (m - 1))
    rwa [hord] at this
  · intro h
    rw [h, orderOf_one] at hord
    exact (Fact.out : p.Prime).one_lt.ne hord

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.RankP
