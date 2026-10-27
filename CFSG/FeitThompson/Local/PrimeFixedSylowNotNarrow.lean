module

public import Mathlib.GroupTheory.Complement
public import Mathlib.GroupTheory.Solvable
public import CFSG.FeitThompson.Definitions.NarrowPGroupsAndBetaPrimes
import CFSG.FeitThompson.Local.OddAutPrimesNarrowGroup
import CFSG.FeitThompson.Local.MixedFittingCentralizerConstrained

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Subgroup

variable {X : Type*} [Group X] [Finite X] {q : ℕ}

omit [Finite X] in
theorem mem_centralizer_of_conjNormal_eq_one {Q : Subgroup X} [Q.Normal] {x : X}
    (hx : MulAut.conjNormal (H := Q) x = 1) : x ∈ centralizer (Q : Set X) := by
  rw [mem_centralizer_iff]
  intro h hh
  have hxh : x * h * x⁻¹ = h := by
    have := congrArg (fun σ : MulAut ↥Q => ((σ ⟨h, hh⟩ : ↥Q) : X)) hx
    simpa only [MulAut.conjNormal_apply, MulAut.one_apply] using this
  calc h * x = x * h * x⁻¹ * x := by rw [hxh]
    _ = x * h := by group

omit [Finite X] in
theorem map_conjNormal_eq_range {Q A : Subgroup X} [Q.Normal] :
    A.map (MulAut.conjNormal (H := Q)) = (MulAut.conjNormal.comp A.subtype).range := by
  simp [MonoidHom.range_comp]

theorem commutator_le_centralizer_of_isPNarrow {Q A : Subgroup X} [Q.Normal] (hq : q.Prime)
    (hqodd : Odd q) (hQ : IsPGroup q ↥Q) (hnarrow : IsPNarrow q ↥Q)
    (hAodd : Odd (Nat.card ↥A)) (hqA : ¬ q ∣ Nat.card ↥A) :
    ⁅A, A⁆ ≤ centralizer (Q : Set X) := by
  have := Fact.mk hq
  set φ : X →* MulAut ↥Q := MulAut.conjNormal with hφ
  have hdvd : Nat.card ↥(A.map φ) ∣ Nat.card ↥A := by
    rw [map_conjNormal_eq_range, ← natCard_setRange_eq_natCard_range]
    exact natCard_setRange_dvd_natCard_domain _
  have hA' : Odd (Nat.card ↥(A.map φ)) := hAodd.of_dvd_nat hdvd
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.1
    (isPGroup_commutator_subgroup_of_odd_aut_of_isPNarrow hq hqodd hQ hnarrow hA')
  have hcard : Nat.card ↥(⁅A.map φ, A.map φ⁆ : Subgroup (MulAut ↥Q)) ∣ Nat.card ↥A :=
    (card_dvd_of_le (commutator_le_self _)).trans hdvd
  have hbot : (⁅A.map φ, A.map φ⁆ : Subgroup (MulAut ↥Q)) = ⊥ := by
    refine (eq_bot_iff_card _).2 ?_
    rcases Nat.eq_zero_or_pos n with rfl | hnpos
    · simpa using hn
    · exact absurd ((dvd_pow_self q hnpos.ne').trans (hn ▸ hcard)) hqA
  have hmap : (⁅A, A⁆ : Subgroup X).map φ = ⊥ := by rw [Subgroup.map_commutator, hbot]
  intro x hx
  refine mem_centralizer_of_conjNormal_eq_one (Q := Q) ?_
  have : φ x ∈ (⊥ : Subgroup (MulAut ↥Q)) := hmap ▸ mem_map_of_mem φ hx
  simpa [hφ] using this

theorem not_isPNarrow_of_centralizer_lt [Group.IsSolvable X] {Q D K Z Q0 : Subgroup X}
    (hq : q.Prime) (hXodd : Odd (Nat.card X))
    (hQnormal : Q.Normal) (_hQcompl : Q.IsComplement' (D ⊔ K))
    (hDnormal : (D.subgroupOf (D ⊔ K)).Normal) (_hDK : D ⊓ K = ⊥)
    (hQ : IsPGroup q ↥Q) (hcop : (Nat.card ↥Q).Coprime (Nat.card ↥(D ⊔ K)))
    (hcopDK : (Nat.card ↥D).Coprime (Nat.card ↥K)) (_hDne : D ≠ ⊥) (hK : K ≠ ⊥)
    (hfree : ∀ k ∈ K, k ≠ 1 → D ⊓ centralizer {k} = ⊥)
    (_hZ : ∀ k ∈ K, k ≠ 1 → Q ⊓ centralizer {k} = Z)
    (_hZK : Z = Q ⊓ centralizer (K : Set X)) (_hZcard : Nat.card ↥Z = q)
    (hQ0 : Q0 = Q ⊓ centralizer (D : Set X)) (hQ0lt : Q0 < Q) :
    ¬ IsPNarrow q ↥Q := by
  intro hnarrow
  have := Fact.mk hq
  have : Q.Normal := hQnormal
  have : (D.subgroupOf (D ⊔ K)).Normal := hDnormal
  have hQne : Q ≠ ⊥ := by
    rintro rfl
    exact absurd (le_bot_iff.1 (hQ0 ▸ inf_le_left)) (by simpa using hQ0lt.ne)
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 hQ
  have hqQ : q ∣ Nat.card ↥Q := by
    rcases Nat.eq_zero_or_pos n with rfl | hnpos
    · exact absurd ((eq_bot_iff_card Q).2 (by simpa using hn)) hQne
    · exact hn ▸ dvd_pow_self q hnpos.ne'
  have hqodd : Odd q := hXodd.of_dvd_nat (hqQ.trans (card_subgroup_dvd_card Q))
  have hAodd : Odd (Nat.card ↥(D ⊔ K)) := hXodd.of_dvd_nat (card_subgroup_dvd_card _)
  have hqA : ¬ q ∣ Nat.card ↥(D ⊔ K) := fun hd => hq.one_lt.ne' <|
    Nat.eq_one_of_dvd_one (hcop ▸ Nat.dvd_gcd hqQ hd)
  have hcomm : ⁅D ⊔ K, D ⊔ K⁆ ≤ centralizer (Q : Set X) :=
    commutator_le_centralizer_of_isPNarrow hq hqodd hQ hnarrow hAodd hqA
  obtain ⟨⟨k, hkK⟩, hk1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hK
  have hk1' : k ≠ 1 := by simpa using hk1
  have hCDK : D ⊓ centralizer (K : Set X) = ⊥ :=
    le_bot_iff.1 <| hfree k hkK hk1' ▸
      inf_le_inf_left D (centralizer_le (Set.singleton_subset_iff.2 hkK))
  have hKN : K ≤ normalizer (D : Set X) :=
    le_sup_right.trans (le_normalizer_of_normal_subgroupOf le_sup_left)
  have hD : D ≤ ⁅D, K⁆ :=
    le_commutator_of_coprime_of_inf_centralizer_eq_bot hKN hcopDK.symm hCDK
  have hDcent : D ≤ centralizer (Q : Set X) :=
    hD.trans ((commutator_mono le_sup_left le_sup_right).trans hcomm)
  refine absurd (le_antisymm inf_le_left ?_ : Q ⊓ centralizer (D : Set X) = Q) ?_
  · exact fun x hx => ⟨hx, mem_centralizer_iff.2 fun d hd =>
      (mem_centralizer_iff.1 (hDcent hd) x hx).symm⟩
  · exact fun h => absurd (hQ0.trans h) hQ0lt.ne

end

end CFSG.FeitThompson
