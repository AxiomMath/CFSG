module

public import CFSG.HardMathSupport.Solomon.Coordinator.I27_1Fam
public import CFSG.HardMathSupport.Solomon.Coordinator.GFR2FamSpor
public import CFSG.HardMathSupport.Timmesfeld.Coordinator.LocalThreeSporadicRank
public import CFSG.Monster.B.TwoA.Base.ElemAut

public section

namespace CFSG.HardMathSupport.Solomon.Proving

open CFSG.ComponentClassification.OuterAutomorphisms

theorem fi22_conj_injective {Y : Type} [Group Y] (hc : Subgroup.center Y = ⊥) :
    Function.Injective (MulAut.conj : Y →* MulAut Y) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  have hmem : g ∈ Subgroup.center Y := by
    rw [Subgroup.mem_center_iff]
    intro x
    have := congrArg (fun φ : MulAut Y => φ x) hg
    simp only [MulAut.conj_apply, MulAut.one_apply] at this
    exact (mul_inv_eq_iff_eq_mul.mp this).symm
  rw [hc] at hmem
  exact Subgroup.mem_bot.mp hmem

theorem fi22_card_mulAut {Y : Type} [Group Y] [Finite Y] (hc : Subgroup.center Y = ⊥) :
    Nat.card (MulAut Y) = Nat.card Y * Nat.card (Outer Y) := by
  have hinj := fi22_conj_injective hc
  have h1 : Nat.card (inner Y) = Nat.card Y := by
    have : inner Y = (MulAut.conj : Y →* MulAut Y).range := rfl
    rw [this]
    exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
  have h2 := Subgroup.card_eq_card_quotient_mul_card_subgroup (inner Y)
  rw [h1] at h2
  rw [h2, mul_comm]

theorem fi22_center_eq_bot {Y : Type} [Group Y] [IsSimpleGroup Y]
    (hnab : ∃ a b : Y, a * b ≠ b * a) : Subgroup.center Y = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center Y) with h | h
  · exact h
  · exfalso
    obtain ⟨a, b, hab⟩ := hnab
    apply hab
    have hc : a ∈ Subgroup.center Y := by
      rw [h]
      exact Subgroup.mem_top a
    exact ((Subgroup.mem_center_iff.mp hc) b).symm

theorem fi22_exists_noncomm {Y : Type} [Group Y] [IsSimpleGroup Y]
    (hnp : ¬ (Nat.card Y).Prime) : ∃ a b : Y, a * b ≠ b * a := by
  by_contra h
  push Not at h
  let : CommGroup Y := { ‹Group Y› with mul_comm := h }
  exact hnp ((CommGroup.is_simple_iff_prime_card).mp inferInstance)

theorem i271Fi22Aut_of_tables
    (hOut : CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicOuterLeTwo)
    (hOrd : CFSG.HardMathSupport.Solomon.Coordinator.SporadicOrdersTable)
    (hsimp : IsSimpleGroup (TauCeti.CFSGIndex.sporadic TauCeti.SporadicName.Fi22).Group) :
    CFSG.HardMathSupport.Solomon.Coordinator.I271Fi22Aut := by
  intro Y _ _ hY
  obtain ⟨e⟩ : Nonempty (Y ≃* (TauCeti.CFSGIndex.sporadic TauCeti.SporadicName.Fi22).Group) := hY
  have hsimpY : IsSimpleGroup Y := by
    have := hsimp
    exact MulEquiv.isSimpleGroup e
  have := hsimpY
  have hcardY : Nat.card Y = 64561751654400 := by
    have hF := hOrd TauCeti.SporadicName.Fi22
    rw [Nat.card_congr e.toEquiv]
    exact hF.trans rfl
  have hnab : ∃ a b : Y, a * b ≠ b * a := by
    apply fi22_exists_noncomm
    rw [hcardY]
    norm_num
  have hcenter : Subgroup.center Y = ⊥ := fi22_center_eq_bot hnab
  have hout : Nat.card (Outer Y) ≤ 2 :=
    hOut Y hsimpY hnab TauCeti.SporadicName.Fi22 ⟨e⟩
  have hmul : Nat.card (MulAut Y) = Nat.card Y * Nat.card (Outer Y) :=
    fi22_card_mulAut hcenter
  have hcpos : 0 < Nat.card (Outer Y) := Nat.card_pos
  have hc12 : Nat.card (Outer Y) = 1 ∨ Nat.card (Outer Y) = 2 := by omega
  have hc5 : Nat.Coprime 5 (Nat.card (Outer Y)) := by
    rcases hc12 with h | h <;> rw [h] <;> norm_num
  have hdiv : Nat.card (MulAut Y) = 25 * (2582470066176 * Nat.card (Outer Y)) := by
    rw [hmul, hcardY]
    ring
  have hcop : Nat.Coprime 5 (2582470066176 * Nat.card (Outer Y)) :=
    Nat.Coprime.mul_right (by norm_num) hc5
  unfold CFSG.Open.pRank
  refine csSup_le' ?_
  rintro k ⟨E, -, -, hE⟩
  have hd : 5 ^ k ∣ Nat.card (MulAut Y) := by
    rw [← hE]
    exact Subgroup.card_subgroup_dvd_card E
  rw [hdiv] at hd
  have h25 : 5 ^ k ∣ 25 := Nat.Coprime.dvd_of_dvd_mul_right (Nat.Coprime.pow_left k hcop) hd
  rw [show (25 : ℕ) = 5 ^ 2 by norm_num] at h25
  exact (Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp h25

end CFSG.HardMathSupport.Solomon.Proving
