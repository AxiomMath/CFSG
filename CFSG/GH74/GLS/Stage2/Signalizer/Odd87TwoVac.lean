module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87TwoVacFix
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93M12Bender
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87AutInner

public section

open Subgroup CFSG CFSG.Blueprint CFSG.GH74.Uniqueness.Bender
  CFSG.ComponentClassification.OuterAutomorphisms CFSG.Open
open scoped commutatorElement

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

theorem false_of_autCfg {Y : Type} [Group Y] [Finite Y] {n i : ℕ}
    (hn : 3 ≤ n) (hB : BenderType Y n i 1)
    (hOut : Odd (Nat.card (Outer Y)) ∨ Nat.card (Outer Y) = 4)
    {α : MulAut Y} {p : ℕ} {X : Subgroup (MulAut Y)} (h : AutCfg Y α p X) : False := by
  classical
  have : Fact p.Prime := ⟨h.prime⟩
  have : Finite (MulAut Y) :=
    Finite.of_injective (fun f : MulAut Y => (f : Y → Y)) DFunLike.coe_injective
  have hinj : Function.Injective (MulAut.conj : Y →* MulAut Y) := by
    rw [injective_iff_map_eq_one]
    intro g hg
    have hg' : g ∈ Subgroup.center Y := by
      rw [Subgroup.mem_center_iff]
      intro y
      have := congrArg (fun σ : MulAut Y => σ y) hg
      simp only [MulAut.conj_apply, MulAut.one_apply] at this
      calc y * g = (g * y * g⁻¹) * g := by rw [this]
        _ = g * y := by group
    rw [hB.center_eq_bot, Subgroup.mem_bot] at hg'
    exact hg'
  obtain ⟨T, hT4, hTsq, hTfix⟩ := Odd87TwoVacFix.exists_fixed_four_group hn hB α h.alpha_sq
  have hXI : X ⊓ innSub Y = ⊥ :=
    autCfg_inf_inner_eq_bot hinj (fun k hk hk1 => hB.centralizer_involution_isPGroup hk hk1) h hT4
      hTsq hTfix
  rcases hOut with hodd | h4
  ·
    refine autCfg_false_of_inner h hXI ?_
    have h1 : (QuotientGroup.mk α : Outer Y) * QuotientGroup.mk α = 1 := by
      rw [← QuotientGroup.mk_mul, h.alpha_sq, QuotientGroup.mk_one]
    have h2 : orderOf (QuotientGroup.mk α : Outer Y) ∣ 2 :=
      orderOf_dvd_of_pow_eq_one (by rwa [pow_two])
    have h3 : orderOf (QuotientGroup.mk α : Outer Y) ∣ Nat.card (Outer Y) := orderOf_dvd_natCard _
    have h4 : orderOf (QuotientGroup.mk α : Outer Y) = 1 := by
      rcases (Nat.dvd_prime Nat.prime_two).mp h2 with h5 | h5
      · exact h5
      · rw [h5] at h3
        exact absurd (even_iff_two_dvd.mpr h3) (Nat.not_even_iff_odd.mpr hodd)
    rw [orderOf_eq_one_iff, QuotientGroup.eq_one_iff] at h4
    exact h4
  ·
    have hdvd : Nat.card ↥X ∣ Nat.card (Outer Y) := autCfg_card_dvd_outer hXI
    obtain ⟨k, hk⟩ := h.pgroup.exists_card_eq
    have hk0 : k ≠ 0 := by
      rintro rfl
      apply h.ne_bot
      rw [← Subgroup.card_eq_one, hk, pow_zero]
    rw [hk, h4] at hdvd
    have : p ∣ 2 ^ 2 := (dvd_pow_self p hk0).trans hdvd
    exact h.odd ((Nat.prime_dvd_prime_iff_eq h.prime Nat.prime_two).mp (h.prime.dvd_of_dvd_pow this))

theorem twoAutVac : TwoAutVac := by
  intro Y _ _ hY α p X h
  rcases hY with h8 | h16 | hSz
  · obtain ⟨e⟩ := KGroups.equiv_psl2_of_lieModel_even (S := Y) (f := 3) (by norm_num) h8
    have hB : BenderType Y 3 1 1 := .linear 3 (by norm_num) e
    have hOut : Odd (Nat.card (Outer Y)) := by rw [hB.outer_linear.2]; decide
    exact false_of_autCfg (by norm_num) hB (Or.inl hOut) h
  · obtain ⟨e⟩ := KGroups.equiv_psl2_of_lieModel_even (S := Y) (f := 4) (by norm_num) h16
    have hB : BenderType Y 4 1 1 := .linear 4 (by norm_num) e
    exact false_of_autCfg (by norm_num) hB (Or.inr hB.outer_linear.2) h
  · have hS : SuzukiModel Y 2 3 := by
      rcases hSz with ⟨ht, -⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩ | ⟨-, -, hS⟩
      · exact absurd ht (by decide)
      · exact absurd ht (by decide)
      · exact absurd ht (by decide)
      · exact hS
    obtain ⟨e⟩ := GLS.IVK.Proofs2.ivk93m12_szModel_equiv hS
    have hB : BenderType Y (2 * 1 + 1) 2 1 := .suzuki 1 le_rfl e
    exact false_of_autCfg (by norm_num) hB (Or.inl hB.outer_suzuki.2.2) h

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
