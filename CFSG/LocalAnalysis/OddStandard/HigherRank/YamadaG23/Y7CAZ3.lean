module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7CAZ1
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7CAZ2
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7CAP

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.OddStandard.HigherRank.G2Three.Sec1
open scoped commutatorElement

variable {Γ M : Type} [Group Γ] [Finite Γ] [Group M] [Finite M] {ρ : Γ →* MulAut M}
  {t : Γ} {J Q P M6 M7 : Subgroup Γ}

theorem y7c_lemmaZ (c : K7Abs ρ t J Q P M6 M7)
    (hq : CFSG.IsQuasisimple ↥(Subgroup.normalClosure (J : Set Γ))) {z : Γ}
    (hz : z ∈ Subgroup.normalClosure (J : Set Γ))
    (hzc : ∀ n ∈ Subgroup.normalClosure (J : Set Γ), z * n = n * z) (hρz : ρ z ≠ 1) :
    ∀ m : M, ρ z m = m → m = 1 := by
  let V : Subgroup M :=
    { carrier := {m | ρ z m = m}
      one_mem' := map_one (ρ z)
      mul_mem' := by
        intro a b ha hb
        simp only [Set.mem_setOf_eq] at ha hb ⊢
        rw [map_mul, ha, hb]
      inv_mem' := by
        intro a ha
        simp only [Set.mem_setOf_eq] at ha ⊢
        rw [map_inv, ha] }
  have hVinv : ∀ n ∈ Subgroup.normalClosure (J : Set Γ), ∀ v ∈ V, ρ n v ∈ V := by
    intro n hn v hv
    show ρ z (ρ n v) = ρ n v
    have hv' : ρ z v = v := hv
    rw [← MulAut.mul_apply, ← map_mul, hzc n hn, map_mul, MulAut.mul_apply, hv']
  obtain ⟨x, hxJ, hx7, hx1⟩ := y7c_J_exists_order7 c
  have hxN : x ∈ Subgroup.normalClosure (J : Set Γ) := Subgroup.subset_normalClosure hxJ
  have hσ : (ρ x) ^ 7 = 1 := by rw [← map_pow, hx7, map_one]
  have hfpf : ∀ m : M, ρ x m = m → m = 1 := c.J_fpf x hxJ hx7 hx1
  rcases y7c_card_invariant_cases c.M_E (σ := ρ x) (V := V) hσ hfpf (hVinv x hxN) with
    h1 | h8 | h64
  ·
    intro m hm
    have hmV : m ∈ V := hm
    rw [Subgroup.eq_bot_of_card_eq V h1] at hmV
    simpa using hmV
  ·
    exfalso
    have hVne : V ≠ ⊥ := by
      rw [← Subgroup.one_lt_card_iff_ne_bot, h8]
      norm_num
    obtain ⟨v, hv1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hVne
    have hne : ρ x (v : M) ≠ (v : M) := by
      intro h
      exact hv1 (Subtype.ext (c.J_fpf x hxJ hx7 hx1 (v : M) h))
    have hnt : ∃ n ∈ Subgroup.normalClosure (J : Set Γ), ∃ w ∈ V, ρ n w ≠ w :=
      ⟨x, hxN, (v : M), v.2, hne⟩
    have h168 := y7c_index_dvd_168 c.M_E ρ (N := Subgroup.normalClosure (J : Set Γ))
      (V := V) hq h8 hVinv hnt
    have hdiv := y7c_two_pow_six_dvd c
    have hdvd : (2 : ℕ) ^ 6 ∣ 168 := dvd_trans hdiv h168
    norm_num at hdvd
  ·
    exfalso
    have hVM : Nat.card ↥V = Nat.card M := by
      rw [h64, c.M_E.2]
      norm_num
    have hVtop : V = ⊤ := Subgroup.eq_top_of_card_eq V hVM
    have hρz1 : ρ z = 1 := by
      ext m
      show ρ z m = m
      have : m ∈ V := by rw [hVtop]; trivial
      exact this
    exact hρz hρz1

end CFSG.OddStandard.HigherRank.YamadaG23
