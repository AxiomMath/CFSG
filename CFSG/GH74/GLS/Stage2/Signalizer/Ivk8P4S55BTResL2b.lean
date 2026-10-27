module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55BTResL2a
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87FL2Cent
public import CFSG.GH74.GLS.IVK.L2.Borel
public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsFieldCent

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.BT.ResL2

open Subgroup CFSG CFSG.GH74.GLS CFSG.GH74.GLS.IVK CFSG.GorensteinWalter
  CFSG.ComponentClassification.CatalogueSchreierLinearTwo CFSG.GH74.GLS.Stage2.Signalizer.Odd87

theorem not_isSolvable_pgl2 {F₀ : Type} [Field F₀] [Finite F₀]
    (hodd : IsOddPrimePower (Nat.card F₀)) (h3 : 3 < Nat.card F₀) :
    ¬ Group.IsSolvable (PGL2 F₀) := by
  intro hsol
  have := Group.isSolvable_of_isSolvable_injective
    (Matrix.ProjectiveSpecialLinearGroup.toPGL_injective (n := Fin 2) (R := F₀))
  have := psl2_isPerfect_of_card_gt_three F₀ h3
  have : Nontrivial (PSL2 F₀) := by
    apply Finite.one_lt_card_iff_nontrivial.mp
    rw [psl2_card_formula F₀ hodd]
    set r := Nat.card F₀
    have h16 : 16 ≤ r ^ 2 := by nlinarith
    have h1 : 15 ≤ r ^ 2 - 1 := by omega
    have h2 : 60 ≤ r * (r ^ 2 - 1) := by nlinarith
    omega
  exact Group.IsPerfect.not_isSolvable _ ‹_›

variable {F : Type} [Field F] [Finite F] {Y : Type} [Group Y]

theorem pgammaAut_apply (e : Y ≃* L2 F) (x : PGammaL2 F) (y : Y) :
    pgammaAut e x y = (toPSL e).symm (semilinearAction F x (toPSL e y)) := rfl

theorem not_isSolvable_fixed (e : Y ≃* L2 F) {p n : ℕ} [Fact p.Prime] (hF : Nat.card F = p ^ n)
    (hp2 : p ≠ 2) (h9 : Nat.card F ≠ 9) {W : Subgroup Y} (hW : W ≠ ⊥) (hWp : IsPGroup p ↥W)
    {D : Subgroup (MulAut Y)} (hD2 : ∀ d ∈ D, d * d = 1) (hDW : ∀ d ∈ D, ∀ w ∈ W, d w ∈ W)
    {d₀ : MulAut Y} (hd₀ : d₀ ∈ D) (hd₀1 : d₀ ≠ 1)
    (hd₀i : d₀ ∈ (MulAut.conj : Y →* MulAut Y).range) {d : MulAut Y} (hd : d ∈ D) (hd1 : d ≠ 1)
    (hdd₀ : d ≠ d₀) : ¬ Group.IsSolvable ↥(fixedSubgroup Y d) := by
  have hp : p.Prime := Fact.out
  have hodd : Odd (Nat.card F) := hF ▸ (hp.odd_of_ne_two hp2).pow
  have h2 : (2 : F) ≠ 0 := L2Borel.two_ne_zero_of_odd_card hodd
  set Φ := pgammaAut e with hΦ
  set W' : Subgroup (PSL2 F) := W.map (toPSL e).toMonoidHom with hW'
  have hW'1 : W' ≠ ⊥ := by
    intro hbot
    apply hW
    rwa [hW', Subgroup.map_eq_bot_iff_of_injective _ (toPSL e).injective] at hbot
  have hW'p : IsPGroup p ↥W' := hWp.map _
  have hn : ∀ {c : MulAut Y}, c ∈ D → ∀ w ∈ W', semilinearAction F (Φ.symm c) w ∈ W' := by
    rintro c hc _ ⟨w₀, hw₀, rfl⟩
    refine ⟨c w₀, hDW c hc w₀ hw₀, ?_⟩
    have h1 : Φ (Φ.symm c) w₀ = c w₀ := by rw [MulEquiv.apply_symm_apply]
    rw [pgammaAut_apply] at h1
    rw [← h1]
    simp
  have hsq : ∀ {c : MulAut Y}, c ∈ D → Φ.symm c * Φ.symm c = 1 := by
    intro c hc
    rw [← map_mul, hD2 c hc, map_one]
  have hr₀ : (Φ.symm d₀).right = 1 := by
    obtain ⟨y, rfl⟩ := hd₀i
    have h1 : Φ (SemidirectProduct.inl (Matrix.ProjectiveSpecialLinearGroup.toPGL (toPSL e y))) =
        MulAut.conj y := by
      rw [hΦ, pgammaAut_inl, L2Borel.innDiagHom_toPGL_toPSL]
    rw [← h1, MulEquiv.symm_apply_apply]
    rfl
  have hr : (Φ.symm d).right ≠ 1 := by
    intro hr
    apply hdd₀
    have hmem : d * d₀ ∈ D := D.mul_mem hd hd₀
    refine Φ.symm.injective (eq_of_right_eq_one hF h2 hW'1 hW'p (hn hd) (hn hd₀) hr hr₀ (hsq hd)
      (hsq hd₀) ?_ ?_ ?_)
    · rw [← map_mul, ← map_mul, hD2 _ hmem, map_one]
    · simpa using hd1
    · simpa using hd₀1
  set x := Φ.symm d with hx
  have hord : orderOf x = 2 :=
    orderOf_eq_prime (by rw [sq]; exact hsq hd) (by simpa [hx] using hd1)
  obtain ⟨C, hC⟩ := H90.pgammaL2_involution_conj_inr x hord hr
  set σ : F ≃+* F := x.right with hσdef
  have hσ2 : orderOf σ = 2 := by
    have hdvd : orderOf σ ∣ orderOf x := orderOf_map_dvd (SemidirectProduct.rightHom) x
    rw [hord] at hdvd
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hr
    · exact h
  have hconj : (innDiagHom e C)⁻¹ * d * (innDiagHom e C)⁻¹⁻¹ = fieldAutHom e σ := by
    have hΦx : Φ x = d := by rw [hx, MulEquiv.apply_symm_apply]
    rw [inv_inv, ← hΦx, hΦ, ← pgammaAut_inl, ← pgammaAut_inr, ← map_inv, ← map_mul, ← map_mul,
      hC]
  obtain ⟨F₀, _, _, hq₀, ⟨eP⟩⟩ := isPGL2_fixedSubgroup e σ ⟨1, by rw [hσ2]⟩
  rw [hσ2] at hq₀
  have hF₀odd : Odd (Nat.card F₀) := by
    rw [← hq₀, sq] at hodd
    exact Nat.odd_mul.mp hodd |>.1
  have h3 : 3 < Nat.card F₀ := by
    have h1 : 1 < Nat.card F₀ := Finite.one_lt_card
    have h3' : Nat.card F₀ ≠ 3 := by
      intro h
      apply h9
      rw [← hq₀, h]
      norm_num
    obtain ⟨k, hk⟩ := hF₀odd
    omega
  intro hsol
  apply not_isSolvable_pgl2
    (CFSG.ComponentClassification.AutL2Facts.isOddPrimePower_of_odd_card F₀ hF₀odd) h3
  exact Group.isSolvable_of_surjective
    (f := ((fixedSubgroupEquivOfConj' hconj).trans eP).toMonoidHom)
    ((fixedSubgroupEquivOfConj' hconj).trans eP).surjective

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.BT.ResL2
