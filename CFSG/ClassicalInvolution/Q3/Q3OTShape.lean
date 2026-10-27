module

public import CFSG.ClassicalInvolution.ModelFacts.TG3VacPSL
public import CFSG.ClassicalInvolution.ModelFacts.TG3VacPSU
public import CFSG.ClassicalInvolution.ModelFacts.TG3VacPSp
public import CFSG.ClassicalInvolution.ModelFacts.TG3Final
public import CFSG.ClassicalInvolution.ModelFacts.Orth15TwinModel
public import CFSG.ClassicalInvolution.ModelFacts.Orth15LieTwin
public import CFSG.ClassicalInvolution.Q3.Q3DInputs3

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3OT

open CFSG CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Models CFSG.ClassicalInvolution.Phan
  CFSG.LieType.BorelTits CFSG.LieType.Universal.Unitary CFSG.LocalAnalysis.ComponentInitial Module
  CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Asc77
  CFSG.ClassicalInvolution.Uniform CFSG.ClassicalInvolution.RouteD
  CFSG.ClassicalInvolution.RouteD.Exotic CFSG.ClassicalInvolution.ModelFacts.TG3
open scoped MatrixGroups Matrix

local notation "𝔽₃" => GaloisField 3 1


section Vac

variable {H : Type} [Group H]

theorem false_of_twin_psl {k : ℕ} (hadm : StatedLieAdmissible .PSL k 3 1) (hk : k ≠ 4)
    (ψ : (modelUniv .PSL k 3 1 Nat.prime_three).K →* H)
    {R R' : Subgroup (modelUniv .PSL k 3 1 Nat.prime_three).K}
    {x x' : (modelUniv .PSL k 3 1 Nat.prime_three).K}
    (hpair : TwinPairOn .PSL (modelUniv .PSL k 3 1 Nat.prime_three) ψ R R' x x') : False := by
  have hk2 : 2 ≤ k := hadm.2.2.1
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  have hodd := odd_natCard_galoisField_three
  have h2 : (2 : 𝔽₃) ≠ 0 := two_ne_zero_three
  have hL := fundamentalSubgroups_psl_eq (p := 3) (f := 1) (m := m) (by omega)
  obtain ⟨e₁⟩ := ModelFacts.nonempty_equiv_sl2_of_mem_fundamentalSubgroups hp2 (t := .PSL)
    trivial hadm (by decide) (by decide) hpair.mem
  obtain ⟨e₂⟩ := ModelFacts.nonempty_equiv_sl2_of_mem_fundamentalSubgroups hp2 (t := .PSL)
    trivial hadm (by decide) (by decide) hpair.mem'
  have hxe₁ : x = sl2Inv e₁ :=
    eq_sl2Inv_of_orderOf_eq_two hodd e₁ hpair.hx
      (orderOf_eq_prime (by rw [_root_.sq]; exact hpair.hx2) hpair.hx1)
  have hxe₂ : x' = sl2Inv e₂ :=
    eq_sl2Inv_of_orderOf_eq_two hodd e₂ hpair.hx'
      (orderOf_eq_prime (by rw [_root_.sq]; exact hpair.hx'2) hpair.hx'1)
  have hcen : sl2Inv e₂ * (sl2Inv e₁)⁻¹ ∈ Subgroup.center (modelUniv .PSL (m + 1) 3 1
      Nat.prime_three).K := by
    apply hpair.ker
    rw [MonoidHom.mem_ker, map_mul, map_inv, ← hxe₁, ← hxe₂, ← hpair.same, mul_inv_cancel]
  have hR₁' : R ∈ longRootSet (K := 𝔽₃) (by omega : 2 ≤ m + 1) := by
    rw [← hL]
    exact hpair.mem
  have hR₂' : R' ∈ longRootSet (K := 𝔽₃) (by omega : 2 ≤ m + 1) := by
    rw [← hL]
    exact hpair.mem'
  obtain ⟨i₁, hi₁⟩ := hR₁'
  obtain ⟨i₂, hi₂⟩ := hR₂'
  have hi₁e : i₁ = sl2Inv e₁ :=
    eq_sl2Inv_of_orderOf_eq_two hodd e₁ hi₁.mem ((hi₁.isClassicalSL2 h2).orderOf_eq_two)
  have hi₂e : i₂ = sl2Inv e₂ :=
    eq_sl2Inv_of_orderOf_eq_two hodd e₂ hi₂.mem ((hi₂.isClassicalSL2 h2).orderOf_eq_two)
  have hRR : R = R' :=
    eq_of_central_ratio_longRoot (by omega) hk hi₁ hi₂ (by rw [hi₁e, hi₂e]; exact hcen)
  exact hpair.ne hRR

theorem false_of_twin_psp {n : ℕ} (hadm : StatedLieAdmissible .PSp n 3 1) (hn2 : n ≠ 2)
    (ψ : (modelUniv .PSp n 3 1 Nat.prime_three).K →* H)
    {R R' : Subgroup (modelUniv .PSp n 3 1 Nat.prime_three).K}
    {x x' : (modelUniv .PSp n 3 1 Nat.prime_three).K}
    (hpair : TwinPairOn .PSp (modelUniv .PSp n 3 1 Nat.prime_three) ψ R R' x x') : False := by
  have hn : 2 ≤ n := hadm.2.2.1
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  have hodd := odd_natCard_galoisField_three
  have h2 : (2 : 𝔽₃) ≠ 0 := two_ne_zero_three
  obtain ⟨e₁⟩ := ModelFacts.nonempty_equiv_sl2_of_mem_fundamentalSubgroups hp2 (t := .PSp)
    trivial hadm (by decide) (by decide) hpair.mem
  obtain ⟨e₂⟩ := ModelFacts.nonempty_equiv_sl2_of_mem_fundamentalSubgroups hp2 (t := .PSp)
    trivial hadm (by decide) (by decide) hpair.mem'
  have hxe₁ : x = sl2Inv e₁ :=
    eq_sl2Inv_of_orderOf_eq_two hodd e₁ hpair.hx
      (orderOf_eq_prime (by rw [_root_.sq]; exact hpair.hx2) hpair.hx1)
  have hxe₂ : x' = sl2Inv e₂ :=
    eq_sl2Inv_of_orderOf_eq_two hodd e₂ hpair.hx'
      (orderOf_eq_prime (by rw [_root_.sq]; exact hpair.hx'2) hpair.hx'1)
  have hcen : sl2Inv e₂ * (sl2Inv e₁)⁻¹ ∈ Subgroup.center (modelUniv .PSp n 3 1
      Nat.prime_three).K := by
    apply hpair.ker
    rw [MonoidHom.mem_ker, map_mul, map_inv, ← hxe₁, ← hxe₂, ← hpair.same, mul_inv_cancel]
  obtain ⟨i₁, hi₁⟩ := (ModelFacts.fund_iff_isLongRootSp2 hadm h2 R).mp hpair.mem
  obtain ⟨i₂, hi₂⟩ := (ModelFacts.fund_iff_isLongRootSp2 hadm h2 R').mp hpair.mem'
  have hi₁e : i₁ = sl2Inv e₁ :=
    eq_sl2Inv_of_orderOf_eq_two hodd e₁ ((hi₁.isClassicalSL2 h2).mem)
      ((hi₁.isClassicalSL2 h2).orderOf_eq_two)
  have hi₂e : i₂ = sl2Inv e₂ :=
    eq_sl2Inv_of_orderOf_eq_two hodd e₂ ((hi₂.isClassicalSL2 h2).mem)
      ((hi₂.isClassicalSL2 h2).orderOf_eq_two)
  have hRR : R = R' :=
    eq_of_central_ratio_longRootSp hn hn2 hi₁ hi₂ (by rw [hi₁e, hi₂e]; exact hcen)
  exact hpair.ne hRR

theorem false_of_twin_psu {k : ℕ} (hadm : StatedLieAdmissible .PSU k 3 1) (hk : k ≠ 4)
    (ψ : (modelUniv .PSU k 3 1 Nat.prime_three).K →* H)
    {R R' : Subgroup (modelUniv .PSU k 3 1 Nat.prime_three).K}
    {x x' : (modelUniv .PSU k 3 1 Nat.prime_three).K}
    (hpair : TwinPairOn .PSU (modelUniv .PSU k 3 1 Nat.prime_three) ψ R R' x x') : False := by
  have hk3 : 3 ≤ k := hadm.2.2.1
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  have hodd := odd_natCard_galoisField_three
  obtain ⟨e, hfund⟩ := psu_model_equiv (p := 3) (f := 1) hp2 hadm
  have hK : Nat.card (GaloisField 3 (2 * 1)) = (3 ^ 1) ^ 2 := by
    rw [GaloisField.card 3 (2 * 1) (by norm_num)]
    norm_num
  obtain ⟨e₁⟩ := ModelFacts.nonempty_equiv_sl2_of_mem_fundamentalSubgroups hp2 (t := .PSU) trivial
    hadm (by decide) (by decide) hpair.mem
  obtain ⟨e₂⟩ := ModelFacts.nonempty_equiv_sl2_of_mem_fundamentalSubgroups hp2 (t := .PSU) trivial
    hadm (by decide) (by decide) hpair.mem'
  have hxe₁ : x = sl2Inv e₁ :=
    eq_sl2Inv_of_orderOf_eq_two hodd e₁ hpair.hx
      (orderOf_eq_prime (by rw [_root_.sq]; exact hpair.hx2) hpair.hx1)
  have hxe₂ : x' = sl2Inv e₂ :=
    eq_sl2Inv_of_orderOf_eq_two hodd e₂ hpair.hx'
      (orderOf_eq_prime (by rw [_root_.sq]; exact hpair.hx'2) hpair.hx'1)
  have hcen : sl2Inv e₂ * (sl2Inv e₁)⁻¹ ∈ Subgroup.center (modelUniv .PSU k 3 1
      Nat.prime_three).K := by
    apply hpair.ker
    rw [MonoidHom.mem_ker, map_mul, map_inv, ← hxe₁, ← hxe₂, ← hpair.same, mul_inv_cancel]
  have hsq₁ := sl2Inv_mul_self hodd e₁
  have hsq₂ := sl2Inv_mul_self hodd e₂
  have hcen' : sl2Inv e₁ * sl2Inv e₂ ∈ Subgroup.center (modelUniv .PSU k 3 1
      Nat.prime_three).K := by
    have h1 : sl2Inv e₁ * sl2Inv e₂ = sl2Inv e₂ * (sl2Inv e₁)⁻¹ := by
      have hc := Subgroup.mem_center_iff.mp hcen (sl2Inv e₁)
      have hinv : (sl2Inv e₁)⁻¹ = sl2Inv e₁ := inv_eq_of_mul_eq_one_right hsq₁
      rw [hinv] at hc ⊢
      have h3 := congrArg (fun x => x * sl2Inv e₁) hc
      simp only [mul_assoc, hsq₁, mul_one] at h3
      exact h3
    rw [h1]
    exact hcen
  have hne' : R.map e.toMonoidHom ≠ R'.map e.toMonoidHom := by
    intro h
    exact hpair.ne (Subgroup.map_injective e.injective h)
  have hcenE : e (sl2Inv e₁) * e (sl2Inv e₂) ∈
      Subgroup.center (Su (GaloisField 3 (2 * 1)) 3 1 k) := by
    refine Subgroup.mem_center_iff.mpr fun y => ?_
    obtain ⟨x, rfl⟩ := e.surjective y
    rw [← map_mul, ← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hcen' x]
  have hres := rank_eq_four_of_central_pair_su3 (K := GaloisField 3 (2 * 1)) (p := 3) (f := 1) hK
    hp2 le_rfl hk3 ((hfund R).mp hpair.mem) ((hfund R').mp hpair.mem') hne'
    (r₁ := e (sl2Inv e₁)) (r₂ := e (sl2Inv e₂))
    (Subgroup.mem_map_of_mem _ (sl2Inv_mem e₁))
    (fun s hs => by
      obtain ⟨s₀, hs₀, rfl⟩ := hs
      change e (sl2Inv e₁) * e s₀ = e s₀ * e (sl2Inv e₁)
      rw [← map_mul, ← map_mul, sl2Inv_commute e₁ hs₀])
    (fun h => sl2Inv_ne_one hodd e₁ (e.injective (by rw [h, map_one])))
    (Subgroup.mem_map_of_mem _ (sl2Inv_mem e₂))
    (fun s hs => by
      obtain ⟨s₀, hs₀, rfl⟩ := hs
      change e (sl2Inv e₂) * e s₀ = e s₀ * e (sl2Inv e₂)
      rw [← map_mul, ← map_mul, sl2Inv_commute e₂ hs₀])
    (fun h => sl2Inv_ne_one hodd e₂ (e.injective (by rw [h, map_one])))
    hcenE
  exact hk hres

theorem false_of_twin_exc {t : StatedLieTag} {n : ℕ}
    (hexc : t = .F4 ∨ t = .E6 ∨ t = .E7 ∨ t = .E8 ∨ t = .twistedE6)
    (hadm : StatedLieAdmissible t n 3 1) (ψ : (modelUniv t n 3 1 Nat.prime_three).K →* H)
    {R R' : Subgroup (modelUniv t n 3 1 Nat.prime_three).K}
    {x x' : (modelUniv t n 3 1 Nat.prime_three).K}
    (hpair : TwinPairOn t (modelUniv t n 3 1 Nat.prime_three) ψ R R' x x') : False := by
  have hfund : ModelFacts.IsFundTag t := by
    rcases hexc with rfl | rfl | rfl | rfl | rfl <;> trivial
  have hG2 : t ≠ .G2 := by rcases hexc with rfl | rfl | rfl | rfl | rfl <;> decide
  have hD4 : t ≠ .trialityD4 := by rcases hexc with rfl | rfl | rfl | rfl | rfl <;> decide
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  have hodd := odd_natCard_galoisField_three
  obtain ⟨e₁⟩ := ModelFacts.nonempty_equiv_sl2_of_mem_fundamentalSubgroups hp2 hfund hadm hG2 hD4
    hpair.mem
  obtain ⟨e₂⟩ := ModelFacts.nonempty_equiv_sl2_of_mem_fundamentalSubgroups hp2 hfund hadm hG2 hD4
    hpair.mem'
  have hxe₁ : x = sl2Inv e₁ :=
    eq_sl2Inv_of_orderOf_eq_two hodd e₁ hpair.hx
      (orderOf_eq_prime (by rw [_root_.sq]; exact hpair.hx2) hpair.hx1)
  have hxe₂ : x' = sl2Inv e₂ :=
    eq_sl2Inv_of_orderOf_eq_two hodd e₂ hpair.hx'
      (orderOf_eq_prime (by rw [_root_.sq]; exact hpair.hx'2) hpair.hx'1)
  have hcen : sl2Inv e₂ * (sl2Inv e₁)⁻¹ ∈ Subgroup.center (modelUniv t n 3 1
      Nat.prime_three).K := by
    apply hpair.ker
    rw [MonoidHom.mem_ker, map_mul, map_inv, ← hxe₁, ← hxe₂, ← hpair.same, mul_inv_cancel]
  exact Disc3.twinNoExc3_proved t n hexc hadm R hpair.mem R' hpair.mem' hpair.ne e₁ e₂ hcen

end Vac

section Shape

variable {H : Type} [Group H]

theorem twinPairOn_shape3 {t : StatedLieTag} {n : ℕ} (hFT : IsFundTag t)
    (hadm : StatedLieAdmissible t n 3 1) (ψ : (modelUniv t n 3 1 Nat.prime_three).K →* H)
    {R R' : Subgroup (modelUniv t n 3 1 Nat.prime_three).K}
    {x x' : (modelUniv t n 3 1 Nat.prime_three).K}
    (hpair : TwinPairOn t (modelUniv t n 3 1 Nat.prime_three) ψ R R' x x') :
    TwinShape t n ∨ t = .G2 ∨ t = .trialityD4 := by
  cases t with
  | PSL =>
    by_cases hn : n = 4
    · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, hn⟩)))))
    · exact (false_of_twin_psl hadm hn ψ hpair).elim
  | PSU =>
    by_cases hn : n = 4
    · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, hn⟩)))))
    · exact (false_of_twin_psu hadm hn ψ hpair).elim
  | PSp =>
    by_cases hn : n = 2
    · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, hn⟩))))
    · exact (false_of_twin_psp hadm hn ψ hpair).elim
  | POmegaOdd => exact Or.inl (Or.inl ⟨rfl, hadm.2.2.1⟩)
  | POmegaPlus => exact Or.inl (Or.inr (Or.inl ⟨rfl, hadm.2.2⟩))
  | POmegaMinus => exact Or.inl (Or.inr (Or.inr (Or.inl ⟨rfl, hadm.2.2⟩)))
  | G2 => exact Or.inr (Or.inl rfl)
  | trialityD4 => exact Or.inr (Or.inr rfl)
  | F4 => exact (false_of_twin_exc (Or.inl rfl) hadm ψ hpair).elim
  | E6 => exact (false_of_twin_exc (Or.inr (Or.inl rfl)) hadm ψ hpair).elim
  | E7 => exact (false_of_twin_exc (Or.inr (Or.inr (Or.inl rfl))) hadm ψ hpair).elim
  | E8 => exact (false_of_twin_exc (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) hadm ψ hpair).elim
  | twistedE6 =>
    exact (false_of_twin_exc (Or.inr (Or.inr (Or.inr (Or.inr rfl)))) hadm ψ hpair).elim
  | twistedB2 => exact hFT.elim
  | twistedG2 => exact hFT.elim
  | twistedF4 => exact hFT.elim
  | Tits => exact hFT.elim

end Shape

end CFSG.ClassicalInvolution.Q3.Q3OT
