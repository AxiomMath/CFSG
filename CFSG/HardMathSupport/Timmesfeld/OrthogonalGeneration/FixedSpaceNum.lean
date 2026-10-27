module

public import CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.FixedSpace
public import CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.ArfFpf

public section

namespace CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration

open QuadraticMap Module CFSG.ClassicalGroups.Orthogonal CFSG.LocalAnalysis.GLTheoremB

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

@[expose] def sgnZ (p : ℕ) (ε : Bool) : ZMod p := if ε then 1 else -1

theorem dvd_iff_pow_eq_sgn {p : ℕ} (k : ℕ) (ε : Bool) :
    p ∣ (if ε then 2 ^ k - 1 else 2 ^ k + 1) ↔ (2 : ZMod p) ^ k = sgnZ p ε := by
  have h1 : 1 ≤ 2 ^ k := Nat.one_le_two_pow
  cases ε
  · simp only [Bool.false_eq_true, ↓reduceIte, sgnZ]
    rw [← ZMod.natCast_eq_zero_iff]
    push_cast
    rw [add_eq_zero_iff_eq_neg]
  · simp only [↓reduceIte, sgnZ]
    rw [← ZMod.natCast_eq_zero_iff, Nat.cast_sub h1]
    push_cast
    rw [sub_eq_zero]

theorem sgnZ_beq (p : ℕ) (ε₁ ε₂ : Bool) : sgnZ p (ε₁ == ε₂) = sgnZ p ε₁ * sgnZ p ε₂ := by
  cases ε₁ <;> cases ε₂ <;> simp [sgnZ]

theorem sgnZ_mul_self (p : ℕ) (ε : Bool) : sgnZ p ε * sgnZ p ε = 1 := by
  cases ε <;> simp [sgnZ]

theorem arith_numerics {p : ℕ} {ε ε₁ ε₂ : Bool} {m₁ m₂ n : ℕ} (hn : n + 1 = m₁ + m₂)
    (hε : ε = (ε₁ == ε₂)) (hm₁ : 1 ≤ m₁)
    (h1 : p ∣ (if ε then 2 ^ n - 1 else 2 ^ n + 1))
    (h2 : p ∣ (if ε₂ then 2 ^ m₂ - 1 else 2 ^ m₂ + 1)) :
    p ∣ (if ε₁ then 2 ^ (m₁ - 1) - 1 else 2 ^ (m₁ - 1) + 1) := by
  rw [dvd_iff_pow_eq_sgn] at h1 h2 ⊢
  have hn' : n = (m₁ - 1) + m₂ := by omega
  rw [hn', pow_add, h2, hε, sgnZ_beq] at h1
  have := congrArg (· * sgnZ p ε₂) h1
  rw [mul_assoc, sgnZ_mul_self, mul_one, mul_assoc, sgnZ_mul_self, mul_one] at this
  exact this

@[expose] noncomputable def restrictPerp (Q : QuadraticForm (ZMod 2) V) (g : V ≃ₗ[ZMod 2] V)
    (hU : (perpSub Q (fixSub (Subgroup.zpowers g))).map (g : V →ₗ[ZMod 2] V) =
      perpSub Q (fixSub (Subgroup.zpowers g))) :
    perpSub Q (fixSub (Subgroup.zpowers g)) ≃ₗ[ZMod 2] perpSub Q (fixSub (Subgroup.zpowers g)) :=
  g.ofSubmodules _ _ hU

theorem coe_restrictPerp_pow {Q : QuadraticForm (ZMod 2) V} {g : V ≃ₗ[ZMod 2] V}
    {hU : (perpSub Q (fixSub (Subgroup.zpowers g))).map (g : V →ₗ[ZMod 2] V) =
      perpSub Q (fixSub (Subgroup.zpowers g))} (k : ℕ)
    (x : perpSub Q (fixSub (Subgroup.zpowers g))) :
    (((restrictPerp Q g hU ^ k) x : perpSub Q (fixSub (Subgroup.zpowers g))) : V) = (g ^ k) x := by
  induction k generalizing x with
  | zero => rfl
  | succ k ih =>
    rw [pow_succ, LinearEquiv.mul_apply, ih, pow_succ, LinearEquiv.mul_apply]
    rfl

theorem polarPerp_eq_perpSub (Q : QuadraticForm (ZMod 2) V) (W : Submodule (ZMod 2) V) :
    polarPerp Q W = perpSub Q W := by
  ext x
  rw [mem_polarPerp, mem_perpSub]
  exact forall₂_congr fun w _ => by rw [polar_comm]

theorem fixedSpace_numerics' [FiniteDimensional (ZMod 2) V] {Q : QuadraticForm (ZMod 2) V}
    (hQ : PolarNondeg Q) {ε : Bool} {n : ℕ} (hstd : IsStdSpace ε Q (n + 1)) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hn : 1 ≤ n) (hfpf : HasFixedPointFreeOrder ε n p)
    {g : V ≃ₗ[ZMod 2] V} (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hgp : g ^ p = 1)
    (hdim : 4 ≤ finrank (ZMod 2) (fixSub (Subgroup.zpowers g))) :
    ∃ (ε' : Bool) (n' : ℕ), 1 ≤ n' ∧ (ε' = true → 2 ≤ n') ∧
      IsStdSpace ε' (Q.restrict (fixSub (Subgroup.zpowers g))) (n' + 1) ∧
      HasFixedPointFreeOrder ε' n' p := by
  have hodd : Odd p := hp.odd_of_ne_two hp2
  have hEO : Subgroup.zpowers g ≤ TauCeti.QuadraticMap.orthogonalGroup Q :=
    (Subgroup.zpowers_le).mpr hg
  have hoddc : Odd (Nat.card (Subgroup.zpowers g)) :=
    odd_natCard_subgroup_of_pow_eq_one hodd fun h hh => by
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hgp, one_zpow]
  have hWnd : PolarNondegOn Q (fixSub (Subgroup.zpowers g)) := polarNondegOn_fixSub hQ hEO hoddc
  obtain ⟨ε₁, ε₂, m₁, m₂, h₁, hm₁, h₂, hm₂, h⟩ := exists_isStdSpace_perp hQ hWnd
  have h₂' : IsStdSpace ε₂ (Q.restrict (perpSub Q (fixSub (Subgroup.zpowers g)))) m₂ := by
    rw [← polarPerp_eq_perpSub]; exact h₂
  have hc : ∀ x ∈ Subgroup.zpowers g, g * x = x * g := fun x hx => by
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    exact (Commute.self_zpow g k).eq
  have hc' : ∀ x ∈ Subgroup.zpowers g, g⁻¹ * x = x * g⁻¹ := fun x hx => by
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    exact ((Commute.self_zpow g k).inv_left).eq
  have hU : (perpSub Q (fixSub (Subgroup.zpowers g))).map (g : V →ₗ[ZMod 2] V) =
      perpSub Q (fixSub (Subgroup.zpowers g)) := by
    refine le_antisymm ?_ fun x hx => ?_
    · rintro _ ⟨x, hx, rfl⟩
      exact apply_mem_perpSub_fixSub_of_commute hg hc hx
    · exact ⟨g⁻¹ x, apply_mem_perpSub_fixSub_of_commute (inv_mem hg) hc' hx, by simp⟩
  set T := restrictPerp Q g hU with hTdef
  have hT : ∀ v, (Q.restrict (perpSub Q (fixSub (Subgroup.zpowers g)))) (T v) =
      (Q.restrict (perpSub Q (fixSub (Subgroup.zpowers g)))) v := fun v =>
    TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup hg (v : V)
  have hTp : T ^ p = 1 := LinearEquiv.ext fun x =>
    Subtype.ext (by rw [hTdef, coe_restrictPerp_pow, hgp]; rfl)
  have hfix : ∀ v, T v = v → v = 0 := fun v hv =>
    Subtype.ext (eq_zero_of_mem_perpSub_fixSub_of_apply_eq hQ hg hodd hgp v.2
      (congrArg Subtype.val hv))
  have hd2 := dvd_of_fpf h₂' hm₂ hp T hT hTp hfix
  have hm : ((ε₁ == ε₂) = false) → 1 ≤ m₁ + m₂ := fun hε => by
    by_cases h1 : ε₁ = false
    · have := hm₁ h1; omega
    · have h2 : ε₂ = false := by cases ε₁ <;> cases ε₂ <;> simp_all
      have := hm₂ h2; omega
  obtain ⟨hεe, hnm⟩ := isStdSpace_unique hstd h (fun _ => by omega) hm
  have hfr := finrank_of_isStdSpace_arf h₁ hm₁
  have hm₁2 : 2 ≤ m₁ := by omega
  have hiff := (hasFixedPointFreeOrder_iff hp hp2 hn).mp hfpf
  have hd1 := arith_numerics hnm hεe (by omega) hiff hd2
  refine ⟨ε₁, m₁ - 1, by omega, fun hε₁ => ?_, ?_, ?_⟩
  · by_contra hlt
    have : m₁ - 1 = 1 := by omega
    rw [hε₁, this] at hd1
    simp only [↓reduceIte, pow_one, Nat.add_one_sub_one] at hd1
    exact hp.one_lt.ne' (Nat.dvd_one.mp (by simpa using hd1))
  · have : m₁ - 1 + 1 = m₁ := by omega
    rw [this]; exact h₁
  · exact (hasFixedPointFreeOrder_iff hp hp2 (by omega)).mpr hd1

end CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration
