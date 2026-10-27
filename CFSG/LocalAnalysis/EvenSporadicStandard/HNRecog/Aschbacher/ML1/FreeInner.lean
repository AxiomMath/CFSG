module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Aschbacher.Fpf.Core

public section

namespace CFSG.EvenSporadicStandard.HNRecog.ML1

open Module CFSG.EvenSporadicStandard.HNRecog.Fpf

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

private theorem inner_free (u β : Module.End (ZMod 2) V) (hu : u ^ 2 = 1) (hβ5 : β ^ 5 = 1)
    (hcomm : β * u = u * β) (hβfree : ∀ w : V, β w = w → w = 0)
    (h8 : finrank (ZMod 2) V = 8) (hu1 : u ≠ 1) :
    ∀ w : V, u w = w → ∃ w' : V, w = w' + u w' := by
  haveI : FiniteDimensional (ZMod 2) V := Module.Finite.of_finite
  intro w hw
  let U : Module.End (ZMod 2) V := u + 1
  have h2 : (2 : ZMod 2) = 0 := by decide
  have hself : ∀ x : Module.End (ZMod 2) V, x + x = 0 := by
    intro x
    rw [← two_smul (ZMod 2) x, h2, zero_smul]
  have hsq : u * u = 1 := by simpa [pow_two] using hu
  have hUU : U * U = 0 := by
    calc U * U = (u + 1) * (u + 1) := rfl
      _ = u * u + (u + u) + 1 := by noncomm_ring
      _ = 0 := by rw [hsq, hself u]; simp only [add_zero]; exact hself 1
  have hrange_le_ker : LinearMap.range U ≤ LinearMap.ker U := by
    rintro _ ⟨v, rfl⟩
    rw [LinearMap.mem_ker, ← Module.End.mul_apply, hUU]
    simp
  have hcommU : β * U = U * β := by
    change β * (u + 1) = (u + 1) * β
    rw [mul_add, add_mul, mul_one, one_mul, hcomm]
  have hstab : ∀ x ∈ LinearMap.range U, β x ∈ LinearMap.range U := by
    rintro x ⟨v, rfl⟩
    refine ⟨β v, ?_⟩
    exact (calc β (U v) = (β * U) v := (Module.End.mul_apply β U v).symm
      _ = (U * β) v := by rw [hcommU]
      _ = U (β v) := Module.End.mul_apply U β v).symm
  have hfix : ∀ x ∈ LinearMap.range U, β x = x → x = 0 := fun x _ hx => hβfree x hx
  have h4dvd : 4 ∣ finrank (ZMod 2) (LinearMap.range U) :=
    four_dvd_finrank_of_fixedFree β hβ5 (LinearMap.range U) hstab hfix
  have hne_bot : LinearMap.range U ≠ ⊥ := by
    intro hbot
    have hU0 : U = 0 := LinearMap.range_eq_bot.mp hbot
    have hU0' : u + 1 = 0 := hU0
    have hneg1 : (-1 : Module.End (ZMod 2) V) = 1 :=
      (neg_eq_iff_add_eq_zero).mpr (hself 1)
    exact hu1 ((eq_neg_of_add_eq_zero_left hU0').trans hneg1)
  have hpos : 0 < finrank (ZMod 2) (LinearMap.range U) :=
    lt_of_lt_of_le Nat.zero_lt_one (Submodule.one_le_finrank_iff.mpr hne_bot)
  have h4le : 4 ≤ finrank (ZMod 2) (LinearMap.range U) := Nat.le_of_dvd hpos h4dvd
  have hrn := LinearMap.finrank_range_add_finrank_ker U
  rw [h8] at hrn
  have hker_le_R : finrank (ZMod 2) (LinearMap.ker U) ≤ finrank (ZMod 2) (LinearMap.range U) := by
    omega
  have hEq : LinearMap.range U = LinearMap.ker U :=
    Submodule.eq_of_le_of_finrank_le hrange_le_ker hker_le_R
  have hwker : w ∈ LinearMap.ker U := by
    rw [LinearMap.mem_ker]
    show u w + w = 0
    rw [hw, ← two_smul (ZMod 2) w, h2, zero_smul]
  rw [← hEq] at hwker
  obtain ⟨w', hw'⟩ := hwker
  refine ⟨w', ?_⟩
  calc w = U w' := hw'.symm
    _ = u w' + w' := rfl
    _ = w' + u w' := add_comm _ _

theorem exists_eq_add_of_fixed_inner (σ : A5 × A5 →* (V ≃ₗ[ZMod 2] V)) (hσ : Function.Injective σ)
    (h8 : finrank (ZMod 2) V = 8)
    (hirr : ∀ U : Submodule (ZMod 2) V, (∀ g : A5 × A5, ∀ u ∈ U, σ g u ∈ U) → U = ⊥ ∨ U = ⊤)
    {a : A5} (ha1 : a ≠ 1) (ha2 : a ^ 2 = 1) :
    (∀ w : V, σ (a, 1) w = w → ∃ w' : V, w = w' + σ (a, 1) w') ∧
      (∀ w : V, σ (1, a) w = w → ∃ w' : V, w = w' + σ (1, a) w') := by
  let ρ : A5 × A5 →* Module.End (ZMod 2) V :=
    (Units.coeHom (Module.End (ZMod 2) V)).comp
      ((LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) V).symm.toMonoidHom.comp σ)
  obtain ⟨hfixA, hfixB⟩ := fixedFree_of_irreducible σ hσ h8 hirr
  have ha0 : (a₀ : A5) ^ 5 = 1 := by
    have h := pow_orderOf_eq_one a₀
    rwa [orderOf_a₀] at h
  constructor
  · have hp2 : ((a, 1) : A5 × A5) ^ 2 = 1 := by
      ext <;> simp [Prod.pow_fst, Prod.pow_snd, ha2]
    have hu : (ρ (a, 1)) ^ 2 = 1 := by rw [← map_pow, hp2, map_one]
    have hq5 : ((1, a₀) : A5 × A5) ^ 5 = 1 := by
      ext <;> simp [Prod.pow_fst, Prod.pow_snd, ha0]
    have hβ5 : (ρ (1, a₀)) ^ 5 = 1 := by rw [← map_pow, hq5, map_one]
    have hcomm : ρ (1, a₀) * ρ (a, 1) = ρ (a, 1) * ρ (1, a₀) := by
      have h : ((1, a₀) : A5 × A5) * (a, 1) = (a, 1) * (1, a₀) := by ext <;> simp
      simpa only [map_mul] using congrArg ρ h
    have hu1 : ρ (a, 1) ≠ 1 := by
      intro h
      apply ha1
      have h' : (σ (a, 1) : V →ₗ[ZMod 2] V) = 1 := h
      have hσa1 : σ (a, 1) = 1 := by
        ext v
        simpa using congrArg (fun f : V →ₗ[ZMod 2] V => f v) h'
      have hpair : ((a, 1) : A5 × A5) = 1 := hσ (hσa1.trans (map_one σ).symm)
      simpa using congrArg Prod.fst hpair
    exact inner_free (ρ (a, 1)) (ρ (1, a₀)) hu hβ5 hcomm hfixB h8 hu1
  · have hp2 : ((1, a) : A5 × A5) ^ 2 = 1 := by
      ext <;> simp [Prod.pow_fst, Prod.pow_snd, ha2]
    have hu : (ρ (1, a)) ^ 2 = 1 := by rw [← map_pow, hp2, map_one]
    have hp5 : ((a₀, 1) : A5 × A5) ^ 5 = 1 := by
      ext <;> simp [Prod.pow_fst, Prod.pow_snd, ha0]
    have hβ5 : (ρ (a₀, 1)) ^ 5 = 1 := by rw [← map_pow, hp5, map_one]
    have hcomm : ρ (a₀, 1) * ρ (1, a) = ρ (1, a) * ρ (a₀, 1) := by
      have h : ((a₀, 1) : A5 × A5) * (1, a) = (1, a) * (a₀, 1) := by ext <;> simp
      simpa only [map_mul] using congrArg ρ h
    have hu1 : ρ (1, a) ≠ 1 := by
      intro h
      apply ha1
      have h' : (σ (1, a) : V →ₗ[ZMod 2] V) = 1 := h
      have hσa1 : σ (1, a) = 1 := by
        ext v
        simpa using congrArg (fun f : V →ₗ[ZMod 2] V => f v) h'
      have hpair : ((1, a) : A5 × A5) = 1 := hσ (hσa1.trans (map_one σ).symm)
      simpa using congrArg Prod.snd hpair
    exact inner_free (ρ (1, a)) (ρ (a₀, 1)) hu hβ5 hcomm hfixA h8 hu1

end CFSG.EvenSporadicStandard.HNRecog.ML1
