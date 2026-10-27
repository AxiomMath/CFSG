module

public import CFSG.LargeExtraspecial.S13Fbar
public import CFSG.LargeExtraspecial.S11Basic

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S13

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6 CFSG.LargeExtraspecial.S10

variable {G : Type*} [Group G] [Finite G] {S : Setting G} {g g' : G} {K : Subgroup S.O}

variable (S) in
structure Hyp13 (g : G) (K : Subgroup S.O) : Prop where
  H : Hyp4 S g
  hNo : NoA2 S g
  C : Cons311 S g
  noAll : S11.NoA2All S
  irr : ¬ S.IsReducible
  seven_le : 7 ≤ S.width
  K_le : K ≤ S.Mbar
  card_K : Nat.card K = 3
  normal : NormalInMbar S K
  fpf : FixFree S K
  one : ∀ τ ∈ Ebar S g K, τ ≠ 1 → (∀ X ∈ Dset S g τ, Ebar S g K ≤ X) ∨ Hyp10 S g τ
  weak : ∀ m ∈ S.Mbar, (∀ e ∈ Ebar S g K, m * e * m⁻¹ ∈ normalizer (Ebar S g K : Set S.O)) →
    ∀ e ∈ Ebar S g K, m * e * m⁻¹ ∈ Ebar S g K
  sec10 : ∃ t : S.O, Hyp10 S g t ∧ (∀ x ∈ Nbar S g t, ∀ k ∈ K, k * x = x * k) ∧
    (∀ x ∈ Nbar S g t, ∀ y ∈ Nbar S g t, x * y * x⁻¹ * y⁻¹ ∈ zpowers t) ∧
    ∃ k : S.M, S.ρ k ∈ normalizer (S.Lbar g : Set S.O) ∧
      S.ρ k * t * (S.ρ k)⁻¹ ∈ S.Lbar g ⊓ Nbar S g t ∧ S.ρ k * t * (S.ρ k)⁻¹ ≠ t

theorem mem_normalizer_map_cK_iff {A : Subgroup S.O} (h : S.M) {x : S.O} :
    x ∈ normalizer ((A.map (cK S h) : Subgroup S.O) : Set S.O) ↔
      (S.ρ h)⁻¹ * x * S.ρ h ∈ normalizer (A : Set S.O) := by
  rw [mem_normalizer_iff, mem_normalizer_iff]
  constructor
  · intro hx y
    have := hx (S.ρ h * y * (S.ρ h)⁻¹)
    rw [mem_map_cK_iff, mem_map_cK_iff] at this
    simpa [mul_assoc] using this
  · intro hx y
    rw [mem_map_cK_iff, mem_map_cK_iff]
    have := hx ((S.ρ h)⁻¹ * y * S.ρ h)
    simpa [mul_assoc] using this

namespace Hyp13

variable (Y : Hyp13 S g K)
include Y

theorem haQ : g * S.z * g⁻¹ ∈ S.QG := Y.H.conj_mem

theorem hne : g * S.z * g⁻¹ ≠ S.z := Y.H.conj_ne

theorem mul {h : S.M} (hg : g' = (h : G) * g) : Hyp13 S g' K := by
  have hEc := Ebar_mul Y.normal hg
  have hρ : S.ρ h ∈ S.Mbar := MonoidHom.mem_range.mpr ⟨h, rfl⟩
  refine ⟨hyp4_mul Y.H hg, noA2_mul Y.hNo hg, cons311_mul Y.C hg, Y.noAll, Y.irr, Y.seven_le,
    Y.K_le, Y.card_K, Y.normal, Y.fpf, ?_, ?_, ?_⟩
  ·
    intro τ hτ hτ1
    rw [hEc, mem_map_cK_iff] at hτ
    set τ₀ := (S.ρ h)⁻¹ * τ * S.ρ h with hτ₀
    have hτeq : τ = S.ρ h * τ₀ * (S.ρ h)⁻¹ := by rw [hτ₀]; group
    have hτ₀1 : τ₀ ≠ 1 := fun e => hτ1 (by rw [hτeq, e]; group)
    rcases Y.one τ₀ hτ hτ₀1 with hD | hX
    · left
      intro X hX
      rw [hg, Dset_mul, hτeq, Dset_conj] at hX
      obtain ⟨X₀, hX₀, rfl⟩ := hX
      rw [hEc]
      exact map_mono (hD X₀ hX₀)
    · exact Or.inr (hyp10_mul hX hg hτeq)
  ·
    intro m hm hcond e he
    rw [hEc, mem_map_cK_iff] at he ⊢
    have hm₀ : (S.ρ h)⁻¹ * m * S.ρ h ∈ S.Mbar :=
      mul_mem (mul_mem (inv_mem hρ) hm) hρ
    have key := Y.weak _ hm₀ (fun e₁ he₁ => by
      have h1 := hcond (S.ρ h * e₁ * (S.ρ h)⁻¹) (by
        rw [hEc, mem_map_cK_iff]; simpa [mul_assoc] using he₁)
      rw [hEc, mem_normalizer_map_cK_iff] at h1
      simpa [mul_assoc] using h1) _ he
    simpa [mul_assoc] using key
  ·
    obtain ⟨t, X, hNK, hNc, k, hkN, hτA, hτt⟩ := Y.sec10
    have hNc' := Nbar_mul_conj X.haQ hg (rfl : S.ρ h * t * (S.ρ h)⁻¹ = _)
    refine ⟨S.ρ h * t * (S.ρ h)⁻¹, hyp10_mul X hg rfl, ?_, ?_, h * k * h⁻¹, ?_, ?_, ?_⟩
    · intro x hx k' hk'
      rw [hNc', mem_map_cK_iff] at hx
      have hk'' := Y.normal _ (inv_mem hρ) k' hk'
      rw [inv_inv] at hk''
      have e := hNK _ hx _ hk''
      calc k' * x = S.ρ h * (((S.ρ h)⁻¹ * k' * S.ρ h) * ((S.ρ h)⁻¹ * x * S.ρ h)) *
            (S.ρ h)⁻¹ := by group
        _ = S.ρ h * (((S.ρ h)⁻¹ * x * S.ρ h) * ((S.ρ h)⁻¹ * k' * S.ρ h)) * (S.ρ h)⁻¹ := by
            rw [e]
        _ = x * k' := by group
    · intro x hx x' hx'
      rw [hNc', mem_map_cK_iff] at hx hx'
      have e := hNc _ hx _ hx'
      rw [mem_zpowers_iff] at e ⊢
      obtain ⟨i, hi⟩ := e
      refine ⟨i, ?_⟩
      have h1 : (S.ρ h * t * (S.ρ h)⁻¹) ^ i = S.ρ h * t ^ i * (S.ρ h)⁻¹ := by
        have := map_zpow (MulAut.conj (S.ρ h)) t i
        simpa only [MulAut.conj_apply] using this.symm
      rw [h1, hi]
      group
    · rw [Lbar_mul' (S := S) hg, mem_normalizer_map_cK_iff]
      simpa [mul_assoc] using hkN
    · rw [Lbar_mul' (S := S) hg, Nbar_mul_conj X.haQ hg rfl,
        ← Subgroup.map_inf_eq _ _ _ (cK_injective h)]
      refine ⟨S.ρ k * t * (S.ρ k)⁻¹, hτA, ?_⟩
      simp [mul_assoc]
    · intro e
      apply hτt
      have e2 := congrArg (fun x => (S.ρ h)⁻¹ * x * S.ρ h) e
      simpa [mul_assoc] using e2

theorem pow_three {k : S.O} (hk : k ∈ K) : k ^ 3 = 1 := pow_three_eq_one Y.card_K hk

theorem exists_K : ∃ k ∈ K, k ≠ 1 := by
  by_contra h
  push Not at h
  have : K = ⊥ := (eq_bot_iff_forall K).mpr h
  have h3 := Y.card_K
  rw [this, card_bot] at h3
  omega

theorem card_Lbar : Nat.card (S.Lbar g) = 2 * Nat.card (Ebar S g K) :=
  card_Lbar_eq_two_mul Y.H Y.card_K Y.normal Y.fpf

theorem card_Ebar : Nat.card (Ebar S g K) = 2 ^ (S.width - 2) := by
  have h1 := Y.card_Lbar
  rw [Y.C.card_Lbar] at h1
  have h7 := Y.seven_le
  have e : 2 ^ (S.width - 1) = 2 * 2 ^ (S.width - 2) := by
    rw [show S.width - 1 = (S.width - 2) + 1 by omega, pow_succ]
    ring
  omega

theorem inv_of_not_mem {x : S.O} (hx : x ∈ S.Lbar g) (hxE : x ∉ Ebar S g K) :
    ∀ k ∈ K, x * k * x⁻¹ = k⁻¹ :=
  inv_of_not_mem_Ebar Y.card_K Y.normal hx hxE

theorem mul_mem_E {x y : S.O} (hx : x ∈ S.Lbar g) (hxE : x ∉ Ebar S g K) (hy : y ∈ S.Lbar g)
    (hyE : y ∉ Ebar S g K) : x * y ∈ Ebar S g K :=
  mul_mem_Ebar Y.card_K Y.normal hx hxE hy hyE

end Hyp13

end CFSG.LargeExtraspecial.S13
