module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabAutIrrDefs
public import CFSG.LocalAnalysis.ComponentClassification.PerfectAutomorphisms

public section

namespace CFSG.AGLEmbedding.BlockCyc

open CFSG.AGLEmbedding.ParabAutIrr

@[expose] def Aut3Le (Y : Type*) [Group Y] : Prop :=
  ∀ W : Subgroup (MulAut Y), IsPGroup 3 W → Nat.card W ≤ 3

theorem aut3Le_of_mulEquiv {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y) (h : Aut3Le X) :
    Aut3Le Y := by
  intro W hW
  have h1 := h (W.map (MulAut.congr e).symm.toMonoidHom) (hW.map _)
  rwa [Subgroup.card_map_of_injective (MulAut.congr e).symm.injective] at h1

theorem aut3Le_of_center_quotient {Q : Type*} [Group Q] [Group.IsPerfect Q]
    (h : Aut3Le (Q ⧸ Subgroup.center Q)) : Aut3Le Q := by
  intro W hW
  have hinj := CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom_injective Q
  have h1 := h (W.map (CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom Q))
    (hW.map _)
  rwa [Subgroup.card_map_of_injective hinj] at h1

theorem card_le_three_of_dvd {A : Type*} [Group A] {W : Subgroup A} (hW : IsPGroup 3 W) {N : ℕ}
    (hdvd : Nat.card W ∣ N) (hN : ¬ 9 ∣ N) : Nat.card W ≤ 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hN0 : N ≠ 0 := fun h0 => hN (h0 ▸ dvd_zero 9)
  have : Finite W := Nat.finite_of_card_ne_zero fun h0 => hN0 (by
    rw [h0] at hdvd
    exact zero_dvd_iff.1 hdvd)
  obtain ⟨k, hk⟩ := hW.exists_card_eq
  by_contra hgt
  push Not at hgt
  have hk2 : 2 ≤ k := by
    by_contra hk2
    have h3k : 3 ^ k ≤ 3 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have : 9 ∣ Nat.card W := by
    rw [hk]
    exact (pow_dvd_pow 3 hk2 : 3 ^ 2 ∣ 3 ^ k)
  exact hN (this.trans hdvd)

theorem aut3Le_of_not_nine_dvd {Y : Type*} [Group Y] [Finite Y]
    (h : ¬ 9 ∣ Nat.card (MulAut Y)) : Aut3Le Y := fun W hW =>
  card_le_three_of_dvd hW (Subgroup.card_subgroup_dvd_card W) h

theorem aut3Le_of_outPInner {Y : Type*} [Group Y] [Finite Y] (hout : OutPInner Y 3)
    (hY : ¬ 9 ∣ Nat.card Y) : Aut3Le Y := fun W hW =>
  card_le_three_of_dvd hW ((Subgroup.card_dvd_of_le (hout W hW)).trans (Subgroup.card_range_dvd _))
    hY

theorem relIndex_le_three_of_aut3Le {A : Type*} [Group A] {Q V : Subgroup A}
    (hV : V ≤ Subgroup.normalizer (Q : Set A)) (hVp : IsPGroup 3 V) (h : Aut3Le Q) :
    (V ⊓ Subgroup.centralizer (Q : Set A)).relIndex V ≤ 3 := by
  let ρ : V →* MulAut Q := (Subgroup.normalizerMonoidHom Q).comp (Subgroup.inclusion hV)
  have hker : ρ.ker = (V ⊓ Subgroup.centralizer (Q : Set A)).subgroupOf V := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf,
      Subgroup.mem_centralizer_iff]
    constructor
    · intro hx
      refine ⟨x.2, fun q hq => ?_⟩
      have := congrArg (fun φ : MulAut Q => ((φ ⟨q, hq⟩ : Q) : A)) hx
      simp only [ρ, MonoidHom.comp_apply, Subgroup.normalizerMonoidHom_apply_apply_coe,
        MulAut.one_apply] at this
      change (x : A) * q * (x : A)⁻¹ = q at this
      calc q * (x : A) = ((x : A) * q * (x : A)⁻¹) * (x : A) := by rw [this]
        _ = (x : A) * q := by group
    · rintro ⟨-, hx⟩
      ext ⟨q, hq⟩
      simp only [ρ, MonoidHom.comp_apply, Subgroup.normalizerMonoidHom_apply_apply_coe,
        MulAut.one_apply]
      change (x : A) * q * (x : A)⁻¹ = q
      rw [mul_inv_eq_iff_eq_mul]
      exact (hx q hq).symm
  have hrange : IsPGroup 3 ρ.range := hVp.of_surjective ρ.rangeRestrict ρ.rangeRestrict_surjective
  have h1 := h ρ.range hrange
  rw [Subgroup.relIndex, ← hker, Subgroup.index_ker]
  exact h1

theorem exists_perfect_of_perfect_image {A B : Type*} [Group A] [Group B] [Finite A] (f : A →* B)
    {P : Subgroup B} (hP : ⁅P, P⁆ = P) (hPf : P ≤ f.range) :
    ∃ R : Subgroup A, ⁅R, R⁆ = R ∧ R.map f = P := by
  classical
  have hne : ∃ R : Subgroup A, R.map f = P :=
    ⟨P.comap f, by rw [Subgroup.map_comap_eq, inf_eq_right.2 hPf]⟩
  obtain ⟨R, hR, hmin⟩ := WellFounded.has_min (wellFounded_lt (α := Subgroup A))
    {R : Subgroup A | R.map f = P} hne
  refine ⟨R, ?_, hR⟩
  have hle : ⁅R, R⁆ ≤ R := Subgroup.commutator_le.2 fun g₁ h₁ g₂ h₂ => by
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem h₁ h₂) (inv_mem h₁)) (inv_mem h₂)
  have hmap : (⁅R, R⁆).map f = P := by rw [Subgroup.map_commutator, hR, hP]
  exact eq_of_le_of_not_lt hle (hmin _ hmap)

end CFSG.AGLEmbedding.BlockCyc
