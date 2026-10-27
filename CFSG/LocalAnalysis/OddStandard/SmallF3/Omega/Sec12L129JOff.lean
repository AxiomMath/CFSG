module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12L129JH
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12L129JTv
public import CFSG.GroupTheory.ElemAbelianClosure

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Open

theorem sec12J_offender {W Γ : Type} [Group W] [Finite W] [Group Γ] [Finite Γ]
    {ψ : Γ →* MulAut W} {φ : Sec12SL × Sec12SL →* Γ} (hS : Sec12Act ψ φ)
    (hψ : Function.Injective ψ) (hE : (MonoidHom.range φ).Normal)
    (hidx : (MonoidHom.range φ).index = 2 ∨ (MonoidHom.range φ).index = 6)
    {X : Type} [Finite X] (j : X → W) (hj : Function.Injective j) {Fb : Subgroup Γ}
    (hFb : IsElemAbelian 2 Fb) (hne : Fb ≠ ⊥)
    (hfix : ∀ b ∈ Fb, ∀ x : X, ψ b (j x) = j x) : Nat.card X * Nat.card Fb ≤ 128 := by
  haveI : (MonoidHom.range φ).Normal := hE
  have hrel : (MonoidHom.range φ).relIndex Fb ≤ 2 :=
    sec12J_relIndex_le_two (MonoidHom.range φ) Fb hidx hFb.isPGroup
  have hcard := sec12J_card_inf_mul_relIndex (MonoidHom.range φ) Fb
  by_cases hΨ : Fb ⊓ MonoidHom.range φ = ⊥
  ·
    rw [hΨ, Subgroup.card_bot, one_mul] at hcard
    obtain ⟨y, hy1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
    have hy2 : (y : Γ) * (y : Γ) = 1 := by
      rw [← pow_two]
      exact hFb.2 y y.2
    have hyne : (y : Γ) ≠ 1 := fun h => hy1 (Subtype.ext h)
    have hTv := sec12J_transvection hS hψ hE hy2 hyne
    have hX : Nat.card X ≤ Nat.card {w : W // ψ (y : Γ) w = w} := by
      refine Nat.card_le_card_of_injective (fun x => ⟨j x, hfix y y.2 x⟩) ?_
      intro a b hab
      exact hj (congrArg (fun z : {w : W // ψ (y : Γ) w = w} => z.1) hab)
    calc Nat.card X * Nat.card Fb ≤ 64 * 2 := by
          refine Nat.mul_le_mul (hX.trans hTv) ?_
          rw [← hcard]
          exact hrel
      _ = 128 := by norm_num
  ·
    set Ψ : Subgroup (Sec12SL × Sec12SL) := (Fb ⊓ MonoidHom.range φ).comap φ with hΨdef
    have hle : Fb ⊓ MonoidHom.range φ ≤ MonoidHom.range φ := inf_le_right
    have hmap : Ψ.map φ = Fb ⊓ MonoidHom.range φ := by
      rw [hΨdef, Subgroup.map_comap_eq, inf_eq_right.mpr hle]
    have hΨcard : Nat.card Ψ = Nat.card (Fb ⊓ MonoidHom.range φ : Subgroup Γ) := by
      rw [← hmap]
      exact (Subgroup.card_map_of_injective hS.inj).symm
    have hΨel : IsElemAbelian 2 Ψ := (hFb.mono inf_le_left).comap hS.inj
    have hΨne : Ψ ≠ ⊥ := by
      intro hbot
      apply hΨ
      rw [← hmap, hbot, Subgroup.map_bot]
    have hstar := sec12J_hstar hS hΨel hΨne
    have hX : Nat.card X ≤ Nat.card {w : W // ∀ p ∈ Ψ, ψ (φ p) w = w} := by
      refine Nat.card_le_card_of_injective
        (fun x => ⟨j x, fun p hp => hfix (φ p) hp.1 x⟩) ?_
      intro a b hab
      exact hj (congrArg (fun z : {w : W // ∀ p ∈ Ψ, ψ (φ p) w = w} => z.1) hab)
    have hFb2 : Nat.card Fb ≤ 2 * Nat.card Ψ := by
      rw [hΨcard, ← hcard]
      calc Nat.card (Fb ⊓ MonoidHom.range φ : Subgroup Γ) *
            (MonoidHom.range φ).relIndex Fb
          ≤ Nat.card (Fb ⊓ MonoidHom.range φ : Subgroup Γ) * 2 := Nat.mul_le_mul_left _ hrel
        _ = 2 * Nat.card (Fb ⊓ MonoidHom.range φ : Subgroup Γ) := mul_comm _ _
    calc Nat.card X * Nat.card Fb
        ≤ Nat.card {w : W // ∀ p ∈ Ψ, ψ (φ p) w = w} * (2 * Nat.card Ψ) :=
          Nat.mul_le_mul hX hFb2
      _ = 2 * (Nat.card Ψ * Nat.card {w : W // ∀ p ∈ Ψ, ψ (φ p) w = w}) := by ring
      _ ≤ 2 * 64 := Nat.mul_le_mul_left 2 hstar
      _ = 128 := by norm_num

end CFSG.OddStandard.SmallF3.Omega
