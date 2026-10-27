module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoCo1.Unique
public import CFSG.LocalAnalysis.EvenSporadicStandard.CentralTwoRowsLarge

public section

namespace CFSG.EvenSporadicStandard.TwoCo1

open Subgroup CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.Open

theorem nonempty_mulEquiv_of_doubleCovers_Co1
    {L₁ L₂ : Type} [Group L₁] [Finite L₁] [Group L₂] [Finite L₂]
    (h₁ : Group.IsPerfect L₁) (h₂ : Group.IsPerfect L₂)
    (hc₁ : Nat.card (center L₁) = 2) (hc₂ : Nat.card (center L₂) = 2)
    (hq₁ : IsSporadic (L₁ ⧸ center L₁) .Co1) (hq₂ : IsSporadic (L₂ ⧸ center L₂) .Co1) :
    Nonempty (L₁ ≃* L₂) := by
  obtain ⟨e₁⟩ := hq₁
  obtain ⟨e₂⟩ := hq₂
  have hsC : IsSimpleGroup (Carrier .Co1) := CFSG.Sporadic.Co1.isSimpleGroup_Co1
  have hsimple : IsSimpleGroup (L₁ ⧸ center L₁) := MulEquiv.isSimpleGroup e₁
  set X := L₁ ⧸ center L₁ with hX
  have hnontriv : Nontrivial X := hsimple.toNontrivial
  have hperf : Group.IsPerfect X := by
    rw [Group.isPerfect_def]
    have hsurj : Function.Surjective (QuotientGroup.mk' (center L₁)) :=
      QuotientGroup.mk'_surjective _
    have := Subgroup.map_commutator (⊤ : Subgroup L₁) ⊤ (QuotientGroup.mk' (center L₁))
    rw [Subgroup.map_top_of_surjective _ hsurj,
      show ⁅(⊤ : Subgroup L₁), ⊤⁆ = _root_.commutator L₁ from rfl, Group.isPerfect_def.1 h₁,
      Subgroup.map_top_of_surjective _ hsurj] at this
    exact this.symm
  have hcenterX : center X = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center X) with h | h
    · exact h
    · exfalso
      have hab : ∀ x y : X, x * y = y * x := fun x y =>
        (mem_center_iff.1 (h ▸ mem_top x) y).symm
      have hbot : _root_.commutator X ≤ ⊥ := by
        show ⁅(⊤ : Subgroup X), ⊤⁆ ≤ ⊥
        exact commutator_le.2 fun a _ b _ => by
          rw [mem_bot, commutatorElement_eq_one_iff_mul_comm]
          exact hab a b
      rw [Group.isPerfect_def.1 hperf] at hbot
      obtain ⟨x, hx⟩ := exists_ne (1 : X)
      exact hx (mem_bot.1 (hbot (mem_top x)))
  let e' : L₂ ⧸ center L₂ ≃* X := e₂.trans e₁.symm
  let π₁ : L₁ →* X := QuotientGroup.mk' (center L₁)
  let π₂ : L₂ →* X := e'.toMonoidHom.comp (QuotientGroup.mk' (center L₂))
  have hπ₁ : Function.Surjective π₁ := QuotientGroup.mk'_surjective _
  have hπ₂ : Function.Surjective π₂ :=
    e'.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker₁ : π₁.ker = center L₁ := QuotientGroup.ker_mk' _
  have hker₂ : π₂.ker = center L₂ := by
    ext x
    simp only [MonoidHom.mem_ker, π₂, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      QuotientGroup.mk'_apply]
    rw [map_eq_one_iff _ e'.injective, QuotientGroup.eq_one_iff]
  have hbound : ∀ (F : Type) [Group F] [Finite F], Group.IsPerfect F → ∀ (ρ : F →* X),
      Function.Surjective ρ → ρ.ker ≤ center F → (∀ k ∈ ρ.ker, k ^ 2 = 1) →
        Nat.card ρ.ker ≤ 2 := by
    intro F _ _ hF ρ hρ hle hsq
    have hcen : center F = ρ.ker := by
      refine le_antisymm (fun z hz => ?_) hle
      rw [MonoidHom.mem_ker, ← mem_bot, ← hcenterX, mem_center_iff]
      intro x
      obtain ⟨y, rfl⟩ := hρ x
      rw [← map_mul, ← map_mul, mem_center_iff.1 hz y]
    have equ : F ⧸ center F ≃* X :=
      (QuotientGroup.quotientMulEquivOfEq hcen).trans
        (QuotientGroup.quotientKerEquivOfSurjective ρ hρ)
    have hq : CFSG.Open.IsQuasisimple F := ⟨Group.isPerfect_def.1 hF, MulEquiv.isSimpleGroup equ⟩
    have hP : IsPGroup 2 (center F) := fun g => ⟨1, by
      have := hsq g.1 (hcen ▸ g.2)
      exact Subtype.ext (by simpa using this)⟩
    have hsp : IsSporadic (F ⧸ center F) .Co1 := ⟨equ.trans e₁⟩
    have hdvd := (CFSG.EvenSporadicStandard.rowBound_Co1 F hq hP hsp).1
    rw [← hcen]
    exact Nat.le_of_dvd (by norm_num) hdvd
  obtain ⟨e, -⟩ := exists_mulEquiv_of_double_covers hperf h₁ h₂ π₁ π₂ hπ₁ hπ₂
    (by rw [hker₁]; exact hc₁) (by rw [hker₂]; exact hc₂) hker₁.le hker₂.le hbound
  exact ⟨e⟩

end CFSG.EvenSporadicStandard.TwoCo1
