module

public import CFSG.LargeExtraspecial.S5Q
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LargeExtraspecial.S6ThreeC
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S9

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6 CFSG.LargeExtraspecial.OrthoF2

universe u

section Abstract

variable {R P A : Type*} [Group R] [Group P] [Group A]

theorem forall_comm_of_exists_trivial (π : R →* P) (ρ : R →* A) {M₀ : Subgroup P}
    (hM₀ : ∀ m ∈ M₀, ∃ x : R, π x = m)
    (hnorm : ∀ x : R, ∀ m ∈ M₀, π x * m * (π x)⁻¹ ∈ M₀) (hsimp : IsSimpleGroup M₀)
    (hidx : ∀ x y : R, π x ∉ M₀ → π y ∉ M₀ → π (x⁻¹ * y) ∈ M₀)
    (hker : ∀ n : R, π n = 1 → ∀ s : R, Commute (ρ n) (ρ s))
    {τ : R} (hτ : ρ τ = 1) (hτ1 : π τ ≠ 1)
    (hcen : (∀ x : R, π x * π τ = π τ * π x) → π τ = 1) :
    ∀ r s : R, Commute (ρ r) (ρ s) := by
  let K : Subgroup R :=
    { carrier := {r | ∀ s, Commute (ρ r) (ρ s)}
      mul_mem' := fun {a b} ha hb s => by
        rw [map_mul]
        exact (ha s).mul_left (hb s)
      one_mem' := fun s => by
        change Commute (ρ 1) (ρ s)
        rw [map_one]
        exact Commute.one_left _
      inv_mem' := fun {a} ha s => by
        rw [map_inv]
        exact (ha s).inv_left }
  have hmemK : ∀ r, r ∈ K ↔ ∀ s, Commute (ρ r) (ρ s) := fun r => Iff.rfl
  have hKn : ∀ x r, r ∈ K → x * r * x⁻¹ ∈ K := by
    intro x r hr s
    have e : ρ (x * r * x⁻¹) = ρ r := by
      rw [map_mul, map_mul, map_inv, ((hr x).symm).eq, mul_assoc, mul_inv_cancel, mul_one]
    rw [e]
    exact hr s
  have hτK : τ ∈ K := fun s => by rw [hτ]; exact Commute.one_left _
  have hA : ∃ k ∈ K, π k ∈ M₀ ∧ π k ≠ 1 := by
    by_contra hcon
    push Not at hcon
    apply hτ1
    apply hcen
    intro x
    have h1 : π τ ∉ M₀ := fun h => hτ1 (hcon τ hτK h)
    have h2 : π (x * τ * x⁻¹) ∉ M₀ := by
      intro h
      apply h1
      have := hnorm x⁻¹ _ h
      rwa [map_inv, inv_inv, map_mul, map_mul, map_inv,
        show (π x)⁻¹ * (π x * π τ * (π x)⁻¹) * π x = π τ by group] at this
    have h3 := hcon _ (K.mul_mem (K.inv_mem hτK) (hKn x τ hτK)) (hidx τ (x * τ * x⁻¹) h1 h2)
    rw [map_mul, map_inv, map_mul, map_mul, map_inv] at h3
    calc π x * π τ = π τ * ((π τ)⁻¹ * (π x * π τ * (π x)⁻¹)) * π x := by group
      _ = π τ * π x := by rw [h3, mul_one]
  have hB : ∀ m ∈ M₀, ∃ k ∈ K, π k = m := by
    let Z : Subgroup M₀ :=
      { carrier := {m | ∃ k ∈ K, π k = m}
        mul_mem' := by
          rintro _ _ ⟨k₁, hk₁, h₁⟩ ⟨k₂, hk₂, h₂⟩
          exact ⟨k₁ * k₂, K.mul_mem hk₁ hk₂, by rw [map_mul, h₁, h₂]; rfl⟩
        one_mem' := ⟨1, K.one_mem, by rw [map_one]; rfl⟩
        inv_mem' := by
          rintro _ ⟨k, hk, h⟩
          exact ⟨k⁻¹, K.inv_mem hk, by rw [map_inv, h]; rfl⟩ }
    have hZn : Z.Normal := by
      refine ⟨fun m hm c => ?_⟩
      obtain ⟨k, hk, hkm⟩ := hm
      obtain ⟨x, hx⟩ := hM₀ c c.2
      refine ⟨x * k * x⁻¹, hKn x k hk, ?_⟩
      rw [map_mul, map_mul, map_inv, hx, hkm]
      rfl
    rcases hsimp.eq_bot_or_eq_top_of_normal Z with hbot | htop
    · exfalso
      obtain ⟨k, hk, hkM, hk1⟩ := hA
      have hmem : (⟨π k, hkM⟩ : M₀) ∈ Z := ⟨k, hk, rfl⟩
      rw [hbot, mem_bot] at hmem
      exact hk1 (congrArg Subtype.val hmem)
    · intro m hm
      have hmem : (⟨m, hm⟩ : M₀) ∈ Z := by rw [htop]; exact mem_top _
      exact hmem
  have hC : ∀ r, π r ∈ M₀ → r ∈ K := by
    intro r hr
    obtain ⟨k, hk, hkr⟩ := hB _ hr
    have hn : k⁻¹ * r ∈ K := hker _ (by rw [map_mul, map_inv, hkr, inv_mul_cancel])
    have := K.mul_mem hk hn
    rwa [mul_inv_cancel_left] at this
  intro r s
  by_cases hr : π r ∈ M₀
  · exact hC r hr s
  by_cases hs : π s ∈ M₀
  · exact (hC s hs r).symm
  have hrs := hC _ (hidx r s hr hs)
  have e : ρ s = ρ r * ρ (r⁻¹ * s) := by rw [← map_mul, mul_inv_cancel_left]
  rw [e]
  exact (Commute.refl (ρ r)).mul_right (hrs r).symm

end Abstract

variable {G : Type u} [Group G] [Finite G] {S : Setting G} {g : G}

section Card

variable (H : Hyp4 S g) (C : Cons311 S g) {t : S.O} (ht : t ∈ S.Lbar g) (ht1 : t ≠ 1)
  (hVQ : ¬ V S g t ≤ S.Qa g) (hP : PGL25Case H C ht ht1 hVQ)
include H C ht ht1 hVQ hP

theorem card_LmodN_pgl25 : Nat.card (LmodN S g t) = 4 := by
  have h1 := card_LmodN_ge H C ht ht1 hVQ
  have h2 := S5.card_LmodN_le_four_of_tau_not_mem H C ht ht1 hVQ hP.finrank_eq hP.tau_not_mem
  rw [hP.finrank_eq] at h1
  norm_num at h1
  omega

theorem card_Abar_mul_four_pgl25 :
    Nat.card (S.Lbar g ⊓ Nbar S g t : Subgroup S.O) * 4 = 2 ^ (S.width - 1) := by
  have h1 := card_Lbar_eq_mul H.conj_mem ht (t := t)
  rw [C.card_Lbar, card_LmodN_pgl25 H C ht ht1 hVQ hP] at h1
  rw [h1, mul_comm]

theorem four_lt_width_pgl25 (hA : S.Lbar g ⊓ Nbar S g t ≠ zpowers t) : 4 < S.width := by
  have hcard := card_Abar_mul_four_pgl25 H C ht ht1 hVQ hP
  have htt : t * t = 1 := mul_self_of_mem_Lbar S H.conj_mem ht
  have hto : orderOf t = 2 := orderOf_eq_prime (by rw [pow_two]; exact htt) ht1
  have hle : zpowers t ≤ S.Lbar g ⊓ Nbar S g t := by
    rw [zpowers_le]
    exact ⟨ht, self_mem_Nbar H ht⟩
  have hlt : Nat.card (zpowers t) < Nat.card (S.Lbar g ⊓ Nbar S g t : Subgroup S.O) :=
    Subgroup.card_lt_of_lt (lt_of_le_of_ne hle (Ne.symm hA))
  rw [Nat.card_zpowers, hto] at hlt
  by_contra hn
  push Not at hn
  have h8 : 2 ^ (S.width - 1) ≤ 8 :=
    calc 2 ^ (S.width - 1) ≤ 2 ^ 3 := Nat.pow_le_pow_right (by norm_num) (by omega)
      _ = 8 := by norm_num
  omega

end Card

end CFSG.LargeExtraspecial.S9
