module

public import CFSG.GH74.GLS.Stage4.T2HCard
public import Mathlib.GroupTheory.IsPerfect
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar

public section

namespace CFSG.GH74.GLS.Stage4.Rest

open Subgroup
open scoped commutatorElement

section Abs

variable {Γ : Type} [Group Γ]

theorem nonabelian_normal_contains (S : Subgroup Γ) [S.Normal] (hperf : ⁅S, S⁆ = S)
    (hq : ∀ T : Subgroup Γ, T ≤ S → (∀ s ∈ S, ∀ t ∈ T, s * t * s⁻¹ ∈ T) →
      (∀ t ∈ T, ∀ s ∈ S, t * s = s * t) ∨ T = S)
    (hC : ∀ g h : Γ, (∀ s ∈ S, g * s = s * g) → (∀ s ∈ S, h * s = s * h) → g * h = h * g)
    (M : Subgroup Γ) [M.Normal] (hMnc : ∃ a ∈ M, ∃ b ∈ M, a * b ≠ b * a) : S ≤ M := by
  set T : Subgroup Γ := M ⊓ S with hT
  have hTS : T ≤ S := inf_le_right
  have hTn : ∀ s ∈ S, ∀ t ∈ T, s * t * s⁻¹ ∈ T := fun s hs t ht =>
    ⟨Subgroup.Normal.conj_mem inferInstance t ht.1 s, S.mul_mem (S.mul_mem hs ht.2) (S.inv_mem hs)⟩
  rcases hq T hTS hTn with hcen | hTeq
  · exfalso
    have hTc : ∀ t ∈ T, ∀ t' ∈ T, t * t' = t' * t := fun t ht t' ht' => hcen t ht t' (hTS ht')
    let _ : CommGroup ↥T :=
      { (inferInstance : Group ↥T) with mul_comm := fun a b => Subtype.ext (hTc a a.2 b b.2) }
    have hMS : ∀ m ∈ M, ∀ s ∈ S, m * s = s * m := by
      intro m hm
      let c : ↥S →* ↥T :=
        { toFun := fun s => ⟨m * s * m⁻¹ * (s : Γ)⁻¹, by
            refine ⟨?_, ?_⟩
            · have h1 : (s : Γ) * m⁻¹ * (s : Γ)⁻¹ ∈ M :=
                Subgroup.Normal.conj_mem inferInstance m⁻¹ (M.inv_mem hm) s
              have := M.mul_mem hm h1
              simpa [mul_assoc] using this
            · have h1 : m * (s : Γ) * m⁻¹ ∈ S := Subgroup.Normal.conj_mem inferInstance (s : Γ) s.2 m
              exact S.mul_mem h1 (S.inv_mem s.2)⟩
          map_one' := by
            apply Subtype.ext
            simp
          map_mul' := by
            intro s s'
            apply Subtype.ext
            have hc' : ((s' : Γ) : Γ) ∈ S := s'.2
            have hct : m * (s' : Γ) * m⁻¹ * (s' : Γ)⁻¹ ∈ T := by
              refine ⟨?_, ?_⟩
              · have h1 : (s' : Γ) * m⁻¹ * (s' : Γ)⁻¹ ∈ M :=
                  Subgroup.Normal.conj_mem inferInstance m⁻¹ (M.inv_mem hm) s'
                have := M.mul_mem hm h1
                simpa [mul_assoc] using this
              · have h1 : m * (s' : Γ) * m⁻¹ ∈ S := Subgroup.Normal.conj_mem inferInstance (s' : Γ) s'.2 m
                exact S.mul_mem h1 (S.inv_mem s'.2)
            have hcs := hcen _ hct (s : Γ) s.2
            show m * ((s : Γ) * (s' : Γ)) * m⁻¹ * ((s : Γ) * (s' : Γ))⁻¹ =
              (m * (s : Γ) * m⁻¹ * (s : Γ)⁻¹) * (m * (s' : Γ) * m⁻¹ * (s' : Γ)⁻¹)
            calc m * ((s : Γ) * (s' : Γ)) * m⁻¹ * ((s : Γ) * (s' : Γ))⁻¹
                = (m * (s : Γ) * m⁻¹ * (s : Γ)⁻¹) *
                  ((s : Γ) * (m * (s' : Γ) * m⁻¹ * (s' : Γ)⁻¹) * (s : Γ)⁻¹) := by group
              _ = (m * (s : Γ) * m⁻¹ * (s : Γ)⁻¹) * (m * (s' : Γ) * m⁻¹ * (s' : Γ)⁻¹) := by
                  rw [← hcs]; group }
      have hperf' : commutator ↥S = ⊤ := by
        have : Group.IsPerfect ↥S := Subgroup.isPerfect_iff.2 hperf
        exact this.commutator_eq_top
      intro s hs
      have hker : (⟨s, hs⟩ : ↥S) ∈ c.ker := by
        have := Abelianization.commutator_subset_ker c
        rw [hperf'] at this
        exact this (Subgroup.mem_top _)
      have h1 : m * s * m⁻¹ * s⁻¹ = 1 := congrArg Subtype.val hker
      calc m * s = (m * s * m⁻¹ * s⁻¹) * s * m := by group
        _ = s * m := by rw [h1, one_mul]
    obtain ⟨a, ha, b, hb, hab⟩ := hMnc
    exact hab (hC a b (fun s hs => hMS a ha s hs) (fun s hs => hMS b hb s hs))
  · exact hTeq ▸ inf_le_left

theorem card_eq_of_perfect_normal [Finite Γ] (S N : Subgroup Γ) [S.Normal] [N.Normal]
    (hNS : N ⊓ S = ⊥) (hab : ∀ x y : Γ, ⁅x, y⁆ ∈ S) (hperf : ⁅S, S⁆ = S)
    (hq : ∀ T : Subgroup Γ, T ≤ S → (∀ s ∈ S, ∀ t ∈ T, s * t * s⁻¹ ∈ T) →
      (∀ t ∈ T, ∀ s ∈ S, t * s = s * t) ∨ T = S)
    (hC : ∀ g h : Γ, (∀ s ∈ S, g * s = s * g) → (∀ s ∈ S, h * s = s * h) → g * h = h * g)
    (M : Subgroup Γ) [M.Normal] (hNM : N ≤ M) (hMperf : ⁅M, M⁆ ⊔ N = M)
    (hMnc : ∃ a ∈ M, ∃ b ∈ M, a * b ≠ b * a) :
    M = S ⊔ N ∧ Nat.card ↥M = Nat.card ↥S * Nat.card ↥N := by
  have hSM : S ≤ M := nonabelian_normal_contains S hperf hq hC M hMnc
  have hcomm_le : ⁅M, M⁆ ≤ S := by
    rw [Subgroup.commutator_le]
    intro a _ b _
    exact hab a b
  have hMeq : M = S ⊔ N :=
    le_antisymm (by rw [← hMperf]; exact sup_le_sup_right hcomm_le N) (sup_le hSM hNM)
  refine ⟨hMeq, ?_⟩
  have hc : ∀ x ∈ S, ∀ y ∈ N, x * y = y * x := by
    intro x hx y hy
    have h1 : x * y * x⁻¹ * y⁻¹ ∈ N :=
      N.mul_mem (Subgroup.Normal.conj_mem inferInstance y hy x) (N.inv_mem hy)
    have h2 : x * y * x⁻¹ * y⁻¹ ∈ S := by
      have := S.mul_mem hx (Subgroup.Normal.conj_mem inferInstance x⁻¹ (S.inv_mem hx) y)
      simpa [mul_assoc] using this
    have h3 : x * y * x⁻¹ * y⁻¹ ∈ N ⊓ S := ⟨h1, h2⟩
    rw [hNS, Subgroup.mem_bot] at h3
    calc x * y = (x * y * x⁻¹ * y⁻¹) * (y * x) := by group
      _ = y * x := by rw [h3, one_mul]
  have hd : S ⊓ N = ⊥ := by rw [inf_comm]; exact hNS
  rw [hMeq]
  exact t2H_card_sup_comm_disjoint S N hc hd

end Abs

end CFSG.GH74.GLS.Stage4.Rest
