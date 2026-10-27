module

public import CFSG.Certificates.Kernel.OrbRow.Tight
public import Mathlib.GroupTheory.Subgroup.Centralizer
import Mathlib.Tactic.Group

public section

namespace CFSG.KC.M24Three

open Subgroup CFSG.KC.OrbRow

variable {α : Type*}

theorem comm_of_mem_cent {t g : Equiv.Perm α} (hg : g ∈ centralizer ({t} : Set (Equiv.Perm α))) :
    g * t = t * g :=
  ((mem_centralizer_iff.1 hg) t (Set.mem_singleton t)).symm

theorem conj_mul_cent {t k c : Equiv.Perm α} (hc : c * t = t * c) :
    k * c * t * (k * c)⁻¹ = k * t * k⁻¹ := by
  calc k * c * t * (k * c)⁻¹ = k * (c * t) * c⁻¹ * k⁻¹ := by group
    _ = k * (t * c) * c⁻¹ * k⁻¹ := by rw [hc]
    _ = k * t * k⁻¹ := by group

theorem card_conj_mul_le (H : Subgroup (Equiv.Perm α)) [Finite H] (t : Equiv.Perm α)
    (s : Finset (Equiv.Perm α)) (hs : ∀ y ∈ s, ∃ h ∈ H, h * t * h⁻¹ = y) :
    s.card * Nat.card ↥(H ⊓ centralizer ({t} : Set (Equiv.Perm α))) ≤ Nat.card H := by
  choose f hfH hft using hs
  let F : s × ↥(H ⊓ centralizer ({t} : Set (Equiv.Perm α))) → H :=
    fun p => ⟨f p.1 p.1.2 * p.2, H.mul_mem (hfH _ _) (mem_inf.1 p.2.2).1⟩
  have hF : Function.Injective F := by
    rintro ⟨⟨x, hx⟩, ⟨g, hg⟩⟩ ⟨⟨y, hy⟩, ⟨g', hg'⟩⟩ he
    have he' : f x hx * g = f y hy * g' := congrArg Subtype.val he
    have hxy : x = y := by
      rw [← hft x hx, ← hft y hy, ← conj_mul_cent (comm_of_mem_cent (mem_inf.1 hg).2),
        ← conj_mul_cent (k := f y hy) (comm_of_mem_cent (mem_inf.1 hg').2), he']
    subst hxy
    have hgg : g = g' := mul_left_cancel he'
    subst hgg
    rfl
  have := Nat.card_le_card_of_injective F hF
  rwa [Nat.card_prod, Nat.card_eq_fintype_card (α := s), Fintype.card_coe] at this

theorem card_cent_le (P H : Subgroup (Equiv.Perm α)) [Finite P] [Finite H] (t : Equiv.Perm α)
    (b : α) (S : Finset α) (hS : ∀ g ∈ P ⊓ centralizer ({t} : Set (Equiv.Perm α)), g b ∈ S)
    (hH : ∀ g ∈ P ⊓ centralizer ({t} : Set (Equiv.Perm α)), g b = b → g ∈ H) :
    Nat.card ↥(P ⊓ centralizer ({t} : Set (Equiv.Perm α))) ≤
      S.card * Nat.card ↥(H ⊓ centralizer ({t} : Set (Equiv.Perm α))) := by
  classical
  set C := P ⊓ centralizer ({t} : Set (Equiv.Perm α))
  let r : α → Equiv.Perm α := fun x => if h : ∃ g ∈ C, g b = x then h.choose else 1
  have hr : ∀ g ∈ C, r (g b) ∈ C ∧ r (g b) b = g b := fun g hg => by
    have h : ∃ k ∈ C, k b = g b := ⟨g, hg, rfl⟩
    simp only [r, dif_pos h]
    exact h.choose_spec
  have hmem : ∀ g ∈ C, (r (g b))⁻¹ * g ∈ H ⊓ centralizer ({t} : Set (Equiv.Perm α)) := by
    intro g hg
    obtain ⟨hrC, hrb⟩ := hr g hg
    have hk : (r (g b))⁻¹ * g ∈ C := C.mul_mem (C.inv_mem hrC) hg
    have hfix : ((r (g b))⁻¹ * g) b = b := by
      set k := r (g b)
      rw [Equiv.Perm.mul_apply, ← hrb]
      exact Equiv.symm_apply_apply k b
    exact mem_inf.2 ⟨hH _ hk hfix, (mem_inf.1 hk).2⟩
  let F : C → S × ↥(H ⊓ centralizer ({t} : Set (Equiv.Perm α))) :=
    fun g => (⟨g.1 b, hS g.1 g.2⟩, ⟨(r (g.1 b))⁻¹ * g.1, hmem g.1 g.2⟩)
  have hF : Function.Injective F := by
    rintro ⟨g, hg⟩ ⟨g', hg'⟩ he
    have h1 : g b = g' b := congrArg (fun p => (p.1 : α)) he
    have h2 : (r (g b))⁻¹ * g = (r (g' b))⁻¹ * g' :=
      congrArg (fun p => (p.2 : Equiv.Perm α)) he
    rw [h1] at h2
    exact Subtype.ext (mul_left_cancel h2)
  have hfin : Finite ↥(H ⊓ centralizer ({t} : Set (Equiv.Perm α))) :=
    Finite.of_injective (Subgroup.inclusion (inf_le_left : H ⊓ _ ≤ H))
      (Subgroup.inclusion_injective _)
  have := Nat.card_le_card_of_injective F hF
  rwa [Nat.card_prod, Nat.card_eq_fintype_card (α := S), Fintype.card_coe] at this

theorem cent_fix3 {t g : Equiv.Perm α} (hg : g ∈ centralizer ({t} : Set (Equiv.Perm α))) {b : α}
    (hb : g b = b) : g b = b ∧ g (t b) = t b ∧ g (t (t b)) = t (t b) := by
  have hc := comm_of_mem_cent hg
  have h1 : g (t b) = t b := by
    rw [← Equiv.Perm.mul_apply, hc, Equiv.Perm.mul_apply, hb]
  refine ⟨hb, h1, ?_⟩
  rw [← Equiv.Perm.mul_apply, hc, Equiv.Perm.mul_apply, h1]

theorem cent_apply_supp {t g : Equiv.Perm α} (hg : g ∈ centralizer ({t} : Set (Equiv.Perm α)))
    {b : α} (hb : t b ≠ b) : t (g b) ≠ g b := by
  intro h
  apply hb
  have hc := comm_of_mem_cent hg
  have : g (t b) = g b := by rw [← Equiv.Perm.mul_apply, hc, Equiv.Perm.mul_apply, h]
  exact g.injective this

theorem finite_stabB (P : Subgroup (Equiv.Perm α)) [Finite P] (c : ℕ → α) (i : ℕ) :
    Finite (stabB P c i) :=
  Finite.of_injective (Subgroup.inclusion (fun _ hg => hg.1 : stabB P c i ≤ P))
    (Subgroup.inclusion_injective _)

theorem card_stab3_le (P : Subgroup (Equiv.Perm α)) [Finite P] (c : ℕ → α) (s₀ s₁ s₂ : Finset α)
    (h₀ : ∀ x ∈ s₀, ∃ g ∈ stabB P c 0, g (c 0) = x) (h₁ : ∀ x ∈ s₁, ∃ g ∈ stabB P c 1, g (c 1) = x)
    (h₂ : ∀ x ∈ s₂, ∃ g ∈ stabB P c 2, g (c 2) = x) :
    s₀.card * s₁.card * s₂.card * Nat.card (stabB P c 3) ≤ Nat.card P := by
  have hfin := finite_stabB P c
  have hstep : ∀ i, ∀ s : Finset α, (∀ x ∈ s, ∃ g ∈ stabB P c i, g (c i) = x) →
      s.card * Nat.card (stabB P c (i + 1)) ≤ Nat.card (stabB P c i) := by
    intro i s hs
    have := hfin i
    exact card_ge_of_orbit (stabB P c i) (c i) s hs (stabB P c (i + 1)) fun g hg =>
      ⟨⟨hg.1, fun t ht => hg.2 t (by omega)⟩, hg.2 i (by omega)⟩
  have e0 : Nat.card (stabB P c 0) ≤ Nat.card P := by
    have := hfin 0
    exact Nat.card_le_card_of_injective (Subgroup.inclusion (fun _ hg => hg.1 : stabB P c 0 ≤ P))
      (Subgroup.inclusion_injective _)
  have e1 := hstep 0 s₀ h₀
  have e2 := hstep 1 s₁ h₁
  have e3 := hstep 2 s₂ h₂
  calc s₀.card * s₁.card * s₂.card * Nat.card (stabB P c 3)
      = s₀.card * (s₁.card * (s₂.card * Nat.card (stabB P c 3))) := by ring
    _ ≤ s₀.card * (s₁.card * Nat.card (stabB P c 2)) :=
      Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ e3)
    _ ≤ s₀.card * Nat.card (stabB P c 1) := Nat.mul_le_mul_left _ e2
    _ ≤ Nat.card (stabB P c 0) := e1
    _ ≤ Nat.card P := e0

end CFSG.KC.M24Three

end
