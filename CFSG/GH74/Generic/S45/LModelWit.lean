module

public import CFSG.GH74.Uniqueness.Bender.AutFixed
public import CFSG.Sporadic.Schreier.MathieuOddCoreClasses
public import Mathlib.GroupTheory.Commutator.Basic
public import CFSG.Foundations.Basic

public section

namespace CFSG.GH74.Generic.S45

open CFSG.GH74.Uniqueness.Bender Subgroup CFSG.Sporadic.Schreier
open scoped commutatorElement

@[expose] def PerfOrd4 {n : ℕ} (G : Subgroup (Equiv.Perm (Fin n))) (t : Equiv.Perm (Fin n)) : Prop :=
  ∃ P : Subgroup (Equiv.Perm (Fin n)), P ≤ G ⊓ Subgroup.centralizer ({t} : Set (Equiv.Perm (Fin n))) ∧
    ⁅P, P⁆ = P ∧ ∃ x ∈ P, orderOf x = 4

theorem PerfOrd4.conj {n : ℕ} {G : Subgroup (Equiv.Perm (Fin n))} {t : Equiv.Perm (Fin n)}
    (h : PerfOrd4 G t) {g : Equiv.Perm (Fin n)} (hg : g ∈ G) : PerfOrd4 G (g * t * g⁻¹) := by
  obtain ⟨P, hPle, hP, x, hx, hx4⟩ := h
  refine ⟨P.map (MulAut.conj g).toMonoidHom, ?_, ?_, g * x * g⁻¹,
    ⟨x, hx, by simp [MulAut.conj_apply]⟩, ?_⟩
  · rintro _ ⟨z, hz, rfl⟩
    obtain ⟨hzG, hzc⟩ := Subgroup.mem_inf.1 (hPle hz)
    refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
    · simpa [MulAut.conj_apply] using G.mul_mem (G.mul_mem hg hzG) (G.inv_mem hg)
    · rw [Subgroup.mem_centralizer_singleton_iff] at hzc ⊢
      have hzc' : z * t = t * z := hzc
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      calc g * z * g⁻¹ * (g * t * g⁻¹) = g * (z * t) * g⁻¹ := by group
        _ = g * (t * z) * g⁻¹ := by rw [hzc']
        _ = g * t * g⁻¹ * (g * z * g⁻¹) := by group
  · rw [← Subgroup.map_commutator, hP]
  · have : orderOf (g * x * g⁻¹) = orderOf x := by
      have := MulEquiv.orderOf_eq (MulAut.conj g) x
      simpa [MulAut.conj_apply] using this
    rw [this, hx4]

variable {n : ℕ} {Pm Rm : Subgroup (Equiv.Perm (Fin n))}

theorem card_autFixed_eq_inf_centralizer (eR : Rm ≃* MulAut Pm)
    (heR : ∀ (x : Rm) (p : Pm), ((eR x p : Pm) : Equiv.Perm (Fin n)) =
      (x : Equiv.Perm (Fin n)) * (p : Equiv.Perm (Fin n)) * (x : Equiv.Perm (Fin n))⁻¹)
    (x : Rm) :
    Nat.card ↥(autFixed (eR x)) =
      Nat.card ↥(Pm ⊓ Subgroup.centralizer ({(x : Equiv.Perm (Fin n))} :
        Set (Equiv.Perm (Fin n)))) := by
  have hmap : (autFixed (eR x)).map Pm.subtype =
      Pm ⊓ Subgroup.centralizer ({(x : Equiv.Perm (Fin n))} : Set (Equiv.Perm (Fin n))) := by
    ext σ
    constructor
    · rintro ⟨p, hp, rfl⟩
      refine Subgroup.mem_inf.2 ⟨p.2, ?_⟩
      have hp' : eR x p = p := hp
      rw [Subgroup.mem_centralizer_singleton_iff]
      have h1 := congrArg Subtype.val hp'
      rw [heR x p] at h1
      calc (p : Equiv.Perm (Fin n)) * x
          = ((x : Equiv.Perm (Fin n)) * (p : Equiv.Perm (Fin n)) *
              (x : Equiv.Perm (Fin n))⁻¹) * x := by rw [h1]
        _ = x * p := by group
    · intro h
      obtain ⟨hσ, hc⟩ := Subgroup.mem_inf.1 h
      refine ⟨⟨σ, hσ⟩, ?_, rfl⟩
      show eR x ⟨σ, hσ⟩ = ⟨σ, hσ⟩
      apply Subtype.ext
      rw [heR x ⟨σ, hσ⟩]
      have hc' : σ * (x : Equiv.Perm (Fin n)) = (x : Equiv.Perm (Fin n)) * σ :=
        Subgroup.mem_centralizer_singleton_iff.1 hc
      calc (x : Equiv.Perm (Fin n)) * σ * (x : Equiv.Perm (Fin n))⁻¹
          = (σ * (x : Equiv.Perm (Fin n))) * (x : Equiv.Perm (Fin n))⁻¹ := by rw [hc']
        _ = σ := by group
  rw [← hmap, Subgroup.card_map_of_injective Pm.subtype_injective]

theorem exists_perfect_order_four_of_model_card (c : ℕ) (eR : Rm ≃* MulAut Pm)
    (heR : ∀ (x : Rm) (p : Pm), ((eR x p : Pm) : Equiv.Perm (Fin n)) =
      (x : Equiv.Perm (Fin n)) * (p : Equiv.Perm (Fin n)) * (x : Equiv.Perm (Fin n))⁻¹)
    (reps : List (Equiv.Perm (Fin n)))
    (hcover : ∀ t ∈ Rm, orderOf t = 2 → ∃ r ∈ reps, ∃ g ∈ Pm, t = g * r * g⁻¹)
    (hwit : ∀ r ∈ reps,
      Nat.card ↥(Pm ⊓ Subgroup.centralizer ({r} : Set (Equiv.Perm (Fin n)))) = c → PerfOrd4 Pm r)
    (α : MulAut Pm) (hα2 : α * α = 1) (hα1 : α ≠ 1) (hcard : Nat.card ↥(autFixed α) = c) :
    ∃ P : Subgroup Pm, P ≤ autFixed α ∧ ⁅P, P⁆ = P ∧ ∃ x ∈ P, orderOf x = 4 := by
  obtain ⟨x, hx⟩ := eR.surjective α
  have hxx : x * x = 1 := eR.injective (by rw [map_mul, hx, hα2, map_one])
  have hx1 : x ≠ 1 := fun h => hα1 (by rw [← hx, h, map_one])
  have hord : orderOf (x : Equiv.Perm (Fin n)) = 2 := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    refine orderOf_eq_prime ?_ ?_
    · have h2 : (x : Equiv.Perm (Fin n)) * x = 1 := by
        have := congrArg Subtype.val hxx
        simpa using this
      rw [pow_two]
      exact h2
    · intro h
      exact hx1 (Subtype.ext h)
  obtain ⟨r, hr, g, hg, hxg⟩ := hcover (x : Equiv.Perm (Fin n)) x.2 hord
  have hcx : Nat.card ↥(Pm ⊓ Subgroup.centralizer ({(x : Equiv.Perm (Fin n))} :
      Set (Equiv.Perm (Fin n)))) = c := by
    rw [← card_autFixed_eq_inf_centralizer eR heR x, hx]
    exact hcard
  have hcr : Nat.card ↥(Pm ⊓ Subgroup.centralizer ({r} : Set (Equiv.Perm (Fin n)))) = c := by
    rw [← hcx, hxg]
    have h1 := centralizerIn_conj Pm hg r
    unfold centralizerIn at h1
    rw [h1, Subgroup.card_map_of_injective (MulAut.conj g).injective]
  obtain ⟨P, hPle, hP, y, hy, hy4⟩ := (hwit r hr hcr).conj hg
  rw [← hxg] at hPle
  have hPPm : P ≤ Pm := fun z hz => (Subgroup.mem_inf.1 (hPle hz)).1
  refine ⟨P.subgroupOf Pm, ?_, ?_, ⟨y, hPPm hy⟩, Subgroup.mem_subgroupOf.2 hy, ?_⟩
  · intro z hz
    rw [mem_autFixed_iff]
    have hzP : (z : Equiv.Perm (Fin n)) ∈ P := Subgroup.mem_subgroupOf.1 hz
    have hzc := (Subgroup.mem_inf.1 (hPle hzP)).2
    rw [Subgroup.mem_centralizer_singleton_iff] at hzc
    apply Subtype.ext
    rw [← hx, heR x z]
    calc (x : Equiv.Perm (Fin n)) * (z : Equiv.Perm (Fin n)) * (x : Equiv.Perm (Fin n))⁻¹
        = (z : Equiv.Perm (Fin n)) * (x : Equiv.Perm (Fin n)) * (x : Equiv.Perm (Fin n))⁻¹ := by
          rw [hzc]
      _ = (z : Equiv.Perm (Fin n)) := by group
  · have hmap : (P.subgroupOf Pm).map Pm.subtype = P := Subgroup.map_subgroupOf_eq_of_le hPPm
    apply Subgroup.map_injective Pm.subtype_injective
    rw [Subgroup.map_commutator, hmap, hP]
  · rw [Subgroup.orderOf_mk]
    exact hy4

theorem exists_perfect_order_four_of_equiv_card {S : Type} [Group S] (c : ℕ) (φ : S ≃* Pm)
    (eR : Rm ≃* MulAut Pm)
    (heR : ∀ (x : Rm) (p : Pm), ((eR x p : Pm) : Equiv.Perm (Fin n)) =
      (x : Equiv.Perm (Fin n)) * (p : Equiv.Perm (Fin n)) * (x : Equiv.Perm (Fin n))⁻¹)
    (reps : List (Equiv.Perm (Fin n)))
    (hcover : ∀ t ∈ Rm, orderOf t = 2 → ∃ r ∈ reps, ∃ g ∈ Pm, t = g * r * g⁻¹)
    (hwit : ∀ r ∈ reps,
      Nat.card ↥(Pm ⊓ Subgroup.centralizer ({r} : Set (Equiv.Perm (Fin n)))) = c → PerfOrd4 Pm r)
    (α : MulAut S) (hα2 : α * α = 1) (hα1 : α ≠ 1) (hcard : Nat.card ↥(autFixed α) = c) :
    ∃ P : Subgroup S, P ≤ autFixed α ∧ ⁅P, P⁆ = P ∧ ∃ x ∈ P, 4 ∣ orderOf x := by
  have hβ2 : MulAut.congr φ α * MulAut.congr φ α = 1 := by rw [← map_mul, hα2, map_one]
  have hβ1 : MulAut.congr φ α ≠ 1 := fun h =>
    hα1 ((MulAut.congr φ).injective (by rw [h, map_one]))
  have hβc : Nat.card ↥(autFixed (MulAut.congr φ α)) = c := by
    rw [← Nat.card_congr (autFixedEquiv φ α).toEquiv]
    exact hcard
  obtain ⟨P, hPfix, hP, y, hy, hy4⟩ :=
    exists_perfect_order_four_of_model_card c eR heR reps hcover hwit (MulAut.congr φ α) hβ2 hβ1 hβc
  refine ⟨P.map φ.symm.toMonoidHom, ?_, ?_, φ.symm y, ⟨y, hy, rfl⟩, ?_⟩
  · rintro _ ⟨w, hw, rfl⟩
    have hw' := mem_autFixed_iff.1 (hPfix hw)
    rw [mem_autFixed_iff]
    have h1 : (MulAut.congr φ α) w = φ (α (φ.symm w)) := by
      rw [MulAut.congr_apply]
      simp
    have h2 : φ (α (φ.symm w)) = w := by rw [← h1]; exact hw'
    show α (φ.symm w) = φ.symm w
    apply φ.injective
    rw [h2, MulEquiv.apply_symm_apply]
  · rw [← Subgroup.map_commutator, hP]
  · have : orderOf (φ.symm y) = orderOf y := MulEquiv.orderOf_eq φ.symm y
    rw [this, hy4]

theorem exists_perfect_order_four_of_equiv {S : Type} [Group S] (φ : S ≃* Pm)
    (eR : Rm ≃* MulAut Pm)
    (heR : ∀ (x : Rm) (p : Pm), ((eR x p : Pm) : Equiv.Perm (Fin n)) =
      (x : Equiv.Perm (Fin n)) * (p : Equiv.Perm (Fin n)) * (x : Equiv.Perm (Fin n))⁻¹)
    (reps : List (Equiv.Perm (Fin n)))
    (hcover : ∀ t ∈ Rm, orderOf t = 2 → ∃ r ∈ reps, ∃ g ∈ Pm, t = g * r * g⁻¹)
    (hwit : ∀ r ∈ reps, PerfOrd4 Pm r) (α : MulAut S) (hα2 : α * α = 1) (hα1 : α ≠ 1) :
    ∃ P : Subgroup S, P ≤ autFixed α ∧ ⁅P, P⁆ = P ∧ ∃ x ∈ P, 4 ∣ orderOf x :=
  exists_perfect_order_four_of_equiv_card _ φ eR heR reps hcover (fun r hr _ => hwit r hr) α hα2
    hα1 rfl

end CFSG.GH74.Generic.S45
