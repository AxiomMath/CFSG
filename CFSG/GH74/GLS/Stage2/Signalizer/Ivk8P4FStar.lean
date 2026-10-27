module

public import CFSG.GroupTheory.Fitting.CharacteristicP
public import CFSG.GroupTheory.LocalCores.Components

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Subgroup CFSG

variable {Γ : Type*} [Group Γ]

@[expose] def cfsgPElements (p : ℕ) (k : ℕ) : Subgroup Γ where
  carrier := {x | x ∈ Subgroup.centralizer (generalizedFitting Γ : Set Γ) ∧
    x ∈ generalizedFitting Γ ∧ x ^ p ^ k = 1}
  mul_mem' := by
    rintro x y ⟨hxc, hxF, hxp⟩ ⟨hyc, hyF, hyp⟩
    have hxy : Commute x y := by
      have := (Subgroup.mem_centralizer_iff.1 hxc) y hyF
      exact this.symm
    refine ⟨mul_mem hxc hyc, mul_mem hxF hyF, ?_⟩
    rw [hxy.mul_pow, hxp, hyp, one_mul]
  one_mem' := ⟨one_mem _, one_mem _, one_pow _⟩
  inv_mem' := by
    rintro x ⟨hxc, hxF, hxp⟩
    exact ⟨inv_mem hxc, inv_mem hxF, by rw [inv_pow, hxp, inv_one]⟩

theorem cfsgPElements_normal (p k : ℕ) : (cfsgPElements p k : Subgroup Γ).Normal := by
  have hFn : (generalizedFitting Γ).Normal :=
    (LocalCores.generalized_fitting_characteristic (G := Γ)).2
  refine ⟨fun x hx c => ?_⟩
  obtain ⟨hxc, hxF, hxp⟩ := hx
  refine ⟨?_, hFn.conj_mem x hxF c, ?_⟩
  · rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hy' : c⁻¹ * y * c⁻¹⁻¹ ∈ generalizedFitting Γ := hFn.conj_mem y hy c⁻¹
    have h := Subgroup.mem_centralizer_iff.1 hxc _ hy'
    calc y * (c * x * c⁻¹) = c * ((c⁻¹ * y * c⁻¹⁻¹) * x) * c⁻¹ := by group
      _ = c * (x * (c⁻¹ * y * c⁻¹⁻¹)) * c⁻¹ := by rw [h]
      _ = c * x * c⁻¹ * y := by group
  · calc (c * x * c⁻¹) ^ p ^ k = c * x ^ p ^ k * c⁻¹ := by rw [conj_pow]
      _ = 1 := by rw [hxp]; group

theorem generalizedFitting_centralizer_pElements_le_pCore [Finite Γ] {p : ℕ} [Fact p.Prime]
    {g : Γ} {k : ℕ} (hgc : g ∈ Subgroup.centralizer (generalizedFitting Γ : Set Γ))
    (hgp : g ^ p ^ k = 1) : g ∈ pCore p Γ := by
  have hgF : g ∈ generalizedFitting Γ := centralizer_generalizedFitting_le Γ hgc
  have hmem : g ∈ (cfsgPElements p k : Subgroup Γ) := ⟨hgc, hgF, hgp⟩
  have hP : IsPGroup p (cfsgPElements p k : Subgroup Γ) := by
    intro x
    exact ⟨k, Subtype.ext x.2.2.2⟩
  have hle : (cfsgPElements p k : Subgroup Γ) ≤ pCore p Γ :=
    le_sSup ⟨cfsgPElements_normal p k, hP⟩
  exact hle hmem

theorem fstar_bridge [Finite Γ] {p : ℕ} [Fact p.Prime] (hO : pCore p Γ = ⊥) {g : Γ} (hg1 : g ≠ 1)
    (hgp : ∃ k : ℕ, g ^ p ^ k = 1) (hF : ∀ x ∈ fittingSubgroup Γ, g * x = x * g) :
    ∃ x ∈ layer Γ, g * x ≠ x * g := by
  by_contra hE
  push Not at hE
  obtain ⟨k, hk⟩ := hgp
  have hF' : fittingSubgroup Γ ≤ Subgroup.centralizer ({g} : Set Γ) := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.2 (hF x hx).symm
  have hE' : layer Γ ≤ Subgroup.centralizer ({g} : Set Γ) := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.2 (hE x hx).symm
  have hsup : generalizedFitting Γ ≤ Subgroup.centralizer ({g} : Set Γ) := sup_le hF' hE'
  have hgc : g ∈ Subgroup.centralizer (generalizedFitting Γ : Set Γ) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    exact Subgroup.mem_centralizer_singleton_iff.1 (hsup hx)
  have := generalizedFitting_centralizer_pElements_le_pCore (p := p) hgc hk
  rw [hO, Subgroup.mem_bot] at this
  exact hg1 this

theorem not_layer_le_centralizer_of_fstar [Finite Γ] {p : ℕ} [Fact p.Prime]
    (hO : pCore p Γ = ⊥) {g : Γ} (hg1 : g ≠ 1) (hgp : ∃ k : ℕ, g ^ p ^ k = 1)
    (hF : ∀ x ∈ fittingSubgroup Γ, g * x = x * g) :
    ¬ layer Γ ≤ Subgroup.centralizer ({g} : Set Γ) := by
  intro h
  obtain ⟨x, hx, hne⟩ := fstar_bridge hO hg1 hgp hF
  exact hne (Subgroup.mem_centralizer_singleton_iff.1 (h hx)).symm

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
