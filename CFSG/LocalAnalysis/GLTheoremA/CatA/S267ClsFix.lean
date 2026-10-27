module

public import CFSG.HardMathSupport.Solomon.Coordinator.LayerCentralFix

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S267.ModelGen

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup mem_fixSubgroup alpha_eq_mul_central
  commutatorElement_mul_mul')
open scoped commutatorElement

section Family

variable {G : Type*} [Group G]

@[expose] def fixFam {ι : Type*} (γ : ι → MulAut G) : Subgroup G := ⨅ i, fixSubgroup (γ i)

theorem mem_fixFam {ι : Type*} {γ : ι → MulAut G} {g : G} : g ∈ fixFam γ ↔ ∀ i, γ i g = g := by
  rw [fixFam, Subgroup.mem_iInf]
  rfl

end Family

section Fix

variable {K Q : Type*} [Group K] [Group Q] (π : K →* Q) (hker : π.ker ≤ Subgroup.center K)
  {ι : Type*} (α : ι → MulAut K) (β : ι → MulAut Q) (hαβ : ∀ i k, π (α i k) = β i (π k))
include hker hαβ

theorem map_inf_fixFam_le (I : Subgroup K) : (I ⊓ fixFam α).map π ≤ I.map π ⊓ fixFam β := by
  rintro _ ⟨k, ⟨hkI, hk⟩, rfl⟩
  refine ⟨⟨k, hkI, rfl⟩, mem_fixFam.2 fun i => ?_⟩
  rw [← hαβ, (mem_fixFam.1 hk) i]

theorem conj_mem_inf_fixFam {I : Subgroup K} {k f : K} (hkI : k ∈ I) (hk : π k ∈ fixFam β)
    (hf : f ∈ I ⊓ fixFam α) : k * f * k⁻¹ ∈ I ⊓ fixFam α := by
  refine ⟨I.mul_mem (I.mul_mem hkI hf.1) (I.inv_mem hkI), mem_fixFam.2 fun i => ?_⟩
  have hki : π k ∈ fixSubgroup (β i) := (mem_fixFam.1 hk) i
  obtain ⟨z, hz, hαk⟩ := alpha_eq_mul_central π hker (α i) (β i) (hαβ i) hki
  have hf' : α i f = f := (mem_fixFam.1 hf.2) i
  rw [map_mul, map_mul, map_inv, hαk, hf']
  have hzc : ∀ g : K, g * z = z * g := fun g => Subgroup.mem_center_iff.1 hz g
  calc k * z * f * (k * z)⁻¹ = k * (z * f) * z⁻¹ * k⁻¹ := by group
    _ = k * (f * z) * z⁻¹ * k⁻¹ := by rw [← hzc f]
    _ = k * f * k⁻¹ := by group

theorem comm_mem_inf_fixFam {I : Subgroup K} {k₁ k₂ : K} (h₁I : k₁ ∈ I) (h₂I : k₂ ∈ I)
    (h₁ : π k₁ ∈ fixFam β) (h₂ : π k₂ ∈ fixFam β) : ⁅k₁, k₂⁆ ∈ I ⊓ fixFam α := by
  refine ⟨Subgroup.commutator_mem_commutator h₁I h₂I |> fun h =>
    (Subgroup.commutator_le_self I) h, mem_fixFam.2 fun i => ?_⟩
  obtain ⟨z₁, hz₁, hα₁⟩ := alpha_eq_mul_central π hker (α i) (β i) (hαβ i) ((mem_fixFam.1 h₁) i)
  obtain ⟨z₂, hz₂, hα₂⟩ := alpha_eq_mul_central π hker (α i) (β i) (hαβ i) ((mem_fixFam.1 h₂) i)
  rw [map_commutatorElement, hα₁, hα₂]
  exact commutatorElement_mul_mul' (Commute.symm (Subgroup.mem_center_iff.1 hz₁ k₂))
    (Commute.symm (Subgroup.mem_center_iff.1 hz₁ z₂))
    (Commute.symm (Subgroup.mem_center_iff.1 hz₂ k₁))

theorem normal_map_inf_fixFam (I : Subgroup K) :
    (((I ⊓ fixFam α).map π).subgroupOf (I.map π ⊓ fixFam β)).Normal := by
  refine ⟨fun x hx g => ?_⟩
  rw [Subgroup.mem_subgroupOf] at hx ⊢
  obtain ⟨f, hf, hfx⟩ := hx
  obtain ⟨k, hkI, hk⟩ := (g.2 : (g : Q) ∈ I.map π ⊓ fixFam β).1
  have hkg : π k ∈ fixFam β := by rw [hk]; exact g.2.2
  refine ⟨k * f * k⁻¹, conj_mem_inf_fixFam π hker α β hαβ hkI hkg hf, ?_⟩
  simp only [map_mul, map_inv, hk, hfx]
  rfl

theorem le_map_inf_fixFam_of_perfect (I : Subgroup K) {A : Subgroup Q}
    (hA : A ≤ I.map π ⊓ fixFam β) (hperf : ⁅A, A⁆ = A) : A ≤ (I ⊓ fixFam α).map π := by
  conv_lhs => rw [← hperf]
  rw [Subgroup.commutator_le]
  intro a₁ ha₁ a₂ ha₂
  obtain ⟨k₁, hk₁I, rfl⟩ := (hA ha₁).1
  obtain ⟨k₂, hk₂I, rfl⟩ := (hA ha₂).1
  exact ⟨⁅k₁, k₂⁆, comm_mem_inf_fixFam π hker α β hαβ hk₁I hk₂I (hA ha₁).2 (hA ha₂).2,
    map_commutatorElement _ _ _⟩

theorem kerCentral_inf_fixFam (I : Subgroup K) :
    ∀ y ∈ (I ⊓ fixFam α) ⊓ π.ker, ∀ x ∈ I ⊓ fixFam α, x * y = y * x := fun _ hy x _ =>
  Subgroup.mem_center_iff.1 (hker hy.2) x

end Fix

section Layers

variable {K Q : Type} [Group K] [Group Q] [Finite K] [Finite Q] (π : K →* Q)
  (hker : π.ker ≤ Subgroup.center K) {ι : Type*} (α : ι → MulAut K) (β : ι → MulAut Q)
  (hαβ : ∀ i k, π (α i k) = β i (π k))
include hker hαβ

theorem glaPComponent_map_inf_fixFam {p : ℕ} (hp : p.Prime) (I : Subgroup K) {J : Subgroup K}
    (hJ : GLAPComponent p (I ⊓ fixFam α) J) :
    GLAPComponent p (I.map π ⊓ fixFam β) (J.map π) :=
  CFSG.HardMathSupport.Solomon.Proving.glaPComponent_of_normal_overgroup hp
    (map_inf_fixFam_le π hker α β hαβ I) (normal_map_inf_fixFam π hker α β hαβ I)
    (CFSG.HardMathSupport.Solomon.Coordinator.glaPComponent_map_central hp π
      (kerCentral_inf_fixFam π hker α β hαβ I) hJ)

theorem exists_glaPComponent_map_inf_fixFam {p : ℕ} (hp : p.Prime) (I : Subgroup K)
    {A : Subgroup Q} (hA : GLAPComponent p (I.map π ⊓ fixFam β) A) :
    ∃ J : Subgroup K, GLAPComponent p (I ⊓ fixFam α) J ∧ J.map π = A := by
  have hAH : A ≤ (I ⊓ fixFam α).map π :=
    le_map_inf_fixFam_of_perfect π hker α β hαβ I hA.1 (glaPComponent_perfect hA)
  exact CFSG.HardMathSupport.Solomon.Coordinator.exists_glaPComponent_map_central hp π
    (kerCentral_inf_fixFam π hker α β hαβ I)
    (glaPComponent_of_le hp hA hAH (map_inf_fixFam_le π hker α β hαβ I))

theorem map_glaPLayer_inf_fixFam_eq {p : ℕ} (hp : p.Prime) (I : Subgroup K) :
    (GLAPLayer p (I ⊓ fixFam α)).map π = GLAPLayer p (I.map π ⊓ fixFam β) := by
  apply le_antisymm
  · rw [Subgroup.map_le_iff_le_comap]
    refine sSup_le fun J hJ => ?_
    rw [← Subgroup.map_le_iff_le_comap]
    exact le_sSup (glaPComponent_map_inf_fixFam π hker α β hαβ hp I hJ)
  · refine sSup_le fun A hA => ?_
    obtain ⟨J, hJ, rfl⟩ := exists_glaPComponent_map_inf_fixFam π hker α β hαβ hp I hA
    exact Subgroup.map_mono (le_sSup hJ)

theorem glaPLayer_inf_fixFam_ne_bot_iff {p : ℕ} (hp : p.Prime) (I : Subgroup K) :
    GLAPLayer p (I ⊓ fixFam α) ≠ ⊥ ↔ GLAPLayer p (I.map π ⊓ fixFam β) ≠ ⊥ := by
  rw [← map_glaPLayer_inf_fixFam_eq π hker α β hαβ hp I]
  constructor
  · intro h hbot
    apply h
    rw [Subgroup.map_eq_bot_iff] at hbot
    rw [eq_bot_iff]
    intro x hx
    have hcomm : GLAPLayer p (I ⊓ fixFam α) ≤ Subgroup.center K := hbot.trans hker
    have hab : ⁅GLAPLayer p (I ⊓ fixFam α), GLAPLayer p (I ⊓ fixFam α)⁆ = ⊥ := by
      rw [eq_bot_iff, Subgroup.commutator_le]
      intro a ha b _
      rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
      exact (Subgroup.mem_center_iff.1 (hcomm ha) b).symm
    have hJ : ∀ J : Subgroup K, GLAPComponent p (I ⊓ fixFam α) J → J = ⊥ := by
      intro J hJ
      have hJL : J ≤ GLAPLayer p (I ⊓ fixFam α) := le_sSup hJ
      have hp' := glaPComponent_perfect hJ
      rw [← hp', eq_bot_iff]
      exact (Subgroup.commutator_mono hJL hJL).trans hab.le
    have hL : GLAPLayer p (I ⊓ fixFam α) = ⊥ := by
      rw [GLAPLayer, eq_bot_iff]
      exact sSup_le fun J hJ' => (hJ J hJ').le
    rw [hL] at hx
    exact hx
  · intro h hbot
    apply h
    rw [hbot, Subgroup.map_bot]

end Layers

end CFSG.LocalAnalysis.GLTheoremA.S267.ModelGen

end
