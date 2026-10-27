module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftDelDecomp

public section

namespace CFSG.QuasithinUnique.Setup.Lift

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup
  CFSG.QuasithinUnique.Setup.Family CFSG.QuasithinUnique.Setup.Layer
  CFSG.QuasithinUnique.Setup.Layer.Actor CFSG.QuasithinUnique.Setup.Offender
open scoped Multiplicative MatrixGroups LinearAlgebra.Projectivization

section Seed

theorem mem_normalizer_zpowers_of_conj_mem {Γ : Type*} [Group Γ] {g t : Γ}
    (h1 : g * t * g⁻¹ ∈ Subgroup.zpowers t) (h2 : g⁻¹ * t * g ∈ Subgroup.zpowers t) :
    g ∈ Subgroup.normalizer (Subgroup.zpowers t : Set Γ) := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · rintro ⟨k, rfl⟩
    rw [← conj_zpow]
    exact Subgroup.zpow_mem _ h1 k
  · rintro ⟨k, hk⟩
    have hk' : t ^ k = g * h * g⁻¹ := hk
    have hh : h = g⁻¹ * (t ^ k) * g := by
      rw [hk']
      group
    rw [hh]
    have := conj_zpow (a := g⁻¹) (b := t) (i := k)
    rw [inv_inv] at this
    rw [← this]
    exact Subgroup.zpow_mem _ h2 k

theorem conj_symm_mem_zpowers_of_mem_normalizer {Γ P : Type*} [Group Γ] [Group P] {B : Subgroup Γ}
    (ψ : ↥B ≃* P) {t g : P} (hg : g ∈ Subgroup.normalizer (Subgroup.zpowers t : Set P))
    (z : ↥B) (hz : ψ z = g) :
    (z : Γ) * ((ψ.symm t : ↥B) : Γ) * (z : Γ)⁻¹ ∈ Subgroup.zpowers (((ψ.symm t : ↥B)) : Γ) := by
  have h1 : g * t * g⁻¹ ∈ Subgroup.zpowers t :=
    (Subgroup.mem_normalizer_iff.1 hg t).1 (Subgroup.mem_zpowers t)
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 h1
  refine Subgroup.mem_zpowers_iff.2 ⟨k, ?_⟩
  have h2 : z * ψ.symm t * z⁻¹ = (ψ.symm t) ^ k := by
    rw [← map_zpow, hk, map_mul, map_mul, map_inv, ← hz]
    simp
  have := congrArg (fun w : ↥B => (w : Γ)) h2
  simpa using this.symm

variable {Ω : Type*} [DecidableEq Ω] [Fintype Ω]

theorem exists_seed_perm {a b c d ω : Ω} (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c)
    (hbd : b ≠ d) (hωa : ω ≠ a) (hωb : ω ≠ b) (hωc : ω ≠ c) (hωd : ω ≠ d) :
    ∃ t : Equiv.Perm Ω, t ∈ alternatingGroup Ω ∧ orderOf t = 3 ∧
      Subgroup.closure ({Equiv.swap a b, Equiv.swap c d} : Set (Equiv.Perm Ω)) ≤
        Subgroup.normalizer (Subgroup.zpowers t : Set (Equiv.Perm Ω)) := by
  have h3 := Equiv.Perm.isThreeCycle_swap_mul_swap_same hab (Ne.symm hωa) (Ne.symm hωb)
  refine ⟨Equiv.swap a b * Equiv.swap a ω, ?_, h3.orderOf, ?_⟩
  · rw [Equiv.Perm.mem_alternatingGroup]
    exact h3.sign
  · rw [Subgroup.closure_le]
    rintro s (rfl | rfl)
    · rw [SetLike.mem_coe]
      refine mem_normalizer_zpowers_of_conj_mem ?_ ?_
      · have : Equiv.swap a b * (Equiv.swap a b * Equiv.swap a ω) * (Equiv.swap a b)⁻¹ =
            (Equiv.swap a b * Equiv.swap a ω)⁻¹ := by simp
        rw [this]
        exact Subgroup.inv_mem _ (Subgroup.mem_zpowers _)
      · have : (Equiv.swap a b)⁻¹ * (Equiv.swap a b * Equiv.swap a ω) * Equiv.swap a b =
            (Equiv.swap a b * Equiv.swap a ω)⁻¹ := by simp
        rw [this]
        exact Subgroup.inv_mem _ (Subgroup.mem_zpowers _)
    · rw [SetLike.mem_coe]
      have hc1 : Commute (Equiv.swap c d) (Equiv.swap a b) :=
        (swap_disjoint hac had hbc hbd).commute.symm
      have hc2 : Commute (Equiv.swap c d) (Equiv.swap a ω) :=
        (swap_disjoint hac had hωc hωd).commute.symm
      have hc : Commute (Equiv.swap c d) (Equiv.swap a b * Equiv.swap a ω) := hc1.mul_right hc2
      refine mem_normalizer_zpowers_of_conj_mem ?_ ?_
      · rw [hc.mul_inv_cancel]
        exact Subgroup.mem_zpowers _
      · have : (Equiv.swap c d)⁻¹ * (Equiv.swap a b * Equiv.swap a ω) * Equiv.swap c d =
            Equiv.swap a b * Equiv.swap a ω := by
          simpa using hc.inv_left.mul_inv_cancel
        rw [this]
        exact Subgroup.mem_zpowers _

theorem exists_seed_subgroup {Γ ι : Type*} [Group Γ] (B A : ι → Subgroup Γ) (Li : Subgroup Γ)
    (i : ι) (hAB : ∀ j, A j ≤ B j)
    (hcomm : ∀ j, j ≠ i → ∀ x ∈ B i, ∀ y ∈ B j, x * y = y * x)
    (ψ : ↥(B i) ≃* Equiv.Perm Ω)
    (hLi : (Li.subgroupOf (B i)).map ψ.toMonoidHom = alternatingGroup Ω)
    {a b c d ω : Ω} (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d)
    (hωa : ω ≠ a) (hωb : ω ≠ b) (hωc : ω ≠ c) (hωd : ω ≠ d)
    (hA : ((A i).subgroupOf (B i)).map ψ.toMonoidHom =
      Subgroup.closure ({Equiv.swap a b, Equiv.swap c d} : Set (Equiv.Perm Ω))) :
    ∃ Fs : Subgroup Γ, Fs ≤ Li ∧ Nat.card Fs = 3 ∧
      (⨆ j, A j) ≤ Subgroup.normalizer (Fs : Set Γ) := by
  obtain ⟨t, htalt, htord, htnorm⟩ := exists_seed_perm hab hac had hbc hbd hωa hωb hωc hωd
  set x : ↥(B i) := ψ.symm t with hx
  have hxLi : (x : Γ) ∈ Li := by
    have h1 : t ∈ (Li.subgroupOf (B i)).map ψ.toMonoidHom := by rw [hLi]; exact htalt
    obtain ⟨y, hy, hyt⟩ := h1
    have h2 : y = x := by
      rw [hx, ← hyt]
      simp
    rw [← h2]
    exact hy
  refine ⟨Subgroup.zpowers (x : Γ), Subgroup.zpowers_le.2 hxLi, ?_, ?_⟩
  · rw [Nat.card_zpowers]
    have h1 : orderOf (x : Γ) = orderOf x :=
      orderOf_injective (B i).subtype (B i).subtype_injective x
    have h2 : orderOf x = orderOf t :=
      orderOf_injective ψ.symm.toMonoidHom ψ.symm.injective t
    rw [h1, h2, htord]
  · refine iSup_le fun j => ?_
    intro y hy
    by_cases hj : j = i
    · subst hj
      have hyB : y ∈ B j := hAB j hy
      have hyA : ψ ⟨y, hyB⟩ ∈ Subgroup.closure
          ({Equiv.swap a b, Equiv.swap c d} : Set (Equiv.Perm Ω)) := by
        rw [← hA]
        exact ⟨⟨y, hyB⟩, hy, rfl⟩
      have hg := htnorm hyA
      have hg' := Subgroup.inv_mem _ hg
      refine mem_normalizer_zpowers_of_conj_mem ?_ ?_
      · exact conj_symm_mem_zpowers_of_mem_normalizer ψ hg ⟨y, hyB⟩ rfl
      · have := conj_symm_mem_zpowers_of_mem_normalizer ψ hg' ⟨y, hyB⟩⁻¹ (by simp)
        simpa using this
    · have hyB : y ∈ B j := hAB j hy
      have hcm := hcomm j hj (x : Γ) x.2 y hyB
      refine mem_normalizer_zpowers_of_conj_mem ?_ ?_
      · have : y * (x : Γ) * y⁻¹ = x := by
          rw [← hcm]
          group
        rw [this]
        exact Subgroup.mem_zpowers _
      · have : y⁻¹ * (x : Γ) * y = x := by
          rw [mul_assoc, hcm, inv_mul_cancel_left]
        rw [this]
        exact Subgroup.mem_zpowers _

end Seed

section Main

theorem delSeedProp
    : DelSeedProp := by
  intro G _ _ R M V n F _ r Lc ctx i
  classical
  have hS := ctx.setting
  have hFfin : Finite F := Nat.finite_of_card_ne_zero (by rw [hS.card_eq]; positivity)
  let _ : Fintype F := Fintype.ofFinite F
  let _ : Fintype (ℙ F (Fin 2 → F)) := Fintype.ofFinite _
  let _ : DecidableEq (ℙ F (Fin 2 → F)) := Classical.decEq _
  obtain ⟨⟨W, hW1, hW2, hW3, θ, hmax, himg⟩⟩ := even_SL2_original_images hS ctx.comps
  have hbridge := even_SL2_original_bridge hS ctx.comps
  set ψ := (binPsi θ).toMonoidHom with hψ
  set L := oddOrderSubgroup (⊤ : Subgroup G)
  have hbK : autOn L V = oddOrderSubgroup (autOn (⊤ : Subgroup G) V) := hbridge.K_eq
  have hKL : (autOn L V).map ψ = oddGen ((autOn (⊤ : Subgroup G) V).map ψ) := by
    rw [hbK]
    exact map_closure_odd (binPsi θ) (autOn (⊤ : Subgroup G) V)
  have hdelF : DeletedFamily ((autOn (⊤ : Subgroup G) V).map ψ) n r
      (fun i => (Lc i).map ψ) := by
    rcases hmax.offenders.family.alternatives with ⟨hnat, -⟩ | ⟨hdelF, -⟩
    · exfalso
      apply ctx.deleted
      have h1 := (himg.natural hnat).2.1.1
      rw [← hKL] at h1
      exact (Subgroup.map_le_map_iff_of_injective (binPsi θ).injective).1 h1
    · exact hdelF
  have common := hmax.offenders.family.common
  obtain ⟨-, -, ψi, _, Ai, -, hD, hdata⟩ := himg.deleted hdelF
  have halt := (hdata i).2.1
  have hAB : ∀ j, Ai j ≤ blockB ((autOn (⊤ : Subgroup G) V).map ψ) ((Lc j).map ψ) :=
    fun j => ((hdata j).2.2.1).trans inf_le_right
  obtain ⟨a, b, c, d, ω, hab, hac, had, hbc, hbd, hcd, hωa, hωb, hωc, hωd, hmap, -⟩ :=
    (hdata i).2.2.2
  obtain ⟨Fs', hFle, hFcard, hFnorm⟩ := exists_seed_subgroup
    (fun j => blockB ((autOn (⊤ : Subgroup G) V).map ψ) ((Lc j).map ψ)) Ai ((Lc i).map ψ) i hAB
    (fun j hj => common.B_comm i j (Ne.symm hj)) (ψi i) halt hab hac had hbc hbd hωa hωb hωc hωd
    hmap
  have hDS : (autOn (baum R) V).map ψ = ⨆ j, Ai j := himg.baumann_eq.symm.trans hD
  refine ⟨Fs'.map (binPsi θ).symm.toMonoidHom, ?_, ?_, ?_⟩
  · rintro _ ⟨f, hf, rfl⟩
    obtain ⟨l, hl, rfl⟩ := hFle hf
    simpa [hψ] using hl
  · rw [Subgroup.card_map_of_injective (binPsi θ).symm.injective]
    exact hFcard
  · intro φ hφ
    have h1 := map_le_normalizer_map_of_le (binPsi θ).symm hFnorm
    refine h1 ⟨ψ φ, ?_, ?_⟩
    · rw [← hDS]
      exact ⟨φ, hφ, rfl⟩
    · simp [hψ]

end Main

end CFSG.QuasithinUnique.Setup.Lift
