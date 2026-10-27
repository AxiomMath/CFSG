module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftBaumannDel

public section

namespace CFSG.QuasithinUnique.Setup.Lift

open CFSG.QuasithinUnique.Setup.Offender CFSG.QuasithinUnique.Setup.Layer CFSG.QuasithinUnique
  CFSG.Quasithin.B6 CFSG.QuasithinUnique.Setup.SL2Modules
open scoped MatrixGroups LinearAlgebra.Projectivization
open Projectivization

universe v

section Span

variable {V : Type v} [AddCommGroup V] [Module (ZMod 2) V] {F : Type} [Field F] [Fintype F]
  [Fintype (ℙ F (Fin 2 → F))] [DecidableEq (ℙ F (Fin 2 → F))]
  {H T : Subgroup (V ≃ₗ[ZMod 2] V)} {n r : ℕ} {Lc : Fin r → Subgroup (V ≃ₗ[ZMod 2] V)}

theorem mem_fixGL_iSup {ι : Type*} {A : ι → Subgroup (V ≃ₗ[ZMod 2] V)} {v : V}
    (h : ∀ j, ∀ y ∈ A j, y v = v) : v ∈ fixGL (⨆ j, A j) := by
  rw [mem_fixGL]
  intro g hg
  refine Subgroup.iSup_induction A (C := fun g => g v = v) hg (fun j y hy => h j y hy) rfl ?_
  intro x y hx hy
  show x (y v) = v
  rw [hy]
  exact hx

variable [Finite V]

omit [Finite V] in
theorem deleted_fixGL_le (common : EvenSL2FamilyCommon H T r Lc)
    {A : Fin r → Subgroup (V ≃ₗ[ZMod 2] V)} (hAB : ∀ i, A i ≤ blockB H (Lc i)) :
    fixGL (oddGen H) ≤ fixGL (⨆ i, A i) := by
  rw [common.C_eq_J]
  have hAJ : (⨆ i, A i) ≤ offenderJ H := by
    rw [common.J_eq]
    exact iSup_mono hAB
  intro v hv
  rw [mem_fixGL] at hv ⊢
  exact fun g hg => hv g (hAJ hg)

theorem deleted_span (ctx : FamilyCtx H T n F r Lc) (common : EvenSL2FamilyCommon H T r Lc)
    {Ω : Type} [Fintype Ω] [DecidableEq Ω] (h5 : Fintype.card Ω = 5)
    (ψ : ∀ i, ↥(blockB H (Lc i)) ≃* Equiv.Perm Ω)
    (β : ∀ i, ↥(commGL (Lc i) ⊤) ≃ₗ[ZMod 2] ↥(SL2Modules.evenWeight Ω))
    (hcompat : ∀ i (b : ↥(blockB H (Lc i))) (u u' : ↥(commGL (Lc i) ⊤)),
      (u' : V) = (b : V ≃ₗ[ZMod 2] V) (u : V) →
        ((β i u' : ↥(SL2Modules.evenWeight Ω)) : Ω → ZMod 2) =
          permAct (ψ i b) ((β i u : ↥(SL2Modules.evenWeight Ω)) : Ω → ZMod 2))
    (A : Fin r → Subgroup (V ≃ₗ[ZMod 2] V))
    (halt : ∀ i, ((Lc i).subgroupOf (blockB H (Lc i))).map (ψ i).toMonoidHom = alternatingGroup Ω)
    (hAB : ∀ i, A i ≤ blockB H (Lc i))
    (hAs : ∀ i, ∃ a b c d : Ω, a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧
      ((A i).subgroupOf (blockB H (Lc i))).map (ψ i).toMonoidHom =
        Subgroup.closure ({Equiv.swap a b, Equiv.swap c d} : Set (Equiv.Perm Ω))) :
    Submodule.span (ZMod 2)
      {w : V | ∃ k ∈ oddGen H, ∃ y ∈ fixGL (⨆ i, A i), w = k y} = ⊤ := by
  classical
  set Y := fixGL (⨆ i, A i) with hY
  set M := Submodule.span (ZMod 2) {w : V | ∃ k ∈ oddGen H, ∃ y ∈ Y, w = k y} with hM
  have hgen : ∀ k ∈ oddGen H, ∀ y ∈ Y, k y ∈ M := fun k hk y hy =>
    Submodule.subset_span ⟨k, hk, y, hy, rfl⟩
  have hYM : Y ≤ M := fun y hy => by simpa using hgen 1 (Subgroup.one_mem _) y hy
  have hLK : ∀ i, Lc i ≤ oddGen H := fun i => by
    rw [ctx.layer.K_eq]
    exact le_iSup Lc i
  have hCY : fixGL (oddGen H) ≤ Y := deleted_fixGL_le common hAB
  have hIM : ∀ i, commGL (Lc i) ⊤ ≤ M := by
    intro i u hu
    obtain ⟨a, b, c, d, hab, hac, had, hbc, hbd, hA⟩ := hAs i
    set v0 : ↥(commGL (Lc i) ⊤) :=
      (β i).symm ⟨delta a + delta b, delta_add_delta_mem a b⟩ with hv0
    have hβv0 : ((β i v0 : ↥(SL2Modules.evenWeight Ω)) : Ω → ZMod 2) = delta a + delta b := by
      rw [hv0, LinearEquiv.apply_symm_apply]
    have hv0Y : (v0 : V) ∈ Y := by
      refine mem_fixGL_iSup fun j y hy => ?_
      by_cases hji : j = i
      · subst hji
        have hyB : y ∈ blockB H (Lc j) := hAB j hy
        have hψy : ψ j ⟨y, hyB⟩ ∈
            Subgroup.closure ({Equiv.swap a b, Equiv.swap c d} : Set (Equiv.Perm Ω)) := by
          rw [← hA]
          exact ⟨⟨y, hyB⟩, hy, rfl⟩
        have hfix := permAct_fix_of_mem_closure hac had hbc hbd hψy
        have hyv0 : y (v0 : V) ∈ commGL (Lc j) ⊤ := blockB_apply_mem_I ctx hyB v0.2
        have hc := hcompat j ⟨y, hyB⟩ v0 ⟨y (v0 : V), hyv0⟩ rfl
        have h1 : ((β j ⟨y (v0 : V), hyv0⟩ : ↥(SL2Modules.evenWeight Ω)) : Ω → ZMod 2) =
            ((β j v0 : ↥(SL2Modules.evenWeight Ω)) : Ω → ZMod 2) := by
          rw [hc, hβv0]
          exact hfix
        have h2 : β j ⟨y (v0 : V), hyv0⟩ = β j v0 := Subtype.ext h1
        have h3 : (⟨y (v0 : V), hyv0⟩ : ↥(commGL (Lc j) ⊤)) = v0 := (β j).injective h2
        exact congrArg Subtype.val h3
      · exact common.B_fix_I j i (fun h => hji h.symm) y (hAB j hy) (v0 : V) v0.2
    have hpair : ∀ x y : Ω, x ≠ y → ((β i).symm ⟨delta x + delta y, delta_add_delta_mem x y⟩ : V) ∈ M := by
      intro x y hxy
      obtain ⟨τ, hτ, hτa, hτb⟩ := alt_two_transitive h5 hab hxy
      have hτ' : τ ∈ ((Lc i).subgroupOf (blockB H (Lc i))).map (ψ i).toMonoidHom := by
        rw [halt i]
        exact hτ
      obtain ⟨k, hk, hkτ⟩ := hτ'
      have hkL : (k : V ≃ₗ[ZMod 2] V) ∈ Lc i := hk
      have hkv0 : (k : V ≃ₗ[ZMod 2] V) (v0 : V) ∈ commGL (Lc i) ⊤ :=
        blockB_apply_mem_I ctx k.2 v0.2
      have hc := hcompat i k v0 ⟨(k : V ≃ₗ[ZMod 2] V) (v0 : V), hkv0⟩ rfl
      have hkτ' : ψ i k = τ := hkτ
      have h1 : ((β i ⟨(k : V ≃ₗ[ZMod 2] V) (v0 : V), hkv0⟩ : ↥(SL2Modules.evenWeight Ω)) : Ω → ZMod 2) =
          delta x + delta y := by
        rw [hc, hβv0, hkτ', permAct_add, permAct_delta, permAct_delta, hτa, hτb]
      have h2 : β i ⟨(k : V ≃ₗ[ZMod 2] V) (v0 : V), hkv0⟩ =
          ⟨delta x + delta y, delta_add_delta_mem x y⟩ := Subtype.ext h1
      have h3 : (⟨(k : V ≃ₗ[ZMod 2] V) (v0 : V), hkv0⟩ : ↥(commGL (Lc i) ⊤)) =
          (β i).symm ⟨delta x + delta y, delta_add_delta_mem x y⟩ := (β i).eq_symm_apply.2 h2
      have h4 := congrArg Subtype.val h3
      rw [← h4]
      exact hgen k (hLK i hkL) (v0 : V) hv0Y
    let f : ↥(SL2Modules.evenWeight Ω) →ₗ[ZMod 2] V :=
      (commGL (Lc i) ⊤).subtype ∘ₗ (β i).symm.toLinearMap
    have hNpair : ∀ x y : Ω, x ≠ y →
        (⟨delta x + delta y, delta_add_delta_mem x y⟩ : ↥(SL2Modules.evenWeight Ω)) ∈ M.comap f := by
      intro x y hxy
      exact hpair x y hxy
    have hNtop : ∀ w : ↥(SL2Modules.evenWeight Ω), w ∈ M.comap f := by
      intro w
      have hne : Nonempty Ω := by
        rw [← Fintype.card_pos_iff]
        omega
      obtain ⟨o⟩ := hne
      have hw : w = ∑ L ∈ Finset.univ.erase o, (w : Ω → ZMod 2) L •
          (⟨delta L + delta o, delta_add_delta_mem L o⟩ : ↥(SL2Modules.evenWeight Ω)) := by
        apply Subtype.ext
        rw [Submodule.coe_sum]
        simp only [Submodule.coe_smul]
        exact eq_sum_pairs o w.2
      rw [hw]
      refine Submodule.sum_mem _ fun L hL => ?_
      exact Submodule.smul_mem _ _ (hNpair L o (Finset.mem_erase.1 hL).1)
    have hu' : f (β i ⟨u, hu⟩) ∈ M := hNtop (β i ⟨u, hu⟩)
    have hfu : f (β i ⟨u, hu⟩) = u := by
      show (((β i).symm (β i ⟨u, hu⟩) : ↥(commGL (Lc i) ⊤)) : V) = u
      rw [(β i).symm_apply_apply]
    rwa [hfu] at hu'
  have hV := V_sum ctx
  refine top_le_iff.1 ?_
  rw [← hV]
  exact sup_le (iSup_le hIM) (hCY.trans hYM)

end Span

end CFSG.QuasithinUnique.Setup.Lift
