module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftBaumannTools
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftSylow5
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftOffenderNat

public section

namespace CFSG.QuasithinUnique.Setup.Lift

open CFSG.QuasithinUnique.Setup.Offender CFSG.QuasithinUnique.Setup.Layer CFSG.QuasithinUnique
  CFSG.Quasithin.B6 CFSG.QuasithinUnique.Setup.SL2Modules
open scoped MatrixGroups LinearAlgebra.Projectivization commutatorElement
open Projectivization

universe v

section Pairs

variable {Ω : Type*} [DecidableEq Ω]

theorem perm_preserves_pair {a b : Ω} (hab : a ≠ b) (τ : Equiv.Perm Ω)
    (h : permAct τ (delta a + delta b) = delta a + delta b) :
    (τ a = a ∧ τ b = b) ∨ (τ a = b ∧ τ b = a) := by
  have key : ∀ p : Ω, p = a ∨ p = b → τ p = a ∨ τ p = b := by
    intro p hp
    have h1 := congrFun h (τ p)
    simp only [permAct, Pi.add_apply, delta, Pi.single_apply, Equiv.symm_apply_apply] at h1
    by_contra hc
    push Not at hc
    rcases hp with rfl | rfl
    · simp [hc.1, hc.2, hab] at h1
    · simp [hc.1, hc.2, hab.symm] at h1
  have ha := key a (Or.inl rfl)
  have hb := key b (Or.inr rfl)
  rcases ha with ha | ha <;> rcases hb with hb | hb
  · exact absurd (τ.injective (ha.trans hb.symm)) hab
  · exact Or.inl ⟨ha, hb⟩
  · exact Or.inr ⟨ha, hb⟩
  · exact absurd (τ.injective (ha.trans hb.symm)) hab

theorem permAct_fix_of_mem_closure {a b c d : Ω} (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c)
    (hbd : b ≠ d) {σ : Equiv.Perm Ω} (hσ : σ ∈ Subgroup.closure {Equiv.swap a b, Equiv.swap c d}) :
    permAct σ (delta a + delta b) = delta a + delta b := by
  induction hσ using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with rfl | rfl
    · rw [permAct_add, permAct_delta, permAct_delta, Equiv.swap_apply_left, Equiv.swap_apply_right,
        add_comm]
    · rw [permAct_add, permAct_delta, permAct_delta, Equiv.swap_apply_of_ne_of_ne hac had,
        Equiv.swap_apply_of_ne_of_ne hbc hbd]
  | one => exact rfl
  | mul x y _ _ hx hy => rw [permAct_mul, hy, hx]
  | inv x _ hx =>
    have h := congrArg (permAct x⁻¹) hx
    rw [← permAct_mul, inv_mul_cancel, permAct_one'] at h
    exact h.symm

end Pairs

section Action

variable {V : Type v} [AddCommGroup V] [Module (ZMod 2) V] [Finite V] {F : Type} [Field F]
  [Fintype F] [Fintype (ℙ F (Fin 2 → F))] [DecidableEq (ℙ F (Fin 2 → F))]
  {H T : Subgroup (V ≃ₗ[ZMod 2] V)} {n r : ℕ} {Lc : Fin r → Subgroup (V ≃ₗ[ZMod 2] V)}
  {ctx : FamilyCtx H T n F r Lc} {i : Fin r}

omit [Finite V] in
theorem DelModel.exists_perm_of_normalizes (M : DelModel ctx i)
    (h5 : Fintype.card (ℙ F (Fin 2 → F)) = 5) {t : V ≃ₗ[ZMod 2] V}
    (ht : t ∈ Subgroup.normalizer (Lc i : Set (V ≃ₗ[ZMod 2] V))) :
    ∃ τ : Equiv.Perm (ℙ F (Fin 2 → F)), ∀ u u' : ↥(commGL (Lc i) ⊤), (u' : V) = t (u : V) →
      ((M.β u' : ↥(SL2Modules.evenWeight (ℙ F (Fin 2 → F)))) : ℙ F (Fin 2 → F) → ZMod 2) =
        permAct τ ((M.β u : ↥(SL2Modules.evenWeight (ℙ F (Fin 2 → F)))) : ℙ F (Fin 2 → F) → ZMod 2) := by
  classical
  have hmap : (commGL (Lc i) ⊤).map (t : V →ₗ[ZMod 2] V) = commGL (Lc i) ⊤ := by
    have h := commGL_conjSub (Lc i) t
    rw [conjSub_eq_self ht] at h
    exact h.symm
  let Tm : ↥(commGL (Lc i) ⊤) ≃ₗ[ZMod 2] ↥(commGL (Lc i) ⊤) :=
    LinearEquiv.ofSubmodules (t : V ≃ₗ[ZMod 2] V) _ _ hmap
  have hTm : ∀ u : ↥(commGL (Lc i) ⊤), (Tm u : V) = t (u : V) := fun u => rfl
  let E : ↥(SL2Modules.evenWeight (ℙ F (Fin 2 → F))) ≃ₗ[ZMod 2] ↥(SL2Modules.evenWeight (ℙ F (Fin 2 → F))) :=
    M.β.symm.trans (Tm.trans M.β)
  let Eu : (Module.End (ZMod 2) ↥(SL2Modules.evenWeight (ℙ F (Fin 2 → F))))ˣ :=
    { val := E.toLinearMap
      inv := E.symm.toLinearMap
      val_inv := LinearMap.ext fun w => E.apply_symm_apply w
      inv_val := LinearMap.ext fun w => E.symm_apply_apply w }
  have hEβ : ∀ u : ↥(commGL (Lc i) ⊤), E (M.β u) = M.β (Tm u) := fun u => by
    show M.β (Tm (M.β.symm (M.β u))) = _
    rw [M.β.symm_apply_apply]
  have hN : ∀ σ ∈ alternatingGroup (ℙ F (Fin 2 → F)), ∃ σ' ∈ alternatingGroup (ℙ F (Fin 2 → F)),
      Eu * permU σ * Eu⁻¹ = permU σ' := by
    intro σ hσ
    have hσ' : σ ∈ ((Lc i).subgroupOf (blockB H (Lc i))).map M.ψ.toMonoidHom := by
      rw [M.alt]
      exact hσ
    obtain ⟨l, hl, hlσ⟩ := hσ'
    have hlσ' : M.ψ l = σ := hlσ
    subst hlσ'
    have hl' : (l : V ≃ₗ[ZMod 2] V) ∈ Lc i := hl
    have hconj : t * (l : V ≃ₗ[ZMod 2] V) * t⁻¹ ∈ Lc i :=
      (Subgroup.mem_normalizer_iff.1 ht _).1 hl'
    let l' : ↥(blockB H (Lc i)) := ⟨t * (l : V ≃ₗ[ZMod 2] V) * t⁻¹, Lc_le_blockB ctx i hconj⟩
    refine ⟨M.ψ l', ?_, ?_⟩
    · rw [← M.alt]
      exact ⟨l', hconj, rfl⟩
    · apply Units.ext
      apply LinearMap.ext
      intro w
      obtain ⟨u, rfl⟩ : ∃ u : ↥(commGL (Lc i) ⊤), M.β u = w :=
        ⟨M.β.symm w, M.β.apply_symm_apply w⟩
      obtain ⟨v, hv⟩ : ∃ v : ↥(commGL (Lc i) ⊤), Tm v = u := ⟨Tm.symm u, Tm.apply_symm_apply u⟩
      have hEs : E.symm (M.β u) = M.β v := by
        rw [LinearEquiv.symm_apply_eq]
        show M.β u = M.β (Tm (M.β.symm (M.β v)))
        rw [M.β.symm_apply_apply, hv]
      let u'' : ↥(commGL (Lc i) ⊤) :=
        ⟨(l : V ≃ₗ[ZMod 2] V) (v : V), blockB_apply_mem_I ctx l.2 v.2⟩
      have hc1 : ((M.β u'' : ↥(SL2Modules.evenWeight (ℙ F (Fin 2 → F)))) : ℙ F (Fin 2 → F) → ZMod 2) =
          permAct (M.ψ l) (M.β v) := M.compat l v u'' rfl
      have hP : (permU (M.ψ l)).val (M.β v) = M.β u'' :=
        Subtype.ext ((permU_apply (M.ψ l) (M.β v)).trans hc1.symm)
      have hinv : t⁻¹ (t (v : V)) = (v : V) :=
        ρ_inv_apply (MonoidHom.id (V ≃ₗ[ZMod 2] V)) t (v : V)
      have hu3 : ((Tm u'' : ↥(commGL (Lc i) ⊤)) : V) = (l' : V ≃ₗ[ZMod 2] V) (u : V) := by
        have hvu : (u : V) = t (v : V) := by rw [← hv, hTm]
        rw [hTm, hvu]
        show t ((l : V ≃ₗ[ZMod 2] V) (v : V)) =
          (t * (l : V ≃ₗ[ZMod 2] V) * t⁻¹) (t (v : V))
        rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, hinv]
      have hc2 := M.compat l' u (Tm u'') hu3
      have hfin : (Eu * permU (M.ψ l) * Eu⁻¹).val (M.β u) = M.β (Tm u'') := by
        show E ((permU (M.ψ l)).val (E.symm (M.β u))) = M.β (Tm u'')
        rw [hEs, hP, hEβ]
      apply Subtype.ext
      rw [hfin]
      exact hc2.trans (permU_apply (M.ψ l') (M.β u)).symm
  obtain ⟨τ, hτ, -⟩ := deleted_five_normalizer h5 Eu hN
  refine ⟨τ, fun u u' hu' => ?_⟩
  have hu'eq : u' = Tm u := Subtype.ext (by rw [hu', hTm])
  have h1 : M.β u' = (permU τ).val (M.β u) :=
    calc M.β u' = M.β (Tm u) := by rw [hu'eq]
      _ = E (M.β u) := (hEβ u).symm
      _ = (permU τ).val (M.β u) :=
        congrArg (fun h : (Module.End (ZMod 2) ↥(SL2Modules.evenWeight (ℙ F (Fin 2 → F))))ˣ =>
          h.val (M.β u)) hτ
  exact (congrArg Subtype.val h1).trans (permU_apply τ (M.β u))

end Action

section Main

variable {V : Type v} [AddCommGroup V] [Module (ZMod 2) V] [Finite V] {F : Type} [Field F]
  [Fintype F] [Fintype (ℙ F (Fin 2 → F))] [DecidableEq (ℙ F (Fin 2 → F))]
  {H T : Subgroup (V ≃ₗ[ZMod 2] V)} {n r : ℕ} {Lc : Fin r → Subgroup (V ≃ₗ[ZMod 2] V)}

theorem deleted_baumann (ctx : FamilyCtx H T n F r Lc)
    (hZ : ∀ i, commGL (Lc i) ⊤ ⊓ fixGL (Lc i) = ⊥)
    (h5 : Fintype.card (ℙ F (Fin 2 → F)) = 5) (M : ∀ i, DelModel ctx i)
    (D : Fin r → Subgroup (V ≃ₗ[ZMod 2] V)) (hD : ∀ i, D i ≤ blockB H (Lc i))
    (hDM : ∀ i, ∃ a b c d : ℙ F (Fin 2 → F), a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d ∧
      ((D i).subgroupOf (blockB H (Lc i))).map (M i).ψ.toMonoidHom =
        Subgroup.closure {Equiv.swap a b, Equiv.swap c d})
    {t : V ≃ₗ[ZMod 2] V} (ht : t ∈ T) (hfix : ∀ v ∈ fixGL (⨆ i, D i), t v = v) :
    t ∈ ⨆ i, D i := by
  classical
  refine eq_iSup_of_actions ctx (T_le_H ctx ht) D hD fun i => ?_
  obtain ⟨a, b, c, d, hab, hac, had, hbc, hbd, hcd, himg⟩ := hDM i
  have hDfix : ∀ x y : ℙ F (Fin 2 → F),
      (∀ σ ∈ ((D i).subgroupOf (blockB H (Lc i))).map (M i).ψ.toMonoidHom,
        permAct σ (delta x + delta y) = delta x + delta y) →
      (((M i).β.symm (pairVec x y) : ↥(commGL (Lc i) ⊤)) : V) ∈ fixGL (⨆ j, D j) := by
    intro x y hxy
    have hle : (⨆ j, D j) ≤
        MulAction.stabilizer (V ≃ₗ[ZMod 2] V) (((M i).β.symm (pairVec x y) : ↥(commGL (Lc i) ⊤)) : V) := by
      refine iSup_le fun j => ?_
      by_cases hji : j = i
      · rw [hji]
        intro z hz
        have hzB : z ∈ blockB H (Lc i) := hD i hz
        have hz' : (⟨z, hzB⟩ : ↥(blockB H (Lc i))) ∈ (D i).subgroupOf (blockB H (Lc i)) := hz
        have hperm : permAct ((M i).ψ ⟨z, hzB⟩) (delta x + delta y) = delta x + delta y :=
          hxy _ ⟨⟨z, hzB⟩, hz', rfl⟩
        set u1 : ↥(commGL (Lc i) ⊤) := (M i).β.symm (pairVec x y) with hu1
        let u' : ↥(commGL (Lc i) ⊤) := ⟨z (u1 : V), blockB_apply_mem_I ctx hzB u1.2⟩
        have hc := (M i).compat ⟨z, hzB⟩ u1 u' rfl
        have hβ : (M i).β u1 = pairVec x y := (M i).β.apply_symm_apply _
        rw [hβ] at hc
        have hβ' : (M i).β u' = (M i).β u1 := by
          apply Subtype.ext
          rw [hc, hβ]
          exact hperm
        exact congrArg Subtype.val ((M i).β.injective hβ')
      · intro z hz
        exact mem_centSub.1 (blockB_le_centSub_I ctx (i := j) (j := i) (Ne.symm hji) (hD j hz)) _
          ((M i).β.symm (pairVec x y)).2
    intro g hg
    exact hle hg
  have hnz : ∀ x y : ℙ F (Fin 2 → F), x ≠ y →
      (((M i).β.symm (pairVec x y) : ↥(commGL (Lc i) ⊤)) : V) ∉ fixGL (Lc i) := by
    intro x y hxy hmem
    have h1 : (((M i).β.symm (pairVec x y) : ↥(commGL (Lc i) ⊤)) : V) ∈
        commGL (Lc i) ⊤ ⊓ fixGL (Lc i) := ⟨((M i).β.symm (pairVec x y)).2, hmem⟩
    rw [hZ i] at h1
    have h2 : (M i).β.symm (pairVec x y) = 0 := Subtype.ext ((Submodule.mem_bot _).1 h1)
    have h3 : pairVec x y = 0 := by simpa using congrArg (M i).β h2
    have h4 := congrFun (congrArg Subtype.val h3) x
    simp [pairVec, delta, hxy] at h4
  have hfix1 : (((M i).β.symm (pairVec a b) : ↥(commGL (Lc i) ⊤)) : V) ∈ fixGL (⨆ j, D j) :=
    hDfix a b (by
      rw [himg]
      exact fun σ hσ => permAct_fix_of_mem_closure hac had hbc hbd hσ)
  have hfix2 : (((M i).β.symm (pairVec c d) : ↥(commGL (Lc i) ⊤)) : V) ∈ fixGL (⨆ j, D j) :=
    hDfix c d (by
      rw [himg, Set.pair_comm]
      exact fun σ hσ => permAct_fix_of_mem_closure hac.symm hbc.symm had.symm hbd.symm hσ)
  have htfix1 := hfix _ hfix1
  have htfix2 := hfix _ hfix2
  have hnorm := normalizes_of_fixed ctx ht ((M i).β.symm (pairVec a b)).2 (hnz a b hab) htfix1
  obtain ⟨τ, hτ⟩ := (M i).exists_perm_of_normalizes h5 hnorm
  have hτ1 : permAct τ (delta a + delta b) = delta a + delta b := by
    have h := hτ ((M i).β.symm (pairVec a b)) ((M i).β.symm (pairVec a b)) htfix1.symm
    rw [(M i).β.apply_symm_apply] at h
    exact h.symm
  have hτ2 : permAct τ (delta c + delta d) = delta c + delta d := by
    have h := hτ ((M i).β.symm (pairVec c d)) ((M i).β.symm (pairVec c d)) htfix2.symm
    rw [(M i).β.apply_symm_apply] at h
    exact h.symm
  have hτmem := mem_four_of_pairs h5 hab hac had hbc hbd hcd τ (perm_preserves_pair hab τ hτ1)
    (perm_preserves_pair hcd τ hτ2)
  have hclos : τ ∈ Subgroup.closure ({Equiv.swap a b, Equiv.swap c d} :
      Set (Equiv.Perm (ℙ F (Fin 2 → F)))) := by
    rcases hτmem with h | h | h | h <;> rw [h]
    · exact one_mem _
    · exact Subgroup.subset_closure (Set.mem_insert _ _)
    · exact Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))
    · exact mul_mem (Subgroup.subset_closure (Set.mem_insert _ _))
        (Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _)))
  rw [← himg] at hclos
  obtain ⟨z, hz, hzτ⟩ := hclos
  have hzτ' : (M i).ψ z = τ := hzτ
  have hzD : (z : V ≃ₗ[ZMod 2] V) ∈ D i := hz
  refine ⟨(z : V ≃ₗ[ZMod 2] V), hzD, fun y hy => ?_⟩
  have hAn : Subgroup.zpowers t ≤ Subgroup.normalizer (Lc i : Set (V ≃ₗ[ZMod 2] V)) :=
    Subgroup.zpowers_le.2 hnorm
  have hty : t y ∈ commGL (Lc i) ⊤ :=
    isInvariant_commGL_of_le_normalizer hAn t (Subgroup.mem_zpowers t) y hy
  have hzy : (z : V ≃ₗ[ZMod 2] V) y ∈ commGL (Lc i) ⊤ := blockB_apply_mem_I ctx z.2 hy
  have h1 := hτ ⟨y, hy⟩ ⟨t y, hty⟩ rfl
  have h2 := (M i).compat z ⟨y, hy⟩ ⟨(z : V ≃ₗ[ZMod 2] V) y, hzy⟩ rfl
  rw [hzτ'] at h2
  have h3 : (M i).β ⟨t y, hty⟩ = (M i).β ⟨(z : V ≃ₗ[ZMod 2] V) y, hzy⟩ :=
    Subtype.ext (h1.trans h2.symm)
  have h4 : t y = (z : V ≃ₗ[ZMod 2] V) y := congrArg Subtype.val ((M i).β.injective h3)
  rw [h4, sub_self]
  exact Submodule.zero_mem _

end Main

end CFSG.QuasithinUnique.Setup.Lift
