module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftFamilyDelB

public section

namespace CFSG.QuasithinUnique.Setup.Lift

open CFSG.QuasithinUnique.Setup.Offender CFSG.QuasithinUnique.Setup.Layer CFSG.QuasithinUnique
open scoped LinearAlgebra.Projectivization commutatorElement
open Projectivization

universe v

section Tools

variable {V : Type v} [AddCommGroup V] [Module (ZMod 2) V] [Finite V] {F : Type} [Field F]
  [Fintype F] [Fintype (ℙ F (Fin 2 → F))] [DecidableEq (ℙ F (Fin 2 → F))]
  {H T : Subgroup (V ≃ₗ[ZMod 2] V)} {n r : ℕ} {Lc : Fin r → Subgroup (V ≃ₗ[ZMod 2] V)}

omit [Finite V] in
theorem add_self_eq_zero_zmod2 (v : V) : v + v = 0 := by
  rw [← two_smul (ZMod 2) v]
  have h2 : (2 : ZMod 2) = 0 := rfl
  rw [h2, zero_smul]

omit [Finite V] in
theorem blockB_apply_mem_I (ctx : FamilyCtx H T n F r Lc) {i : Fin r} {b : V ≃ₗ[ZMod 2] V}
    (hb : b ∈ blockB H (Lc i)) {x : V} (hx : x ∈ commGL (Lc i) ⊤) : b x ∈ commGL (Lc i) ⊤ :=
  blockB_isInvariant ctx i b hb x hx

omit [Finite V] in
theorem normalizes_of_fixed (ctx : FamilyCtx H T n F r Lc) {t : V ≃ₗ[ZMod 2] V} (ht : t ∈ T)
    {i : Fin r} {v : V} (hv : v ∈ commGL (Lc i) ⊤) (hvz : v ∉ fixGL (Lc i)) (htv : t v = v) :
    t ∈ Subgroup.normalizer (Lc i : Set (V ≃ₗ[ZMod 2] V)) := by
  classical
  obtain ⟨j, hjL, -, hjI⟩ := family_perm ctx ht i
  by_cases hji : j = i
  · subst hji
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr hjL
  · exfalso
    have hvj : v ∈ commGL (Lc j) ⊤ := by
      rw [← hjI]
      exact ⟨v, hv, htv⟩
    let x : Fin r → V := fun k => if k = i then v else if k = j then v else 0
    have hx : ∀ k, x k ∈ commGL (Lc k) ⊤ := by
      intro k
      by_cases hki : k = i
      · subst hki
        simpa [x] using hv
      · by_cases hkj : k = j
        · subst hkj
          simpa [x, hki] using hvj
        · simp [x, hki, hkj]
    have hsum : ∑ k, x k = 0 := by
      rw [Finset.sum_eq_add i j (Ne.symm hji)]
      · simp [x, hji, add_self_eq_zero_zmod2]
      · intro k _ hk
        simp [x, hk.1, hk.2]
      · intro h
        exact absurd (Finset.mem_univ i) h
      · intro h
        exact absurd (Finset.mem_univ j) h
    have hs : ∑ k, x k ∈ fixGL (oddGen H) := by
      rw [hsum]
      exact Submodule.zero_mem _
    exact hvz (by simpa [x] using sum_direct ctx x hx hs i)

theorem eq_iSup_of_actions (ctx : FamilyCtx H T n F r Lc) {t : V ≃ₗ[ZMod 2] V} (ht : t ∈ H)
    (D : Fin r → Subgroup (V ≃ₗ[ZMod 2] V)) (hD : ∀ i, D i ≤ blockB H (Lc i))
    (hact : ∀ i, ∃ a ∈ D i, ∀ x ∈ commGL (Lc i) ⊤, t x - a x ∈ fixGL (oddGen H)) :
    t ∈ ⨆ i, D i := by
  classical
  choose a haD hat using hact
  have hDH : ∀ i, D i ≤ H := fun i => (hD i).trans ((blockB_le_J i).trans offenderJ_le)
  have key : ∀ s : Finset (Fin r), ∃ d ∈ ⨆ i ∈ s, D i,
      (∀ j ∈ s, ∀ x ∈ commGL (Lc j) ⊤, d x = a j x) ∧
      (∀ j ∉ s, ∀ x ∈ commGL (Lc j) ⊤, d x = x) ∧ ∀ c ∈ fixGL (oddGen H), d c = c := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact ⟨1, Subgroup.one_mem _, by simp, fun j _ x _ => rfl, fun c _ => rfl⟩
    | insert j s hj ih =>
      obtain ⟨d, hdmem, hd1, hd2, hd3⟩ := ih
      have haj : a j ∈ blockB H (Lc j) := hD j (haD j)
      have hmono : (⨆ i ∈ s, D i) ≤ ⨆ i ∈ insert j s, D i :=
        iSup₂_le fun i hi => le_iSup₂_of_le i (Finset.mem_insert_of_mem hi) le_rfl
      have hjmem : D j ≤ ⨆ i ∈ insert j s, D i :=
        le_iSup₂_of_le j (Finset.mem_insert_self j s) le_rfl
      have hfixI : ∀ k, k ≠ j → ∀ x ∈ commGL (Lc k) ⊤, a j x = x := fun k hkj x hx =>
        mem_centSub.1 (blockB_le_centSub_I ctx (i := j) (j := k) hkj haj) x hx
      refine ⟨d * a j, Subgroup.mul_mem _ (hmono hdmem) (hjmem (haD j)), ?_, ?_, ?_⟩
      · intro k hk x hx
        rcases Finset.mem_insert.1 hk with rfl | hks
        · show d (a k x) = a k x
          exact hd2 k hj _ (blockB_apply_mem_I ctx haj hx)
        · have hkj : k ≠ j := fun h => hj (h ▸ hks)
          show d (a j x) = a k x
          rw [hfixI k hkj x hx]
          exact hd1 k hks x hx
      · intro k hk x hx
        have hkj : k ≠ j := fun h => hk (h ▸ Finset.mem_insert_self j s)
        have hks : k ∉ s := fun h => hk (Finset.mem_insert_of_mem h)
        show d (a j x) = x
        rw [hfixI k hkj x hx]
        exact hd2 k hks x hx
      · intro c hc
        have hac : a j c = c := mem_centSub.1 (blockB_le_centSub_C ctx haj) c hc
        show d (a j c) = c
        rw [hac]
        exact hd3 c hc
  obtain ⟨d, hdmem, hd1, -, hd3⟩ := key Finset.univ
  have hdD : d ∈ ⨆ i, D i :=
    (iSup₂_le fun i _ => le_iSup D i : (⨆ i ∈ (Finset.univ : Finset (Fin r)), D i) ≤ ⨆ i, D i)
      hdmem
  have hdH : d ∈ H :=
    (iSup₂_le fun i _ => hDH i : (⨆ i ∈ (Finset.univ : Finset (Fin r)), D i) ≤ H) hdmem
  have hh : d⁻¹ * t ∈ H := H.mul_mem (H.inv_mem hdH) ht
  have hinvfix : ∀ c ∈ fixGL (oddGen H), d⁻¹ c = c := fun c hc =>
    calc d⁻¹ c = d⁻¹ (d c) := by rw [hd3 c hc]
      _ = c := ρ_inv_apply (MonoidHom.id (V ≃ₗ[ZMod 2] V)) d c
  have hf : ∀ w, (d⁻¹ * t) w - w ∈ fixGL (oddGen H) := by
    let S : Submodule (ZMod 2) V := (fixGL (oddGen H)).comap
      (((d⁻¹ * t : V ≃ₗ[ZMod 2] V) : V →ₗ[ZMod 2] V) - LinearMap.id)
    have hS : (⊤ : Submodule (ZMod 2) V) ≤ S := by
      rw [← V_sum ctx]
      refine sup_le (iSup_le fun i x hx => ?_) (fun c hc => ?_)
      · show (d⁻¹ * t) x - x ∈ fixGL (oddGen H)
        have hc1 : t x - a i x ∈ fixGL (oddGen H) := hat i x hx
        have hdx : d⁻¹ (a i x) = x := by
          rw [← hd1 i (Finset.mem_univ i) x hx]
          exact ρ_inv_apply (MonoidHom.id (V ≃ₗ[ZMod 2] V)) d x
        have e : (d⁻¹ * t) x = x + (t x - a i x) := by
          have h1 : t x = a i x + (t x - a i x) := by abel
          calc (d⁻¹ * t) x = d⁻¹ (t x) := rfl
            _ = d⁻¹ (a i x + (t x - a i x)) := by rw [← h1]
            _ = d⁻¹ (a i x) + d⁻¹ (t x - a i x) := map_add _ _ _
            _ = x + (t x - a i x) := by rw [hdx, hinvfix _ hc1]
        rw [e, add_sub_cancel_left]
        exact hc1
      · show (d⁻¹ * t) c - c ∈ fixGL (oddGen H)
        have htc : t c ∈ fixGL (oddGen H) := H_fix_C ctx ht hc
        have e : (d⁻¹ * t) c = t c := hinvfix _ htc
        rw [e]
        exact (fixGL (oddGen H)).sub_mem htc hc
    intro w
    exact hS (Submodule.mem_top : w ∈ ⊤)
  have h1 : d⁻¹ * t = 1 := faithful_VC ctx hh hf
  have h2 : t = d := by
    have := congrArg (fun z => d * z) h1
    simpa using this
  rw [h2]
  exact hdD

end Tools

end CFSG.QuasithinUnique.Setup.Lift
