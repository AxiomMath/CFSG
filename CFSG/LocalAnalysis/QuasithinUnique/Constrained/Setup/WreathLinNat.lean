module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LayerS3
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.WreathLinBase
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.WreathLinDefs

public section

universe v

namespace CFSG.QuasithinUnique.Setup.Wreath

open CFSG.QuasithinUnique.Setup.Offender CFSG.QuasithinUnique.Setup.Layer CFSG.Quasithin.B6
  CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup
open scoped commutatorElement

variable {k : Type*} [Field k] {V : Type v} [AddCommGroup V] [Module k V]

section NatFamily

variable {H N A : Subgroup (V ≃ₗ[k] V)} {r : ℕ} {g : Fin r → V ≃ₗ[k] V}

theorem natI_ne_bot (hnat : NaturalS3Factors H N A g) (i : Fin r) : natI N A g i ≠ ⊥ := by
  intro h
  have h2 := hnat.finrank_I i
  rw [h] at h2
  simp at h2

theorem natI_injective (hnat : NaturalS3Factors H N A g) : Function.Injective (natI N A g) :=
  hnat.I_indep.injective (natI_ne_bot hnat)

theorem actsAs_one_of_mem_B (hnat : NaturalS3Factors H N A g) {b : V ≃ₗ[k] V}
    (hb : b ∈ natB H N A) : ActsAs (natI N A g) b 1 := by
  rw [hnat.B_eq] at hb
  intro i v
  show b v ∈ natI N A g i ↔ v ∈ natI N A g i
  refine Subgroup.iSup_induction (natS N A g)
    (C := fun b => ∀ w, b w ∈ natI N A g i ↔ w ∈ natI N A g i) hb ?_ ?_ ?_ v
  · intro j s hs w
    by_cases hji : j = i
    · subst hji
      obtain ⟨hW, -⟩ := hnat.S_action j
      constructor
      · intro hsw
        have := hW s⁻¹ ((natS N A g j).inv_mem hs) _ hsw
        simpa [ρ_inv_apply] using this
      · exact hW s hs w
    · constructor
      · intro hsw
        have h1 := hnat.S_fix_I j i hji hsw s⁻¹ ((natS N A g j).inv_mem hs)
        have h2 : s⁻¹ (s w) = w := by
          rw [← LinearEquiv.mul_apply, inv_mul_cancel]; rfl
        have h1' : s⁻¹ (s w) = s w := h1
        rw [h2] at h1'
        rw [h1']
        exact hsw
      · intro hw
        have := hnat.S_fix_I j i hji hw s hs
        have h1 : s w = w := this
        rw [h1]
        exact hw
  · intro w
    exact Iff.rfl
  · intro b b' hb hb' w
    show b (b' w) ∈ natI N A g i ↔ w ∈ natI N A g i
    exact (hb _).trans (hb' w)

theorem conjSub_eq_of_mem_B (hnat : NaturalS3Factors H N A g) {b : V ≃ₗ[k] V}
    (hb : b ∈ natB H N A) (j : Fin r) :
    conjSub b (natS N A g j) = natS N A g j ∧ conjSub b (natL N A g j) = natL N A g j := by
  obtain ⟨j', hS, hL, hI⟩ := hnat.S_perm b (hnat.B_le hb) j
  have hI' : (natI N A g j).map (b : V →ₗ[k] V) = natI N A g j :=
    (actsAs_iff_map.1 (actsAs_one_of_mem_B hnat hb)) j
  have : j' = j := natI_injective hnat (hI.symm.trans hI')
  subst this
  exact ⟨hS, hL⟩

theorem fix_of_mem_B (hnat : NaturalS3Factors H N A g) {b : V ≃ₗ[k] V}
    (hb : b ∈ natB H N A) : ∀ c ∈ fixGL (natD N A g), b c = c := by
  rw [hnat.B_eq] at hb
  refine Subgroup.iSup_induction (natS N A g) (C := fun b => ∀ c ∈ fixGL (natD N A g), b c = c)
    hb ?_ ?_ ?_
  · intro i s hs c hc
    exact hnat.S_fix_C i hc s hs
  · intro c _
    rfl
  · intro b b' hb hb' c hc
    show b (b' c) = c
    rw [hb' c hc, hb c hc]

theorem eq_one_of_mem_B_fix_W (hnat : NaturalS3Factors H N A g) {b : V ≃ₗ[k] V}
    (hb : b ∈ natB H N A) (hW : ∀ w ∈ natW N A g, b w = w) : b = 1 := by
  apply LinearEquiv.ext
  intro v
  have hv : v ∈ natW N A g ⊔ fixGL (natD N A g) := by
    rw [hnat.V_compl.sup_eq_top]
    exact Submodule.mem_top
  obtain ⟨w, hw, c, hc, rfl⟩ := Submodule.mem_sup.1 hv
  rw [map_add, hW w hw, fix_of_mem_B hnat hb c hc]
  rfl

theorem exists_base_agree (hnat : NaturalS3Factors H N A g) {W : Submodule k V}
    (hWeq : W = ⨆ i, natI N A g i) (g' : W ≃ₗ[k] W)
    (hg' : ∀ i, ∀ w : W, ((g' w : W) : V) ∈ natI N A g i ↔ (w : V) ∈ natI N A g i) :
    ∃ b ∈ natB H N A, ∀ w : W, ((g' w : W) : V) = b w := by
  classical
  have hIW : ∀ i, natI N A g i ≤ W := fun i => hWeq ▸ le_iSup (natI N A g) i
  have key : ∀ s : Finset (Fin r), ∃ b ∈ natB H N A,
      (∀ j ∈ s, ∀ w : W, (w : V) ∈ natI N A g j → b w = ((g' w : W) : V)) ∧
      (∀ j ∉ s, ∀ w ∈ natI N A g j, b w = w) := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact ⟨1, Subgroup.one_mem _, by simp, by simp⟩
    | insert j s hj ih =>
      obtain ⟨b, hbB, hb1, hb2⟩ := ih
      obtain ⟨hWj, hbij⟩ := hnat.S_action j
      obtain ⟨sj, hsj⟩ := hbij.2 (restrictPlane (hIW j) g' (hg' j))
      have hsjv : ∀ w : W, (w : V) ∈ natI N A g j →
          (sj : V ≃ₗ[k] V) w = ((g' w : W) : V) := by
        intro w hw
        have := congrArg
          (fun f : ↥(natI N A g j) ≃ₗ[k] ↥(natI N A g j) => ((f ⟨w, hw⟩ : natI N A g j) : V)) hsj
        simpa [resSub_apply, restrictPlane_apply] using this
      have hsjB : (sj : V ≃ₗ[k] V) ∈ natB H N A := hnat.S_le_B j sj.2
      refine ⟨b * sj, (natB H N A).mul_mem hbB hsjB, ?_, ?_⟩
      · intro j' hj' w hw
        show b ((sj : V ≃ₗ[k] V) w) = ((g' w : W) : V)
        rcases Finset.mem_insert.1 hj' with hj'j | hj's
        · subst hj'j
          have hg'w : ((g' w : W) : V) ∈ natI N A g j' := (hg' j' w).2 hw
          rw [hsjv w hw]
          exact hb2 j' hj ((g' w : W) : V) hg'w
        · have hne : j' ≠ j := fun e => hj (e ▸ hj's)
          have hfix : (sj : V ≃ₗ[k] V) w = w := hnat.S_fix_I j j' (Ne.symm hne) hw sj sj.2
          rw [hfix]
          exact hb1 j' hj's w hw
      · intro j' hj' w hw
        show b ((sj : V ≃ₗ[k] V) w) = w
        have hne : j' ≠ j := fun e => hj' (Finset.mem_insert.2 (Or.inl e))
        have hns : j' ∉ s := fun e => hj' (Finset.mem_insert_of_mem e)
        have hfix : (sj : V ≃ₗ[k] V) w = w := hnat.S_fix_I j j' (Ne.symm hne) hw sj sj.2
        rw [hfix]
        exact hb2 j' hns w hw
  obtain ⟨b, hbB, hb1, -⟩ := key Finset.univ
  refine ⟨b, hbB, fun w => ?_⟩
  have hw : (w : V) ∈ ⨆ i, natI N A g i := hWeq ▸ w.2
  have := Submodule.iSup_induction (natI N A g)
    (motive := fun v => ∃ hv : v ∈ W, b v = ((g' ⟨v, hv⟩ : W) : V)) hw ?_ ?_ ?_
  · obtain ⟨hv, h⟩ := this
    exact h.symm
  · intro i v hv
    exact ⟨hIW i hv, hb1 i (Finset.mem_univ i) ⟨v, hIW i hv⟩ hv⟩
  · refine ⟨W.zero_mem, ?_⟩
    have e : (⟨(0 : V), W.zero_mem⟩ : W) = 0 := rfl
    rw [e, map_zero]
    simp
  · rintro x y ⟨hx, hhx⟩ ⟨hy, hhy⟩
    refine ⟨W.add_mem hx hy, ?_⟩
    have e : (⟨x + y, W.add_mem hx hy⟩ : W) = ⟨x, hx⟩ + ⟨y, hy⟩ := rfl
    rw [e, map_add, map_add, Submodule.coe_add, hhx, hhy]

end NatFamily

end CFSG.QuasithinUnique.Setup.Wreath
