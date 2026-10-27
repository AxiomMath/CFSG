module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.OutFactsBeta
public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.M22FusionData
public import Certificates.Certificate24800

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.M22Std

open CFSG.EvenSporadicStandard.M22Std.TabCheck CFSG.EvenSporadicStandard.M22Std.FusionCheck
  CFSG.EvenSporadicStandard.M22Std.OutCheck CFSG.Blueprint.NativeSporadic
  CFSG.Monster.B.TwoA.Fischer

theorem s0Check_spec :
    (s0Tabs.length = 256 ∧ s0Tabs.Nodup ∧ ∀ l ∈ s0Tabs, ∀ g ∈ s0Gens, tmul l g ∈ s0Tabs) ∧
    tmul betaTab betaTab = idTab ∧
    ((∀ g ∈ s0Gens, comm tTab g = true) ∧
      ∀ l ∈ s0Tabs, (∀ g ∈ s0Gens, comm l g = true) → l = idTab ∨ l = tTab) ∧
    (∀ g ∈ s0Gens, normOK (elemTabs 1) g = true) ∧
    (orbitTabs s0Tabs f1Tabs x8Tab).length = 8 ∧
    ((s0Outer.filter fun l => decide (tmul l l = idTab)).length = 36 ∧
      (s0Outer.filter fun l => decide (tmul l l = tTab)).length = 20) := by
  have h := Certificates.certificate24800
  simp only [s0Check, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6⟩

theorem autTab_mul (g h : MulAut (Carrier .M22)) :
    autTab (g * h) = tmul (autTab g) (autTab h) := autTabMap.mul g h

theorem autTab_one : autTab (1 : MulAut (Carrier .M22)) = idTab := autTabMap.one

theorem autTab_injective : Function.Injective (autTab : MulAut (Carrier .M22) → Tab) :=
  autTabMap.inj

theorem autTab_conj_iff (α : MulAut (Carrier .M22)) (x y : Carrier .M22) :
    tmul (autTab α) (tab x) = tmul (tab y) (autTab α) ↔ α x = y := by
  have h0 : rho α * toPerm x = toPerm (α x) * rho α := by
    rw [toPerm_apply_rho]
    group
  have e1 : tmul (autTab α) (tab x) = tabP (rho α * toPerm x) := (tabP_mul _ _).symm
  have e2 : tmul (tab y) (autTab α) = tabP (toPerm y * rho α) := (tabP_mul _ _).symm
  rw [e1, e2, tabP_injective.eq_iff, h0, mul_left_inj]
  exact ⟨fun h => toPerm_inj h, fun h => by rw [h]⟩

theorem autTab_conj_tEl : autTab (MulAut.conj tEl) = tTab := by
  rw [autTab_conj, tab_tEl]

@[expose] noncomputable def s0Gens' : List (MulAut (Carrier .M22)) :=
  betaAut :: sylowGens.map MulAut.conj

theorem map_autTab_s0Gens' : s0Gens'.map autTab = s0Gens := by
  simp only [s0Gens', List.map_cons, autTab_betaAut, List.map_map, s0Gens]
  congr 1
  rw [show (autTab ∘ MulAut.conj : Carrier .M22 → Tab) = tab from funext autTab_conj]
  exact tab_sylowGens

@[expose] noncomputable def s0 : Subgroup (MulAut (Carrier .M22)) :=
  Subgroup.closure {g | g ∈ s0Gens'}

theorem betaAut_mem_s0 : betaAut ∈ s0 :=
  Subgroup.subset_closure (List.mem_cons_self ..)

theorem isTabsOf_s0 : autTabMap.IsTabsOf s0 s0Tabs := by
  have hmap : s0Gens'.map autTabMap.tb = s0Gens := map_autTab_s0Gens'
  have hcl : ∀ l ∈ span (s0Gens'.map autTabMap.tb), ∀ g ∈ s0Gens',
      tmul l (autTabMap.tb g) ∈ span (s0Gens'.map autTabMap.tb) := by
    rw [hmap]
    intro l hl g hg
    refine (s0Check_spec).1.2.2 l hl _ ?_
    rw [← hmap]
    exact List.mem_map_of_mem hg
  have := TabMap.isTabsOf_closure (τ := autTabMap) s0Gens' hcl
  rw [hmap] at this
  exact this

theorem mem_s0_iff (α : MulAut (Carrier .M22)) : α ∈ s0 ↔ autTab α ∈ s0Tabs :=
  isTabsOf_s0.mem_iff α

theorem card_s0 : Nat.card s0 = 256 := by
  rw [isTabsOf_s0.card (s0Check_spec).1.2.1, (s0Check_spec).1.1]

theorem isPGroup_s0 : IsPGroup 2 s0 := IsPGroup.of_card (n := 8) (by rw [card_s0]; norm_num)

theorem index_s0_odd : ¬ 2 ∣ s0.index := by
  have h1 := Subgroup.card_mul_index s0
  have h2 : Nat.card (MulAut (Carrier .M22)) = 887040 := catalog_M22_full_automorphism_order.1
  rw [card_s0, h2] at h1
  omega

theorem s0_center : ∀ α ∈ s0, (∀ β ∈ s0, β * α = α * β) ↔ (α = 1 ∨ α = MulAut.conj tEl) := by
  intro α hα
  constructor
  · intro hc
    have h1 := (s0Check_spec).2.2.1.2 (autTab α) ((mem_s0_iff α).1 hα) (fun g hg => ?_)
    · rcases h1 with h | h
      · exact Or.inl (autTab_injective (h.trans autTab_one.symm))
      · exact Or.inr (autTab_injective (h.trans autTab_conj_tEl.symm))
    · rw [← map_autTab_s0Gens'] at hg
      obtain ⟨γ, hγ, rfl⟩ := List.mem_map.1 hg
      have := hc γ (Subgroup.subset_closure hγ)
      simp only [TabCheck.comm, decide_eq_true_eq]
      rw [← autTab_mul, ← autTab_mul, this]
  · rintro (rfl | rfl)
    · intro β _
      rw [mul_one, one_mul]
    · intro β hβ
      have hle : s0 ≤ Subgroup.centralizer {MulAut.conj tEl} := by
        refine (Subgroup.closure_le _).2 fun γ hγ => ?_
        rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
        apply autTab_injective
        rw [autTab_mul, autTab_mul, autTab_conj_tEl]
        have hg : autTab γ ∈ s0Gens := by
          rw [← map_autTab_s0Gens']
          exact List.mem_map_of_mem hγ
        have := (s0Check_spec).2.2.1.1 _ hg
        simp only [TabCheck.comm, decide_eq_true_eq] at this
        exact this.symm
      exact Subgroup.mem_centralizer_singleton_iff.1 (hle hβ)

end CFSG.EvenSporadicStandard.M22Std
