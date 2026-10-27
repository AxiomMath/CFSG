module

public import CFSG.GF2Type.SmithTypeE.E8.FactsForm
public import CFSG.GF2Type.SmithTypeE.E8.FactsRel
public import CFSG.GF2Type.SmithTypeE.E8.E23Four

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

public section

namespace CFSG.GF2Type.SmithTypeE.E8.F

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.Minuscule CFSG.HardMathSupport.Cooperstein.Coordinator.Survivors
  CFSG.Quasithin.SmithCurtis CFSG.Quasithin.SmithCurtis.Chev CFSG.SeitzReduction
  CFSG.SeitzReduction.EPilot


@[expose] def Sθ : Set ↥(adjointGroup .E7 (ZMod 2)) :=
  {s | IsRootInvol s ∧ s * pinnedElt .E7 (highRoot .E7) (1 : ZMod 2) =
    pinnedElt .E7 (highRoot .E7) (1 : ZMod 2) * s}

theorem pinnedElt_mem_Sθ {β : Fin (Tag.rank .E7) → ℤ} (hβ : IsRoot .E7 β) (hpos : 0 < height β) :
    pinnedElt .E7 β (1 : ZMod 2) ∈ Sθ := by
  refine ⟨isRootInvol_pinnedElt hβ, ?_⟩
  exact commute_posUnipotent_xtheta (pinnedElt .E7 β (1 : ZMod 2))
    (pinnedElt_mem_posUnipotent hβ hpos)

theorem posUnipotent_mem_closure {u : ↥(adjointGroup .E7 (ZMod 2))}
    (hu : (u : ModGL .E7 (ZMod 2)) ∈ posUnipotent .E7 (ZMod 2)) : u ∈ Subgroup.closure Sθ := by
  exact posUnipotent_induction (P := fun g => g ∈ Subgroup.closure Sθ) (one_mem _)
    (fun g h hg hh => mul_mem hg hh) (fun g hg => inv_mem hg)
    (fun β hβ hpos => Subgroup.subset_closure (pinnedElt_mem_Sθ hβ hpos)) hu

theorem nC_mem_closure {i : Fin (Tag.rank .E7)} (hi : i ≠ ⟨0, by decide⟩) :
    nC .E7 (ZMod 2) i ∈ Subgroup.closure Sθ := by
  obtain ⟨-, h2, -, h4⟩ := cn_listed i hi
  have hi1 : IsRoot .E7 (Pi.single i 1) := isRoot_single .E7 i
  have hi2 : IsRoot .E7 (-Pi.single i 1) := CFSG.LieType.Chevalley.IsRoot.neg hi1
  have hθ : IsRoot .E7 (highRoot .E7) := isRoot_highRoot .E7
  have hpos : 0 < height (Pi.single i 1 : Fin (Tag.rank .E7) → ℤ) := by simp [height]
  have hA : pinnedElt .E7 (Pi.single i 1) (1 : ZMod 2) ∈ Sθ := pinnedElt_mem_Sθ hi1 hpos
  have hB : pinnedElt .E7 (-Pi.single i 1) (1 : ZMod 2) ∈ Sθ := by
    refine ⟨isRootInvol_pinnedElt hi2, ?_⟩
    exact (pinnedElt_commute hθ hi2 h4 (not_isRoot_of_listed h2)).symm
  rw [nC_eq_prod i]
  exact mul_mem (mul_mem (Subgroup.subset_closure hA) (Subgroup.subset_closure hB))
    (Subgroup.subset_closure hA)

theorem prod_nC_mem_closure (l : List (Fin (Tag.rank .E7))) (hl : ∀ i ∈ l, i ≠ ⟨0, by decide⟩) :
    (l.map (nC .E7 (ZMod 2))).prod ∈ Subgroup.closure Sθ := by
  induction l with
  | nil =>
    rw [List.map_nil, List.prod_nil]
    exact one_mem _
  | cons a l ih =>
    rw [List.map_cons, List.prod_cons]
    exact mul_mem (nC_mem_closure (hl a (by simp))) (ih fun i hi => hl i (by simp [hi]))

theorem exists_list_of_mem_closure_Sθ {g : ↥(adjointGroup .E7 (ZMod 2))}
    (hg : g ∈ Subgroup.closure Sθ) :
    ∃ l : List ↥(adjointGroup .E7 (ZMod 2)),
      (∀ s ∈ l, IsRootInvol s ∧ s * pinnedElt .E7 (highRoot .E7) (1 : ZMod 2) =
        pinnedElt .E7 (highRoot .E7) (1 : ZMod 2) * s) ∧ l.prod = g := by
  have hg' : g ∈ (Subgroup.closure Sθ).toSubmonoid := hg
  rw [Subgroup.closure_toSubmonoid] at hg'
  obtain ⟨l, hl, hprod⟩ := Submonoid.exists_list_of_mem_closure hg'
  refine ⟨l, fun s hs => ?_, hprod⟩
  rcases (Set.mem_union _ _ _).1 (hl s hs) with h | h
  · exact h
  · obtain ⟨hr, hc⟩ := Set.mem_inv.1 h
    have hss : s⁻¹ = s := by
      have h2 := inv_eq_of_mul_eq_one_right (isRootInvol_mul_self hr)
      rw [inv_inv] at h2
      exact h2.symm
    rw [hss] at hr hc
    exact ⟨hr, hc⟩

theorem word_xtheta {w w' : Fin e7Data.d →₀ ZMod 2} (hw : w ∈ weightVec) (hw' : w' ∈ weightVec)
    (hc : InComm (pinnedElt .E7 (highRoot .E7) (1 : ZMod 2)) w)
    (hc' : InComm (pinnedElt .E7 (highRoot .E7) (1 : ZMod 2)) w') :
    ∃ l : List ↥(adjointGroup .E7 (ZMod 2)),
      (∀ s ∈ l, IsRootInvol s ∧ s * pinnedElt .E7 (highRoot .E7) (1 : ZMod 2) =
        pinnedElt .E7 (highRoot .E7) (1 : ZMod 2) * s) ∧ e7Rep56 (ZMod 2) l.prod w = w' := by
  have hθ := isRoot_highRoot .E7
  have hDS : ∀ {v : Fin e7Data.d →₀ ZMod 2},
      InComm (pinnedElt .E7 (highRoot .E7) (1 : ZMod 2)) v → IsDSupp v := by
    rintro v ⟨c, rfl⟩ b hb
    by_contra h0
    exact hb (coord_rho_sub_ne_zero hθ c h0)
  obtain ⟨u, hu, a, rfl⟩ := exists_posUnipotent_basis' hw
  obtain ⟨u', hu', a', rfl⟩ := exists_posUnipotent_basis' hw'
  have hsingle : ∀ {x : Fin e7Data.d}, IsDSupp (Finsupp.single x (1 : ZMod 2)) →
      e7Data.wt x ⬝ᵥ highRoot .E7 = 1 := by
    intro x hx
    by_contra h
    have := hx x h
    simp at this
  have ha := hsingle (((posUnipotent_dsupp_qD hu).1 _).1 (hDS hc))
  have ha' := hsingle (((posUnipotent_dsupp_qD hu').1 _).1 (hDS hc'))
  obtain ⟨l, hl, hlw⟩ := exists_word_th ha ha'
  obtain ⟨L, hL, hLprod⟩ := exists_list_of_mem_closure_Sθ
    (g := u' * (l.map (nC .E7 (ZMod 2))).prod * u⁻¹)
    (mul_mem (mul_mem (posUnipotent_mem_closure hu') (prod_nC_mem_closure l hl))
      (inv_mem (posUnipotent_mem_closure hu)))
  refine ⟨L, hL, ?_⟩
  rw [hLprod, rep_mul_apply, rep_mul_apply, rep_inv_apply', hlw]

theorem word_core {r : ↥(adjointGroup .E7 (ZMod 2))} (hr : IsRootInvol r)
    {w w' : Fin e7Data.d →₀ ZMod 2} (hw : w ∈ weightVec) (hw' : w' ∈ weightVec)
    (hc : InComm r w) (hc' : InComm r w') :
    ∃ l : List ↥(adjointGroup .E7 (ZMod 2)), (∀ s ∈ l, IsRootInvol s ∧ s * r = r * s) ∧
      e7Rep56 (ZMod 2) l.prod w = w' := by
  obtain ⟨g, rfl⟩ := isConj_iff.mp hr
  have hconj : ∀ {v : Fin e7Data.d →₀ ZMod 2}, InComm (g * pinnedElt .E7 (highRoot .E7)
      (1 : ZMod 2) * g⁻¹) v → InComm (pinnedElt .E7 (highRoot .E7) (1 : ZMod 2))
      (e7Rep56 (ZMod 2) g⁻¹ v) := by
    rintro v ⟨c, rfl⟩
    refine ⟨e7Rep56 (ZMod 2) g⁻¹ c, ?_⟩
    rw [rep_conj_sub, rep_inv_apply']
  obtain ⟨l₀, hl₀, hl₀w⟩ := word_xtheta ((rep_mem_weightVec hw g⁻¹)) (rep_mem_weightVec hw' g⁻¹)
    (hconj hc) (hconj hc')
  refine ⟨l₀.map fun s => g * s * g⁻¹, ?_, ?_⟩
  · intro s hs
    obtain ⟨s₀, hs₀, rfl⟩ := List.mem_map.1 hs
    exact ⟨isRootInvol_conj (hl₀ s₀ hs₀).1 g, conj_comm g (hl₀ s₀ hs₀).2⟩
  · rw [list_prod_conj, rep_mul_apply, rep_mul_apply, hl₀w, rep_inv_apply]

theorem plane_core {r r' : ↥(adjointGroup .E7 (ZMod 2))} (hr : IsRootInvol r)
    (hr' : IsRootInvol r') (hncomm : ¬ r * r' = r' * r) (hnbraid : ¬ r * r' * r = r' * r * r') :
    ∃ w ∈ weightVec, InComm r w ∧ e7Rep56 (ZMod 2) r' w = w ∧ ¬ InComm r' w := by
  obtain ⟨g, β, hβ, rfl, rfl⟩ := pair_normal_form_involutions hr hr'
  have hθ := isRoot_highRoot .E7
  by_cases hneg : β = -highRoot .E7
  · exfalso
    apply hnbraid
    subst hneg
    exact conj_braid g (pinnedElt_braid hθ)
  by_cases hroot : IsRoot .E7 (highRoot .E7 + β)
  · obtain ⟨k, hk, rfl⟩ := exists_e8fRoot_eq hβ
    obtain ⟨a, ha1, ha0⟩ := plane_listed k (List.mem_range.2 hk) (by
      obtain ⟨j, hj, hjeq⟩ := exists_e8fRoot_eq hroot
      exact ⟨j, List.mem_range.2 hj, hjeq⟩)
    obtain ⟨a', ha'⟩ := unshift_exists a ha1
    have hdot : e7Data.wt a' ⬝ᵥ highRoot .E7 = -1 := by
      rw [ha', sub_dotProduct, ha1]
      have := th_dot_th
      rw [this]
      norm_num
    have hwt : e7Data.wt a = e7Data.wt a' + MinData.toWeight (highRoot .E7) := by
      rw [ha']
      exact (sub_add_cancel _ _).symm
    have hshift : e7Shift (highRoot .E7) a' = a := wt_e7Shift hwt.symm.symm
    have hρ : e7Rep56 (ZMod 2) (pinnedElt .E7 (highRoot .E7) 1) (Finsupp.single a' 1) -
        Finsupp.single a' 1 = Finsupp.single a 1 := by
      rw [e7Rep56_pinnedElt_single hθ, if_pos hdot, hshift, add_sub_cancel_left]
    refine ⟨e7Rep56 (ZMod 2) g (Finsupp.single a 1), rep_mem_weightVec (single_mem_weightVec a) g,
      ⟨e7Rep56 (ZMod 2) g (Finsupp.single a' 1), ?_⟩, ?_, ?_⟩
    · rw [rep_conj_sub, rep_inv_apply', hρ]
    · rw [← rep_mul_apply]
      have e : g * pinnedElt .E7 (e8fRoot k) (1 : ZMod 2) * g⁻¹ * g =
          g * pinnedElt .E7 (e8fRoot k) 1 := by group
      rw [e, rep_mul_apply, e7Rep56_pinnedElt_single hβ a, if_neg (by rw [ha0]; decide),
        add_zero]
    · rintro ⟨c, hc⟩
      rw [rep_conj_sub] at hc
      have hc2 := congrArg (e7Rep56 (ZMod 2) g⁻¹) hc
      rw [rep_inv_apply', rep_inv_apply'] at hc2
      have hne : (e7Rep56 (ZMod 2) (pinnedElt .E7 (e8fRoot k) (1 : ZMod 2))
          (e7Rep56 (ZMod 2) g⁻¹ c) - e7Rep56 (ZMod 2) g⁻¹ c) a ≠ 0 := by
        rw [hc2]
        simp
      have h1 := coord_rho_sub_ne_zero hβ _ hne
      rw [ha0] at h1
      exact absurd h1 (by decide)
  · exfalso
    apply hncomm
    exact conj_comm g (pinnedElt_commute hθ hβ (fun h0 => hneg (eq_neg_of_add_eq_zero_right h0))
      hroot)

end CFSG.GF2Type.SmithTypeE.E8.F
