module

public import CFSG.GF2Type.SmithTypeE.E8.FactsCoord

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

public section

namespace CFSG.GF2Type.SmithTypeE.E8.F

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.Minuscule CFSG.HardMathSupport.Cooperstein.Coordinator.Survivors
  CFSG.Quasithin.SmithCurtis CFSG.Quasithin.SmithCurtis.Chev CFSG.SeitzReduction
  CFSG.SeitzReduction.EPilot


theorem conj_comm {G : Type*} [Group G] {a b : G} (g : G) (h : a * b = b * a) :
    (g * a * g⁻¹) * (g * b * g⁻¹) = (g * b * g⁻¹) * (g * a * g⁻¹) := by
  calc (g * a * g⁻¹) * (g * b * g⁻¹) = g * (a * b) * g⁻¹ := by group
    _ = g * (b * a) * g⁻¹ := by rw [h]
    _ = (g * b * g⁻¹) * (g * a * g⁻¹) := by group

theorem conj_braid {G : Type*} [Group G] {a b : G} (g : G) (h : a * b * a = b * a * b) :
    (g * a * g⁻¹) * (g * b * g⁻¹) * (g * a * g⁻¹) =
      (g * b * g⁻¹) * (g * a * g⁻¹) * (g * b * g⁻¹) := by
  calc (g * a * g⁻¹) * (g * b * g⁻¹) * (g * a * g⁻¹) = g * (a * b * a) * g⁻¹ := by group
    _ = g * (b * a * b) * g⁻¹ := by rw [h]
    _ = (g * b * g⁻¹) * (g * a * g⁻¹) * (g * b * g⁻¹) := by group

theorem conj_dihedral {G : Type*} [Group G] {a b : G} (g : G) (h : a * b * a * b = b * a * b * a) :
    (g * a * g⁻¹) * (g * b * g⁻¹) * (g * a * g⁻¹) * (g * b * g⁻¹) =
      (g * b * g⁻¹) * (g * a * g⁻¹) * (g * b * g⁻¹) * (g * a * g⁻¹) := by
  calc (g * a * g⁻¹) * (g * b * g⁻¹) * (g * a * g⁻¹) * (g * b * g⁻¹) =
        g * (a * b * a * b) * g⁻¹ := by group
    _ = g * (b * a * b * a) * g⁻¹ := by rw [h]
    _ = (g * b * g⁻¹) * (g * a * g⁻¹) * (g * b * g⁻¹) * (g * a * g⁻¹) := by group

theorem xtheta_pinned_rel {β : Fin (Tag.rank .E7) → ℤ} (hβ : IsRoot .E7 β) :
    (pinnedElt .E7 (highRoot .E7) (1 : ZMod 2)) * (pinnedElt .E7 β (1 : ZMod 2)) =
        (pinnedElt .E7 β (1 : ZMod 2)) * (pinnedElt .E7 (highRoot .E7) (1 : ZMod 2)) ∨
      (pinnedElt .E7 (highRoot .E7) (1 : ZMod 2)) * (pinnedElt .E7 β (1 : ZMod 2)) *
          (pinnedElt .E7 (highRoot .E7) (1 : ZMod 2)) =
        (pinnedElt .E7 β (1 : ZMod 2)) * (pinnedElt .E7 (highRoot .E7) (1 : ZMod 2)) *
          (pinnedElt .E7 β (1 : ZMod 2)) ∨
      (pinnedElt .E7 (highRoot .E7) (1 : ZMod 2)) * (pinnedElt .E7 β (1 : ZMod 2)) *
          (pinnedElt .E7 (highRoot .E7) (1 : ZMod 2)) * (pinnedElt .E7 β (1 : ZMod 2)) =
        (pinnedElt .E7 β (1 : ZMod 2)) * (pinnedElt .E7 (highRoot .E7) (1 : ZMod 2)) *
          (pinnedElt .E7 β (1 : ZMod 2)) * (pinnedElt .E7 (highRoot .E7) (1 : ZMod 2)) := by
  have hθ := isRoot_highRoot .E7
  by_cases hneg : β = -highRoot .E7
  · right; left
    subst hneg
    exact pinnedElt_braid hθ
  by_cases hroot : IsRoot .E7 (highRoot .E7 + β)
  · right; right
    refine pinnedElt_dihedral hθ hβ ?_ hroot
    exact isRoot_ne_zero hroot
  · left
    refine pinnedElt_commute hθ hβ ?_ hroot
    intro h0
    apply hneg
    exact eq_neg_of_add_eq_zero_right h0

theorem pair_rel_sym_core {r r' : ↥(adjointGroup .E7 (ZMod 2))} (hr : IsRootInvol r)
    (hr' : IsRootInvol r') (hne : r ≠ r') :
    r * r' = r' * r ∨ r * r' * r = r' * r * r' ∨ r * r' * r * r' = r' * r * r' * r := by
  obtain ⟨g, β, hβ, rfl, rfl⟩ := pair_normal_form_involutions hr hr'
  rcases xtheta_pinned_rel hβ with h | h | h
  · exact Or.inl (conj_comm g h)
  · exact Or.inr (Or.inl (conj_braid g h))
  · exact Or.inr (Or.inr (conj_dihedral g h))

theorem int_core {β : Fin (Tag.rank .E7) → ℤ} (hβ : IsRoot .E7 β) (hne : β ≠ highRoot .E7)
    (c c' : Fin e7Data.d →₀ ZMod 2)
    (h : e7Rep56 (ZMod 2) (pinnedElt .E7 (highRoot .E7) (1 : ZMod 2)) c - c =
      e7Rep56 (ZMod 2) (pinnedElt .E7 β (1 : ZMod 2)) c' - c') :
    e7Rep56 (ZMod 2) (pinnedElt .E7 (highRoot .E7) (1 : ZMod 2)) c - c = 0 ∨
      (pinnedElt .E7 (highRoot .E7) (1 : ZMod 2) * pinnedElt .E7 β (1 : ZMod 2) =
          pinnedElt .E7 β (1 : ZMod 2) * pinnedElt .E7 (highRoot .E7) (1 : ZMod 2) ∧
        e7Rep56 (ZMod 2) (pinnedElt .E7 (highRoot .E7) (1 : ZMod 2)) c - c ∈ weightVec) := by
  obtain ⟨u, hu⟩ : ∃ u : Fin e7Data.d →₀ ZMod 2,
      u = e7Rep56 (ZMod 2) (pinnedElt .E7 (highRoot .E7) (1 : ZMod 2)) c - c := ⟨_, rfl⟩
  rw [← hu] at h ⊢
  by_cases hu0 : u = 0
  · exact Or.inl hu0
  right
  have hθ := isRoot_highRoot .E7
  obtain ⟨k, hk, hkβ⟩ := exists_e8fRoot_eq hβ
  subst hkβ
  have hk' : k ∈ List.range 126 := List.mem_range.2 hk
  have hsupp : ∀ b, u b ≠ 0 → (e7Data.wt b ⬝ᵥ highRoot .E7 = 1 ∧
      e7Data.wt b ⬝ᵥ e8fRoot k = 1) := by
    intro b hb
    refine ⟨?_, ?_⟩
    · exact coord_rho_sub_ne_zero hθ c (hu ▸ hb)
    · have h' : (e7Rep56 (ZMod 2) (pinnedElt .E7 (e8fRoot k) (1 : ZMod 2)) c' - c') b ≠ 0 := by
        rw [← h]; exact hb
      exact coord_rho_sub_ne_zero hβ c' h'
  have hTne : u.support.Nonempty := Finsupp.support_nonempty_iff.mpr hu0
  have hmem : ∀ b ∈ u.support, b ∈ e8fLam k := fun b hb =>
    mem_e8fLam.2 (hsupp b (Finsupp.mem_support_iff.1 hb))
  have hLam : e8fLam k ≠ [] := by
    obtain ⟨b, hb⟩ := hTne
    exact List.ne_nil_of_mem (hmem b hb)
  obtain ⟨hneg, hnroot⟩ := comm_case_listed k hk' hne hLam
  refine ⟨?_, ?_⟩
  · refine pinnedElt_commute hθ hβ ?_ (not_isRoot_of_listed hnroot)
    intro h0
    exact hneg (eq_neg_of_add_eq_zero_right h0)
  · have hsum : (∑ b ∈ u.support, (Finsupp.single b 1 : Fin e7Data.d →₀ ZMod 2)) ∈ weightVec := by
      refine sum_single_mem_weightVec u.support hTne ?_
      intro μ hμ l hl hμl
      obtain ⟨j, hj, hjeq⟩ := clique_exists_listed k hk' hne μ (hmem μ hμ) l (hmem l hl) hμl
      refine ⟨e8fRoot j, e8fRoot_isRoot (List.mem_range.1 hj), hjeq,
        clique_moves_listed k hk' hne μ (hmem μ hμ) l (hmem l hl) hμl j hj hjeq, ?_⟩
      intro ν hν hνμ hνl
      exact clique_fix_listed k hk' hne μ (hmem μ hμ) l (hmem l hl) hμl j hj hjeq ν
        (hmem ν hν) hνμ hνl
    rwa [← finsupp_eq_sum_single] at hsum

theorem int_rel_sym_core {r r' : ↥(adjointGroup .E7 (ZMod 2))} (hr : IsRootInvol r)
    (hr' : IsRootInvol r') (hne : r ≠ r') (c c' : Fin e7Data.d →₀ ZMod 2)
    (h : e7Rep56 (ZMod 2) r c - c = e7Rep56 (ZMod 2) r' c' - c') :
    e7Rep56 (ZMod 2) r c - c = 0 ∨
      (r * r' = r' * r ∧ e7Rep56 (ZMod 2) r c - c ∈ weightVec) := by
  obtain ⟨g, β, hβ, rfl, rfl⟩ := pair_normal_form_involutions hr hr'
  have hβθ : β ≠ highRoot .E7 := by
    rintro rfl
    exact hne rfl
  rw [rep_conj_sub, rep_conj_sub] at h
  have hAB := congrArg (e7Rep56 (ZMod 2) g⁻¹) h
  rw [rep_inv_apply', rep_inv_apply'] at hAB
  rcases int_core hβ hβθ (e7Rep56 (ZMod 2) g⁻¹ c) (e7Rep56 (ZMod 2) g⁻¹ c') hAB with
    h0 | ⟨hcomm, hw⟩
  · left
    rw [rep_conj_sub, h0, map_zero]
  · right
    refine ⟨conj_comm g hcomm, ?_⟩
    rw [rep_conj_sub]
    exact rep_mem_weightVec hw g

end CFSG.GF2Type.SmithTypeE.E8.F
