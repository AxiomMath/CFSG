module

public import CFSG.GF2Type.SmithTypeE.E8.SfFix

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

public noncomputable section

namespace CFSG.GF2Type.SmithTypeE.E8

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.Minuscule CFSG.HardMathSupport.Cooperstein.Coordinator.Survivors
  CFSG.Quasithin.SmithCurtis CFSG.Quasithin.SmithCurtis.Chev CFSG.SeitzReduction
  CFSG.SeitzReduction.EPilot


theorem exists_bruhat_decomp (g : ↥(adjointGroup .E7 (ZMod 2))) :
    ∃ (u u' : ↥(adjointGroup .E7 (ZMod 2))) (w : WeylGroup .E7),
      (u : ModGL .E7 (ZMod 2)) ∈ posUnipotent .E7 (ZMod 2) ∧
      (u' : ModGL .E7 (ZMod 2)) ∈ posUnipotent .E7 (ZMod 2) ∧
      g = u * nWC .E7 (ZMod 2) w * u' := by
  have hg : (g : ModGL .E7 (ZMod 2)) ∈ (adjointGroup .E7 (ZMod 2) : Set (ModGL .E7 (ZMod 2))) :=
    g.2
  rw [CFSG.LieType.Chevalley.adjointGroup_eq_iUnion_bruhatCell] at hg
  obtain ⟨w, hw⟩ := Set.mem_iUnion.1 hg
  obtain ⟨b, hb, b', hb', hbb⟩ := CFSG.LieType.Chevalley.mem_bruhatCell.1 hw
  rw [borel_eq_posUnipotent] at hb hb'
  exact ⟨⟨b, posUnipotent_le_adjointGroup_E7 hb⟩, ⟨b', posUnipotent_le_adjointGroup_E7 hb'⟩, w,
    hb, hb', Subtype.ext hbb.symm⟩

private theorem e7Rep56_mul_apply (g h : ↥(adjointGroup .E7 (ZMod 2)))
    (v : Fin e7Data.d →₀ ZMod 2) :
    e7Rep56 (ZMod 2) (g * h) v = e7Rep56 (ZMod 2) g (e7Rep56 (ZMod 2) h v) := by
  rw [map_mul, Module.End.mul_apply]

private theorem exists_e7Rep56_nWC_e7Y56 (w : WeylGroup .E7) :
    ∃ b : Fin e7Data.d, e7Rep56 (ZMod 2) (nWC .E7 (ZMod 2) w) e7Y56 = Finsupp.single b 1 :=
  e7Rep56_nWC_single (K := ZMod 2) w ⟨0, by decide⟩

theorem pair_normal_form_weights {w w' : Fin e7Data.d →₀ ZMod 2}
    (hw : ∃ g₁ : ↥(adjointGroup .E7 (ZMod 2)), w = e7Rep56 (ZMod 2) g₁ e7Y56)
    (hw' : ∃ g₂ : ↥(adjointGroup .E7 (ZMod 2)), w' = e7Rep56 (ZMod 2) g₂ e7Y56) :
    ∃ (g : ↥(adjointGroup .E7 (ZMod 2))) (b : Fin e7Data.d),
      w = e7Rep56 (ZMod 2) g e7Y56 ∧ w' = e7Rep56 (ZMod 2) g (Finsupp.single b 1) := by
  obtain ⟨g₁, rfl⟩ := hw
  obtain ⟨g₂, rfl⟩ := hw'
  obtain ⟨u, u', v, hu, hu', huv⟩ := exists_bruhat_decomp (g₁⁻¹ * g₂)
  obtain ⟨b, hb⟩ := exists_e7Rep56_nWC_e7Y56 v
  have h2 : g₂ = g₁ * u * (nWC .E7 (ZMod 2) v * u') := by
    calc g₂ = g₁ * (g₁⁻¹ * g₂) := (mul_inv_cancel_left g₁ g₂).symm
      _ = g₁ * (u * nWC .E7 (ZMod 2) v * u') := by rw [huv]
      _ = g₁ * u * (nWC .E7 (ZMod 2) v * u') := by group
  refine ⟨g₁ * u, b, ?_, ?_⟩
  · rw [e7Rep56_mul_apply, e7Rep56_posUnipotent_e7Y56 u hu]
  · rw [h2, e7Rep56_mul_apply (g₁ * u), e7Rep56_mul_apply (nWC .E7 (ZMod 2) v) u',
      e7Rep56_posUnipotent_e7Y56 u' hu', hb]

theorem exists_posUnipotent_basis {w : Fin e7Data.d →₀ ZMod 2}
    (hw : ∃ g₁ : ↥(adjointGroup .E7 (ZMod 2)), w = e7Rep56 (ZMod 2) g₁ e7Y56) :
    ∃ u : ↥(adjointGroup .E7 (ZMod 2)),
      (u : ModGL .E7 (ZMod 2)) ∈ posUnipotent .E7 (ZMod 2) ∧
        ∃ a : Fin e7Data.d, w = e7Rep56 (ZMod 2) u (Finsupp.single a 1) := by
  obtain ⟨g₁, rfl⟩ := hw
  obtain ⟨u, u', v, hu, hu', huv⟩ := exists_bruhat_decomp g₁
  obtain ⟨b, hb⟩ := exists_e7Rep56_nWC_e7Y56 v
  refine ⟨u, hu, b, ?_⟩
  rw [huv, e7Rep56_mul_apply, e7Rep56_mul_apply, e7Rep56_posUnipotent_e7Y56 u' hu', hb]

private theorem commute_pinnedX_highRoot_E7 {β : Fin (Tag.rank .E7) → ℤ} (hβ : IsRoot .E7 β)
    (hβp : 0 < height β) (a b : ZMod 2) :
    Commute (pinnedX .E7 (ZMod 2) β a) (pinnedX .E7 (ZMod 2) (highRoot .E7) b) := by
  by_cases hβθ : β = highRoot .E7
  · subst hβθ
    rw [Commute, SemiconjBy, ← pinnedX_add, ← pinnedX_add, add_comm]
  · have hc := commutator_rootSubgroup_le (ZMod 2) hβ (isRoot_highRoot .E7) hβp
      (height_highRoot_pos .E7) hβθ
    have hbot : (⨆ (γ : Fin (Tag.rank .E7) → ℤ) (_ : IsRoot .E7 γ ∧
        ∃ a b : ℕ, 1 ≤ a ∧ 1 ≤ b ∧ γ = a • β + b • highRoot .E7),
          rootSubgroup .E7 (ZMod 2) γ) = ⊥ := by
      refine iSup₂_eq_bot.2 ?_
      rintro γ ⟨hγ, a, b, ha, hb, rfl⟩
      exact absurd hγ (not_isRoot_nsmul_add_nsmul_highRoot hβp ha hb)
    rw [hbot] at hc
    have hmem := hc (Subgroup.commutator_mem_commutator
      (CFSG.Blueprint.Chevalley.mem_rootSubgroup.2 ⟨a, rfl⟩)
      (CFSG.Blueprint.Chevalley.mem_rootSubgroup.2 ⟨b, rfl⟩))
    rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hmem
    exact hmem

private theorem commute_posUnipotent_pinnedX_highRoot {g : ModGL .E7 (ZMod 2)}
    (hg : g ∈ posUnipotent .E7 (ZMod 2)) (b : ZMod 2) :
    Commute g (pinnedX .E7 (ZMod 2) (highRoot .E7) b) := by
  have hle : posUnipotent .E7 (ZMod 2) ≤
      Subgroup.centralizer {pinnedX .E7 (ZMod 2) (highRoot .E7) b} := by
    refine iSup₂_le fun β hβ => (Subgroup.closure_le _).2 ?_
    rintro _ ⟨a, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
    exact (commute_pinnedX_highRoot_E7 hβ.1 hβ.2 a b).eq
  exact Subgroup.mem_centralizer_singleton_iff.1 (hle hg)

theorem commute_posUnipotent_xtheta (u : ↥(adjointGroup .E7 (ZMod 2)))
    (hu : (u : ModGL .E7 (ZMod 2)) ∈ posUnipotent .E7 (ZMod 2)) :
    u * pinnedElt .E7 (highRoot .E7) (1 : ZMod 2) =
      pinnedElt .E7 (highRoot .E7) (1 : ZMod 2) * u :=
  Subtype.ext (commute_posUnipotent_pinnedX_highRoot hu 1).eq

theorem nWC_mul_xtheta_mul_inv (w : WeylGroup .E7) :
    nWC .E7 (ZMod 2) w * pinnedElt .E7 (highRoot .E7) (1 : ZMod 2) * (nWC .E7 (ZMod 2) w)⁻¹ =
      pinnedElt .E7 (w • highRoot .E7) (1 : ZMod 2) := by
  obtain ⟨ε, hε, h⟩ :=
    exists_canonicalRep_mul_pinnedX_mul_inv (ZMod 2) w (isRoot_highRoot .E7)
  have hε1 : ε = 1 := by
    have key : ∀ e : ZMod 2, e * e = 1 → e = 1 := by decide
    exact key ε hε
  refine Subtype.ext ?_
  have h1 := h 1
  rw [hε1, one_mul] at h1
  exact h1

private theorem conj_eq_conj_of_commute {G : Type*} [Group G] {g u x : G} (hc : u * x = x * u) :
    g * x * g⁻¹ = g * u * x * (g * u)⁻¹ := by
  have h : u * x * u⁻¹ = x := by rw [hc, mul_inv_cancel_right]
  calc g * x * g⁻¹ = g * (u * x * u⁻¹) * g⁻¹ := by rw [h]
    _ = g * u * x * (g * u)⁻¹ := by group

private theorem conj_eq_conj_of_bruhat {G : Type*} [Group G] {g₁ g₂ u n u' x y : G}
    (h : g₁⁻¹ * g₂ = u * n * u') (hc : u' * x = x * u') (hn : n * x * n⁻¹ = y) :
    g₂ * x * g₂⁻¹ = g₁ * u * y * (g₁ * u)⁻¹ := by
  have hg₂ : g₂ = g₁ * (u * n * u') := by rw [← h, mul_inv_cancel_left]
  have h' : u' * x * u'⁻¹ = x := by rw [hc, mul_inv_cancel_right]
  rw [hg₂, ← hn]
  calc g₁ * (u * n * u') * x * (g₁ * (u * n * u'))⁻¹ =
      g₁ * u * (n * (u' * x * u'⁻¹) * n⁻¹) * (g₁ * u)⁻¹ := by group
    _ = g₁ * u * (n * x * n⁻¹) * (g₁ * u)⁻¹ := by rw [h']

theorem pair_normal_form_involutions {r r' : ↥(adjointGroup .E7 (ZMod 2))}
    (hr : IsConj (pinnedElt .E7 (highRoot .E7) (1 : ZMod 2)) r)
    (hr' : IsConj (pinnedElt .E7 (highRoot .E7) (1 : ZMod 2)) r') :
    ∃ (g : ↥(adjointGroup .E7 (ZMod 2))) (β : Fin (Tag.rank .E7) → ℤ), IsRoot .E7 β ∧
      r = g * pinnedElt .E7 (highRoot .E7) (1 : ZMod 2) * g⁻¹ ∧
      r' = g * pinnedElt .E7 β (1 : ZMod 2) * g⁻¹ := by
  obtain ⟨g₁, hg₁⟩ := isConj_iff.1 hr
  obtain ⟨g₂, hg₂⟩ := isConj_iff.1 hr'
  obtain ⟨u, u', v, hu, hu', huv⟩ := exists_bruhat_decomp (g₁⁻¹ * g₂)
  refine ⟨g₁ * u, v • highRoot .E7, IsRoot.smul (isRoot_highRoot .E7) v, ?_, ?_⟩
  · rw [← hg₁]
    exact conj_eq_conj_of_commute (commute_posUnipotent_xtheta u hu)
  · rw [← hg₂]
    exact conj_eq_conj_of_bruhat huv (commute_posUnipotent_xtheta u' hu')
      (nWC_mul_xtheta_mul_inv v)

theorem pair_normal_form_weight_involution {w : Fin e7Data.d →₀ ZMod 2}
    {r : ↥(adjointGroup .E7 (ZMod 2))}
    (hw : ∃ g₁ : ↥(adjointGroup .E7 (ZMod 2)), w = e7Rep56 (ZMod 2) g₁ e7Y56)
    (hr : IsConj (pinnedElt .E7 (highRoot .E7) (1 : ZMod 2)) r) :
    ∃ (g : ↥(adjointGroup .E7 (ZMod 2))) (β : Fin (Tag.rank .E7) → ℤ), IsRoot .E7 β ∧
      w = e7Rep56 (ZMod 2) g e7Y56 ∧ r = g * pinnedElt .E7 β (1 : ZMod 2) * g⁻¹ := by
  obtain ⟨g₁, rfl⟩ := hw
  obtain ⟨g₂, hg₂⟩ := isConj_iff.1 hr
  obtain ⟨u, u', v, hu, hu', huv⟩ := exists_bruhat_decomp (g₁⁻¹ * g₂)
  refine ⟨g₁ * u, v • highRoot .E7, IsRoot.smul (isRoot_highRoot .E7) v, ?_, ?_⟩
  · rw [e7Rep56_mul_apply, e7Rep56_posUnipotent_e7Y56 u hu]
  · rw [← hg₂]
    exact conj_eq_conj_of_bruhat huv (commute_posUnipotent_xtheta u' hu')
      (nWC_mul_xtheta_mul_inv v)

end CFSG.GF2Type.SmithTypeE.E8
