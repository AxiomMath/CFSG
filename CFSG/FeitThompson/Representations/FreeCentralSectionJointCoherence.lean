module

public import CFSG.FeitThompson.Representations.NormBoundLinearFamilyOrientation
public import CFSG.FeitThompson.Representations.FreeCentralSectionCoherentLayer
public import CFSG.FeitThompson.Representations.QuotientFrobeniusNoncoherentChiefReduction
public import CFSG.FeitThompson.Representations.DisjointSupportCoherentFamiliesOrthogonal

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

namespace FreeCentralSectionJointCoherence

open Subgroup NormalLinearInduced
open FrobeniusQuotientLayer (FixesOnlyCommutatorCoset)
open QuotientFrobeniusNoncoherent (mem_commutator_of_fixesOnlyCommutatorCoset)
open SibleyCentralAlignment (exists_isCoherentWith_apply_eq_of_bridge)

section Transport

variable {L G : Type*} [Group L] [Fintype L] [Group G] [Fintype G]

theorem isCoherent_of_eq_of_coe_eq {S S' : Set (L → ℂ)} {tau : (L → ℂ) → (G → ℂ)} (hSS' : S = S')
    {τ : charSpanZero S →+ virtualChars G} {τ' : charSpanZero S' →+ virtualChars G}
    (hval : ∀ f, (τ f : G → ℂ) = tau (f : L → ℂ))
    (hval' : ∀ f, (τ' f : G → ℂ) = tau (f : L → ℂ))
    (hcoh : IsCoherent S τ) : IsCoherent S' τ' := by
  subst hSS'
  obtain ⟨ν, hν⟩ := isCoherent_iff.1 hcoh
  refine isCoherent_iff.2 ⟨ν, hν.inner_eq, fun f => Subtype.ext ?_⟩
  rw [hν.eq_on_zero f, hval f, hval' f]

end Transport

section Group

variable {G : Type*} [Group G] {p a : ℕ} {L P E Z : Subgroup G}

theorem inf_centralizer_le_commutator (h : IsFreeCentralSection p a L P E Z)
    [(P.subgroupOf L).Normal]
    (hfix : FixesOnlyCommutatorCoset (P.subgroupOf L) (E.subgroupOf L)) :
    ∀ u ∈ E, u ≠ 1 → P ⊓ centralizer ({u} : Set G) ≤ (⁅P, P⁆ : Subgroup G) := by
  intro u hu hu1 k hk
  obtain ⟨hkP, hkc⟩ := Subgroup.mem_inf.1 hk
  have hkL : k ∈ L := h.P_le hkP
  have huL : u ∈ L := h.E_le hu
  have hcommL : (⟨k, hkL⟩ : ↥L) * ⟨u, huL⟩ = (⟨u, huL⟩ : ↥L) * ⟨k, hkL⟩ :=
    Subtype.ext (Subgroup.mem_centralizer_singleton_iff.1 hkc)
  have hconj : (⟨u, huL⟩ : ↥L)⁻¹ * (⟨k, hkL⟩ : ↥L) * ⟨u, huL⟩ = ⟨k, hkL⟩ := by
    rw [mul_assoc, hcommL, inv_mul_cancel_left]
  have hfixed : (⟨k, hkL⟩ : ↥L)⁻¹ * ((⟨u, huL⟩ : ↥L)⁻¹ * ⟨k, hkL⟩ * ⟨u, huL⟩)
      ∈ ⁅P.subgroupOf L, P.subgroupOf L⁆ := by
    rw [hconj, inv_mul_cancel]
    exact one_mem _
  have hmem := mem_commutator_of_fixesOnlyCommutatorCoset hfix
    (Subgroup.mem_subgroupOf.2 hu) (fun hc => hu1 (congrArg Subtype.val hc))
    (Subgroup.mem_subgroupOf.2 hkP) hfixed
  rw [commutator_subgroupOf_eq h.P_le] at hmem
  exact Subgroup.mem_subgroupOf.1 hmem

end Group

section MinDegree

variable {G : Type*} [Group G] [Finite G] {p a : ℕ} {L P E Z : Subgroup G} [Fintype ↥L]
  [(P.subgroupOf L).Normal] [(Z.subgroupOf L).Normal]

theorem exists_min_degree_ratio (h : IsFreeCentralSection p a L P E Z) :
    ∃ ξ₀ ∈ indFamDetect (P.subgroupOf L) ((Z.subgroupOf L).subgroupOf (P.subgroupOf L)),
      ∀ χ : indFamDetect (P.subgroupOf L) ((Z.subgroupOf L).subgroupOf (P.subgroupOf L)),
        ∃ b : ℤ, 0 < b ∧ (χ : ↥L → ℂ) 1 = (b : ℂ) * ξ₀ 1 := by
  classical
  obtain ⟨f₀, hf₀⟩ := h.indFamDetect_nonempty_subgroupOf
  have hXFne : (indFamDetectFinset (P.subgroupOf L)
      ((Z.subgroupOf L).subgroupOf (P.subgroupOf L))).Nonempty :=
    ⟨f₀, mem_indFamDetectFinset.2 hf₀⟩
  have hform : ∀ χ ∈ indFamDetectFinset (P.subgroupOf L)
      ((Z.subgroupOf L).subgroupOf (P.subgroupOf L)),
      ∃ b : ℕ, χ 1 = ((Nat.card ↥E * p ^ b : ℕ) : ℂ) := by
    intro χ hχ
    obtain ⟨b, hb, -⟩ := h.exists_degree_eq_mul_pow_and_sq_dvd (mem_indFamDetectFinset.1 hχ)
    exact ⟨b, hb⟩
  choose! bb hbb using hform
  obtain ⟨ξ₀, hξ₀F, hmin⟩ := (indFamDetectFinset (P.subgroupOf L)
    ((Z.subgroupOf L).subgroupOf (P.subgroupOf L))).exists_min_image bb hXFne
  refine ⟨ξ₀, mem_indFamDetectFinset.1 hξ₀F, fun χ => ?_⟩
  have hχF : (χ : ↥L → ℂ) ∈ indFamDetectFinset (P.subgroupOf L)
      ((Z.subgroupOf L).subgroupOf (P.subgroupOf L)) := mem_indFamDetectFinset.2 χ.2
  have hple : (0 : ℤ) < (p : ℤ) := by exact_mod_cast h.prime.pos
  refine ⟨(p : ℤ) ^ (bb (χ : ↥L → ℂ) - bb ξ₀), pow_pos hple _, ?_⟩
  have hle : bb ξ₀ ≤ bb (χ : ↥L → ℂ) := hmin _ hχF
  have hsplit : (p : ℂ) ^ (bb (χ : ↥L → ℂ))
      = (p : ℂ) ^ (bb (χ : ↥L → ℂ) - bb ξ₀) * (p : ℂ) ^ (bb ξ₀) := by
    rw [← pow_add]
    congr 1
    omega
  rw [hbb _ hχF, hbb _ hξ₀F]
  push_cast
  rw [hsplit]
  ring

end MinDegree

namespace IsFreeCentralSection

variable {G : Type*} [Group G] [Fintype G] {p a : ℕ} {L P E Z : Subgroup G} [Fintype ↥L]
  [(P.subgroupOf L).Normal] [(Z.subgroupOf L).Normal]

theorem isCoherent_indFamDetect_union_indFamLinear
    (h : IsFreeCentralSection p a L P E Z)
    (_hPnonabelian : ¬ IsMulCommutative ↥P) (_hEcyclic : IsCyclic ↥E)
    (hZP' : Z ≤ (⁅P, P⁆ : Subgroup G))
    (hfix : FixesOnlyCommutatorCoset (P.subgroupOf L) (E.subgroupOf L))
    {S : Finset (↥L → ℂ)} (hS : S = indFamNonprincipalFinset (P.subgroupOf L))
    {R : (↥L → ℂ) → Finset (G → ℂ)} (hc : IsSubcoherent S (indClassFun L) R)
    (τ : charSpanZero (indFamDetect (P.subgroupOf L)
        ((Z.subgroupOf L).subgroupOf (P.subgroupOf L)) ∪ indFamLinear (P.subgroupOf L)) →+
      virtualChars G)
    (hτ : ∀ f, (τ f : G → ℂ) = indClassFun L (f : ↥L → ℂ)) :
    IsCoherent (indFamDetect (P.subgroupOf L) ((Z.subgroupOf L).subgroupOf (P.subgroupOf L))
      ∪ indFamLinear (P.subgroupOf L)) τ := by
  classical
  have hCP := inf_centralizer_le_commutator h hfix
  have hXIrr : indFamDetect (P.subgroupOf L) ((Z.subgroupOf L).subgroupOf (P.subgroupOf L))
      ⊆ Irr ↥L := h.indFamDetect_subset_Irr
  have hYIrr : indFamLinear (P.subgroupOf L) ⊆ Irr ↥L := h.indFamLinear_subset_Irr hCP
  have hXne := h.indFamDetect_nonempty_subgroupOf
  have hYne := h.indFamLinear_nonempty'
  have hXstar : ∀ χ ∈ indFamDetect (P.subgroupOf L)
      ((Z.subgroupOf L).subgroupOf (P.subgroupOf L)), star χ ∈ indFamDetect (P.subgroupOf L)
      ((Z.subgroupOf L).subgroupOf (P.subgroupOf L)) := fun _ hχ => h.conj_mem_indFamDetect hχ
  have hYstar : ∀ χ ∈ indFamLinear (P.subgroupOf L), star χ ∈ indFamLinear (P.subgroupOf L) :=
    fun _ hχ => NormalLinearInduced.conj_mem_indFamLinear _ hχ
  have hXnr : ∀ χ ∈ indFamDetect (P.subgroupOf L)
      ((Z.subgroupOf L).subgroupOf (P.subgroupOf L)), star χ ≠ χ := fun _ hχ hcon =>
    h.not_conj_eq_self_of_mem_indFamDetect hχ hcon.symm
  have hYnr : ∀ χ ∈ indFamLinear (P.subgroupOf L), star χ ≠ χ := fun _ hχ hcon =>
    h.not_conj_eq_self_of_mem_indFamLinear' hCP hχ hcon.symm
  have hXY : Disjoint (indFamDetect (P.subgroupOf L)
      ((Z.subgroupOf L).subgroupOf (P.subgroupOf L))) (indFamLinear (P.subgroupOf L)) :=
    Set.disjoint_iff_inter_eq_empty.2 (h.inter_indFamDetect_indFamLinear_eq_empty' hZP')
  have hUind : indFamDetect (P.subgroupOf L) ((Z.subgroupOf L).subgroupOf (P.subgroupOf L))
      ∪ indFamLinear (P.subgroupOf L) ⊆ indFam (P.subgroupOf L) (Irr ↥(P.subgroupOf L)) := by
    refine Set.union_subset ?_ (indFamLinear_subset_indFam_Irr _)
    have hh := indFamDetect_subset_indFam_irrChar (P.subgroupOf L)
      ((Z.subgroupOf L).subgroupOf (P.subgroupOf L))
    rwa [irrChar_eq_Irr] at hh
  have hUirr : indFamDetect (P.subgroupOf L) ((Z.subgroupOf L).subgroupOf (P.subgroupOf L))
      ∪ indFamLinear (P.subgroupOf L) ⊆ Irr ↥L := Set.union_subset hXIrr hYIrr
  have hz : ∀ f : charSpanZero (indFamDetect (P.subgroupOf L)
      ((Z.subgroupOf L).subgroupOf (P.subgroupOf L)) ∪ indFamLinear (P.subgroupOf L)),
      (f : ↥L → ℂ) ∈ dadeZDomain L ((P : Set G) \ {1}) :=
    fun f => mem_dadeZDomain_of_mem_charSpanZero hUind hUirr f
  have hτ1 : ∀ f : charSpanZero (indFamDetect (P.subgroupOf L)
      ((Z.subgroupOf L).subgroupOf (P.subgroupOf L)) ∪ indFamLinear (P.subgroupOf L)),
      (τ f : G → ℂ) 1 = 0 := by
    intro f
    rw [hτ]
    exact h.isTI.indClassFun_apply_one (fun x hx => (mem_dadeZDomain.1 (hz f)).2 x hx)
  have hτiso : ∀ f g : charSpanZero (indFamDetect (P.subgroupOf L)
      ((Z.subgroupOf L).subgroupOf (P.subgroupOf L)) ∪ indFamLinear (P.subgroupOf L)),
      cfInner (τ f : G → ℂ) (τ g : G → ℂ) = cfInner (f : ↥L → ℂ) (g : ↥L → ℂ) := by
    intro f g
    rw [hτ, hτ]
    exact h.isTI.cfInner_indClassFun (mem_dadeDomain_of_mem_dadeZDomain (hz f))
      (mem_dadeDomain_of_mem_dadeZDomain (hz g))
  have hτstar₂ : ∀ f g : charSpanZero (indFamDetect (P.subgroupOf L)
      ((Z.subgroupOf L).subgroupOf (P.subgroupOf L)) ∪ indFamLinear (P.subgroupOf L)),
      (g : ↥L → ℂ) = star (f : ↥L → ℂ) → (τ g : G → ℂ) = star ((τ f : G → ℂ)) := by
    intro f g hfg
    rw [hτ, hτ, hfg]
    exact DisjointCoherentFamilies.indClassFun_star L (f : ↥L → ℂ)
  have hτstar : ∀ f : charSpanZero (indFamDetect (P.subgroupOf L)
      ((Z.subgroupOf L).subgroupOf (P.subgroupOf L)) ∪ indFamLinear (P.subgroupOf L)),
      (τ (starCharSpanZero (star_mem_union hXstar hYstar) f) : G → ℂ) = star ((τ f : G → ℂ)) :=
    fun f => hτstar₂ f _ (coe_starCharSpanZero _ f)
  have hsub : (indFamDetectFinset (P.subgroupOf L)
      ((Z.subgroupOf L).subgroupOf (P.subgroupOf L)) : Set (↥L → ℂ))
        ⊆ indFamDetect (P.subgroupOf L) ((Z.subgroupOf L).subgroupOf (P.subgroupOf L))
          ∪ indFamLinear (P.subgroupOf L) := by
    rw [coe_indFamDetectFinset]
    exact Set.subset_union_left
  have hcohX0 := (h.isCoherent_centralLayer hc hS (restrictBaseline hsub τ)
    (fun f => by rw [restrictBaseline_apply, hτ]; rfl)).2
  have hcohX : IsCoherent (indFamDetect (P.subgroupOf L)
      ((Z.subgroupOf L).subgroupOf (P.subgroupOf L)))
      (restrictBaseline Set.subset_union_left τ) :=
    isCoherent_of_eq_of_coe_eq (tau := indClassFun L) (coe_indFamDetectFinset _ _)
      (fun f => by rw [restrictBaseline_apply, hτ]; rfl)
      (fun f => by rw [restrictBaseline_apply, hτ]; rfl) hcohX0
  have hcohY : IsCoherent (indFamLinear (P.subgroupOf L))
      (restrictBaseline Set.subset_union_right τ) :=
    isCoherent_of_eq_of_coe_eq (tau := indClassFun L) rfl
      (fun _ => by rw [coe_tiIndCharSpanZeroHom])
      (fun f => by rw [restrictBaseline_apply, hτ]; rfl) (h.isCoherent_indFamLinear hCP)
  obtain ⟨νX, hνX⟩ := isCoherent_iff.1 hcohX
  obtain ⟨νY, hνY⟩ := isCoherent_iff.1 hcohY
  obtain ⟨ξ₀, hξ₀, hdegratio⟩ := exists_min_degree_ratio h
  obtain ⟨η₀, hη₀⟩ := hYne
  have hη₀deg : η₀ 1 = (Nat.card ↥E : ℂ) := h.apply_one_of_mem_indFamLinear hη₀
  obtain ⟨c, hc1, hcdeg, μY, hμY, -, Γ, hΓmem, hΓnorm, hΓortho, hbridge0⟩ :=
    SibleyLinearOrientation.IsFreeCentralSection.exists_int_and_isCoherentWith_and_bridge h hCP
      hZP' (τX := restrictBaseline Set.subset_union_left τ)
      (fun f => by rw [restrictBaseline_apply, hτ]; rfl) νX hνX
      (τY := restrictBaseline Set.subset_union_right τ)
      (fun f => by rw [restrictBaseline_apply, hτ]; rfl) νY hνY hξ₀ hη₀
  have hcη : ξ₀ 1 = (c : ℂ) * η₀ 1 := by rw [hcdeg, hη₀deg]
  obtain ⟨μX, hμX, -, hμXξ₀⟩ :=
    exists_isCoherentWith_apply_eq_of_bridge hXIrr hYIrr hXY hXne ⟨η₀, hη₀⟩ hXstar hYstar
      hXnr hYnr hτ1 hτiso hτstar₂ hνX hμY hξ₀ hη₀ hdegratio hcη hΓmem hΓnorm hΓortho
      (fun f hf => by
        rw [hτ, hf, ← Int.cast_smul_eq_zsmul ℂ c η₀]
        exact hbridge0)
  have hmem₃ : η₀ 1 • ξ₀ - ξ₀ 1 • η₀ ∈ charSpanZero (indFamDetect (P.subgroupOf L)
      ((Z.subgroupOf L).subgroupOf (P.subgroupOf L)) ∪ indFamLinear (P.subgroupOf L)) := by
    have h1 : η₀ 1 • ξ₀ = ((Nat.card ↥E : ℤ)) • ξ₀ := by
      rw [hη₀deg, show ((Nat.card ↥E : ℂ)) = (((Nat.card ↥E : ℤ) : ℂ)) by push_cast; ring,
        Int.cast_smul_eq_zsmul]
    have h2 : ξ₀ 1 • η₀ = ((c * Nat.card ↥E : ℤ)) • η₀ := by
      rw [hcdeg, show ((c : ℂ) * (Nat.card ↥E : ℂ)) = (((c * Nat.card ↥E : ℤ) : ℂ)) by
        push_cast; ring, Int.cast_smul_eq_zsmul]
    refine mem_charSpanZero.2 ⟨?_, ?_⟩
    · rw [h1, h2]
      exact sub_mem (Submodule.smul_mem _ _ (Submodule.subset_span (Or.inl hξ₀)))
        (Submodule.smul_mem _ _ (Submodule.subset_span (Or.inr hη₀)))
    · simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      ring
  refine (isCoherentWith_joinHom hXIrr hYIrr hXY hXne ⟨η₀, hη₀⟩ hXstar hYstar hXnr hYnr
    hτ1 hτiso hτstar hμX hμY hξ₀ hη₀ (hw3 := hmem₃) ?_).isCoherent
  have hkey : (η₀ 1 • ξ₀ - ξ₀ 1 • η₀ : ↥L → ℂ)
      = (Nat.card ↥E : ℂ) • (ξ₀ - (c : ℂ) • η₀) := by
    rw [hη₀deg, hcdeg]
    module
  rw [hτ]
  change indClassFun L (η₀ 1 • ξ₀ - ξ₀ 1 • η₀) = _
  rw [hkey, indClassFun_smul, hbridge0, hμXξ₀, hη₀deg, hcdeg]
  module

end IsFreeCentralSection

end FreeCentralSectionJointCoherence

end CFSG.FeitThompson
