module

public import CFSG.LocalAnalysis.SeitzReduction.E8PilotPositionNeighbour
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotLeviAutBasic

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.E8Pilot

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.EvenSmallLie

section RootSL2

variable {τ : Tag} {K : Type} [Field K]

variable (τ K) in
@[expose] noncomputable def rootPairSL2 (β : Fin τ.rank → ℤ) : Subgroup (adjointGroup τ K) :=
  (rootSubgroup τ K β ⊔ rootSubgroup τ K (-β)).subgroupOf (adjointGroup τ K)

theorem rootPairSL2_eq_closure (β : Fin τ.rank → ℤ) :
    rootPairSL2 τ K β = closure (Set.range (fun c : K => EPilot.pinnedElt τ β c) ∪
      Set.range (fun c : K => EPilot.pinnedElt τ (-β) c)) := by
  apply map_injective (adjointGroup τ K).subtype_injective
  rw [rootPairSL2, map_subgroupOf_eq_of_le
      (sup_le (rootSubgroup_le_adjointGroup _) (rootSubgroup_le_adjointGroup _)),
    MonoidHom.map_closure, Set.image_union, Subgroup.closure_union, rootSubgroup, rootSubgroup,
    ← Set.range_comp, ← Set.range_comp]
  rfl

theorem map_rootPairSL2_eq_of_forall {N : Type*} [Group N] (Ψ : adjointGroup τ K →* N)
    (β : Fin τ.rank → ℤ) {a b : K → N} (ha : ∀ c, Ψ (EPilot.pinnedElt τ β c) = a c)
    (hb : ∀ c, Ψ (EPilot.pinnedElt τ (-β) c) = b c) :
    (rootPairSL2 τ K β).map Ψ = closure (Set.range a ∪ Set.range b) := by
  rw [rootPairSL2_eq_closure, MonoidHom.map_closure, Set.image_union, ← Set.range_comp,
    ← Set.range_comp]
  congr 3
  · exact funext ha
  · exact funext hb

theorem map_entrywiseAdjointAut_rootPairSL2 (σ : K ≃+* K) (β : Fin τ.rank → ℤ) :
    (rootPairSL2 τ K β).map (entrywiseAdjointAut τ σ).toMonoidHom = rootPairSL2 τ K β := by
  rw [map_rootPairSL2_eq_of_forall _ β (a := fun c => EPilot.pinnedElt τ β (σ c))
      (b := fun c => EPilot.pinnedElt τ (-β) (σ c))
      (fun c => EPilot.entrywiseAdjointAut_pinnedElt σ β c)
      (fun c => EPilot.entrywiseAdjointAut_pinnedElt σ (-β) c),
    rootPairSL2_eq_closure]
  have hrange : ∀ F : K → adjointGroup τ K, Set.range (fun c => F (σ c)) = Set.range F :=
    fun F => Set.ext fun x => ⟨fun ⟨c, hc⟩ => ⟨σ c, hc⟩, fun ⟨c, hc⟩ => ⟨σ.symm c, by
      simp only [RingEquiv.apply_symm_apply]
      exact hc⟩⟩
  rw [hrange (fun c => EPilot.pinnedElt τ β c), hrange (fun c => EPilot.pinnedElt τ (-β) c)]

theorem isAutConj_rootPairSL2_E7_E8 (hτ : τ = .E7 ∨ τ = .E8) {f : ℕ} (hf : 1 ≤ f)
    (hK : Nat.card K = 2 ^ f) (β : Fin τ.rank → ℤ) :
    E6Pilot.IsAutConj (rootPairSL2 τ K β) := by
  intro α
  obtain ⟨hNF, -⟩ := even_E7_E8_exact_inner_field_automorphism_normal_form hf K hK τ hτ
  obtain ⟨⟨g, σ⟩, hgσ, -⟩ := hNF α
  have hα : α = MulAut.conj g * entrywiseAdjointAut τ σ := by
    refine MulEquiv.ext fun h => Subtype.ext ?_
    rw [hgσ h, MulAut.mul_apply, MulAut.conj_apply]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, coe_entrywiseAdjointAut]
  refine ⟨g, ?_⟩
  have hcomp : (MulAut.conj g * entrywiseAdjointAut τ σ).toMonoidHom =
      (MulAut.conj g).toMonoidHom.comp (entrywiseAdjointAut τ σ).toMonoidHom := rfl
  rw [hα, hcomp, ← Subgroup.map_map, map_entrywiseAdjointAut_rootPairSL2]

end RootSL2

section Levi

@[expose] noncomputable def xWeylE8 : WeylGroup .E8 :=
  (EPilot.exists_smul_highRoot_eq (Or.inr (Or.inr rfl)) isRoot_rootXE8).choose

theorem xWeylE8_smul_highRoot : xWeylE8 • highRoot .E8 = rootXE8 :=
  (EPilot.exists_smul_highRoot_eq (Or.inr (Or.inr rfl)) isRoot_rootXE8).choose_spec

theorem inv_xWeylE8_smul_highRoot_mem_perpRoots :
    xWeylE8⁻¹ • highRoot .E8 ∈ EPilot.perpRoots .E8 := by
  rw [EPilot.mem_perpRoots_iff_iform (Or.inr (Or.inr rfl))]
  refine ⟨IsRoot.smul (isRoot_highRoot _) _, ?_⟩
  rw [← iform_smul xWeylE8, smul_inv_smul, xWeylE8_smul_highRoot,
    CFSG.LieType.Steinberg.Adjoint.iform_comm,
    EPilot.iform_highRoot (Or.inr (Or.inr rfl))]
  decide

@[expose] noncomputable def xRootE7 : Fin (Tag.rank .E7) → ℤ :=
  e8Restrict (xWeylE8⁻¹ • highRoot .E8)

theorem isRoot_xRootE7 : IsRoot .E7 xRootE7 :=
  isRoot_e8Restrict inv_xWeylE8_smul_highRoot_mem_perpRoots.1
    inv_xWeylE8_smul_highRoot_mem_perpRoots.2

theorem e7Embed_xRootE7 : e7Embed xRootE7 = xWeylE8⁻¹ • highRoot .E8 :=
  e7Embed_e8Restrict inv_xWeylE8_smul_highRoot_mem_perpRoots.2

variable {K : Type} [Field K] [Finite K] [CharP K 2]

variable (K) in
@[expose] noncomputable def xConjE8 : adjointGroup .E8 K :=
  ⟨canonicalRep (coxeterSystem .E8) K xWeylE8, canonicalRep_mem_adjointGroup _ K xWeylE8⟩

theorem xLeviE8_eq_map_xConjE8 :
    xLeviE8 K = (e7Levi K).map (MulAut.conj (xConjE8 K)).toMonoidHom := by
  rw [xLeviE8, EPilot.rootPerpLevi, ← xWeylE8_smul_highRoot,
    ← EPilot.map_conj_rootSpan_perpRoots (Or.inr (Or.inr rfl)) xWeylE8, e7Levi,
    CFSG.LieType.Chevalley.map_conj_subgroupOf (EPilot.rootSpan_le_adjointGroup' _)]
  rfl

variable (K) in
@[expose] noncomputable def xLeviE8Equiv : adjointGroup .E7 K ≃* xLeviE8 K :=
  (e7LeviEquiv K).symm.trans (((e7Levi K).equivMapOfInjective _
    (MulAut.conj (xConjE8 K)).injective).trans (MulEquiv.subgroupCongr xLeviE8_eq_map_xConjE8.symm))

theorem coe_xLeviE8Equiv (y : adjointGroup .E7 K) :
    ((xLeviE8Equiv K y : xLeviE8 K) : adjointGroup .E8 K) =
      xConjE8 K * ((e7LeviEquiv K).symm y : adjointGroup .E8 K) * (xConjE8 K)⁻¹ :=
  rfl

theorem canonicalRep_conj_pinnedX_eq {γ : Fin (Tag.rank .E8) → ℤ} (hγ : IsRoot .E8 γ) (c : K) :
    canonicalRep (coxeterSystem .E8) K xWeylE8 * pinnedX .E8 K γ c *
        (canonicalRep (coxeterSystem .E8) K xWeylE8)⁻¹ = pinnedX .E8 K (xWeylE8 • γ) c := by
  obtain ⟨ε, hε, hεc⟩ := exists_canonicalRep_mul_pinnedX_mul_inv K xWeylE8 hγ
  have hε1 : ε = 1 := by
    have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
    have : (ε - 1) * (ε - 1) = 0 := by linear_combination hε + (1 - ε) * h2
    exact sub_eq_zero.1 (mul_self_eq_zero.1 this)
  rw [hεc, hε1, one_mul]

theorem xLeviE8Equiv_pinnedElt (c : K) :
    ((xLeviE8Equiv K (EPilot.pinnedElt .E7 xRootE7 c) : xLeviE8 K) : adjointGroup .E8 K) =
      EPilot.pinnedElt .E8 (highRoot .E8) c := by
  refine Subtype.ext ?_
  rw [coe_xLeviE8Equiv]
  simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  rw [coe_e7LeviEquiv_symm_pinnedX isRoot_xRootE7 c, e7Embed_xRootE7]
  have hr : IsRoot .E8 (xWeylE8⁻¹ • highRoot .E8) := IsRoot.smul (isRoot_highRoot _) _
  have h := canonicalRep_conj_pinnedX_eq (K := K) hr c
  rw [smul_inv_smul] at h
  exact h

theorem xLeviE8Equiv_pinnedElt_neg (c : K) :
    ((xLeviE8Equiv K (EPilot.pinnedElt .E7 (-xRootE7) c) : xLeviE8 K) : adjointGroup .E8 K) =
      EPilot.pinnedElt .E8 (-highRoot .E8) c := by
  refine Subtype.ext ?_
  rw [coe_xLeviE8Equiv]
  simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  rw [coe_e7LeviEquiv_symm_pinnedX (IsRoot.neg isRoot_xRootE7) c, e7Embed_neg, e7Embed_xRootE7]
  have hr : IsRoot .E8 (-(xWeylE8⁻¹ • highRoot .E8)) := IsRoot.neg (IsRoot.smul (isRoot_highRoot _) _)
  have h := canonicalRep_conj_pinnedX_eq (K := K) hr c
  rw [smul_neg, smul_inv_smul] at h
  exact h

theorem map_rootPairSL2_xLeviE8Equiv :
    ((rootPairSL2 .E7 K xRootE7).map (xLeviE8Equiv K).toMonoidHom).map (xLeviE8 K).subtype =
      posJE8 K := by
  rw [Subgroup.map_map, map_rootPairSL2_eq_of_forall ((xLeviE8 K).subtype.comp
      (xLeviE8Equiv K).toMonoidHom) xRootE7 (a := fun c => EPilot.pinnedElt .E8 (highRoot .E8) c)
      (b := fun c => EPilot.pinnedElt .E8 (-highRoot .E8) c) xLeviE8Equiv_pinnedElt
      xLeviE8Equiv_pinnedElt_neg, ← rootPairSL2_eq_closure]
  rfl

theorem factF5E8 {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f) : FactF5E8 K := by
  intro ι
  obtain ⟨m, -, hm⟩ :=
    (isAutConj_rootPairSL2_E7_E8 (Or.inl rfl) hf hK xRootE7).isAutConjIn_map (xLeviE8Equiv K) ι
  rw [map_rootPairSL2_xLeviE8Equiv] at hm
  exact ⟨m, hm⟩

end Levi

theorem not_normal_neighbour_E8_of_two_le {G : Type} [Group G] [Finite G] {L : Subgroup G}
    (hset : StandardSetting G L) {f : ℕ} (hf : 2 ≤ f) {K : Type} [Field K]
    (hK : Nat.card K = 2 ^ f) (e : L ≃* adjointGroup .E8 K) {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t) {X : Subgroup G}
    (hX : (∃ A : Subgroup (adjointGroup .E8 K), A ≤ posJE8 K ∧ IsCyclic A ∧
        Nat.card A = Nat.card K + 1 ∧ X = (A.map e.symm.toMonoidHom).map L.subtype) ∨
      X = (((EPilot.highTorusLine .E8 K).subgroupOf (adjointGroup .E8 K)).map
        e.symm.toMonoidHom).map L.subtype)
    {D : Subgroup G} (hDe : D = ((e7Levi K).map e.symm.toMonoidHom).map L.subtype) :
    ¬ ((D.subgroupOf (centralizer (X : Set G))).map
        (QuotientGroup.mk' (oddCore (centralizer (X : Set G))))).Normal := by
  have := F4Pilot.finite_of_natCard_eq_two_pow hK
  have := F4Pilot.charP_two_of_natCard_eq_two_pow hK
  exact not_normal_neighbour_E8 hset hf hK e ht hKt (factF5E8 (by omega) hK) hX hDe

end CFSG.SeitzReduction.E8Pilot
