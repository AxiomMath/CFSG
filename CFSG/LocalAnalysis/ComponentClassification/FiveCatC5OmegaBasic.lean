module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofComponentLift

public section

namespace CFSG.ComponentClassification.SolMax.FiveCat.C5Omega

open CFSG Subgroup
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open scoped commutatorElement

@[expose] def NotOnlyA5 (G : Type) [Group G] : Prop :=
  ∀ L : Subgroup G, IsComponent L → Nonempty (↥L ⧸ center ↥L ≃* alternatingGroup (Fin 5)) →
    ∃ L' : Subgroup G, IsComponent L' ∧ L' ≠ L

theorem nonempty_a5_map {G H : Type} [Group G] [Group H] (e : G ≃* H) {L : Subgroup G}
    (hA : Nonempty (↥L ⧸ center ↥L ≃* alternatingGroup (Fin 5))) :
    Nonempty (↥(L.map e.toMonoidHom) ⧸ center ↥(L.map e.toMonoidHom) ≃*
      alternatingGroup (Fin 5)) := by
  obtain ⟨eA⟩ := hA
  exact ⟨(QuotientGroup.congr _ _ (L.equivMapOfInjective e.toMonoidHom e.injective)
    (Subgroup.map_center_eq _)).symm.trans eA⟩

theorem exists_component_ne_of_mulEquiv {G H : Type} [Group G] [Group H] (e : G ≃* H)
    {L : Subgroup G} (h : ∃ L' : Subgroup H, IsComponent L' ∧ L' ≠ L.map e.toMonoidHom) :
    ∃ L' : Subgroup G, IsComponent L' ∧ L' ≠ L := by
  obtain ⟨L', hL', hne⟩ := h
  refine ⟨L'.map e.symm.toMonoidHom, LocalCores.isComponent_map_mulEquiv e.symm hL',
    fun h => hne ?_⟩
  calc L' = (L'.map e.symm.toMonoidHom).map e.toMonoidHom := by
        rw [Subgroup.map_map]
        have : e.toMonoidHom.comp e.symm.toMonoidHom = MonoidHom.id H := by
          ext
          simp
        rw [this, Subgroup.map_id]
    _ = L.map e.toMonoidHom := by rw [h]

theorem NotOnlyA5.of_mulEquiv {G H : Type} [Group G] [Group H] (e : G ≃* H) (h : NotOnlyA5 H) :
    NotOnlyA5 G := fun L hL hA =>
  exists_component_ne_of_mulEquiv e
    (h _ (LocalCores.isComponent_map_mulEquiv e hL) (nonempty_a5_map e hA))

theorem isComponent_map_inr {G₁ G₂ : Type} [Group G₁] [Group G₂] {C : Subgroup G₂}
    (hC : IsComponent C) : IsComponent (C.map (MonoidHom.inr G₁ G₂)) := by
  refine ⟨LocalCores.isQuasisimple_of_mulEquiv
    (C.equivMapOfInjective (MonoidHom.inr G₁ G₂) (fun x y h => (Prod.ext_iff.1 h).2)) hC.1, ?_⟩
  have h : C.map (MonoidHom.inr G₁ G₂) =
      C.comap (MonoidHom.snd G₁ G₂) ⊓ (MonoidHom.fst G₁ G₂).ker := by
    ext x
    simp only [Subgroup.mem_map, Subgroup.mem_inf, Subgroup.mem_comap, MonoidHom.mem_ker,
      MonoidHom.coe_snd, MonoidHom.coe_fst, MonoidHom.inr_apply]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨hy, rfl⟩
    · rintro ⟨h1, h2⟩
      exact ⟨x.2, h1, Prod.ext h2.symm rfl⟩
  rw [h]
  exact (hC.2.comap _).inf (Subgroup.Normal.isSubnormal inferInstance)

theorem two_components_of_central_cover {P S : Type} [Group P] [Group S] [Finite P] {π : P →* S}
    (hπ : Function.Surjective π) (hK : π.ker ≤ center P) {a : MulAut P} {α : MulAut S}
    (ha : ∀ x, a (a x) = x) (hα : ∀ s, α (α s) = s) (hcomm : ∀ x, π (a x) = α (π x))
    {Q₁ Q₂ : Subgroup P} (h₁ : CFSG.Assembly.IsComponentOf Q₁ (fixedSubgroup a))
    (h₂ : CFSG.Assembly.IsComponentOf Q₂ (fixedSubgroup a)) (hne : Q₁ ≠ Q₂) :
    ∃ L₁ L₂ : Subgroup ↥(fixedSubgroup α), IsComponent L₁ ∧ IsComponent L₂ ∧ L₁ ≠ L₂ := by
  obtain ⟨-, -, hbij, -⟩ :=
    LocalAnalysis.ComponentInitial.full_central_kernel_involution_fixed_component_correspondence
      hπ hK ha hα hcomm
  have hR₁ : CFSG.Assembly.IsComponentOf (Q₁.map π) (fixedSubgroup α) := hbij.mapsTo h₁
  have hR₂ : CFSG.Assembly.IsComponentOf (Q₂.map π) (fixedSubgroup α) := hbij.mapsTo h₂
  have hne' : Q₁.map π ≠ Q₂.map π := fun h => hne (hbij.injOn h₁ h₂ h)
  refine ⟨(Q₁.map π).subgroupOf (fixedSubgroup α), (Q₂.map π).subgroupOf (fixedSubgroup α),
    (LocalAnalysis.ComponentInitial.isComponentOf_iff_isComponent_subgroupOf hR₁.1).1 hR₁,
    (LocalAnalysis.ComponentInitial.isComponentOf_iff_isComponent_subgroupOf hR₂.1).1 hR₂,
    fun h => hne' ?_⟩
  have := (Subgroup.subgroupOf_inj).1 h
  rwa [inf_eq_left.2 hR₁.1, inf_eq_left.2 hR₂.1] at this

open CFSG.ComponentClassification.CatalogueBOrthogonalLinearFixed in
theorem two_components_of_normalQuotientFixed {X : Type} [Group X] [Finite X] (N Z : Subgroup X)
    [N.Normal] [Z.Normal] (hcentral : Z ≤ center X) (hXN : commutator X ≤ N) (ψ : MulAut X)
    (hψ : ∀ x, ψ (ψ x) = x) (hN : N.map ψ.toMonoidHom = N) (hZ : Z.map ψ.toMonoidHom = Z)
    {M₁ M₂ : Subgroup ↥(fixedSubgroup ψ)} (h₁ : IsComponent M₁) (h₂ : IsComponent M₂)
    (hne : M₁ ≠ M₂) :
    ∃ L₁ L₂ : Subgroup ↥(fixedSubgroup (onNormalCentralQuotient N Z ψ hN hZ)),
      IsComponent L₁ ∧ IsComponent L₂ ∧ L₁ ≠ L₂ := by
  set a := restrictAutomorphism N ψ hN with ha_def
  set Fn : Subgroup ↥(fixedSubgroup ψ) := N.subgroupOf (fixedSubgroup ψ) with hFn
  set B := fixedSubgroup a with hB
  have hle : ∀ {M : Subgroup ↥(fixedSubgroup ψ)}, IsComponent M → M ≤ Fn := by
    intro M hM x hx
    have hperf : ⁅M, M⁆ = M := Subgroup.isPerfect_iff.mp hM.1.1
    rw [← hperf] at hx
    have hcomm : ⁅M, M⁆ ≤ N.subgroupOf (fixedSubgroup ψ) := by
      rw [Subgroup.commutator_le]
      intro g₁ _ g₂ _
      have h1 : ((⁅g₁, g₂⁆ : ↥(fixedSubgroup ψ)) : X) = ⁅(g₁ : X), (g₂ : X)⁆ := rfl
      rw [Subgroup.mem_subgroupOf, h1]
      exact hXN (Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _))
    exact hcomm hx
  let lift : Subgroup ↥(fixedSubgroup ψ) → Subgroup ↥N := fun M =>
    ((M.subgroupOf Fn).map (fixedNormalEquiv N ψ hN).symm.toMonoidHom).map B.subtype
  have hlift : ∀ {M : Subgroup ↥(fixedSubgroup ψ)}, IsComponent M →
      CFSG.Assembly.IsComponentOf (lift M) B := by
    intro M hM
    have hc₁ : IsComponent (M.subgroupOf Fn) :=
      LocalAnalysis.ComponentInitial.component_overgroup hM (hle hM)
    have hc₂ := LocalCores.isComponent_map_mulEquiv (fixedNormalEquiv N ψ hN).symm hc₁
    refine (LocalAnalysis.ComponentInitial.isComponentOf_iff_isComponent_subgroupOf
      (Subgroup.map_subtype_le _)).2 ?_
    have hQQ : ((((M.subgroupOf Fn).map (fixedNormalEquiv N ψ hN).symm.toMonoidHom).map
        B.subtype)).subgroupOf B =
        (M.subgroupOf Fn).map (fixedNormalEquiv N ψ hN).symm.toMonoidHom :=
      Subgroup.comap_map_eq_self_of_injective (Subgroup.subtype_injective _) _
    rw [hQQ]
    exact hc₂
  have hinj : ∀ {M₁ M₂ : Subgroup ↥(fixedSubgroup ψ)}, IsComponent M₁ → IsComponent M₂ →
      lift M₁ = lift M₂ → M₁ = M₂ := by
    intro M₁ M₂ hM₁ hM₂ h
    have h1 := Subgroup.map_injective (Subgroup.subtype_injective B) h
    have h2 := Subgroup.map_injective (fixedNormalEquiv N ψ hN).symm.injective h1
    have h3 := (Subgroup.subgroupOf_inj).1 h2
    rwa [inf_eq_left.2 (hle hM₁), inf_eq_left.2 (hle hM₂)] at h3
  have hπ : Function.Surjective (QuotientGroup.mk' (Z.subgroupOf N)) :=
    QuotientGroup.mk'_surjective _
  have hK : (QuotientGroup.mk' (Z.subgroupOf N)).ker ≤ center ↥N := by
    rw [QuotientGroup.ker_mk']
    exact central_subgroupOf N Z hcentral
  have ha : ∀ x, a (a x) = x := fun x => Subtype.ext (by
    rw [ha_def, restrictAutomorphism_apply, restrictAutomorphism_apply]
    exact hψ x.val)
  have hcomm : ∀ x, QuotientGroup.mk' (Z.subgroupOf N) (a x) =
      onNormalCentralQuotient N Z ψ hN hZ (QuotientGroup.mk' (Z.subgroupOf N) x) :=
    fun x => (onNormalCentralQuotient_mk N Z ψ hN hZ x).symm
  have hα : ∀ s, onNormalCentralQuotient N Z ψ hN hZ
      (onNormalCentralQuotient N Z ψ hN hZ s) = s := by
    intro s
    obtain ⟨x, rfl⟩ := hπ s
    rw [← hcomm, ← hcomm, ha]
  exact two_components_of_central_cover hπ hK ha hα hcomm (hlift h₁) (hlift h₂)
    (fun h => hne (hinj h₁ h₂ h))

open CFSG.ComponentClassification.CatalogueBOrthogonalLinearFixed in
theorem notOnlyA5_of_normalQuotient {X : Type} [Group X] [Finite X] (N Z : Subgroup X)
    [N.Normal] [Z.Normal] (hcentral : Z ≤ center X) (hXN : commutator X ≤ N) (ψ : MulAut X)
    (hψ : ∀ x, ψ (ψ x) = x) (hN : N.map ψ.toMonoidHom = N) (hZ : Z.map ψ.toMonoidHom = Z)
    (h : NotOnlyA5 ↥(fixedSubgroup ψ)) :
    NotOnlyA5 ↥(fixedSubgroup (onNormalCentralQuotient N Z ψ hN hZ)) := by
  intro L hL hA
  obtain ⟨M, hM, ⟨e⟩⟩ :=
    CatLeafProof.exists_component_of_normalQuotientFixed N Z hcentral ψ hN hZ hL
  obtain ⟨M', hM', hne⟩ := h M hM ⟨e.symm.trans hA.some⟩
  obtain ⟨L₁, L₂, h₁, h₂, hne'⟩ :=
    two_components_of_normalQuotientFixed N Z hcentral hXN ψ hψ hN hZ hM hM' (Ne.symm hne)
  by_cases h1 : L₁ = L
  · exact ⟨L₂, h₂, fun h => hne' (h1.trans h.symm)⟩
  · exact ⟨L₁, h₁, h1⟩

end CFSG.ComponentClassification.SolMax.FiveCat.C5Omega
