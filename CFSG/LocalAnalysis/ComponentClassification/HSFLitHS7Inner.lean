module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB5bTypes
public import CFSG.LocalAnalysis.ComponentClassification.AS76bLemma21Simple
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueRelativeBAlmostSimple
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneBasic
public import CFSG.ClassicalInvolution.LocalComponent.Layer
public import CFSG.ClassicalInvolution.LBalance.Main
public import CFSG.Adapters.QiuzhenLegacy.FeitThompson.GroupAction.Quotient

public section

namespace CFSG.ComponentClassification.HSFLit.HS7

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer

variable {G : Type} [Group G] [Finite G]

theorem not_isSolvable_alternating_seven : ¬ Group.IsSolvable (alternatingGroup (Fin 7)) := by
  have : IsSimpleGroup (alternatingGroup (Fin 7)) :=
    alternatingGroup.isSimpleGroup (by norm_num : 5 ≤ Nat.card (Fin 7))
  refine AS76b.not_isSolvable_of_isSimpleGroup fun h => ?_
  have h1 := h ⟨Equiv.swap 0 1 * Equiv.swap 1 2, by rw [Equiv.Perm.mem_alternatingGroup]; decide⟩
    ⟨Equiv.swap 0 1 * Equiv.swap 1 3, by rw [Equiv.Perm.mem_alternatingGroup]; decide⟩
  have h2 := congrArg (fun x : alternatingGroup (Fin 7) => (x : Equiv.Perm (Fin 7)) 0) h1
  revert h2
  decide

omit [Finite G] in
theorem not_isSolvable_of_oddBar {L : Subgroup G}
    (h7 : Nonempty (GSThmB.OddBar L ≃* alternatingGroup (Fin 7))) : ¬ Group.IsSolvable L := by
  obtain ⟨e⟩ := h7
  intro hs
  exact not_isSolvable_alternating_seven (Group.isSolvable_of_surjective (f := e.toMonoidHom.comp
    (QuotientGroup.mk' (pPrimeCore 2 ↥L))) (e.surjective.comp (QuotientGroup.mk'_surjective _)))

theorem generalizedFitting_nonabelian (hF : IsSimpleGroup ↥(generalizedFitting G))
    {L : Subgroup G} (h7 : Nonempty (GSThmB.OddBar L ≃* alternatingGroup (Fin 7))) :
    ∃ a b : ↥(generalizedFitting G), a * b ≠ b * a := by
  by_contra hc
  push Not at hc
  have hs := AS76b.isSolvable_of_generalizedFitting_comm hF hc
  exact not_isSolvable_of_oddBar h7 (subgroup_solvable_of_solvable L)

theorem oddCore_eq_bot [IsSimpleGroup ↥(GeneralizedFitting.subgroup G)]
    (hnonab : ∃ a b : ↥(GeneralizedFitting.subgroup G), a * b ≠ b * a) :
    CFSG.Open.componentClassificationOddCore G = ⊥ := by
  have hsolv : Group.IsSolvable (CFSG.Open.componentClassificationOddCore G) :=
    CFSG.Milestones.odd_order_solvable (OddCore.odd_card G)
  have hcomp : CFSG.IsComponent (GeneralizedFitting.subgroup G) :=
    ⟨(CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hnonab).1,
      (GeneralizedFitting.normal G).isSubnormal⟩
  have h := (CFSG.LocalCores.component_solvable_centralizer hsolv
    (Subgroup.Normal.isSubnormal inferInstance)).1 _ hcomp
  rw [Subgroup.commutator_comm, Subgroup.commutator_eq_bot_iff_le_centralizer,
    CatalogueRelativeB.simple_generalizedFitting_centralizer_eq_bot hnonab] at h
  exact le_bot_iff.1 h

theorem le_generalizedFitting (hF : IsSimpleGroup ↥(generalizedFitting G))
    (hnab : ∃ a b : ↥(generalizedFitting G), a * b ≠ b * a) {t : G} (ht : orderOf t = 2)
    {L : Subgroup G} (hLt : L ≤ centralizer ({t} : Set G))
    (hL : IsPComponent 2 (L.subgroupOf (centralizer ({t} : Set G)))) :
    L ≤ generalizedFitting G := by
  have hFeq := CFSG.generalizedFitting_eq_componentClassification G
  have : IsSimpleGroup ↥(GeneralizedFitting.subgroup G) := hFeq ▸ hF
  have hnab' : ∃ a b : ↥(GeneralizedFitting.subgroup G), a * b ≠ b * a := hFeq ▸ hnab
  have hcore := oddCore_eq_bot hnab'
  have htt : t * t = 1 := by rw [← pow_two, ← ht, pow_orderOf_eq_one]
  have h1 := ClassicalInvolution.twoComponent_le_layer_of_l2PrimeBalance
    ClassicalInvolution.l2PrimeBalance hcore htt rfl
    ((CatalogueBAlternating.pComponent_two_iff _).mp hL)
  rw [subgroupOf_map_subtype, inf_eq_left.mpr hLt] at h1
  rw [hFeq]
  exact h1.trans le_sup_right

section Restrict

variable {N : Subgroup G}

omit [Finite G] in
theorem map_centralizer_subtype (t : N) :
    (centralizer ({t} : Set ↥N)).map N.subtype = centralizer ({(t : G)} : Set G) ⊓ N := by
  ext x
  simp only [mem_map, mem_inf, mem_centralizer_singleton_iff, subtype_apply]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨congrArg Subtype.val hy, y.2⟩
  · rintro ⟨hx, hxN⟩
    exact ⟨⟨x, hxN⟩, Subtype.ext hx, rfl⟩

theorem isPComponent_restrict {t : N} {L : Subgroup G} (hLN : L ≤ N)
    (hLt : L ≤ centralizer ({(t : G)} : Set G))
    (hL : IsPComponent 2 (L.subgroupOf (centralizer ({(t : G)} : Set G)))) :
    IsPComponent 2 ((L.subgroupOf N).subgroupOf (centralizer ({t} : Set ↥N))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [Burgoyne.isPComponent_subgroupOf_map_iff 2 Nat.prime_two N.subtype_injective,
    map_centralizer_subtype, subgroupOf_map_subtype, inf_eq_left.mpr hLN]
  exact CatalogueBPrimeJoin.pComponent_subgroupOf_of_le (le_inf hLt hLN) inf_le_left hL

omit [Finite G] in
theorem le_centralizer_restrict {t : N} {L : Subgroup G}
    (hLt : L ≤ centralizer ({(t : G)} : Set G)) :
    L.subgroupOf N ≤ centralizer ({t} : Set ↥N) := by
  intro x hx
  rw [mem_centralizer_singleton_iff]
  exact Subtype.ext (mem_centralizer_singleton_iff.mp (hLt (mem_subgroupOf.mp hx)))

omit [Finite G] in
theorem nonempty_oddBar_restrict {L : Subgroup G} (hLN : L ≤ N) {Q : Type*} [Group Q]
    (h : Nonempty (GSThmB.OddBar L ≃* Q)) :
    Nonempty (↥(L.subgroupOf N) ⧸ pPrimeCore 2 ↥(L.subgroupOf N) ≃* Q) := by
  obtain ⟨e⟩ := h
  let e₀ : ↥(L.subgroupOf N) ≃* ↥L := subgroupOfEquivOfLe hLN
  exact ⟨(QuotientGroup.congr _ _ e₀ (pPrimeCore_map_iso 2 e₀)).trans e⟩

omit [Finite G] in
theorem map_pPrimeCore_restrict {L : Subgroup G} (hLN : L ≤ N) :
    ((pPrimeCore 2 ↥(L.subgroupOf N)).map (L.subgroupOf N).subtype).map N.subtype =
      (pPrimeCore 2 ↥L).map L.subtype := by
  let e₀ : ↥(L.subgroupOf N) ≃* ↥L := subgroupOfEquivOfLe hLN
  have hcomp : N.subtype.comp (L.subgroupOf N).subtype = L.subtype.comp e₀.toMonoidHom := by
    ext x
    rfl
  rw [map_map, hcomp, ← map_map, pPrimeCore_map_iso 2 e₀]

omit [Finite G] in
theorem mem_normalizer_of_restrict {L : Subgroup G} (hLN : L ≤ N) {g : N}
    (hg : g ∈ normalizer ((L.subgroupOf N : Subgroup ↥N) : Set ↥N)) :
    (g : G) ∈ normalizer (L : Set G) := by
  rw [mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    have h1 := (mem_normalizer_iff.mp hg ⟨x, hLN hx⟩).mp (mem_subgroupOf.mpr hx)
    exact mem_subgroupOf.mp h1
  · intro hx
    have hxN : x ∈ N := by
      have h2 : (g : G) * x * (g : G)⁻¹ ∈ N := hLN hx
      have h3 : (g : G)⁻¹ * ((g : G) * x * (g : G)⁻¹) * (g : G) ∈ N :=
        mul_mem (mul_mem (inv_mem g.2) h2) g.2
      simpa [mul_assoc] using h3
    have h1 := (mem_normalizer_iff.mp hg ⟨x, hxN⟩).mpr (mem_subgroupOf.mpr hx)
    exact mem_subgroupOf.mp h1

omit [Finite G] in
theorem map_coreActionKernel_restrict_le {L : Subgroup G} (hLN : L ≤ N) :
    (coreActionKernel (L.subgroupOf N)).map N.subtype ≤ coreActionKernel L := by
  rintro _ ⟨g, hg, rfl⟩
  obtain ⟨hgN, hgc⟩ := mem_coreActionKernel.mp hg
  refine mem_coreActionKernel.mpr ⟨mem_normalizer_of_restrict hLN hgN, fun j hj => ?_⟩
  have h1 := hgc ⟨j, hLN hj⟩ (mem_subgroupOf.mpr hj)
  have h2 : N.subtype (⟨j, hLN hj⟩⁻¹ * g⁻¹ * ⟨j, hLN hj⟩ * g) ∈
      ((pPrimeCore 2 ↥(L.subgroupOf N)).map (L.subgroupOf N).subtype).map N.subtype :=
    mem_map_of_mem _ h1
  rw [map_pPrimeCore_restrict hLN] at h2
  simpa using h2

omit [Finite G] in
theorem isCyclic_sylow_restrict {L : Subgroup G} (hLN : L ≤ N)
    (hcyc : ∀ R : Sylow 2 ↥(coreActionKernel L), IsCyclic (R : Subgroup ↥(coreActionKernel L))) :
    ∀ P : Sylow 2 ↥(coreActionKernel (L.subgroupOf N)),
      IsCyclic (P : Subgroup ↥(coreActionKernel (L.subgroupOf N))) := by
  intro P
  have hle := map_coreActionKernel_restrict_le hLN
  let φ : ↥(coreActionKernel (L.subgroupOf N)) →* ↥(coreActionKernel L) :=
    { toFun := fun g => ⟨((g : N) : G), hle (mem_map_of_mem _ g.2)⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hφ : Function.Injective φ := by
    intro a b hab
    have h1 := congrArg (fun x : ↥(coreActionKernel L) => (x : G)) hab
    exact Subtype.ext (Subtype.ext h1)
  have hP2 : IsPGroup 2 ((P : Subgroup _).map φ) := P.isPGroup'.map φ
  obtain ⟨R, hR⟩ := hP2.exists_le_sylow
  have : IsCyclic (R : Subgroup ↥(coreActionKernel L)) := hcyc R
  have hc : IsCyclic ↥(((P : Subgroup _).map φ).subgroupOf (R : Subgroup _)) := inferInstance
  have hc' : IsCyclic ↥((P : Subgroup _).map φ) :=
    isCyclic_of_surjective (subgroupOfEquivOfLe hR).toMonoidHom (subgroupOfEquivOfLe hR).surjective
  exact isCyclic_of_surjective ((P : Subgroup _).equivMapOfInjective φ hφ).symm.toMonoidHom
    ((P : Subgroup _).equivMapOfInjective φ hφ).symm.surjective

end Restrict

theorem oddLieType_of_mem (hHSF : GSLit.HarrisSolomonFritzA7Input)
    (hF : IsSimpleGroup ↥(generalizedFitting G)) {t : G} (ht : orderOf t = 2)
    (htF : t ∈ generalizedFitting G) {L : Subgroup G} (hLt : L ≤ centralizer ({t} : Set G))
    (hL : IsPComponent 2 (L.subgroupOf (centralizer ({t} : Set G))))
    (h7 : Nonempty (GSThmB.OddBar L ≃* alternatingGroup (Fin 7)))
    (hcyc : ∀ R : Sylow 2 ↥(coreActionKernel L), IsCyclic (R : Subgroup ↥(coreActionKernel L))) :
    Blueprint.OddLieType ↥(generalizedFitting G) := by
  have hnab := generalizedFitting_nonabelian hF h7
  have hLN := le_generalizedFitting hF hnab ht hLt hL
  set N := generalizedFitting G with hN
  let t' : ↥N := ⟨t, htF⟩
  have ht' : orderOf t' = 2 := by rw [orderOf_mk]; exact ht
  rcases hHSF ↥N hnab t' ht' (L.subgroupOf N) (le_centralizer_restrict (t := t') hLt)
      (isPComponent_restrict (t := t') hLN hLt hL) (nonempty_oddBar_restrict hLN h7)
      (isCyclic_sylow_restrict hLN hcyc) with h | ⟨⟨e6⟩, -⟩
  · exact h
  · exfalso
    obtain ⟨e7⟩ := nonempty_oddBar_restrict hLN h7
    have h1 := Nat.card_congr (e6.symm.trans e7).toEquiv
    rw [nat_card_alternatingGroup, nat_card_alternatingGroup] at h1
    norm_num [Nat.factorial] at h1

end CFSG.ComponentClassification.HSFLit.HS7
