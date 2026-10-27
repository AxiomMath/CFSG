module

public import CFSG.GroupTheory.OddOverlap
public import CFSG.Open.StandardComponentRecognitionMilestoneDefs
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.LocalAnalysis.ComponentClassification.AssemblyBPredicates
public import CFSG.LocalAnalysis.ComponentClassification.TightEmbeddingConjugate

public section

namespace CFSG.StandardSubgroupAPI

open Subgroup ComponentClassification

variable {G : Type*} [Group G]

theorem conjugate_eq_map_conj_inv (H : Subgroup G) (g : G) :
    CFSG.conjugate H g = H.map (MulAut.conj g⁻¹).toMonoidHom := rfl

theorem rightConjugate_eq_conjugate (H : Subgroup G) (g : G) :
    AschbacherTightEmbedding.rightConjugate H g = CFSG.conjugate H g := rfl

theorem map_conj_eq_conjugate_inv (H : Subgroup G) (g : G) :
    H.map (MulAut.conj g).toMonoidHom = CFSG.conjugate H g⁻¹ := by
  rw [conjugate_eq_map_conj_inv, inv_inv]

theorem forall_not_mem_map_conj_iff (N H : Subgroup G) (P : Subgroup G → Prop) :
    (∀ g : G, g ∉ N → P (H.map (MulAut.conj g).toMonoidHom)) ↔
      ∀ g : G, g ∉ N → P (CFSG.conjugate H g) := by
  constructor
  · intro h g hg
    exact h g⁻¹ fun hinv => hg (N.inv_mem_iff.1 hinv)
  · intro h g hg
    rw [map_conj_eq_conjugate_inv]
    exact h g⁻¹ fun hinv => hg (N.inv_mem_iff.1 hinv)

theorem forall_map_conj_iff (H : Subgroup G) (P : Subgroup G → Prop) :
    (∀ g : G, P (H.map (MulAut.conj g).toMonoidHom)) ↔ ∀ g : G, P (CFSG.conjugate H g) :=
  ⟨fun h g => h g⁻¹, fun h g => by rw [map_conj_eq_conjugate_inv]; exact h g⁻¹⟩

theorem exists_mem_orderOf_eq_two_of_even [Finite G] {Q : Subgroup G}
    (h : Even (Nat.card Q)) : ∃ t ∈ Q, orderOf t = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := Q) 2 (even_iff_two_dvd.1 h)
  exact ⟨x, x.2, (Subgroup.orderOf_coe x).trans hx⟩

theorem standardComponentIsStandard_iff_assembly {L : Subgroup G} :
    Open.standardComponentIsStandard L ↔ Assembly.ComponentType.IsStandardSubgroup L :=
  Iff.rfl

theorem isStandardSubgroup_iff_standardComponentIsStandard {L : Subgroup G} :
    CFSG.IsStandardSubgroup L ↔ Open.standardComponentIsStandard L := by
  have hq := AssemblyBPredicates.isQuasisimple_iff_native L
  constructor
  · rintro ⟨hL, heven, htight, hNC, hcomm⟩
    exact ⟨hq.2 hL, heven,
      (forall_not_mem_map_conj_iff _ _ fun X => Odd (Nat.card ↥(centralizer (L : Set G) ⊓ X))).2
        htight, hNC, (forall_map_conj_iff L fun X => ⁅L, X⁆ ≠ ⊥).2 hcomm⟩
  · rintro ⟨hL, heven, htight, hNC, hcomm⟩
    exact ⟨hq.1 hL, heven,
      (forall_not_mem_map_conj_iff _ _ fun X => Odd (Nat.card ↥(centralizer (L : Set G) ⊓ X))).1
        htight, hNC, (forall_map_conj_iff L fun X => ⁅L, X⁆ ≠ ⊥).1 hcomm⟩

theorem isStandardSubgroup_iff_assembly {L : Subgroup G} :
    CFSG.IsStandardSubgroup L ↔ Assembly.ComponentType.IsStandardSubgroup L :=
  isStandardSubgroup_iff_standardComponentIsStandard

theorem classicalInvolutionTightlyEmbedded_bot :
    Open.classicalInvolutionTightlyEmbedded (⊥ : Subgroup G) := fun g hg =>
  (hg (by rw [Subgroup.normalizer_eq_top_iff.2 inferInstance]; exact Subgroup.mem_top g)).elim

theorem not_tightlyEmbedded_bot :
    ¬ AschbacherTightEmbedding.TightlyEmbedded (⊥ : Subgroup G) := by
  rintro ⟨heven, -⟩
  rw [Subgroup.card_bot] at heven
  exact Nat.not_even_one heven

theorem classicalInvolutionTightlyEmbedded_bot_and_not_tightlyEmbedded :
    Open.classicalInvolutionTightlyEmbedded (⊥ : Subgroup G) ∧
      ¬ AschbacherTightEmbedding.TightlyEmbedded (⊥ : Subgroup G) :=
  ⟨classicalInvolutionTightlyEmbedded_bot, not_tightlyEmbedded_bot⟩

theorem tightlyEmbedded_of_classical_of_mem {Q : Subgroup G}
    (h : Open.classicalInvolutionTightlyEmbedded Q) {u : G} (hu : u ∈ Q) (hu2 : orderOf u = 2) :
    AschbacherTightEmbedding.TightlyEmbedded Q :=
  (AschbacherTightEmbedding.tightlyEmbedded_iff_classical Q).2
    ⟨even_card_of_mem_of_orderOf_eq_two hu hu2, h⟩

theorem standardComponentIsStandard_iff_classical {L : Subgroup G} :
    Open.standardComponentIsStandard L ↔
      Open.IsQuasisimple L ∧ Even (Nat.card (centralizer (L : Set G))) ∧
        Open.classicalInvolutionTightlyEmbedded (centralizer (L : Set G)) ∧
        normalizer ((centralizer (L : Set G) : Subgroup G) : Set G) = normalizer (L : Set G) ∧
        ∀ g : G, ⁅L, L.map (MulAut.conj g).toMonoidHom⁆ ≠ ⊥ :=
  Iff.rfl

theorem standardComponentIsStandard_iff_tightlyEmbedded {L : Subgroup G} :
    Open.standardComponentIsStandard L ↔
      Open.IsQuasisimple L ∧ AschbacherTightEmbedding.TightlyEmbedded (centralizer (L : Set G)) ∧
        normalizer ((centralizer (L : Set G) : Subgroup G) : Set G) = normalizer (L : Set G) ∧
        ∀ g : G, ⁅L, L.map (MulAut.conj g).toMonoidHom⁆ ≠ ⊥ := by
  rw [standardComponentIsStandard_iff_classical,
    AschbacherTightEmbedding.tightlyEmbedded_iff_classical]
  exact ⟨fun ⟨hq, he, ht, hN, hc⟩ => ⟨hq, ⟨he, ht⟩, hN, hc⟩,
    fun ⟨hq, ⟨he, ht⟩, hN, hc⟩ => ⟨hq, he, ht, hN, hc⟩⟩

theorem centralizer_subgroupOf {L H : Subgroup G} (hLH : L ≤ H) :
    centralizer ((L.subgroupOf H : Subgroup H) : Set H) =
      (centralizer (L : Set G)).subgroupOf H := by
  ext c
  rw [mem_subgroupOf, mem_centralizer_iff, mem_centralizer_iff]
  constructor
  · intro h l hl
    have hl' : (⟨l, hLH hl⟩ : H) ∈ (L.subgroupOf H : Set H) := hl
    simpa using congrArg Subtype.val (h _ hl')
  · intro h l hl
    apply Subtype.ext
    simpa using h l hl

section MulEquiv

variable {K : Type*} [Group K]

theorem centralizer_map_mulEquiv (e : G ≃* K) (L : Subgroup G) :
    centralizer ((L.map e.toMonoidHom : Subgroup K) : Set K) =
      (centralizer (L : Set G)).map e.toMonoidHom := by
  ext x
  obtain ⟨y, rfl⟩ := e.surjective x
  rw [mem_map_equiv, MulEquiv.symm_apply_apply, mem_centralizer_iff, mem_centralizer_iff]
  constructor
  · intro h s hs
    apply e.injective
    rw [_root_.map_mul, _root_.map_mul]
    exact h (e s) ⟨s, hs, rfl⟩
  · rintro h _ ⟨s, hs, rfl⟩
    change e s * e y = e y * e s
    rw [← _root_.map_mul, ← _root_.map_mul, h s hs]

theorem map_conj_map_mulEquiv (e : G ≃* K) (H : Subgroup G) (g : G) :
    (H.map (MulAut.conj g).toMonoidHom).map e.toMonoidHom =
      (H.map e.toMonoidHom).map (MulAut.conj (e g)).toMonoidHom := by
  rw [map_map, map_map]
  congr 1
  ext x
  simp

end MulEquiv

end CFSG.StandardSubgroupAPI

namespace CFSG

theorem isStandardSubgroup_iff_standardComponentIsStandard {G : Type*} [Group G]
    {L : Subgroup G} : IsStandardSubgroup L ↔ Open.standardComponentIsStandard L :=
  StandardSubgroupAPI.isStandardSubgroup_iff_standardComponentIsStandard

theorem IsStandardSubgroup.standardComponentIsStandard {G : Type*} [Group G] {L : Subgroup G}
    (h : IsStandardSubgroup L) : Open.standardComponentIsStandard L :=
  isStandardSubgroup_iff_standardComponentIsStandard.1 h

theorem IsStandardSubgroup.tightlyEmbedded_centralizer {G : Type*} [Group G] {L : Subgroup G}
    (h : IsStandardSubgroup L) :
    ComponentClassification.AschbacherTightEmbedding.TightlyEmbedded
      (Subgroup.centralizer (L : Set G)) :=
  ⟨h.2.1, h.2.2.1⟩

theorem IsStandardSubgroup.assembly {G : Type*} [Group G] {L : Subgroup G}
    (h : IsStandardSubgroup L) : Assembly.ComponentType.IsStandardSubgroup L :=
  isStandardSubgroup_iff_standardComponentIsStandard.1 h

end CFSG

namespace CFSG.Open

variable {G : Type*} [Group G] {L : Subgroup G}

theorem standardComponentIsStandard.isStandardSubgroup (h : standardComponentIsStandard L) :
    CFSG.IsStandardSubgroup L :=
  isStandardSubgroup_iff_standardComponentIsStandard.2 h

theorem standardComponentIsStandard.ne_top (h : standardComponentIsStandard L)
    (hG : IsSimpleGroup G) (hGn : ∃ x y : G, x * y ≠ y * x) : L ≠ ⊤ := by
  intro htop
  subst htop
  have heven : Even (Nat.card (Subgroup.centralizer ((⊤ : Subgroup G) : Set G))) := h.2.1
  rw [Subgroup.coe_top, Subgroup.centralizer_univ] at heven
  rcases @Subgroup.Normal.eq_bot_or_eq_top G _ hG (Subgroup.center G) inferInstance with hc | hc
  · rw [hc, Subgroup.card_bot] at heven
    exact Nat.not_even_one heven
  · obtain ⟨x, y, hxy⟩ := hGn
    exact hxy (Subgroup.mem_center_iff.mp (hc ▸ Subgroup.mem_top x) y).symm

theorem standardComponentIsStandard.not_normal (h : standardComponentIsStandard L)
    (hG : IsSimpleGroup G) (hGn : ∃ x y : G, x * y ≠ y * x) : ¬ L.Normal := by
  intro hLn
  rcases @Subgroup.Normal.eq_bot_or_eq_top G _ hG L hLn with rfl | rfl
  · have hs : IsSimpleGroup (↥(⊥ : Subgroup G) ⧸ Subgroup.center ↥(⊥ : Subgroup G)) := h.1.2
    exact not_nontrivial _ hs.toNontrivial
  · exact h.ne_top hG hGn rfl

theorem standardComponentIsStandard.exists_involution_centralizer [Finite G]
    (h : standardComponentIsStandard L) :
    ∃ t ∈ Subgroup.centralizer (L : Set G), orderOf t = 2 :=
  StandardSubgroupAPI.exists_mem_orderOf_eq_two_of_even h.2.1

theorem standardComponentIsStandard.tightlyEmbedded_centralizer
    (h : standardComponentIsStandard L) :
    ComponentClassification.AschbacherTightEmbedding.TightlyEmbedded
      (Subgroup.centralizer (L : Set G)) :=
  (StandardSubgroupAPI.standardComponentIsStandard_iff_tightlyEmbedded.1 h).2.1

theorem standardComponentIsStandard.mem_normalizer_centralizer_of_commute
    (h : standardComponentIsStandard L) {u y : G} (hu : u ∈ Subgroup.centralizer (L : Set G))
    (hu2 : orderOf u = 2) (hy : y * u = u * y) :
    y ∈ Subgroup.normalizer (Subgroup.centralizer (L : Set G) : Set G) :=
  StandardSubgroupAPI.mem_of_odd_inf_map_conj_of_commute h.2.2.1 hu hu2 hy

theorem standardComponentIsStandard.mem_normalizer_of_commute
    (h : standardComponentIsStandard L) {u y : G} (hu : u ∈ Subgroup.centralizer (L : Set G))
    (hu2 : orderOf u = 2) (hy : y * u = u * y) : y ∈ Subgroup.normalizer (L : Set G) :=
  h.2.2.2.1 ▸ h.mem_normalizer_centralizer_of_commute hu hu2 hy

theorem standardComponentIsStandard.map_mulEquiv {K : Type*} [Group K] (e : G ≃* K)
    (h : standardComponentIsStandard L) : standardComponentIsStandard (L.map e.toMonoidHom) := by
  obtain ⟨hq, heven, htight, hnorm, hcomm⟩ := h
  have hC := CFSG.StandardSubgroupAPI.centralizer_map_mulEquiv e L
  refine ⟨IsQuasisimple.of_mulEquiv (e.subgroupMap L).symm hq, ?_, ?_, ?_, ?_⟩
  · rw [hC, Subgroup.card_map_of_injective e.injective]
    exact heven
  · intro g hg
    obtain ⟨g', rfl⟩ := e.surjective g
    have hg' : g' ∉ Subgroup.normalizer (Subgroup.centralizer (L : Set G) : Set G) := by
      intro h
      apply hg
      rw [hC, ← Subgroup.map_equiv_normalizer_eq]
      exact ⟨g', h, rfl⟩
    rw [hC, ← CFSG.StandardSubgroupAPI.map_conj_map_mulEquiv,
      ← Subgroup.map_inf_eq _ _ _ e.injective, Subgroup.card_map_of_injective e.injective]
    exact htight g' hg'
  · rw [hC, ← Subgroup.map_equiv_normalizer_eq, hnorm, Subgroup.map_equiv_normalizer_eq]
  · intro g h
    obtain ⟨g', rfl⟩ := e.surjective g
    apply hcomm g'
    rw [← CFSG.StandardSubgroupAPI.map_conj_map_mulEquiv, ← Subgroup.map_commutator,
      Subgroup.map_eq_bot_iff_of_injective _ e.injective] at h
    exact h

open Subgroup in
theorem standardComponentIsStandard.subgroupOf {H : Subgroup G}
    (h : standardComponentIsStandard L) (hLH : L ≤ H)
    (heven : Even (Nat.card (centralizer (L : Set G) ⊓ H : Subgroup G))) :
    standardComponentIsStandard (L.subgroupOf H) := by
  have hKt := h.tightlyEmbedded_centralizer
  obtain ⟨hq, -, -, hNK, hcomm⟩ := h
  set K := centralizer (L : Set G) with hKdef
  have hC : centralizer ((L.subgroupOf H : Subgroup H) : Set H) = (K ⊓ H).subgroupOf H := by
    rw [CFSG.StandardSubgroupAPI.centralizer_subgroupOf hLH, inf_subgroupOf_right]
  have hKH := CFSG.StandardSubgroupAPI.tightlyEmbedded_inf_subgroupOf hKt heven
  have hNH : normalizer (((K ⊓ H).subgroupOf H : Subgroup H) : Set H) =
      normalizer ((L.subgroupOf H : Subgroup H) : Set H) := by
    rw [← subgroupOf_normalizer_eq inf_le_right, ← subgroupOf_normalizer_eq hLH]
    ext x
    rw [mem_subgroupOf, mem_subgroupOf]
    constructor
    · intro hx
      rw [← hNK]
      exact CFSG.StandardSubgroupAPI.normalizer_le_normalizer_of_le_of_even hKt inf_le_left heven hx
    · intro hx
      have hxK : (x : G) ∈ normalizer (K : Set G) := by rw [hNK]; exact hx
      rw [mem_normalizer_iff]
      intro y
      rw [mem_inf, mem_inf, mem_normalizer_iff.mp hxK y]
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨h1, H.mul_mem (H.mul_mem x.2 h2) (H.inv_mem x.2)⟩
      · rintro ⟨h1, h2⟩
        refine ⟨h1, ?_⟩
        have := H.mul_mem (H.mul_mem (H.inv_mem x.2) h2) x.2
        simpa [mul_assoc] using this
  obtain ⟨hKHe, hKHt⟩ :=
    (CFSG.ComponentClassification.AschbacherTightEmbedding.tightlyEmbedded_iff_classical _).mp hKH
  refine ⟨IsQuasisimple.of_mulEquiv (subgroupOfEquivOfLe hLH) hq, ?_, ?_, ?_, ?_⟩
  · rw [hC]
    exact hKHe
  · rw [hC]
    exact hKHt
  · rw [hC]
    exact hNH
  · intro x hx
    apply hcomm x
    have hcomp : H.subtype.comp (MulAut.conj x).toMonoidHom =
        (MulAut.conj (x : G)).toMonoidHom.comp H.subtype := by
      ext y
      simp [MulAut.conj_apply]
    have hmap : ((L.subgroupOf H).map (MulAut.conj x).toMonoidHom).map H.subtype =
        L.map (MulAut.conj (x : G)).toMonoidHom := by
      rw [map_map, hcomp, ← map_map, subgroupOf_map_subtype, inf_eq_left.mpr hLH]
    have h2 : (⁅L.subgroupOf H, (L.subgroupOf H).map (MulAut.conj x).toMonoidHom⁆).map
        H.subtype = ⁅L, L.map (MulAut.conj (x : G)).toMonoidHom⁆ := by
      rw [map_commutator, hmap, subgroupOf_map_subtype, inf_eq_left.mpr hLH]
    rw [← h2, hx, Subgroup.map_bot]

end CFSG.Open

namespace CFSG

theorem IsStandardSubgroup.map_mulEquiv {G K : Type*} [Group G] [Group K] (e : G ≃* K)
    {L : Subgroup G} (h : IsStandardSubgroup L) : IsStandardSubgroup (L.map e.toMonoidHom) :=
  (h.standardComponentIsStandard.map_mulEquiv e).isStandardSubgroup

theorem IsStandardSubgroup.subgroupOf {G : Type*} [Group G] {L H : Subgroup G}
    (h : IsStandardSubgroup L) (hLH : L ≤ H)
    (heven : Even (Nat.card (Subgroup.centralizer ((L.subgroupOf H : Subgroup H) : Set H)))) :
    IsStandardSubgroup (L.subgroupOf H) := by
  rw [StandardSubgroupAPI.centralizer_subgroupOf hLH, ← Subgroup.inf_subgroupOf_right,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv] at heven
  exact (h.standardComponentIsStandard.subgroupOf hLH heven).isStandardSubgroup

end CFSG

namespace CFSG.Assembly.ComponentType

theorem IsStandardSubgroup.isStandardSubgroup {G : Type*} [Group G] {L : Subgroup G}
    (h : IsStandardSubgroup L) : CFSG.IsStandardSubgroup L :=
  isStandardSubgroup_iff_standardComponentIsStandard.2 h

end CFSG.Assembly.ComponentType
