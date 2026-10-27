module

public import CFSG.Open.ClassicalInvolutionTheoremMilestoneDefs
public import CFSG.LocalAnalysis.ComponentClassification.NormalizedProduct

public section

namespace CFSG.ComponentClassification.AschbacherTightEmbedding

@[expose] def rightConjugate {G : Type*} [Group G] (Q : Subgroup G) (g : G) : Subgroup G :=
  Q.map (MulAut.conj g⁻¹).toMonoidHom

@[expose] def TightlyEmbedded {G : Type*} [Group G] (Q : Subgroup G) : Prop :=
  Even (Nat.card Q) ∧ ∀ g : G, g ∉ Subgroup.normalizer (Q : Set G) →
    Odd (Nat.card (Q ⊓ rightConjugate Q g : Subgroup G))

@[expose] def sylowImage {G : Type*} [Group G] (M : Subgroup G) (T : Sylow 2 M) : Subgroup G :=
  (T : Subgroup M).map M.subtype

theorem mem_rightConjugate_iff {G : Type*} [Group G] (Q : Subgroup G) (g x : G) :
    x ∈ rightConjugate Q g ↔ g * x * g⁻¹ ∈ Q := by
  simpa [rightConjugate, MulAut.conj_apply] using
    (Subgroup.mem_map_equiv (f := MulAut.conj g⁻¹) (K := Q) (x := x))

theorem rightConjugate_one {G : Type*} [Group G] (Q : Subgroup G) :
    rightConjugate Q 1 = Q := by
  ext x
  simp [mem_rightConjugate_iff]

theorem rightConjugate_mul {G : Type*} [Group G] (Q : Subgroup G) (g h : G) :
    rightConjugate (rightConjugate Q g) h = rightConjugate Q (g * h) := by
  ext x
  simp only [mem_rightConjugate_iff, mul_inv_rev]
  group

theorem rightConjugate_card {G : Type*} [Group G] (Q : Subgroup G) (g : G) :
    Nat.card (rightConjugate Q g) = Nat.card Q :=
  Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective

theorem rightConjugate_eq_self_iff {G : Type*} [Group G] (Q : Subgroup G) (g : G) :
    rightConjugate Q g = Q ↔ g ∈ Subgroup.normalizer (Q : Set G) := by
  change Q.map (MulAut.conj g⁻¹) = Q ↔ g ∈ Subgroup.normalizer (Q : Set G)
  rw [← Subgroup.mem_normalizer_iff_map_conj_eq]
  exact (Subgroup.normalizer (Q : Set G)).inv_mem_iff

theorem tightlyEmbedded_iff_classical {G : Type*} [Group G] (Q : Subgroup G) :
    TightlyEmbedded Q ↔
      Even (Nat.card Q) ∧ CFSG.Open.classicalInvolutionTightlyEmbedded Q := by
  constructor
  · rintro ⟨heven, htight⟩
    refine ⟨heven, fun g hg => ?_⟩
    have h := htight g⁻¹ (fun hinv => hg ((Subgroup.normalizer _).inv_mem_iff.mp hinv))
    simpa [rightConjugate] using h
  · rintro ⟨heven, htight⟩
    refine ⟨heven, fun g hg => ?_⟩
    exact htight g⁻¹ (fun hinv => hg ((Subgroup.normalizer _).inv_mem_iff.mp hinv))

theorem two_subgroup_of_odd_eq_bot {G : Type*} [Group G] [Finite G]
    (T M : Subgroup G) (htwo : IsPGroup 2 T) (hodd : Odd (Nat.card M)) (hle : T ≤ M) :
    T = ⊥ := by
  apply T.eq_bot_iff_card.mpr
  have hoddT := hodd.of_dvd_nat (Subgroup.card_dvd_of_le hle)
  rcases htwo.card_eq_or_dvd with hone | hdivides
  · exact hone
  · exact (hoddT.not_two_dvd_nat hdivides).elim

theorem two_subgroup_inf_conjugate_eq_bot {G : Type*} [Group G] [Finite G]
    (Q T : Subgroup G) (htight : TightlyEmbedded Q) (htwo : IsPGroup 2 T)
    (g : G) (hg : g ∉ Subgroup.normalizer (Q : Set G)) (hle : T ≤ rightConjugate Q g) :
    T ⊓ Q = ⊥ := by
  exact two_subgroup_of_odd_eq_bot (T ⊓ Q) (Q ⊓ rightConjugate Q g)
    (htwo.to_le inf_le_left) (htight.2 g hg)
    (le_inf inf_le_right (inf_le_left.trans hle))

theorem normalizer_two_subgroup_le {G : Type*} [Group G] [Finite G]
    (Q T : Subgroup G) (htight : TightlyEmbedded Q) (htwo : IsPGroup 2 T)
    (hT : T ≤ Q) (hne : T ≠ ⊥) :
    Subgroup.normalizer (T : Set G) ≤ Subgroup.normalizer (Q : Set G) := by
  intro g hg
  by_contra houtside
  have hconjugate : T ≤ rightConjugate Q g := by
    have hmap := Subgroup.map_mono (f := (MulAut.conj g⁻¹).toMonoidHom) hT
    have hfixed : rightConjugate T g = T := (rightConjugate_eq_self_iff T g).mpr hg
    change rightConjugate T g ≤ rightConjugate Q g at hmap
    rwa [hfixed] at hmap
  have hbot := two_subgroup_inf_conjugate_eq_bot Q T htight htwo g houtside hconjugate
  rw [inf_eq_left.mpr hT] at hbot
  exact hne hbot

theorem centralizer_two_subgroup_le {G : Type*} [Group G] [Finite G]
    (Q T : Subgroup G) (htight : TightlyEmbedded Q) (htwo : IsPGroup 2 T)
    (hT : T ≤ Q) (hne : T ≠ ⊥) :
    Subgroup.centralizer (T : Set G) ≤ Subgroup.normalizer (Q : Set G) :=
  (Subgroup.centralizer_le_normalizer _).trans
    (normalizer_two_subgroup_le Q T htight htwo hT hne)

theorem sylowImage_le {G : Type*} [Group G] (M : Subgroup G) (T : Sylow 2 M) :
    sylowImage M T ≤ M := by
  rintro x ⟨t, ht, rfl⟩
  exact t.property

theorem sylowImage_isPGroup {G : Type*} [Group G] (M : Subgroup G) (T : Sylow 2 M) :
    IsPGroup 2 (sylowImage M T) :=
  T.isPGroup'.map M.subtype

theorem sylowImage_card {G : Type*} [Group G] (M : Subgroup G) (T : Sylow 2 M) :
    Nat.card (sylowImage M T) = Nat.card (T : Subgroup M) :=
  Subgroup.card_map_of_injective M.subtype_injective

theorem sylowImage_eq_bot_iff {G : Type*} [Group G] (M : Subgroup G) (T : Sylow 2 M) :
    sylowImage M T = ⊥ ↔ (T : Subgroup M) = ⊥ :=
  Subgroup.map_eq_bot_iff_of_injective _ M.subtype_injective

theorem overlap_sylow_le_normalizer {G : Type*} [Group G]
    (Q : Subgroup G) (g : G)
    (T : Sylow 2 ↥(rightConjugate Q g ⊓ Subgroup.normalizer (Q : Set G))) :
    sylowImage _ T ≤ Subgroup.normalizer (Q : Set G) :=
  (sylowImage_le _ T).trans inf_le_right

theorem overlap_sylow_le_conjugate {G : Type*} [Group G]
    (Q : Subgroup G) (g : G)
    (T : Sylow 2 ↥(rightConjugate Q g ⊓ Subgroup.normalizer (Q : Set G))) :
    sylowImage _ T ≤ rightConjugate Q g :=
  (sylowImage_le _ T).trans inf_le_left

theorem overlap_sylow_inf_eq_bot {G : Type*} [Group G] [Finite G]
    (Q : Subgroup G) (htight : TightlyEmbedded Q) (g : G)
    (hg : g ∉ Subgroup.normalizer (Q : Set G))
    (T : Sylow 2 ↥(rightConjugate Q g ⊓ Subgroup.normalizer (Q : Set G))) :
    sylowImage _ T ⊓ Q = ⊥ :=
  two_subgroup_inf_conjugate_eq_bot Q _ htight (sylowImage_isPGroup _ T) g hg
    (overlap_sylow_le_conjugate Q g T)

theorem overlap_product_le_normalizer {G : Type*} [Group G]
    (Q : Subgroup G) (g : G)
    (T : Sylow 2 ↥(rightConjugate Q g ⊓ Subgroup.normalizer (Q : Set G))) :
    Q ⊔ sylowImage _ T ≤ Subgroup.normalizer (Q : Set G) :=
  sup_le Subgroup.le_normalizer (overlap_sylow_le_normalizer Q g T)

theorem normal_in_overlap_product {G : Type*} [Group G]
    (Q : Subgroup G) (g : G)
    (T : Sylow 2 ↥(rightConjugate Q g ⊓ Subgroup.normalizer (Q : Set G))) :
    (Q.subgroupOf (Q ⊔ sylowImage _ T)).Normal :=
  Subgroup.normal_subgroupOf_of_le_normalizer (overlap_product_le_normalizer Q g T)

theorem overlap_product_coordinates {G : Type*} [Group G]
    (Q : Subgroup G) (g : G)
    (T : Sylow 2 ↥(rightConjugate Q g ⊓ Subgroup.normalizer (Q : Set G)))
    (x : G) (hx : x ∈ Q ⊔ sylowImage _ T) :
    ∃ q ∈ Q, ∃ t ∈ sylowImage _ T, q * t = x :=
  NormalizedProduct.coordinates Q _ (overlap_sylow_le_normalizer Q g T) x hx

end CFSG.ComponentClassification.AschbacherTightEmbedding
