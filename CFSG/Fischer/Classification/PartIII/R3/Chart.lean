module

public import CFSG.Fischer.Uniq.MuSets

public section

namespace CFSG.Fischer.Classification.LocalR3

open CFSG.Blueprint.Fischer CFSG.Fischer

variable {X Y Z : Type} [Group X] [Group Y] [Group Z]

@[expose] def IsAdm (E S : Set X) : Prop :=
  S ⊆ E ∧ ∀ g ∈ S, ∃ q ∈ E, q * g ≠ g * q ∧ S ∩ LocalClass E g = muSet E g q

structure IsChart (c : X → Y) (A : Set X) (F : Set Y) : Prop where
  injOn : Set.InjOn c A
  image_eq : c '' A = F
  comm_iff : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a ↔ c a * c b = c b * c a

theorem localClass_subset (E : Set X) (g : X) : LocalClass E g ⊆ E :=
  fun _ h => h.1

theorem muSet_subset (E : Set X) (g q : X) : muSet E g q ⊆ E :=
  fun _ h => h.1.1

namespace IsChart

variable {c : X → Y} {A : Set X} {F : Set Y}

theorem mem (h : IsChart c A F) {a : X} (ha : a ∈ A) : c a ∈ F :=
  h.image_eq ▸ ⟨a, ha, rfl⟩

theorem exists_eq (h : IsChart c A F) {y : Y} (hy : y ∈ F) : ∃ a ∈ A, c a = y := by
  rw [← h.image_eq] at hy
  exact hy

theorem image_subset (h : IsChart c A F) {S : Set X} (hS : S ⊆ A) : c '' S ⊆ F :=
  h.image_eq ▸ Set.image_mono hS

theorem mem_localClass_iff (h : IsChart c A F) {a g : X} (ha : a ∈ A) (hg : g ∈ A) :
    c a ∈ LocalClass F (c g) ↔ a ∈ LocalClass A g := by
  simp only [mem_localClass, h.injOn.ne_iff ha hg, ← h.comm_iff a ha g hg, h.mem ha, ha,
    true_and]

theorem image_localClass (h : IsChart c A F) {g : X} (hg : g ∈ A) :
    c '' LocalClass A g = LocalClass F (c g) := by
  ext y
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact (h.mem_localClass_iff ha.1 hg).2 ha
  · intro hy
    obtain ⟨a, ha, rfl⟩ := h.exists_eq hy.1
    exact ⟨a, (h.mem_localClass_iff ha hg).1 hy, rfl⟩

theorem image_inter (h : IsChart c A F) {S T : Set X} (hS : S ⊆ A) (hT : T ⊆ A) :
    c '' (S ∩ T) = c '' S ∩ c '' T :=
  h.injOn.image_inter hS hT

theorem image_muSet (h : IsChart c A F) {g q : X} (hg : g ∈ A) (hq : q ∈ A) :
    c '' muSet A g q = muSet F (c g) (c q) := by
  rw [muSet, h.image_inter (localClass_subset A g) (localClass_subset A q),
    h.image_localClass hg, h.image_localClass hq]
  rfl

theorem image_eq_image_iff (h : IsChart c A F) {S T : Set X} (hS : S ⊆ A) (hT : T ⊆ A) :
    c '' S = c '' T ↔ S = T :=
  h.injOn.image_eq_image_iff hS hT

theorem isAdm_image_iff (h : IsChart c A F) {S : Set X} (hS : S ⊆ A) :
    IsAdm F (c '' S) ↔ IsAdm A S := by
  have key : ∀ g ∈ S, ∀ q ∈ A, c '' S ∩ LocalClass F (c g) = muSet F (c g) (c q) ↔
      S ∩ LocalClass A g = muSet A g q := fun g hg q hq => by
    rw [← h.image_localClass (hS hg), ← h.image_muSet (hS hg) hq,
      ← h.image_inter hS (localClass_subset A g),
      h.image_eq_image_iff (Set.inter_subset_left.trans hS) (muSet_subset A g q)]
  constructor
  · rintro ⟨-, hadm⟩
    refine ⟨hS, fun g hg => ?_⟩
    obtain ⟨q', hq', hqg, hμ⟩ := hadm (c g) ⟨g, hg, rfl⟩
    obtain ⟨q, hq, rfl⟩ := h.exists_eq hq'
    exact ⟨q, hq, fun e => hqg ((h.comm_iff q hq g (hS hg)).1 e), (key g hg q hq).1 hμ⟩
  · rintro ⟨-, hadm⟩
    refine ⟨h.image_subset hS, ?_⟩
    rintro _ ⟨g, hg, rfl⟩
    obtain ⟨q, hq, hqg, hμ⟩ := hadm g hg
    exact ⟨c q, h.mem hq, fun e => hqg ((h.comm_iff q hq g (hS hg)).2 e), (key g hg q hq).2 hμ⟩

theorem comp {c' : Y → Z} {F' : Set Z} (h : IsChart c A F) (h' : IsChart c' F F') :
    IsChart (c' ∘ c) A F' where
  injOn := h'.injOn.comp h.injOn fun _ ha => h.mem ha
  image_eq := by rw [Set.image_comp, h.image_eq, h'.image_eq]
  comm_iff a ha b hb := (h.comm_iff a ha b hb).trans (h'.comm_iff _ (h.mem ha) _ (h.mem hb))

theorem mono (h : IsChart c A F) {A' : Set X} (hA : A' ⊆ A) : IsChart c A' (c '' A') where
  injOn := h.injOn.mono hA
  image_eq := rfl
  comm_iff a ha b hb := h.comm_iff a (hA ha) b (hA hb)

theorem localClass (h : IsChart c A F) {g : X} (hg : g ∈ A) :
    IsChart c (LocalClass A g) (LocalClass F (c g)) :=
  h.image_localClass hg ▸ h.mono (localClass_subset A g)

end IsChart

theorem isChart_mulEquiv (ψ : X ≃* Y) (A : Set X) : IsChart ψ A (ψ '' A) where
  injOn := ψ.injective.injOn
  image_eq := rfl
  comm_iff a _ b _ := by rw [← map_mul, ← map_mul, ψ.injective.eq_iff]

variable {E : Set X}

@[expose] noncomputable def lqMap (E : Set X) (d : X) (g : X) : LocalQuotient E d :=
  open Classical in
  if h : g ∈ LocalGroup E d then QuotientGroup.mk (⟨g, h⟩ : LocalGroup E d) else 1

theorem lqMap_of_mem {d g : X} (hg : g ∈ LocalClass E d) :
    lqMap E d g = starImage E d ⟨g, hg⟩ := by
  simp only [lqMap, mem_localGroup hg, ↓reduceDIte]
  rfl

theorem lqMap_image {d : X} {S : Set X} (hS : S ⊆ LocalClass E d) :
    lqMap E d '' S = starImage E d '' {f | (f : X) ∈ S} := by
  ext q
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact ⟨⟨g, hS hg⟩, hg, (lqMap_of_mem (hS hg)).symm⟩
  · rintro ⟨f, hf, rfl⟩
    exact ⟨f, hf, lqMap_of_mem f.2⟩

theorem Pair.isChart_lqMap (hP : Pair X E) {d : X} (hi : Function.Injective (starImage E d)) :
    IsChart (lqMap E d) (LocalClass E d) (LocalImages E d) where
  injOn a ha b hb hab := by
    rw [lqMap_of_mem ha, lqMap_of_mem hb] at hab
    exact congrArg Subtype.val (hi hab)
  image_eq := by
    rw [lqMap_image subset_rfl, ← range_starImage, ← Set.image_univ]
    congr 1
    exact Set.eq_univ_of_forall fun f => f.2
  comm_iff a ha b hb := by
    rw [lqMap_of_mem ha, lqMap_of_mem hb, ← commute_iff_eq, ← commute_iff_eq]
    exact (Pair.starImage_commute_iff hP ⟨a, ha⟩ ⟨b, hb⟩).symm

end CFSG.Fischer.Classification.LocalR3
