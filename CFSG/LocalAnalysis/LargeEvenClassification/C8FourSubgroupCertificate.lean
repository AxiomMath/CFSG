module

public import CFSG.LocalAnalysis.LargeEvenClassification.C8FourAutomorphisms
public import CFSG.LocalAnalysis.LargeEvenClassification.FrattiniExact

public section

namespace CFSG.LargeEvenClassification.Helpers

instance c8FourCodeInhabited : Inhabited C8FourCode := ⟨1⟩

@[expose] def c8FourCertificateProduct (g h : C8FourCode) : C8FourCode := c8FourMultiply g h

@[expose] def c8FourCertificateInverse (g : C8FourCode) : C8FourCode := c8FourInverse g

@[expose] def certificateListAll {α : Type*} : List α → (α → Prop) → Prop
  | [], _ => True
  | x :: xs, p => p x ∧ certificateListAll xs p

instance certificateListAll_decidable {α : Type*} (xs : List α) (p : α → Prop)
    [DecidablePred p] : Decidable (certificateListAll xs p) := by
  induction xs with
  | nil => exact isTrue trivial
  | cons x xs ih => exact @instDecidableAnd (p x) (certificateListAll xs p) (inferInstance) ih

theorem certificateListAll_iff {α : Type*} (xs : List α) (p : α → Prop) :
    certificateListAll xs p ↔ ∀ x ∈ xs, p x := by
  induction xs with
  | nil => simp [certificateListAll]
  | cons x xs ih => simp [certificateListAll, ih]

@[expose] def c8FourDecodeWord : ℕ → ℕ → List ℕ
  | 0, _ => []
  | fuel + 1, word =>
      if word % 6 = 0 then [] else (word % 6 - 1) :: c8FourDecodeWord fuel (word / 6)

structure C8FourSubgroupRecord where
  mask : ℕ
  elements : List C8FourCode
  generators : List C8FourCode
  wordData : List (C8FourCode × ℕ × Fin 32)
  children : Array (Fin 896)

@[expose] def c8FourRecordMem (r : C8FourSubgroupRecord) (g : C8FourCode) : Prop :=
  r.mask.testBit g.index.val = true

instance c8FourRecordMem_decidable (r : C8FourSubgroupRecord) (g : C8FourCode) :
    Decidable (c8FourRecordMem r g) := inferInstanceAs (Decidable (r.mask.testBit g.index.val = true))

@[expose] def c8FourRecordWord (r : C8FourSubgroupRecord) (g : C8FourCode) : List ℕ :=
  c8FourDecodeWord 8 ((r.wordData.find? (fun entry => entry.1 = g)).getD (g, 0, 0)).2.1

@[expose] def c8FourRecordWordProduct (r : C8FourSubgroupRecord) (g : C8FourCode) : C8FourCode :=
  ((c8FourRecordWord r g).map (fun i => r.generators[i]!)).prod

@[expose] def c8FourWordVector (word : List ℕ) : Fin 32 :=
  Fin.ofNat 32 (word.foldl (fun value i => value ^^^ (2 ^ i)) 0)

@[expose] def c8FourVector (r : C8FourSubgroupRecord) (g : C8FourCode) : Fin 32 :=
  ((r.wordData.find? (fun entry => entry.1 = g)).getD (g, 0, 0)).2.2

@[expose] def c8FourRecordValid (r : C8FourSubgroupRecord) : Prop :=
  (∀ g : C8FourCode, c8FourRecordMem r g ↔ g ∈ r.elements) ∧
  c8FourRecordMem r 1 ∧
  certificateListAll r.elements (fun g =>
    c8FourRecordMem r (c8FourCertificateInverse g) ∧ certificateListAll r.elements (fun h => c8FourRecordMem r (c8FourCertificateProduct g h))) ∧
  certificateListAll r.generators (c8FourRecordMem r) ∧
  certificateListAll r.elements (fun g =>
    c8FourRecordWordProduct r g = g ∧
    certificateListAll (c8FourRecordWord r g) (fun i => i < r.generators.length) ∧
    c8FourWordVector (c8FourRecordWord r g) = c8FourVector r g) ∧
  c8FourVector r 1 = 0 ∧
  certificateListAll r.elements (fun g => certificateListAll r.elements (fun h =>
    c8FourVector r (c8FourCertificateProduct g h) = Fin.ofNat 32 ((c8FourVector r g).val ^^^ (c8FourVector r h).val))) ∧
  r.generators.length ≤ 5

instance c8FourRecordValid_decidable (r : C8FourSubgroupRecord) : Decidable (c8FourRecordValid r) :=
  inferInstanceAs (Decidable (
    (∀ g : C8FourCode, c8FourRecordMem r g ↔ g ∈ r.elements) ∧
    c8FourRecordMem r 1 ∧
    certificateListAll r.elements (fun g =>
      c8FourRecordMem r (c8FourCertificateInverse g) ∧ certificateListAll r.elements (fun h => c8FourRecordMem r (c8FourCertificateProduct g h))) ∧
    certificateListAll r.generators (c8FourRecordMem r) ∧
    certificateListAll r.elements (fun g =>
      c8FourRecordWordProduct r g = g ∧
      certificateListAll (c8FourRecordWord r g) (fun i => i < r.generators.length) ∧
      c8FourWordVector (c8FourRecordWord r g) = c8FourVector r g) ∧
    c8FourVector r 1 = 0 ∧
    certificateListAll r.elements (fun g => certificateListAll r.elements (fun h =>
      c8FourVector r (c8FourCertificateProduct g h) = Fin.ofNat 32 ((c8FourVector r g).val ^^^ (c8FourVector r h).val))) ∧
    r.generators.length ≤ 5))

@[expose] def c8FourRecordSubgroup (r : C8FourSubgroupRecord) (hr : c8FourRecordValid r) :
    Subgroup C8FourCode where
  carrier := {g | c8FourRecordMem r g}
  one_mem' := hr.2.1
  inv_mem' := by
    intro g hg
    exact ((certificateListAll_iff _ _).mp hr.2.2.1 g ((hr.1 g).mp hg)).1
  mul_mem' := by
    intro g h hg hh
    exact (certificateListAll_iff _ _).mp
      (((certificateListAll_iff _ _).mp hr.2.2.1 g ((hr.1 g).mp hg)).2) h ((hr.1 h).mp hh)

theorem c8FourRecord_generates (r : C8FourSubgroupRecord) (hr : c8FourRecordValid r) :
    Subgroup.closure (r.generators.toFinset : Set C8FourCode) = c8FourRecordSubgroup r hr := by
  classical
  let H := c8FourRecordSubgroup r hr
  have hgenerators : ∀ g ∈ r.generators, g ∈ H :=
    (certificateListAll_iff _ _).mp hr.2.2.2.1
  apply le_antisymm
  · apply (Subgroup.closure_le _).mpr
    intro g hg
    exact hgenerators g (List.mem_toFinset.mp hg)
  · intro g hg
    have hword := (certificateListAll_iff _ _).mp hr.2.2.2.2.1 g ((hr.1 g).mp hg)
    rw [← hword.1]
    change ((c8FourRecordWord r g).map (fun i => r.generators[i]!)).prod ∈ _
    apply (Subgroup.closure (r.generators.toFinset : Set C8FourCode)).list_prod_mem
    intro x hx
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
    apply Subgroup.subset_closure
    have hiLt := (certificateListAll_iff _ _).mp hword.2.1 i hi
    rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hiLt, Option.getD_some]
    exact List.mem_toFinset.mpr (List.getElem_mem hiLt)

theorem c8FourRecord_generator_rank_le (r : C8FourSubgroupRecord) (hr : c8FourRecordValid r) :
    pGeneratorRank 2 (c8FourRecordSubgroup r hr) ≤ r.generators.length := by
  classical
  let H := c8FourRecordSubgroup r hr
  let embedding : r.generators.toFinset ↪ H := {
    toFun := fun g => ⟨g.val, by
      exact ((certificateListAll_iff _ _).mp hr.2.2.2.1) g.val (List.mem_toFinset.mp g.property)⟩
    inj' := fun _ _ h => Subtype.ext (congrArg (fun x : H => x.val) h) }
  let X : Finset H := r.generators.toFinset.attach.map embedding
  have hgenerates : Subgroup.closure (X : Set H) = ⊤ := by
    apply (Subgroup.map_injective (f := H.subtype) Subtype.val_injective)
    rw [MonoidHom.map_closure, Subgroup.map_top]
    have himage : H.subtype '' (X : Set H) = (r.generators.toFinset : Set C8FourCode) := by
      ext g
      simp only [X, Finset.coe_map, Finset.coe_attach, Set.mem_image]
      constructor
      · rintro ⟨h, ⟨x, _, rfl⟩, rfl⟩
        exact x.property
      · intro hg
        exact ⟨⟨g, ((certificateListAll_iff _ _).mp hr.2.2.2.1) g (List.mem_toFinset.mp hg)⟩,
          ⟨⟨g, hg⟩, Set.mem_univ _, rfl⟩, rfl⟩
    rw [himage, c8FourRecord_generates]
    exact H.range_subtype.symm
  have hbound := pGeneratorRank_le_generators Nat.prime_two (c8Four_code_isPGroup.to_subgroup H) X hgenerates
  have hcard : X.card ≤ r.generators.length := by
    rw [Finset.card_map, Finset.card_attach]
    exact List.toFinset_card_le _
  exact hbound.trans hcard

theorem c8FourRecord_hom_ext {T : Type*} [Group T]
    (r : C8FourSubgroupRecord) (hr : c8FourRecordValid r)
    (f g : c8FourRecordSubgroup r hr →* T)
    (heq : ∀ x : c8FourRecordSubgroup r hr, x.val ∈ r.generators → f x = g x) : f = g := by
  let H := c8FourRecordSubgroup r hr
  apply MonoidHom.ext
  intro x
  have hx : x.val ∈ Subgroup.closure (r.generators.toFinset : Set C8FourCode) :=
    (c8FourRecord_generates r hr).symm ▸ x.property
  have hproof : ∀ y : C8FourCode, (hy : y ∈ Subgroup.closure (r.generators.toFinset : Set C8FourCode)) →
      ∀ hyH : y ∈ H, f ⟨y, hyH⟩ = g ⟨y, hyH⟩ := by
    intro y hy
    induction hy using Subgroup.closure_induction with
    | mem y hy =>
      intro hyH
      exact heq ⟨y, hyH⟩ (List.mem_toFinset.mp hy)
    | one =>
      intro hOne
      change f 1 = g 1
      rw [map_one, map_one]
    | mul y z hy hz ihy ihz =>
      intro hyzH
      have hyH : y ∈ H := (c8FourRecord_generates r hr).le hy
      have hzH : z ∈ H := (c8FourRecord_generates r hr).le hz
      change f (⟨y, hyH⟩ * ⟨z, hzH⟩) = g (⟨y, hyH⟩ * ⟨z, hzH⟩)
      rw [map_mul, map_mul, ihy hyH, ihz hzH]
    | inv y hy ih =>
      intro hInv
      have hyH : y ∈ H := (c8FourRecord_generates r hr).le hy
      change f (⟨y, hyH⟩⁻¹) = g (⟨y, hyH⟩⁻¹)
      rw [map_inv, map_inv, ih hyH]
  exact hproof x.val hx x.property

end CFSG.LargeEvenClassification.Helpers
