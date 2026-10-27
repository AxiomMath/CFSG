module

public import CFSG.LieType.AlgebraicGroups.ToralRootCoverWords
public import CFSG.LieType.AlgebraicGroups.HopfTensorPoints
import CFSG.LieType.AlgebraicGroups.ConvolutionPoints

public noncomputable section

namespace CFSG.LieType.AlgebraicGroups

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley WithConv TensorProduct
open scoped Pointwise

open scoped CFSG.ConvolutionPoints

variable {τ : Tag} {k : Type} [Field k]

theorem mapWord_mapWord {R S T : Type} [CommRing R] [CommRing S] [CommRing T] (f : R →+* S)
    (g : S →+* T) (w : List (Letter τ × R)) :
    mapWord g (mapWord f w) = mapWord (g.comp f) w := by
  simp [mapWord, List.map_map, Function.comp_def]

variable (τ k) in
structure WordCurve where
  D : Type
  [commRing : CommRing D]
  [algebra : Algebra k D]
  [finiteType : Algebra.FiniteType k D]
  [isDomain : IsDomain D]
  word : List (Letter τ × D)
  base : D →ₐ[k] k
  base_eq : wordUnit τ k (mapWord (base : D →+* k) word) = 1

attribute [instance] WordCurve.commRing WordCurve.algebra WordCurve.finiteType WordCurve.isDomain

namespace WordCurve

@[expose] def values
    (F : WordCurve τ k) : Set (ModGL τ k) :=
  Set.range fun z : F.D →ₐ[k] k => wordUnit τ k (mapWord (z : F.D →+* k) F.word)

theorem one_mem_values
    (F : WordCurve τ k) : (1 : ModGL τ k) ∈ F.values :=
  ⟨F.base, F.base_eq⟩

@[expose] def ofWord
    (D : Type) [CommRing D] [Algebra k D] [Algebra.FiniteType k D] [IsDomain D]
    (word : List (Letter τ × D)) (base : D →ₐ[k] k)
    (h : wordUnit τ k (mapWord (base : D →+* k) word) = 1) : WordCurve τ k :=
  ⟨D, word, base, h⟩

theorem values_ofWord
    (D : Type) [CommRing D] [Algebra k D] [Algebra.FiniteType k D]
    [IsDomain D] (word : List (Letter τ × D)) (base : D →ₐ[k] k)
    (h : wordUnit τ k (mapWord (base : D →+* k) word) = 1) :
    (ofWord D word base h).values =
      Set.range fun z : D →ₐ[k] k => wordUnit τ k (mapWord (z : D →+* k) word) :=
  rfl

variable (τ k) in
@[expose] def unit : WordCurve τ k where
  D := k
  word := []
  base := AlgHom.id k k
  base_eq := wordUnit_nil

theorem values_unit
    : (unit τ k).values = {1} := by
  ext g
  constructor
  · rintro ⟨z, rfl⟩
    exact wordUnit_nil
  · rintro rfl
    exact ⟨AlgHom.id k k, wordUnit_nil⟩

variable [IsAlgClosed k]

@[expose] def mul
    (F G : WordCurve τ k) : WordCurve τ k where
  D := F.D ⊗[k] G.D
  isDomain := isDomain_tensorProduct k F.D G.D
  word := mapWord ((Algebra.TensorProduct.includeLeft : F.D →ₐ[k] F.D ⊗[k] G.D) :
      F.D →+* F.D ⊗[k] G.D) F.word ++
    mapWord ((Algebra.TensorProduct.includeRight : G.D →ₐ[k] F.D ⊗[k] G.D) :
      G.D →+* F.D ⊗[k] G.D) G.word
  base := Algebra.TensorProduct.productMap F.base G.base
  base_eq := by
    rw [mapWord_append, mapWord_mapWord, mapWord_mapWord, wordUnit_append, ← AlgHom.comp_toRingHom,
      ← AlgHom.comp_toRingHom, Algebra.TensorProduct.productMap_left,
      Algebra.TensorProduct.productMap_right, F.base_eq, G.base_eq, mul_one]

theorem wordUnit_mul_word
    (F G : WordCurve τ k) (z : F.D ⊗[k] G.D →ₐ[k] k) :
    wordUnit τ k (mapWord (z : F.D ⊗[k] G.D →+* k) (mul F G).word) =
      wordUnit τ k (mapWord ((z.comp Algebra.TensorProduct.includeLeft : F.D →ₐ[k] k) :
        F.D →+* k) F.word) *
      wordUnit τ k (mapWord ((z.comp Algebra.TensorProduct.includeRight : G.D →ₐ[k] k) :
        G.D →+* k) G.word) := by
  show wordUnit τ k (mapWord _ (mapWord _ F.word ++ mapWord _ G.word)) = _
  rw [mapWord_append, mapWord_mapWord, mapWord_mapWord, wordUnit_append]
  rfl

theorem values_mul
    (F G : WordCurve τ k) : (mul F G).values = F.values * G.values := by
  ext g
  constructor
  · rintro ⟨z, rfl⟩
    exact Set.mem_mul.2 ⟨_, ⟨z.comp Algebra.TensorProduct.includeLeft, rfl⟩, _,
      ⟨z.comp Algebra.TensorProduct.includeRight, rfl⟩, (wordUnit_mul_word F G z).symm⟩
  · intro hg
    obtain ⟨_, ⟨z₁, rfl⟩, _, ⟨z₂, rfl⟩, rfl⟩ := Set.mem_mul.1 hg
    refine ⟨Algebra.TensorProduct.productMap z₁ z₂,
      (wordUnit_mul_word F G (Algebra.TensorProduct.productMap z₁ z₂)).trans ?_⟩
    rw [Algebra.TensorProduct.productMap_left, Algebra.TensorProduct.productMap_right]

@[expose] def listProd
    {ι : Type} (F : ι → WordCurve τ k) : List ι → WordCurve τ k
  | [] => unit τ k
  | i :: l => mul (F i) (listProd F l)

theorem values_listProd_nil
    {ι : Type} (F : ι → WordCurve τ k) :
    (listProd F []).values = {1} :=
  values_unit

theorem values_listProd_cons
    {ι : Type} (F : ι → WordCurve τ k) (i : ι) (l : List ι) :
    (listProd F (i :: l)).values = (F i).values * (listProd F l).values :=
  values_mul _ _

theorem values_listProd_append
    {ι : Type} (F : ι → WordCurve τ k) (l₁ l₂ : List ι) :
    (listProd F (l₁ ++ l₂)).values = (listProd F l₁).values * (listProd F l₂).values := by
  induction l₁ with
  | nil => rw [List.nil_append, values_listProd_nil, Set.singleton_one, one_mul]
  | cons i l ih => rw [List.cons_append, values_listProd_cons, values_listProd_cons, ih, mul_assoc]

theorem values_listProd_singleton
    {ι : Type} (F : ι → WordCurve τ k) (i : ι) :
    (listProd F [i]).values = (F i).values := by
  rw [values_listProd_cons, values_listProd_nil, Set.singleton_one, mul_one]

end WordCurve

variable [IsAlgClosed k]

open WordCurve in
theorem isPointIrreducible_iSup_wordCurves
    {ι : Type} (F : ι → WordCurve τ k)
    (H : ι → Subgroup (ModGL τ k)) (hFH : ∀ i, (F i).values = (H i : Set (ModGL τ k))) :
    IsPointIrreducible k
      (transportPoints (modGLPoint τ k) ((⨆ i, H i : Subgroup (ModGL τ k)) : Set (ModGL τ k))) := by
  have hone : ∀ l, (1 : ModGL τ k) ∈ (listProd F l).values := fun l => one_mem_values _
  have hsub : ∀ l, (listProd F l).values ⊆
      ((⨆ i, H i : Subgroup (ModGL τ k)) : Set (ModGL τ k)) := by
    intro l
    induction l with
    | nil =>
      intro g hg
      rw [values_listProd_nil, Set.mem_singleton_iff] at hg
      rw [hg]
      exact one_mem _
    | cons i l ih =>
      intro g hg
      rw [values_listProd_cons] at hg
      obtain ⟨a, ha, b, hb, rfl⟩ := Set.mem_mul.1 hg
      rw [hFH] at ha
      exact mul_mem (Subgroup.mem_iSup_of_mem i ha) (ih hb)
  have hinv : ∀ l, ∀ g ∈ (listProd F l).values, g⁻¹ ∈ (listProd F l.reverse).values := by
    intro l
    induction l with
    | nil =>
      intro g hg
      rw [values_listProd_nil, Set.mem_singleton_iff] at hg
      rw [hg, inv_one]
      exact hone _
    | cons i l ih =>
      intro g hg
      rw [values_listProd_cons] at hg
      obtain ⟨a, ha, b, hb, rfl⟩ := Set.mem_mul.1 hg
      rw [mul_inv_rev, List.reverse_cons, values_listProd_append, values_listProd_singleton]
      refine Set.mem_mul.2 ⟨b⁻¹, ih b hb, a⁻¹, ?_, rfl⟩
      rw [hFH] at ha ⊢
      exact inv_mem ha
  let U : Subgroup (ModGL τ k) :=
    { carrier := ⋃ l, (listProd F l).values
      mul_mem' := by
        intro a b ha hb
        obtain ⟨l₁, ha⟩ := Set.mem_iUnion.1 ha
        obtain ⟨l₂, hb⟩ := Set.mem_iUnion.1 hb
        refine Set.mem_iUnion.2 ⟨l₁ ++ l₂, ?_⟩
        rw [values_listProd_append]
        exact Set.mem_mul.2 ⟨a, ha, b, hb, rfl⟩
      one_mem' := Set.mem_iUnion.2 ⟨[], hone []⟩
      inv_mem' := by
        intro a ha
        obtain ⟨l, ha⟩ := Set.mem_iUnion.1 ha
        exact Set.mem_iUnion.2 ⟨l.reverse, hinv l a ha⟩ }
  have hU : ((⨆ i, H i : Subgroup (ModGL τ k)) : Set (ModGL τ k)) =
      ⋃ l, (listProd F l).values := by
    refine le_antisymm ?_ (Set.iUnion_subset hsub)
    have hle : (⨆ i, H i : Subgroup (ModGL τ k)) ≤ U := iSup_le fun i g hg => by
      refine Set.mem_iUnion.2 ⟨[i], ?_⟩
      rw [values_listProd_singleton, hFH]
      exact hg
    exact hle
  rw [hU, transportPoints, Set.image_iUnion]
  have : Nonempty (List ι) := ⟨[]⟩
  refine isPointIrreducible_iUnion_of_directed _ (fun l => ?_) fun l₁ l₂ => ⟨l₁ ++ l₂, ?_, ?_⟩
  · have h : (fun g : ModGL τ k => (modGLPoint τ k g).ofConv) '' (listProd F l).values =
        Set.range fun z : (listProd F l).D →ₐ[k] k =>
          z.comp (unitCo k (wordUnit τ _ (listProd F l).word)) := by
      ext y
      constructor
      · rintro ⟨_, ⟨z, rfl⟩, rfl⟩
        exact ⟨z, comp_unitCo_wordUnit z _⟩
      · rintro ⟨z, rfl⟩
        exact ⟨_, ⟨z, rfl⟩, (comp_unitCo_wordUnit z _).symm⟩
    rw [h]
    exact isPointIrreducible_range_of_isDomain _
  · refine Set.image_mono fun g hg => ?_
    rw [values_listProd_append]
    exact Set.mem_mul.2 ⟨g, hg, 1, hone l₂, mul_one g⟩
  · refine Set.image_mono fun g hg => ?_
    rw [values_listProd_append]
    exact Set.mem_mul.2 ⟨1, hone l₁, g, hg, one_mul g⟩

end CFSG.LieType.AlgebraicGroups
