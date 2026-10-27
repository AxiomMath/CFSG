module

public import CFSG.LieType.AlgebraicGroups.RootWordRegular
public import CFSG.LieType.Chevalley.BruhatCellFactorization
public import Mathlib.GroupTheory.NoncommPiCoprod
public import CFSG.LieType.AlgebraicGroups.HopfTensorPoints

public noncomputable section

namespace CFSG.LieType.AlgebraicGroups

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint WithConv
open TensorProduct
open scoped Pointwise

variable {τ : Tag} {k : Type} [Field k]

variable (τ k) in
@[expose] def torusProdHom
    : (Fin τ.rank → kˣ) →* ModGL τ k :=
  MonoidHom.noncommPiCoprod (fun i => torusEltHom τ k i)
    (show Pairwise fun i j => ∀ (x y : kˣ), Commute (torusEltHom τ k i x) (torusEltHom τ k j y)
      from fun i j _ t u => torusElt_mul_comm i j t u)

theorem torusProdHom_apply
    (t : Fin τ.rank → kˣ) :
    torusProdHom τ k t = (List.ofFn fun i => torusElt τ k i (t i)).prod := by
  simp only [torusProdHom, MonoidHom.noncommPiCoprod_apply, Finset.noncommProd, Fin.univ_val_map,
    Multiset.noncommProd_coe]
  rfl

theorem range_torusProdHom
    : (torusProdHom τ k).range = torusGroup τ k := by
  rw [torusProdHom, MonoidHom.noncommPiCoprod_range]
  apply le_antisymm
  · refine iSup_le fun i => ?_
    rintro _ ⟨t, rfl⟩
    exact torusElt_mem_torusGroup i t
  · show Subgroup.closure _ ≤ _
    refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨⟨i, t⟩, rfl⟩
    exact Subgroup.mem_iSup_of_mem i ⟨t, rfl⟩

variable (τ) in
@[expose] def bruhatWord
    (R : Type) [CommRing R] (w : WeylGroup τ) {N m : ℕ}
    (α : Fin N → Fin τ.rank → ℤ) (β : Fin m → Fin τ.rank → ℤ) (t : Fin τ.rank → Rˣ)
    (c : Fin N → R) (c' : Fin m → R) : List (Letter τ × R) :=
  (List.ofFn fun i => torusWord τ R i (t i)).flatten ++
    (List.ofFn fun j => pinnedWord τ R (α j) (c j)).flatten ++ canonicalWord τ R w ++
    (List.ofFn fun l => pinnedWord τ R (β l) (c' l)).flatten

section BruhatWord

variable
    {R S : Type} [CommRing R] [CommRing S] (w : WeylGroup τ) {N m : ℕ}
  (α : Fin N → Fin τ.rank → ℤ) (β : Fin m → Fin τ.rank → ℤ)

theorem wordUnit_bruhatWord
    (t : Fin τ.rank → Rˣ) (c : Fin N → R) (c' : Fin m → R) :
    wordUnit τ R (bruhatWord τ R w α β t c c') =
      (List.ofFn fun i => torusElt τ R i (t i)).prod *
        (List.ofFn fun j => pinnedX τ R (α j) (c j)).prod * canonicalRep (coxeterSystem τ) R w *
        (List.ofFn fun l => pinnedX τ R (β l) (c' l)).prod := by
  simp only [bruhatWord, wordUnit_append, wordUnit_flatten, List.map_ofFn, Function.comp_def,
    wordUnit_torusWord, wordUnit_pinnedWord, wordUnit_canonicalWord]

theorem mapWord_bruhatWord
    (f : R →+* S) (t : Fin τ.rank → Rˣ) (c : Fin N → R)
    (c' : Fin m → R) :
    mapWord f (bruhatWord τ R w α β t c c') =
      bruhatWord τ S w α β (fun i => Units.map f.toMonoidHom (t i)) (fun j => f (c j))
        (fun l => f (c' l)) := by
  simp only [bruhatWord, mapWord_append, mapWord_flatten, List.map_ofFn, Function.comp_def,
    mapWord_torusWord, mapWord_pinnedWord, mapWord_canonicalWord]

end BruhatWord

variable (τ k) in
@[expose] def bruhatParamWord
    (w : WeylGroup τ) {N m : ℕ} (α : Fin N → Fin τ.rank → ℤ)
    (β : Fin m → Fin τ.rank → ℤ) : List (Letter τ × TorusAffine k τ.rank (N + m)) :=
  bruhatWord τ (TorusAffine k τ.rank (N + m)) w α β (torusUnit k τ.rank (N + m))
    (fun j => affineCoord k τ.rank (N + m) (Fin.castAdd m j))
    (fun l => affineCoord k τ.rank (N + m) (Fin.natAdd N l))

variable (τ k) in
@[expose] def bruhatCo
    (w : WeylGroup τ) {N m : ℕ} (α : Fin N → Fin τ.rank → ℤ)
    (β : Fin m → Fin τ.rank → ℤ) : GLCoord k (Label τ) →ₐ[k] TorusAffine k τ.rank (N + m) :=
  unitCo k (wordUnit τ _ (bruhatParamWord τ k w α β))

theorem comp_unitCo_wordUnit
    {D : Type} [CommRing D] [Algebra k D] (z : D →ₐ[k] k)
    (w : List (Letter τ × D)) :
    z.comp (unitCo k (wordUnit τ D w)) =
      (modGLPoint τ k (wordUnit τ k (mapWord (z : D →+* k) w))).ofConv :=
  comp_unitCo_of_baseChange z _ _ (baseChange_wordUnit _ w)

theorem units_map_torusUnit {a b : ℕ} (t : Fin a → kˣ) (c : Fin b → k) (i : Fin a) :
    Units.map (torusAffinePoint t c : TorusAffine k a b →+* k).toMonoidHom
      (torusUnit k a b i) = t i :=
  Units.ext (by simp [coe_torusUnit])

theorem mapWord_bruhatParamWord
    (w : WeylGroup τ) {N m : ℕ} (α : Fin N → Fin τ.rank → ℤ)
    (β : Fin m → Fin τ.rank → ℤ) (t : Fin τ.rank → kˣ) (c : Fin (N + m) → k) :
    mapWord (torusAffinePoint t c : TorusAffine k τ.rank (N + m) →+* k)
        (bruhatParamWord τ k w α β) =
      bruhatWord τ k w α β t (fun j => c (Fin.castAdd m j)) (fun l => c (Fin.natAdd N l)) := by
  rw [bruhatParamWord, mapWord_bruhatWord]
  simp only [units_map_torusUnit]
  congr 1 <;> funext j <;> simp

theorem point_bruhatCo
    (w : WeylGroup τ) {N m : ℕ} (α : Fin N → Fin τ.rank → ℤ)
    (β : Fin m → Fin τ.rank → ℤ) (t : Fin τ.rank → kˣ) (c : Fin (N + m) → k) :
    (modGLPoint τ k).symm (toConv ((torusAffinePoint t c).comp (bruhatCo τ k w α β))) =
      (List.ofFn fun i => torusElt τ k i (t i)).prod *
        (List.ofFn fun j => pinnedX τ k (α j) (c (Fin.castAdd m j))).prod *
        canonicalRep (coxeterSystem τ) k w *
        (List.ofFn fun l => pinnedX τ k (β l) (c (Fin.natAdd N l))).prod := by
  rw [bruhatCo, comp_unitCo_wordUnit, toConv_ofConv, MulEquiv.symm_apply_apply,
    mapWord_bruhatParamWord, wordUnit_bruhatWord]

theorem range_bruhatCo
    (w : WeylGroup τ) {N m : ℕ} (α : Fin N → Fin τ.rank → ℤ)
    (hα : Function.Injective α) (hαr : Set.range α = {β | IsRoot τ β ∧ 0 < height β})
    (β : Fin m → Fin τ.rank → ℤ) (hβ : Function.Injective β)
    (hβr : Set.range β = inversionSet w) :
    Set.range (fun z : TorusAffine k τ.rank (N + m) →ₐ[k] k =>
      (modGLPoint τ k).symm (toConv (z.comp (bruhatCo τ k w α β)))) = bruhatCell τ k w := by
  obtain ⟨-, -, -, -, hHU, -⟩ := triangular_borel_structure.{0, 0} τ k
  have hpos := (positive_root_collection τ k).2 α hα hαr
  have hinv := (bruhat_cell_factorization τ k).2.1 w β hβ hβr
  have hcell := (bruhat_cell_factorization τ k).1 w
  ext x
  constructor
  · rintro ⟨z, rfl⟩
    obtain ⟨⟨t, c⟩, rfl⟩ := torusAffinePointEquiv.surjective z
    show (modGLPoint τ k).symm (toConv ((torusAffinePoint t c).comp (bruhatCo τ k w α β))) ∈
      bruhatCell τ k w
    rw [point_bruhatCo]
    have hh : (List.ofFn fun i => torusElt τ k i (t i)).prod ∈ torusGroup τ k := by
      rw [← torusProdHom_apply, ← range_torusProdHom]
      exact ⟨t, rfl⟩
    have hu := hpos.mapsTo (Set.mem_univ fun j => c (Fin.castAdd m j))
    have hu' := hinv.mapsTo (Set.mem_univ fun l => c (Fin.natAdd N l))
    have hb : (List.ofFn fun i => torusElt τ k i (t i)).prod *
        (List.ofFn fun j => pinnedX τ k (α j) (c (Fin.castAdd m j))).prod ∈ borelGroup τ k := by
      unfold borelGroup
      exact mul_mem (Subgroup.mem_sup_left hh) (Subgroup.mem_sup_right hu)
    exact hcell.mapsTo (Set.mk_mem_prod hb hu')
  · intro hx
    obtain ⟨⟨b, u'⟩, ⟨hb, hu'⟩, rfl⟩ := hcell.surjOn hx
    have hb' : b ∈ (torusGroup τ k : Set (ModGL τ k)) * (posUnipotent τ k : Set (ModGL τ k)) :=
      hHU ▸ hb
    obtain ⟨h, hh, u, hu, rfl⟩ := hb'
    have hh' : h ∈ (torusProdHom τ k).range := by
      rw [range_torusProdHom]
      exact hh
    obtain ⟨t, rfl⟩ := hh'
    obtain ⟨c₁, -, rfl⟩ := hpos.surjOn hu
    obtain ⟨c₂, -, rfl⟩ := hinv.surjOn hu'
    refine ⟨torusAffinePoint t (Fin.append c₁ c₂), ?_⟩
    simp only [point_bruhatCo, torusProdHom_apply, Fin.append_left, Fin.append_right]

theorem exists_enum {X : Type} {S : Set X} (hS : S.Finite) :
    ∃ (n : ℕ) (f : Fin n → X), Function.Injective f ∧ Set.range f = S := by
  classical
  let e := hS.toFinset.equivFin
  refine ⟨hS.toFinset.card, fun i => (e.symm i : X),
    fun i j h => e.symm.injective (Subtype.ext h), ?_⟩
  ext x
  constructor
  · rintro ⟨i, rfl⟩
    exact hS.mem_toFinset.1 (e.symm i).2
  · intro hx
    exact ⟨e ⟨x, hS.mem_toFinset.2 hx⟩, by simp⟩

theorem finite_posRoots
    (τ : Tag) : {β : Fin τ.rank → ℤ | IsRoot τ β ∧ 0 < height β}.Finite :=
  (finite_setOf_isRoot τ).subset fun _ h => h.1

@[expose] def invWord {R : Type} [CommRing R] (w : List (Letter τ × R)) : List (Letter τ × R) :=
  (w.map fun p => (p.1, -p.2)).reverse

theorem wordUnit_invWord
    {R : Type} [CommRing R] (w : List (Letter τ × R)) :
    wordUnit τ R (invWord w) = (wordUnit τ R w)⁻¹ := by
  induction w with
  | nil => simp [invWord, wordUnit]
  | cons p w ih =>
    rw [invWord, List.map_cons, List.reverse_cons, ← invWord, wordUnit_append, ih,
      show wordUnit τ R [(p.1, -p.2)] = (letterUnit τ R p.1 p.2)⁻¹ by
        rw [wordUnit_cons, wordUnit_nil, mul_one, letterUnit_neg],
      wordUnit_cons, mul_inv_rev]

theorem exists_wordElt_eq
    (g : adjointGroup τ k) : ∃ w : List (Letter τ × k), wordElt τ w = g := by
  suffices h : ∀ x : ModGL τ k, x ∈ adjointGroup τ k → ∃ w : List (Letter τ × k),
      wordUnit τ k w = x by
    obtain ⟨w, hw⟩ := h g g.2
    exact ⟨w, Subtype.ext (by rw [coe_wordElt, hw])⟩
  intro x hx
  unfold adjointGroup at hx
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨i, c, h | h⟩ := hx
    · exact ⟨[((i, true), c)], Units.ext (by simp [wordUnit, letterUnit, coe_xUnit, h])⟩
    · exact ⟨[((i, false), c)], Units.ext (by simp [wordUnit, letterUnit, coe_yUnit, h])⟩
  | one => exact ⟨[], rfl⟩
  | mul x y _ _ hx hy =>
    obtain ⟨w, rfl⟩ := hx
    obtain ⟨w', rfl⟩ := hy
    exact ⟨w ++ w', wordUnit_append w w'⟩
  | inv x _ hx =>
    obtain ⟨w, rfl⟩ := hx
    exact ⟨invWord w, wordUnit_invWord w⟩

@[expose] def freeWord {n : ℕ} (ℓ : Fin n → Letter τ) :
    List (Letter τ × MvPolynomial (Fin n) k) :=
  List.ofFn fun j => (ℓ j, MvPolynomial.X j)

theorem mapWord_freeWord {n : ℕ} (ℓ : Fin n → Letter τ) (z : MvPolynomial (Fin n) k →ₐ[k] k) :
    mapWord (z : MvPolynomial (Fin n) k →+* k) (freeWord (k := k) ℓ) =
      List.ofFn fun j => (ℓ j, z (MvPolynomial.X j)) := by
  simp [freeWord, mapWord, List.map_ofFn, Function.comp_def]

theorem wordElt_ofFn_zero
    {n : ℕ} (ℓ : Fin n → Letter τ) :
    wordElt τ (List.ofFn fun j => (ℓ j, (0 : k))) = 1 := by
  refine Subtype.ext ?_
  rw [coe_wordElt, Subgroup.coe_one, wordUnit, List.map_ofFn]
  refine List.prod_eq_one fun x hx => ?_
  obtain ⟨j, rfl⟩ := List.mem_ofFn.1 hx
  exact letterUnit_zero _

omit [Field k] in
theorem ofFn_append_pairs {n₁ n₂ : ℕ} (ℓ₁ : Fin n₁ → Letter τ) (ℓ₂ : Fin n₂ → Letter τ)
    (c₁ : Fin n₁ → k) (c₂ : Fin n₂ → k) :
    (List.ofFn fun j => (Fin.append ℓ₁ ℓ₂ j, Fin.append c₁ c₂ j)) =
      (List.ofFn fun j => (ℓ₁ j, c₁ j)) ++ List.ofFn fun j => (ℓ₂ j, c₂ j) := by
  rw [← List.ofFn_fin_append]
  congr 1
  funext j
  refine Fin.addCases (fun i => ?_) (fun i => ?_) j <;> simp

theorem isPointIrreducible_range_of_words
    [IsAlgClosed k] {A : Type} [CommRing A] [Algebra k A]
    (F : adjointGroup τ k → (A →ₐ[k] k))
    (co : ∀ {n : ℕ}, (Fin n → Letter τ) → (A →ₐ[k] MvPolynomial (Fin n) k))
    (hco : ∀ {n : ℕ} (ℓ : Fin n → Letter τ) (z : MvPolynomial (Fin n) k →ₐ[k] k),
      z.comp (co ℓ) = F (wordElt τ (List.ofFn fun j => (ℓ j, z (MvPolynomial.X j))))) :
    IsPointIrreducible k (Set.range F) := by
  classical
  let S : (Σ n, Fin n → Letter τ) → Set (A →ₐ[k] k) := fun p =>
    Set.range fun z : MvPolynomial (Fin p.1) k →ₐ[k] k => z.comp (co p.2)
  have hS : ∀ p, S p = Set.range fun c : Fin p.1 → k =>
      F (wordElt τ (List.ofFn fun j => (p.2 j, c j))) := by
    intro p
    ext y
    constructor
    · rintro ⟨z, rfl⟩
      exact ⟨fun j => z (MvPolynomial.X j), (hco p.2 z).symm⟩
    · rintro ⟨c, rfl⟩
      refine ⟨MvPolynomial.aeval c, ?_⟩
      show (MvPolynomial.aeval c).comp (co p.2) = _
      rw [hco]
      simp
  have hunion : Set.range F = ⋃ p, S p := by
    ext y
    constructor
    · rintro ⟨g, rfl⟩
      obtain ⟨w, rfl⟩ := exists_wordElt_eq g
      refine Set.mem_iUnion.2 ⟨⟨w.length, fun j => (w.get j).1⟩, ?_⟩
      rw [hS]
      refine ⟨fun j => (w.get j).2, ?_⟩
      simp only
      congr 2
      exact List.ofFn_get w
    · intro hy
      obtain ⟨p, hp⟩ := Set.mem_iUnion.1 hy
      rw [hS] at hp
      obtain ⟨c, rfl⟩ := hp
      exact ⟨_, rfl⟩
  rw [hunion]
  have : Nonempty (Σ n, Fin n → Letter τ) := ⟨⟨0, Fin.elim0⟩⟩
  refine isPointIrreducible_iUnion_of_directed S (fun p => ?_) fun p q => ?_
  · exact isPointIrreducible_range_of_isDomain (co p.2)
  · refine ⟨⟨p.1 + q.1, Fin.append p.2 q.2⟩, ?_, ?_⟩
    · rw [hS, hS]
      rintro _ ⟨c, rfl⟩
      refine ⟨Fin.append c 0, ?_⟩
      simp only
      rw [ofFn_append_pairs, wordElt, List.map_append, List.prod_append, ← wordElt, ← wordElt]
      simp only [Pi.zero_apply, wordElt_ofFn_zero, mul_one]
    · rw [hS, hS]
      rintro _ ⟨c, rfl⟩
      refine ⟨Fin.append 0 c, ?_⟩
      simp only
      rw [ofFn_append_pairs, wordElt, List.map_append, List.prod_append, ← wordElt, ← wordElt]
      simp only [Pi.zero_apply, wordElt_ofFn_zero, one_mul]

theorem isPointConstructible_range_of_cover [IsAlgClosed k] {A : Type} [CommRing A]
    [Algebra k A] [Algebra.FiniteType k A] (F : adjointGroup τ k → (A →ₐ[k] k)) {J : Type}
    [Finite J] (D : J → Type) [∀ j, CommRing (D j)] [∀ j, Algebra k (D j)]
    [∀ j, Algebra.FiniteType k (D j)] (co : ∀ j, A →ₐ[k] D j)
    (hco : ∀ j (z : D j →ₐ[k] k), ∃ g, z.comp (co j) = F g)
    (hcov : ∀ g, ∃ j, ∃ z : D j →ₐ[k] k, z.comp (co j) = F g) :
    IsPointConstructible k (Set.range F) := by
  have h := isPointConstructible_iUnion_range D co
  convert h using 1
  ext y
  simp only [Set.mem_range, Set.mem_iUnion]
  constructor
  · rintro ⟨g, rfl⟩
    exact hcov g
  · rintro ⟨j, z, rfl⟩
    exact (hco j z).imp fun g hg => hg.symm

variable (τ k) in
@[expose] def groupPoints : Set (GLCoord k (Label τ) →ₐ[k] k) :=
  {y | (modGLPoint τ k).symm (toConv y) ∈ adjointGroup τ k}

theorem groupPoints_eq_range :
    groupPoints τ k = Set.range fun g : adjointGroup τ k => (modGLPoint τ k g).ofConv := by
  ext y
  constructor
  · intro hy
    exact ⟨⟨_, hy⟩, by simp⟩
  · rintro ⟨g, rfl⟩
    simp [groupPoints]

variable (τ k) in
@[expose] def graphPoints
    {M : ℕ} (ψ : adjointGroup τ k →* Matrix.GeneralLinearGroup (Fin M) k) :
    Set (GLCoord k (Label τ) ⊗[k] GLCoord k (Fin M) →ₐ[k] k) :=
  Set.range fun g : adjointGroup τ k =>
    tensorPointEquiv ((modGLPoint τ k g).ofConv, (glPointEquiv (ψ g)).ofConv)

theorem comp_productMap {D B C : Type} [CommRing D] [Algebra k D] [CommRing B] [Algebra k B]
    [CommRing C] [Algebra k C] (z : D →ₐ[k] k) (f : B →ₐ[k] D) (g : C →ₐ[k] D) :
    z.comp (Algebra.TensorProduct.productMap f g) = tensorPointEquiv (z.comp f, z.comp g) := by
  apply Algebra.TensorProduct.ext'
  intro b c
  rw [tensorPointEquiv_tmul]
  simp

theorem exists_bruhatParam
    (g : adjointGroup τ k) {N : ℕ} (α : Fin N → Fin τ.rank → ℤ)
    (hα : Function.Injective α) (hαr : Set.range α = {β | IsRoot τ β ∧ 0 < height β})
    (m : WeylGroup τ → ℕ) (β : ∀ w, Fin (m w) → Fin τ.rank → ℤ)
    (hβ : ∀ w, Function.Injective (β w)) (hβr : ∀ w, Set.range (β w) = inversionSet w) :
    ∃ w, ∃ z : TorusAffine k τ.rank (N + m w) →ₐ[k] k,
      wordElt τ (mapWord (z : TorusAffine k τ.rank (N + m w) →+* k)
        (bruhatParamWord τ k w α (β w))) = g := by
  have hg : (g : ModGL τ k) ∈ ⋃ w, bruhatCell τ k w := by
    rw [← adjointGroup_eq_iUnion_bruhatCell]
    exact g.2
  obtain ⟨w, hw⟩ := Set.mem_iUnion.1 hg
  rw [← range_bruhatCo w α hα hαr (β w) (hβ w) (hβr w)] at hw
  obtain ⟨z, hz⟩ := hw
  simp only at hz
  refine ⟨w, z, Subtype.ext ?_⟩
  rw [coe_wordElt, ← hz, bruhatCo, comp_unitCo_wordUnit, toConv_ofConv,
    MulEquiv.symm_apply_apply]

theorem exceptional_Lang_rootword_Bruhat_regular_cover
    (τ : Tag) (k : Type) [Field k]
    [IsAlgClosed k] :
    (∀ (w : WeylGroup τ) {N m : ℕ} (α : Fin N → Fin τ.rank → ℤ), Function.Injective α →
      Set.range α = {β | IsRoot τ β ∧ 0 < height β} →
      ∀ β : Fin m → Fin τ.rank → ℤ, Function.Injective β → Set.range β = inversionSet w →
        (∀ (t : Fin τ.rank → kˣ) (c : Fin (N + m) → k),
          (modGLPoint τ k).symm (toConv ((torusAffinePoint t c).comp (bruhatCo τ k w α β))) =
            (List.ofFn fun i => torusElt τ k i (t i)).prod *
              (List.ofFn fun j => pinnedX τ k (α j) (c (Fin.castAdd m j))).prod *
              canonicalRep (coxeterSystem τ) k w *
              (List.ofFn fun l => pinnedX τ k (β l) (c (Fin.natAdd N l))).prod) ∧
        Set.range (fun z : TorusAffine k τ.rank (N + m) →ₐ[k] k =>
          (modGLPoint τ k).symm (toConv (z.comp (bruhatCo τ k w α β)))) = bruhatCell τ k w) ∧
    (⋃ w : WeylGroup τ, bruhatCell τ k w) = adjointGroup τ k ∧
    (∀ {N : ℕ} (α : Fin N → Fin τ.rank → ℤ), Function.Injective α →
      Set.range α = {β | IsRoot τ β ∧ 0 < height β} →
      ∀ (m : WeylGroup τ → ℕ) (β : ∀ w, Fin (m w) → Fin τ.rank → ℤ),
        (∀ w, Function.Injective (β w)) → (∀ w, Set.range (β w) = inversionSet w) →
          (⋃ w, Set.range fun z : TorusAffine k τ.rank (N + m w) →ₐ[k] k =>
            z.comp (bruhatCo τ k w α (β w))) = groupPoints τ k) ∧
    (∀ (M : ℕ) (ψ : adjointGroup τ k →* Matrix.GeneralLinearGroup (Fin M) k),
      (∀ i, ∃ φ : GLCoord k (Fin M) →ₐ[k] Polynomial k,
        ∀ c, toConv ((Polynomial.aeval c).comp φ) = glPointEquiv (ψ (adjX τ k i c))) →
      (∀ i, ∃ φ : GLCoord k (Fin M) →ₐ[k] Polynomial k,
        ∀ c, toConv ((Polynomial.aeval c).comp φ) = glPointEquiv (ψ (adjY τ k i c))) →
      ∃ ν : WeylGroup τ → ∀ {N m : ℕ}, (Fin N → Fin τ.rank → ℤ) →
          (Fin m → Fin τ.rank → ℤ) → (GLCoord k (Fin M) →ₐ[k] TorusAffine k τ.rank (N + m)),
        (∀ (w : WeylGroup τ) {N m : ℕ} (α : Fin N → Fin τ.rank → ℤ)
          (β : Fin m → Fin τ.rank → ℤ) (z : TorusAffine k τ.rank (N + m) →ₐ[k] k),
          ∃ g : adjointGroup τ k, toConv (z.comp (bruhatCo τ k w α β)) = modGLPoint τ k g ∧
            toConv (z.comp (ν w α β)) = glPointEquiv (ψ g)) ∧
        (∀ {N : ℕ} (α : Fin N → Fin τ.rank → ℤ), Function.Injective α →
          Set.range α = {β | IsRoot τ β ∧ 0 < height β} →
          ∀ (m : WeylGroup τ → ℕ) (β : ∀ w, Fin (m w) → Fin τ.rank → ℤ),
            (∀ w, Function.Injective (β w)) → (∀ w, Set.range (β w) = inversionSet w) →
              (⋃ w, Set.range fun z : TorusAffine k τ.rank (N + m w) →ₐ[k] k =>
                z.comp (Algebra.TensorProduct.productMap (bruhatCo τ k w α (β w))
                  (ν w α (β w)))) = graphPoints τ k ψ) ∧
        IsPointConstructible k (graphPoints τ k ψ) ∧ IsPointIrreducible k (graphPoints τ k ψ)) ∧
    IsPointConstructible k (groupPoints τ k) ∧ IsPointIrreducible k (groupPoints τ k) := by
  obtain ⟨N₀, α₀, hα₀, hα₀r⟩ := exists_enum (finite_posRoots τ)
  choose m₀ β₀ hβ₀ hβ₀r using fun w : WeylGroup τ => exists_enum (inversionSet_finite w)
  have hpt : ∀ (w : WeylGroup τ) {N m : ℕ} (α : Fin N → Fin τ.rank → ℤ)
      (β : Fin m → Fin τ.rank → ℤ) (z : TorusAffine k τ.rank (N + m) →ₐ[k] k),
      z.comp (bruhatCo τ k w α β) = (modGLPoint τ k (wordElt τ
        (mapWord (z : TorusAffine k τ.rank (N + m) →+* k)
          (bruhatParamWord τ k w α β)))).ofConv := by
    intro w N m α β z
    rw [bruhatCo, comp_unitCo_wordUnit, coe_wordElt]
  have hcovG : ∀ {N : ℕ} (α : Fin N → Fin τ.rank → ℤ), Function.Injective α →
      Set.range α = {β | IsRoot τ β ∧ 0 < height β} →
      ∀ (m : WeylGroup τ → ℕ) (β : ∀ w, Fin (m w) → Fin τ.rank → ℤ),
        (∀ w, Function.Injective (β w)) → (∀ w, Set.range (β w) = inversionSet w) →
          (⋃ w, Set.range fun z : TorusAffine k τ.rank (N + m w) →ₐ[k] k =>
            z.comp (bruhatCo τ k w α (β w))) = groupPoints τ k := by
    intro N α hα hαr m β hβ hβr
    rw [groupPoints_eq_range]
    ext y
    simp only [Set.mem_iUnion, Set.mem_range]
    constructor
    · rintro ⟨w, z, rfl⟩
      exact ⟨_, (hpt w α (β w) z).symm⟩
    · rintro ⟨g, rfl⟩
      obtain ⟨w, z, hz⟩ := exists_bruhatParam g α hα hαr m β hβ hβr
      exact ⟨w, z, by rw [hpt, hz]⟩
  refine ⟨fun w N m α hα hαr β hβ hβr => ⟨point_bruhatCo w α β, range_bruhatCo w α hα hαr β hβ hβr⟩,
    (adjointGroup_eq_iUnion_bruhatCell (τ := τ) (K := k)).symm, hcovG, ?_, ?_, ?_⟩
  ·
    intro M ψ hx hy
    choose φx hφx using hx
    choose φy hφy using hy
    let ν : WeylGroup τ → ∀ {N m : ℕ}, (Fin N → Fin τ.rank → ℤ) →
        (Fin m → Fin τ.rank → ℤ) → (GLCoord k (Fin M) →ₐ[k] TorusAffine k τ.rank (N + m)) :=
      fun w _ _ α β => (psiWordCo φx φy (bruhatParamWord τ k w α β)).ofConv
    have hν : ∀ (w : WeylGroup τ) {N m : ℕ} (α : Fin N → Fin τ.rank → ℤ)
        (β : Fin m → Fin τ.rank → ℤ) (z : TorusAffine k τ.rank (N + m) →ₐ[k] k),
        z.comp (Algebra.TensorProduct.productMap (bruhatCo τ k w α β) (ν w α β)) =
          tensorPointEquiv ((modGLPoint τ k (wordElt τ (mapWord
            (z : TorusAffine k τ.rank (N + m) →+* k) (bruhatParamWord τ k w α β)))).ofConv,
            (glPointEquiv (ψ (wordElt τ (mapWord (z : TorusAffine k τ.rank (N + m) →+* k)
              (bruhatParamWord τ k w α β))))).ofConv) := by
      intro w N m α β z
      rw [comp_productMap, hpt]
      congr 2
      rw [← point_psiWordCo ψ φx φy hφx hφy z, ofConv_toConv]
    let coF : ∀ {n : ℕ}, (Fin n → Letter τ) →
        (GLCoord k (Label τ) ⊗[k] GLCoord k (Fin M) →ₐ[k] MvPolynomial (Fin n) k) :=
      fun ℓ => Algebra.TensorProduct.productMap (unitCo k (wordUnit τ _ (freeWord ℓ)))
        (psiWordCo φx φy (freeWord ℓ)).ofConv
    have hcoF : ∀ {n : ℕ} (ℓ : Fin n → Letter τ) (z : MvPolynomial (Fin n) k →ₐ[k] k),
        z.comp (coF ℓ) = tensorPointEquiv
          ((modGLPoint τ k (wordElt τ (List.ofFn fun j => (ℓ j, z (MvPolynomial.X j))))).ofConv,
          (glPointEquiv (ψ (wordElt τ
            (List.ofFn fun j => (ℓ j, z (MvPolynomial.X j)))))).ofConv) := by
      intro n ℓ z
      rw [comp_productMap, comp_unitCo_wordUnit, ← mapWord_freeWord ℓ z, ← coe_wordElt,
        ← point_psiWordCo ψ φx φy hφx hφy z, ofConv_toConv]
    have hcovΓ : ∀ {N : ℕ} (α : Fin N → Fin τ.rank → ℤ), Function.Injective α →
        Set.range α = {β | IsRoot τ β ∧ 0 < height β} →
        ∀ (m : WeylGroup τ → ℕ) (β : ∀ w, Fin (m w) → Fin τ.rank → ℤ),
          (∀ w, Function.Injective (β w)) → (∀ w, Set.range (β w) = inversionSet w) →
            (⋃ w, Set.range fun z : TorusAffine k τ.rank (N + m w) →ₐ[k] k =>
              z.comp (Algebra.TensorProduct.productMap (bruhatCo τ k w α (β w))
                (ν w α (β w)))) = graphPoints τ k ψ := by
      intro N α hα hαr m β hβ hβr
      ext y
      simp only [graphPoints, Set.mem_iUnion, Set.mem_range]
      constructor
      · rintro ⟨w, z, rfl⟩
        exact ⟨_, (hν w α (β w) z).symm⟩
      · rintro ⟨g, rfl⟩
        obtain ⟨w, z, hz⟩ := exists_bruhatParam g α hα hαr m β hβ hβr
        exact ⟨w, z, by rw [hν, hz]⟩
    refine ⟨ν, fun w N m α β z => ⟨_, by rw [hpt, toConv_ofConv], ?_⟩, hcovΓ, ?_, ?_⟩
    · rw [← point_psiWordCo ψ φx φy hφx hφy z]
    · rw [← hcovΓ α₀ hα₀ hα₀r m₀ β₀ hβ₀ hβ₀r]
      have h := isPointConstructible_iUnion_range
        (fun w => TorusAffine k τ.rank (N₀ + m₀ w))
        (fun w => Algebra.TensorProduct.productMap (bruhatCo τ k w α₀ (β₀ w)) (ν w α₀ (β₀ w)))
      exact h
    · have h := isPointIrreducible_range_of_words (τ := τ)
        (fun g => tensorPointEquiv ((modGLPoint τ k g).ofConv, (glPointEquiv (ψ g)).ofConv))
        coF hcoF
      exact h
  · rw [← hcovG α₀ hα₀ hα₀r m₀ β₀ hβ₀ hβ₀r]
    exact isPointConstructible_iUnion_range (fun w => TorusAffine k τ.rank (N₀ + m₀ w))
      (fun w => bruhatCo τ k w α₀ (β₀ w))
  · let coG : ∀ {n : ℕ}, (Fin n → Letter τ) →
        (GLCoord k (Label τ) →ₐ[k] MvPolynomial (Fin n) k) :=
      fun ℓ => unitCo k (wordUnit τ _ (freeWord ℓ))
    have hcoG : ∀ {n : ℕ} (ℓ : Fin n → Letter τ) (z : MvPolynomial (Fin n) k →ₐ[k] k),
        z.comp (coG ℓ) =
          (modGLPoint τ k (wordElt τ (List.ofFn fun j => (ℓ j, z (MvPolynomial.X j))))).ofConv := by
      intro n ℓ z
      rw [comp_unitCo_wordUnit, mapWord_freeWord, coe_wordElt]
    rw [groupPoints_eq_range]
    have h := isPointIrreducible_range_of_words (τ := τ) (A := GLCoord k (Label τ))
      (F := fun g => (modGLPoint τ k g).ofConv) (co := @coG)
    exact h @hcoG

end CFSG.LieType.AlgebraicGroups
