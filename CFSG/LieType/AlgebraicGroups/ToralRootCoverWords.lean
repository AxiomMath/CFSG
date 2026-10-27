module

public import CFSG.LieType.AlgebraicGroups.ConstructibleSubgroupGL
public import CFSG.LieType.AlgebraicGroups.RootWordBruhatCover
public import CFSG.LieType.Chevalley.SignKernelComponentBorel

public noncomputable section

namespace CFSG.LieType.AlgebraicGroups

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint WithConv

variable {τ : Tag} {k : Type} [Field k]

variable (τ) in
@[expose] def torusRootWord
    (R : Type) [CommRing R] {n : ℕ} (ℓ : Fin n → Fin τ.rank → ℤ)
    (t : Fin τ.rank → Rˣ) (c : Fin n → R) : List (Letter τ × R) :=
  (List.ofFn fun i => torusWord τ R i (t i)).flatten ++
    (List.ofFn fun p => pinnedWord τ R (ℓ p) (c p)).flatten

section TorusRootWord

variable {R S : Type} [CommRing R] [CommRing S] {n : ℕ} (ℓ : Fin n → Fin τ.rank → ℤ)

theorem wordUnit_torusRootWord
    (t : Fin τ.rank → Rˣ) (c : Fin n → R) :
    wordUnit τ R (torusRootWord τ R ℓ t c) =
      (List.ofFn fun i => torusElt τ R i (t i)).prod *
        (List.ofFn fun p => pinnedX τ R (ℓ p) (c p)).prod := by
  simp only [torusRootWord, wordUnit_append, wordUnit_flatten, List.map_ofFn, Function.comp_def,
    wordUnit_torusWord, wordUnit_pinnedWord]

theorem mapWord_torusRootWord
    (f : R →+* S) (t : Fin τ.rank → Rˣ) (c : Fin n → R) :
    mapWord f (torusRootWord τ R ℓ t c) =
      torusRootWord τ S ℓ (fun i => Units.map f.toMonoidHom (t i)) fun p => f (c p) := by
  simp only [torusRootWord, mapWord_append, mapWord_flatten, List.map_ofFn, Function.comp_def,
    mapWord_torusWord, mapWord_pinnedWord]

end TorusRootWord

variable (τ k) in
@[expose] def torusRootCo
    {n : ℕ} (ℓ : Fin n → Fin τ.rank → ℤ) :
    GLCoord k (Label τ) →ₐ[k] TorusAffine k τ.rank n :=
  unitCo k (wordUnit τ _ (torusRootWord τ (TorusAffine k τ.rank n) ℓ (torusUnit k τ.rank n)
    (affineCoord k τ.rank n)))

theorem point_torusRootCo
    {n : ℕ} (ℓ : Fin n → Fin τ.rank → ℤ) (t : Fin τ.rank → kˣ)
    (c : Fin n → k) :
    (modGLPoint τ k).symm (toConv ((torusAffinePoint t c).comp (torusRootCo τ k ℓ))) =
      (List.ofFn fun i => torusElt τ k i (t i)).prod *
        (List.ofFn fun p => pinnedX τ k (ℓ p) (c p)).prod := by
  rw [torusRootCo, comp_unitCo_wordUnit, toConv_ofConv, MulEquiv.symm_apply_apply,
    mapWord_torusRootWord, wordUnit_torusRootWord]
  simp only [units_map_torusUnit]
  simp

theorem mapWord_invWord {R S : Type} [CommRing R] [CommRing S] (f : R →+* S)
    (w : List (Letter τ × R)) : mapWord f (invWord w) = invWord (mapWord f w) := by
  simp [mapWord, invWord, List.map_reverse]

variable (τ) in
@[expose] def liftWord
    (R : Type) [CommRing R] (v : (Fin τ.rank → ℤ) → WeylGroup τ)
    (j : (Fin τ.rank → ℤ) → Fin τ.rank) (β : Fin τ.rank → ℤ) : List (Letter τ × R) :=
  canonicalWord τ R (v β) ++ weylWord τ R (j β) ++ invWord (canonicalWord τ R (v β))

theorem wordUnit_liftWord
    {R : Type} [CommRing R] (v : (Fin τ.rank → ℤ) → WeylGroup τ)
    (j : (Fin τ.rank → ℤ) → Fin τ.rank) (β : Fin τ.rank → ℤ) :
    wordUnit τ R (liftWord τ R v j β) = canonicalRep (coxeterSystem τ) R (v β) *
      weylElt τ R (j β) 1 * (canonicalRep (coxeterSystem τ) R (v β))⁻¹ := by
  rw [liftWord, wordUnit_append, wordUnit_append, wordUnit_invWord, wordUnit_canonicalWord,
    wordUnit_weylWord]

theorem mapWord_liftWord
    {R S : Type} [CommRing R] [CommRing S] (f : R →+* S)
    (v : (Fin τ.rank → ℤ) → WeylGroup τ) (j : (Fin τ.rank → ℤ) → Fin τ.rank)
    (β : Fin τ.rank → ℤ) : mapWord f (liftWord τ R v j β) = liftWord τ S v j β := by
  rw [liftWord, mapWord_append, mapWord_append, mapWord_invWord, mapWord_canonicalWord,
    mapWord_weylWord]
  rfl

variable (τ k) in
@[expose] def toralCoverElt
    {nI : ℕ} {m : Fin nI → ℕ}
    (α : (l : Fin nI) → Fin (m l) → Fin τ.rank → ℤ) (v : (Fin τ.rank → ℤ) → WeylGroup τ)
    (j : (Fin τ.rank → ℤ) → Fin τ.rank) (ω : Fin nI → List (Fin τ.rank → ℤ))
    (t : Fin τ.rank → kˣ) (c d : (l : Fin nI) → Fin (m l) → k) : ModGL τ k :=
  (List.ofFn fun i => torusElt τ k i (t i)).prod *
    (List.ofFn fun l => (List.ofFn fun p => pinnedX τ k (α l p) (c l p)).prod *
      ((ω l).map (componentWeylElt k v j)).prod *
      (List.ofFn fun p => pinnedX τ k (α l p) (d l p)).prod).prod

variable (τ) in
@[expose] def toralCoverWord
    (R : Type) [CommRing R] {nI : ℕ} {m : Fin nI → ℕ}
    (α : (l : Fin nI) → Fin (m l) → Fin τ.rank → ℤ) (v : (Fin τ.rank → ℤ) → WeylGroup τ)
    (j : (Fin τ.rank → ℤ) → Fin τ.rank) (ω : Fin nI → List (Fin τ.rank → ℤ))
    (t : Fin τ.rank → Rˣ) (c d : (l : Fin nI) → Fin (m l) → R) : List (Letter τ × R) :=
  (List.ofFn fun i => torusWord τ R i (t i)).flatten ++
    (List.ofFn fun l => (List.ofFn fun p => pinnedWord τ R (α l p) (c l p)).flatten ++
      ((ω l).map (liftWord τ R v j)).flatten ++
      (List.ofFn fun p => pinnedWord τ R (α l p) (d l p)).flatten).flatten

section CoverWord

variable
    {nI : ℕ} {m : Fin nI → ℕ} (α : (l : Fin nI) → Fin (m l) → Fin τ.rank → ℤ)
  (v : (Fin τ.rank → ℤ) → WeylGroup τ) (j : (Fin τ.rank → ℤ) → Fin τ.rank)
  (ω : Fin nI → List (Fin τ.rank → ℤ))

theorem wordUnit_toralCoverWord
    (t : Fin τ.rank → kˣ) (c d : (l : Fin nI) → Fin (m l) → k) :
    wordUnit τ k (toralCoverWord τ k α v j ω t c d) = toralCoverElt τ k α v j ω t c d := by
  simp only [toralCoverWord, toralCoverElt, wordUnit_append, wordUnit_flatten, List.map_ofFn,
    Function.comp_def, wordUnit_torusWord, wordUnit_pinnedWord, List.map_map,
    wordUnit_liftWord]
  rfl

theorem mapWord_toralCoverWord
    {R S : Type} [CommRing R] [CommRing S] (f : R →+* S)
    (t : Fin τ.rank → Rˣ) (c d : (l : Fin nI) → Fin (m l) → R) :
    mapWord f (toralCoverWord τ R α v j ω t c d) =
      toralCoverWord τ S α v j ω (fun i => Units.map f.toMonoidHom (t i))
        (fun l p => f (c l p)) fun l p => f (d l p) := by
  simp only [toralCoverWord, mapWord_append, mapWord_flatten, List.map_ofFn, Function.comp_def,
    mapWord_torusWord, mapWord_pinnedWord, List.map_map, mapWord_liftWord]

variable (τ k) in
@[expose] def toralCoverCo
    : GLCoord k (Label τ) →ₐ[k] TorusAffine k τ.rank (∑ l, (m l + m l)) :=
  unitCo k (wordUnit τ _ (toralCoverWord τ (TorusAffine k τ.rank (∑ l, (m l + m l))) α v j ω
    (torusUnit k τ.rank _)
    (fun l p => affineCoord k τ.rank _ (finSigmaFinEquiv ⟨l, Fin.castAdd (m l) p⟩))
    (fun l p => affineCoord k τ.rank _ (finSigmaFinEquiv ⟨l, Fin.natAdd (m l) p⟩))))

theorem point_toralCoverCo
    (t : Fin τ.rank → kˣ) (e : Fin (∑ l, (m l + m l)) → k) :
    (modGLPoint τ k).symm (toConv ((torusAffinePoint t e).comp (toralCoverCo τ k α v j ω))) =
      toralCoverElt τ k α v j ω t (fun l p => e (finSigmaFinEquiv ⟨l, Fin.castAdd (m l) p⟩))
        (fun l p => e (finSigmaFinEquiv ⟨l, Fin.natAdd (m l) p⟩)) := by
  rw [toralCoverCo, comp_unitCo_wordUnit, toConv_ofConv, MulEquiv.symm_apply_apply,
    mapWord_toralCoverWord, ← wordUnit_toralCoverWord]
  simp only [units_map_torusUnit]
  simp

end CoverWord

theorem exists_ofFn_pinnedX_eq
    {S : Set (Fin τ.rank → ℤ)} {s : ModGL τ k}
    (hs : s ∈ rootSpan τ k S) :
    ∃ (n : ℕ) (ℓ : Fin n → Fin τ.rank → ℤ) (c : Fin n → k), (∀ p, ℓ p ∈ S) ∧
      (List.ofFn fun p => pinnedX τ k (ℓ p) (c p)).prod = s := by
  suffices h : ∃ L : List ((Fin τ.rank → ℤ) × k), (∀ q ∈ L, q.1 ∈ S) ∧
      (L.map fun q => pinnedX τ k q.1 q.2).prod = s by
    obtain ⟨L, hL, rfl⟩ := h
    refine ⟨L.length, fun p => (L.get p).1, fun p => (L.get p).2,
      fun p => hL _ (List.get_mem L p), ?_⟩
    conv_rhs => rw [← List.ofFn_get L]
    rw [List.map_ofFn]
    rfl
  have hspan : rootSpan τ k S = Subgroup.closure (⋃ α ∈ S, Set.range (pinnedX τ k α)) := by
    simp only [Subgroup.closure_iUnion]
    rfl
  rw [hspan] at hs
  induction hs using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨α, hα, c, rfl⟩ : ∃ α ∈ S, ∃ c, pinnedX τ k α c = x := by
      simpa using hx
    exact ⟨[(α, c)], by simp [hα], by simp⟩
  | one => exact ⟨[], by simp, rfl⟩
  | mul x y _ _ hx hy =>
    obtain ⟨L, hL, rfl⟩ := hx
    obtain ⟨L', hL', rfl⟩ := hy
    exact ⟨L ++ L', fun q hq => (List.mem_append.1 hq).elim (hL q) (hL' q), by simp⟩
  | inv x _ hx =>
    obtain ⟨L, hL, rfl⟩ := hx
    refine ⟨(L.map fun q => (q.1, -q.2)).reverse, fun q hq => ?_, ?_⟩
    · obtain ⟨q', hq', rfl⟩ := List.mem_map.1 (List.mem_reverse.1 hq)
      exact hL q' hq'
    · rw [List.prod_inv_reverse, List.map_reverse, List.map_map, List.map_map]
      congr 2
      exact List.map_congr_left fun (q : (Fin τ.rank → ℤ) × k) _ => (pinnedX_neg τ k q.1 q.2).symm

theorem ofFn_pinnedX_append
    {n₁ n₂ : ℕ} (ℓ₁ : Fin n₁ → Fin τ.rank → ℤ)
    (ℓ₂ : Fin n₂ → Fin τ.rank → ℤ) (c₁ : Fin n₁ → k) (c₂ : Fin n₂ → k) :
    (List.ofFn fun p => pinnedX τ k (Fin.append ℓ₁ ℓ₂ p) (Fin.append c₁ c₂ p)) =
      (List.ofFn fun p => pinnedX τ k (ℓ₁ p) (c₁ p)) ++
        List.ofFn fun p => pinnedX τ k (ℓ₂ p) (c₂ p) := by
  rw [← List.ofFn_fin_append]
  congr 1
  funext p
  refine Fin.addCases (fun p => ?_) (fun p => ?_) p <;> simp

theorem eq_ofConv_of_symm_eq
    {y : GLCoord k (Label τ) →ₐ[k] k} {g : ModGL τ k}
    (h : (modGLPoint τ k).symm (toConv y) = g) : y = (modGLPoint τ k g).ofConv := by
  rw [← h, MulEquiv.apply_symm_apply, ofConv_toConv]

theorem isPointIrreducible_torusGroup_sup_rootSpan
    [IsAlgClosed k] {S : Set (Fin τ.rank → ℤ)}
    (hS : ∀ α ∈ S, IsRoot τ α) :
    IsPointIrreducible k (transportPoints (modGLPoint τ k)
      ((torusGroup τ k ⊔ rootSpan τ k S : Subgroup (ModGL τ k)) : Set (ModGL τ k))) := by
  classical
  let ι := Σ n : ℕ, {ℓ : Fin n → Fin τ.rank → ℤ // ∀ p, ℓ p ∈ S}
  let P : ι → Set (GLCoord k (Label τ) →ₐ[k] k) := fun q =>
    Set.range fun z : TorusAffine k τ.rank q.1 →ₐ[k] k => z.comp (torusRootCo τ k q.2.1)
  have hP : ∀ q, P q = Set.range fun x : (Fin τ.rank → kˣ) × (Fin q.1 → k) =>
      (modGLPoint τ k ((List.ofFn fun i => torusElt τ k i (x.1 i)).prod *
        (List.ofFn fun p => pinnedX τ k (q.2.1 p) (x.2 p)).prod)).ofConv := by
    intro q
    ext y
    constructor
    · rintro ⟨z, rfl⟩
      obtain ⟨⟨t, c⟩, rfl⟩ := torusAffinePointEquiv.surjective z
      exact ⟨(t, c), (eq_ofConv_of_symm_eq (point_torusRootCo q.2.1 t c)).symm⟩
    · rintro ⟨⟨t, c⟩, rfl⟩
      exact ⟨torusAffinePoint t c, eq_ofConv_of_symm_eq (point_torusRootCo q.2.1 t c)⟩
  have hHU := Subgroup.coe_mul_of_left_le_normalizer_right _ _
    (torusGroup_le_normalizer_rootSpan (K := k) hS)
  have hunion : transportPoints (modGLPoint τ k)
      ((torusGroup τ k ⊔ rootSpan τ k S : Subgroup (ModGL τ k)) : Set (ModGL τ k)) =
      ⋃ q, P q := by
    ext y
    constructor
    · rintro ⟨g, hg, rfl⟩
      rw [hHU] at hg
      obtain ⟨h, hh, s, hs, rfl⟩ := hg
      have hh' : h ∈ (torusProdHom τ k).range := by
        rw [range_torusProdHom]
        exact hh
      obtain ⟨t, rfl⟩ := hh'
      obtain ⟨n, ℓ, c, hℓ, rfl⟩ := exists_ofFn_pinnedX_eq hs
      refine Set.mem_iUnion.2 ⟨⟨n, ℓ, hℓ⟩, ?_⟩
      rw [hP]
      exact ⟨(t, c), by rw [torusProdHom_apply]⟩
    · intro hy
      obtain ⟨q, hq⟩ := Set.mem_iUnion.1 hy
      rw [hP] at hq
      obtain ⟨⟨t, c⟩, rfl⟩ := hq
      refine ⟨_, ?_, rfl⟩
      refine mul_mem (Subgroup.mem_sup_left ?_) (Subgroup.mem_sup_right ?_)
      · rw [← torusProdHom_apply, ← range_torusProdHom]
        exact ⟨t, rfl⟩
      · refine Subgroup.list_prod_mem _ fun x hx => ?_
        obtain ⟨p, rfl⟩ := List.mem_ofFn.1 hx
        exact le_iSup₂_of_le (f := fun β (_ : β ∈ S) => rootSubgroup τ k β) (q.2.1 p) (q.2.2 p)
          le_rfl (Subgroup.subset_closure ⟨c p, rfl⟩)
  rw [hunion]
  have : Nonempty ι := ⟨⟨0, Fin.elim0, fun p => p.elim0⟩⟩
  refine isPointIrreducible_iUnion_of_directed P (fun q => isPointIrreducible_range_of_isDomain _)
    fun q q' => ?_
  refine ⟨⟨q.1 + q'.1, Fin.append q.2.1 q'.2.1, fun p => ?_⟩, ?_, ?_⟩
  · refine Fin.addCases (fun p => ?_) (fun p => ?_) p
    · simpa using q.2.2 p
    · simpa using q'.2.2 p
  · rw [hP, hP]
    rintro _ ⟨⟨t, c⟩, rfl⟩
    refine ⟨(t, Fin.append c 0), ?_⟩
    simp only
    rw [ofFn_pinnedX_append, List.prod_append]
    simp only [Pi.zero_apply, pinnedX_zero, List.ofFn_const, List.prod_replicate, one_pow, mul_one]
  · rw [hP, hP]
    rintro _ ⟨⟨t, c⟩, rfl⟩
    refine ⟨(t, Fin.append 0 c), ?_⟩
    simp only
    rw [ofFn_pinnedX_append, List.prod_append]
    simp only [Pi.zero_apply, pinnedX_zero, List.ofFn_const, List.prod_replicate, one_pow, one_mul]

end CFSG.LieType.AlgebraicGroups
