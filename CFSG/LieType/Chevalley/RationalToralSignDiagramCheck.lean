module

public import CFSG.LieType.Chevalley.RationalToralSignDiagramTheta

public section

namespace CFSG.LieType.Chevalley.ToralSign

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint Matrix

variable {τ : Tag}

theorem wordElt_nil
    : wordElt τ [] = 1 :=
  (coxeterSystem τ).wordProd_nil

theorem wordElt_cons
    (i : Fin τ.rank) (l : List (Fin τ.rank)) :
    wordElt τ (i :: l) = wordElt τ l * simple τ i := by
  rw [wordElt, wordElt, List.reverse_cons, CoxeterSystem.wordProd_append,
    CoxeterSystem.wordProd_singleton]

variable (C : RootCertificate τ)

@[expose] def applyWordIdx (l : List (Fin τ.rank)) (k : ℕ) : ℕ :=
  l.foldl (fun k i => C.image k i) k

variable {C}

theorem applyWordIdx_spec
    (hC : C.check = true) (l : List (Fin τ.rank)) {k : ℕ}
    (hk : k < C.roots.length) :
    applyWordIdx C l k < C.roots.length ∧
      C.root (applyWordIdx C l k) = wordElt τ l • C.root k := by
  induction l generalizing k with
  | nil => exact ⟨hk, by rw [wordElt_nil, one_smul]; rfl⟩
  | cons i l ih =>
    obtain ⟨h1, h2⟩ := RootCertificate.image_spec hC hk i
    obtain ⟨h3, h4⟩ := ih h1
    refine ⟨h3, ?_⟩
    change C.root (applyWordIdx C l (C.image k i)) = _
    rw [h4, h2, wordElt_cons, mul_smul, simple_smul]

theorem root_fin
    (hC : C.check = true) (j : Fin τ.rank) :
    (j : ℕ) < C.roots.length ∧ C.root j = Pi.single j 1 := by
  have h := (RootCertificate.represents_one hC).2 j
  have hget : (List.range τ.rank).getD j 0 = j := by
    rw [List.getD_eq_getElem _ _ (by rw [List.length_range]; exact j.2), List.getElem_range]
  rw [hget, one_smul] at h
  exact h

variable (C) in
@[expose] def inKernel (m k : ℕ) : Bool :=
  decide (Even (maskPairing (natBits (τ := τ) m) (C.root k)))

theorem mem_kernelRoots_iff (hC : C.check = true) {m : ℕ} {α : Fin τ.rank → ℤ} :
    α ∈ kernelRoots (signMaskChar τ m) ↔
      ∃ k < C.roots.length, C.root k = α ∧ inKernel C m k = true := by
  rw [signMaskChar, mem_kernelRoots_maskChar, RootCertificate.isRoot_iff hC]
  constructor
  · rintro ⟨⟨k, hk, rfl⟩, he⟩
    exact ⟨k, hk, rfl, by simpa [inKernel] using he⟩
  · rintro ⟨k, hk, rfl, he⟩
    exact ⟨⟨k, hk, rfl⟩, by simpa [inKernel] using he⟩

variable (C) in
@[expose] def splusCheck (m : ℕ) (splus : List ℕ) : Bool :=
  splus == (List.range C.roots.length).filter fun k =>
    inKernel C m k && decide (0 < height (C.root k))

theorem mem_splus_iff {m : ℕ} {splus : List ℕ} (h : splusCheck C m splus = true) {k : ℕ} :
    k ∈ splus ↔ k < C.roots.length ∧ inKernel C m k = true ∧ 0 < height (C.root k) := by
  rw [splusCheck, beq_iff_eq] at h
  rw [h, List.mem_filter, List.mem_range, Bool.and_eq_true, decide_eq_true_eq]

theorem mem_posRoots_iff (hC : C.check = true) {m : ℕ} {splus : List ℕ}
    (h : splusCheck C m splus = true) {α : Fin τ.rank → ℤ} :
    α ∈ posRoots (kernelRoots (signMaskChar τ m)) ↔ ∃ k ∈ splus, C.root k = α := by
  constructor
  · rintro ⟨hα, hpos⟩
    obtain ⟨k, hk, rfl, he⟩ := (mem_kernelRoots_iff hC).1 hα
    exact ⟨k, (mem_splus_iff h).2 ⟨hk, he, hpos⟩, rfl⟩
  · rintro ⟨k, hk, rfl⟩
    obtain ⟨hk, he, hpos⟩ := (mem_splus_iff h).1 hk
    exact ⟨(mem_kernelRoots_iff hC).2 ⟨k, hk, rfl, he⟩, hpos⟩

variable (C) in
@[expose] def deltaCheck (splus delta : List ℕ) : Bool :=
  delta.all fun d => splus.contains d &&
    (decide (height (C.root d) = 1) || splus.all fun k => splus.all fun k' =>
      List.ofFn (C.root d) != List.ofFn (C.root k + C.root k'))

theorem root_mem_simpleUnion
    (hC : C.check = true) {m : ℕ} {splus delta : List ℕ}
    (hsp : splusCheck C m splus = true) (hd : deltaCheck C splus delta = true) {d : ℕ}
    (hdm : d ∈ delta) : C.root d ∈ simpleUnion (signMaskChar τ m) := by
  simp only [deltaCheck, List.all_eq_true, Bool.and_eq_true, List.contains_iff_mem,
    Bool.or_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq] at hd
  obtain ⟨hds, hdec⟩ := hd d hdm
  have hpos : C.root d ∈ posRoots (kernelRoots (signMaskChar τ m)) :=
    (mem_posRoots_iff hC hsp).2 ⟨d, hds, rfl⟩
  rw [simpleUnion_eq, Finset.mem_coe, mem_simpleRoots]
  refine ⟨hpos.1.1, hpos, fun γ hγ δ hδ e => ?_⟩
  rcases hdec with h1 | h2
  · have := congrArg height e
    rw [height_add, h1] at this
    have := hγ.2
    have := hδ.2
    omega
  · obtain ⟨k, hk, rfl⟩ := (mem_posRoots_iff hC hsp).1 hγ
    obtain ⟨k', hk', rfl⟩ := (mem_posRoots_iff hC hsp).1 hδ
    exact h2 k hk k' hk' (congrArg List.ofFn e)

theorem mem_kernelPosStabilizer_of_forall
    {b : Fin τ.rank → Bool} {w : WeylGroup τ}
    (hchar : ∀ j : Fin τ.rank, (Even (maskPairing b (w • Pi.single j 1)) ↔ b j = false))
    (hpos : ∀ α ∈ posRoots (kernelRoots (maskChar b)), 0 < height (w • α)) :
    w ∈ kernelPosStabilizer (maskChar b) := by
  have hcomp : maskCharComp b w = maskChar b := lattice_hom_ext fun j => by
    rw [maskCharComp_apply, maskChar_apply, maskChar_apply]
    have hp : maskPairing b (Pi.single j 1) = if b j then 1 else 0 := by
      rw [maskPairing, Finset.sum_eq_single j (fun k _ hk => by simp [hk]) (by simp)]
      simp
    rw [hp]
    cases hb : b j
    · rw [Even.neg_one_zpow ((hchar j).2 hb)]
      rfl
    · have hodd : Odd (maskPairing b (w • Pi.single j 1)) :=
        Int.not_even_iff_odd.1 fun he => by simp [(hchar j).1 he] at hb
      rw [Odd.neg_one_zpow hodd]
      rfl
  have hw : w ∈ charStabilizer (maskChar b) := fun v => by
    rw [← maskCharComp_apply, hcomp]
  refine ⟨hw, ?_⟩
  have hmaps : Set.MapsTo (w • ·) (posRoots (kernelRoots (maskChar b)))
      (posRoots (kernelRoots (maskChar b))) :=
    fun α hα => ⟨smul_mem_kernelRoots hw hα.1, hpos α hα⟩
  exact (((finite_posRoots_kernelRoots _).injOn_iff_bijOn_of_mapsTo hmaps).1
    (MulAction.injective w).injOn).image_eq

variable (C) in
@[expose] def omegaCheck (m : ℕ) (splus : List ℕ) (l : List (Fin τ.rank)) : Bool :=
  (List.finRange τ.rank).all (fun j =>
    inKernel C m (applyWordIdx C l j) == !natBits (τ := τ) m j) &&
  splus.all fun k => decide (0 < height (C.root (applyWordIdx C l k)))

theorem wordElt_mem_of_omegaCheck
    (hC : C.check = true) {m : ℕ} {splus : List ℕ}
    (hsp : splusCheck C m splus = true) {l : List (Fin τ.rank)}
    (h : omegaCheck C m splus l = true) :
    wordElt τ l ∈ kernelPosStabilizer (signMaskChar τ m) := by
  simp only [omegaCheck, Bool.and_eq_true, List.all_eq_true, List.mem_finRange, true_implies,
    beq_iff_eq, decide_eq_true_eq] at h
  refine mem_kernelPosStabilizer_of_forall (fun j => ?_) (fun α hα => ?_)
  · obtain ⟨hj, hj'⟩ := root_fin hC j
    have hw := (applyWordIdx_spec hC l hj).2
    rw [hj'] at hw
    have := h.1 j
    rw [inKernel, hw] at this
    cases hb : natBits (τ := τ) m j <;> simp_all
  · obtain ⟨k, hk, rfl⟩ := (mem_posRoots_iff hC hsp).1 hα
    rw [← (applyWordIdx_spec hC l ((mem_splus_iff hsp).1 hk).1).2]
    exact h.2 k hk

variable (C) in
@[expose] def distinctCheck (ls : List (List (Fin τ.rank))) : Bool :=
  decide (ls.Pairwise fun l l' => ((List.finRange τ.rank).any fun j =>
    List.ofFn (C.root (applyWordIdx C l j)) != List.ofFn (C.root (applyWordIdx C l' j))) = true)

theorem pairwise_ne_of_distinctCheck
    (hC : C.check = true) {ls : List (List (Fin τ.rank))}
    (h : distinctCheck C ls = true) : ls.Pairwise fun l l' => wordElt τ l ≠ wordElt τ l' := by
  rw [distinctCheck, decide_eq_true_eq] at h
  refine h.imp fun {l l'} hll' e => ?_
  simp only [List.any_eq_true, List.mem_finRange, true_and, bne_iff_ne, ne_eq] at hll'
  obtain ⟨j, hj⟩ := hll'
  obtain ⟨hjn, hj'⟩ := root_fin hC j
  rw [(applyWordIdx_spec hC l hjn).2, (applyWordIdx_spec hC l' hjn).2, e] at hj
  exact hj rfl

theorem kernelPosStabilizer_eq_of_check
    (hC : C.check = true) {m : ℕ} {splus : List ℕ}
    (hsp : splusCheck C m splus = true) {ls : List (List (Fin τ.rank))}
    (hω : ls.all (omegaCheck C m splus) = true) (hdist : distinctCheck C ls = true)
    (hcard : Nat.card (kernelPosStabilizer (signMaskChar τ m)) ≤ ls.length) :
    (kernelPosStabilizer (signMaskChar τ m) : Set (WeylGroup τ)) =
        {w | ∃ l ∈ ls, wordElt τ l = w} ∧
      Nat.card (kernelPosStabilizer (signMaskChar τ m)) = ls.length := by
  classical
  have hmem : ∀ l ∈ ls, wordElt τ l ∈ kernelPosStabilizer (signMaskChar τ m) := fun l hl =>
    wordElt_mem_of_omegaCheck hC hsp (List.all_eq_true.1 hω l hl)
  have hnd : (ls.map (wordElt τ)).Nodup :=
    List.pairwise_map.2 (pairwise_ne_of_distinctCheck hC hdist)
  have hT : {w | ∃ l ∈ ls, wordElt τ l = w} = ((ls.map (wordElt τ)).toFinset : Set _) := by
    ext w
    simp
  have hTcard : ({w | ∃ l ∈ ls, wordElt τ l = w} : Set (WeylGroup τ)).ncard = ls.length := by
    rw [hT, Set.ncard_coe_finset, List.toFinset_card_of_nodup hnd, List.length_map]
  have hΩ : ((kernelPosStabilizer (signMaskChar τ m) : Set (WeylGroup τ))).ncard =
      Nat.card (kernelPosStabilizer (signMaskChar τ m)) :=
    (Nat.card_coe_set_eq _).symm
  have heq : {w | ∃ l ∈ ls, wordElt τ l = w} =
      (kernelPosStabilizer (signMaskChar τ m) : Set (WeylGroup τ)) :=
    Set.eq_of_subset_of_ncard_le (by rintro _ ⟨l, hl, rfl⟩; exact hmem l hl)
      (by rw [hΩ, hTcard]; exact hcard) (Set.toFinite _)
  refine ⟨heq.symm, ?_⟩
  rw [← hΩ, ← heq, hTcard]

variable (C) in
@[expose] def rhoCheck (ρ : Equiv.Perm (Fin τ.rank)) (rhoIdx : List ℕ) : Bool :=
  (List.range C.roots.length).all fun k => decide (rhoIdx.getD k 0 < C.roots.length) &&
    List.ofFn (C.root (rhoIdx.getD k 0)) == List.ofFn (permLattice ρ (C.root k))

variable (C) in
@[expose] def thetaIdx (rhoIdx : List ℕ) (l : List (Fin τ.rank)) (k : ℕ) : ℕ :=
  applyWordIdx C l (rhoIdx.getD k 0)

theorem thetaIdx_spec
    (hC : C.check = true) {ρ : Equiv.Perm (Fin τ.rank)} {rhoIdx : List ℕ}
    (hρ : rhoCheck C ρ rhoIdx = true) (l : List (Fin τ.rank)) {k : ℕ}
    (hk : k < C.roots.length) :
    thetaIdx C rhoIdx l k < C.roots.length ∧
      C.root (thetaIdx C rhoIdx l k) = thetaMap (wordElt τ l) ρ (C.root k) := by
  simp only [rhoCheck, List.all_eq_true, List.mem_range, Bool.and_eq_true, decide_eq_true_eq,
    beq_iff_eq] at hρ
  obtain ⟨h1, h2⟩ := hρ k hk
  obtain ⟨h3, h4⟩ := applyWordIdx_spec hC l h1
  exact ⟨h3, by rw [thetaIdx, h4, List.ofFn_injective h2, thetaMap]⟩

@[expose] def cpair (x y : Fin τ.rank → ℤ) : ℤ :=
  ∑ i, x i * ∑ j, τ.cartan i j * y j

theorem iform_eq_cpair (hS : τ.symmetrizedCartan = τ.cartan) (x y : Fin τ.rank → ℤ) :
    iform x y = cpair x y := by
  simp only [iform, cpair, hS, Finset.mul_sum, mul_assoc]

theorem dotProduct_eq_cpair (hS : τ.symmetrizedCartan = τ.cartan) (x y : Fin τ.rank → ℤ) :
    x ⬝ᵥ (τ.symmetrizedCartan *ᵥ y) = cpair x y := by
  rw [dotProduct_mulVec_eq_iform, iform_eq_cpair hS]

@[expose] def orbitIdx (f : ℕ → ℕ) (p k : ℕ) : List ℕ :=
  (List.range p).map fun i => f^[i] k

variable (C) in
@[expose] def orbitCheckAt (f : ℕ → ℕ) (p k : ℕ) : Bool :=
  f^[p] k == k &&
    (f k == k || decide (((orbitIdx f p k).map fun a => List.ofFn (C.root a)).Nodup)) &&
    (orbitIdx f p k).all fun a => (orbitIdx f p k).all fun c =>
      List.ofFn (C.root a) == List.ofFn (C.root c) || cpair (C.root a) (C.root c) == 0

variable (C) in
@[expose] def orbitCheck (m : ℕ) (f : ℕ → ℕ) (p : ℕ) : Bool :=
  (List.range C.roots.length).all fun k => !inKernel C m k || orbitCheckAt C f p k

section Orbits

variable {θ : (Fin τ.rank → ℤ) → Fin τ.rank → ℤ} {f : ℕ → ℕ}
  (hf : ∀ k < C.roots.length, f k < C.roots.length ∧ C.root (f k) = θ (C.root k))
include hf

theorem iterate_spec {k : ℕ} (hk : k < C.roots.length) (i : ℕ) :
    f^[i] k < C.roots.length ∧ C.root (f^[i] k) = θ^[i] (C.root k) := by
  induction i with
  | zero => exact ⟨hk, rfl⟩
  | succ i ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    obtain ⟨h1, h2⟩ := hf _ ih.1
    exact ⟨h1, by rw [h2, ih.2]⟩

theorem iterOrbit_eq_singleton {k : ℕ} (hk : k < C.roots.length) (hfix : f k = k) :
    iterOrbit θ (C.root k) = {C.root k} := by
  have h : θ (C.root k) = C.root k := by rw [← (hf k hk).2, hfix]
  ext y
  simp only [iterOrbit, Set.mem_range, Set.mem_singleton_iff]
  constructor
  · rintro ⟨i, rfl⟩
    exact Function.iterate_fixed h i
  · rintro rfl
    exact ⟨0, rfl⟩

theorem iterOrbit_eq_of_period {k : ℕ} (hk : k < C.roots.length) {p : ℕ} (hp : 0 < p)
    (hper : f^[p] k = k) :
    iterOrbit θ (C.root k) = {y | y ∈ (orbitIdx f p k).map C.root} := by
  have hper' : Function.IsPeriodicPt θ p (C.root k) := by
    change θ^[p] (C.root k) = C.root k
    rw [← (iterate_spec hf hk p).2, hper]
  ext y
  simp only [iterOrbit, Set.mem_range, Set.mem_ofPred_eq, orbitIdx, List.map_map, List.mem_map,
    List.mem_range, Function.comp_apply]
  constructor
  · rintro ⟨j, rfl⟩
    exact ⟨j % p, Nat.mod_lt _ hp, by
      rw [(iterate_spec hf hk _).2, hper'.iterate_mod_apply]⟩
  · rintro ⟨i, -, rfl⟩
    exact ⟨i, (iterate_spec hf hk i).2.symm⟩

theorem orbit_facts (hS : τ.symmetrizedCartan = τ.cartan) {k : ℕ} (hk : k < C.roots.length)
    {p : ℕ} (hp : 0 < p) (h : orbitCheckAt C f p k = true) :
    ((iterOrbit θ (C.root k)).ncard = 1 ∨ (iterOrbit θ (C.root k)).ncard = p) ∧
      (iterOrbit θ (C.root k)).Pairwise fun x y => x ⬝ᵥ (τ.symmetrizedCartan *ᵥ y) = 0 := by
  classical
  simp only [orbitCheckAt, Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true, decide_eq_true_eq,
    List.all_eq_true] at h
  obtain ⟨⟨hper, hfix⟩, hall⟩ := h
  have horb := iterOrbit_eq_of_period hf hk hp hper
  refine ⟨?_, ?_⟩
  · rcases hfix with hfix | hnd
    · left
      rw [iterOrbit_eq_singleton hf hk hfix, Set.ncard_singleton]
    · right
      have hnd' : ((orbitIdx f p k).map C.root).Nodup :=
        List.Nodup.of_map (fun v : Fin τ.rank → ℤ => List.ofFn v) (by
          rw [List.map_map]
          exact hnd)
      have : {y | y ∈ (orbitIdx f p k).map C.root} =
          (((orbitIdx f p k).map C.root).toFinset : Set (Fin τ.rank → ℤ)) := by
        ext y
        simp
      rw [horb, this, Set.ncard_coe_finset, List.toFinset_card_of_nodup hnd', List.length_map,
        orbitIdx, List.length_map, List.length_range]
  · rw [horb]
    rintro _ hy _ hz hyz
    obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hy
    obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hz
    rcases hall a ha c hc with he | ho
    · exact absurd (List.ofFn_injective he) hyz
    · rw [dotProduct_eq_cpair hS]
      exact ho

end Orbits

@[expose] def reflC (x v : Fin τ.rank → ℤ) : Fin τ.rank → ℤ :=
  v - (2 * cpair x v / cpair x x) • x

theorem rootReflection_smul_eq_reflC
    (hS : τ.symmetrizedCartan = τ.cartan)
    {x : Fin τ.rank → ℤ} (hx : IsRoot τ x) (v : Fin τ.rank → ℤ) :
    rootReflection x • v = reflC x v := by
  rw [rootReflection_smul hx, corootPair, reflC, iform_eq_cpair hS, iform_eq_cpair hS]

theorem prod_smul_eq_foldr
    (hS : τ.symmetrizedCartan = τ.cartan) {l : List (Fin τ.rank → ℤ)}
    (hl : ∀ x ∈ l, IsRoot τ x) (v : Fin τ.rank → ℤ) :
    (l.map rootReflection).prod • v = l.foldr reflC v := by
  induction l with
  | nil => simp
  | cons x l ih =>
    rw [List.map_cons, List.prod_cons, mul_smul, ih fun y hy => hl y (List.mem_cons_of_mem _ hy),
      rootReflection_smul_eq_reflC hS (hl x (List.mem_cons_self ..))]
    rfl

variable (C) in
@[expose] def orbitVecs (f : ℕ → ℕ) (p d : ℕ) : List (Fin τ.rank → ℤ) :=
  if f d = d then [C.root d] else (orbitIdx f p d).map C.root

variable (C) in
@[expose] def genApply (f : ℕ → ℕ) (p d : ℕ) (v : Fin τ.rank → ℤ) : Fin τ.rank → ℤ :=
  (orbitVecs C f p d).foldr reflC v

variable (C) in
@[expose] def pathApply (f : ℕ → ℕ) (p : ℕ) (path : List ℕ) (v : Fin τ.rank → ℤ) :
    Fin τ.rank → ℤ :=
  path.foldl (fun v d => genApply C f p d v) v

variable (C) in
@[expose] def pathCheck (m : ℕ) (f : ℕ → ℕ) (p : ℕ) (delta : List ℕ)
    (paths : List (ℕ × List ℕ)) : Bool :=
  (List.range C.roots.length).all fun k => !inKernel C m k ||
    paths.any fun e => e.1 == k && e.2.all (delta.contains ·) &&
      delta.any fun d => List.ofFn (C.root d) == List.ofFn (pathApply C f p e.2 (C.root k))

theorem thetaProperties_of_check
    (hC : C.check = true) {ρ : Equiv.Perm (Fin τ.rank)}
    (hA : ∀ i j, τ.cartan (ρ i) (ρ j) = τ.cartan i j) (hS : τ.symmetrizedCartan = τ.cartan)
    {m : ℕ} (hχ : permChar ρ (signMaskChar τ m) = signMaskChar τ m)
    {l : List (Fin τ.rank)} (hω : wordElt τ l ∈ kernelPosStabilizer (signMaskChar τ m))
    {p : ℕ} (hp : 0 < p) {rhoIdx splus delta : List ℕ} {paths : List (ℕ × List ℕ)}
    (hρ : rhoCheck C ρ rhoIdx = true) (hsp : splusCheck C m splus = true)
    (hd : deltaCheck C splus delta = true)
    (ho : orbitCheck C m (thetaIdx C rhoIdx l) p = true)
    (hpath : pathCheck C m (thetaIdx C rhoIdx l) p delta paths = true) :
    ThetaProperties ρ p (signMaskChar τ m) (wordElt τ l) := by
  classical
  have hB : ∀ i j, τ.symmetrizedCartan (ρ i) (ρ j) = τ.symmetrizedCartan i j := fun i j => by
    rw [hS]
    exact hA i j
  set f := thetaIdx C rhoIdx l
  have hf : ∀ k < C.roots.length, f k < C.roots.length ∧
      C.root (f k) = thetaMap (wordElt τ l) ρ (C.root k) :=
    fun k hk => thetaIdx_spec hC hρ l hk
  have hoAt : ∀ k < C.roots.length, inKernel C m k = true → orbitCheckAt C f p k = true := by
    intro k hk he
    simp only [orbitCheck, List.all_eq_true, List.mem_range, Bool.or_eq_true,
      Bool.not_eq_true'] at ho
    rcases ho k hk with h | h
    · rw [he] at h
      exact absurd h (by decide)
    · exact h
  have hfacts : ∀ α ∈ kernelRoots (signMaskChar τ m),
      ((iterOrbit (thetaMap (wordElt τ l) ρ) α).ncard = 1 ∨
        (iterOrbit (thetaMap (wordElt τ l) ρ) α).ncard = p) ∧
      (iterOrbit (thetaMap (wordElt τ l) ρ) α).Pairwise
        fun x y => x ⬝ᵥ (τ.symmetrizedCartan *ᵥ y) = 0 := by
    intro α hα
    obtain ⟨k, hk, rfl, he⟩ := (mem_kernelRoots_iff hC).1 hα
    exact orbit_facts hf hS hk hp (hoAt k hk he)
  have hpair := fun α hα => (hfacts α hα).2
  have hgen : ∀ d ∈ delta, ∃ g ∈ orbitReflectionGroup (thetaMap (wordElt τ l) ρ)
      (simpleUnion (signMaskChar τ m)), ∀ v, g • v = genApply C f p d v := by
    intro d hdm
    have hβ := root_mem_simpleUnion hC hsp hd hdm
    obtain ⟨k, hk, hkd, he⟩ := (mem_kernelRoots_iff hC).1 (simpleUnion_subset _ hβ)
    have hdn : d < C.roots.length := by
      simp only [deltaCheck, List.all_eq_true, Bool.and_eq_true, List.contains_iff_mem] at hd
      exact ((mem_splus_iff hsp).1 (hd d hdm).1).1
    have hd' : inKernel C m d = true := by
      simp only [deltaCheck, List.all_eq_true, Bool.and_eq_true, List.contains_iff_mem] at hd
      exact ((mem_splus_iff hsp).1 (hd d hdm).1).2.1
    have hcheck := hoAt d hdn hd'
    have hcheck' := hcheck
    simp only [orbitCheckAt, Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true,
      decide_eq_true_eq] at hcheck'
    obtain ⟨⟨hper, hfix⟩, -⟩ := hcheck'
    have hnd : (orbitVecs C f p d).Nodup := by
      unfold orbitVecs
      split_ifs with hfd
      · exact List.nodup_singleton _
      · rcases hfix with hfix | hnd
        · exact absurd hfix hfd
        · exact List.Nodup.of_map (fun v : Fin τ.rank → ℤ => List.ofFn v)
            (by rw [List.map_map]; exact hnd)
    have hset : ∀ x, x ∈ orbitVecs C f p d ↔ x ∈ iterOrbit (thetaMap (wordElt τ l) ρ) (C.root d) :=
      fun x => by
      unfold orbitVecs
      split_ifs with hfd
      · rw [iterOrbit_eq_singleton hf hdn hfd]
        simp
      · rw [iterOrbit_eq_of_period hf hdn hp hper]
        rfl
    have hroots : ∀ x ∈ orbitVecs C f p d, IsRoot τ x := fun x hx =>
      (simpleUnion_subset _ (iterOrbit_subset_simpleUnion hA hχ hω hβ ((hset x).1 hx))).1
    let O := (orbitVecs C f p d).toFinset
    have hO : (O : Set (Fin τ.rank → ℤ)) = iterOrbit (thetaMap (wordElt τ l) ρ) (C.root d) := by
      ext x
      rw [Finset.mem_coe, List.mem_toFinset, hset]
    have hcomm : ∀ x ∈ O, ∀ y ∈ O, Commute (rootReflection x) (rootReflection y) :=
      fun x hx y hy => commute_rootReflection_of_mem hA hχ hω hpair hβ
        ((hset x).1 (List.mem_toFinset.1 hx)) ((hset y).1 (List.mem_toFinset.1 hy))
    refine ⟨orbitReflection O, Subgroup.subset_closure ⟨C.root d, hβ, O, hO, rfl⟩, fun v => ?_⟩
    rw [orbitReflection_eq_prod hnd (fun x => List.mem_toFinset) hcomm,
      prod_smul_eq_foldr hS hroots]
    rfl
  have hpathg : ∀ path : List ℕ, (∀ d ∈ path, d ∈ delta) →
      ∃ g ∈ orbitReflectionGroup (thetaMap (wordElt τ l) ρ) (simpleUnion (signMaskChar τ m)),
        ∀ v, g • v = pathApply C f p path v := by
    intro path
    induction path with
    | nil => exact fun _ => ⟨1, one_mem _, fun v => by rw [one_smul]; rfl⟩
    | cons d rest ih =>
      intro hpd
      obtain ⟨g, hg, hgv⟩ := hgen d (hpd d (List.mem_cons_self ..))
      obtain ⟨g', hg', hg'v⟩ := ih fun d' hd' => hpd d' (List.mem_cons_of_mem _ hd')
      refine ⟨g' * g, mul_mem hg' hg, fun v => ?_⟩
      rw [mul_smul, hgv, hg'v]
      rfl
  refine ThetaProperties.of_orbits hA hχ hω hpair hB (fun α hα => (hfacts α hα).1)
    (fun α hα => ?_)
  obtain ⟨k, hk, rfl, he⟩ := (mem_kernelRoots_iff hC).1 hα
  simp only [pathCheck, List.all_eq_true, List.mem_range, Bool.or_eq_true, Bool.not_eq_true',
    List.any_eq_true, Bool.and_eq_true, beq_iff_eq, List.contains_iff_mem] at hpath
  rcases hpath k hk with h | ⟨e, -, ⟨⟨rfl, hall⟩, d', hd', hd'v⟩⟩
  · rw [he] at h
    exact absurd h (by decide)
  · obtain ⟨g, hg, hgv⟩ := hpathg e.2 hall
    refine ⟨g, hg, ?_⟩
    rw [hgv, ← List.ofFn_injective hd'v]
    exact root_mem_simpleUnion hC hsp hd hd'

theorem repClaims_of_check
    (hC : C.check = true) {ρ : Equiv.Perm (Fin τ.rank)}
    (hA : ∀ i j, τ.cartan (ρ i) (ρ j) = τ.cartan i j) (hS : τ.symmetrizedCartan = τ.cartan)
    {p : ℕ} (hp : 0 < p) {e : SignRep τ}
    (hχ : permChar ρ (signMaskChar τ e.mask) = signMaskChar τ e.mask)
    {rhoIdx splus delta : List ℕ} (hρ : rhoCheck C ρ rhoIdx = true)
    (hsp : splusCheck C e.mask splus = true) (hd : deltaCheck C splus delta = true)
    (hω : e.omegaWords.all (omegaCheck C e.mask splus) = true)
    (hdist : distinctCheck C e.omegaWords = true) (hlen : e.omegaWords.length = e.omegaOrder)
    (hcard : Nat.card (kernelPosStabilizer (signMaskChar τ e.mask)) ≤ e.omegaOrder)
    (htheta : ∀ l ∈ e.omegaWords, ∃ paths : List (ℕ × List ℕ),
      orbitCheck C e.mask (thetaIdx C rhoIdx l) p = true ∧
        pathCheck C e.mask (thetaIdx C rhoIdx l) p delta paths = true) :
    Nat.card (kernelPosStabilizer (signMaskChar τ e.mask)) = e.omegaOrder ∧
      (kernelPosStabilizer (signMaskChar τ e.mask) : Set (WeylGroup τ)) =
        {w | ∃ l ∈ e.omegaWords, wordElt τ l = w} ∧
      ∀ l ∈ e.omegaWords, ThetaProperties ρ p (signMaskChar τ e.mask) (wordElt τ l) := by
  obtain ⟨h1, h2⟩ := kernelPosStabilizer_eq_of_check hC hsp hω hdist (hlen ▸ hcard)
  refine ⟨h2.trans hlen, h1, fun l hl => ?_⟩
  obtain ⟨paths, ho, hpath⟩ := htheta l hl
  exact thetaProperties_of_check hC hA hS hχ
    (wordElt_mem_of_omegaCheck hC hsp (List.all_eq_true.1 hω l hl)) hp hρ hsp hd ho hpath

end CFSG.LieType.Chevalley.ToralSign
