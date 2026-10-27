module

public import CFSG.LocalAnalysis.ComponentClassification.PSL3FourGroupSpec

public section

namespace CFSG.QuasithinUnique.Id2519.HSAut

open CFSG.PSL3Four CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four

@[expose] def classOKGen (n : Nat) (T gens ginv : Array Tab) (C : ClassData) (sizes : Array Nat) :
    Bool :=
  let m := T.size
  let idx := indexOf T
  invsOK n gens ginv &&
    (allBelow m fun k => posOf idx T T[k]! == k) &&
    (allBelow m fun k => allBelow gens.size fun j =>
      found idx T (conjTab n gens[j]! ginv[j]! T[k]!) &&
        C.lab[posOf idx T (conjTab n gens[j]! ginv[j]! T[k]!)]! == C.lab[k]!) &&
    C.reps.size == sizes.size &&
    (allBelow sizes.size fun l => C.reps[l]! < m && C.lab[C.reps[l]!]! == l) &&
    (allBelow m fun k => C.lab[k]! < sizes.size && C.wit[k]! < m &&
      comp n T[C.wit[k]!]! T[C.reps[C.lab[k]!]!]! == comp n T[k]! T[C.wit[k]!]!) &&
    (allBelow sizes.size fun l => countBelow m (fun k => C.lab[k]! == l) == sizes[l]!) &&
    0 < m && T[0]! == idTab n && C.lab[0]! == 0

theorem classOKGen_spec {n : ℕ} {T gens ginv : Array Tab} {C : ClassData} {sizes : Array ℕ}
    (h : classOKGen n T gens ginv C sizes = true) :
    invsOK n gens ginv = true ∧
      (∀ k < T.size, ∀ j < gens.size,
        found (indexOf T) T (conjTab n gens[j]! ginv[j]! T[k]!) = true ∧
          C.lab[posOf (indexOf T) T (conjTab n gens[j]! ginv[j]! T[k]!)]! = C.lab[k]!) ∧
      (∀ l < sizes.size, C.reps[l]! < T.size ∧ C.lab[C.reps[l]!]! = l) ∧
      (∀ k < T.size, C.lab[k]! < sizes.size ∧ C.wit[k]! < T.size ∧
        comp n T[C.wit[k]!]! T[C.reps[C.lab[k]!]!]! = comp n T[k]! T[C.wit[k]!]!) ∧
      (∀ l < sizes.size, countBelow T.size (fun k => C.lab[k]! == l) = sizes[l]!) ∧
      0 < T.size ∧ T[0]! = idTab n ∧ C.lab[0]! = 0 := by
  simp only [classOKGen, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, allBelow_eq_true,
    and_assoc] at h
  obtain ⟨h1, -, h3, -, h5, h6, h7, h8, h9, h10⟩ := h
  exact ⟨h1, fun k hk j hj => h3 k hk j hj, h5, h6, h7, h8, h9, h10⟩

theorem classes_of_classOKGen {n : ℕ} {A : Set (Equiv.Perm (Fin n))} {T gens ginv : Array Tab}
    {C : ClassData} {sizes : Array ℕ}
    (hA : ∀ a ∈ A, ∃ j < gens.size, TabRep gens[j]! a)
    (hH : Enumerates (Subgroup.closure A) T.toList)
    (h : classOKGen n T gens ginv C sizes = true) :
    ∃ e : Fin sizes.size ≃ ConjClasses (Subgroup.closure A),
      (∀ l, Nat.card (e l).carrier = sizes[l.val]!) ∧
      ∃ l₀ : Fin sizes.size, l₀.val = 0 ∧ e l₀ = ConjClasses.mk 1 := by
  classical
  obtain ⟨hinv, hconj, hreps, hwit, hcount, hm, hT0, hlab0⟩ := classOKGen_spec h
  obtain ⟨elt, pos, elt_rep, pos_lt, pos_rep, elt_pos, pos_elt, pos_eq⟩ := exists_elt_pos hH
  let labG : Subgroup.closure A → ℕ := fun g => C.lab[pos g]!
  have hlab_gen : ∀ a ∈ A, ∀ (ha : a ∈ Subgroup.closure A) (x : Subgroup.closure A),
      labG (⟨a, ha⟩ * x * ⟨a, ha⟩⁻¹) = labG x := by
    intro a haA ha x
    obtain ⟨j, hj, hrep⟩ := hA a haA
    obtain ⟨hf, hl⟩ := hconj (pos x) (pos_lt x) j hj
    have hrepi : TabRep ginv[j]! a⁻¹ := invsOK_spec hinv hj hrep
    have hrep' : TabRep (conjTab n gens[j]! ginv[j]! T[pos x]!)
        ((⟨a, ha⟩ * x * ⟨a, ha⟩⁻¹ : Subgroup.closure A) : Equiv.Perm (Fin n)) := by
      simpa using hrep.conjTab (pos_rep x) hrepi
    obtain ⟨hp, hpe⟩ := found_spec hf
    have hposc : pos (⟨a, ha⟩ * x * ⟨a, ha⟩⁻¹) =
        posOf (indexOf T) T (conjTab n gens[j]! ginv[j]! T[pos x]!) :=
      pos_eq _ _ hp (by rw [hpe]; exact hrep')
    simp only [labG]
    rw [hposc, hl]
  have hlab_conj : ∀ c x : Subgroup.closure A, labG (c * x * c⁻¹) = labG x := by
    intro c
    obtain ⟨c, hc⟩ := c
    induction hc using Subgroup.closure_induction with
    | mem a ha => intro x; exact hlab_gen a ha (Subgroup.subset_closure ha) x
    | one =>
      intro x
      have e : (⟨1, one_mem _⟩ : Subgroup.closure A) = 1 := rfl
      rw [e]
      simp
    | mul c₁ c₂ hc₁ hc₂ ih₁ ih₂ =>
      intro x
      have e : (⟨c₁ * c₂, mul_mem hc₁ hc₂⟩ : Subgroup.closure A) * x *
          (⟨c₁ * c₂, mul_mem hc₁ hc₂⟩ : Subgroup.closure A)⁻¹ =
          ⟨c₁, hc₁⟩ * (⟨c₂, hc₂⟩ * x * ⟨c₂, hc₂⟩⁻¹) * ⟨c₁, hc₁⟩⁻¹ := by
        apply Subtype.ext
        simp [mul_assoc]
      rw [e, ih₁ (⟨c₂, hc₂⟩ * x * ⟨c₂, hc₂⟩⁻¹), ih₂]
    | inv c₁ hc₁ ih =>
      intro x
      have e : x = (⟨c₁, hc₁⟩ * ((⟨c₁⁻¹, inv_mem hc₁⟩ : Subgroup.closure A) * x *
          (⟨c₁⁻¹, inv_mem hc₁⟩ : Subgroup.closure A)⁻¹) * ⟨c₁, hc₁⟩⁻¹) := by
        apply Subtype.ext
        simp [mul_assoc]
      have := ih ((⟨c₁⁻¹, inv_mem hc₁⟩ : Subgroup.closure A) * x *
        (⟨c₁⁻¹, inv_mem hc₁⟩ : Subgroup.closure A)⁻¹)
      rw [← e] at this
      exact this.symm
  have hconj_lab : ∀ x y : Subgroup.closure A, IsConj x y → labG x = labG y := by
    intro x y hxy
    obtain ⟨c, hc⟩ := isConj_iff.1 hxy
    rw [← hc, hlab_conj]
  have hlab_lt : ∀ x : Subgroup.closure A, labG x < sizes.size := fun x => (hwit _ (pos_lt x)).1
  let rep : ℕ → Subgroup.closure A := fun l => elt (C.reps[l]!)
  have hrep_lab : ∀ l < sizes.size, labG (rep l) = l := fun l hl => by
    simp only [labG, rep]
    rw [pos_elt _ (hreps l hl).1]
    exact (hreps l hl).2
  have hconj_rep : ∀ x : Subgroup.closure A, IsConj (rep (labG x)) x := by
    intro x
    obtain ⟨hl, hw, he⟩ := hwit _ (pos_lt x)
    have h1 := (elt_rep _ hw).comp (elt_rep _ (hreps _ hl).1)
    have h2 := (pos_rep x).comp (elt_rep _ hw)
    rw [he] at h1
    have h3 := h1.perm_eq h2
    refine isConj_iff.2 ⟨elt (C.wit[pos x]!), Subtype.ext ?_⟩
    show (elt (C.wit[pos x]!) : Equiv.Perm (Fin n)) *
      (elt (C.reps[C.lab[pos x]!]!) : Equiv.Perm (Fin n)) *
      (elt (C.wit[pos x]!) : Equiv.Perm (Fin n))⁻¹ = (x : Equiv.Perm (Fin n))
    rw [mul_inv_eq_iff_eq_mul]
    exact h3
  have hlab_conj' : ∀ x y : Subgroup.closure A, labG x = labG y → IsConj x y := fun x y hxy =>
    (hconj_rep x).symm.trans (hxy ▸ hconj_rep y)
  let e : Fin sizes.size → ConjClasses (Subgroup.closure A) := fun l => ConjClasses.mk (rep l.val)
  have he_inj : Function.Injective e := by
    intro l l' hll
    have := hconj_lab _ _ (ConjClasses.mk_eq_mk_iff_isConj.1 hll)
    rw [hrep_lab _ l.2, hrep_lab _ l'.2] at this
    exact Fin.ext this
  have he_surj : Function.Surjective e := by
    intro c
    obtain ⟨x, rfl⟩ := ConjClasses.mk_surjective c
    exact ⟨⟨labG x, hlab_lt x⟩, ConjClasses.mk_eq_mk_iff_isConj.2 (hconj_rep x)⟩
  have hpos1 : pos 1 = 0 := pos_eq 1 0 hm (by rw [hT0]; simpa using TabRep.idTab)
  have hsize : 0 < sizes.size := by
    have := (hwit 0 hm).1
    rwa [hlab0] at this
  refine ⟨Equiv.ofBijective e ⟨he_inj, he_surj⟩, fun l => ?_, ⟨0, hsize⟩, rfl, ?_⟩
  · have hset : ∀ x : Subgroup.closure A, x ∈ (e l).carrier ↔ (C.lab[pos x]! == l.val) = true := by
      intro x
      rw [ConjClasses.mem_carrier_iff_mk_eq, ConjClasses.mk_eq_mk_iff_isConj, beq_iff_eq]
      constructor
      · intro hx
        have := hconj_lab _ _ hx
        rwa [hrep_lab _ l.2] at this
      · intro hx
        apply hlab_conj'
        rw [hrep_lab _ l.2]
        exact hx
    have hcard := card_pos_filter pos_lt elt_pos pos_elt (fun k => C.lab[k]! == l.val)
    rw [hcount _ l.2] at hcard
    rw [← hcard]
    exact Nat.card_congr (Equiv.subtypeEquivRight hset)
  · show ConjClasses.mk (rep 0) = ConjClasses.mk 1
    rw [ConjClasses.mk_eq_mk_iff_isConj]
    apply hlab_conj'
    rw [hrep_lab _ hsize]
    simp only [labG, hpos1, hlab0]

theorem isSimpleGroup_of_classOKGen {n : ℕ} {A : Set (Equiv.Perm (Fin n))} {T gens ginv : Array Tab}
    {C : ClassData} {sizes : Array ℕ}
    (hA : ∀ a ∈ A, ∃ j < gens.size, TabRep gens[j]! a)
    (hH : Enumerates (Subgroup.closure A) T.toList)
    (h : classOKGen n T gens ginv C sizes = true) (hT : 1 < T.size)
    (hsums : ∀ l₀ : Fin sizes.size, l₀.val = 0 → ∀ U : Finset (Fin sizes.size), l₀ ∈ U →
      (∑ l ∈ U, sizes[l.val]!) ∣ T.size → U = {l₀} ∨ U = Finset.univ) :
    IsSimpleGroup ↥(Subgroup.closure A) := by
  obtain ⟨e, he, l₀, hl₀0, hl₀⟩ := classes_of_classOKGen hA hH h
  have hcard := hH.card
  refine isSimpleGroup_of_classes e (fun l => sizes[l.val]!) he l₀ hl₀ ?_ ?_
  · rw [hcard, Array.length_toList]; exact hT
  · intro U hU hdvd
    refine hsums l₀ hl₀0 U hU ?_
    rw [hcard, Array.length_toList] at hdvd
    exact hdvd

end CFSG.QuasithinUnique.Id2519.HSAut
