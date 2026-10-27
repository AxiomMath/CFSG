module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.ElementaryAbelian
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.ANineSylowInvolutions

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37.TwoANine

open Equiv Finset

section Words

variable {G : Type*} [Group G] {ι : Type*}

theorem exists_eq_of_mem_closure_of_mul (w : ι → G) {s : Set G} (h1 : ∃ i, w i = 1)
    (hs : ∀ y ∈ s, y * y = 1) (hw : ∀ y ∈ s, ∀ i, ∃ j, w j = w i * y) {x : G}
    (hx : x ∈ Subgroup.closure s) : ∃ i, w i = x := by
  induction hx using Subgroup.closure_induction_right with
  | one => exact h1
  | mul_right x _ y hy ih =>
    obtain ⟨i, rfl⟩ := ih
    exact hw y hy i
  | mul_inv_cancel x _ y hy ih =>
    obtain ⟨i, rfl⟩ := ih
    rw [inv_eq_of_mul_eq_one_left (hs y hy)]
    exact hw y hy i

theorem mem_normalizer_of_conj (w : ι → G) {E : Subgroup G} (hwE : ∀ i, w i ∈ E)
    (hEw : ∀ x ∈ E, ∃ i, w i = x) {g : G} (hg2 : g * g = 1)
    (hg : ∀ i, ∃ j, w j = g * w i * g) : g ∈ Subgroup.normalizer (E : Set G) := by
  have hinv : g⁻¹ = g := inv_eq_of_mul_eq_one_left hg2
  have key : ∀ x ∈ E, g * x * g⁻¹ ∈ E := fun x hx => by
    obtain ⟨i, rfl⟩ := hEw x hx
    obtain ⟨j, hj⟩ := hg i
    rw [hinv, ← hj]
    exact hwE j
  refine Subgroup.mem_normalizer_iff.mpr fun x => ⟨key x, fun hx => ?_⟩
  have e : x = g * (g * x * g⁻¹) * g⁻¹ :=
    calc x = g⁻¹ * (g * x * g⁻¹) * g := by group
      _ = g * (g * x * g⁻¹) * g⁻¹ := by rw [hinv]
  rw [e]
  exact key _ hx

@[expose] def tripleWord (x y z : G) (v : Fin 8) : G :=
  x ^ (v.val / 4 % 2) * y ^ (v.val / 2 % 2) * z ^ (v.val % 2)

theorem coe_tripleWord {H : Subgroup G} (x y z : H) (v : Fin 8) :
    ((tripleWord x y z v : H) : G) = tripleWord (x : G) y z v := by
  simp only [tripleWord, Subgroup.coe_mul, Subgroup.coe_pow]

theorem tripleWord_mem_closure (x y z : G) (v : Fin 8) :
    tripleWord x y z v ∈ Subgroup.closure {x, y, z} := by
  have hx : x ∈ Subgroup.closure {x, y, z} := Subgroup.subset_closure (by simp)
  have hy : y ∈ Subgroup.closure {x, y, z} := Subgroup.subset_closure (by simp)
  have hz : z ∈ Subgroup.closure {x, y, z} := Subgroup.subset_closure (by simp)
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.pow_mem _ hx _)
    (Subgroup.pow_mem _ hy _)) (Subgroup.pow_mem _ hz _)

end Words

structure IsRegularTriple (x y z : Perm (Fin 9)) : Prop where
  mul_self_x : x * x = 1
  mul_self_y : y * y = 1
  mul_self_z : z * z = 1
  mul_x : ∀ v : Fin 8, ∃ w : Fin 8, tripleWord x y z w = tripleWord x y z v * x
  mul_y : ∀ v : Fin 8, ∃ w : Fin 8, tripleWord x y z w = tripleWord x y z v * y
  mul_z : ∀ v : Fin 8, ∃ w : Fin 8, tripleWord x y z w = tripleWord x y z v * z
  injective : ∀ v w : Fin 8, tripleWord x y z v = tripleWord x y z w → v = w
  comm : ∀ v w : Fin 8,
    tripleWord x y z v * tripleWord x y z w = tripleWord x y z w * tripleWord x y z v
  sq : ∀ v : Fin 8, tripleWord x y z v ^ 2 = 1
  card_support : ∀ v : Fin 8, v ≠ 0 → #(tripleWord x y z v).support = 2 * 4
  apply_eight : ∀ v : Fin 8, tripleWord x y z v 8 = 8
  transitive : ∀ i j : Fin 9, i ≠ 8 → j ≠ 8 → ∃ v : Fin 8, tripleWord x y z v i = j
  free : ∀ v : Fin 8, ∀ i : Fin 9, i ≠ 8 → tripleWord x y z v i = i → v = 0

namespace IsRegularTriple

variable {x y z : alternatingGroup (Fin 9)}
  (h : IsRegularTriple (x : Perm (Fin 9)) (y : Perm (Fin 9)) (z : Perm (Fin 9)))
include h

theorem exists_tripleWord_eq {g : alternatingGroup (Fin 9)}
    (hg : g ∈ Subgroup.closure {x, y, z}) : ∃ v, tripleWord x y z v = g := by
  have hw : ∀ u : alternatingGroup (Fin 9),
      (∀ v : Fin 8, ∃ w : Fin 8, tripleWord (x : Perm (Fin 9)) y z w =
        tripleWord (x : Perm (Fin 9)) y z v * u) →
      ∀ v, ∃ w, tripleWord x y z w = tripleWord x y z v * u := fun u hu v => by
    obtain ⟨w, hw⟩ := hu v
    exact ⟨w, Subtype.ext (by rw [Subgroup.coe_mul, coe_tripleWord, coe_tripleWord, hw])⟩
  refine exists_eq_of_mem_closure_of_mul (tripleWord x y z) ⟨0, by simp [tripleWord]⟩ ?_ ?_ hg
  · intro u hu
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu
    rcases hu with rfl | rfl | rfl
    · exact Subtype.ext h.mul_self_x
    · exact Subtype.ext h.mul_self_y
    · exact Subtype.ext h.mul_self_z
  · intro u hu
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu
    rcases hu with rfl | rfl | rfl
    · exact hw _ h.mul_x
    · exact hw _ h.mul_y
    · exact hw _ h.mul_z

theorem exists_tripleWord_eq_coe {g : alternatingGroup (Fin 9)}
    (hg : g ∈ Subgroup.closure {x, y, z}) :
    ∃ v, tripleWord (x : Perm (Fin 9)) y z v = (g : Perm (Fin 9)) := by
  obtain ⟨v, rfl⟩ := h.exists_tripleWord_eq hg
  exact ⟨v, (coe_tripleWord x y z v).symm⟩

theorem card_closure : Nat.card (Subgroup.closure {x, y, z}) = 8 := by
  have hinj : Function.Injective
      (fun v : Fin 8 => (⟨tripleWord x y z v, tripleWord_mem_closure x y z v⟩ :
        Subgroup.closure {x, y, z})) := fun v w hvw => by
    have e := congrArg (fun g : Subgroup.closure {x, y, z} =>
      ((g : alternatingGroup (Fin 9)) : Perm (Fin 9))) hvw
    simp only [coe_tripleWord] at e
    exact h.injective v w e
  have hsurj : Function.Surjective
      (fun v : Fin 8 => (⟨tripleWord x y z v, tripleWord_mem_closure x y z v⟩ :
        Subgroup.closure {x, y, z})) := fun g => by
    obtain ⟨v, hv⟩ := h.exists_tripleWord_eq g.2
    exact ⟨v, Subtype.ext hv⟩
  rw [← Nat.card_congr (Equiv.ofBijective _ ⟨hinj, hsurj⟩), Nat.card_eq_fintype_card,
    Fintype.card_fin]

theorem isElementaryAbelian : IsElementaryAbelian 2 (Subgroup.closure {x, y, z}) where
  is_comm := ⟨fun a b => by
    obtain ⟨v, hv⟩ := h.exists_tripleWord_eq_coe a.2
    obtain ⟨w, hw⟩ := h.exists_tripleWord_eq_coe b.2
    refine Subtype.ext (Subtype.ext ?_)
    simp only [Subgroup.coe_mul, ← hv, ← hw]
    exact h.comm v w⟩
  exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun a => by
    obtain ⟨v, hv⟩ := h.exists_tripleWord_eq_coe a.2
    refine Subtype.ext (Subtype.ext ?_)
    simp only [Subgroup.coe_pow, Subgroup.coe_one, ← hv]
    exact h.sq v

theorem apply_eight_of_mem {g : alternatingGroup (Fin 9)}
    (hg : g ∈ Subgroup.closure {x, y, z}) : (g : Perm (Fin 9)) 8 = 8 := by
  obtain ⟨v, hv⟩ := h.exists_tripleWord_eq_coe hg
  rw [← hv]
  exact h.apply_eight v

theorem cycleType_of_mem {g : alternatingGroup (Fin 9)} (hg : g ∈ Subgroup.closure {x, y, z})
    (hg1 : g ≠ 1) : (g : Perm (Fin 9)).cycleType = {2, 2, 2, 2} := by
  obtain ⟨v, hv⟩ := h.exists_tripleWord_eq_coe hg
  have hv0 : v ≠ 0 := by
    rintro rfl
    exact hg1 (Subtype.ext (by rw [← hv]; simp [tripleWord]))
  rw [← multiset_replicate_four_two, ← hv,
    cycleType_eq_replicate_iff_of_sq_eq_one (h.sq v)]
  exact h.card_support v hv0

theorem exists_mem_apply_eq {i j : Fin 9} (hi : i ≠ 8) (hj : j ≠ 8) :
    ∃ g ∈ Subgroup.closure {x, y, z}, (g : Perm (Fin 9)) i = j := by
  obtain ⟨v, hv⟩ := h.transitive i j hi hj
  exact ⟨tripleWord x y z v, tripleWord_mem_closure x y z v, by rw [coe_tripleWord, hv]⟩

theorem eq_one_of_apply_eq {g : alternatingGroup (Fin 9)} (hg : g ∈ Subgroup.closure {x, y, z})
    {i : Fin 9} (hi : i ≠ 8) (hgi : (g : Perm (Fin 9)) i = i) : g = 1 := by
  obtain ⟨v, hv⟩ := h.exists_tripleWord_eq_coe hg
  rw [← hv] at hgi
  have hv0 := h.free v i hi hgi
  subst hv0
  exact Subtype.ext (by rw [← hv]; simp [tripleWord])

theorem existsUnique_mem_apply_eq {i j : Fin 9} (hi : i ≠ 8) (hj : j ≠ 8) :
    ∃! g, g ∈ Subgroup.closure {x, y, z} ∧ (g : Perm (Fin 9)) i = j := by
  obtain ⟨g, hg, hgi⟩ := h.exists_mem_apply_eq hi hj
  refine ⟨g, ⟨hg, hgi⟩, fun g' ⟨hg', hg'i⟩ => ?_⟩
  have hmem : g'⁻¹ * g ∈ Subgroup.closure {x, y, z} :=
    Subgroup.mul_mem _ (Subgroup.inv_mem _ hg') hg
  have hfix : ((g'⁻¹ * g : alternatingGroup (Fin 9)) : Perm (Fin 9)) i = i := by
    rw [Subgroup.coe_mul, Subgroup.coe_inv, Perm.mul_apply, hgi, ← hg'i]
    exact Perm.inv_eq_iff_eq.mpr rfl
  exact inv_mul_eq_one.mp (h.eq_one_of_apply_eq hmem hi hfix)

theorem normalizer_le_stabilizer :
    Subgroup.normalizer ((Subgroup.closure {x, y, z} : Subgroup (alternatingGroup (Fin 9))) :
      Set (alternatingGroup (Fin 9))) ≤
      MulAction.stabilizer (alternatingGroup (Fin 9)) (8 : Fin 9) := by
  intro g hg
  have hx : x ∈ Subgroup.closure {x, y, z} := Subgroup.subset_closure (by simp)
  have hc := h.apply_eight_of_mem ((Subgroup.mem_normalizer_iff.mp hg x).mp hx)
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, Perm.mul_apply,
    Perm.mul_apply] at hc
  have hfix : (x : Perm (Fin 9)) ((g : Perm (Fin 9))⁻¹ 8) = (g : Perm (Fin 9))⁻¹ 8 :=
    Perm.eq_inv_iff_eq.mpr hc
  have h8 : (g : Perm (Fin 9))⁻¹ 8 = 8 := by
    by_contra hne
    have := h.eq_one_of_apply_eq hx hne hfix
    have h4 := h.card_support 4 (by decide)
    rw [this] at h4
    simp [tripleWord] at h4
  rw [MulAction.mem_stabilizer_iff, Subgroup.smul_def, Perm.smul_def]
  exact (Perm.inv_eq_iff_eq.mp h8).symm

theorem mem_normalizer {g : alternatingGroup (Fin 9)} (hg2 : (g : Perm (Fin 9)) * g = 1)
    (hg : ∀ v : Fin 8, ∃ w : Fin 8, tripleWord (x : Perm (Fin 9)) y z w =
      g * tripleWord (x : Perm (Fin 9)) y z v * g) :
    g ∈ Subgroup.normalizer ((Subgroup.closure {x, y, z} :
      Subgroup (alternatingGroup (Fin 9))) : Set (alternatingGroup (Fin 9))) := by
  refine mem_normalizer_of_conj (tripleWord x y z) (tripleWord_mem_closure x y z)
    (fun _ hg' => h.exists_tripleWord_eq hg') (Subtype.ext hg2) fun v => ?_
  obtain ⟨w, hw⟩ := hg v
  exact ⟨w, Subtype.ext (by simp only [Subgroup.coe_mul, coe_tripleWord, hw])⟩

end IsRegularTriple

end CFSG.ProperTwoGeneratedCore.Lemma37.TwoANine
