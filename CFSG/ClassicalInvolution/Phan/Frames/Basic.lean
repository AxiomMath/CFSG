module

public import CFSG.ClassicalInvolution.Phan.Geometry.Points

public section

namespace CFSG.ClassicalInvolution.Phan

open CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary Module Matrix

variable {K : Type} [Field K] {σ : K ≃+* K} {m : ℕ}

variable (σ m) in
@[ext] structure Frame where
  line : Fin m → Submodule K (Fin m → K)
  finrank_line : ∀ k, finrank K (line k) = 1
  nondeg_line : ∀ k, Nondeg σ (line k)
  orth_line : ∀ k l, k ≠ l → Orth σ (line k) (line l)

namespace Frame

variable {c d : Frame σ m}

theorem exists_ne_zero_mem_line (c : Frame σ m) (k : Fin m) :
    ∃ v : Fin m → K, v ≠ 0 ∧ c.line k = K ∙ v :=
  exists_eq_span_of_finrank_eq_one (c.finrank_line k)

theorem exists_gen (hσ : IsUnitaryInvolution σ) (c : Frame σ m) :
    ∃ v : Fin m → Fin m → K, (∀ k, c.line k = K ∙ v k) ∧
      ∀ j k, herm σ (v j) (v k) = if j = k then 1 else 0 := by
  have h1 : ∀ k, ∃ w : Fin m → K, c.line k = K ∙ w ∧ herm σ w w = 1 := by
    intro k
    obtain ⟨u, hu0, hu⟩ := c.exists_ne_zero_mem_line k
    have hne : herm σ u u ≠ 0 := herm_self_ne_zero_of_nondeg_span hu0 (hu ▸ c.nondeg_line k)
    obtain ⟨a, ha⟩ := exists_smul_norm_one hσ hne
    have ha0 : a ≠ 0 := by
      rintro rfl
      rw [zero_smul, herm_zero_left] at ha
      exact zero_ne_one ha
    exact ⟨a • u, by rw [hu, Submodule.span_singleton_smul_eq (IsUnit.mk0 a ha0)], ha⟩
  choose v hv hn using h1
  refine ⟨v, hv, fun j k => ?_⟩
  by_cases hjk : j = k
  · subst hjk
    simpa using hn j
  · rw [ite_eq_right hjk]
    exact c.orth_line j k hjk (v j) (hv j ▸ Submodule.mem_span_singleton_self _) (v k)
      (hv k ▸ Submodule.mem_span_singleton_self _)

end Frame

@[expose] def colMat (v : Fin m → Fin m → K) : Matrix (Fin m) (Fin m) K :=
  Matrix.of fun a k => v k a

omit [Field K] in
theorem colMat_apply (v : Fin m → Fin m → K) (a k : Fin m) : colMat v a k = v k a := rfl

theorem conjTr_colMat_mul_colMat {v : Fin m → Fin m → K}
    (hv : ∀ j k, herm σ (v j) (v k) = if j = k then 1 else 0) :
    conjTr σ (colMat v) * colMat v = 1 := by
  ext j k
  rw [Matrix.mul_apply, Matrix.one_apply, ← hv j k, herm]
  simp [conjTr, colMat]

theorem colMat_mul_conjTr_colMat {v : Fin m → Fin m → K}
    (hv : ∀ j k, herm σ (v j) (v k) = if j = k then 1 else 0) :
    colMat v * conjTr σ (colMat v) = 1 :=
  mul_eq_one_comm.mp (conjTr_colMat_mul_colMat hv)

theorem sum_herm_smul_eq {v : Fin m → Fin m → K}
    (hv : ∀ j k, herm σ (v j) (v k) = if j = k then 1 else 0) (x : Fin m → K) :
    ∑ k, herm σ (v k) x • v k = x := by
  have h := congrFun (congrArg (fun M => M *ᵥ x) (colMat_mul_conjTr_colMat hv))
  funext a
  have := h a
  rw [← Matrix.mulVec_mulVec, Matrix.one_mulVec] at this
  rw [← this]
  simp [Matrix.mulVec, dotProduct, colMat, conjTr, herm, Finset.sum_apply, mul_comm]

namespace Frame

variable {c d : Frame σ m}

@[expose] def spanAt (c : Frame σ m) (S : Finset (Fin m)) : Submodule K (Fin m → K) :=
  S.sup c.line

theorem spanAt_empty (c : Frame σ m) : c.spanAt ∅ = ⊥ := Finset.sup_empty

theorem spanAt_insert (c : Frame σ m) (a : Fin m) (S : Finset (Fin m)) :
    c.spanAt (insert a S) = c.line a ⊔ c.spanAt S := by
  classical
  exact Finset.sup_insert

theorem spanAt_singleton (c : Frame σ m) (a : Fin m) : c.spanAt {a} = c.line a :=
  Finset.sup_singleton

theorem spanAt_congr {S : Finset (Fin m)} (h : ∀ k ∈ S, c.line k = d.line k) :
    c.spanAt S = d.spanAt S :=
  Finset.sup_congr rfl h

theorem spanAt_pair (c : Frame σ m) (a b : Fin m) : c.spanAt {a, b} = c.line a ⊔ c.line b := by
  rw [spanAt_insert, spanAt_singleton]

theorem line_le_spanAt {a : Fin m} {S : Finset (Fin m)} (h : a ∈ S) : c.line a ≤ c.spanAt S :=
  Finset.le_sup h

theorem spanAt_mono {S T : Finset (Fin m)} (h : S ⊆ T) : c.spanAt S ≤ c.spanAt T :=
  Finset.sup_mono h

theorem orth_spanAt {l : Fin m} {S : Finset (Fin m)} (hl : l ∉ S) :
    Orth σ (c.line l) (c.spanAt S) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    rw [spanAt_empty]
    intro u _ v hv
    rw [Submodule.mem_bot] at hv
    rw [hv, herm_zero_right]
  | insert a S haS ih =>
    rw [spanAt_insert]
    refine Orth.sup_right (c.orth_line l a ?_) (ih fun h => hl (Finset.mem_insert_of_mem h))
    rintro rfl
    exact hl (Finset.mem_insert_self _ _)

theorem orth_spanAt' {l : Fin m} {S : Finset (Fin m)} (hl : l ∉ S) :
    Orth σ (c.spanAt S) (c.line l) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    rw [spanAt_empty]
    intro u hu v _
    rw [Submodule.mem_bot] at hu
    rw [hu, herm_zero_left]
  | insert a S haS ih =>
    rw [spanAt_insert]
    refine Orth.sup_left (c.orth_line a l ?_) (ih fun h => hl (Finset.mem_insert_of_mem h))
    rintro rfl
    exact hl (Finset.mem_insert_self _ _)

variable (hσ : IsUnitaryInvolution σ)
include hσ

theorem mem_spanAt_iff {S : Finset (Fin m)} {y : Fin m → K} :
    y ∈ c.spanAt S ↔ ∀ l ∉ S, ∀ w ∈ c.line l, herm σ w y = 0 := by
  refine ⟨fun hy l hl w hw => c.orth_spanAt hl w hw y hy, fun h => ?_⟩
  obtain ⟨v, hvl, hv⟩ := c.exists_gen hσ
  rw [← sum_herm_smul_eq hv y]
  refine Submodule.sum_mem _ fun k _ => ?_
  by_cases hk : k ∈ S
  · exact Submodule.smul_mem _ _ (c.line_le_spanAt hk (hvl k ▸ Submodule.mem_span_singleton_self _))
  · rw [h k hk (v k) (hvl k ▸ Submodule.mem_span_singleton_self _), zero_smul]
    exact Submodule.zero_mem _

theorem le_spanAt_iff {S : Finset (Fin m)} {x : Submodule K (Fin m → K)} :
    x ≤ c.spanAt S ↔ ∀ l ∉ S, Orth σ (c.line l) x :=
  ⟨fun hx l hl w hw _ hy => (c.mem_spanAt_iff hσ).1 (hx hy) l hl w hw,
    fun h y hy => (c.mem_spanAt_iff hσ).2 fun l hl w hw => h l hl w hw y hy⟩

theorem spanAt_univ : c.spanAt Finset.univ = ⊤ := by
  rw [eq_top_iff]
  exact fun _ _ => (c.mem_spanAt_iff hσ).2 fun l hl => absurd (Finset.mem_univ l) hl

theorem nondeg_spanAt (S : Finset (Fin m)) : Nondeg σ (c.spanAt S) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    rw [spanAt_empty]
    intro s hs _
    exact (Submodule.mem_bot K).1 hs
  | insert a S haS ih =>
    rw [spanAt_insert]
    exact Nondeg.sup_of_orth hσ (c.nondeg_line a) ih (c.orth_spanAt haS)

omit hσ in
theorem disjoint_line_spanAt {a : Fin m} {S : Finset (Fin m)} (ha : a ∉ S) :
    Disjoint (c.line a) (c.spanAt S) := by
  rw [Submodule.disjoint_def]
  intro x hxa hxS
  exact c.nondeg_line a x hxa fun t ht => c.orth_spanAt' ha x hxS t ht

omit hσ in
theorem finrank_spanAt (S : Finset (Fin m)) : finrank K (c.spanAt S) = S.card := by
  classical
  induction S using Finset.induction_on with
  | empty => rw [spanAt_empty, finrank_bot, Finset.card_empty]
  | insert a S haS ih =>
    rw [spanAt_insert, finrank_sup_of_disjoint (c.disjoint_line_spanAt haS), ih,
      c.finrank_line, Finset.card_insert_of_notMem haS]
    omega

theorem spanAt_eq_of_agree {S : Finset (Fin m)} (h : ∀ k ∉ S, c.line k = d.line k) :
    c.spanAt S = d.spanAt S := by
  refine le_antisymm ((d.le_spanAt_iff hσ).2 fun l hl => ?_)
    ((c.le_spanAt_iff hσ).2 fun l hl => ?_)
  · rw [← h l hl]
    exact c.orth_spanAt hl
  · rw [h l hl]
    exact d.orth_spanAt hl

theorem line_eq_of_agree_except {a : Fin m} (h : ∀ k, k ≠ a → c.line k = d.line k) :
    c.line a = d.line a := by
  have h1 := c.spanAt_eq_of_agree hσ (S := {a}) fun k hk => h k (by simpa using hk)
  simpa [spanAt_singleton] using h1

end Frame

section Replace

variable (hσ : IsUnitaryInvolution σ)
include hσ

theorem exists_orth_complement_in_plane {P x : Submodule K (Fin m → K)} (hP : finrank K P = 2)
    (hPnd : Nondeg σ P) (hx : x ∈ nsPts σ P) :
    ∃ y ∈ nsPts σ P, Orth σ x y ∧ x ⊔ y = P := by
  obtain ⟨a, ha, haP, rfl⟩ := mem_nsPts_iff.mp hx
  have hdim := finrank_eq_inf_perp_add_one hσ haP ha
  refine ⟨P ⊓ perp σ (K ∙ a), ⟨inf_le_left, by omega,
    Nondeg.inf_perp_span_singleton hσ haP ha hPnd⟩, ?_, span_sup_inf_perp hσ haP ha⟩
  intro u hu v hv
  exact herm_eq_zero_comm σ hσ.invol (hv.2 u hu)

end Replace

namespace Frame

variable {c d : Frame σ m}

@[expose] def replaceLine (c : Frame σ m) (i j : Fin m) (x y : Submodule K (Fin m → K)) :
    Fin m → Submodule K (Fin m → K) :=
  fun k => if k = i then x else if k = j then y else c.line k

theorem replaceLine_left (c : Frame σ m) {i j : Fin m} (x y : Submodule K (Fin m → K)) :
    c.replaceLine i j x y i = x := by
  simp [replaceLine]

theorem replaceLine_right (c : Frame σ m) {i j : Fin m} (hij : i ≠ j)
    (x y : Submodule K (Fin m → K)) : c.replaceLine i j x y j = y := by
  simp [replaceLine, hij.symm]

theorem replaceLine_of_ne (c : Frame σ m) {i j k : Fin m} (hki : k ≠ i) (hkj : k ≠ j)
    (x y : Submodule K (Fin m → K)) : c.replaceLine i j x y k = c.line k := by
  simp [replaceLine, hki, hkj]

@[expose] def replace (hσ : IsUnitaryInvolution σ) (c : Frame σ m) (i j : Fin m) (hij : i ≠ j)
    (x y : Submodule K (Fin m → K)) (hx : x ∈ nsPts σ (c.line i ⊔ c.line j))
    (hy : y ∈ nsPts σ (c.line i ⊔ c.line j)) (hxy : Orth σ x y) : Frame σ m where
  line := c.replaceLine i j x y
  finrank_line k := by
    by_cases hki : k = i
    · subst hki
      rw [replaceLine_left]
      exact hx.2.1
    · by_cases hkj : k = j
      · subst hkj
        rw [replaceLine_right c hij]
        exact hy.2.1
      · rw [replaceLine_of_ne c hki hkj]
        exact c.finrank_line k
  nondeg_line k := by
    by_cases hki : k = i
    · subst hki
      rw [replaceLine_left]
      exact hx.2.2
    · by_cases hkj : k = j
      · subst hkj
        rw [replaceLine_right c hij]
        exact hy.2.2
      · rw [replaceLine_of_ne c hki hkj]
        exact c.nondeg_line k
  orth_line k l hkl := by
    have hP : ∀ k, k ≠ i → k ≠ j →
        Orth σ (c.line k) (c.line i ⊔ c.line j) ∧ Orth σ (c.line i ⊔ c.line j) (c.line k) :=
      fun k hki hkj => ⟨Orth.sup_right (c.orth_line k i hki) (c.orth_line k j hkj),
        Orth.sup_left (c.orth_line i k (Ne.symm hki)) (c.orth_line j k (Ne.symm hkj))⟩
    have hyx : Orth σ y x := Orth.symm hσ hxy
    have hxo : ∀ k, k ≠ i → k ≠ j → Orth σ (c.line k) x ∧ Orth σ x (c.line k) :=
      fun k hki hkj => ⟨(hP k hki hkj).1.mono le_rfl hx.1, (hP k hki hkj).2.mono hx.1 le_rfl⟩
    have hyo : ∀ k, k ≠ i → k ≠ j → Orth σ (c.line k) y ∧ Orth σ y (c.line k) :=
      fun k hki hkj => ⟨(hP k hki hkj).1.mono le_rfl hy.1, (hP k hki hkj).2.mono hy.1 le_rfl⟩
    by_cases hki : k = i
    · subst hki
      rw [replaceLine_left]
      by_cases hlj : l = j
      · subst hlj
        rw [replaceLine_right c hij]
        exact hxy
      · rw [replaceLine_of_ne c (Ne.symm hkl) hlj]
        exact (hxo l (Ne.symm hkl) hlj).2
    · by_cases hkj : k = j
      · subst hkj
        rw [replaceLine_right c hij]
        by_cases hli : l = i
        · subst hli
          rw [replaceLine_left]
          exact hyx
        · rw [replaceLine_of_ne c hli (Ne.symm hkl)]
          exact (hyo l hli (Ne.symm hkl)).2
      · rw [replaceLine_of_ne c hki hkj]
        by_cases hli : l = i
        · subst hli
          rw [replaceLine_left]
          exact (hxo k hki hkj).1
        · by_cases hlj : l = j
          · subst hlj
            rw [replaceLine_right c hij]
            exact (hyo k hki hkj).1
          · rw [replaceLine_of_ne c hli hlj]
            exact c.orth_line k l hkl

@[expose] def glueLine (c e : Frame σ m) (S : Finset (Fin m)) : Fin m → Submodule K (Fin m → K) :=
  fun k => if k ∈ S then e.line k else c.line k

theorem glueLine_of_mem (c e : Frame σ m) {S : Finset (Fin m)} {k : Fin m} (hk : k ∈ S) :
    glueLine c e S k = e.line k :=
  ite_eq_left hk

theorem glueLine_of_not_mem (c e : Frame σ m) {S : Finset (Fin m)} {k : Fin m} (hk : k ∉ S) :
    glueLine c e S k = c.line k :=
  ite_eq_right hk

@[expose] def glue (c e : Frame σ m) (S : Finset (Fin m)) (h : e.spanAt S = c.spanAt S) :
    Frame σ m where
  line := glueLine c e S
  finrank_line k := by
    by_cases hk : k ∈ S
    · rw [glueLine_of_mem c e hk]
      exact e.finrank_line k
    · rw [glueLine_of_not_mem c e hk]
      exact c.finrank_line k
  nondeg_line k := by
    by_cases hk : k ∈ S
    · rw [glueLine_of_mem c e hk]
      exact e.nondeg_line k
    · rw [glueLine_of_not_mem c e hk]
      exact c.nondeg_line k
  orth_line k l hkl := by
    by_cases hk : k ∈ S <;> by_cases hl : l ∈ S
    · rw [glueLine_of_mem c e hk, glueLine_of_mem c e hl]
      exact e.orth_line k l hkl
    · rw [glueLine_of_mem c e hk, glueLine_of_not_mem c e hl]
      exact (c.orth_spanAt' hl).mono ((e.line_le_spanAt hk).trans h.le) le_rfl
    · rw [glueLine_of_not_mem c e hk, glueLine_of_mem c e hl]
      exact (c.orth_spanAt hk).mono le_rfl ((e.line_le_spanAt hl).trans h.le)
    · rw [glueLine_of_not_mem c e hk, glueLine_of_not_mem c e hl]
      exact c.orth_line k l hkl

theorem glue_line_of_mem (c e : Frame σ m) {S : Finset (Fin m)} (h : e.spanAt S = c.spanAt S)
    {k : Fin m} (hk : k ∈ S) : (c.glue e S h).line k = e.line k :=
  glueLine_of_mem c e hk

theorem glue_line_of_not_mem (c e : Frame σ m) {S : Finset (Fin m)} (h : e.spanAt S = c.spanAt S)
    {k : Fin m} (hk : k ∉ S) : (c.glue e S h).line k = c.line k :=
  glueLine_of_not_mem c e hk

end Frame

end CFSG.ClassicalInvolution.Phan
