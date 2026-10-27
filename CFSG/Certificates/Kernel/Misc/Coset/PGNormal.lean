module

public import CFSG.Certificates.CosetTablePresented

public section

namespace CFSG.KC.MiscCoset

open CFSG.CosetTable

variable {m : ℕ}

@[expose] def conjTailOK (A : List (Fin m)) (c a : Fin m) (w : List (Fin m × Bool)) : Bool :=
  w.take 3 == [(c, false), (a, true), (c, true)] && (w.drop 3).all fun l => decide (l.1 ∈ A)

@[expose] def commOK (c a : Fin m) (w : List (Fin m × Bool)) : Bool :=
  w == [(a, false), (c, true), (a, true), (c, false)]

@[expose] def conjOK (A : List (Fin m)) (c a : Fin m) (w : List (Fin m × Bool)) : Bool :=
  conjTailOK A c a w || commOK c a w

section Presented

variable {ws : List (List (Fin m × Bool))}

variable (ws) in
abbrev pgRels : Set (FreeGroup (Fin m)) := {r : FreeGroup (Fin m) | r ∈ ws.map FreeGroup.mk}

theorem pg_mk_cons_true (j : Fin m) (w : List (Fin m × Bool)) :
    PresentedGroup.mk (pgRels ws) (FreeGroup.mk ((j, true) :: w)) =
      PresentedGroup.of j * PresentedGroup.mk (pgRels ws) (FreeGroup.mk w) := by
  rw [show FreeGroup.mk ((j, true) :: w) = FreeGroup.of j * FreeGroup.mk w from rfl, map_mul]
  rfl

theorem pg_mk_cons_false (j : Fin m) (w : List (Fin m × Bool)) :
    PresentedGroup.mk (pgRels ws) (FreeGroup.mk ((j, false) :: w)) =
      (PresentedGroup.of j)⁻¹ * PresentedGroup.mk (pgRels ws) (FreeGroup.mk w) := by
  rw [show FreeGroup.mk ((j, false) :: w) = (FreeGroup.of j)⁻¹ * FreeGroup.mk w from rfl, map_mul,
    map_inv]
  rfl

theorem pg_mk_nil : PresentedGroup.mk (pgRels ws) (FreeGroup.mk ([] : List (Fin m × Bool))) = 1 := by
  rw [← FreeGroup.one_eq_mk, map_one]

theorem pg_mk_rel {w : List (Fin m × Bool)} (hw : w ∈ ws) :
    PresentedGroup.mk (pgRels ws) (FreeGroup.mk w) = 1 :=
  PresentedGroup.one_of_mem (List.mem_map_of_mem hw)

theorem pg_mk_mem_genSub {A : List (Fin m)} :
    ∀ (w : List (Fin m × Bool)), (∀ l ∈ w, l.1 ∈ A) →
      PresentedGroup.mk (pgRels ws) (FreeGroup.mk w) ∈ genSub (pgRels ws) A
  | [], _ => by rw [pg_mk_nil]; exact one_mem _
  | (j, b) :: w, hw => by
    have hj : PresentedGroup.of j ∈ genSub (pgRels ws) A :=
      Subgroup.subset_closure ⟨j, hw _ List.mem_cons_self, rfl⟩
    have ih := pg_mk_mem_genSub w fun l hl => hw l (List.mem_cons_of_mem _ hl)
    cases b
    · rw [pg_mk_cons_false]
      exact mul_mem (inv_mem hj) ih
    · rw [pg_mk_cons_true]
      exact mul_mem hj ih

theorem pg_mk_replicate (c : Fin m) (k : ℕ) :
    PresentedGroup.mk (pgRels ws) (FreeGroup.mk (List.replicate k (c, true))) =
      (PresentedGroup.of c) ^ k := by
  induction k with
  | zero => exact pg_mk_nil
  | succ k ih => rw [List.replicate_succ, pg_mk_cons_true, ih, pow_succ']

theorem conj_mem_of_conjOK {A : List (Fin m)} {c a : Fin m} (ha : a ∈ A)
    {w : List (Fin m × Bool)} (hw : w ∈ ws) (h : conjOK A c a w = true) :
    (PresentedGroup.of c)⁻¹ * PresentedGroup.of a * PresentedGroup.of c ∈ genSub (pgRels ws) A := by
  have hrel := pg_mk_rel hw
  simp only [conjOK, Bool.or_eq_true] at h
  rcases h with h | h
  · simp only [conjTailOK, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_true_eq]
      at h
    obtain ⟨h3, hv⟩ := h
    rw [← List.take_append_drop 3 w, h3] at hrel
    simp only [List.cons_append, List.nil_append, pg_mk_cons_true, pg_mk_cons_false] at hrel
    have e : (PresentedGroup.of c)⁻¹ * PresentedGroup.of a * PresentedGroup.of c =
        (PresentedGroup.mk (pgRels ws) (FreeGroup.mk (w.drop 3)))⁻¹ := by
      rw [eq_inv_iff_mul_eq_one, ← hrel]
      group
    rw [e]
    exact inv_mem (pg_mk_mem_genSub _ hv)
  · simp only [commOK, beq_iff_eq] at h
    subst h
    simp only [pg_mk_cons_true, pg_mk_cons_false, pg_mk_nil, mul_one] at hrel
    have e : (PresentedGroup.of c)⁻¹ * PresentedGroup.of a * PresentedGroup.of c =
        (PresentedGroup.of a : PresentedGroup (pgRels ws)) := by
      have h1 := inv_mul_eq_one.mp (show (PresentedGroup.of a : PresentedGroup (pgRels ws))⁻¹ *
          (PresentedGroup.of c * PresentedGroup.of a * (PresentedGroup.of c)⁻¹) = 1 by
        rw [← hrel]
        group)
      nth_rewrite 1 [h1]
      group
    rw [e]
    exact Subgroup.subset_closure ⟨a, ha, rfl⟩

theorem conj_le_of_conjOK {A : List (Fin m)} {c : Fin m}
    (hA : ∀ a ∈ A, ws.any (conjOK A c a) = true) :
    ∀ x ∈ genSub (pgRels ws) A, (PresentedGroup.of c)⁻¹ * x * PresentedGroup.of c ∈ genSub (pgRels ws) A := by
  intro x hx
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨a, ha, rfl⟩ := hx
    obtain ⟨w, hw, h⟩ := List.any_eq_true.1 (hA a ha)
    exact conj_mem_of_conjOK ha hw h
  | one => simp
  | mul x y _ _ hx hy =>
    have e : (PresentedGroup.of c)⁻¹ * (x * y) * PresentedGroup.of c =
        ((PresentedGroup.of c)⁻¹ * x * PresentedGroup.of c) *
          ((PresentedGroup.of c)⁻¹ * y * PresentedGroup.of c) := by group
    rw [e]
    exact mul_mem hx hy
  | inv x _ hx =>
    have e : (PresentedGroup.of c)⁻¹ * x⁻¹ * PresentedGroup.of c =
        ((PresentedGroup.of c)⁻¹ * x * PresentedGroup.of c)⁻¹ := by group
    rw [e]
    exact inv_mem hx

theorem genSub_normal {A : List (Fin m)} {c : Fin m} (hall : ∀ j : Fin m, j ∈ A ∨ j = c)
    (hA : ∀ a ∈ A, ws.any (conjOK A c a) = true) {k : ℕ} (hk : 0 < k)
    (hck : List.replicate k (c, true) ∈ ws) : (genSub (pgRels ws) A).Normal := by
  set g : PresentedGroup (pgRels ws) := PresentedGroup.of c
  have hg : g ^ k = 1 := by rw [← pg_mk_replicate, pg_mk_rel hck]
  have h1 := conj_le_of_conjOK hA
  have hj : ∀ j : ℕ, ∀ x ∈ genSub (pgRels ws) A, (g ^ j)⁻¹ * x * g ^ j ∈ genSub (pgRels ws) A := by
    intro j
    induction j with
    | zero => intro x hx; simpa using hx
    | succ j ih =>
      intro x hx
      have e : (g ^ (j + 1))⁻¹ * x * g ^ (j + 1) = g⁻¹ * ((g ^ j)⁻¹ * x * g ^ j) * g := by
        rw [pow_succ]
        group
      rw [e]
      exact h1 _ (ih x hx)
  have hgi : g ^ (k - 1) = g⁻¹ := by
    rw [eq_inv_iff_mul_eq_one, ← pow_succ, Nat.sub_add_cancel hk, hg]
  have h2 : ∀ x ∈ genSub (pgRels ws) A, g * x * g⁻¹ ∈ genSub (pgRels ws) A := by
    intro x hx
    have := hj (k - 1) x hx
    rwa [hgi, inv_inv] at this
  have hn : g ∈ Subgroup.normalizer
      ((genSub (pgRels ws) A : Subgroup (PresentedGroup (pgRels ws))) :
        Set (PresentedGroup (pgRels ws))) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    refine ⟨h2 x, fun hx => ?_⟩
    have := h1 _ hx
    rwa [show g⁻¹ * (g * x * g⁻¹) * g = x by group] at this
  rw [← Subgroup.normalizer_eq_top_iff, eq_top_iff, ← PresentedGroup.closure_range_of,
    Subgroup.closure_le]
  rintro _ ⟨j, rfl⟩
  rcases hall j with hj | rfl
  · exact Subgroup.le_normalizer (Subgroup.subset_closure ⟨j, hj, rfl⟩)
  · exact hn

theorem genSub_index_le_of_normal {A : List (Fin m)} {c : Fin m}
    (hall : ∀ j : Fin m, j ∈ A ∨ j = c) (hA : ∀ a ∈ A, ws.any (conjOK A c a) = true) {k : ℕ}
    (hk : 0 < k) (hck : List.replicate k (c, true) ∈ ws) :
    (genSub (pgRels ws) A).FiniteIndex ∧ (genSub (pgRels ws) A).index ≤ k := by
  have := genSub_normal hall hA hk hck
  set K := genSub (pgRels ws) A
  set q : PresentedGroup (pgRels ws) ⧸ K := ((PresentedGroup.of c : PresentedGroup (pgRels ws)) : _ ⧸ K)
  have hq : q ^ k = 1 := by
    rw [← QuotientGroup.mk_pow, ← pg_mk_replicate, pg_mk_rel hck]
    rfl
  have htop : (⊤ : Subgroup (PresentedGroup (pgRels ws) ⧸ K)) = Subgroup.zpowers q := by
    rw [eq_comm, eq_top_iff]
    intro y hy'
    clear hy'
    induction y using QuotientGroup.induction_on with
    | H y =>
      have hy : y ∈ Subgroup.closure
          (Set.range (PresentedGroup.of : Fin m → PresentedGroup (pgRels ws))) := by
        rw [PresentedGroup.closure_range_of]
        exact Subgroup.mem_top y
      induction hy using Subgroup.closure_induction with
      | mem x hx =>
        obtain ⟨j, rfl⟩ := hx
        rcases hall j with hj | rfl
        · have hjK : (PresentedGroup.of j : PresentedGroup (pgRels ws)) ∈ K :=
            Subgroup.subset_closure ⟨j, hj, rfl⟩
          rw [(QuotientGroup.eq_one_iff _).2 hjK]
          exact one_mem _
        · exact Subgroup.mem_zpowers _
      | one => exact one_mem _
      | mul x y _ _ hx hy =>
        rw [QuotientGroup.mk_mul]
        exact mul_mem hx hy
      | inv x _ hx =>
        rw [QuotientGroup.mk_inv]
        exact inv_mem hx
  have hfo : IsOfFinOrder q := isOfFinOrder_iff_pow_eq_one.2 ⟨k, hk, hq⟩
  have hidx : K.index = orderOf q := by
    rw [← Nat.card_zpowers, ← htop, Subgroup.card_top]
    rfl
  have hle : orderOf q ≤ k := orderOf_le_of_pow_eq_one hk hq
  exact ⟨⟨by rw [hidx]; exact (orderOf_pos_iff.2 hfo).ne'⟩, hidx ▸ hle⟩

theorem genSub_sup_eq_top {A S : List (Fin m)} (h : ∀ j : Fin m, j ∈ A ∨ j ∈ S) :
    genSub (pgRels ws) A ⊔ genSub (pgRels ws) S = ⊤ := by
  rw [eq_top_iff, ← PresentedGroup.closure_range_of, Subgroup.closure_le]
  rintro _ ⟨j, rfl⟩
  rcases h j with hj | hj
  · exact Subgroup.mem_sup_left (Subgroup.subset_closure ⟨j, hj, rfl⟩)
  · exact Subgroup.mem_sup_right (Subgroup.subset_closure ⟨j, hj, rfl⟩)

end Presented

section Map

variable {n : ℕ} {ws : List (List (Fin m × Bool))} {ws' : List (List (Fin n × Bool))}

noncomputable def pgMap (f : Fin m → Fin n)
    (hrel : ∀ w ∈ ws, w.map (fun l => (f l.1, l.2)) ∈ ws') : PG m ws →* PG n ws' :=
  PresentedGroup.toGroup (f := fun i => (PresentedGroup.of (f i) : PG n ws')) (by
    intro r hr
    obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hr
    have e : FreeGroup.lift (fun i => (PresentedGroup.of (f i) : PG n ws')) =
        (PresentedGroup.mk _).comp (FreeGroup.map f) :=
      FreeGroup.ext_hom _ _ fun i => by
        rw [FreeGroup.lift_apply_of, MonoidHom.comp_apply, FreeGroup.map.of]
        rfl
    rw [e, MonoidHom.comp_apply, FreeGroup.map.mk]
    exact PresentedGroup.one_of_mem (List.mem_map_of_mem (hrel w hw)))

theorem pgMap_of (f : Fin m → Fin n) (hrel : ∀ w ∈ ws, w.map (fun l => (f l.1, l.2)) ∈ ws')
    (i : Fin m) : pgMap f hrel (PresentedGroup.of i) = PresentedGroup.of (f i) :=
  PresentedGroup.toGroup.of _

theorem map_genSub_le (f : Fin m → Fin n) (hrel : ∀ w ∈ ws, w.map (fun l => (f l.1, l.2)) ∈ ws')
    {S : List (Fin m)} {T : List (Fin n)} (hST : ∀ i ∈ S, f i ∈ T) :
    (genSub {r : FreeGroup (Fin m) | r ∈ ws.map FreeGroup.mk} S).map (pgMap f hrel) ≤
      genSub {r : FreeGroup (Fin n) | r ∈ ws'.map FreeGroup.mk} T := by
  rw [MonoidHom.map_closure, Subgroup.closure_le]
  rintro _ ⟨_, ⟨i, hi, rfl⟩, rfl⟩
  rw [pgMap_of]
  exact Subgroup.subset_closure ⟨f i, hST i hi, rfl⟩

theorem genSub_le_range (f : Fin m → Fin n) (hrel : ∀ w ∈ ws, w.map (fun l => (f l.1, l.2)) ∈ ws')
    {T : List (Fin n)} (hT : ∀ j ∈ T, ∃ i, f i = j) :
    genSub {r : FreeGroup (Fin n) | r ∈ ws'.map FreeGroup.mk} T ≤ (pgMap f hrel).range := by
  rw [Subgroup.closure_le]
  rintro _ ⟨j, hj, rfl⟩
  obtain ⟨i, rfl⟩ := hT j hj
  exact ⟨PresentedGroup.of i, pgMap_of f hrel i⟩

end Map

theorem index_le_of_hom {O G : Type*} [Group O] [Group G] (h : O →* G) (P : Subgroup O)
    (H K : Subgroup G) [K.Normal] (hK : K ≤ h.range) (hKH : K ⊔ H = ⊤) (hP : P.map h ≤ H)
    [P.FiniteIndex] : H.FiniteIndex ∧ H.index ≤ P.index := by
  have key : ∀ g : G, ∃ o : O, (h o)⁻¹ * g ∈ H := by
    intro g
    have hg : g ∈ ((K ⊔ H : Subgroup G) : Set G) := by rw [hKH]; exact Subgroup.mem_top g
    rw [Subgroup.normal_mul] at hg
    obtain ⟨x, hx, y, hy, rfl⟩ := hg
    obtain ⟨o, ho⟩ := hK hx
    refine ⟨o, ?_⟩
    rwa [ho, inv_mul_cancel_left]
  let F : O ⧸ P → G ⧸ H := fun q => Quotient.liftOn' q (fun o => ((h o : G) : G ⧸ H))
    (fun a b hab => by
      rw [QuotientGroup.leftRel_apply] at hab
      apply QuotientGroup.eq.2
      rw [← map_inv, ← map_mul]
      exact hP ⟨_, hab, rfl⟩)
  have hs : Function.Surjective F := by
    intro y
    induction y using QuotientGroup.induction_on with
    | H g =>
      obtain ⟨o, ho⟩ := key g
      exact ⟨(o : O ⧸ P), QuotientGroup.eq.2 ho⟩
  have : Finite (G ⧸ H) := Finite.of_surjective F hs
  exact ⟨Subgroup.finiteIndex_of_finite_quotient, Nat.card_le_card_of_surjective F hs⟩

end CFSG.KC.MiscCoset
