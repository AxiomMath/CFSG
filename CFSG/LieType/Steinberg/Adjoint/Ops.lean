module

public import CFSG.LieType.Steinberg.Adjoint.Cert
public import CFSG.LieType.Chevalley.BraidWalk
public import CFSG.Blueprint.ChevalleyInfinitesimals
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate117

public noncomputable section

namespace CFSG.LieType.Steinberg.Adjoint

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley.RootWalk

variable {τ : Tag}

instance instRingEndRootModule (R : Type*) [CommRing R] :
    Ring (Module.End R (RootModule τ R)) :=
  Module.End.instRing

theorem sum_zipWith_mul (v w : List ℤ) :
    (List.zipWith (· * ·) v w).sum = ∑ j ∈ Finset.range w.length, v.getD j 0 * w.getD j 0 := by
  induction v generalizing w with
  | nil => simp
  | cons a v ih =>
    cases w with
    | nil => simp
    | cons b w =>
      rw [List.zipWith_cons_cons, List.sum_cons, ih, List.length_cons, Finset.sum_range_succ']
      simp [add_comm]

theorem getD_range_map (n : ℕ) (f : ℕ → ℤ) {j : ℕ} (hj : j < n) :
    ((List.range n).map f).getD j 0 = f j := by
  simp [List.getD_eq_getElem?_getD, hj]

theorem getD_map_mul (v : List ℤ) (s : ℤ) (j : ℕ) : (v.map (s * ·)).getD j 0 = s * v.getD j 0 := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases v[j]? <;> simp

theorem getD_zipWith_sub {v w : List ℤ} {n j : ℕ} (hv : v.length = n) (hw : w.length = n)
    (hj : j < n) : (List.zipWith (· - ·) v w).getD j 0 = v.getD j 0 - w.getD j 0 := by
  simp [List.getD_eq_getElem?_getD, hv, hw, hj]

theorem getD_eq_zero_of_forall {v : List ℤ} (h : ∀ x ∈ v, x = 0) (j : ℕ) : v.getD j 0 = 0 := by
  rw [List.getD_eq_getElem?_getD]
  cases hv : v[j]? with
  | none => rfl
  | some x => exact h x (List.mem_of_getElem? hv)

theorem rootVec_of_isRoot' {R : Type*} [CommRing R] {β : Fin τ.rank → ℤ} (hβ : IsRoot τ β) :
    rootVec τ R β = Finsupp.single (Sum.inr ⟨β, hβ⟩) 1 :=
  dite_eq_left hβ

theorem rootVec_of_not_isRoot' {R : Type*} [CommRing R] {β : Fin τ.rank → ℤ}
    (hβ : ¬IsRoot τ β) : rootVec τ R β = 0 :=
  dite_eq_right hβ

@[expose] def pos (α : {v : Fin τ.rank → ℤ // IsRoot τ v}) : ℕ :=
  (RootCertificate.exists_root_eq τ.rootCertificate_check α.2).choose

theorem pos_lt (α : {v : Fin τ.rank → ℤ // IsRoot τ v}) :
    pos α < τ.rootCertificate.roots.length :=
  (RootCertificate.exists_root_eq τ.rootCertificate_check α.2).choose_spec.1

theorem root_pos (α : {v : Fin τ.rank → ℤ // IsRoot τ v}) :
    τ.rootCertificate.root (pos α) = α.1 :=
  (RootCertificate.exists_root_eq τ.rootCertificate_check α.2).choose_spec.2

theorem pos_root {k : ℕ} (hk : k < τ.rootCertificate.roots.length) :
    pos ⟨τ.rootCertificate.root k, isRoot_rootCertificate_root hk⟩ = k :=
  rootCertificate_root_injOn (pos_lt _) hk (root_pos _)

theorem pos_eq_iff {α : {v : Fin τ.rank → ℤ // IsRoot τ v}} {k : ℕ}
    (hk : k < τ.rootCertificate.roots.length) :
    pos α = k ↔ τ.rootCertificate.root k = α.1 := by
  constructor
  · rintro rfl
    exact root_pos α
  · intro h
    exact rootCertificate_root_injOn (pos_lt α) hk ((root_pos α).trans h.symm)

theorem root_simple (j : Fin τ.rank) : τ.rootCertificate.root j = Pi.single j 1 :=
  rootCertificate_basis_table.2.1 j

theorem simple_lt (j : Fin τ.rank) : (j : ℕ) < τ.rootCertificate.roots.length :=
  lt_of_lt_of_le j.2 rootCertificate_basis_table.1

namespace AVec

variable (τ) (R : Type*) [CommRing R]

@[expose] def interp : AVec → RootModule τ R
  | zero => 0
  | root m c => (c : R) • rootVec τ R (τ.rootCertificate.root m)
  | hvec v => ∑ j : Fin τ.rank, (v.getD j 0 : R) • hVec τ R j

@[expose] def WF : AVec → Prop
  | zero => True
  | root m c => c = 0 ∨ m < τ.rootCertificate.roots.length
  | hvec v => v.length = τ.rank

variable {τ R}

@[simp] theorem interp_zero : interp τ R zero = 0 := rfl

@[simp] theorem interp_root (m : ℕ) (c : ℤ) :
    interp τ R (root m c) = (c : R) • rootVec τ R (τ.rootCertificate.root m) := rfl

@[simp] theorem interp_hvec (v : List ℤ) :
    interp τ R (hvec v) = ∑ j : Fin τ.rank, (v.getD j 0 : R) • hVec τ R j := rfl

theorem interp_hvec_of_forall {v : List ℤ} (h : ∀ x ∈ v, x = 0) : interp τ R (hvec v) = 0 := by
  rw [interp_hvec]
  exact Finset.sum_eq_zero fun j _ => by rw [getD_eq_zero_of_forall h, Int.cast_zero, zero_smul]

theorem interp_norm (u : AVec) : interp τ R u.norm = interp τ R u := by
  cases u with
  | zero => rfl
  | root m c =>
    simp only [norm]
    split_ifs with h
    · rw [h, interp_zero, interp_root, Int.cast_zero, zero_smul]
    · rfl
  | hvec v =>
    simp only [norm]
    split_ifs with h
    · rw [interp_zero, interp_hvec_of_forall]
      simpa using h
    · rfl

theorem interp_smul (s : ℤ) (u : AVec) : interp τ R (u.smul s) = (s : R) • interp τ R u := by
  cases u with
  | zero => simp [smul]
  | root m c => simp [smul, interp_norm, mul_smul]
  | hvec v =>
    simp only [smul, interp_norm, interp_hvec, getD_map_mul, Finset.smul_sum, Int.cast_mul,
      smul_smul]

theorem beq_iff {u v : AVec} : u.beq v = true ↔ u = v := by
  cases u <;> cases v <;> simp [beq]

theorem obeq_some_iff {u v : AVec} : obeq (some u) (some v) = true ↔ u = v := by
  simp [obeq, beq_iff]

theorem interp_of_sub {u v w : AVec} (hu : u.WF τ) (hv : v.WF τ) (h : u.sub v = some w) :
    interp τ R w = interp τ R u - interp τ R v := by
  cases u with
  | zero =>
    simp only [sub, Option.some.injEq] at h
    rw [← h, interp_smul, interp_zero]
    simp
  | root m c =>
    cases v with
    | zero =>
      simp only [sub, Option.some.injEq] at h
      rw [← h, interp_zero, sub_zero]
    | root m' c' =>
      simp only [sub] at h
      split_ifs at h with hm
      simp only [Option.some.injEq] at h
      rw [← h, interp_norm, interp_root, interp_root, interp_root, hm, Int.cast_sub, sub_smul]
    | hvec w' => simp [sub] at h
  | hvec v' =>
    cases v with
    | zero =>
      simp only [sub, Option.some.injEq] at h
      rw [← h, interp_zero, sub_zero]
    | root m' c' => simp [sub] at h
    | hvec w' =>
      simp only [sub, Option.some.injEq] at h
      simp only [WF] at hu hv
      rw [← h, interp_norm, interp_hvec, interp_hvec, interp_hvec, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [getD_zipWith_sub hu hv j.2, Int.cast_sub, sub_smul]

theorem WF.norm {u : AVec} (hu : u.WF τ) : u.norm.WF τ := by
  cases u with
  | zero => trivial
  | root m c =>
    simp only [AVec.norm]
    split_ifs
    · trivial
    · exact hu
  | hvec v =>
    simp only [AVec.norm]
    split_ifs
    · trivial
    · exact hu

theorem WF.smul {u : AVec} (hu : u.WF τ) (s : ℤ) : (u.smul s).WF τ := by
  cases u with
  | zero => trivial
  | root m c =>
    simp only [AVec.smul]
    refine WF.norm ?_
    rcases hu with rfl | hm
    · exact Or.inl (mul_zero s)
    · exact Or.inr hm
  | hvec v =>
    simp only [AVec.smul]
    refine WF.norm ?_
    simp only [WF, List.length_map] at hu ⊢
    exact hu

end AVec

open AVec

@[expose] def ofLabel : Label τ → AVec
  | .inl j => .hvec (AdjData.hUnit j)
  | .inr α => .root (pos α) 1

theorem hUnit_length (j : Fin τ.rank) : (AdjData.hUnit j).length = τ.rank := by
  simp [AdjData.hUnit]

theorem hUnit_getD (j : Fin τ.rank) (m : Fin τ.rank) :
    (AdjData.hUnit j).getD m 0 = if m = j then 1 else 0 := by
  rw [AdjData.hUnit, getD_range_map _ _ m.2]
  simp only [Fin.val_inj]

theorem ofLabel_wf (b : Label τ) : (ofLabel b).WF τ := by
  rcases b with j | α
  · exact hUnit_length j
  · exact Or.inr (pos_lt α)

theorem interp_ofLabel (R : Type*) [CommRing R] (b : Label τ) :
    (ofLabel b).interp τ R = Finsupp.single b 1 := by
  rcases b with j | ⟨α, hα⟩
  · simp only [ofLabel, interp_hvec, hUnit_getD]
    simp [hVec]
  · simp only [ofLabel, interp_root, Int.cast_one, one_smul]
    rw [root_pos, rootVec_of_isRoot' hα]

theorem ofLabel_mem_basis (b : Label τ) : ofLabel b ∈ AdjData.basis τ := by
  rcases b with j | α
  · exact List.mem_append_right _ (List.mem_map.2 ⟨j, List.mem_finRange j, rfl⟩)
  · exact List.mem_append_left _ (List.mem_map.2 ⟨pos α, List.mem_range.2 (pos_lt α), rfl⟩)

namespace AdjData

variable (D : AdjData τ) (R : Type*) [CommRing R]

@[expose] def recOp (k : ℕ) : Module.End R (RootModule τ R) :=
  Finsupp.linearCombination R fun b => (D.act k (ofLabel b)).interp τ R

variable {R}

theorem recOp_single (k : ℕ) (b : Label τ) :
    D.recOp R k (Finsupp.single b 1) = (D.act k (ofLabel b)).interp τ R := by
  rw [recOp, Finsupp.linearCombination_single, one_smul]

theorem act_eq (k : ℕ) (u : AVec) : D.act k u = D.actM (D.opNat k) k u := rfl

theorem actM_root_interp (M k b : ℕ) (c : ℤ) :
    (D.actM M k (.root b c)).interp τ R = (c : R) • (D.actM M k (.root b 1)).interp τ R := by
  simp only [actM]
  split_ifs
  · simp only [interp_norm, interp_hvec, getD_map_mul, Int.cast_mul, one_mul, Finset.smul_sum,
      smul_smul, List.map_id']
  · simp
  · simp only [interp_norm, interp_root, Int.cast_mul, one_mul, mul_smul]

theorem hpart_length (k : ℕ) : (D.hpart k).length = τ.rank := by
  simp [hpart]

theorem sum_zipWith_hUnit (j : Fin τ.rank) {w : List ℤ} (hw : w.length = τ.rank) :
    (List.zipWith (· * ·) (hUnit j) w).sum = w.getD j 0 := by
  rw [sum_zipWith_mul, hw, ← Fin.sum_univ_eq_sum_range (fun m => (hUnit j).getD m 0 * w.getD m 0)]
  simp only [hUnit_getD, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ,
    ite_true]

theorem actM_hvec_interp (M k : ℕ) (v : List ℤ) :
    (D.actM M k (.hvec v)).interp τ R =
      (((List.zipWith (· * ·) v (D.hpart k)).sum : ℤ) : R) •
        rootVec τ R (τ.rootCertificate.root k) := by
  simp only [actM, interp_norm, interp_root]

theorem recOp_interp (k : ℕ) {u : AVec} (hu : u.WF τ) :
    D.recOp R k (u.interp τ R) = (D.act k u).interp τ R := by
  cases u with
  | zero => simp [act, actM]
  | root m c =>
    rw [act_eq, actM_root_interp]
    rcases hu with rfl | hm
    · simp
    · rw [interp_root, rootVec_of_isRoot' (isRoot_rootCertificate_root hm), map_smul,
        recOp_single]
      simp only [ofLabel]
      rw [pos_root hm, act_eq]
  | hvec v =>
    rw [interp_hvec, map_sum, act_eq, actM_hvec_interp, sum_zipWith_mul, hpart_length,
      ← Fin.sum_univ_eq_sum_range (fun m => v.getD m 0 * (D.hpart k).getD m 0), Int.cast_sum,
      Finset.sum_smul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul, hVec, recOp_single]
    simp only [ofLabel]
    rw [act_eq, actM_hvec_interp, sum_zipWith_hUnit j (D.hpart_length k), smul_smul,
      Int.cast_mul]

variable {D}

theorem checkTables_at (hT : D.checkTables = true) {b : ℕ}
    (hb : b < τ.rootCertificate.roots.length) :
    D.neg b < τ.rootCertificate.roots.length ∧
      τ.rootCertificate.root (D.neg b) = -τ.rootCertificate.root b ∧
      ∀ i : Fin τ.rank, D.img b i = τ.rootCertificate.image b i ∧
        (if b = (i : ℕ) then D.dn b i = 2 ∧ D.upl b i = 0
          else if b = D.neg i then D.dn b i = 0 ∧ D.upl b i = 2
          else D.dn b i = τ.stringData.down b i ∧ D.upl b i = τ.stringData.up b i) ∧
        D.par b i = (∑ j, τ.cartan i j * τ.rootCertificate.root b j).natAbs % 2 ∧
        (if D.upI b i = 0 then τ.stringData.memDec τ.rootCertificate
            (τ.rootCertificate.root b + Pi.single i 1) = false
          else D.upI b i - 1 < τ.rootCertificate.roots.length ∧
            τ.rootCertificate.root (D.upI b i - 1) =
              τ.rootCertificate.root b + Pi.single i 1) ∧
        (if D.downI b i = 0 then τ.stringData.memDec τ.rootCertificate
            (τ.rootCertificate.root b - Pi.single i 1) = false
          else D.downI b i - 1 < τ.rootCertificate.roots.length ∧
            τ.rootCertificate.root (D.downI b i - 1) =
              τ.rootCertificate.root b - Pi.single i 1) := by
  have h := hT
  simp only [checkTables, nR, List.all_eq_true, List.mem_range, Bool.and_eq_true, beq_iff_eq,
    List.mem_finRange, true_implies] at h
  obtain ⟨⟨hn, hr⟩, hi⟩ := h b hb
  refine ⟨of_decide_eq_true hn, RootCertificate.eq_of_ofFn_beq (beq_iff_eq.2 hr), fun i => ?_⟩
  obtain ⟨⟨⟨⟨hi1, hi2⟩, hi3⟩, hi4⟩, hi5⟩ := hi i
  refine ⟨hi1, ?_, hi3, ?_, ?_⟩
  · split_ifs at hi2 ⊢ <;> simpa using hi2
  · split_ifs at hi4 ⊢
    · simpa using hi4
    · simp only [Bool.and_eq_true, beq_iff_eq] at hi4
      exact ⟨of_decide_eq_true hi4.1, List.ofFn_injective hi4.2⟩
  · split_ifs at hi5 ⊢
    · simpa using hi5
    · simp only [Bool.and_eq_true, beq_iff_eq] at hi5
      exact ⟨of_decide_eq_true hi5.1, List.ofFn_injective hi5.2⟩

theorem neg_lt (hT : D.checkTables = true) {b : ℕ} (hb : b < τ.rootCertificate.roots.length) :
    D.neg b < τ.rootCertificate.roots.length :=
  (checkTables_at hT hb).1

theorem root_neg (hT : D.checkTables = true) {b : ℕ} (hb : b < τ.rootCertificate.roots.length) :
    τ.rootCertificate.root (D.neg b) = -τ.rootCertificate.root b :=
  (checkTables_at hT hb).2.1

theorem img_eq (hT : D.checkTables = true) {b : ℕ} (hb : b < τ.rootCertificate.roots.length)
    (i : Fin τ.rank) : D.img b i = τ.rootCertificate.image b i :=
  ((checkTables_at hT hb).2.2 i).1

theorem img_lt (hT : D.checkTables = true) {b : ℕ} (hb : b < τ.rootCertificate.roots.length)
    (i : Fin τ.rank) : D.img b i < τ.rootCertificate.roots.length := by
  rw [img_eq hT hb]
  exact rootCertificate_image_lt hb i

theorem root_img (hT : D.checkTables = true) {b : ℕ} (hb : b < τ.rootCertificate.roots.length)
    (i : Fin τ.rank) :
    τ.rootCertificate.root (D.img b i) = reflect τ i (τ.rootCertificate.root b) := by
  rw [img_eq hT hb]
  exact rootCertificate_root_image hb i

theorem neg_simple (hT : D.checkTables = true) (i : Fin τ.rank) :
    D.neg i = τ.rootCertificate.image i i := by
  refine rootCertificate_root_injOn (neg_lt hT (simple_lt i))
    (rootCertificate_image_lt (simple_lt i) i) ?_
  rw [root_neg hT (simple_lt i), rootCertificate_root_image (simple_lt i), root_simple,
    reflect_single_self]

theorem dn_eq (hT : D.checkTables = true) {b : ℕ} (hb : b < τ.rootCertificate.roots.length)
    (i : Fin τ.rank) : D.dn b i = stringDown τ i (τ.rootCertificate.root b) := by
  have h := ((checkTables_at hT hb).2.2 i).2.1
  rw [stringDown_rootCertificate_root hb i, downAt, ← neg_simple hT i]
  split_ifs at h ⊢
  · exact h.1
  · exact h.1
  · exact h.1

theorem par_eq (hT : D.checkTables = true) {b : ℕ} (hb : b < τ.rootCertificate.roots.length)
    (i : Fin τ.rank) :
    D.par b i = (∑ j, τ.cartan i j * τ.rootCertificate.root b j).natAbs % 2 :=
  ((checkTables_at hT hb).2.2 i).2.2.1

theorem not_isRoot_of_upI (hT : D.checkTables = true) {b : ℕ}
    (hb : b < τ.rootCertificate.roots.length) {i : Fin τ.rank} (h : D.upI b i = 0) :
    ¬IsRoot τ (τ.rootCertificate.root b + Pi.single i 1) := by
  have h' := ((checkTables_at hT hb).2.2 i).2.2.2.1
  rw [ite_eq_left h] at h'
  rw [← StringData.memDec_iff τ.rootCertificate_check τ.stringData_check, h']
  exact Bool.false_ne_true

theorem upI_spec (hT : D.checkTables = true) {b : ℕ} (hb : b < τ.rootCertificate.roots.length)
    {i : Fin τ.rank} (h : D.upI b i ≠ 0) :
    D.upI b i - 1 < τ.rootCertificate.roots.length ∧
      τ.rootCertificate.root (D.upI b i - 1) = τ.rootCertificate.root b + Pi.single i 1 := by
  have h' := ((checkTables_at hT hb).2.2 i).2.2.2.1
  rwa [ite_eq_right h] at h'

theorem not_isRoot_of_downI (hT : D.checkTables = true) {b : ℕ}
    (hb : b < τ.rootCertificate.roots.length) {i : Fin τ.rank} (h : D.downI b i = 0) :
    ¬IsRoot τ (τ.rootCertificate.root b - Pi.single i 1) := by
  have h' := ((checkTables_at hT hb).2.2 i).2.2.2.2
  rw [ite_eq_left h] at h'
  rw [← StringData.memDec_iff τ.rootCertificate_check τ.stringData_check, h']
  exact Bool.false_ne_true

theorem downI_spec (hT : D.checkTables = true) {b : ℕ} (hb : b < τ.rootCertificate.roots.length)
    {i : Fin τ.rank} (h : D.downI b i ≠ 0) :
    D.downI b i - 1 < τ.rootCertificate.roots.length ∧
      τ.rootCertificate.root (D.downI b i - 1) = τ.rootCertificate.root b - Pi.single i 1 := by
  have h' := ((checkTables_at hT hb).2.2 i).2.2.2.2
  rwa [ite_eq_right h] at h'

theorem units_neg_one_zpow (z : ℤ) :
    (((-1 : Rˣ) ^ z : Rˣ) : R) = (-1 : R) ^ (z.natAbs % 2) := by
  rcases Int.even_or_odd z with h | h
  · rw [h.neg_one_zpow, Units.val_one]
    have : z.natAbs % 2 = 0 := by
      obtain ⟨k, rfl⟩ := h
      omega
    rw [this, pow_zero]
  · rw [h.neg_one_zpow, Units.val_neg, Units.val_one]
    have : z.natAbs % 2 = 1 := by
      obtain ⟨k, rfl⟩ := h
      omega
    rw [this, pow_one]

theorem hReflect_getD (i m : Fin τ.rank) (v : List ℤ) :
    (hReflect i v).getD m 0 =
      v.getD m 0 - if m = i then ∑ l : Fin τ.rank, v.getD l 0 * ((τ.cartan l i).natAbs : ℤ)
        else 0 := by
  rw [hReflect, getD_range_map _ _ m.2]
  simp only [Fin.val_inj]

theorem hReflect_length (i : Fin τ.rank) (v : List ℤ) : (hReflect i v).length = τ.rank := by
  simp [hReflect]

theorem weylElt_interp_hvec (i : Fin τ.rank) (t : Rˣ) (v : List ℤ) :
    (weylElt τ R i t : Module.End R (RootModule τ R)) ((AVec.hvec v).interp τ R) =
      (AVec.hvec (hReflect i v)).interp τ R := by
  simp only [interp_hvec, map_sum, map_smul, weylElt_hVec, hReflect_getD, smul_sub,
    Finset.sum_sub_distrib, Int.cast_sub, sub_smul]
  congr 1
  simp only [apply_ite, Int.cast_zero, ite_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ,
    ite_true, Int.cast_sum, Int.cast_mul, Int.cast_natCast, Finset.sum_smul, smul_smul]

theorem weylElt_interp (hT : D.checkTables = true) (i : Fin τ.rank) {u : AVec} (hu : u.WF τ) :
    (weylElt τ R i 1 : Module.End R (RootModule τ R)) (u.interp τ R) = (D.actN i u).interp τ R := by
  cases u with
  | zero => simp [actN]
  | root m c =>
    rcases hu with rfl | hm
    · simp [actN]
    · rw [interp_root, map_smul, weylElt_rootVec i 1 (isRoot_rootCertificate_root hm)]
      simp only [actN, interp_root, one_zpow, Units.val_one, mul_one, smul_smul,
        root_img hT hm, dn_eq hT hm, Int.cast_mul, Int.cast_pow, Int.cast_neg, Int.cast_one]
  | hvec v => rw [weylElt_interp_hvec, actN, interp_norm]

theorem weylElt_inv_interp (hT : D.checkTables = true) (i : Fin τ.rank) {u : AVec}
    (hu : u.WF τ) :
    (((weylElt τ R i 1)⁻¹ : (Module.End R (RootModule τ R))ˣ) : Module.End R (RootModule τ R))
        (u.interp τ R) = (D.actNinv i u).interp τ R := by
  rw [weylElt_inv]
  cases u with
  | zero => simp [actNinv]
  | root m c =>
    rcases hu with rfl | hm
    · simp [actNinv]
    · rw [interp_root, map_smul, weylElt_rootVec i (-1) (isRoot_rootCertificate_root hm)]
      simp only [actNinv, interp_root, smul_smul, root_img hT hm, dn_eq hT hm, par_eq hT hm,
        units_neg_one_zpow, Int.natAbs_neg, pow_add, Int.cast_mul, Int.cast_pow, Int.cast_neg,
        Int.cast_one]
  | hvec v => rw [weylElt_interp_hvec, actNinv, interp_norm]

theorem actN_wf (hT : D.checkTables = true) (i : Fin τ.rank) {u : AVec} (hu : u.WF τ) :
    (D.actN i u).WF τ := by
  cases u with
  | zero => trivial
  | root m c =>
    rcases hu with rfl | hm
    · exact Or.inl (zero_mul _)
    · exact Or.inr (img_lt hT hm i)
  | hvec v => exact WF.norm (show (AVec.hvec (hReflect i v)).WF τ from hReflect_length i v)

theorem actNinv_wf (hT : D.checkTables = true) (i : Fin τ.rank) {u : AVec} (hu : u.WF τ) :
    (D.actNinv i u).WF τ := by
  cases u with
  | zero => trivial
  | root m c =>
    rcases hu with rfl | hm
    · exact Or.inl (zero_mul _)
    · exact Or.inr (img_lt hT hm i)
  | hvec v => exact WF.norm (show (AVec.hvec (hReflect i v)).WF τ from hReflect_length i v)

theorem coroot_length (k : ℕ) : (D.coroot k).length = τ.rank := by
  simp [coroot]

@[expose] def ActWF (D : AdjData τ) (k : ℕ) : Prop :=
  ∀ b < τ.rootCertificate.roots.length, (D.act k (.root b 1)).WF τ

theorem actM_root_wf (M k b : ℕ) (c : ℤ) (h : (D.actM M k (.root b 1)).WF τ) :
    (D.actM M k (.root b c)).WF τ := by
  simp only [actM] at h ⊢
  split_ifs with h1 h2
  · exact WF.norm (by simp [WF, coroot_length])
  · trivial
  · rw [ite_eq_right h1, ite_eq_right h2] at h
    simp only [AVec.norm] at h ⊢
    split_ifs with hc
    · trivial
    · split_ifs at h with hN
      · rw [one_mul] at hN
        exact absurd (by rw [hN, mul_zero]) hc
      · rcases h with h | h
        · exact absurd h hN
        · exact Or.inr h

theorem act_wf {k : ℕ} (hk : k < τ.rootCertificate.roots.length) (hP : D.ActWF k) {u : AVec}
    (hu : u.WF τ) : (D.act k u).WF τ := by
  cases u with
  | zero => trivial
  | root m c =>
    rcases hu with rfl | hm
    · simp only [act, actM]
      split_ifs
      · exact WF.norm (by simp [WF, coroot_length])
      · trivial
      · simp [AVec.norm, WF]
    · exact D.actM_root_wf _ k m c (hP m hm)
  | hvec v =>
    simp only [act, actM]
    exact WF.norm (Or.inr hk)

theorem checkSimple_at (hS : D.checkSimple = true) (i : Fin τ.rank) :
    (∀ b < τ.rootCertificate.roots.length, D.act i (.root b 1) =
      if b = i then .zero
      else if b = D.neg i then .hvec (hUnit i)
      else if D.upI b i = 0 then .zero
      else .root (D.upI b i - 1) ((D.dn b i : ℤ) + 1)) ∧
    ∀ m : Fin τ.rank, D.act i (.hvec (hUnit m)) = AVec.norm (.root i ((τ.cartan m i).natAbs : ℤ)) := by
  simp only [checkSimple, nR, List.all_eq_true, List.mem_finRange, List.mem_range,
    Bool.and_eq_true, AVec.beq_iff, true_implies] at hS
  exact ⟨fun b hb => ((hS i).1 b hb).1, fun m => ((hS i).2 m).1⟩

theorem pos_eq_simple_iff {α : {v : Fin τ.rank → ℤ // IsRoot τ v}} (i : Fin τ.rank) :
    pos α = i ↔ α.1 = Pi.single i 1 := by
  rw [pos_eq_iff (simple_lt i), root_simple, eq_comm]

theorem pos_eq_neg_simple_iff (hT : D.checkTables = true)
    {α : {v : Fin τ.rank → ℤ // IsRoot τ v}} (i : Fin τ.rank) :
    pos α = D.neg i ↔ α.1 = -Pi.single i 1 := by
  rw [pos_eq_iff (neg_lt hT (simple_lt i)), root_neg hT (simple_lt i), root_simple, eq_comm]

theorem recOp_simple (hT : D.checkTables = true) (hS : D.checkSimple = true) (i : Fin τ.rank) :
    D.recOp R i = infE τ R i := by
  refine Finsupp.lhom_ext' fun b => LinearMap.ext_ring ?_
  simp only [LinearMap.comp_apply, Finsupp.lsingle_apply]
  rw [recOp_single]
  rcases b with m | ⟨α, hα⟩
  · change _ = infE τ R i (hVec τ R m)
    simp only [ofLabel]
    rw [(checkSimple_at hS i).2 m, interp_norm, interp_root, infE_hVec, root_simple,
      Int.cast_natCast]
  · rw [← rootVec_of_isRoot' hα]
    simp only [ofLabel]
    rw [(checkSimple_at hS i).1 _ (pos_lt _)]
    by_cases h₁ : α = Pi.single i 1
    · subst h₁
      rw [ite_eq_left ((pos_eq_simple_iff i).2 rfl), interp_zero, infE_rootVec_single]
    rw [ite_eq_right (mt (pos_eq_simple_iff i).1 h₁)]
    by_cases h₂ : α = -Pi.single i 1
    · subst h₂
      rw [ite_eq_left ((pos_eq_neg_simple_iff hT i).2 rfl), infE_rootVec_neg_single,
        interp_hvec]
      simp only [hUnit_getD]
      simp [hVec]
    rw [ite_eq_right (mt (pos_eq_neg_simple_iff hT i).1 h₂), infE_rootVec_of_ne i hα h₁ h₂]
    have hp := pos_lt (⟨α, hα⟩ : {v : Fin τ.rank → ℤ // IsRoot τ v})
    have hr := root_pos (⟨α, hα⟩ : {v : Fin τ.rank → ℤ // IsRoot τ v})
    split_ifs with hu
    · rw [interp_zero, rootVec_of_not_isRoot' (by simpa [hr] using not_isRoot_of_upI hT hp hu),
        smul_zero]
    · obtain ⟨-, hm⟩ := upI_spec hT hp hu
      rw [interp_root, hm, dn_eq hT hp, hr]
      push_cast
      rfl

theorem actWF_simple (hT : D.checkTables = true) (hS : D.checkSimple = true) (i : Fin τ.rank) :
    D.ActWF i := by
  intro b hb
  rw [(checkSimple_at hS i).1 b hb]
  split_ifs with h1 h2 h3
  · trivial
  · exact hUnit_length i
  · trivial
  · exact Or.inr (upI_spec hT hb h3).1

theorem weylSign_eq (k : ℕ) (i : Fin τ.rank) : D.weylSign k i = 1 ∨ D.weylSign k i = -1 := by
  unfold weylSign
  split_ifs
  · exact Or.inr rfl
  · exact Or.inl rfl

theorem weylSign_mul_self (k : ℕ) (i : Fin τ.rank) : D.weylSign k i * D.weylSign k i = 1 := by
  rcases D.weylSign_eq k i with h | h <;> rw [h] <;> norm_num

theorem checkWeyl_at (hW : D.checkWeyl = true) {k : ℕ} (hk : k < τ.rootCertificate.roots.length)
    (i : Fin τ.rank) :
    ∀ u ∈ basis τ, D.actN i (D.act k (D.actNinv i u)) = (D.act (D.img k i) u).smul (D.weylSign k i) := by
  simp only [checkWeyl, checkWeylRange, nR, List.all_eq_true, List.mem_map, List.mem_range,
    List.mem_finRange, true_implies, forall_exists_index, and_imp, weylOne] at hW
  intro u hu
  exact AVec.beq_iff.1 (hW _ k hk (zero_add k) i u hu)

theorem actM_root_wf_of_smul (M k b : ℕ) {s : ℤ} (hs : s = 1 ∨ s = -1)
    (h : ((D.actM M k (.root b 1)).smul s).WF τ) : (D.actM M k (.root b 1)).WF τ := by
  have hs0 : s ≠ 0 := by rcases hs with rfl | rfl <;> norm_num
  simp only [actM] at h ⊢
  split_ifs at h ⊢ with h1 h2
  · exact WF.norm (by simp [WF, coroot_length])
  · trivial
  · simp only [AVec.norm] at h ⊢
    split_ifs at h ⊢ with hN
    · trivial
    · simp only [AVec.smul, AVec.norm] at h
      rw [ite_eq_right (mul_ne_zero hs0 hN)] at h
      rcases h with h | h
      · exact absurd h (mul_ne_zero hs0 hN)
      · exact Or.inr h

theorem actWF_img (hT : D.checkTables = true) (hW : D.checkWeyl = true) {k : ℕ}
    (hk : k < τ.rootCertificate.roots.length) (hP : D.ActWF k) (i : Fin τ.rank) :
    D.ActWF (D.img k i) := by
  intro b hb
  have hu : AVec.root b 1 ∈ basis τ :=
    List.mem_append_left _ (List.mem_map.2 ⟨b, List.mem_range.2 hb, rfl⟩)
  have h := D.checkWeyl_at hW hk i _ hu
  have hl : (D.actN i (D.act k (D.actNinv i (.root b 1)))).WF τ :=
    actN_wf hT i (act_wf hk hP (actNinv_wf hT i (Or.inr hb)))
  rw [h] at hl
  exact D.actM_root_wf_of_smul _ _ _ (D.weylSign_eq k i) hl

theorem pos_reflect (hT : D.checkTables = true) {v : Fin τ.rank → ℤ} (hv : IsRoot τ v)
    (i : Fin τ.rank) :
    pos ⟨reflect τ i v, IsRoot.reflect i hv⟩ = D.img (pos ⟨v, hv⟩) i := by
  rw [pos_eq_iff (img_lt hT (pos_lt _) i), root_img hT (pos_lt _), root_pos]

theorem actWF_pos (hT : D.checkTables = true) (hS : D.checkSimple = true)
    (hW : D.checkWeyl = true) {v : Fin τ.rank → ℤ} (hv : IsRoot τ v) : D.ActWF (pos ⟨v, hv⟩) := by
  induction hv with
  | basis j =>
    rw [(pos_eq_simple_iff j).2 rfl]
    exact actWF_simple hT hS j
  | reflect i hv ih =>
    rw [pos_reflect hT hv i]
    exact actWF_img hT hW (pos_lt _) ih i

theorem actWF (hT : D.checkTables = true) (hS : D.checkSimple = true) (hW : D.checkWeyl = true)
    {k : ℕ} (hk : k < τ.rootCertificate.roots.length) : D.ActWF k := by
  have := actWF_pos hT hS hW (isRoot_rootCertificate_root hk)
  rwa [pos_root hk] at this

theorem recOp_weyl (hT : D.checkTables = true) (hS : D.checkSimple = true)
    (hW : D.checkWeyl = true) {k : ℕ} (hk : k < τ.rootCertificate.roots.length) (i : Fin τ.rank) :
    (weylElt τ R i 1 : Module.End R (RootModule τ R)) * D.recOp R k *
        (((weylElt τ R i 1)⁻¹ : (Module.End R (RootModule τ R))ˣ) :
          Module.End R (RootModule τ R)) =
      (D.weylSign k i : R) • D.recOp R (D.img k i) := by
  refine Finsupp.lhom_ext' fun b => LinearMap.ext_ring ?_
  simp only [LinearMap.comp_apply, Finsupp.lsingle_apply, Module.End.mul_apply,
    LinearMap.smul_apply]
  rw [← interp_ofLabel R b, weylElt_inv_interp hT i (ofLabel_wf b),
    recOp_interp _ _ (actNinv_wf hT i (ofLabel_wf b)),
    weylElt_interp hT i (act_wf hk (actWF hT hS hW hk) (actNinv_wf hT i (ofLabel_wf b))),
    D.checkWeyl_at hW hk i _ (ofLabel_mem_basis b), interp_smul,
    recOp_interp _ _ (ofLabel_wf b)]

theorem checkPairs_at (hP : D.checkPairs = true) {l : ℕ} (hl : l < τ.rootCertificate.roots.length)
    (j : Fin τ.rank) (hlj : l ≠ D.neg j) :
    (if D.pairDig l j = 0 then l = j ∨ D.upI l j = 0 else D.pairDig l j / 8 = D.upI l j) ∧
      ∀ u ∈ basis τ, (AVec.sub (D.act j (D.act l u)) (D.act l (D.act j u))) =
        some (if D.pairDig l j = 0 then .zero
          else AVec.smul ((D.pairDig l j % 8 : ℕ) - 4 : ℤ) (D.act (D.pairDig l j / 8 - 1) u)) := by
  simp only [checkPairs, checkPairsRange, nR, List.all_eq_true, List.mem_map, List.mem_range,
    List.mem_finRange, true_implies, forall_exists_index, and_imp] at hP
  have h := hP _ l hl (zero_add l) j
  simp only [Bool.or_eq_true, decide_eq_true_eq, hlj, false_or, Bool.and_eq_true] at h
  obtain ⟨h1, h2⟩ := h
  refine ⟨?_, fun u hu => ?_⟩
  · split_ifs at h1 ⊢
    · simpa using h1
    · simpa using h1
  · simp only [pairOne, List.all_eq_true] at h2
    have h3 := h2 u hu
    rw [← act_eq, ← act_eq, ← act_eq, ← act_eq, ← act_eq] at h3
    cases hs : AVec.sub (D.act j (D.act l u)) (D.act l (D.act j u)) with
    | none => rw [hs] at h3; simp [AVec.obeq] at h3
    | some w => rw [hs, AVec.obeq_some_iff] at h3; rw [h3]

theorem recOp_bracket_simple (hT : D.checkTables = true) (hS : D.checkSimple = true)
    (hW : D.checkWeyl = true) (hP : D.checkPairs = true) {l : ℕ}
    (hl : l < τ.rootCertificate.roots.length) (j : Fin τ.rank) (hlj : l ≠ D.neg j) :
    D.recOp R j * D.recOp R l - D.recOp R l * D.recOp R j =
      if D.pairDig l j = 0 then 0
      else ((((D.pairDig l j % 8 : ℕ) : ℤ) - 4 : ℤ) : R) • D.recOp R (D.pairDig l j / 8 - 1) := by
  refine Finsupp.lhom_ext' fun b => LinearMap.ext_ring ?_
  simp only [LinearMap.comp_apply, Finsupp.lsingle_apply, LinearMap.sub_apply,
    Module.End.mul_apply]
  have hb := ofLabel_wf b
  have hlu : (D.act l (ofLabel b)).WF τ := act_wf hl (actWF hT hS hW hl) hb
  have hju : (D.act j (ofLabel b)).WF τ :=
    act_wf (simple_lt j) (actWF hT hS hW (simple_lt j)) hb
  rw [← interp_ofLabel R b, recOp_interp _ _ hb, recOp_interp _ _ hb, recOp_interp _ _ hlu,
    recOp_interp _ _ hju, ← interp_of_sub (act_wf (simple_lt j) (actWF hT hS hW (simple_lt j)) hlu)
      (act_wf hl (actWF hT hS hW hl) hju)
      ((D.checkPairs_at hP hl j hlj).2 _ (ofLabel_mem_basis b))]
  split_ifs
  · rfl
  · rw [interp_smul, LinearMap.smul_apply, recOp_interp _ _ hb]

end AdjData

end CFSG.LieType.Steinberg.Adjoint
