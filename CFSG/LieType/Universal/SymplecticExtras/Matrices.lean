module

public import CFSG.LieType.Universal.SymplecticRoots
public import CFSG.LieType.Steinberg.Basic
import all CFSG.LieType.Universal.SymplecticRoots

public section

namespace CFSG.LieType.Universal.Symplectic.SpExtras

open Matrix CFSG.LieType.RootSystem CFSG.LieType.Steinberg CFSG.Assembly.LowTwoRank
  TauCeti.GLSymplecticFin

variable {n : ℕ} {F : Type} [Field F]

theorem toStd_inj : Function.Injective (toStd n) := toStd_injective n

theorem toStd_add' (v w : Fin n → ℤ) : toStd n (v + w) = toStd n v + toStd n w :=
  map_add (toStdLin n) v w

theorem toStd_zsmul' (c : ℤ) (v : Fin n → ℤ) : toStd n (c • v) = c • toStd n v :=
  toStd_smul n c v

theorem toStd_nsmul' (c : ℕ) (v : Fin n → ℤ) : toStd n (c • v) = c • toStd n v :=
  map_nsmul (toStdLin n) c v

theorem toStd_neg' (v : Fin n → ℤ) : toStd n (-v) = -toStd n v := toStd_neg n v

theorem toStd_zero' : toStd n 0 = 0 := map_zero (toStdLin n)

theorem toStd_single_of_lt' {k : Fin n} (h : k.val + 1 < n) :
    toStd n (Pi.single k 1) = Pi.single k 1 - Pi.single ⟨k.val + 1, h⟩ 1 :=
  toStd_single_of_lt n h

theorem toStd_single_of_not_lt' {k : Fin n} (h : ¬k.val + 1 < n) :
    toStd n (Pi.single k 1) = 2 • Pi.single k 1 :=
  toStd_single_of_not_lt n h

theorem ne_succ' {k : Fin n} (h : k.val + 1 < n) : k ≠ ⟨k.val + 1, h⟩ :=
  Fin.ne_of_val_ne (by simp)

@[expose] noncomputable def mat (n : ℕ) (F : Type) [Field F] :
    StatedSp n F →* Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F :=
  (Units.coeHom _).comp (StatedSp n F).subtype

theorem mat_apply (x : StatedSp n F) :
    mat n F x = ((x : GL (Fin n ⊕ Fin n) F) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) := rfl

theorem mat_injective : Function.Injective (mat n F) := fun _ _ h =>
  Subtype.ext (Units.ext h)

theorem mat_equivStatedSp (g : TauCeti.GLSymplecticFin n F) :
    mat n F (equivStatedSp n F g) =
      ((g : GL (Fin (n + n)) F) : Matrix (Fin (n + n)) (Fin (n + n)) F).submatrix
        finSumFinEquiv finSumFinEquiv := by
  simp [mat_apply, equivStatedSp]

theorem mat_equiv_diagonal (t : Fin n → Fˣ) :
    mat n F (equivStatedSp n F (TauCeti.GLSymplecticFin.diagonal t)) =
      Matrix.diagonal (Sum.elim (fun i => (t i : F)) (fun i => (((t i)⁻¹ : Fˣ) : F))) := by
  rw [mat_equivStatedSp, coe_diagonal, TauCeti.diagGL_coe, Matrix.submatrix_diagonal_equiv]
  congr 1
  funext a
  rcases a with i | i
  · simp
  · simp [Fin.natAdd_eq_addNat]

@[expose] noncomputable def elt (r : RootSubgroupIndex n) (c : F) : StatedSp n F :=
  equivStatedSp n F (r.hom (Multiplicative.ofAdd c))

theorem elt_add (r : RootSubgroupIndex n) (c d : F) : elt r (c + d) = elt r c * elt r d := by
  simp only [elt, ofAdd_add, map_mul]

theorem elt_zero (r : RootSubgroupIndex n) : elt r (0 : F) = 1 := by
  simp only [elt, ofAdd_zero, map_one]

theorem elt_neg (r : RootSubgroupIndex n) (c : F) : elt r (-c) = (elt r c)⁻¹ := by
  simp only [elt, ofAdd_neg, map_inv]

theorem elt_injective (r : RootSubgroupIndex n) : Function.Injective (elt (F := F) r) :=
  fun _ _ h => Multiplicative.ofAdd.injective (r.hom_injective ((equivStatedSp n F).injective h))

@[expose] noncomputable def E (F : Type) [Field F] :
    RootSubgroupIndex n → Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F
  | .positiveLong i => single (.inl i) (.inr i) 1
  | .negativeLong i => single (.inr i) (.inl i) 1
  | .difference i j _ => single (.inl i) (.inl j) 1 - single (.inr j) (.inr i) 1
  | .positiveSum i j _ => single (.inl i) (.inr j) 1 + single (.inl j) (.inr i) 1
  | .negativeSum i j _ => single (.inr i) (.inl j) 1 + single (.inr j) (.inl i) 1

theorem mat_elt (r : RootSubgroupIndex n) (c : F) : mat n F (elt r c) = 1 + c • E F r := by
  rw [elt, mat_equivStatedSp]
  have key : ∀ (x y a b : Fin n ⊕ Fin n) (d : F),
      (single (finSumFinEquiv x) (finSumFinEquiv y) d :
        Matrix (Fin (n + n)) (Fin (n + n)) F) (finSumFinEquiv a) (finSumFinEquiv b) =
        single x y d a b := by
    intro x y a b d
    simp only [Matrix.single_apply, Equiv.apply_eq_iff_eq]
  have key1 : ∀ (a b : Fin n ⊕ Fin n),
      (1 : Matrix (Fin (n + n)) (Fin (n + n)) F) (finSumFinEquiv a) (finSumFinEquiv b) =
        (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) a b := by
    intro a b
    simp only [Matrix.one_apply, Equiv.apply_eq_iff_eq]
  cases r with
  | positiveLong i =>
    ext a b
    simp only [E, Matrix.submatrix_apply, RootSubgroupIndex.hom_positiveLong,
      positiveLongRootTransvectionHom_apply, coe_positiveLongRootTransvectionUnit,
      TauCeti.coe_transvectionUnit, Matrix.transvection, Matrix.add_apply, key, key1,
      Matrix.smul_apply, Matrix.single_apply, smul_eq_mul, toAdd_ofAdd]
    split_ifs <;> simp
  | negativeLong i =>
    ext a b
    simp only [E, Matrix.submatrix_apply, RootSubgroupIndex.hom_negativeLong,
      negativeLongRootTransvectionHom_apply, coe_negativeLongRootTransvectionUnit,
      TauCeti.coe_transvectionUnit, Matrix.transvection, Matrix.add_apply, key, key1,
      Matrix.smul_apply, Matrix.single_apply, smul_eq_mul, toAdd_ofAdd]
    split_ifs <;> simp
  | difference i j hij =>
    rw [RootSubgroupIndex.hom_difference, differenceShortRootHom_apply, toAdd_ofAdd,
      coe_differenceShortRootUnit_eq_one_add_single_sub_single]
    ext a b
    simp only [E, Matrix.submatrix_apply, Matrix.add_apply, Matrix.sub_apply, key, key1,
      Matrix.smul_apply, smul_eq_mul, Matrix.single_apply]
    split_ifs <;> simp
    ring
  | positiveSum i j hij =>
    rw [RootSubgroupIndex.hom_positiveSum, positiveSumShortRootHom_apply, toAdd_ofAdd,
      coe_positiveSumShortRootUnit, Units.val_mul, TauCeti.coe_transvectionUnit,
      TauCeti.coe_transvectionUnit, Matrix.transvection, Matrix.transvection, add_mul, one_mul,
      mul_add, mul_one, Matrix.single_mul_single_of_ne _ _ _ _ (finSumFinEquiv_inr_ne_inl j j)]
    ext a b
    simp only [E, Matrix.submatrix_apply, Matrix.add_apply, key, key1, Matrix.smul_apply,
      smul_eq_mul, Matrix.single_apply]
    split_ifs <;> simp
    ring
  | negativeSum i j hij =>
    rw [RootSubgroupIndex.hom_negativeSum, negativeSumShortRootHom_apply, toAdd_ofAdd,
      coe_negativeSumShortRootUnit, Units.val_mul, TauCeti.coe_transvectionUnit,
      TauCeti.coe_transvectionUnit, Matrix.transvection, Matrix.transvection, add_mul, one_mul,
      mul_add, mul_one, Matrix.single_mul_single_of_ne _ _ _ _ (finSumFinEquiv_inl_ne_inr j j)]
    ext a b
    simp only [E, Matrix.submatrix_apply, Matrix.add_apply, key, key1, Matrix.smul_apply,
      smul_eq_mul, Matrix.single_apply]
    split_ifs <;> simp
    ring

@[expose] def wt : Fin n ⊕ Fin n → Fin n → ℤ
  | .inl i => Pi.single i 1
  | .inr i => -Pi.single i 1

@[expose] def pos1 : RootSubgroupIndex n → (Fin n ⊕ Fin n) × (Fin n ⊕ Fin n)
  | .positiveLong i => (.inl i, .inr i)
  | .negativeLong i => (.inr i, .inl i)
  | .difference i j _ => (.inl i, .inl j)
  | .positiveSum i j _ => (.inl i, .inr j)
  | .negativeSum i j _ => (.inr i, .inl j)

@[expose] def pos2 : RootSubgroupIndex n → (Fin n ⊕ Fin n) × (Fin n ⊕ Fin n)
  | .positiveLong i => (.inl i, .inr i)
  | .negativeLong i => (.inr i, .inl i)
  | .difference i j _ => (.inr j, .inr i)
  | .positiveSum i j _ => (.inl j, .inr i)
  | .negativeSum i j _ => (.inr j, .inl i)

@[expose] def sgn2 : RootSubgroupIndex n → ℤ
  | .difference _ _ _ => -1
  | _ => 1

theorem eq_pos_of_wt_sub (r : RootSubgroupIndex n) (a b : Fin n ⊕ Fin n)
    (h : wt a - wt b = stdVec r) : (a, b) = pos1 r ∨ (a, b) = pos2 r := by
  cases r with
  | positiveLong i =>
    simp only [stdVec, two_nsmul] at h
    have h1 := congrFun h i
    rcases a with k | k <;> rcases b with l | l <;>
      simp only [wt, Pi.sub_apply, Pi.add_apply, Pi.neg_apply, Pi.single_apply, pos1,
        pos2, Prod.mk.injEq, Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq, false_and, and_false,
        or_self] at h1 ⊢ <;>
      split_ifs at h1 <;> (try subst_vars) <;> omega
  | negativeLong i =>
    simp only [stdVec, two_nsmul] at h
    have h1 := congrFun h i
    rcases a with k | k <;> rcases b with l | l <;>
      simp only [wt, Pi.sub_apply, Pi.add_apply, Pi.neg_apply, Pi.single_apply, pos1,
        pos2, Prod.mk.injEq, Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq, false_and, and_false,
        or_self] at h1 ⊢ <;>
      split_ifs at h1 <;> (try subst_vars) <;> omega
  | difference i j hij =>
    have h1 := congrFun h i
    have h2 := congrFun h j
    rcases a with k | k <;> rcases b with l | l <;>
      simp only [wt, stdVec, Pi.sub_apply, Pi.neg_apply, Pi.single_apply, pos1, pos2,
        Prod.mk.injEq, Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq, false_and, and_false,
        or_false, false_or] at h1 h2 ⊢ <;>
      split_ifs at h1 h2 <;> (try subst_vars) <;> omega
  | positiveSum i j hij =>
    have h1 := congrFun h i
    have h2 := congrFun h j
    rcases a with k | k <;> rcases b with l | l <;>
      simp only [wt, stdVec, Pi.sub_apply, Pi.add_apply, Pi.neg_apply, Pi.single_apply, pos1,
        pos2, Prod.mk.injEq, Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq, false_and, and_false,
        or_false] at h1 h2 ⊢ <;>
      split_ifs at h1 h2 <;> (try subst_vars) <;> omega
  | negativeSum i j hij =>
    have h1 := congrFun h i
    have h2 := congrFun h j
    rcases a with k | k <;> rcases b with l | l <;>
      simp only [wt, stdVec, Pi.sub_apply, Pi.add_apply, Pi.neg_apply, Pi.single_apply, pos1,
        pos2, Prod.mk.injEq, Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq, false_and, and_false,
        or_false] at h1 h2 ⊢ <;>
      split_ifs at h1 h2 <;> (try subst_vars) <;> omega

theorem pos1_ne (r : RootSubgroupIndex n) : (pos1 r).1 ≠ (pos1 r).2 := by
  cases r with
  | difference i j hij => simpa [pos1] using hij
  | _ => simp [pos1]

theorem wt_pos1 (r : RootSubgroupIndex n) : wt (pos1 r).1 - wt (pos1 r).2 = stdVec r := by
  cases r <;> simp only [pos1, wt, stdVec, two_nsmul] <;> abel

theorem wt_pos2 (r : RootSubgroupIndex n) : wt (pos2 r).1 - wt (pos2 r).2 = stdVec r := by
  cases r <;> simp only [pos2, wt, stdVec, two_nsmul] <;> abel

theorem E_pos1 (r : RootSubgroupIndex n) : E F r (pos1 r).1 (pos1 r).2 = 1 := by
  cases r with
  | difference i j hij => simp [E, pos1]
  | positiveSum i j hij => simp [E, pos1, hij.ne]
  | negativeSum i j hij => simp [E, pos1, hij.ne]
  | _ => simp [E, pos1]

theorem E_pos2 (r : RootSubgroupIndex n) : E F r (pos2 r).1 (pos2 r).2 = sgn2 r := by
  cases r with
  | difference i j hij => simp [E, pos2, sgn2]
  | positiveSum i j hij => simp [E, pos2, sgn2, hij.ne']
  | negativeSum i j hij => simp [E, pos2, sgn2, hij.ne']
  | _ => simp [E, pos2, sgn2]

theorem eq_pos_of_E_ne_zero (r : RootSubgroupIndex n) (a b : Fin n ⊕ Fin n)
    (h : E F r a b ≠ 0) : (a, b) = pos1 r ∨ (a, b) = pos2 r := by
  cases r <;> simp only [E, Matrix.sub_apply, Matrix.add_apply, Matrix.single_apply] at h <;>
    split_ifs at h <;> simp_all [pos1, pos2]

theorem E_eq_zero (r : RootSubgroupIndex n) {a b : Fin n ⊕ Fin n} (h1 : (a, b) ≠ pos1 r)
    (h2 : (a, b) ≠ pos2 r) : E F r a b = 0 := by
  by_contra h
  rcases eq_pos_of_E_ne_zero r a b h with h' | h'
  exacts [h1 h', h2 h']

@[expose] def HasDeg (v : Fin n → ℤ) (N : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) : Prop :=
  ∀ a b, N a b ≠ 0 → wt a - wt b = v

@[expose] def IsPosWt (v : Fin n → ℤ) : Prop := ∃ a b : Fin n ⊕ Fin n, wt a - wt b = v

section Deg

variable {u v : Fin n → ℤ} {N M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F}

theorem HasDeg.mul (hN : HasDeg u N) (hM : HasDeg v M) : HasDeg (u + v) (N * M) := by
  intro a b hab
  rw [Matrix.mul_apply] at hab
  obtain ⟨c, -, hc⟩ := Finset.exists_ne_zero_of_sum_ne_zero hab
  rw [← hN a c (left_ne_zero_of_mul hc), ← hM c b (right_ne_zero_of_mul hc)]
  abel

theorem HasDeg.add (hN : HasDeg v N) (hM : HasDeg v M) : HasDeg v (N + M) := by
  intro a b hab
  by_cases h : N a b = 0
  · rw [Matrix.add_apply, h, zero_add] at hab
    exact hM a b hab
  · exact hN a b h

theorem HasDeg.smul (c : F) (hN : HasDeg v N) : HasDeg v (c • N) := fun a b hab =>
  hN a b (right_ne_zero_of_mul hab)

theorem HasDeg.neg (hN : HasDeg v N) : HasDeg v (-N) := fun a b hab =>
  hN a b (by simpa using hab)

theorem HasDeg.sub (hN : HasDeg v N) (hM : HasDeg v M) : HasDeg v (N - M) := by
  rw [sub_eq_add_neg]
  exact hN.add hM.neg

theorem HasDeg.zero : HasDeg v (0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) :=
  fun _ _ h => absurd rfl h

theorem HasDeg.congr (hN : HasDeg u N) (h : u = v) : HasDeg v N := h ▸ hN

theorem HasDeg.eq_zero (hN : HasDeg v N) (hv : ¬IsPosWt v) : N = 0 := by
  ext a b
  by_contra h
  exact hv ⟨a, b, hN a b h⟩

theorem hasDeg_E (r : RootSubgroupIndex n) : HasDeg (stdVec r) (E F r) := by
  intro a b h
  rcases eq_pos_of_E_ne_zero r a b h with h' | h'
  · rw [show a = (pos1 r).1 from congrArg Prod.fst h',
      show b = (pos1 r).2 from congrArg Prod.snd h']
    exact wt_pos1 r
  · rw [show a = (pos2 r).1 from congrArg Prod.fst h',
      show b = (pos2 r).2 from congrArg Prod.snd h']
    exact wt_pos2 r

end Deg

def ofPos : Fin n ⊕ Fin n → Fin n ⊕ Fin n → RootSubgroupIndex n
  | .inl i, .inl j => if h : i = j then .positiveLong i else .difference i j h
  | .inr i, .inr j => if h : i = j then .positiveLong i else .difference j i (Ne.symm h)
  | .inl i, .inr j => if h : i = j then .positiveLong i else
      if h' : i < j then .positiveSum i j h' else
        .positiveSum j i (lt_of_le_of_ne (not_lt.mp h') (Ne.symm h))
  | .inr i, .inl j => if h : i = j then .negativeLong i else
      if h' : i < j then .negativeSum i j h' else
        .negativeSum j i (lt_of_le_of_ne (not_lt.mp h') (Ne.symm h))

theorem stdVec_ofPos {a b : Fin n ⊕ Fin n} (hab : a ≠ b) : stdVec (ofPos a b) = wt a - wt b := by
  rcases a with i | i <;> rcases b with j | j
  · have hij : i ≠ j := fun h => hab (by rw [h])
    simp only [ofPos, dite_eq_right hij, stdVec, wt]
  · by_cases hij : i = j
    · subst hij
      rw [show ofPos (.inl i) (.inr i) = .positiveLong i by simp [ofPos]]
      simp only [stdVec, wt, two_nsmul]
      abel
    · by_cases h' : i < j
      · simp only [ofPos, dite_eq_right hij, dite_eq_left h', stdVec, wt]
        abel
      · simp only [ofPos, dite_eq_right hij, dite_eq_right h', stdVec, wt]
        abel
  · by_cases hij : i = j
    · subst hij
      rw [show ofPos (.inr i) (.inl i) = .negativeLong i by simp [ofPos]]
      simp only [stdVec, wt, two_nsmul]
      abel
    · by_cases h' : i < j
      · simp only [ofPos, dite_eq_right hij, dite_eq_left h', stdVec, wt]
        abel
      · simp only [ofPos, dite_eq_right hij, dite_eq_right h', stdVec, wt]
        abel
  · have hij : i ≠ j := fun h => hab (by rw [h])
    simp only [ofPos, dite_eq_right hij, stdVec, wt]
    abel

theorem ofPos_pos1 (r : RootSubgroupIndex n) : ofPos (pos1 r).1 (pos1 r).2 = r := by
  cases r with
  | positiveLong i => simp [ofPos, pos1]
  | negativeLong i => simp [ofPos, pos1]
  | difference i j hij => simp [ofPos, pos1, hij]
  | positiveSum i j hij => simp [ofPos, pos1, hij, hij.ne]
  | negativeSum i j hij => simp [ofPos, pos1, hij, hij.ne]

theorem ofPos_pos2 (r : RootSubgroupIndex n) : ofPos (pos2 r).1 (pos2 r).2 = r := by
  cases r with
  | positiveLong i => simp [ofPos, pos2]
  | negativeLong i => simp [ofPos, pos2]
  | difference i j hij => simp [ofPos, pos2, Ne.symm hij]
  | positiveSum i j hij => simp [ofPos, pos2, hij.ne', not_lt.mpr hij.le]
  | negativeSum i j hij => simp [ofPos, pos2, hij.ne', not_lt.mpr hij.le]

theorem stdVec_injective : Function.Injective (stdVec (n := n)) := by
  intro r r' h
  have hw := wt_pos1 r
  rw [h] at hw
  rcases eq_pos_of_wt_sub r' _ _ hw with h' | h'
  · rw [← ofPos_pos1 r, ← ofPos_pos1 r', ← h']
  · rw [← ofPos_pos1 r, ← ofPos_pos2 r', ← h']

theorem isPosWt_stdVec (r : RootSubgroupIndex n) : IsPosWt (stdVec r) :=
  ⟨_, _, wt_pos1 r⟩

theorem exists_stdVec_of_isPosWt {v : Fin n → ℤ} (hv : IsPosWt v) (h0 : v ≠ 0) :
    ∃ r : RootSubgroupIndex n, stdVec r = v := by
  obtain ⟨a, b, rfl⟩ := hv
  have hab : a ≠ b := by
    rintro rfl
    exact h0 (sub_self _)
  exact ⟨ofPos a b, stdVec_ofPos hab⟩

noncomputable def eltHom (r : RootSubgroupIndex n) : Multiplicative F →* StatedSp n F :=
  (equivStatedSp n F).toMonoidHom.comp r.hom

theorem rootGroup_eq_range {γ : Fin n → ℤ} {r : RootSubgroupIndex n}
    (hr : stdVec r = toStd n γ) : rootGroup n F γ = (eltHom (F := F) r).range := by
  apply le_antisymm
  · refine iSup₂_le fun r' hr' => ?_
    obtain rfl : r' = r := stdVec_injective (hr'.trans hr.symm)
    rw [eltHom, MonoidHom.range_comp]
  · rw [eltHom, MonoidHom.range_comp]
    exact le_iSup₂_of_le (f := fun (r' : RootSubgroupIndex n) (_ : stdVec r' = toStd n γ) =>
      (r'.hom (R := F)).range.map (equivStatedSp n F).toMonoidHom) r hr le_rfl

theorem mem_rootGroup_iff {γ : Fin n → ℤ} {r : RootSubgroupIndex n}
    (hr : stdVec r = toStd n γ) {x : StatedSp n F} :
    x ∈ rootGroup n F γ ↔ ∃ c : F, x = elt r c := by
  rw [rootGroup_eq_range hr, MonoidHom.mem_range]
  constructor
  · rintro ⟨c, rfl⟩
    exact ⟨Multiplicative.toAdd c, rfl⟩
  · rintro ⟨c, rfl⟩
    exact ⟨Multiplicative.ofAdd c, rfl⟩

theorem elt_mem_rootGroup {γ : Fin n → ℤ} {r : RootSubgroupIndex n}
    (hr : stdVec r = toStd n γ) (c : F) : elt r c ∈ rootGroup n F γ :=
  (mem_rootGroup_iff hr).2 ⟨c, rfl⟩

theorem exists_stdVec_of_mem_roots {γ : Fin n → ℤ} (hγ : γ ∈ roots (isFiniteType_cartanC n) ∅) :
    ∃ r : RootSubgroupIndex n, stdVec r = toStd n γ := by
  rw [roots_eq] at hγ
  exact hγ

theorem mem_roots_of_stdVec {γ : Fin n → ℤ} {r : RootSubgroupIndex n}
    (hr : stdVec r = toStd n γ) : γ ∈ roots (isFiniteType_cartanC n) ∅ := by
  rw [roots_eq]
  exact ⟨r, hr⟩

theorem mat_elt_apply_pos1 (r : RootSubgroupIndex n) (c : F) :
    mat n F (elt r c) (pos1 r).1 (pos1 r).2 = c := by
  rw [mat_elt, Matrix.add_apply, Matrix.one_apply_ne (pos1_ne r), Matrix.smul_apply, E_pos1,
    smul_eq_mul, mul_one, zero_add]

def lvl : Fin n ⊕ Fin n → ℤ
  | .inl i => i
  | .inr i => 2 * n - 1 - i

def lv (n : ℕ) : (Fin n → ℤ) →+ ℤ where
  toFun v := ∑ a : Fin n, (2 * (n : ℤ) - 2 * a - 1) * v a
  map_zero' := by simp
  map_add' v w := by simp [mul_add, Finset.sum_add_distrib]

theorem lv_single (i : Fin n) : lv n (Pi.single i 1) = 2 * n - 2 * i - 1 := by
  simp [lv, Pi.single_apply]

theorem lv_wt (a : Fin n ⊕ Fin n) : lv n (wt a) = 2 * n - 1 - 2 * lvl a := by
  rcases a with i | i
  · simp only [wt, lvl, lv_single]
    ring
  · simp only [wt, lvl, map_neg, lv_single]
    ring

theorem lvl_sub_eq_of_wt_sub_eq {a b a' b' : Fin n ⊕ Fin n} (h : wt a - wt b = wt a' - wt b') :
    lvl b - lvl a = lvl b' - lvl a' := by
  have := congrArg (lv n) h
  rw [map_sub, map_sub, lv_wt, lv_wt, lv_wt, lv_wt] at this
  linarith

theorem two_mul_ht (v : Fin n → ℤ) : 2 * ht v = lv n (toStd n v) := by
  let f : (Fin n → ℤ) →+ ℤ :=
    { toFun := fun v => 2 * ht v
      map_zero' := by simp [ht]
      map_add' := fun v w => by simp [ht, Finset.sum_add_distrib, mul_add] }
  let g : (Fin n → ℤ) →+ ℤ := (lv n).comp (toStdLin n).toAddMonoidHom
  have hfg : f = g := by
    refine AddMonoidHom.functions_ext _ f g fun k x => ?_
    have hs : (Pi.single k x : Fin n → ℤ) = x • Pi.single k 1 := by
      funext j
      simp [Pi.single_apply]
    change 2 * ht (Pi.single k x) = lv n (toStdLin n (Pi.single k x))
    rw [toStdLin_apply, hs, toStd_smul, map_zsmul]
    have hht : ht (x • Pi.single k (1 : ℤ)) = x := by
      simp [ht, Pi.single_apply]
    rw [hht, smul_eq_mul]
    by_cases h : k.val + 1 < n
    · rw [toStd_single_of_lt n h, map_sub, lv_single, lv_single]
      push_cast
      ring
    · rw [toStd_single_of_not_lt n h, map_nsmul, lv_single]
      have hk : (k : ℤ) = n - 1 := by
        have := k.2
        omega
      rw [hk]
      simp only [nsmul_eq_mul, Nat.cast_ofNat]
      ring
  exact DFunLike.congr_fun hfg v

theorem ht_eq_lvl {γ : Fin n → ℤ} {r : RootSubgroupIndex n} (hr : stdVec r = toStd n γ) :
    ht γ = lvl (pos1 r).2 - lvl (pos1 r).1 := by
  have h := two_mul_ht γ
  rw [← hr, ← wt_pos1 r, map_sub, lv_wt, lv_wt] at h
  linarith

theorem lvl_of_E_ne_zero {r : RootSubgroupIndex n} {a b : Fin n ⊕ Fin n} (h : E F r a b ≠ 0) :
    lvl b - lvl a = lvl (pos1 r).2 - lvl (pos1 r).1 :=
  lvl_sub_eq_of_wt_sub_eq ((hasDeg_E r a b h).trans (wt_pos1 r).symm)

end CFSG.LieType.Universal.Symplectic.SpExtras
