module

public import CFSG.ClassicalGroups.Unitary.SUnThreeLocalDefs
public import CFSG.Open.LocalVocabulary
import CFSG.GroupTheory.PGroup.RankTwoCommute

public section

namespace CFSG.ClassicalGroups.SUnThreeLocal

open Matrix CFSG.Open CFSG.LieType.Universal.Unitary

variable {L : Type} [Field L] {n : ℕ} {σ : L ≃+* L}

@[expose] noncomputable def rootPos (hσ : ∀ c, σ (σ c) = c) (hn : n = 6 ∨ n = 7) {i j : Fin 3}
    (hij : i ≠ j) (c : L) : SU σ n :=
  rootHom σ hσ ((pos_injective hn).ne hij) (pos_ne_rev_pos hn i i) (pos_ne_rev_pos hn j j)
    (Multiplicative.ofAdd c)

@[expose] noncomputable def longPos (hn : n = 6 ∨ n = 7) (i : Fin 3) (c : L)
    (hc : c + σ c = 0) : SU σ n :=
  longRootHom σ (pos_ne_rev_pos hn i i) (Multiplicative.ofAdd (⟨c, hc⟩ : traceZero σ))

theorem coe_rootPos (hσ : ∀ c, σ (σ c) = c) (hn : n = 6 ∨ n = 7) {i j : Fin 3} (hij : i ≠ j)
    (c : L) :
    (((rootPos hσ hn hij c : SU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) =
      rootMatrix σ (pos hn i) (pos hn j) c :=
  rfl

theorem coe_longPos (hn : n = 6 ∨ n = 7) (i : Fin 3) (c : L) (hc : c + σ c = 0) :
    (((longPos hn i c hc : SU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) =
      longRootMatrix (pos hn i) c :=
  rfl

theorem diagonal_mul_comm_of {ι : Type} [Fintype ι] [DecidableEq ι] (d : ι → L)
    (X : Matrix ι ι L) (h : ∀ i j, X i j ≠ 0 → d i = d j) :
    Matrix.diagonal d * X = X * Matrix.diagonal d := by
  ext i j
  rw [Matrix.diagonal_mul, Matrix.mul_diagonal]
  by_cases hx : X i j = 0
  · simp [hx]
  · rw [h i j hx, mul_comm]

theorem rootMatrix_entry_ne_zero {a b : Fin n} {c : L} {i j : Fin n}
    (h : rootMatrix σ a b c i j ≠ 0) :
    i = j ∨ (i = a ∧ j = b) ∨ (i = Fin.rev b ∧ j = Fin.rev a) := by
  by_contra hc
  apply h
  rw [rootMatrix, Matrix.sub_apply, Matrix.add_apply, Matrix.one_apply, Matrix.single_apply,
    Matrix.single_apply]
  rw [if_neg (fun hh : i = j => hc (Or.inl hh)),
    if_neg (fun hh : a = i ∧ b = j => hc (Or.inr (Or.inl ⟨hh.1.symm, hh.2.symm⟩))),
    if_neg (fun hh : Fin.rev b = i ∧ Fin.rev a = j =>
      hc (Or.inr (Or.inr ⟨hh.1.symm, hh.2.symm⟩)))]
  ring

theorem longRootMatrix_entry_ne_zero {a : Fin n} {c : L} {i j : Fin n}
    (h : longRootMatrix a c i j ≠ 0) : i = j ∨ (i = a ∧ j = Fin.rev a) := by
  by_contra hc
  apply h
  rw [longRootMatrix, Matrix.add_apply, Matrix.one_apply, Matrix.single_apply]
  rw [if_neg (fun hh : i = j => hc (Or.inl hh)),
    if_neg (fun hh : a = i ∧ Fin.rev a = j => hc (Or.inr ⟨hh.1.symm, hh.2.symm⟩))]
  ring

theorem rootMatrix_mulVec (a b : Fin n) (c : L) (w : Fin n → L) :
    rootMatrix σ a b c *ᵥ w =
      w + (c * w b) • (Pi.single a 1 : Fin n → L) -
        (σ c * w (Fin.rev a)) • (Pi.single (Fin.rev b) 1 : Fin n → L) := by
  unfold rootMatrix
  rw [Matrix.sub_mulVec, Matrix.add_mulVec, Matrix.one_mulVec, Matrix.single_mulVec_eq,
    Matrix.single_mulVec_eq]

theorem longRootMatrix_mulVec (a : Fin n) (c : L) (w : Fin n → L) :
    longRootMatrix a c *ᵥ w = w + (c * w (Fin.rev a)) • (Pi.single a 1 : Fin n → L) := by
  unfold longRootMatrix
  rw [Matrix.add_mulVec, Matrix.one_mulVec, Matrix.single_mulVec_eq]

theorem rootMatrix_mul_comm {a b a' b' : Fin n} (c c' : L) (h1 : b ≠ a')
    (h2 : b ≠ Fin.rev b') (h3 : Fin.rev a ≠ a') (h4 : Fin.rev a ≠ Fin.rev b') (h5 : b' ≠ a)
    (h6 : b' ≠ Fin.rev b) (h7 : Fin.rev a' ≠ a) (h8 : Fin.rev a' ≠ Fin.rev b) :
    rootMatrix σ a b c * rootMatrix σ a' b' c' = rootMatrix σ a' b' c' * rootMatrix σ a b c := by
  simp only [rootMatrix, Matrix.add_mul, Matrix.mul_add, Matrix.sub_mul, Matrix.mul_sub,
    Matrix.one_mul, Matrix.mul_one,
    single_mul_single_of_ne _ _ _ _ h1, single_mul_single_of_ne _ _ _ _ h2,
    single_mul_single_of_ne _ _ _ _ h3, single_mul_single_of_ne _ _ _ _ h4,
    single_mul_single_of_ne _ _ _ _ h5, single_mul_single_of_ne _ _ _ _ h6,
    single_mul_single_of_ne _ _ _ _ h7, single_mul_single_of_ne _ _ _ _ h8]
  abel

theorem rootMatrix_mul_longRootMatrix_comm {a b a' : Fin n} (c c' : L) (h1 : b ≠ a')
    (h2 : Fin.rev a ≠ a') (h3 : Fin.rev a' ≠ a) (h4 : Fin.rev a' ≠ Fin.rev b) :
    rootMatrix σ a b c * longRootMatrix a' c' = longRootMatrix a' c' * rootMatrix σ a b c := by
  simp only [rootMatrix, longRootMatrix, Matrix.add_mul, Matrix.mul_add, Matrix.sub_mul,
    Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one,
    single_mul_single_of_ne _ _ _ _ h1, single_mul_single_of_ne _ _ _ _ h2,
    single_mul_single_of_ne _ _ _ _ h3, single_mul_single_of_ne _ _ _ _ h4]
  abel

theorem longRootMatrix_mul_comm {a a' : Fin n} (c c' : L) (h1 : Fin.rev a ≠ a')
    (h2 : Fin.rev a' ≠ a) :
    longRootMatrix a c * longRootMatrix a' c' = longRootMatrix a' c' * longRootMatrix a c := by
  simp only [longRootMatrix, Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one,
    single_mul_single_of_ne _ _ _ _ h1, single_mul_single_of_ne _ _ _ _ h2]
  abel

theorem commute_c₀_rootPos (hσ : ∀ c, σ (σ c) = c) (ζ : FixedCubeRoot σ)
    (hn : n = 6 ∨ n = 7) {i j : Fin 3} (hij : i ≠ j) (c : L)
    (v : Multiplicative (Fin 3 → ZMod 3))
    (hv : Multiplicative.toAdd v i = Multiplicative.toAdd v j) :
    Commute (rootPos hσ hn hij c) (c₀ ζ hn v) := by
  apply Subtype.ext
  apply Units.ext
  simp only [Subgroup.coe_mul, Units.val_mul, coe_rootPos, coe_c₀, coe_diagGL]
  exact (diagonal_mul_comm_of _ _ fun i' j' hX => by
    rcases rootMatrix_entry_ne_zero hX with rfl | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rfl
    · rw [wt_pos, wt_pos, hv]
    · rw [wt_neg, wt_neg, hv]).symm

theorem commute_c₀_longPos (ζ : FixedCubeRoot σ) (hn : n = 6 ∨ n = 7) (i : Fin 3) (c : L)
    (hc : c + σ c = 0) (v : Multiplicative (Fin 3 → ZMod 3))
    (hv : Multiplicative.toAdd v i = 0) :
    Commute (longPos hn i c hc) (c₀ ζ hn v) := by
  apply Subtype.ext
  apply Units.ext
  simp only [Subgroup.coe_mul, Units.val_mul, coe_longPos, coe_c₀, coe_diagGL]
  exact (diagonal_mul_comm_of _ _ fun i' j' hX => by
    rcases longRootMatrix_entry_ne_zero hX with rfl | ⟨rfl, rfl⟩
    · rfl
    · rw [wt_pos, wt_neg, hv]
      exact (congrArg (fun k : ZMod 3 => (ζ.pow k : L)) (neg_zero : (-0 : ZMod 3) = 0)).symm).symm

theorem commute_longPos_longPos (hn : n = 6 ∨ n = 7) (i k : Fin 3) (c d : L) (hc : c + σ c = 0)
    (hd : d + σ d = 0) : Commute (longPos hn i c hc) (longPos hn k d hd) := by
  apply Subtype.ext
  apply Units.ext
  simp only [Subgroup.coe_mul, Units.val_mul, coe_longPos]
  exact longRootMatrix_mul_comm c d (rev_pos_ne_pos hn i k) (rev_pos_ne_pos hn k i)

theorem commute_rootPos_longPos (hσ : ∀ c, σ (σ c) = c) (hn : n = 6 ∨ n = 7) {i j : Fin 3}
    (hij : i ≠ j) (k : Fin 3) (hjk : j ≠ k) (c d : L) (hd : d + σ d = 0) :
    Commute (rootPos hσ hn hij c) (longPos hn k d hd) := by
  apply Subtype.ext
  apply Units.ext
  simp only [Subgroup.coe_mul, Units.val_mul, coe_rootPos, coe_longPos]
  exact rootMatrix_mul_longRootMatrix_comm c d ((pos_injective hn).ne hjk)
    (rev_pos_ne_pos hn i k) (rev_pos_ne_pos hn k i) ((rev_pos_injective hn).ne hjk.symm)

theorem commute_rootPos_rootPos (hσ : ∀ c, σ (σ c) = c) (hn : n = 6 ∨ n = 7) {i j k l : Fin 3}
    (hij : i ≠ j) (hkl : k ≠ l) (hjk : j ≠ k) (hil : i ≠ l) (c d : L) :
    Commute (rootPos hσ hn hij c) (rootPos hσ hn hkl d) := by
  apply Subtype.ext
  apply Units.ext
  simp only [Subgroup.coe_mul, Units.val_mul, coe_rootPos]
  exact rootMatrix_mul_comm c d ((pos_injective hn).ne hjk) (pos_ne_rev_pos hn j l)
    (rev_pos_ne_pos hn i k) ((rev_pos_injective hn).ne hil) ((pos_injective hn).ne hil.symm)
    (pos_ne_rev_pos hn l j) (rev_pos_ne_pos hn k i) ((rev_pos_injective hn).ne hjk.symm)

theorem orderOf_rootPos {r : ℕ} [CharP L r] [Fact r.Prime] (hσ : ∀ c, σ (σ c) = c)
    (hn : n = 6 ∨ n = 7) {i j : Fin 3} (hij : i ≠ j) {c : L} (hc : c ≠ 0) :
    orderOf (rootPos hσ hn hij c) = r := by
  refine orderOf_eq_prime ?_ ?_
  · change (rootHom σ hσ ((pos_injective hn).ne hij) (pos_ne_rev_pos hn i i)
      (pos_ne_rev_pos hn j j) (Multiplicative.ofAdd c)) ^ r = 1
    rw [← map_pow, ← ofAdd_nsmul, nsmul_eq_mul, CharP.cast_eq_zero, zero_mul,
      ofAdd_zero, map_one]
  · intro h1
    have h2 := congrArg (fun g : SU σ n =>
      (((g : GL (Fin n) L)) : Matrix (Fin n) (Fin n) L) (pos hn i) (pos hn j)) h1
    rw [coe_rootPos, Subgroup.coe_one, Units.val_one,
      Matrix.one_apply_ne ((pos_injective hn).ne hij)] at h2
    have h3 : rootMatrix σ (pos hn i) (pos hn j) c (pos hn i) (pos hn j) = c := by
      rw [rootMatrix, Matrix.sub_apply, Matrix.add_apply,
        Matrix.one_apply_ne ((pos_injective hn).ne hij), Matrix.single_apply_same,
        Matrix.single_apply_of_ne _ _ _ _ _ (fun hh => rev_pos_ne_pos hn j i hh.1)]
      ring
    exact hc (h3.symm.trans h2)

theorem orderOf_longPos {r : ℕ} [CharP L r] [Fact r.Prime] (hn : n = 6 ∨ n = 7) (i : Fin 3) {c : L}
    (hcσ : c + σ c = 0) (hc : c ≠ 0) : orderOf (longPos hn i c hcσ) = r := by
  refine orderOf_eq_prime ?_ ?_
  · have hz : r • (⟨c, hcσ⟩ : traceZero σ) = 0 := by
      apply Subtype.ext
      show r • c = (0 : L)
      rw [nsmul_eq_mul, CharP.cast_eq_zero, zero_mul]
    change (longRootHom σ (pos_ne_rev_pos hn i i)
      (Multiplicative.ofAdd (⟨c, hcσ⟩ : traceZero σ))) ^ r = 1
    rw [← map_pow, ← ofAdd_nsmul, hz, ofAdd_zero, map_one]
  · intro h1
    have h2 := congrArg (fun g : SU σ n =>
      (((g : GL (Fin n) L)) : Matrix (Fin n) (Fin n) L) (pos hn i) (Fin.rev (pos hn i))) h1
    rw [coe_longPos, Subgroup.coe_one, Units.val_one,
      Matrix.one_apply_ne (pos_ne_rev_pos hn i i)] at h2
    have h3 : longRootMatrix (pos hn i) c (pos hn i) (Fin.rev (pos hn i)) = c := by
      rw [longRootMatrix, Matrix.add_apply, Matrix.one_apply_ne (pos_ne_rev_pos hn i i),
        Matrix.single_apply_same]
      ring
    exact hc (h3.symm.trans h2)

theorem longPos_mulVec_single_rev_pos_of_ne (hn : n = 6 ∨ n = 7) {i k : Fin 3} (hik : i ≠ k)
    (c : L) (hc : c + σ c = 0) :
    (((longPos hn i c hc : SU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) *ᵥ
        (Pi.single (Fin.rev (pos hn k)) 1 : Fin n → L) =
      (Pi.single (Fin.rev (pos hn k)) 1 : Fin n → L) := by
  rw [coe_longPos, longRootMatrix_mulVec,
    Pi.single_eq_of_ne (Fin.rev_injective.ne ((pos_injective hn).ne hik)), mul_zero, zero_smul,
    add_zero]

theorem longPos_mulVec_single_rev_pos_ne (hn : n = 6 ∨ n = 7) (i : Fin 3) {c : L}
    (hcσ : c + σ c = 0) (hc : c ≠ 0) :
    (((longPos hn i c hcσ : SU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) *ᵥ
        (Pi.single (Fin.rev (pos hn i)) 1 : Fin n → L) ≠
      (Pi.single (Fin.rev (pos hn i)) 1 : Fin n → L) := by
  rw [coe_longPos, longRootMatrix_mulVec]
  intro h
  have h1 := congrFun h (pos hn i)
  rw [Pi.add_apply, Pi.smul_apply, Pi.single_eq_of_ne (pos_ne_rev_pos hn i i),
    Pi.single_eq_same, Pi.single_eq_same] at h1
  exact hc (by simpa using h1)

theorem longPos_mulVec_single_pos (hn : n = 6 ∨ n = 7) (i k : Fin 3) (c : L)
    (hc : c + σ c = 0) :
    (((longPos hn i c hc : SU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) *ᵥ
        (Pi.single (pos hn k) 1 : Fin n → L) = (Pi.single (pos hn k) 1 : Fin n → L) := by
  rw [coe_longPos, longRootMatrix_mulVec, Pi.single_eq_of_ne (rev_pos_ne_pos hn i k), mul_zero,
    zero_smul, add_zero]

theorem rootPos_mulVec_single_pos_of_ne (hσ : ∀ c, σ (σ c) = c) (hn : n = 6 ∨ n = 7)
    {i j : Fin 3} (hij : i ≠ j) {k : Fin 3} (hkj : k ≠ j) (c : L) :
    (((rootPos hσ hn hij c : SU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) *ᵥ
        (Pi.single (pos hn k) 1 : Fin n → L) = (Pi.single (pos hn k) 1 : Fin n → L) := by
  rw [coe_rootPos, rootMatrix_mulVec,
    Pi.single_eq_of_ne (((pos_injective hn).ne hkj).symm),
    Pi.single_eq_of_ne (rev_pos_ne_pos hn i k), mul_zero, zero_smul, mul_zero, zero_smul,
    add_zero, sub_zero]

theorem rootPos_mulVec_single_pos_ne (hσ : ∀ c, σ (σ c) = c) (hn : n = 6 ∨ n = 7)
    {i j : Fin 3} (hij : i ≠ j) {c : L} (hc : c ≠ 0) :
    (((rootPos hσ hn hij c : SU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) *ᵥ
        (Pi.single (pos hn j) 1 : Fin n → L) ≠ (Pi.single (pos hn j) 1 : Fin n → L) := by
  rw [coe_rootPos, rootMatrix_mulVec]
  intro h
  have h1 := congrFun h (pos hn i)
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, Pi.single_eq_same,
    Pi.single_eq_of_ne ((pos_injective hn).ne hij),
    Pi.single_eq_of_ne (rev_pos_ne_pos hn i j),
    Pi.single_eq_of_ne (pos_ne_rev_pos hn i j)] at h1
  exact hc (by simpa using h1)

theorem one_le_pRank_of_orderOf {G : Type*} [Group G] [Finite G] {r : ℕ} [Fact r.Prime]
    {H : Subgroup G} {x : G} (hx : x ∈ H) (hxo : orderOf x = r) : 1 ≤ pRank r H := by
  have hcard : Nat.card (Subgroup.zpowers x) = r := by rw [Nat.card_zpowers, hxo]
  exact CFSG.SectionRank.le_pRank (Fact.out : r.Prime).one_lt (Subgroup.zpowers_le.mpr hx)
    (CFSG.GroupTheory.isElemAbelian_of_card_prime hcard) (by simpa using hcard)

theorem two_le_pRank_of_mulVec [Finite L] {r : ℕ} [Fact r.Prime] {H : Subgroup (SU σ n)}
    {x y : SU σ n} (hx : x ∈ H) (hy : y ∈ H) (hxo : orderOf x = r) (hyo : orderOf y = r)
    (hxy : Commute x y) {w : Fin n → L}
    (hxw : ((x : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) *ᵥ w = w)
    (hyw : ((y : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) *ᵥ w ≠ w) : 2 ≤ pRank r H := by
  let W : Subgroup (SU σ n) :=
    { carrier := {g : SU σ n | (((g : GL (Fin n) L)) : Matrix (Fin n) (Fin n) L) *ᵥ w = w}
      one_mem' := by simp [Matrix.one_mulVec]
      mul_mem' := by
        intro a b ha hb
        simp only [Set.mem_setOf_eq, Subgroup.coe_mul, Units.val_mul,
          ← Matrix.mulVec_mulVec] at ha hb ⊢
        rw [hb, ha]
      inv_mem' := by
        intro a ha
        simp only [Set.mem_setOf_eq] at ha ⊢
        have h1 : (((a : GL (Fin n) L)⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) *ᵥ
            (((a : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) *ᵥ w) = w := by
          rw [Matrix.mulVec_mulVec]
          simp
        rw [ha] at h1
        simpa using h1 }
  have hxW : x ∈ W := by
    show ((x : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) *ᵥ w = w
    exact hxw
  have hyx : y ∉ Subgroup.zpowers x := fun hmem =>
    hyw (show ((y : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) *ᵥ w = w from
      Subgroup.zpowers_le.mpr hxW hmem)
  exact CFSG.GroupTheory.two_le_pRank_of_commute hx hy hxo hyo hxy hyx

end CFSG.ClassicalGroups.SUnThreeLocal
