module

public import CFSG.ClassicalGroups.Symplectic.Model
public import CFSG.LieType.Steinberg.Classical.Symplectic.RankOne
public import CFSG.Open.StatedAPI

public section

namespace CFSG.ClassicalInvolution.Models.SymplecticPairs

open Matrix CFSG.LieType.Steinberg.Sp CFSG.Assembly.LowTwoRank
open CFSG.LieType.Steinberg (sl2Upper sl2Lower)
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_apply mat_injective mat_elt_positiveLong
  mat_elt_negativeLong elt)
open scoped MatrixGroups

section Gram

variable (K : Type) [Field K] {n : ℕ}

@[expose] def par : Fin n ⊕ Fin n → Fin n ⊕ Fin n := Sum.swap

@[expose] def sgn : Fin n ⊕ Fin n → K := Sum.elim (fun _ => 1) (fun _ => -1)

variable (n) in
@[expose] def gram : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K := fromBlocks 0 1 (-1) 0

variable {K}

@[simp] theorem par_par (a : Fin n ⊕ Fin n) : par (par a) = a := by
  cases a <;> rfl

@[simp] theorem par_inl (i : Fin n) : par (Sum.inl i : Fin n ⊕ Fin n) = Sum.inr i := rfl

@[simp] theorem par_inr (i : Fin n) : par (Sum.inr i : Fin n ⊕ Fin n) = Sum.inl i := rfl

theorem par_injective : Function.Injective (par : Fin n ⊕ Fin n → Fin n ⊕ Fin n) :=
  fun a b h => by rw [← par_par a, h, par_par]

@[simp] theorem sgn_inl (i : Fin n) : sgn K (Sum.inl i : Fin n ⊕ Fin n) = 1 := rfl

@[simp] theorem sgn_inr (i : Fin n) : sgn K (Sum.inr i : Fin n ⊕ Fin n) = -1 := rfl

theorem sgn_ne_zero (a : Fin n ⊕ Fin n) : sgn K a ≠ 0 := by
  cases a <;> simp [sgn]

theorem gram_apply (a b : Fin n ⊕ Fin n) :
    gram K n a b = if b = par a then sgn K a else 0 := by
  rcases a with i | i <;> rcases b with j | j <;>
    simp [gram, par, sgn, Matrix.one_apply, eq_comm, neg_ite]

theorem transpose_mul_gram_apply (M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K)
    (a c : Fin n ⊕ Fin n) : (Mᵀ * gram K n) a c = M (par c) a * sgn K (par c) := by
  simp only [Matrix.mul_apply, transpose_apply, gram_apply]
  rw [Finset.sum_eq_single (par c)]
  · simp
  · intro d _ hd
    rw [ite_eq_right_iff.mpr (fun h => absurd (by rw [h, par_par]) hd), mul_zero]
  · simp

theorem transpose_mul_gram_mul_apply (M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K)
    (a b : Fin n ⊕ Fin n) :
    (Mᵀ * gram K n * M) a b = ∑ c, M c a * (sgn K c * M (par c) b) := by
  rw [Matrix.mul_apply]
  simp only [transpose_mul_gram_apply]
  rw [← (Equiv.sumComm (Fin n) (Fin n)).sum_comp]
  refine Finset.sum_congr rfl fun c _ => ?_
  have h : (Equiv.sumComm (Fin n) (Fin n)) c = par c := rfl
  rw [h, par_par]
  ring

theorem gram_eq_neg_J : gram K n = -Matrix.J (Fin n) K :=
  CFSG.ClassicalGroups.Symplectic.blueprintGram_eq_neg_J

theorem gram_mul_gram : gram K n * gram K n = -1 := by
  rw [gram_eq_neg_J, Matrix.neg_mul, Matrix.mul_neg, neg_neg, Matrix.J_squared]

end Gram

section Support

variable {K : Type} [Field K] {n : ℕ}

theorem mem_statedSp_iff {g : GL (Fin n ⊕ Fin n) K} :
    g ∈ StatedSp n K ↔
      (g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K)ᵀ * gram K n *
        (g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) = gram K n :=
  CFSG.Open.StatedAPI.mem_statedSp_iff

theorem mat_transpose_mul_gram_mul (x : StatedSp n K) :
    (mat n K x)ᵀ * gram K n * mat n K x = gram K n :=
  mem_statedSp_iff.1 x.2

@[expose] noncomputable def ofSymplecticMat (M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K)
    (hM : Mᵀ * gram K n * M = gram K n) : StatedSp n K :=
  ⟨⟨M, -(gram K n * Mᵀ * gram K n),
    mul_eq_one_comm.1 (by
      calc -(gram K n * Mᵀ * gram K n) * M = -(gram K n * (Mᵀ * gram K n * M)) := by
            simp only [Matrix.neg_mul, Matrix.mul_assoc]
        _ = 1 := by rw [hM, gram_mul_gram, neg_neg]),
    by
      calc -(gram K n * Mᵀ * gram K n) * M = -(gram K n * (Mᵀ * gram K n * M)) := by
            simp only [Matrix.neg_mul, Matrix.mul_assoc]
        _ = 1 := by rw [hM, gram_mul_gram, neg_neg]⟩,
    mem_statedSp_iff.2 hM⟩

theorem mat_ofSymplecticMat (M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K)
    (hM : Mᵀ * gram K n * M = gram K n) : mat n K (ofSymplecticMat M hM) = M := rfl

@[expose] def IsSupp (S : Set (Fin n ⊕ Fin n)) (M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) :
    Prop :=
  ∀ r t, ¬(r ∈ S ∧ t ∈ S) → M r t = (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) r t

theorem IsSupp.one (S : Set (Fin n ⊕ Fin n)) :
    IsSupp S (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) := fun _ _ _ => rfl

theorem IsSupp.mul {S : Set (Fin n ⊕ Fin n)} {M N : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K}
    (hM : IsSupp S M) (hN : IsSupp S N) : IsSupp S (M * N) := by
  intro r t hrt
  rw [not_and_or] at hrt
  rcases hrt with hr | ht
  · have h : ∀ u, M r u = (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) r u :=
      fun u => hM r u (fun h => hr h.1)
    rw [Matrix.mul_apply, Finset.sum_congr rfl (fun u _ => by rw [h u]), ← Matrix.mul_apply,
      Matrix.one_mul]
    exact hN r t (fun h => hr h.1)
  · have h : ∀ u, N u t = (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) u t :=
      fun u => hN u t (fun h => ht h.2)
    rw [Matrix.mul_apply, Finset.sum_congr rfl (fun u _ => by rw [h u]), ← Matrix.mul_apply,
      Matrix.mul_one]
    exact hM r t (fun h => ht h.2)

theorem IsSupp.of_mul_eq_one {S : Set (Fin n ⊕ Fin n)}
    {M N : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K} (hM : IsSupp S M) (hNM : N * M = 1)
    (hMN : M * N = 1) : IsSupp S N := by
  intro r t hrt
  rw [not_and_or] at hrt
  rcases hrt with hr | ht
  · have h : ∀ u, M r u = (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) r u :=
      fun u => hM r u (fun h => hr h.1)
    have e : (M * N) r t = N r t := by
      rw [Matrix.mul_apply, Finset.sum_congr rfl (fun u _ => by rw [h u]), ← Matrix.mul_apply,
        Matrix.one_mul]
    rw [← e, hMN]
  · have h : ∀ u, M u t = (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) u t :=
      fun u => hM u t (fun h => ht h.2)
    have e : (N * M) r t = N r t := by
      rw [Matrix.mul_apply, Finset.sum_congr rfl (fun u _ => by rw [h u]), ← Matrix.mul_apply,
        Matrix.mul_one]
    rw [← e, hNM]

@[expose] def suppGroup (S : Set (Fin n ⊕ Fin n)) : Subgroup (StatedSp n K) where
  carrier := {x | IsSupp S (mat n K x)}
  one_mem' := by
    change IsSupp S (mat n K 1)
    rw [map_one]
    exact IsSupp.one S
  mul_mem' := by
    intro x y hx hy
    change IsSupp S (mat n K (x * y))
    rw [map_mul]
    exact IsSupp.mul hx hy
  inv_mem' := by
    intro x hx
    change IsSupp S (mat n K x⁻¹)
    refine IsSupp.of_mul_eq_one hx ?_ ?_
    · rw [← map_mul, inv_mul_cancel, map_one]
    · rw [← map_mul, mul_inv_cancel, map_one]

theorem mem_suppGroup {S : Set (Fin n ⊕ Fin n)} {x : StatedSp n K} :
    x ∈ suppGroup S ↔ IsSupp S (mat n K x) := Iff.rfl

@[expose] def ParClosed (S : Set (Fin n ⊕ Fin n)) : Prop := ∀ a ∈ S, par a ∈ S

theorem ParClosed.compl {S : Set (Fin n ⊕ Fin n)} (hS : ParClosed S) : ParClosed Sᶜ :=
  fun a ha h => ha (by simpa using hS _ h)

theorem isSupp_of_fix {S : Set (Fin n ⊕ Fin n)} (hS : ParClosed S) (x : StatedSp n K)
    (hfix : ∀ t ∉ S, ∀ r, mat n K x r t = (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) r t) :
    IsSupp S (mat n K x) := by
  intro r t hrt
  by_cases ht : t ∈ S
  · have hr : r ∉ S := fun hr => hrt ⟨hr, ht⟩
    have ha : par r ∉ S := fun h => hr (by simpa using hS _ h)
    have key := congrFun (congrFun (mat_transpose_mul_gram_mul x) (par r)) t
    rw [transpose_mul_gram_mul_apply, gram_apply] at key
    have hsum : ∑ c, mat n K x c (par r) * (sgn K c * mat n K x (par c) t) =
        sgn K (par r) * mat n K x r t := by
      rw [Finset.sum_eq_single (par r)]
      · rw [hfix _ ha, Matrix.one_apply_eq, one_mul, par_par]
      · intro c _ hc
        rw [hfix _ ha c, Matrix.one_apply_ne hc, zero_mul]
      · simp
    rw [hsum] at key
    have hne : t ≠ par (par r) := by
      rw [par_par]
      exact fun h => hr (h ▸ ht)
    rw [ite_eq_right_iff.mpr (fun h => absurd h hne)] at key
    have h0 := (mul_eq_zero.1 key).resolve_left (sgn_ne_zero _)
    rw [h0, Matrix.one_apply_ne]
    exact fun h => hr (h ▸ ht)
  · exact hfix t ht r

theorem mem_suppGroup_iff {S : Set (Fin n ⊕ Fin n)} (hS : ParClosed S) {x : StatedSp n K} :
    x ∈ suppGroup S ↔
      ∀ t ∉ S, ∀ r, mat n K x r t = (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) r t :=
  ⟨fun h t ht r => h r t (fun h' => ht h'.2), isSupp_of_fix hS x⟩

end Support

section Fixing

variable {K : Type} [Field K] {n : ℕ}

theorem mulVec_single_one_apply {R : Type*} [Semiring R] {m ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix m ι R) (j : ι) (r : m) : (M *ᵥ Pi.single j (1 : R)) r = M r j := by
  rw [Matrix.mulVec_single_one]
  rfl

@[expose] def fixing (W : Set (Fin n ⊕ Fin n → K)) : Subgroup (StatedSp n K) where
  carrier := {x | ∀ v ∈ W, mat n K x *ᵥ v = v}
  one_mem' := by simp
  mul_mem' := by
    intro x y hx hy v hv
    rw [map_mul, ← Matrix.mulVec_mulVec, hy v hv, hx v hv]
  inv_mem' := by
    intro x hx v hv
    calc mat n K x⁻¹ *ᵥ v = mat n K x⁻¹ *ᵥ (mat n K x *ᵥ v) := by rw [hx v hv]
      _ = v := by
        rw [Matrix.mulVec_mulVec, ← map_mul, inv_mul_cancel, map_one, Matrix.one_mulVec]

theorem mem_fixing {W : Set (Fin n ⊕ Fin n → K)} {x : StatedSp n K} :
    x ∈ fixing W ↔ ∀ v ∈ W, mat n K x *ᵥ v = v := Iff.rfl

theorem fixing_anti {W W' : Set (Fin n ⊕ Fin n → K)} (h : W ⊆ W') : fixing W' ≤ fixing W :=
  fun _ hx v hv => hx v (h hv)

@[expose] def fixSpace (i : StatedSp n K) : Submodule K (Fin n ⊕ Fin n → K) where
  carrier := {v | mat n K i *ᵥ v = v}
  add_mem' := by
    intro v w hv hw
    change mat n K i *ᵥ v = v at hv
    change mat n K i *ᵥ w = w at hw
    change mat n K i *ᵥ (v + w) = v + w
    rw [Matrix.mulVec_add, hv, hw]
  zero_mem' := by simp
  smul_mem' := by
    intro c v hv
    change mat n K i *ᵥ v = v at hv
    change mat n K i *ᵥ (c • v) = c • v
    rw [Matrix.mulVec_smul, hv]

@[expose] def minusSpace (i : StatedSp n K) : Submodule K (Fin n ⊕ Fin n → K) where
  carrier := {v | mat n K i *ᵥ v = -v}
  add_mem' := by
    intro v w hv hw
    change mat n K i *ᵥ v = -v at hv
    change mat n K i *ᵥ w = -w at hw
    change mat n K i *ᵥ (v + w) = -(v + w)
    rw [Matrix.mulVec_add, hv, hw, neg_add]
  zero_mem' := by simp
  smul_mem' := by
    intro c v hv
    change mat n K i *ᵥ v = -v at hv
    change mat n K i *ᵥ (c • v) = -(c • v)
    rw [Matrix.mulVec_smul, hv, smul_neg]

theorem mem_fixSpace {i : StatedSp n K} {v : Fin n ⊕ Fin n → K} :
    v ∈ fixSpace i ↔ mat n K i *ᵥ v = v := Iff.rfl

theorem mem_minusSpace {i : StatedSp n K} {v : Fin n ⊕ Fin n → K} :
    v ∈ minusSpace i ↔ mat n K i *ᵥ v = -v := Iff.rfl

@[expose] def longRootGroup (i : StatedSp n K) : Subgroup (StatedSp n K) :=
  fixing (fixSpace i : Set (Fin n ⊕ Fin n → K))

theorem mem_longRootGroup {i x : StatedSp n K} :
    x ∈ longRootGroup i ↔ ∀ v ∈ fixSpace i, mat n K x *ᵥ v = v := Iff.rfl

@[expose] def complGroup (i : StatedSp n K) : Subgroup (StatedSp n K) :=
  fixing (minusSpace i : Set (Fin n ⊕ Fin n → K))

theorem mem_complGroup {i x : StatedSp n K} :
    x ∈ complGroup i ↔ ∀ v ∈ minusSpace i, mat n K x *ᵥ v = v := Iff.rfl

theorem mulVec_mem_fixSpace {i c : StatedSp n K} (hc : c * i = i * c) {v : Fin n ⊕ Fin n → K}
    (hv : v ∈ fixSpace i) : mat n K c *ᵥ v ∈ fixSpace i := by
  rw [mem_fixSpace, Matrix.mulVec_mulVec, ← map_mul, ← hc, map_mul, ← Matrix.mulVec_mulVec,
    mem_fixSpace.1 hv]

theorem conj_mem_longRootGroup {i c x : StatedSp n K} (hc : c * i = i * c)
    (hx : x ∈ longRootGroup i) : c * x * c⁻¹ ∈ longRootGroup i := by
  have hc' : c⁻¹ * i = i * c⁻¹ := (Commute.inv_left (show Commute c i from hc)).eq
  intro v hv
  rw [map_mul, map_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    mem_longRootGroup.1 hx _ (mulVec_mem_fixSpace hc' hv), Matrix.mulVec_mulVec, ← map_mul,
    mul_inv_cancel, map_one, Matrix.one_mulVec]

end Fixing

section LongBlock

variable {K : Type} [Field K] {n : ℕ}

@[expose] def coords (k : Fin n) : Set (Fin n ⊕ Fin n) := {Sum.inl k, Sum.inr k}

theorem mem_coords {k : Fin n} {a : Fin n ⊕ Fin n} :
    a ∈ coords k ↔ a = Sum.inl k ∨ a = Sum.inr k := by
  simp [coords]

instance (k : Fin n) : DecidablePred (· ∈ coords k) := fun _ =>
  decidable_of_iff _ mem_coords.symm

theorem inl_mem_coords (k : Fin n) : (Sum.inl k : Fin n ⊕ Fin n) ∈ coords k :=
  mem_coords.2 (Or.inl rfl)

theorem inr_mem_coords (k : Fin n) : (Sum.inr k : Fin n ⊕ Fin n) ∈ coords k :=
  mem_coords.2 (Or.inr rfl)

theorem parClosed_coords (k : Fin n) : ParClosed (coords k) := by
  intro a ha
  rcases mem_coords.1 ha with rfl | rfl
  · exact inr_mem_coords k
  · exact inl_mem_coords k

@[expose] def stdBlock (k : Fin n) (M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) :
    Matrix (Fin 2) (Fin 2) K :=
  !![M (Sum.inl k) (Sum.inl k), M (Sum.inl k) (Sum.inr k);
    M (Sum.inr k) (Sum.inl k), M (Sum.inr k) (Sum.inr k)]

theorem blockMat_apply_of_not {κ : Type*} [DecidableEq κ] {p q : κ} (hpq : p ≠ q)
    (A : Matrix (Fin 2) (Fin 2) K) {r t : κ} (h : ¬((r = p ∨ r = q) ∧ (t = p ∨ t = q))) :
    blockMat p q A r t = (1 : Matrix κ κ K) r t := by
  rw [not_and_or, not_or, not_or] at h
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · simp [blockMat, h1, h2]
  · by_cases hr1 : r = p
    · subst hr1
      simp [blockMat, h1, h2, Matrix.one_apply, Ne.symm h1]
    · by_cases hr2 : r = q
      · subst hr2
        simp [blockMat, h1, h2, Matrix.one_apply, Ne.symm h2]
      · simp [blockMat, hr1, hr2]

theorem blockMat_apply_of_not_mem (k : Fin n) (A : Matrix (Fin 2) (Fin 2) K)
    {r t : Fin n ⊕ Fin n} (h : ¬(r ∈ coords k ∧ t ∈ coords k)) :
    blockMat (Sum.inl k) (Sum.inr k) A r t = (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) r t :=
  blockMat_apply_of_not Sum.inl_ne_inr A (by simpa only [mem_coords] using h)

theorem isSupp_blockMat (k : Fin n) (A : Matrix (Fin 2) (Fin 2) K) :
    IsSupp (coords k) (blockMat (Sum.inl k) (Sum.inr k) A) :=
  fun _ _ h => blockMat_apply_of_not_mem k A h

theorem stdBlock_blockMat (k : Fin n) (A : Matrix (Fin 2) (Fin 2) K) :
    stdBlock k (blockMat (Sum.inl k) (Sum.inr k) A) = A := by
  have hpq : (Sum.inl k : Fin n ⊕ Fin n) ≠ Sum.inr k := Sum.inl_ne_inr
  ext i j
  fin_cases i <;> fin_cases j <;> simp [stdBlock, blockMat, hpq.symm]

theorem eq_blockMat_stdBlock {k : Fin n} {M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K}
    (hM : IsSupp (coords k) M) :
    M = blockMat (Sum.inl k) (Sum.inr k) (stdBlock k M) := by
  have hpq : (Sum.inl k : Fin n ⊕ Fin n) ≠ Sum.inr k := Sum.inl_ne_inr
  ext r t
  by_cases h : r ∈ coords k ∧ t ∈ coords k
  · obtain ⟨hr, ht⟩ := h
    rcases mem_coords.1 hr with rfl | rfl <;> rcases mem_coords.1 ht with rfl | rfl <;>
      simp [stdBlock, blockMat, hpq.symm]
  · rw [hM r t h, blockMat_apply_of_not_mem k _ h]

theorem blockHom_sl2Upper (k : Fin n) (c : K) :
    blockHom K (Sum.inl_ne_inr : (Sum.inl k : Fin n ⊕ Fin n) ≠ Sum.inr k) (sl2Upper c) =
      (elt (.positiveLong k) c : GL (Fin n ⊕ Fin n) K) :=
  Units.ext (by
    rw [blockHom_upper, TauCeti.coe_transvectionUnit, ← mat_apply, mat_elt_positiveLong])

theorem blockHom_sl2Lower (k : Fin n) (c : K) :
    blockHom K (Sum.inl_ne_inr : (Sum.inl k : Fin n ⊕ Fin n) ≠ Sum.inr k) (sl2Lower c) =
      (elt (.negativeLong k) c : GL (Fin n ⊕ Fin n) K) :=
  Units.ext (by
    rw [blockHom_lower, TauCeti.coe_transvectionUnit, ← mat_apply, mat_elt_negativeLong])

theorem blockHom_mem_statedSp (k : Fin n) (A : SL(2, K)) :
    blockHom K (Sum.inl_ne_inr : (Sum.inl k : Fin n ⊕ Fin n) ≠ Sum.inr k) A ∈ StatedSp n K := by
  have hle : Subgroup.closure (Set.range (sl2Upper (k := K)) ∪ Set.range sl2Lower) ≤
      (StatedSp n K).comap
        (blockHom K (Sum.inl_ne_inr : (Sum.inl k : Fin n ⊕ Fin n) ≠ Sum.inr k)) := by
    rw [Subgroup.closure_le]
    rintro _ (⟨c, rfl⟩ | ⟨c, rfl⟩)
    · change blockHom K Sum.inl_ne_inr (sl2Upper c) ∈ StatedSp n K
      rw [blockHom_sl2Upper]
      exact (elt _ c).2
    · change blockHom K Sum.inl_ne_inr (sl2Lower c) ∈ StatedSp n K
      rw [blockHom_sl2Lower]
      exact (elt _ c).2
  exact hle (mem_closure_sl2 A)

@[expose] def mkSL (B : Matrix (Fin 2) (Fin 2) K) (h : B.det = 1) : SL(2, K) := ⟨B, h⟩

@[simp] theorem coe_mkSL (B : Matrix (Fin 2) (Fin 2) K) (h : B.det = 1) :
    (mkSL B h : Matrix (Fin 2) (Fin 2) K) = B := rfl

variable (K n) in
@[expose] noncomputable def longBlock (k : Fin n) : SL(2, K) →* StatedSp n K :=
  (blockHom K (Sum.inl_ne_inr : (Sum.inl k : Fin n ⊕ Fin n) ≠ Sum.inr k)).codRestrict
    (StatedSp n K) (blockHom_mem_statedSp k)

theorem mat_longBlock (k : Fin n) (A : SL(2, K)) :
    mat n K (longBlock K n k A) =
      blockMat (Sum.inl k) (Sum.inr k) (A : Matrix (Fin 2) (Fin 2) K) := rfl

theorem longBlock_sl2Upper (k : Fin n) (c : K) :
    longBlock K n k (sl2Upper c) = elt (.positiveLong k) c :=
  Subtype.ext (blockHom_sl2Upper k c)

theorem longBlock_sl2Lower (k : Fin n) (c : K) :
    longBlock K n k (sl2Lower c) = elt (.negativeLong k) c :=
  Subtype.ext (blockHom_sl2Lower k c)

theorem longBlock_injective (k : Fin n) : Function.Injective (longBlock K n k) := fun _ _ h =>
  blockHom_injective Sum.inl_ne_inr (congrArg Subtype.val h)

theorem isSupp_longBlock (k : Fin n) (A : SL(2, K)) :
    IsSupp (coords k) (mat n K (longBlock K n k A)) :=
  isSupp_blockMat k _

theorem det_stdBlock_eq_one (x : StatedSp n K) (k : Fin n)
    (hcol : ∀ c, c ∉ coords k → mat n K x c (Sum.inl k) = 0) :
    (stdBlock k (mat n K x)).det = 1 := by
  have hpq : (Sum.inl k : Fin n ⊕ Fin n) ≠ Sum.inr k := Sum.inl_ne_inr
  have key := congrFun (congrFun (mat_transpose_mul_gram_mul x) (Sum.inl k)) (Sum.inr k)
  rw [transpose_mul_gram_mul_apply, gram_apply,
    Finset.sum_eq_add (Sum.inl k) (Sum.inr k) hpq] at key
  · simp only [par_inl, par_inr, sgn_inl, sgn_inr, ite_true] at key
    rw [Matrix.det_fin_two]
    simp only [stdBlock, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one]
    linear_combination key
  · intro c _ hc
    rw [hcol c (fun h => by rcases mem_coords.1 h with rfl | rfl <;> simp_all), zero_mul]
  · simp
  · simp

theorem range_longBlock (k : Fin n) : (longBlock K n k).range = suppGroup (coords k) := by
  ext x
  constructor
  · rintro ⟨A, rfl⟩
    exact isSupp_longBlock k A
  · intro hx
    have hdet : (stdBlock k (mat n K x)).det = 1 :=
      det_stdBlock_eq_one x k fun c hc => by
        rw [hx c _ (fun h => hc h.1)]
        exact Matrix.one_apply_ne (fun h => hc (h ▸ inl_mem_coords k))
    refine ⟨mkSL (stdBlock k (mat n K x)) hdet, mat_injective ?_⟩
    rw [mat_longBlock, coe_mkSL]
    exact (eq_blockMat_stdBlock hx).symm

end LongBlock

section Standard

variable {K : Type} [Field K] {n : ℕ}

theorem mulVec_eq_self_of_isSupp {S : Set (Fin n ⊕ Fin n)}
    {M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K} (hM : IsSupp S M) {v : Fin n ⊕ Fin n → K}
    (hv : ∀ t ∈ S, v t = 0) : M *ᵥ v = v := by
  have h : M *ᵥ v = (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) *ᵥ v := by
    funext r
    simp only [Matrix.mulVec, dotProduct]
    refine Finset.sum_congr rfl fun t _ => ?_
    by_cases ht : t ∈ S
    · rw [hv t ht, mul_zero, mul_zero]
    · rw [hM r t (fun h' => ht h'.2)]
  rw [h, Matrix.one_mulVec]

variable (K n) in
@[expose] noncomputable def longInv (k : Fin n) : StatedSp n K := longBlock K n k (-1)

theorem mat_longInv (k : Fin n) :
    mat n K (longInv K n k) = Matrix.diagonal (fun a => if a ∈ coords k then (-1 : K) else 1) := by
  have hpq : (Sum.inl k : Fin n ⊕ Fin n) ≠ Sum.inr k := Sum.inl_ne_inr
  ext r t
  by_cases h : r ∈ coords k ∧ t ∈ coords k
  · obtain ⟨hr, ht⟩ := h
    rcases mem_coords.1 hr with rfl | rfl <;> rcases mem_coords.1 ht with rfl | rfl <;>
      simp [longInv, mat_longBlock, blockMat, hpq, hpq.symm, inl_mem_coords, inr_mem_coords]
  · rw [longInv, mat_longBlock, blockMat_apply_of_not_mem k _ h, Matrix.diagonal_apply,
      Matrix.one_apply]
    by_cases hrt : r = t
    · subst hrt
      have : r ∉ coords k := fun hr => h ⟨hr, hr⟩
      simp [this]
    · simp [hrt]

theorem mulVec_diagonal_eq (d : Fin n ⊕ Fin n → K) (w : Fin n ⊕ Fin n → K) :
    Matrix.diagonal d *ᵥ w = fun t => d t * w t :=
  funext fun _ => Matrix.mulVec_diagonal _ _ _

theorem mem_fixSpace_longInv (h2 : (2 : K) ≠ 0) (k : Fin n) {v : Fin n ⊕ Fin n → K} :
    v ∈ fixSpace (longInv K n k) ↔ ∀ t ∈ coords k, v t = 0 := by
  rw [mem_fixSpace, mat_longInv, mulVec_diagonal_eq]
  constructor
  · intro h t ht
    have := congrFun h t
    simp only [ht, ite_true] at this
    have h' : (2 : K) * v t = 0 := by linear_combination -this
    exact (mul_eq_zero.1 h').resolve_left h2
  · intro h
    funext t
    by_cases ht : t ∈ coords k
    · simp [ht, h t ht]
    · simp [ht]

theorem mem_minusSpace_longInv (h2 : (2 : K) ≠ 0) (k : Fin n) {v : Fin n ⊕ Fin n → K} :
    v ∈ minusSpace (longInv K n k) ↔ ∀ t ∉ coords k, v t = 0 := by
  rw [mem_minusSpace, mat_longInv, mulVec_diagonal_eq]
  constructor
  · intro h t ht
    have := congrFun h t
    simp only [ht, ite_false, one_mul, Pi.neg_apply] at this
    have h' : (2 : K) * v t = 0 := by linear_combination this
    exact (mul_eq_zero.1 h').resolve_left h2
  · intro h
    funext t
    by_cases ht : t ∈ coords k
    · simp [ht]
    · simp [ht, h t ht]

theorem fixing_supported_eq {S : Set (Fin n ⊕ Fin n)} (hS : ParClosed S) :
    fixing {v : Fin n ⊕ Fin n → K | ∀ t ∈ S, v t = 0} = suppGroup S := by
  ext x
  rw [mem_fixing, mem_suppGroup_iff hS]
  constructor
  · intro h t ht r
    have hv : (Pi.single t (1 : K) : Fin n ⊕ Fin n → K) ∈
        {v : Fin n ⊕ Fin n → K | ∀ t ∈ S, v t = 0} := by
      intro u hu
      have : u ≠ t := fun e => ht (e ▸ hu)
      simp [this]
    have := congrFun (h _ hv) r
    rw [Matrix.mulVec_single_one] at this
    simpa [Pi.single_apply, Matrix.one_apply] using this
  · intro h v hv
    have hS' : IsSupp S (mat n K x) := fun r t hrt => by
      rcases not_and_or.1 hrt with hr | ht
      · exact isSupp_of_fix hS x h r t (fun h' => hr h'.1)
      · exact h t ht r
    exact mulVec_eq_self_of_isSupp hS' hv

theorem longRootGroup_longInv (h2 : (2 : K) ≠ 0) (k : Fin n) :
    longRootGroup (longInv K n k) = suppGroup (coords k) := by
  rw [← fixing_supported_eq (parClosed_coords k), longRootGroup]
  congr 1
  ext v
  exact mem_fixSpace_longInv h2 k

theorem complGroup_longInv (h2 : (2 : K) ≠ 0) (k : Fin n) :
    complGroup (longInv K n k) = suppGroup (coords k)ᶜ := by
  rw [← fixing_supported_eq (parClosed_coords k).compl, complGroup]
  congr 1
  ext v
  exact mem_minusSpace_longInv h2 k

theorem range_longBlock_eq_longRootGroup (h2 : (2 : K) ≠ 0) (k : Fin n) :
    (longBlock K n k).range = longRootGroup (longInv K n k) := by
  rw [range_longBlock, longRootGroup_longInv h2]

end Standard

end CFSG.ClassicalInvolution.Models.SymplecticPairs
