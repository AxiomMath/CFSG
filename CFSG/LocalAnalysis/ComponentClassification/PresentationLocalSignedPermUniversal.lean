module

public import CFSG.LieType.RootSystem.Positivity
public import CFSG.LocalAnalysis.ComponentClassification.PresentationLocalSignedPermModule
public import TauCeti.LinearAlgebra.RootSystem.FiniteType.Classical

public noncomputable section

namespace CFSG.ComponentClassification.PresentationLocal

open Equiv SemidirectProduct

variable {n : ℕ}

@[expose] def tau (i : Fin n) : Perm (Fin n) := swap ⟨i - 1, by omega⟩ i

theorem s_eq_inr {i : Fin n} (hi : (i : ℕ) ≠ 0) : s i = inr (tau i) := by
  rw [s_of_ne_zero hi, mk_zero, tau]

theorem pow_mul_comm_eq_one {G : Type*} [Group G] {x y : G} {m : ℕ} (h : (x * y) ^ m = 1) :
    (y * x) ^ m = 1 := by
  have : y * x = x⁻¹ * (x * y) * x⁻¹⁻¹ := by group
  rw [this, conj_pow, h, mul_one, mul_inv_cancel]

theorem swap_mul_swap_sq {a b c d : Fin n} (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c)
    (hbd : b ≠ d) : (swap a b * swap c d) ^ 2 = 1 := by
  have hcomm : swap a b * swap c d = swap c d * swap a b := by
    have h := swap_apply_apply (swap a b) c d
    rw [swap_apply_of_ne_of_ne hac.symm hbc.symm, swap_apply_of_ne_of_ne had.symm hbd.symm,
      swap_inv] at h
    conv_rhs => rw [h]
    exact (mul_swap_mul_self _ _ _).symm
  rw [sq, mul_assoc, ← mul_assoc (swap c d), ← hcomm, mul_assoc, swap_mul_self, mul_one,
    swap_mul_self]

theorem swap_mul_swap_cube {a b c : Fin n} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    (swap a b * swap b c) ^ 3 = 1 := by
  rw [swap_comm a b, ← (Perm.isThreeCycle_swap_mul_swap_same hab.symm hbc hac).orderOf]
  exact pow_orderOf_eq_one _

theorem forkGraph_adj_of_ne_zero {i j : Fin n} (hi : (i : ℕ) ≠ 0) (hj : (j : ℕ) ≠ 0) :
    (forkGraph n).Adj i j ↔ (j : ℕ) = i + 1 ∨ (i : ℕ) = j + 1 := by
  rw [forkGraph_adj_iff]
  omega

theorem pow_coxeterEntry_s_mul_s_of_ne_zero {i j : Fin n} (hi : (i : ℕ) ≠ 0)
    (hj : (j : ℕ) ≠ 0) (hij : i ≠ j) : (s i * s j) ^ coxeterEntry i j = 1 := by
  have hij' : (i : ℕ) ≠ j := fun h => hij (Fin.ext h)
  rw [s_eq_inr hi, s_eq_inr hj, ← map_mul, ← map_pow]
  refine (map_eq_one_iff _ inr_injective).2 ?_
  rw [coxeterEntry, tau, tau]
  by_cases hadj : (forkGraph n).Adj i j
  · rw [ite_eq_left hadj]
    rcases (forkGraph_adj_of_ne_zero hi hj).1 hadj with h | h
    · have hji : (⟨j - 1, by omega⟩ : Fin n) = i := Fin.ext (by simp; omega)
      rw [hji]
      exact swap_mul_swap_cube (fun h' => by simp [Fin.ext_iff] at h'; omega)
        (fun h' => by simp [Fin.ext_iff] at h'; omega) hij
    · have hij2 : (⟨i - 1, by omega⟩ : Fin n) = j := Fin.ext (by simp; omega)
      rw [hij2]
      refine pow_mul_comm_eq_one ?_
      exact swap_mul_swap_cube (fun h' => by simp [Fin.ext_iff] at h'; omega)
        (fun h' => by simp [Fin.ext_iff] at h'; omega) hij.symm
  · rw [ite_eq_right hadj]
    have h := (forkGraph_adj_of_ne_zero hi hj).not.1 hadj
    exact swap_mul_swap_sq (fun h' => by simp [Fin.ext_iff] at h'; omega)
      (fun h' => by simp [Fin.ext_iff] at h'; omega) (fun h' => by simp [Fin.ext_iff] at h'; omega)
      (fun h' => by simp [Fin.ext_iff] at h'; omega)

@[expose] def leafSwap (h : 0 < n) : W n →* W n where
  toFun x := mk (vec x + (basisVec ⟨0, h⟩ + permVec x.right (basisVec ⟨0, h⟩)))
    (Submodule.add_mem _ (vec_mem x) (by
      rw [permVec_basisVec]
      exact basisVec_add_basisVec_mem _ _)) x.right
  map_one' := ext_vec (by
    rw [vec_mk, vec_one, right_one, permVec_one, add_self_vec, add_zero]) rfl
  map_mul' x y := by
    refine ext_vec ?_ rfl
    have key : ∀ a b c d e : ZMod 2, a + d + (b + e) = (a + (b + c)) + (d + (c + e)) := by
      decide
    funext j
    simp only [vec_mk, vec_mul, right_mk, right_mul, permVec_add, ← permVec_mul, Pi.add_apply]
    exact key _ _ _ _ _

theorem leafSwap_s_one (h : 1 < n) :
    leafSwap (by omega) (s (⟨1, h⟩ : Fin n)) = s (⟨0, by omega⟩ : Fin n) := by
  rw [s_zero h, s_of_ne_zero (by simp)]
  refine ext_vec ?_ rfl
  change 0 + (basisVec _ + permVec (swap _ _) (basisVec _)) = _
  rw [permVec_basisVec, zero_add]
  rfl

theorem leafSwap_s_of_two_le {i : Fin n} (hi : 2 ≤ (i : ℕ)) :
    leafSwap (by omega) (s i) = s i := by
  rw [s_of_ne_zero (by omega)]
  refine ext_vec ?_ rfl
  change 0 + (basisVec _ + permVec (swap _ _) (basisVec _)) = 0
  rw [permVec_basisVec, swap_apply_of_ne_of_ne (by simp [Fin.ext_iff]; omega)
    (by simp [Fin.ext_iff]; omega), add_self_vec, zero_add]

theorem s_zero_mul_s_one (h : 1 < n) :
    s (⟨0, by omega⟩ : Fin n) * s ⟨1, h⟩ =
      mk (basisVec ⟨0, by omega⟩ + basisVec ⟨1, h⟩) (basisVec_add_basisVec_mem _ _) 1 := by
  rw [s_zero h, s_of_ne_zero (by simp)]
  refine ext_vec ?_ ?_
  · change basisVec _ + basisVec _ + permVec _ 0 = _
    rw [permVec_zero, add_zero]
    rfl
  · change swap _ _ * swap _ _ = 1
    simp

theorem s_mul_self (h : 1 < n) (i : Fin n) : s i * s i = 1 := by
  by_cases hi : (i : ℕ) = 0
  · have hi' : i = ⟨0, by omega⟩ := Fin.ext hi
    rw [hi', ← leafSwap_s_one h, ← map_mul, s_eq_inr (by simp), ← map_mul, tau, swap_mul_self,
      map_one, map_one]
  · rw [s_eq_inr hi, ← map_mul, tau, swap_mul_self, map_one]

theorem coxeterEntry_comm (i j : Fin n) : coxeterEntry i j = coxeterEntry j i := by
  rw [coxeterEntry, coxeterEntry]
  exact if_congr ((forkGraph n).adj_comm i j) rfl rfl

theorem pow_coxeterEntry_s_mul_s (h : 1 < n) {i j : Fin n} (hij : i ≠ j) :
    (s i * s j) ^ coxeterEntry i j = 1 := by
  have hij' : (i : ℕ) ≠ j := fun h => hij (Fin.ext h)
  have h01 : (s (⟨0, by omega⟩ : Fin n) * s ⟨1, h⟩) ^ coxeterEntry (⟨0, by omega⟩ : Fin n)
      ⟨1, h⟩ = 1 := by
    have hent : coxeterEntry (⟨0, by omega⟩ : Fin n) ⟨1, h⟩ = 2 := by
      rw [coxeterEntry, ite_eq_right]
      rw [forkGraph_adj_iff]
      simp
    rw [hent, s_zero_mul_s_one h, sq]
    exact mul_self_of_mem_signSubgroup (mem_signSubgroup_iff.2 rfl)
  have h0j : ∀ j : Fin n, 2 ≤ (j : ℕ) →
      (s (⟨0, by omega⟩ : Fin n) * s j) ^ coxeterEntry (⟨0, by omega⟩ : Fin n) j = 1 := by
    intro j hj
    have hent : coxeterEntry (⟨0, by omega⟩ : Fin n) j = coxeterEntry ⟨1, h⟩ j := by
      rw [coxeterEntry, coxeterEntry]
      refine if_congr ?_ rfl rfl
      rw [forkGraph_adj_iff, forkGraph_adj_iff]
      simp only [true_and]
      omega
    rw [hent, ← leafSwap_s_one h, ← leafSwap_s_of_two_le hj, ← map_mul, ← map_pow,
      pow_coxeterEntry_s_mul_s_of_ne_zero (by simp) (by omega)
        (fun h' => by rw [← h'] at hj; simp at hj), map_one]
  by_cases hi : (i : ℕ) = 0
  · have hi' : i = ⟨0, Nat.zero_lt_of_lt h⟩ := Fin.ext hi
    subst hi'
    by_cases hj1 : (j : ℕ) = 1
    · have hj' : j = ⟨1, h⟩ := Fin.ext hj1
      subst hj'
      exact h01
    · exact h0j j (by simp at hij'; omega)
  by_cases hj : (j : ℕ) = 0
  · have hj' : j = ⟨0, Nat.zero_lt_of_lt h⟩ := Fin.ext hj
    subst hj'
    rw [coxeterEntry_comm]
    refine pow_mul_comm_eq_one ?_
    by_cases hi1 : (i : ℕ) = 1
    · have hi' : i = ⟨1, h⟩ := Fin.ext hi1
      subst hi'
      exact h01
    · exact h0j i (by omega)
  exact pow_coxeterEntry_s_mul_s_of_ne_zero hi hj hij

theorem signSubgroup_le_of_forall_mem (H : Subgroup (W n)) (r : Fin n)
    (hH : ∀ k, (inl (Multiplicative.ofAdd
      ⟨basisVec r + basisVec k, basisVec_add_basisVec_mem r k⟩) : W n) ∈ H) :
    signSubgroup n ≤ H := by
  rintro _ ⟨x, rfl⟩
  have h01 : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide
  have key : ∀ v : Fin n → ZMod 2,
      v ∈ Submodule.span (ZMod 2) (Set.range fun k => basisVec r + basisVec k) →
      ∀ hv : v ∈ evenSubspace n, (inl (Multiplicative.ofAdd ⟨v, hv⟩) : W n) ∈ H := by
    intro v hv
    induction hv using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨k, rfl⟩ := hy
      intro _
      exact hH k
    | zero =>
      intro _
      exact H.one_mem
    | add y z hy hz ihy ihz =>
      intro _
      rw [span_basisVec_add] at hy hz
      have := H.mul_mem (ihy hy) (ihz hz)
      rwa [← map_mul] at this
    | smul c y hy ih =>
      intro hcy
      rw [span_basisVec_add] at hy
      rcases h01 c with rfl | rfl
      · have : (⟨(0 : ZMod 2) • y, hcy⟩ : evenSubspace n) = 0 := Subtype.ext (zero_smul _ _)
        rw [this]
        exact H.one_mem
      · have : (⟨(1 : ZMod 2) • y, hcy⟩ : evenSubspace n) = ⟨y, hy⟩ := Subtype.ext (one_smul _ _)
        rw [this]
        exact ih hy
  exact key _ (by rw [span_basisVec_add]; exact (Multiplicative.toAdd x).2)
    (Multiplicative.toAdd x).2

theorem vec_inr_mul_inl_mul_inv (σ : Perm (Fin n)) (v : Multiplicative (evenSubspace n)) :
    vec ((inr σ : W n) * inl v * (inr σ)⁻¹) = permVec σ (vec (inl v : W n)) := by
  simp only [vec_mul, vec_inv, right_mul, right_inr, right_inl, vec_inr, permVec_zero,
    zero_add, add_zero]

theorem closure_range_s (h : 1 < n) : Subgroup.closure (Set.range (s (n := n))) = ⊤ := by
  set H := Subgroup.closure (Set.range (s (n := n))) with hHdef
  have hs : ∀ i, s i ∈ H := fun i => Subgroup.subset_closure ⟨i, rfl⟩
  have hperm : ∀ σ : Perm (Fin n), (inr σ : W n) ∈ H := by
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    have hle : Submonoid.closure (Set.range fun i : Fin m => swap i.castSucc i.succ) ≤
        (H.comap inr).toSubmonoid := by
      rw [Submonoid.closure_le]
      rintro _ ⟨i, rfl⟩
      have hi := hs i.succ
      rw [s_eq_inr (by simp)] at hi
      have htau : tau i.succ = swap i.castSucc i.succ := by
        rw [tau]
        congr 1
      rw [htau] at hi
      exact hi
    intro σ
    exact hle (by rw [Perm.mclosure_swap_castSucc_succ]; trivial)
  have h0 : 0 < n := by omega
  have hsign : signSubgroup n ≤ H := by
    refine signSubgroup_le_of_forall_mem H ⟨0, h0⟩ fun k => ?_
    by_cases hk0 : (k : ℕ) = 0
    · have hk : k = ⟨0, h0⟩ := Fin.ext hk0
      have : (⟨basisVec ⟨0, h0⟩ + basisVec k, basisVec_add_basisVec_mem _ k⟩ :
          evenSubspace n) = 0 := Subtype.ext (by
            change basisVec _ + basisVec k = 0
            rw [hk, add_self_vec])
      rw [this]
      exact H.one_mem
    have h01 : (inl (Multiplicative.ofAdd ⟨basisVec ⟨0, h0⟩ + basisVec ⟨1, h⟩,
        basisVec_add_basisVec_mem _ _⟩) : W n) = s ⟨0, h0⟩ * s ⟨1, h⟩ := by
      rw [s_zero_mul_s_one h]
      rfl
    by_cases hk1 : (k : ℕ) = 1
    · have hk : k = ⟨1, h⟩ := Fin.ext hk1
      subst hk
      rw [h01]
      exact H.mul_mem (hs _) (hs _)
    have hconj : (inl (Multiplicative.ofAdd ⟨basisVec ⟨0, h0⟩ + basisVec k,
        basisVec_add_basisVec_mem _ _⟩) : W n) = inr (swap ⟨1, h⟩ k) *
          inl (Multiplicative.ofAdd ⟨basisVec ⟨0, h0⟩ + basisVec ⟨1, h⟩,
            basisVec_add_basisVec_mem _ _⟩) * (inr (swap ⟨1, h⟩ k))⁻¹ := by
      refine ext_vec ?_ ?_
      · rw [vec_inr_mul_inl_mul_inv, vec_inl, vec_inl]
        change _ = permVec _ (basisVec _ + basisVec _)
        rw [permVec_add, permVec_basisVec, permVec_basisVec, swap_apply_left,
          swap_apply_of_ne_of_ne (by simp) (fun h' => hk0 (by rw [← h']))]
      · simp
    rw [hconj, h01]
    exact H.mul_mem (H.mul_mem (hperm _) (H.mul_mem (hs _) (hs _))) (H.inv_mem (hperm _))
  refine eq_top_iff.2 fun x _ => ?_
  rw [← inl_left_mul_inr_right x]
  exact H.mul_mem (hsign ⟨x.left, rfl⟩) (hperm _)

variable (n) in
@[expose] def forkCartan : Matrix (Fin n) (Fin n) ℤ :=
  Matrix.of fun i j => if i = j then 2 else if (forkGraph n).Adj i j then -1 else 0

theorem forkCartan_apply (i j : Fin n) :
    forkCartan n i j = if i = j then 2 else if (forkGraph n).Adj i j then -1 else 0 := rfl

theorem forkCartan_eq_submatrix : forkCartan n = (CartanMatrix.D n).submatrix Fin.rev Fin.rev := by
  ext i j
  have hi := i.isLt
  have hj := j.isLt
  simp only [forkCartan_apply, forkGraph_adj_iff, CartanMatrix.D, Matrix.submatrix_apply,
    Matrix.of_apply, Fin.val_rev, Fin.ext_iff]
  split_ifs <;> omega

theorem isFiniteType_forkCartan : TauCeti.IsFiniteType (forkCartan n) := by
  rw [forkCartan_eq_submatrix]
  exact (TauCeti.isFiniteType_cartanMatrix_D n).submatrix Fin.rev_injective

variable (n) in
abbrev forkCoxeterMatrix : CoxeterMatrix (Fin n) :=
  CFSG.LieType.RootSystem.coxeterMatrix (isFiniteType_forkCartan (n := n))

theorem forkCoxeterMatrix_apply_of_ne {i j : Fin n} (hij : i ≠ j) :
    forkCoxeterMatrix n i j = coxeterEntry i j := by
  rw [forkCoxeterMatrix, CFSG.LieType.RootSystem.coxeterMatrix,
    TauCeti.coxeterMatrixOfCartanMatrix_apply, forkCartan_apply, forkCartan_apply,
    ite_eq_right hij, ite_eq_right (Ne.symm hij), coxeterEntry]
  by_cases hadj : (forkGraph n).Adj i j
  · rw [ite_eq_left hadj, ite_eq_left hadj.symm, ite_eq_left hadj]
    norm_num
  · rw [ite_eq_right hadj, ite_eq_right (fun h => hadj h.symm), ite_eq_right hadj]
    norm_num

theorem isLiftable_s (h : 1 < n) : (forkCoxeterMatrix n).IsLiftable (s (n := n)) := by
  intro i j
  by_cases hij : i = j
  · rw [hij, (forkCoxeterMatrix n).diagonal, pow_one]
    exact s_mul_self h j
  · rw [forkCoxeterMatrix_apply_of_ne hij]
    exact pow_coxeterEntry_s_mul_s h hij

@[expose] def coxeterHom (h : 1 < n) : (forkCoxeterMatrix n).Group →* W n :=
  (forkCoxeterMatrix n).toCoxeterSystem.lift ⟨s, isLiftable_s h⟩

theorem coxeterHom_simple (h : 1 < n) (i : Fin n) :
    coxeterHom h ((forkCoxeterMatrix n).toCoxeterSystem.simple i) = s i :=
  (forkCoxeterMatrix n).toCoxeterSystem.lift_apply_simple (isLiftable_s h) i

theorem coxeterHom_surjective (h : 1 < n) : Function.Surjective (coxeterHom h) := by
  rw [← MonoidHom.range_eq_top, eq_top_iff, ← closure_range_s h, Subgroup.closure_le]
  rintro _ ⟨i, rfl⟩
  exact ⟨_, coxeterHom_simple h i⟩

theorem simpleRoot_zero (h : 1 < n) :
    simpleRoot ℤ (⟨0, Nat.zero_lt_of_lt h⟩ : Fin n) =
      -Pi.single ⟨0, Nat.zero_lt_of_lt h⟩ 1 - Pi.single ⟨1, h⟩ 1 := by
  rw [simpleRoot, dite_eq_left ⟨rfl, h⟩]

theorem simpleRoot_of_ne_zero {i : Fin n} (hi : (i : ℕ) ≠ 0) :
    simpleRoot ℤ i = Pi.single ⟨i - 1, by omega⟩ 1 - Pi.single i 1 := by
  rw [simpleRoot, dite_eq_right fun h => hi h.1]

theorem signedPermAction_s (h : 1 < n) (i : Fin n) (x : Fin n → ℤ) :
    signedPermAction ℤ (s i) x = x - (x ⬝ᵥ simpleRoot ℤ i) • simpleRoot ℤ i := by
  by_cases hi : (i : ℕ) = 0
  · have hi' : i = ⟨0, Nat.zero_lt_of_lt h⟩ := Fin.ext hi
    subst hi'
    rw [s_zero h, simpleRoot_zero h]
    funext k
    simp only [signedPermAction_apply, sZero, vec_mk, right_mk, swap_inv, basisVec,
      Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.neg_apply, dotProduct_sub,
      dotProduct_neg, dotProduct_single, mul_one, Pi.single_apply]
    by_cases hk0 : (k : ℕ) = 0
    · have hk : k = ⟨0, Nat.zero_lt_of_lt h⟩ := Fin.ext hk0
      subst hk
      have h10 : (⟨0, Nat.zero_lt_of_lt h⟩ : Fin n) ≠ ⟨1, h⟩ := by simp
      simp [h10, swap_apply_left]
    by_cases hk1 : (k : ℕ) = 1
    · have hk : k = ⟨1, h⟩ := Fin.ext hk1
      subst hk
      have h10 : (⟨1, h⟩ : Fin n) ≠ ⟨0, Nat.zero_lt_of_lt h⟩ := by simp
      simp [h10, swap_apply_right]
    have hk0' : k ≠ ⟨0, Nat.zero_lt_of_lt h⟩ := fun h' => hk0 (by rw [h'])
    have hk1' : k ≠ ⟨1, h⟩ := fun h' => hk1 (by rw [h'])
    simp [hk0', hk1', swap_apply_of_ne_of_ne hk0' hk1']
  · rw [s_eq_inr hi, simpleRoot_of_ne_zero hi, tau]
    funext k
    simp only [signedPermAction_apply, vec_inr, right_inr, swap_inv, Pi.zero_apply,
      negOnePow_zero, one_mul, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, dotProduct_sub,
      dotProduct_single, mul_one, Pi.single_apply]
    have hne : (⟨i - 1, by omega⟩ : Fin n) ≠ i := fun h' => by
      rw [Fin.ext_iff] at h'
      simp at h'
      omega
    by_cases hka : k = ⟨i - 1, by omega⟩
    · subst hka
      simp [hne, swap_apply_left]
    by_cases hkb : k = i
    · subst hkb
      simp [hne.symm, swap_apply_right]
    simp [hka, hkb, swap_apply_of_ne_of_ne hka hkb]

theorem forkCartan_comm (i j : Fin n) : forkCartan n i j = forkCartan n j i := by
  rw [forkCartan_apply, forkCartan_apply]
  by_cases hij : i = j
  · rw [hij]
  · rw [ite_eq_right hij, ite_eq_right (Ne.symm hij)]
    exact if_congr ((forkGraph n).adj_comm i j) rfl rfl

theorem simpleRoot_dotProduct_simpleRoot_zero (h : 1 < n) (j : Fin n) :
    simpleRoot ℤ j ⬝ᵥ simpleRoot ℤ ⟨0, Nat.zero_lt_of_lt h⟩ =
      forkCartan n ⟨0, Nat.zero_lt_of_lt h⟩ j := by
  have hj := j.isLt
  rw [forkCartan_apply]
  by_cases hj0 : (j : ℕ) = 0
  · have hj' : j = ⟨0, Nat.zero_lt_of_lt h⟩ := Fin.ext hj0
    subst hj'
    rw [simpleRoot_zero h]
    simp [dotProduct_sub, Fin.ext_iff]
  · rw [simpleRoot_zero h, simpleRoot_of_ne_zero hj0]
    simp only [dotProduct_sub, sub_dotProduct, dotProduct_neg, single_dotProduct,
      Pi.single_apply, one_mul, forkGraph_adj_iff, Fin.ext_iff]
    split_ifs
    all_goals simp_all
    all_goals omega

theorem simpleRoot_dotProduct_simpleRoot (h : 1 < n) (i j : Fin n) :
    simpleRoot ℤ j ⬝ᵥ simpleRoot ℤ i = forkCartan n i j := by
  by_cases hi0 : (i : ℕ) = 0
  · have hi' : i = ⟨0, Nat.zero_lt_of_lt h⟩ := Fin.ext hi0
    subst hi'
    exact simpleRoot_dotProduct_simpleRoot_zero h j
  by_cases hj0 : (j : ℕ) = 0
  · have hj' : j = ⟨0, Nat.zero_lt_of_lt h⟩ := Fin.ext hj0
    subst hj'
    rw [dotProduct_comm, forkCartan_comm]
    exact simpleRoot_dotProduct_simpleRoot_zero h i
  have hi := i.isLt
  have hj := j.isLt
  rw [forkCartan_apply, simpleRoot_of_ne_zero hi0, simpleRoot_of_ne_zero hj0]
  simp only [dotProduct_sub, sub_dotProduct, single_dotProduct, Pi.single_apply, one_mul,
    forkGraph_adj_iff, Fin.ext_iff]
  split_ifs <;> omega

theorem signedPermAction_s_simpleRoot (h : 1 < n) (i j : Fin n) :
    signedPermAction ℤ (s i) (simpleRoot ℤ j) =
      simpleRoot ℤ j - forkCartan n i j • simpleRoot ℤ i := by
  rw [signedPermAction_s h, simpleRoot_dotProduct_simpleRoot h]

variable (n) in
@[expose] def rootMap : (Fin n → ℤ) →ₗ[ℤ] (Fin n → ℤ) :=
  Fintype.linearCombination ℤ (simpleRoot ℤ)

theorem rootMap_single (j : Fin n) : rootMap n (Pi.single j 1) = simpleRoot ℤ j := by
  rw [rootMap, Fintype.linearCombination_apply_single, one_smul]

theorem rootMap_injective (h : 1 < n) : Function.Injective (rootMap n) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro c hc
  refine Matrix.eq_zero_of_mulVec_eq_zero (isFiniteType_forkCartan (n := n)).det_ne_zero ?_
  funext i
  have hi : rootMap n c ⬝ᵥ simpleRoot ℤ i = 0 := by rw [hc, zero_dotProduct]
  rw [rootMap, Fintype.linearCombination_apply, sum_dotProduct] at hi
  simp only [smul_dotProduct, smul_eq_mul, simpleRoot_dotProduct_simpleRoot h] at hi
  rw [Matrix.mulVec, dotProduct, Pi.zero_apply, ← hi]
  exact Finset.sum_congr rfl fun j _ => mul_comm _ _

open CFSG.LieType.RootSystem in
theorem signedPermAction_comp_rootMap (h : 1 < n) (c : (forkCoxeterMatrix n).Group) :
    signedPermAction ℤ (coxeterHom h c) ∘ₗ rootMap n =
      rootMap n ∘ₗ weylAction (isFiniteType_forkCartan (n := n)) c := by
  induction c using (forkCoxeterMatrix n).toCoxeterSystem.simple_induction_left with
  | one =>
    rw [map_one, map_one, map_one]
    rfl
  | mul_simple_left w i ih =>
    have hgen : signedPermAction ℤ (s i) ∘ₗ rootMap n =
        rootMap n ∘ₗ reflection (forkCartan n) i := by
      refine LinearMap.pi_ext fun j x => ?_
      rw [← mul_one x, ← smul_eq_mul, Pi.single_smul, map_smul, map_smul]
      congr 1
      rw [LinearMap.comp_apply, LinearMap.comp_apply, rootMap_single,
        signedPermAction_s_simpleRoot h, reflection_apply_coroot, coroot_single, map_sub,
        map_zsmul, rootMap_single, rootMap_single]
    rw [map_mul, map_mul, map_mul, Module.End.mul_eq_comp, Module.End.mul_eq_comp,
      LinearMap.comp_assoc, ih, ← LinearMap.comp_assoc, coxeterHom_simple, weylAction_simple,
      hgen, LinearMap.comp_assoc]

theorem coxeterHom_injective (h : 1 < n) : Function.Injective (coxeterHom h) := by
  rw [injective_iff_map_eq_one]
  intro c hc
  refine CFSG.LieType.RootSystem.weylAction_injective (isFiniteType_forkCartan (n := n)) ?_
  rw [map_one]
  have hcomp := signedPermAction_comp_rootMap h c
  rw [hc, map_one] at hcomp
  refine LinearMap.ext fun v => rootMap_injective h ?_
  have := congrArg (fun f => f v) hcomp
  simpa using this.symm

@[expose] def coxeterEquiv (h : 1 < n) : (forkCoxeterMatrix n).Group ≃* W n :=
  MulEquiv.ofBijective (coxeterHom h) ⟨coxeterHom_injective h, coxeterHom_surjective h⟩

theorem even_signed_permutation_universal_homomorphism (hn : 2 ≤ n) {K : Type*} [Group K]
    (t : Fin n → K) (ht : ∀ i, t i ^ 2 = 1)
    (htt : ∀ i j, i ≠ j → (t i * t j) ^ coxeterEntry i j = 1) :
    (∃! φ : W n →* K, ∀ i, φ (s i) = t i) ∧
      ∀ φ : W n →* K, (∀ i, φ (s i) = t i) → φ.range = Subgroup.closure (Set.range t) := by
  have h : 1 < n := hn
  have hlift : (forkCoxeterMatrix n).IsLiftable t := by
    intro i j
    by_cases hij : i = j
    · rw [hij, (forkCoxeterMatrix n).diagonal, pow_one, ← sq]
      exact ht j
    · rw [forkCoxeterMatrix_apply_of_ne hij]
      exact htt i j hij
  let L : (forkCoxeterMatrix n).Group →* K :=
    (forkCoxeterMatrix n).toCoxeterSystem.lift ⟨t, hlift⟩
  have hφ : ∀ i, (L.comp (coxeterEquiv h).symm.toMonoidHom) (s i) = t i := by
    intro i
    have he : (coxeterEquiv h).symm (s i) = (forkCoxeterMatrix n).toCoxeterSystem.simple i :=
      (coxeterEquiv h).symm_apply_eq.2 (coxeterHom_simple h i).symm
    rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, he]
    exact (forkCoxeterMatrix n).toCoxeterSystem.lift_apply_simple hlift i
  have huniq : ∀ φ ψ : W n →* K, (∀ i, φ (s i) = t i) → (∀ i, ψ (s i) = t i) → φ = ψ := by
    intro φ ψ hφ' hψ'
    refine MonoidHom.eq_of_eqOn_dense (closure_range_s h) ?_
    rintro _ ⟨i, rfl⟩
    rw [hφ', hψ']
  refine ⟨⟨_, hφ, fun ψ hψ => huniq ψ _ hψ hφ⟩, fun φ hφ' => ?_⟩
  rw [MonoidHom.range_eq_map, ← closure_range_s h, MonoidHom.map_closure, ← Set.range_comp]
  congr 1
  ext x
  simp [hφ']

end CFSG.ComponentClassification.PresentationLocal
