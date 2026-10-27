module

public import CFSG.LieType.Universal.Unitary.Roots
public import CFSG.LieType.Steinberg.Basic
import all CFSG.LieType.Universal.Unitary.Roots

public section

namespace CFSG.LieType.Universal.Unitary.SUExtras

open Matrix CFSG.LieType.RootSystem CFSG.LieType.Steinberg

variable {F : Type*} [Field F] {σ : F ≃+* F} {n : ℕ}

variable (σ n) in
@[expose] noncomputable def mat : SU σ n →* Matrix (Fin n) (Fin n) F :=
  (Units.coeHom _).comp (SU σ n).subtype

theorem mat_apply (x : SU σ n) :
    mat σ n x = ((x : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) := rfl

theorem mat_injective : Function.Injective (mat σ n) := fun _ _ h => Subtype.ext (Units.ext h)

theorem conjTr_mat_mul (x : SU σ n) :
    conjTr σ (mat σ n x) * antidiag n * mat σ n x = antidiag n := x.2.2

theorem sum_mat_mul_mat (x : SU σ n) (a b : Fin n) :
    ∑ t, σ (mat σ n x t a) * mat σ n x (Fin.rev t) b = if b = Fin.rev a then 1 else 0 := by
  have h := congrFun (congrFun (conjTr_mat_mul x) a) b
  simp only [mul_apply, conjTr, transpose_apply, map_apply, antidiag, of_apply,
    Finset.sum_mul] at h
  rw [Finset.sum_comm] at h
  rw [← h]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [Finset.sum_eq_single (Fin.rev t)]
  · simp
  · intro u _ hu
    simp [hu]
  · simp

theorem mat_rev_apply_of_col {x : SU σ n} {s : Fin n} (hs : ∀ a, mat σ n x a s = (1 : Matrix
    (Fin n) (Fin n) F) a s) (b : Fin n) :
    mat σ n x (Fin.rev s) b = (1 : Matrix (Fin n) (Fin n) F) (Fin.rev s) b := by
  have h := sum_mat_mul_mat x s b
  rw [Finset.sum_eq_single s] at h
  · rw [hs, one_apply_eq, map_one, one_mul] at h
    rw [h, one_apply]
    by_cases hb : b = Fin.rev s
    · simp [hb]
    · simp [hb, Ne.symm hb]
  · intro t _ ht
    rw [hs, one_apply_ne ht, map_zero, zero_mul]
  · simp

theorem weight_apply' (i : Fin n) (c : Fin (n / 2)) :
    weight n i c = if i.val = c.val then 1 else if i.val + c.val + 1 = n then -1 else 0 := by
  rw [weight_apply]
  have := c.isLt
  have := i.isLt
  split_ifs <;> omega

theorem weight_rev' (i : Fin n) : weight n (Fin.rev i) = -weight n i := weight_rev n i

theorem weight_eq_zero_of_rev_eq {k : Fin n} (hk : Fin.rev k = k) : weight n k = 0 := by
  have h := weight_rev' k
  rw [hk] at h
  funext c
  have := congrFun h c
  simp only [Pi.neg_apply, Pi.zero_apply] at this ⊢
  omega

theorem exists_weight_ne_zero {i : Fin n} (hi : i ≠ Fin.rev i) :
    ∃ c : Fin (n / 2), (i.val = c.val ∨ i.val + c.val + 1 = n) := by
  obtain ⟨c, rfl | rfl⟩ := exists_lowIdx hi
  · exact ⟨c, Or.inl rfl⟩
  · refine ⟨c, Or.inr ?_⟩
    simp only [Fin.val_rev, lowIdx]
    have := c.isLt
    omega

theorem weight_injective : Function.Injective (weight n) := by
  intro a b h
  by_cases ha : a = Fin.rev a
  · have hb : b = Fin.rev b := by
      by_contra hb
      obtain ⟨c, hc⟩ := exists_weight_ne_zero hb
      have h1 := congrFun h c
      rw [weight_eq_zero_of_rev_eq ha.symm, Pi.zero_apply, weight_apply'] at h1
      have := c.isLt
      split_ifs at h1 <;> omega
    exact middle_unique ha.symm hb.symm
  · obtain ⟨c, hc⟩ := exists_weight_ne_zero ha
    have h1 := congrFun h c
    rw [weight_apply', weight_apply'] at h1
    have := c.isLt
    have := a.isLt
    have := b.isLt
    exact Fin.ext (by split_ifs at h1 <;> omega)

theorem weight_apply_bounds (i : Fin n) (c : Fin (n / 2)) :
    -1 ≤ weight n i c ∧ weight n i c ≤ 1 := by
  rw [weight_apply']
  split_ifs <;> simp

theorem eq_zero_of_weight_sub_eq_nsmul {a b : Fin n} {e : Fin (n / 2) → ℤ} {k : ℕ}
    (h : weight n a - weight n b = k • e) (hk : 3 ≤ k) : e = 0 := by
  funext c
  have h1 := congrFun h c
  simp only [Pi.sub_apply, Pi.smul_apply, nsmul_eq_mul, Pi.zero_apply] at h1 ⊢
  obtain ⟨ha1, ha2⟩ := weight_apply_bounds a c
  obtain ⟨hb1, hb2⟩ := weight_apply_bounds b c
  have hk' : (3 : ℤ) ≤ k := by exact_mod_cast hk
  rcases lt_trichotomy (e c) 0 with h2 | h2 | h2
  · exfalso
    have h3 : e c ≤ -1 := by omega
    nlinarith
  · exact h2
  · exfalso
    have h3 : 1 ≤ e c := by omega
    nlinarith

theorem eq_rev_of_weight_sub_eq_two_smul {a b : Fin n} {e : Fin (n / 2) → ℤ}
    (h : weight n a - weight n b = 2 • e) (he : e ≠ 0) : b = Fin.rev a ∧ weight n a = e := by
  obtain ⟨c, hc⟩ : ∃ c, e c ≠ 0 := by
    by_contra h'
    push Not at h'
    exact he (funext h')
  have h1 := congrFun h c
  simp only [Pi.sub_apply, Pi.smul_apply, nsmul_eq_mul, Nat.cast_ofNat, weight_apply'] at h1
  have hb : b = Fin.rev a := by
    apply Fin.ext
    simp only [Fin.val_rev]
    have := a.isLt
    have := b.isLt
    have := c.isLt
    split_ifs at h1 <;> omega
  refine ⟨hb, ?_⟩
  rw [hb, weight_rev', sub_neg_eq_add] at h
  funext c'
  have := congrFun h c'
  simp only [Pi.add_apply, Pi.smul_apply, nsmul_eq_mul, Nat.cast_ofNat] at this
  omega

theorem eq_of_weight_sub_eq_two_smul {a b i : Fin n} (hi : i ≠ Fin.rev i)
    (h : weight n a - weight n b = 2 • weight n i) : a = i ∧ b = Fin.rev i := by
  have hne : weight n i ≠ 0 := by
    intro h0
    obtain ⟨c, hc⟩ := exists_weight_ne_zero hi
    have h1 := congrFun h0 c
    rw [weight_apply', Pi.zero_apply] at h1
    have := c.isLt
    split_ifs at h1 <;> omega
  obtain ⟨hb, ha⟩ := eq_rev_of_weight_sub_eq_two_smul h hne
  obtain rfl := weight_injective ha
  exact ⟨rfl, hb⟩

theorem eq_of_weight_sub_eq_sub {a b i j : Fin n} (hij : i ≠ j) (hi : i ≠ Fin.rev i)
    (hj : j ≠ Fin.rev j) (hji : j ≠ Fin.rev i)
    (h : weight n a - weight n b = weight n i - weight n j) :
    (a = i ∧ b = j) ∨ (a = Fin.rev j ∧ b = Fin.rev i) := by
  have := a.isLt
  have := b.isLt
  obtain ⟨ci, rfl | rfl⟩ := exists_lowIdx hi <;> obtain ⟨cj, rfl | rfl⟩ := exists_lowIdx hj
  · have hc : ci.val ≠ cj.val := fun e => hij (by rw [Fin.ext e])
    rw [weight_lowIdx, weight_lowIdx] at h
    have hcij : ci ≠ cj := Fin.ne_of_val_ne hc
    have hcji : cj ≠ ci := Fin.ne_of_val_ne (Ne.symm hc)
    have h1 := congrFun h ci
    have h2 := congrFun h cj
    simp only [Pi.sub_apply, Pi.single_eq_same, Pi.single_eq_of_ne hcij,
      Pi.single_eq_of_ne hcji, weight_apply', sub_zero, zero_sub] at h1 h2
    simp only [Fin.ext_iff, Fin.val_rev, val_lowIdx]
    have := ci.isLt
    have := cj.isLt
    split_ifs at h1 h2 <;> omega
  · have hc : ci.val ≠ cj.val := fun e => hji (by rw [Fin.ext e])
    rw [weight_lowIdx, weight_rev_lowIdx] at h
    have hcij : ci ≠ cj := Fin.ne_of_val_ne hc
    have hcji : cj ≠ ci := Fin.ne_of_val_ne (Ne.symm hc)
    have h1 := congrFun h ci
    have h2 := congrFun h cj
    simp only [Pi.sub_apply, Pi.neg_apply, Pi.single_eq_same, Pi.single_eq_of_ne hcij,
      Pi.single_eq_of_ne hcji, weight_apply', neg_zero, sub_zero, zero_sub] at h1 h2
    simp only [Fin.ext_iff, Fin.val_rev, val_lowIdx]
    have := ci.isLt
    have := cj.isLt
    split_ifs at h1 h2 <;> omega
  · have hc : ci.val ≠ cj.val := fun e => hji (by rw [Fin.ext e, Fin.rev_rev])
    rw [weight_rev_lowIdx, weight_lowIdx] at h
    have hcij : ci ≠ cj := Fin.ne_of_val_ne hc
    have hcji : cj ≠ ci := Fin.ne_of_val_ne (Ne.symm hc)
    have h1 := congrFun h ci
    have h2 := congrFun h cj
    simp only [Pi.sub_apply, Pi.neg_apply, Pi.single_eq_same, Pi.single_eq_of_ne hcij,
      Pi.single_eq_of_ne hcji, weight_apply', neg_zero, sub_zero, zero_sub] at h1 h2
    simp only [Fin.ext_iff, Fin.val_rev, val_lowIdx]
    have := ci.isLt
    have := cj.isLt
    split_ifs at h1 h2 <;> omega
  · have hc : ci.val ≠ cj.val := fun e => hij (by rw [Fin.ext e])
    rw [weight_rev_lowIdx, weight_rev_lowIdx] at h
    have hcij : ci ≠ cj := Fin.ne_of_val_ne hc
    have hcji : cj ≠ ci := Fin.ne_of_val_ne (Ne.symm hc)
    have h1 := congrFun h ci
    have h2 := congrFun h cj
    simp only [Pi.sub_apply, Pi.neg_apply, Pi.single_eq_same, Pi.single_eq_of_ne hcij,
      Pi.single_eq_of_ne hcji, weight_apply', neg_zero, sub_zero, zero_sub] at h1 h2
    simp only [Fin.ext_iff, Fin.val_rev, val_lowIdx]
    have := ci.isLt
    have := cj.isLt
    split_ifs at h1 h2 <;> omega

theorem eq_of_weight_sub_eq_weight {a b i k : Fin n} (hi : i ≠ Fin.rev i) (hk : Fin.rev k = k)
    (h : weight n a - weight n b = weight n i) :
    (a = i ∧ b = k) ∨ (a = k ∧ b = Fin.rev i) := by
  have key : a = i ∨ b = Fin.rev i := by
    have := a.isLt
    have := b.isLt
    obtain ⟨ci, rfl | rfl⟩ := exists_lowIdx hi
    · rw [weight_lowIdx] at h
      have h1 := congrFun h ci
      simp only [Pi.sub_apply, Pi.single_eq_same, weight_apply'] at h1
      simp only [Fin.ext_iff, Fin.val_rev, val_lowIdx]
      have := ci.isLt
      split_ifs at h1 <;> omega
    · rw [weight_rev_lowIdx] at h
      have h1 := congrFun h ci
      simp only [Pi.sub_apply, Pi.neg_apply, Pi.single_eq_same, weight_apply'] at h1
      simp only [Fin.ext_iff, Fin.val_rev, val_lowIdx, Fin.rev_rev]
      have := ci.isLt
      split_ifs at h1 <;> omega
  rcases key with rfl | rfl
  · left
    refine ⟨rfl, weight_injective ?_⟩
    rw [weight_eq_zero_of_rev_eq hk]
    funext c
    have := congrFun h c
    simp only [Pi.sub_apply, Pi.zero_apply] at this ⊢
    omega
  · right
    refine ⟨weight_injective ?_, rfl⟩
    rw [weight_eq_zero_of_rev_eq hk]
    rw [weight_rev'] at h
    funext c
    have := congrFun h c
    simp only [Pi.sub_apply, Pi.neg_apply, Pi.zero_apply] at this ⊢
    omega

@[expose] def HasWt (C : Set (Fin (n / 2) → ℤ)) (N : Matrix (Fin n) (Fin n) F) : Prop :=
  ∀ a b, N a b ≠ 0 → weight n a - weight n b ∈ C

section HasWt

variable {C D E : Set (Fin (n / 2) → ℤ)} {N M : Matrix (Fin n) (Fin n) F}

theorem HasWt.zero : HasWt C (0 : Matrix (Fin n) (Fin n) F) := fun _ _ h => absurd rfl h

theorem HasWt.mono' (hN : HasWt C N)
    (h : ∀ a b : Fin n, weight n a - weight n b ∈ C → weight n a - weight n b ∈ D) :
    HasWt D N := fun a b hab => h a b (hN a b hab)

theorem HasWt.mono (hN : HasWt C N) (h : C ⊆ D) : HasWt D N := fun a b hab => h (hN a b hab)

theorem HasWt.add (hN : HasWt C N) (hM : HasWt C M) : HasWt C (N + M) := by
  intro a b hab
  by_cases h : N a b = 0
  · rw [Matrix.add_apply, h, zero_add] at hab
    exact hM a b hab
  · exact hN a b h

theorem HasWt.neg (hN : HasWt C N) : HasWt C (-N) := fun a b hab => hN a b (by simpa using hab)

theorem HasWt.sub (hN : HasWt C N) (hM : HasWt C M) : HasWt C (N - M) := by
  rw [sub_eq_add_neg]
  exact hN.add hM.neg

theorem HasWt.smul (c : F) (hN : HasWt C N) : HasWt C (c • N) := fun a b hab =>
  hN a b (right_ne_zero_of_mul hab)

theorem HasWt.mul (hN : HasWt C N) (hM : HasWt D M)
    (h : ∀ a c b : Fin n, weight n a - weight n c ∈ C → weight n c - weight n b ∈ D →
      weight n a - weight n b ∈ E) : HasWt E (N * M) := by
  intro a b hab
  rw [mul_apply] at hab
  obtain ⟨c, -, hc⟩ := Finset.exists_ne_zero_of_sum_ne_zero hab
  exact h a c b (hN a c (left_ne_zero_of_mul hc)) (hM c b (right_ne_zero_of_mul hc))

theorem HasWt.eq_zero_apply (hN : HasWt C N) {a b : Fin n} (h : weight n a - weight n b ∉ C) :
    N a b = 0 := by
  by_contra h'
  exact h (hN a b h')

theorem hasWt_single (i j : Fin n) (c : F) :
    HasWt {weight n i - weight n j} (single i j c : Matrix (Fin n) (Fin n) F) := by
  intro a b hab
  rw [single_apply] at hab
  split_ifs at hab with h
  · obtain ⟨rfl, rfl⟩ := h
    rfl
  · exact absurd rfl hab

theorem hasWt_one_sub_one : HasWt C ((1 : Matrix (Fin n) (Fin n) F) - 1) := by
  rw [sub_self]
  exact HasWt.zero

end HasWt

@[expose] def wt2 (e : Fin (n / 2) → ℤ) : Set (Fin (n / 2) → ℤ) := {w | w = e ∨ w = 2 • e}

theorem mem_wt2 {e w : Fin (n / 2) → ℤ} : w ∈ wt2 e ↔ w = e ∨ w = 2 • e := Iff.rfl

theorem wt2_add {e : Fin (n / 2) → ℤ} (a c b : Fin n) (h1 : weight n a - weight n c ∈ wt2 e)
    (h2 : weight n c - weight n b ∈ wt2 e) : weight n a - weight n b ∈ wt2 e := by
  have hsum : weight n a - weight n b = (weight n a - weight n c) + (weight n c - weight n b) := by
    abel
  rw [mem_wt2] at h1 h2 ⊢
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
  · right
    rw [hsum, h1, h2, two_nsmul]
  · have h3 : weight n a - weight n b = 3 • e := by rw [hsum, h1, h2]; abel
    have he := eq_zero_of_weight_sub_eq_nsmul h3 le_rfl
    left
    rw [h3, he, smul_zero]
  · have h3 : weight n a - weight n b = 3 • e := by rw [hsum, h1, h2]; abel
    have he := eq_zero_of_weight_sub_eq_nsmul h3 le_rfl
    left
    rw [h3, he, smul_zero]
  · have h3 : weight n a - weight n b = 4 • e := by rw [hsum, h1, h2]; abel
    have he := eq_zero_of_weight_sub_eq_nsmul h3 (by norm_num)
    left
    rw [h3, he, smul_zero]

theorem hasWt_mul_sub_one {e : Fin (n / 2) → ℤ} {M M' : Matrix (Fin n) (Fin n) F}
    (hM : HasWt (wt2 e) (M - 1)) (hM' : HasWt (wt2 e) (M' - 1)) :
    HasWt (wt2 e) (M * M' - 1) := by
  have h : M * M' - 1 = (M - 1) + (M' - 1) + (M - 1) * (M' - 1) := by noncomm_ring
  rw [h]
  exact (hM.add hM').add (hM.mul hM' fun a c b h1 h2 => wt2_add a c b h1 h2)

variable (σ n) in
@[expose] def wt2Subgroup (e : Fin (n / 2) → ℤ) : Subgroup (SU σ n) where
  carrier := {x | HasWt (wt2 e) (mat σ n x - 1) ∧ HasWt (wt2 e) (mat σ n x⁻¹ - 1)}
  mul_mem' {x y} hx hy := by
    refine ⟨by rw [map_mul]; exact hasWt_mul_sub_one hx.1 hy.1, ?_⟩
    rw [_root_.mul_inv_rev, map_mul]
    exact hasWt_mul_sub_one hy.2 hx.2
  one_mem' := ⟨by rw [map_one]; exact hasWt_one_sub_one,
    by rw [inv_one, map_one]; exact hasWt_one_sub_one⟩
  inv_mem' {x} hx := ⟨hx.2, by rw [inv_inv]; exact hx.1⟩

theorem mem_wt2Subgroup {e : Fin (n / 2) → ℤ} {x : SU σ n} :
    x ∈ wt2Subgroup σ n e ↔
      HasWt (wt2 e) (mat σ n x - 1) ∧ HasWt (wt2 e) (mat σ n x⁻¹ - 1) := Iff.rfl

variable (hσ : ∀ c, σ (σ c) = c)

theorem hasWt_rootMatrix {i j : Fin n} (c : F) :
    HasWt {weight n i - weight n j} (rootMatrix σ i j c - 1) := by
  have h : rootMatrix σ i j c - 1 = single i j c - single (Fin.rev j) (Fin.rev i) (σ c) := by
    rw [rootMatrix]
    abel
  rw [h]
  refine (hasWt_single i j c).sub ((hasWt_single _ _ _).mono' fun a b hab => ?_)
  rw [Set.mem_singleton_iff] at hab ⊢
  rw [hab, weight_rev', weight_rev']
  abel

theorem hasWt_longRootMatrix (i : Fin n) (c : F) :
    HasWt {2 • weight n i} (longRootMatrix i c - 1) := by
  have h : longRootMatrix i c - 1 = single i (Fin.rev i) c := by
    rw [longRootMatrix]
    abel
  rw [h]
  refine (hasWt_single _ _ _).mono' fun a b hab => ?_
  rw [Set.mem_singleton_iff] at hab ⊢
  rw [hab, weight_rev', sub_neg_eq_add, two_nsmul]

theorem hasWt_heisenbergMatrix {i k : Fin n} (hk : Fin.rev k = k) (a b : F) :
    HasWt (wt2 (weight n i)) (heisenbergMatrix σ i k a b - 1) := by
  have h : heisenbergMatrix σ i k a b - 1 =
      single i k a - single k (Fin.rev i) (σ a) + single i (Fin.rev i) b := by
    rw [heisenbergMatrix]
    abel
  have hk0 := weight_eq_zero_of_rev_eq (n := n) hk
  rw [h]
  refine (((hasWt_single _ _ _).mono' fun p q hpq => ?_).sub
    ((hasWt_single _ _ _).mono' fun p q hpq => ?_)).add
    ((hasWt_single _ _ _).mono' fun p q hpq => ?_)
  · rw [Set.mem_singleton_iff] at hpq
    rw [mem_wt2, hpq, hk0, sub_zero]
    exact Or.inl rfl
  · rw [Set.mem_singleton_iff] at hpq
    rw [mem_wt2, hpq, hk0, weight_rev', zero_sub, neg_neg]
    exact Or.inl rfl
  · rw [Set.mem_singleton_iff] at hpq
    rw [mem_wt2, hpq, weight_rev', sub_neg_eq_add, two_nsmul]
    exact Or.inr rfl

theorem rootGroup_le_wt2Subgroup (γ : Fin (n / 2) → ℤ) :
    rootGroup σ hσ n γ ≤ wt2Subgroup σ n (toStd n γ) := by
  unfold rootGroup
  refine sup_le (sup_le ?_ ?_) ?_
  · refine iSup_le fun i => iSup_le fun j => iSup_le fun hij => iSup_le fun hi => iSup_le fun hj =>
      iSup_le fun _ => iSup_le fun hw => ?_
    rintro _ ⟨c, rfl⟩
    refine mem_wt2Subgroup.2 ⟨?_, ?_⟩
    · rw [mat_apply, coe_rootHom]
      exact (hasWt_rootMatrix c.toAdd).mono fun w hw' =>
        mem_wt2.2 (Or.inl ((Set.mem_singleton_iff.mp hw').trans hw))
    · rw [← map_inv, mat_apply, coe_rootHom]
      exact (hasWt_rootMatrix _).mono fun w hw' =>
        mem_wt2.2 (Or.inl ((Set.mem_singleton_iff.mp hw').trans hw))
  · refine iSup_le fun i => iSup_le fun hi => iSup_le fun hw => ?_
    rintro _ ⟨c, rfl⟩
    refine mem_wt2Subgroup.2 ⟨?_, ?_⟩
    · rw [mat_apply, coe_longRootHom]
      exact (hasWt_longRootMatrix i _).mono fun w hw' =>
        mem_wt2.2 (Or.inl ((Set.mem_singleton_iff.mp hw').trans hw))
    · rw [← map_inv, mat_apply, coe_longRootHom]
      exact (hasWt_longRootMatrix i _).mono fun w hw' =>
        mem_wt2.2 (Or.inl ((Set.mem_singleton_iff.mp hw').trans hw))
  · refine iSup_le fun i => iSup_le fun k => iSup_le fun hi => iSup_le fun hik =>
      iSup_le fun hk => iSup_le fun hw => ?_
    intro x hx
    obtain ⟨a', b', -, hab'⟩ := (heisenbergSubgroup σ hσ hi hik hk).inv_mem hx
    obtain ⟨a, b, -, hab⟩ := hx
    refine mem_wt2Subgroup.2 ⟨?_, ?_⟩
    · rw [mat_apply, hab, ← hw]
      exact hasWt_heisenbergMatrix hk a b
    · rw [mat_apply, hab', ← hw]
      exact hasWt_heisenbergMatrix hk a' b'

theorem hasWt_of_mem_rootGroup {γ : Fin (n / 2) → ℤ} {x : SU σ n}
    (hx : x ∈ rootGroup σ hσ n γ) : HasWt (wt2 (toStd n γ)) (mat σ n x - 1) :=
  (mem_wt2Subgroup.1 (rootGroup_le_wt2Subgroup hσ γ hx)).1

theorem mat_apply_of_mem_rootGroup {γ : Fin (n / 2) → ℤ} {x : SU σ n}
    (hx : x ∈ rootGroup σ hσ n γ) {a b : Fin n}
    (h : weight n a - weight n b ≠ toStd n γ) (h2 : weight n a - weight n b ≠ 2 • toStd n γ) :
    mat σ n x a b = (1 : Matrix (Fin n) (Fin n) F) a b := by
  have := (hasWt_of_mem_rootGroup hσ hx).eq_zero_apply (a := a) (b := b) (by
    rw [mem_wt2]
    rintro (h' | h')
    exacts [h h', h2 h'])
  rwa [Matrix.sub_apply, sub_eq_zero] at this

theorem eq_zero_of_two_nsmul_eq_zero {e : Fin (n / 2) → ℤ} (h : (0 : Fin (n / 2) → ℤ) = 2 • e) :
    e = 0 := by
  funext c
  have := congrFun h c
  simp only [Pi.zero_apply, Pi.smul_apply, nsmul_eq_mul, Nat.cast_ofNat] at this ⊢
  omega

theorem mat_apply_self_of_mem_rootGroup {γ : Fin (n / 2) → ℤ} (hγ : toStd n γ ≠ 0)
    {x : SU σ n} (hx : x ∈ rootGroup σ hσ n γ) (a : Fin n) : mat σ n x a a = 1 := by
  rw [mat_apply_of_mem_rootGroup hσ hx, one_apply_eq]
  · rw [sub_self]
    exact fun h => hγ h.symm
  · rw [sub_self]
    exact fun h => hγ (eq_zero_of_two_nsmul_eq_zero h)

theorem mat_apply_of_weight_sub_eq_neg {γ : Fin (n / 2) → ℤ} (hγ : toStd n γ ≠ 0)
    {x : SU σ n} (hx : x ∈ rootGroup σ hσ n γ) {a b : Fin n}
    (h : weight n a - weight n b = -toStd n γ) : mat σ n x a b = 0 := by
  have hab : a ≠ b := by
    rintro rfl
    rw [sub_self, zero_eq_neg] at h
    exact hγ h
  rw [mat_apply_of_mem_rootGroup hσ hx, one_apply_ne hab]
  · rw [h]
    intro h'
    apply hγ
    funext c
    have := congrFun h' c
    simp only [Pi.neg_apply, Pi.zero_apply] at this ⊢
    omega
  · rw [h]
    intro h'
    apply hγ
    funext c
    have := congrFun h' c
    simp only [Pi.neg_apply, Pi.smul_apply, nsmul_eq_mul, Nat.cast_ofNat, Pi.zero_apply] at this ⊢
    omega

theorem eq_of_mem_rootGroup {γ : Fin (n / 2) → ℤ} {x y : SU σ n} (hx : x ∈ rootGroup σ hσ n γ)
    (hy : y ∈ rootGroup σ hσ n γ)
    (h : ∀ a b, (weight n a - weight n b = toStd n γ ∨
      weight n a - weight n b = 2 • toStd n γ) → mat σ n x a b = mat σ n y a b) : x = y := by
  apply mat_injective
  ext a b
  by_cases hab : weight n a - weight n b = toStd n γ ∨ weight n a - weight n b = 2 • toStd n γ
  · exact h a b hab
  · rw [not_or] at hab
    rw [mat_apply_of_mem_rootGroup hσ hx hab.1 hab.2, mat_apply_of_mem_rootGroup hσ hy hab.1 hab.2]

theorem rootHom_mem {i j : Fin n} (hij : i ≠ j) (hi : i ≠ Fin.rev i) (hj : j ≠ Fin.rev j)
    (hji : j ≠ Fin.rev i) {γ : Fin (n / 2) → ℤ} (hw : weight n i - weight n j = toStd n γ)
    (c : Multiplicative F) : rootHom σ hσ hij hi hj c ∈ rootGroup σ hσ n γ :=
  rootHom_mem_rootGroup hσ hij hi hj hji hw c

theorem longRootHom_mem {i : Fin n} (hi : i ≠ Fin.rev i) {γ : Fin (n / 2) → ℤ}
    (hw : 2 • weight n i = toStd n γ) (c : Multiplicative (traceZero σ)) :
    longRootHom σ hi c ∈ rootGroup σ hσ n γ :=
  longRootHom_mem_rootGroup hσ hi hw c

theorem heisenberg_le {i k : Fin n} (hi : i ≠ Fin.rev i) (hik : i ≠ k) (hk : Fin.rev k = k)
    {γ : Fin (n / 2) → ℤ} (hw : weight n i = toStd n γ) :
    heisenbergSubgroup σ hσ hi hik hk ≤ rootGroup σ hσ n γ :=
  heisenberg_le_rootGroup hσ hi hik hk hw

variable (n) in
def lv : (Fin (n / 2) → ℤ) →+ ℤ where
  toFun v := ∑ c : Fin (n / 2), ((n : ℤ) - 1 - 2 * c) * v c
  map_zero' := by simp
  map_add' v w := by simp [mul_add, Finset.sum_add_distrib]

theorem lv_single (c : Fin (n / 2)) : lv n (Pi.single c 1) = (n : ℤ) - 1 - 2 * c := by
  simp [lv, Pi.single_apply]

theorem lv_weight (i : Fin n) : lv n (weight n i) = (n : ℤ) - 1 - 2 * i.val := by
  have := i.isLt
  unfold weight
  split_ifs with h h'
  · rw [lv_single]
  · rw [map_neg, lv_single]
    have hc : ((n - 1 - i.val : ℕ) : ℤ) = (n : ℤ) - 1 - i.val := by omega
    rw [hc]
    ring
  · rw [map_zero]
    omega

theorem two_mul_ht (v : Fin (n / 2) → ℤ) : 2 * ht v = lv n (toStd n v) := by
  let f : (Fin (n / 2) → ℤ) →+ ℤ :=
    { toFun := fun v => 2 * ht v
      map_zero' := by simp [ht]
      map_add' := fun v w => by simp [ht, Finset.sum_add_distrib, mul_add] }
  let g : (Fin (n / 2) → ℤ) →+ ℤ := (lv n).comp (toStdLin n).toAddMonoidHom
  have hfg : f = g := by
    refine AddMonoidHom.functions_ext _ f g fun k x => ?_
    have hs : (Pi.single k x : Fin (n / 2) → ℤ) = x • Pi.single k 1 := by
      funext j
      simp [Pi.single_apply]
    change 2 * ht (Pi.single k x) = lv n (toStdLin n (Pi.single k x))
    rw [toStdLin_apply, hs, toStd_zsmul, map_zsmul]
    have hht : ht (x • Pi.single k (1 : ℤ)) = x := by
      simp [ht, Pi.single_apply]
    rw [hht, smul_eq_mul]
    have hk := k.isLt
    by_cases h : k.val + 1 < n / 2
    · rw [toStd_single_of_lt n h, map_sub, lv_single, lv_single]
      push_cast
      ring
    · by_cases he : Even n
      · rw [toStd_single_of_even he h, map_nsmul, lv_single]
        obtain ⟨r, hr⟩ := he
        have hk' : ((k : ℕ) : ℤ) = r - 1 := by omega
        rw [hk', hr, nsmul_eq_mul]
        push_cast
        ring
      · rw [toStd_single_of_odd he h, lv_single]
        rw [Nat.not_even_iff_odd] at he
        obtain ⟨r, hr⟩ := he
        have hk' : ((k : ℕ) : ℤ) = r - 1 := by omega
        rw [hk', hr]
        push_cast
        ring
  exact DFunLike.congr_fun hfg v

theorem ht_eq_of_weight_sub {γ : Fin (n / 2) → ℤ} {a b : Fin n}
    (h : weight n a - weight n b = toStd n γ) : ht γ = (b.val : ℤ) - a.val := by
  have h1 := two_mul_ht γ
  rw [← h, map_sub, lv_weight, lv_weight] at h1
  linarith

theorem two_mul_ht_eq_of_weight_sub {γ : Fin (n / 2) → ℤ} {a b : Fin n}
    (h : weight n a - weight n b = 2 • toStd n γ) : 2 * ht γ = (b.val : ℤ) - a.val := by
  have h1 := two_mul_ht γ
  have h2 := congrArg (lv n) h
  rw [map_sub, lv_weight, lv_weight, map_nsmul, ← h1] at h2
  simp only [nsmul_eq_mul, Nat.cast_ofNat] at h2
  linarith

theorem mem_roots_of_weight_sub {γ : Fin (n / 2) → ℤ} {a b : Fin n} (hab : a ≠ b)
    (h : weight n a - weight n b = toStd n γ) : γ ∈ roots (isFiniteType_cartan n) (divisible n) := by
  rw [roots_eq]
  by_cases ha : a = Fin.rev a
  ·
    have hb : b ≠ Fin.rev b := fun hb => hab (middle_unique ha.symm hb.symm)
    right; right
    refine ⟨fun he => ?_, Fin.rev b, (rev_ne_rev_rev hb), ?_⟩
    · obtain ⟨r, hr⟩ := he
      have h1 := congrArg Fin.val ha
      have := a.isLt
      simp only [Fin.val_rev] at h1
      omega
    · rw [← h, weight_eq_zero_of_rev_eq ha.symm, weight_rev', zero_sub]
  by_cases hb : b = Fin.rev b
  · right; right
    refine ⟨fun he => ?_, a, ha, ?_⟩
    · obtain ⟨r, hr⟩ := he
      have h1 := congrArg Fin.val hb
      have := b.isLt
      simp only [Fin.val_rev] at h1
      omega
    · rw [← h, weight_eq_zero_of_rev_eq hb.symm, sub_zero]
  by_cases hba : b = Fin.rev a
  · right; left
    refine ⟨a, ha, ?_⟩
    rw [← h, hba, weight_rev', sub_neg_eq_add, two_nsmul]
  · left
    exact ⟨a, b, hab, ha, hb, hba, h.symm⟩

end CFSG.LieType.Universal.Unitary.SUExtras
