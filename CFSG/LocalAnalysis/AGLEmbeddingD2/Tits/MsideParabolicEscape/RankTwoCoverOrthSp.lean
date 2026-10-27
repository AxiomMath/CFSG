module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.RankTwoCoverOrthRank
public import CFSG.LieType.Steinberg.Classical.Symplectic.RankOne
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabHub

public section

namespace CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.RankTwoCoverOrth

open Matrix CFSG.LieType.Steinberg.Sp CFSG.LieType.Universal CFSG.LieType.Universal.Symplectic
  CFSG.LieType.Universal.Symplectic.SpExtras CFSG.Assembly.LowTwoRank CFSG.LieType.Steinberg
  CFSG.AGLEmbedding.ParabHub

section Matrices

variable {n : ℕ} {F : Type} [Field F]

theorem mat_x_short {k : Fin n} (hk : k.val + 1 < n) (c : F) :
    mat n F (x n F (Pi.single k 1) c) =
      fromBlocks (Matrix.transvection k ⟨k.val + 1, hk⟩ c) 0 0
        (Matrix.transvection k ⟨k.val + 1, hk⟩ (-c))ᵀ := by
  rw [x_eq (stdVec_shortPos_eq hk), elt_difference_eq_leviHom, mat_equiv_leviHom,
    TauCeti.transvectionUnit_inv, TauCeti.coe_transvectionUnit, TauCeti.coe_transvectionUnit]

theorem mat_x_neg_short {k : Fin n} (hk : k.val + 1 < n) (c : F) :
    mat n F (x n F (-Pi.single k 1) c) =
      fromBlocks (Matrix.transvection ⟨k.val + 1, hk⟩ k c) 0 0
        (Matrix.transvection ⟨k.val + 1, hk⟩ k (-c))ᵀ := by
  rw [x_eq (stdVec_shortNeg_eq hk), elt_difference_eq_leviHom, mat_equiv_leviHom,
    TauCeti.transvectionUnit_inv, TauCeti.coe_transvectionUnit, TauCeti.coe_transvectionUnit]

theorem mat_x_long {k : Fin n} (hk : ¬k.val + 1 < n) (c : F) :
    mat n F (x n F (Pi.single k 1) c) = Matrix.transvection (.inl k) (.inr k) c := by
  rw [x_eq (stdVec_positiveLong_eq hk), mat_elt_positiveLong]

theorem mat_x_neg_long {k : Fin n} (hk : ¬k.val + 1 < n) (c : F) :
    mat n F (x n F (-Pi.single k 1) c) = Matrix.transvection (.inr k) (.inl k) c := by
  rw [x_eq (stdVec_negativeLong_eq hk), mat_elt_negativeLong]

theorem blk1 {ι : Type*} [Fintype ι] [DecidableEq ι] {p q : ι} (hpq : p ≠ q) :
    Matrix.transvection p q (1 : F) * Matrix.transvection q p 1 - 1 =
      Matrix.single p p (1 : F) + Matrix.single p q 1 + Matrix.single q p 1 := by
  simp only [Matrix.transvection, add_mul, mul_add, Matrix.one_mul, Matrix.mul_one,
    Matrix.single_mul_single_same, mul_one]
  abel

theorem blk2 {ι : Type*} [Fintype ι] [DecidableEq ι] {p q : ι} (hpq : p ≠ q) :
    (Matrix.transvection p q (-1 : F))ᵀ * (Matrix.transvection q p (-1 : F))ᵀ - 1 =
      Matrix.single q q (1 : F) - Matrix.single p q 1 - Matrix.single q p 1 := by
  simp only [Matrix.transvection, Matrix.transpose_add, Matrix.transpose_one,
    Matrix.transpose_single, add_mul, mul_add, Matrix.one_mul, Matrix.mul_one,
    Matrix.single_mul_single_same, mul_one, neg_mul_neg]
  ext a b
  simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.one_apply, Matrix.single_apply]
  split_ifs <;> simp_all <;> ring

theorem fromBlocks_sub_one {a b : Type*} [Fintype a] [Fintype b] [DecidableEq a] [DecidableEq b]
    (A : Matrix a a F) (B : Matrix a b F) (C : Matrix b a F) (D : Matrix b b F) :
    fromBlocks A B C D - 1 = fromBlocks (A - 1) B C (D - 1) := by
  ext (i | i) (j | j) <;> simp [Matrix.one_apply]

theorem mat_ubar_short {k : Fin n} (hk : k.val + 1 < n) :
    mat n F (x n F (Pi.single k 1) 1 * x n F (-Pi.single k 1) 1) - 1 =
      fromBlocks (Matrix.single k k (1 : F) + Matrix.single k ⟨k.val + 1, hk⟩ 1 +
          Matrix.single ⟨k.val + 1, hk⟩ k 1) 0 0
        (Matrix.single ⟨k.val + 1, hk⟩ ⟨k.val + 1, hk⟩ (1 : F) -
          Matrix.single k ⟨k.val + 1, hk⟩ 1 - Matrix.single ⟨k.val + 1, hk⟩ k 1) := by
  have hne : k ≠ ⟨k.val + 1, hk⟩ := Fin.ne_of_val_ne (by simp)
  rw [map_mul, mat_x_short hk, mat_x_neg_short hk, fromBlocks_multiply]
  simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add]
  rw [fromBlocks_sub_one, blk1 hne, blk2 hne]

theorem mat_ubar_long {k : Fin n} (hk : ¬k.val + 1 < n) :
    mat n F (x n F (Pi.single k 1) 1 * x n F (-Pi.single k 1) 1) - 1 =
      Matrix.single (.inl k) (.inl k) (1 : F) + Matrix.single (.inl k) (.inr k) 1 +
        Matrix.single (.inr k) (.inl k) 1 := by
  rw [map_mul, mat_x_long hk, mat_x_neg_long hk, blk1 Sum.inl_ne_inr]

noncomputable def ubar (n : ℕ) (F : Type) [Field F] (k : Fin n) : StatedSp n F :=
  x n F (Pi.single k 1) 1 * x n F (-Pi.single k 1) 1

def supp (n : ℕ) (k : Fin n) : Finset (Fin n ⊕ Fin n) :=
  if hk : k.val + 1 < n then
    {.inl k, .inl ⟨k.val + 1, hk⟩, .inr k, .inr ⟨k.val + 1, hk⟩}
  else {.inl k, .inr k}

theorem mem_supp {k : Fin n} {a : Fin n ⊕ Fin n} (h : a ∈ supp n k) :
    (a.elim (fun x => x.val) (fun x => x.val)) = k.val ∨
      (a.elim (fun x => x.val) (fun x => x.val)) = k.val + 1 := by
  unfold supp at h
  split_ifs at h with hk
  · simp only [Finset.mem_insert, Finset.mem_singleton] at h
    rcases h with rfl | rfl | rfl | rfl <;> simp
  · simp only [Finset.mem_insert, Finset.mem_singleton] at h
    rcases h with rfl | rfl <;> simp

theorem card_supp_short {k : Fin n} (hk : k.val + 1 < n) : (supp n k).card = 4 := by
  unfold supp
  rw [dif_pos hk]
  have : k ≠ ⟨k.val + 1, hk⟩ := Fin.ne_of_val_ne (by simp)
  simp [Finset.card_insert_of_notMem, this]

theorem card_supp_long {k : Fin n} (hk : ¬ k.val + 1 < n) : (supp n k).card = 2 := by
  unfold supp
  rw [dif_neg hk]
  simp

theorem disjoint_supp {i j : Fin n} (hij : i ≠ j) (h1 : ¬ i.val + 1 = j.val)
    (h2 : ¬ j.val + 1 = i.val) : Disjoint (supp n i) (supp n j) := by
  rw [Finset.disjoint_left]
  intro a ha hb
  have := mem_supp ha
  have := mem_supp hb
  have : i.val ≠ j.val := fun h => hij (Fin.ext h)
  omega

theorem N_supp (k : Fin n) : ∀ a b, (mat n F (ubar n F k) - 1) a b ≠ 0 →
    a ∈ supp n k ∧ b ∈ supp n k := by
  unfold ubar
  by_cases hk : k.val + 1 < n
  · rw [mat_ubar_short hk]
    unfold supp
    rw [dif_pos hk]
    rintro (a | a) (b | b) h <;>
      simp only [Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁,
        Matrix.fromBlocks_apply₂₂, Matrix.zero_apply, Matrix.add_apply, Matrix.sub_apply,
        Matrix.single_apply] at h <;>
      first
      | exact absurd rfl h
      | (split_ifs at h <;> aesop)
  · rw [mat_ubar_long hk]
    unfold supp
    rw [dif_neg hk]
    intro a b h
    simp only [Matrix.add_apply, Matrix.single_apply] at h
    split_ifs at h <;> aesop

theorem Nv_short_inl_k {k : Fin n} (hk : k.val + 1 < n) (v : Fin n ⊕ Fin n → F) :
    ((mat n F (ubar n F k) - 1) *ᵥ v) (.inl k) = v (.inl k) + v (.inl ⟨k.val + 1, hk⟩) := by
  have hne : k ≠ ⟨k.val + 1, hk⟩ := Fin.ne_of_val_ne (by simp)
  unfold ubar
  rw [mat_ubar_short hk]
  simp only [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Matrix.fromBlocks_apply₁₁,
    Matrix.fromBlocks_apply₁₂, Matrix.zero_apply, zero_mul, Finset.sum_const_zero, add_zero,
    Matrix.add_apply, Matrix.single_apply, add_mul, Finset.sum_add_distrib, ite_mul, one_mul]
  simp [hne, hne.symm]

theorem Nv_short_inl_k' {k : Fin n} (hk : k.val + 1 < n) (v : Fin n ⊕ Fin n → F) :
    ((mat n F (ubar n F k) - 1) *ᵥ v) (.inl ⟨k.val + 1, hk⟩) = v (.inl k) := by
  have hne : k ≠ ⟨k.val + 1, hk⟩ := Fin.ne_of_val_ne (by simp)
  unfold ubar
  rw [mat_ubar_short hk]
  simp only [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Matrix.fromBlocks_apply₁₁,
    Matrix.fromBlocks_apply₁₂, Matrix.zero_apply, zero_mul, Finset.sum_const_zero, add_zero,
    Matrix.add_apply, Matrix.single_apply, add_mul, Finset.sum_add_distrib, ite_mul, one_mul]
  simp [hne, hne.symm]

theorem Nv_short_inr_k {k : Fin n} (hk : k.val + 1 < n) (v : Fin n ⊕ Fin n → F) :
    ((mat n F (ubar n F k) - 1) *ᵥ v) (.inr k) = - v (.inr ⟨k.val + 1, hk⟩) := by
  have hne : k ≠ ⟨k.val + 1, hk⟩ := Fin.ne_of_val_ne (by simp)
  unfold ubar
  rw [mat_ubar_short hk]
  simp only [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Matrix.fromBlocks_apply₂₁,
    Matrix.fromBlocks_apply₂₂, Matrix.zero_apply, zero_mul, Finset.sum_const_zero, zero_add,
    Matrix.add_apply, Matrix.sub_apply, Matrix.single_apply, sub_mul, add_mul,
    Finset.sum_sub_distrib, Finset.sum_add_distrib, ite_mul, one_mul]
  simp [hne, hne.symm]

theorem Nv_short_inr_k' {k : Fin n} (hk : k.val + 1 < n) (v : Fin n ⊕ Fin n → F) :
    ((mat n F (ubar n F k) - 1) *ᵥ v) (.inr ⟨k.val + 1, hk⟩) =
      v (.inr ⟨k.val + 1, hk⟩) - v (.inr k) := by
  have hne : k ≠ ⟨k.val + 1, hk⟩ := Fin.ne_of_val_ne (by simp)
  unfold ubar
  rw [mat_ubar_short hk]
  simp only [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Matrix.fromBlocks_apply₂₁,
    Matrix.fromBlocks_apply₂₂, Matrix.zero_apply, zero_mul, Finset.sum_const_zero, zero_add,
    Matrix.add_apply, Matrix.sub_apply, Matrix.single_apply, sub_mul, add_mul,
    Finset.sum_sub_distrib, Finset.sum_add_distrib, ite_mul, one_mul]
  simp [hne, hne.symm]

theorem Nv_long_inl {k : Fin n} (hk : ¬ k.val + 1 < n) (v : Fin n ⊕ Fin n → F) :
    ((mat n F (ubar n F k) - 1) *ᵥ v) (.inl k) = v (.inl k) + v (.inr k) := by
  unfold ubar
  rw [mat_ubar_long hk]
  simp only [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Matrix.add_apply,
    Matrix.single_apply, add_mul, Finset.sum_add_distrib, ite_mul, one_mul, zero_mul]
  simp

theorem Nv_long_inr {k : Fin n} (hk : ¬ k.val + 1 < n) (v : Fin n ⊕ Fin n → F) :
    ((mat n F (ubar n F k) - 1) *ᵥ v) (.inr k) = v (.inl k) := by
  unfold ubar
  rw [mat_ubar_long hk]
  simp only [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Matrix.add_apply,
    Matrix.single_apply, add_mul, Finset.sum_add_distrib, ite_mul, one_mul, zero_mul]
  simp

theorem N_inj (k : Fin n) : ∀ v : Fin n ⊕ Fin n → F, (∀ a ∉ supp n k, v a = 0) →
    (∀ a ∈ supp n k, ((mat n F (ubar n F k) - 1) *ᵥ v) a = 0) → ∀ a, v a = 0 := by
  intro v hv h a
  by_cases hk : k.val + 1 < n
  · have e1 := h (.inl k) (by simp [supp, hk])
    have e2 := h (.inl ⟨k.val + 1, hk⟩) (by simp [supp, hk])
    have e3 := h (.inr k) (by simp [supp, hk])
    have e4 := h (.inr ⟨k.val + 1, hk⟩) (by simp [supp, hk])
    rw [Nv_short_inl_k hk] at e1
    rw [Nv_short_inl_k' hk] at e2
    rw [Nv_short_inr_k hk] at e3
    rw [Nv_short_inr_k' hk] at e4
    have a1 : v (.inl k) = 0 := e2
    have a2 : v (.inl ⟨k.val + 1, hk⟩) = 0 := by rw [a1, zero_add] at e1; exact e1
    have a3 : v (.inr ⟨k.val + 1, hk⟩) = 0 := neg_eq_zero.1 e3
    have a4 : v (.inr k) = 0 := by rw [a3, zero_sub, neg_eq_zero] at e4; exact e4
    by_cases ha : a ∈ supp n k
    · simp only [supp, dif_pos hk, Finset.mem_insert, Finset.mem_singleton] at ha
      rcases ha with rfl | rfl | rfl | rfl <;> assumption
    · exact hv a ha
  · have e1 := h (.inl k) (by simp [supp, hk])
    have e2 := h (.inr k) (by simp [supp, hk])
    rw [Nv_long_inl hk] at e1
    rw [Nv_long_inr hk] at e2
    have a1 : v (.inl k) = 0 := e2
    have a2 : v (.inr k) = 0 := by rw [a1, zero_add] at e1; exact e1
    by_cases ha : a ∈ supp n k
    · simp only [supp, dif_neg hk, Finset.mem_insert, Finset.mem_singleton] at ha
      rcases ha with rfl | rfl <;> assumption
    · exact hv a ha

theorem card_supp_le (k : Fin n) : (supp n k).card ≤ 4 := by
  by_cases hk : k.val + 1 < n
  · rw [card_supp_short hk]
  · rw [card_supp_long hk]; omega

theorem rk1_ubar_le (k : Fin n) : RankTwoCoverOrth.rk1 (mat n F (ubar n F k)) ≤ 4 := by
  unfold RankTwoCoverOrth.rk1
  refine (RankTwoCoverOrth.rank_le_card_of_rowSupport _ (supp n k) ?_).trans (card_supp_le k)
  intro a ha b
  by_contra hne
  exact ha (N_supp k a b hne).1

theorem N_mul_N {i j : Fin n} (hd : Disjoint (supp n i) (supp n j)) :
    (mat n F (ubar n F i) - 1) * (mat n F (ubar n F j) - 1) = 0 := by
  ext a b
  simp only [Matrix.mul_apply, Matrix.zero_apply]
  refine Finset.sum_eq_zero fun c _ => ?_
  by_cases h1 : (mat n F (ubar n F i) - 1) a c = 0
  · simp [h1]
  by_cases h2 : (mat n F (ubar n F j) - 1) c b = 0
  · simp [h2]
  exact absurd (N_supp j c b h2).1 (Finset.disjoint_left.1 hd (N_supp i a c h1).2)

theorem rk1_pair_ge {i j : Fin n} (hij : i ≠ j) (h1 : ¬ i.val + 1 = j.val)
    (h2 : ¬ j.val + 1 = i.val) :
    6 ≤ RankTwoCoverOrth.rk1 (mat n F (ubar n F i * ubar n F j)) := by
  have hd := disjoint_supp hij h1 h2
  have hsum : mat n F (ubar n F i * ubar n F j) - 1 =
      (mat n F (ubar n F i) - 1) + (mat n F (ubar n F j) - 1) := by
    have e : ∀ A B : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F,
        A * B - 1 = (A - 1) + (B - 1) + (A - 1) * (B - 1) := fun A B => by noncomm_ring
    rw [map_mul, e, N_mul_N hd, add_zero]
  unfold RankTwoCoverOrth.rk1
  rw [hsum]
  refine le_trans ?_ (RankTwoCoverOrth.card_add_le_rank_add _ _ _ _ hd (N_supp i) (N_supp j)
    (N_inj i) (N_inj j))
  have hs : ∀ k : Fin n, (supp n k).card = if k.val + 1 < n then 4 else 2 := fun k => by
    by_cases hk : k.val + 1 < n
    · rw [card_supp_short hk, if_pos hk]
    · rw [card_supp_long hk, if_neg hk]
  rw [hs i, hs j]
  have : i.val ≠ j.val := fun h => hij (Fin.ext h)
  split_ifs <;> omega

theorem sp_not_conj {i j : Fin n} (hij : i ≠ j) (h1 : ¬ i.val + 1 = j.val)
    (h2 : ¬ j.val + 1 = i.val) (g : StatedSp n F) (k : Fin n) (ε : ℤ) :
    g * (ubar n F k) ^ ε * g⁻¹ ≠ ubar n F i * ubar n F j := by
  intro h
  have hrank := rk1_pair_ge (F := F) hij h1 h2
  have hcoe : ((g * (ubar n F k) ^ ε * g⁻¹ : StatedSp n F) : GL (Fin n ⊕ Fin n) F) =
      (g : GL (Fin n ⊕ Fin n) F) * (ubar n F k : GL (Fin n ⊕ Fin n) F) ^ ε *
        (g : GL (Fin n ⊕ Fin n) F)⁻¹ := by
    simp
  have hmat : mat n F (ubar n F i * ubar n F j) =
      (((g : GL (Fin n ⊕ Fin n) F) * (ubar n F k : GL (Fin n ⊕ Fin n) F) ^ ε *
        (g : GL (Fin n ⊕ Fin n) F)⁻¹ : GL (Fin n ⊕ Fin n) F) : Matrix (Fin n ⊕ Fin n) _ F) := by
    rw [← h, mat_apply, hcoe]
  rw [hmat, Units.val_mul, Units.val_mul] at hrank
  have h3 := RankTwoCoverOrth.rk1_conj (F := F) (g : GL (Fin n ⊕ Fin n) F)
    (((ubar n F k : GL (Fin n ⊕ Fin n) F) ^ ε : GL (Fin n ⊕ Fin n) F) : Matrix _ _ F)
  have h4 := RankTwoCoverOrth.rk1_zpow_le (F := F) (ubar n F k : GL (Fin n ⊕ Fin n) F) ε
  have h5 := rk1_ubar_le (F := F) k
  rw [mat_apply] at h5
  rw [h3] at hrank
  exact absurd (hrank.trans (h4.trans h5)) (by omega)

theorem two_le_rk1_ubar (k : Fin n) : 2 ≤ RankTwoCoverOrth.rk1 (mat n F (ubar n F k)) := by
  unfold RankTwoCoverOrth.rk1
  refine le_trans ?_ (RankTwoCoverOrth.card_le_rank _ (supp n k) (N_inj k))
  by_cases hk : k.val + 1 < n
  · rw [card_supp_short hk]; omega
  · rw [card_supp_long hk]

end Matrices

section Inner

variable {n : ℕ} {F : Type} [Field F]

theorem x_zero_eq_one {γ : Fin n → ℤ}
    (hpar : IsParametrization (Φ := Φ n F) (rootDatum n F).rootGroup (x n F)) (hγ : γ ∈ (Φ n F).roots) :
    x n F γ 0 = 1 := by
  have h := (hpar γ hγ).2.1 0 0
  rw [add_zero] at h
  exact (mul_eq_left.1 h.symm)

theorem sp_ubar_pow_three [CharP F 2] (k : Fin n) : (ubar n F k) ^ 3 = 1 := by
  obtain ⟨φ, -, hU, hL⟩ := Sp.rankOne (n := n) (F := F) k
  have : ubar n F k = φ (sl2Upper 1 * sl2Lower 1) := by
    rw [map_mul, hU, hL]; rfl
  rw [this, ← map_pow, sl2_upper_lower_cube, map_one]

theorem root_pair_eq_ubar [Finite F] [CharP F 2] (hF : Nat.card F = 2) (k : Fin n)
    {x' y' : StatedSp n F} (hx' : x' ∈ (rootDatum n F).rootGroup (Pi.single k 1))
    (hy' : y' ∈ (rootDatum n F).rootGroup (-Pi.single k 1)) (h3 : (x' * y') ^ 3 = 1)
    (h1 : x' * y' ≠ 1) : x' * y' = ubar n F k := by
  have hpar := Sp.isParametrization (n := n) (F := F)
  have hroot : (Pi.single k 1 : Fin n → ℤ) ∈ (Φ n F).roots ∧
      (-Pi.single k 1 : Fin n → ℤ) ∈ (Φ n F).roots :=
    ⟨(Φ n F).single_mem k, (Φ n F).neg_mem _ ((Φ n F).single_mem k)⟩
  obtain ⟨c, rfl⟩ := ((hpar _ hroot.1).1 x').1 hx'
  obtain ⟨d, rfl⟩ := ((hpar _ hroot.2).1 y').1 hy'
  have hcard2 : ∀ c : F, c = 0 ∨ c = 1 := by
    obtain ⟨y, -, hy⟩ := (Nat.card_eq_two_iff' (0 : F)).1 hF
    intro c
    by_cases hc : c = 0
    · exact Or.inl hc
    · exact Or.inr ((hy c hc).trans (hy 1 one_ne_zero).symm)
  have hsq : ∀ {γ : Fin n → ℤ}, γ ∈ (Φ n F).roots → ∀ c : F, x n F γ c * x n F γ c = 1 := by
    intro γ hγ c
    rw [← (hpar γ hγ).2.1 c c, CharTwo.add_self_eq_zero]
    exact x_zero_eq_one hpar hγ
  have hc1 : c = 1 := by
    rcases hcard2 c with hc | hc
    · exfalso
      have e0 : x n F (Pi.single k 1) c = 1 := by rw [hc]; exact x_zero_eq_one hpar hroot.1
      have hy2 := hsq hroot.2 d
      rw [e0, one_mul] at h3 h1
      apply h1
      calc x n F (-Pi.single k 1) d = x n F (-Pi.single k 1) d ^ 3 := by
            rw [pow_succ, pow_two, hy2, one_mul]
        _ = 1 := h3
    · exact hc
  have hd1 : d = 1 := by
    rcases hcard2 d with hd | hd
    · exfalso
      have e0 : x n F (-Pi.single k 1) d = 1 := by rw [hd]; exact x_zero_eq_one hpar hroot.2
      have hx2 := hsq hroot.1 c
      rw [e0, mul_one] at h3 h1
      apply h1
      calc x n F (Pi.single k 1) c = x n F (Pi.single k 1) c ^ 3 := by
            rw [pow_succ, pow_two, hx2, one_mul]
        _ = 1 := h3
    · exact hd
  subst hc1 hd1
  rfl

theorem sp_orth [Finite F] [CharP F 2] (hF : Nat.card F = 2) {i j : Fin n} (hij : i ≠ j)
    (h1 : ¬ i.val + 1 = j.val) (h2 : ¬ j.val + 1 = i.val) :
    ∃ xi ∈ (rootDatum n F).rootGroup (Pi.single i 1),
    ∃ yi ∈ (rootDatum n F).rootGroup (-Pi.single i 1),
    ∃ xj ∈ (rootDatum n F).rootGroup (Pi.single j 1),
    ∃ yj ∈ (rootDatum n F).rootGroup (-Pi.single j 1),
      (xi * yi) ^ 3 = 1 ∧ xi * yi ≠ 1 ∧ (xj * yj) ^ 3 = 1 ∧ xj * yj ≠ 1 ∧
      xj * yj ∉ Subgroup.zpowers (xi * yi) ∧
      ∀ k, ∀ x ∈ (rootDatum n F).rootGroup (Pi.single k 1),
        ∀ y ∈ (rootDatum n F).rootGroup (-Pi.single k 1),
        (x * y) ^ 3 = 1 → x * y ≠ 1 → ∀ g : StatedSp n F, ∀ e : ℕ,
          g * (x * y) ^ e * g⁻¹ ≠ xi * yi * (xj * yj) := by
  have hpar := Sp.isParametrization (n := n) (F := F)
  have hroot : ∀ k : Fin n, (Pi.single k 1 : Fin n → ℤ) ∈ (Φ n F).roots ∧
      (-Pi.single k 1 : Fin n → ℤ) ∈ (Φ n F).roots := fun k =>
    ⟨(Φ n F).single_mem k, (Φ n F).neg_mem _ ((Φ n F).single_mem k)⟩
  have hx : ∀ k : Fin n, x n F (Pi.single k 1) 1 ∈ (rootDatum n F).rootGroup (Pi.single k 1) :=
    fun k => ((hpar _ (hroot k).1).1 _).2 ⟨1, rfl⟩
  have hy : ∀ k : Fin n, x n F (-Pi.single k 1) 1 ∈ (rootDatum n F).rootGroup (-Pi.single k 1) :=
    fun k => ((hpar _ (hroot k).2).1 _).2 ⟨1, rfl⟩
  have hne1 : ∀ k : Fin n, ubar n F k ≠ 1 := by
    intro k h
    have := two_le_rk1_ubar (F := F) k
    rw [h] at this
    simp [rk1] at this
  refine ⟨x n F (Pi.single i 1) 1, hx i, x n F (-Pi.single i 1) 1, hy i,
    x n F (Pi.single j 1) 1, hx j, x n F (-Pi.single j 1) 1, hy j, sp_ubar_pow_three i,
    hne1 i, sp_ubar_pow_three j, hne1 j, ?_, ?_⟩
  · intro hz
    obtain ⟨ε, hε⟩ := Subgroup.mem_zpowers_iff.1 hz
    refine sp_not_conj (F := F) hij h1 h2 1 i (1 + ε) ?_
    show (1 : StatedSp n F) * ubar n F i ^ (1 + ε) * (1 : StatedSp n F)⁻¹ =
      ubar n F i * ubar n F j
    rw [inv_one, mul_one, one_mul, _root_.zpow_add, zpow_one]
    exact congrArg _ hε
  · intro k x' hx' y' hy' h3 h1' g e
    change Fin n at k
    rw [root_pair_eq_ubar hF k hx' hy' h3 h1']
    have := sp_not_conj (F := F) hij h1 h2 g k (e : ℤ)
    rwa [zpow_natCast] at this

end Inner

end CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.RankTwoCoverOrth
