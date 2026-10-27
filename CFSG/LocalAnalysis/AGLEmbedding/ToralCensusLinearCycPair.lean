module

public import CFSG.RankThree.SteinbergR3ECALinearSplitBlocks
public import CFSG.LocalAnalysis.ComponentInitial.LinearCoverFourRoots

public section

namespace CFSG.AGLEmbedding.ToralCensus

open Matrix

section Pair

variable {G : Type*} [Group G]

theorem exists_noncyclic_of_commute [Finite G] {p : ℕ} (hp : p.Prime) {x y : G}
    (hxy : Commute x y) (hx : x ^ p = 1) (hy : y ^ p = 1) (hx1 : x ≠ 1) (hy1 : y ≠ 1)
    {Z : Subgroup G} (hsep : ∀ i j : ℕ, x ^ i * y ^ j ∈ Z → x ^ i = 1 ∧ y ^ j = 1) :
    IsPGroup p (Subgroup.closure {x, y}) ∧ Subgroup.closure {x, y} ⊓ Z = ⊥ ∧
      ¬ IsCyclic (Subgroup.closure {x, y}) := by
  have : Fact p.Prime := ⟨hp⟩
  have hxinv : x⁻¹ = x ^ (p - 1) :=
    (eq_inv_of_mul_eq_one_left (by rw [← pow_succ, Nat.sub_add_cancel hp.one_le, hx])).symm
  have hyinv : y⁻¹ = y ^ (p - 1) :=
    (eq_inv_of_mul_eq_one_left (by rw [← pow_succ, Nat.sub_add_cancel hp.one_le, hy])).symm
  have hform : ∀ g ∈ Subgroup.closure {x, y}, ∃ i j : ℕ, x ^ i * y ^ j = g := by
    intro g hg
    induction hg using Subgroup.closure_induction with
    | mem g hg =>
      rcases hg with rfl | rfl
      · exact ⟨1, 0, by simp⟩
      · exact ⟨0, 1, by simp⟩
    | one => exact ⟨0, 0, by simp⟩
    | mul g h _ _ hg hh =>
      obtain ⟨i, j, rfl⟩ := hg
      obtain ⟨k, l, rfl⟩ := hh
      refine ⟨i + k, j + l, ?_⟩
      rw [pow_add, pow_add, mul_assoc, mul_assoc]
      congr 1
      rw [← mul_assoc, ← mul_assoc, (hxy.pow_pow k j).eq]
    | inv g _ hg =>
      obtain ⟨i, j, rfl⟩ := hg
      refine ⟨(p - 1) * i, (p - 1) * j, ?_⟩
      rw [_root_.mul_inv_rev, ← inv_pow, ← inv_pow, hxinv, hyinv, ← pow_mul, ← pow_mul,
        ((hxy.pow_pow ((p - 1) * i) ((p - 1) * j))).eq]
  have hpow : ∀ i j : ℕ, (x ^ i * y ^ j) ^ p = 1 := fun i j => by
    rw [(hxy.pow_pow i j).mul_pow, ← pow_mul, ← pow_mul, mul_comm i, mul_comm j, pow_mul,
      pow_mul, hx, hy, one_pow, one_pow, one_mul]
  refine ⟨fun g => ?_, ?_, fun hcyc => ?_⟩
  · obtain ⟨i, j, hij⟩ := hform g g.2
    exact ⟨1, Subtype.ext (by simpa [← hij] using hpow i j)⟩
  · rw [eq_bot_iff]
    rintro g ⟨hg, hgZ⟩
    obtain ⟨i, j, rfl⟩ := hform g hg
    obtain ⟨h1, h2⟩ := hsep i j hgZ
    rw [h1, h2, one_mul]
    exact Subgroup.one_mem _
  · set Q := Subgroup.closure ({x, y} : Set G) with hQ
    have hxQ : Subgroup.zpowers x ≤ Q := (Subgroup.zpowers_le).mpr
      (Subgroup.subset_closure (Set.mem_insert x {y}))
    have hyQ : Subgroup.zpowers y ≤ Q := (Subgroup.zpowers_le).mpr
      (Subgroup.subset_closure (Set.mem_insert_of_mem x rfl))
    have hc1 : Nat.card ((Subgroup.zpowers x).subgroupOf Q) = p := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hxQ).toEquiv, Nat.card_zpowers,
        orderOf_eq_prime hx hx1]
    have hc2 : Nat.card ((Subgroup.zpowers y).subgroupOf Q) = p := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hyQ).toEquiv, Nat.card_zpowers,
        orderOf_eq_prime hy hy1]
    have heq := (IsCyclic.subgroup_eq_iff_card_eq (G := Q)).mpr (hc1.trans hc2.symm)
    rw [Subgroup.subgroupOf_inj, inf_of_le_left hxQ, inf_of_le_left hyQ] at heq
    have hyx : y⁻¹ ∈ Submonoid.powers x :=
      mem_powers_iff_mem_zpowers.mpr (Subgroup.inv_mem _ (heq ▸ Subgroup.mem_zpowers y))
    obtain ⟨i, hi⟩ := (Submonoid.mem_powers_iff _ _).mp hyx
    have h := (hsep i 1 (by rw [hi, pow_one, inv_mul_cancel]; exact Z.one_mem)).2
    exact hy1 (by simpa using h)

theorem pow_eq_one_of_pow_mem_center [Finite G] {p : ℕ} (hp : p.Prime) {s : G} (hs : s ^ p = 1)
    (hsZ : s ∉ Subgroup.center G) {i : ℕ} (hi : s ^ i ∈ Subgroup.center G) : s ^ i = 1 := by
  have : Fact p.Prime := ⟨hp⟩
  by_contra h
  have hs1 : s ≠ 1 := fun h1 => hsZ (h1 ▸ Subgroup.one_mem _)
  have hord : orderOf (s ^ i) = p :=
    orderOf_eq_prime (by rw [← pow_mul, mul_comm, pow_mul, hs, one_pow]) h
  have hle : Subgroup.zpowers (s ^ i) ≤ Subgroup.zpowers s :=
    (Subgroup.zpowers_le).mpr (Subgroup.npow_mem_zpowers s i)
  have heq := Subgroup.eq_of_le_of_card_ge hle (by
    rw [Nat.card_zpowers, Nat.card_zpowers, hord, orderOf_eq_prime hs hs1])
  exact hsZ ((Subgroup.zpowers_le.mpr hi) (heq ▸ Subgroup.mem_zpowers s))

end Pair

open CFSG.RankThree.CALinearPlane

variable {K : Type*} [Field K] {n : ℕ}

theorem blockOn_sub_one_mul_blockOn_sub_one {J₁ J₂ : Finset (Fin n)} (h : Disjoint J₁ J₂)
    (X : Matrix (Fin J₁.card) (Fin J₁.card) K) (Y : Matrix (Fin J₂.card) (Fin J₂.card) K) :
    (blockOn K J₁ X - 1) * (blockOn K J₂ Y - 1) = 0 := by
  ext i j
  rw [Matrix.mul_apply, Matrix.zero_apply]
  refine Finset.sum_eq_zero fun k _ => ?_
  by_cases hk : k ∈ J₁
  · have hk2 : k ∉ J₂ := Finset.disjoint_left.mp h hk
    rw [Matrix.sub_apply (blockOn K J₂ Y), blockOn_apply_not_mem J₂ Y (Or.inl hk2),
      Matrix.one_apply, sub_self, mul_zero]
  · rw [Matrix.sub_apply (blockOn K J₁ X), blockOn_apply_not_mem J₁ X (Or.inr hk),
      Matrix.one_apply, sub_self, zero_mul]

theorem blockOn_mul_comm_of_disjoint {J₁ J₂ : Finset (Fin n)} (h : Disjoint J₁ J₂)
    (X : Matrix (Fin J₁.card) (Fin J₁.card) K) (Y : Matrix (Fin J₂.card) (Fin J₂.card) K) :
    blockOn K J₁ X * blockOn K J₂ Y = blockOn K J₂ Y * blockOn K J₁ X := by
  have h1 := blockOn_sub_one_mul_blockOn_sub_one h X Y
  have h2 := blockOn_sub_one_mul_blockOn_sub_one h.symm Y X
  calc blockOn K J₁ X * blockOn K J₂ Y
      = (blockOn K J₁ X - 1) * (blockOn K J₂ Y - 1) + blockOn K J₁ X + blockOn K J₂ Y - 1 := by
        noncomm_ring
    _ = (blockOn K J₂ Y - 1) * (blockOn K J₁ X - 1) + blockOn K J₂ Y + blockOn K J₁ X - 1 := by
        rw [h1, h2, zero_add, zero_add, add_comm (blockOn K J₁ X)]
    _ = blockOn K J₂ Y * blockOn K J₁ X := by noncomm_ring

theorem blockSLOn_mul_comm_of_disjoint {J₁ J₂ : Finset (Fin n)} (h : Disjoint J₁ J₂)
    (X : SpecialLinearGroup (Fin J₁.card) K) (Y : SpecialLinearGroup (Fin J₂.card) K) :
    blockSLOn K J₁ X * blockSLOn K J₂ Y = blockSLOn K J₂ Y * blockSLOn K J₁ X := by
  apply Subtype.ext
  change (blockSLOn K J₁ X : Matrix (Fin n) (Fin n) K) * blockSLOn K J₂ Y =
    (blockSLOn K J₂ Y : Matrix (Fin n) (Fin n) K) * blockSLOn K J₁ X
  rw [coe_blockSLOn, coe_blockSLOn]
  exact blockOn_mul_comm_of_disjoint h _ _

theorem mem_center_of_blockSLOn_mul_mem_center {J₁ J₂ : Finset (Fin n)} (h : Disjoint J₁ J₂)
    {X : SpecialLinearGroup (Fin J₁.card) K} {Y : SpecialLinearGroup (Fin J₂.card) K}
    (hc : blockSLOn K J₁ X * blockSLOn K J₂ Y ∈
      Subgroup.center (SpecialLinearGroup (Fin n) K)) :
    X ∈ Subgroup.center (SpecialLinearGroup (Fin J₁.card) K) := by
  rw [Subgroup.mem_center_iff]
  intro Z
  apply blockSLOn_injective J₁
  have hZ := Subgroup.mem_center_iff.mp hc (blockSLOn K J₁ Z)
  have hYZ := blockSLOn_mul_comm_of_disjoint h Z Y
  rw [map_mul, map_mul]
  apply mul_right_cancel (b := blockSLOn K J₂ Y)
  rw [mul_assoc, mul_assoc, hZ, hYZ, ← mul_assoc]

theorem exists_noncyclic_of_blocks [Finite K] {p : ℕ} (hp : p.Prime) {J₁ J₂ : Finset (Fin n)}
    (h : Disjoint J₁ J₂) {s₁ : SpecialLinearGroup (Fin J₁.card) K}
    {s₂ : SpecialLinearGroup (Fin J₂.card) K} (hs₁ : s₁ ^ p = 1) (hs₂ : s₂ ^ p = 1)
    (hz₁ : s₁ ∉ Subgroup.center (SpecialLinearGroup (Fin J₁.card) K))
    (hz₂ : s₂ ∉ Subgroup.center (SpecialLinearGroup (Fin J₂.card) K)) :
    IsPGroup p (Subgroup.closure {blockSLOn K J₁ s₁, blockSLOn K J₂ s₂}) ∧
      Subgroup.closure {blockSLOn K J₁ s₁, blockSLOn K J₂ s₂} ⊓
        Subgroup.center (SpecialLinearGroup (Fin n) K) = ⊥ ∧
      ¬ IsCyclic (Subgroup.closure {blockSLOn K J₁ s₁, blockSLOn K J₂ s₂}) := by
  have hne : ∀ {m : ℕ} {s : SpecialLinearGroup (Fin m) K},
      s ∉ Subgroup.center (SpecialLinearGroup (Fin m) K) → s ≠ 1 :=
    fun hs h1 => hs (h1 ▸ Subgroup.one_mem _)
  refine exists_noncyclic_of_commute hp (blockSLOn_mul_comm_of_disjoint h s₁ s₂)
    (by rw [← map_pow, hs₁, map_one]) (by rw [← map_pow, hs₂, map_one])
    (fun h1 => hne hz₁ (blockSLOn_injective J₁ (h1.trans (map_one _).symm)))
    (fun h1 => hne hz₂ (blockSLOn_injective J₂ (h1.trans (map_one _).symm))) fun i j hij => ?_
  rw [← map_pow, ← map_pow] at hij ⊢
  have hc₁ := mem_center_of_blockSLOn_mul_mem_center h hij
  have hij' := hij
  rw [blockSLOn_mul_comm_of_disjoint h] at hij'
  have hc₂ := mem_center_of_blockSLOn_mul_mem_center h.symm hij'
  rw [pow_eq_one_of_pow_mem_center hp hs₁ hz₁ hc₁, pow_eq_one_of_pow_mem_center hp hs₂ hz₂ hc₂]
  exact ⟨map_one _, map_one _⟩

open CFSG.LocalAnalysis.ComponentInitial.LinearCover

theorem coroot_pow_eq_one_of_pow {a b : Fin n} {ω : K} {p : ℕ} (hω : ω ^ p = 1) :
    corootVec a b ω ^ p = 1 := by
  rw [corootVec, mul_pow, ← Pi.mulSingle_pow, ← Pi.mulSingle_pow, hω, inv_pow, hω, inv_one,
    Pi.mulSingle_one, Pi.mulSingle_one, mul_one]

theorem sq_eq_one_imp_eq_one_charTwo [CharP K 2] {r : K} (h : r ^ 2 = 1) : r = 1 := by
  have h0 : (r - 1) ^ 2 = 0 := by
    linear_combination h + (1 - r) * (CharP.cast_eq_zero K 2)
  exact sub_eq_zero.mp (pow_eq_zero_iff (by norm_num) |>.mp h0)

theorem eq_one_of_pow_prime_eq_one_of_not_dvd {p : ℕ} (hp : p.Prime) {r : K} (hr : r ^ p = 1)
    (hndvd : ¬ p ∣ Nat.card K - 1) : r = 1 := by
  have hr0 : r ≠ 0 := by
    rintro rfl
    rw [zero_pow hp.ne_zero] at hr
    exact zero_ne_one hr
  have hu : Units.mk0 r hr0 ^ p = 1 := Units.ext (by simp [hr])
  rcases (Nat.dvd_prime hp).mp (orderOf_dvd_of_pow_eq_one hu) with h | h
  · simpa using congrArg Units.val (orderOf_eq_one_iff.mp h)
  · have hdvd := orderOf_dvd_natCard (Units.mk0 r hr0)
    rw [h, Nat.card_units] at hdvd
    exact absurd hdvd hndvd

theorem apply_self_eq_of_mem_center {g : SpecialLinearGroup (Fin n) K}
    (hg : g ∈ Subgroup.center (SpecialLinearGroup (Fin n) K)) (i j : Fin n) :
    (g : Matrix (Fin n) (Fin n) K) i i = (g : Matrix (Fin n) (Fin n) K) j j := by
  obtain ⟨r, -, hr⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hg
  rw [← hr, scalar_apply, diagonal_apply_eq, diagonal_apply_eq]

theorem coe_diagElt_pow_mul_pow (s s' : Fin n → K) (hs : ∏ i, s i = 1) (hs' : ∏ i, s' i = 1)
    (i j : ℕ) :
    ((diagElt s hs ^ i * diagElt s' hs' ^ j : SpecialLinearGroup (Fin n) K) :
      Matrix (Fin n) (Fin n) K) = diagonal (s ^ i * s' ^ j) := by
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_pow,
    Matrix.SpecialLinearGroup.coe_pow, coe_diagElt, coe_diagElt, diagonal_pow, diagonal_pow,
    diagonal_mul_diagonal]
  rfl

theorem diagElt_corootVec_pow_eq_one {a b : Fin n} {ω : K} (hω0 : ω ≠ 0) {i : ℕ}
    (hi : ω ^ i = 1) : diagElt (corootVec a b ω) (prod_corootVec a b hω0) ^ i = 1 := by
  ext k l
  rw [Matrix.SpecialLinearGroup.coe_pow, coe_diagElt, diagonal_pow, coroot_pow_eq_one_of_pow hi,
    Matrix.SpecialLinearGroup.coe_one]
  simp

theorem exists_noncyclic_of_diag [Finite K] {p : ℕ} (hp : p.Prime) {ω : K} (hω1 : ω ≠ 1)
    (hωp : ω ^ p = 1) {a₀ a₁ a₂ c : Fin n} (h01 : a₀ ≠ a₁) (h12 : a₁ ≠ a₂) (h02 : a₀ ≠ a₂)
    (hc0 : c ≠ a₀) (hc1 : c ≠ a₁) (hc2 : c ≠ a₂) :
    ∃ x y : SpecialLinearGroup (Fin n) K,
      (x : Matrix (Fin n) (Fin n) K) = diagonal (corootVec a₀ a₁ ω) ∧
      (y : Matrix (Fin n) (Fin n) K) = diagonal (corootVec a₁ a₂ ω) ∧
      IsPGroup p (Subgroup.closure {x, y}) ∧
      Subgroup.closure {x, y} ⊓ Subgroup.center (SpecialLinearGroup (Fin n) K) = ⊥ ∧
      ¬ IsCyclic (Subgroup.closure {x, y}) := by
  have hω0 : ω ≠ 0 := by
    rintro rfl
    rw [zero_pow hp.ne_zero] at hωp
    exact zero_ne_one hωp
  set x := diagElt (corootVec a₀ a₁ ω) (prod_corootVec a₀ a₁ hω0) with hx
  set y := diagElt (corootVec a₁ a₂ ω) (prod_corootVec a₁ a₂ hω0) with hy
  refine ⟨x, y, rfl, rfl, exists_noncyclic_of_commute hp (diagElt_mul_comm _ _ _ _)
    (diagElt_corootVec_pow_eq_one hω0 hωp) (diagElt_corootVec_pow_eq_one hω0 hωp)
    (fun h => hω1 ?_) (fun h => hω1 ?_) fun i j hij => ?_⟩
  · have := congrArg (fun g : SpecialLinearGroup (Fin n) K =>
      (g : Matrix (Fin n) (Fin n) K) a₀ a₀) h
    simpa [hx, coe_diagElt, corootVec_apply_left h01] using this
  · have := congrArg (fun g : SpecialLinearGroup (Fin n) K =>
      (g : Matrix (Fin n) (Fin n) K) a₁ a₁) h
    simpa [hy, coe_diagElt, corootVec_apply_left h12] using this
  · have e := fun k => apply_self_eq_of_mem_center hij k c
    simp only [coe_diagElt_pow_mul_pow, diagonal_apply_eq, Pi.mul_apply,
      Pi.pow_apply, corootVec_apply_of_ne hc0 hc1, corootVec_apply_of_ne hc1 hc2, one_pow,
      mul_one] at e
    have e0 := e a₀
    rw [corootVec_apply_left h01, corootVec_apply_of_ne h01 h02, one_pow, mul_one] at e0
    have e2 := e a₂
    rw [corootVec_apply_of_ne h02.symm h12.symm, corootVec_apply_right h12, one_pow, one_mul,
      inv_pow, inv_eq_one] at e2
    exact ⟨diagElt_corootVec_pow_eq_one hω0 e0, diagElt_corootVec_pow_eq_one hω0 e2⟩

theorem exists_noncentral_of_dvd_card [Finite K] [CharP K 2] {m : ℕ} (hm : 2 ≤ m) {p : ℕ}
    (hp : p.Prime) (hdvd : p ∣ Nat.card (SpecialLinearGroup (Fin m) K)) :
    ∃ s : SpecialLinearGroup (Fin m) K, s ^ p = 1 ∧
      s ∉ Subgroup.center (SpecialLinearGroup (Fin m) K) := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨s, hs⟩ := exists_prime_orderOf_dvd_card' p hdvd
  have hsp : s ^ p = 1 := hs ▸ pow_orderOf_eq_one s
  by_cases hsZ : s ∈ Subgroup.center (SpecialLinearGroup (Fin m) K)
  · obtain ⟨r, -, hr⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hsZ
    have hentry : ∀ k : ℕ, ((s ^ k : SpecialLinearGroup (Fin m) K) :
        Matrix (Fin m) (Fin m) K) = scalar (Fin m) (r ^ k) := fun k => by
      rw [Matrix.SpecialLinearGroup.coe_pow, ← hr, map_pow]
    have hrp : r ^ p = 1 := by
      have := congrArg (fun A : Matrix (Fin m) (Fin m) K => A ⟨0, by omega⟩ ⟨0, by omega⟩)
        ((hentry p).symm.trans (by rw [hsp, Matrix.SpecialLinearGroup.coe_one]))
      simpa [scalar_apply] using this
    have hr1 : r ≠ 1 := by
      rintro rfl
      have h1 : s = 1 := Subtype.ext (by rw [← hr, map_one, Matrix.SpecialLinearGroup.coe_one])
      rw [h1, orderOf_one] at hs
      exact hp.one_lt.ne hs
    have hr0 : r ≠ 0 := by
      rintro rfl
      rw [zero_pow hp.ne_zero] at hrp
      exact zero_ne_one hrp
    have h01 : (⟨0, by omega⟩ : Fin m) ≠ ⟨1, by omega⟩ := by simp
    refine ⟨diagElt (corootVec _ _ r) (prod_corootVec ⟨0, by omega⟩ ⟨1, by omega⟩ hr0),
      diagElt_corootVec_pow_eq_one hr0 hrp, fun hc => hr1 ?_⟩
    have e := apply_self_eq_of_mem_center hc ⟨0, by omega⟩ ⟨1, by omega⟩
    rw [coe_diagElt, diagonal_apply_eq, diagonal_apply_eq, corootVec_apply_left h01,
      corootVec_apply_right h01] at e
    refine sq_eq_one_imp_eq_one_charTwo ?_
    rw [sq]
    nth_rw 2 [e]
    exact mul_inv_cancel₀ hr0
  · exact ⟨s, hsp, hsZ⟩

theorem exists_noncentral_of_dvd_pow_sub_one [Finite K] {d : ℕ} (hd : 1 ≤ d) {p : ℕ}
    (hp : p.Prime) (hdvd : p ∣ Nat.card K ^ d - 1) (hndvd : ¬ p ∣ Nat.card K - 1) :
    ∃ s : SpecialLinearGroup (Fin d) K, s ^ p = 1 ∧
      s ∉ Subgroup.center (SpecialLinearGroup (Fin d) K) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : Fintype K := Fintype.ofFinite K
  have hGL : p ∣ Nat.card (GL (Fin d) K) := by
    rw [Matrix.card_GL_field]
    refine dvd_trans ?_ (Finset.dvd_prod_of_mem _ (Finset.mem_univ (⟨0, hd⟩ : Fin d)))
    simpa [Nat.card_eq_fintype_card] using hdvd
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' p hGL
  have hgp : g ^ p = 1 := hg ▸ pow_orderOf_eq_one g
  have hdet : GeneralLinearGroup.det g = 1 := by
    have h1 : GeneralLinearGroup.det g ^ p = 1 := by rw [← map_pow, hgp, map_one]
    have h2 := eq_one_of_pow_prime_eq_one_of_not_dvd hp
      (r := ((GeneralLinearGroup.det g : Kˣ) : K)) (by rw [← Units.val_pow_eq_pow_val, h1,
        Units.val_one]) hndvd
    exact Units.ext h2
  have hdet' : (g : Matrix (Fin d) (Fin d) K).det = 1 := by
    rw [← GeneralLinearGroup.val_det_apply, hdet, Units.val_one]
  obtain ⟨s, hs⟩ : ∃ s : SpecialLinearGroup (Fin d) K,
      (s : Matrix (Fin d) (Fin d) K) = g := ⟨⟨g, hdet'⟩, rfl⟩
  refine ⟨s, ?_, fun hc => ?_⟩
  · ext i j
    rw [Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_one, hs,
      ← Units.val_pow_eq_pow_val, hgp, Units.val_one]
  · obtain ⟨r, -, hr⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hc
    have hr' : scalar (Fin d) r = (g : Matrix (Fin d) (Fin d) K) := hr.trans hs
    have hrp : r ^ p = 1 := by
      have h := congrArg (fun A : Matrix (Fin d) (Fin d) K => A ⟨0, hd⟩ ⟨0, hd⟩)
        (show scalar (Fin d) (r ^ p) = 1 by
          rw [map_pow, hr', ← Units.val_pow_eq_pow_val, hgp, Units.val_one])
      simpa [scalar_apply] using h
    have hr1 := eq_one_of_pow_prime_eq_one_of_not_dvd hp hrp hndvd
    have hg1 : g = 1 := Units.ext (by rw [← hr', hr1, map_one, Units.val_one])
    rw [hg1, orderOf_one] at hg
    exact hp.one_lt.ne hg

end CFSG.AGLEmbedding.ToralCensus
