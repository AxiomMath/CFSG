module

public import CFSG.CGT.M24R.L2Sub

public section

namespace CFSG.CGT.M24R

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.CosetTable

@[expose] def bb0 : N8 := n8 (bWord 0)

@[expose] def bb1 : N8 := n8 (bWord 1)

@[expose] def B8 : Subgroup N8 := Subgroup.closure {bb0, bb1}

section B


theorem isTab_b0T : IsTab b0T bb0 := isTab_wTab _

theorem isTab_b1T : IsTab b1T bb1 := isTab_wTab _

theorem isTab_b01T : IsTab b01T (bb0 * bb1) := isTab_b0T.mul isTab_b1T

variable (hcard : Nat.card N8 = 322560)
include hcard

theorem bFacts : bb0 * bb0 = 1 ∧ bb1 * bb1 = 1 ∧ bb0 * bb1 = bb1 * bb0 ∧ bb0 ≠ 1 ∧ bb1 ≠ 1 ∧
    bb0 ≠ bb1 ∧ bb0 * bb1 ≠ 1 ∧ bb0 * bb1 ≠ bb0 ∧ bb0 * bb1 ≠ bb1 ∧ bb0 ∉ T8 := by
  have hb := Certificates.certificate21193.2.2.2.2.1
  simp only [bCheck, Bool.and_eq_true, Bool.not_eq_true'] at hb
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩ := hb
  have s0 : b0T.size = 16 := wTab_size _
  have s1 : b1T.size = 16 := wTab_size _
  have s01 : b01T.size = 16 := compT_size _ _
  have t0 := isTab_b0T
  have t1 := isTab_b1T
  have t01 := isTab_b01T
  have ne : ∀ {X Y : Table} {x y : N8}, IsTab X x → IsTab Y y → X.size = 16 → Y.size = 16 →
      (X == Y) = false → x ≠ y := by
    intro X Y x y hX hY hXs hYs h hxy
    rw [← (hX.beq_iff hcard hY hXs hYs)] at hxy
    rw [hxy] at h
    exact Bool.false_ne_true h.symm
  refine ⟨(t0.mul t0).beq_iff hcard IsTab.one (compT_size _ _) idT_size |>.1 h1,
    (t1.mul t1).beq_iff hcard IsTab.one (compT_size _ _) idT_size |>.1 h2,
    (t0.commT_iff hcard t1).1 h3, ne t0 IsTab.one s0 idT_size h4, ne t1 IsTab.one s1 idT_size h5,
    ne t0 t1 s0 s1 h6, ne t01 IsTab.one s01 idT_size h7, ne t01 t0 s01 s0 h8,
    ne t01 t1 s01 s1 h9, fun h => ?_⟩
  rw [← isTt_iff hcard t0 s0, h10] at h
  exact Bool.false_ne_true h

theorem mem_B8_iff (x : N8) : x ∈ B8 ↔ x = 1 ∨ x = bb0 ∨ x = bb1 ∨ x = bb0 * bb1 := by
  obtain ⟨h1, h2, h3, -⟩ := bFacts hcard
  exact mem_closure_pair_iff h1 h2 h3 x

theorem isBt_iff {X : Table} {x : N8} (hX : IsTab X x) (hXs : X.size = 16) :
    isBt X = true ↔ x ∈ B8 := by
  rw [mem_B8_iff hcard, isBt, bList, List.contains_iff_mem]
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  rw [hX.eq_iff hcard IsTab.one hXs idT_size, hX.eq_iff hcard isTab_b0T hXs (wTab_size _),
    hX.eq_iff hcard isTab_b1T hXs (wTab_size _),
    hX.eq_iff hcard isTab_b01T hXs (compT_size _ _)]

theorem card_B8 : Nat.card B8 = 4 := by
  obtain ⟨-, -, -, h4, h5, h6, h7, h8, h9, -⟩ := bFacts hcard
  have hm := mem_B8_iff hcard
  exact card_eq_four_of B8 (a := 1) (b := bb0) (c := bb1) (d := bb0 * bb1)
    (fun y hy => (hm y).1 hy) (one_mem _) ((hm _).2 (Or.inr (Or.inl rfl)))
    ((hm _).2 (Or.inr (Or.inr (Or.inl rfl)))) ((hm _).2 (Or.inr (Or.inr (Or.inr rfl))))
    h4.symm h5.symm h7.symm h6 h8.symm h9.symm

end B

section Norm

variable (hcard : Nat.card N8 = 322560)
include hcard

theorem conjIn_iff {L : List Table} {K : Subgroup N8} (hL1 : ∀ Y ∈ L, ∃ y ∈ K, IsTab Y y)
    (hL2 : ∀ y ∈ K, ∃ Y ∈ L, IsTab Y y) {X P : Table} {x p : N8} (hX : IsTab X x)
    (hP : IsTab P p) : conjIn X P L = true ↔ x * p * x⁻¹ ∈ K := by
  rw [conjIn, List.any_eq_true]
  constructor
  · rintro ⟨Y, hY, h⟩
    obtain ⟨y, hyK, hy⟩ := hL1 Y hY
    have e := ((hX.mul hP).beq_iff hcard (hy.mul hX) (compT_size _ _) (compT_size _ _)).1 h
    rw [e, mul_inv_cancel_right]
    exact hyK
  · intro h
    obtain ⟨Y, hY, hy⟩ := hL2 _ h
    refine ⟨Y, hY, ((hX.mul hP).beq_iff hcard (hy.mul hX) (compT_size _ _) (compT_size _ _)).2 ?_⟩
    group

theorem conjInR_iff {L : List Table} {K : Subgroup N8} (hL1 : ∀ Y ∈ L, ∃ y ∈ K, IsTab Y y)
    (hL2 : ∀ y ∈ K, ∃ Y ∈ L, IsTab Y y) {X P : Table} {x p : N8} (hX : IsTab X x)
    (hP : IsTab P p) : conjInR X P L = true ↔ x⁻¹ * p * x ∈ K := by
  rw [conjInR, List.any_eq_true]
  constructor
  · rintro ⟨Y, hY, h⟩
    obtain ⟨y, hyK, hy⟩ := hL1 Y hY
    have e := ((hP.mul hX).beq_iff hcard (hX.mul hy) (compT_size _ _) (compT_size _ _)).1 h
    rw [mul_assoc, e, inv_mul_cancel_left]
    exact hyK
  · intro h
    obtain ⟨Y, hY, hy⟩ := hL2 _ h
    refine ⟨Y, hY, ((hP.mul hX).beq_iff hcard (hX.mul hy) (compT_size _ _) (compT_size _ _)).2 ?_⟩
    group

theorem normK_iff {L : List Table} {K : Subgroup N8} (hL1 : ∀ Y ∈ L, ∃ y ∈ K, IsTab Y y)
    (hL2 : ∀ y ∈ K, ∃ Y ∈ L, IsTab Y y) {P Q X : Table} {p q x : N8} (hP : IsTab P p)
    (hQ : IsTab Q q) (hX : IsTab X x) (hp : p ∈ K) (hq : q ∈ K)
    (hK : ∀ y ∈ K, y = 1 ∨ y = p ∨ y = q ∨ y = p * q) :
    normK L P Q X = true ↔ x ∈ Subgroup.normalizer (K : Set N8) := by
  rw [mem_normalizer_four hp hq hK, normK, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true,
    conjIn_iff hcard hL1 hL2 hX hP, conjIn_iff hcard hL1 hL2 hX hQ,
    conjInR_iff hcard hL1 hL2 hX hP, conjInR_iff hcard hL1 hL2 hX hQ]
  tauto

theorem bList_spec : (∀ Y ∈ bList, ∃ y ∈ B8, IsTab Y y) ∧ ∀ y ∈ B8, ∃ Y ∈ bList, IsTab Y y := by
  have hm := mem_B8_iff hcard
  constructor
  · intro Y hY
    simp only [bList, List.mem_cons, List.not_mem_nil, or_false] at hY
    rcases hY with rfl | rfl | rfl | rfl
    · exact ⟨1, one_mem _, IsTab.one⟩
    · exact ⟨bb0, (hm _).2 (Or.inr (Or.inl rfl)), isTab_b0T⟩
    · exact ⟨bb1, (hm _).2 (Or.inr (Or.inr (Or.inl rfl))), isTab_b1T⟩
    · exact ⟨bb0 * bb1, (hm _).2 (Or.inr (Or.inr (Or.inr rfl))), isTab_b01T⟩
  · intro y hy
    rcases (hm y).1 hy with rfl | rfl | rfl | rfl
    · exact ⟨_, by simp [bList], IsTab.one⟩
    · exact ⟨_, by simp [bList], isTab_b0T⟩
    · exact ⟨_, by simp [bList], isTab_b1T⟩
    · exact ⟨_, by simp [bList], isTab_b01T⟩

theorem normB_iff {X : Table} {x : N8} (hX : IsTab X x) :
    normB X = true ↔ x ∈ Subgroup.normalizer (B8 : Set N8) := by
  have hm := mem_B8_iff hcard
  exact normK_iff hcard (bList_spec hcard).1 (bList_spec hcard).2 isTab_b0T isTab_b1T hX
    ((hm _).2 (Or.inr (Or.inl rfl))) ((hm _).2 (Or.inr (Or.inr (Or.inl rfl))))
    fun y hy => (hm y).1 hy

theorem mem_dList_iff {c : ℕ} : c ∈ (mkCtx ()).dList ↔
    c ∈ (mkCtx ()).codes ∧ el c ∈ Subgroup.normalizer (B8 : Set N8) := by
  rw [Ctx8.dList, List.mem_filter]
  constructor
  · rintro ⟨hc, h⟩
    exact ⟨hc, (normB_iff hcard (isTab_tab (mem_codes.1 hc).1)).1 h⟩
  · rintro ⟨hc, h⟩
    exact ⟨hc, (normB_iff hcard (isTab_tab (mem_codes.1 hc).1)).2 h⟩

theorem el_of_mem_D {x : N8} (hx : x ∈ Subgroup.normalizer (B8 : Set N8)) :
    ∃ c ∈ (mkCtx ()).dList, x = el c := by
  obtain ⟨c, hc, rfl⟩ := el_surj hcard x
  exact ⟨c, (mem_dList_iff hcard).2 ⟨hc, hx⟩, rfl⟩

end Norm

end CFSG.CGT.M24R
