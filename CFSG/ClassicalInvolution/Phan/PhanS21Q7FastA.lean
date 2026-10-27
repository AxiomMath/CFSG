module

public import CFSG.ClassicalInvolution.Phan.PhanS19Q7Fast
public import CFSG.ClassicalInvolution.Phan.PhanS21Q7SoundC

public section

namespace CFSG.ClassicalInvolution.PhanB3.S.Std.Q7

open CFSG.ClassicalInvolution.PhanB3.S.Std

theorem getElem!_map_range {n : Nat} (f : Nat → Nat) {i : Nat} (hi : i < n) :
    ((Array.range n).map f)[i]! = f i := by
  rw [getElem!_pos _ _ (by simpa using hi)]
  simp

theorem getElem!_map_range_lt {n : Nat} (f : Nat → Nat) (hf : ∀ i, f i < 49) (i : Nat) :
    ((Array.range n).map f)[i]! < 49 := by
  by_cases hi : i < n
  · rw [getElem!_map_range f hi]
    exact hf i
  · rw [getElem!_neg _ _ (by simpa using hi)]
    simp

theorem gfNeg_lt (a : Nat) : gfNeg a < 49 := mk_lt _ _

theorem gfConj_lt (a : Nat) : gfConj a < 49 := mk_lt _ _

theorem fMul_eq {a b : Nat} (ha : a < 49) (hb : b < 49) : fMul a b = gfMul a b := by
  have h : a * 49 + b < 2401 := by omega
  unfold fMul tMul
  rw [getElem!_map_range _ h]
  have h1 : (a * 49 + b) / 49 = a := by omega
  have h2 : (a * 49 + b) % 49 = b := by omega
  rw [h1, h2]

theorem fAdd_eq {a b : Nat} (ha : a < 49) (hb : b < 49) : fAdd a b = gfAdd a b := by
  have h : a * 49 + b < 2401 := by omega
  unfold fAdd tAdd
  rw [getElem!_map_range _ h]
  have h1 : (a * 49 + b) / 49 = a := by omega
  have h2 : (a * 49 + b) % 49 = b := by omega
  rw [h1, h2]

theorem fNeg_eq {a : Nat} (ha : a < 49) : fNeg a = gfNeg a := by
  unfold fNeg tNeg
  rw [getElem!_map_range _ ha]

theorem fConj_eq {a : Nat} (ha : a < 49) : fConj a = gfConj a := by
  unfold fConj tConj
  rw [getElem!_map_range _ ha]

theorem fNorm_eq {a : Nat} (ha : a < 49) : fNorm a = gfMul a (gfConj a) := by
  unfold fNorm tNorm
  rw [getElem!_map_range _ ha]

theorem fMul_lt (a b : Nat) : fMul a b < 49 :=
  getElem!_map_range_lt _ (fun _ => gfMul_lt _ _) _

theorem fAdd_lt (a b : Nat) : fAdd a b < 49 :=
  getElem!_map_range_lt _ (fun _ => gfAdd_lt _ _) _

theorem fNeg_lt (a : Nat) : fNeg a < 49 :=
  getElem!_map_range_lt _ (fun _ => gfNeg_lt _) _

theorem fConj_lt (a : Nat) : fConj a < 49 :=
  getElem!_map_range_lt _ (fun _ => gfConj_lt _) _

theorem fNorm_lt (a : Nat) : fNorm a < 49 :=
  getElem!_map_range_lt _ (fun _ => gfMul_lt _ _) _

@[expose] def Lt49 (x : N7) : Prop :=
  x.x0 < 49 ∧ x.x1 < 49 ∧ x.x2 < 49 ∧ x.x3 < 49 ∧ x.x4 < 49 ∧ x.x5 < 49 ∧ x.x6 < 49

theorem coordsLt_iff (c : N7) : coordsLt c = true ↔ Lt49 c := by
  simp [coordsLt, Lt49, and_assoc]

theorem gfDec_five : gfDec 5 = -2 := gfDec_kappa

theorem five_lt : (5 : Nat) < 49 := by norm_num

theorem hDiag_lt (x : N7) : hDiag x < 49 := fAdd_lt _ _

theorem hF_lt (x y : N7) : hF x y < 49 := fAdd_lt _ _

theorem bF_lt (x y : N7) : bF x y < 49 := fAdd_lt _ _

theorem b0F_lt (c : N7) (b1 b2 b4 b5 b6 : Nat) : b0F c b1 b2 b4 b5 b6 < 49 := fNeg_lt _

theorem bF_eq {x y : N7} (hx : Lt49 x) (hy : Lt49 y) : bF x y = bfN x y := by
  obtain ⟨hx0, hx1, hx2, hx3, hx4, hx5, hx6⟩ := hx
  obtain ⟨hy0, hy1, hy2, hy3, hy4, hy5, hy6⟩ := hy
  simp only [bF, bfN, gfKappa, fMul_eq, fAdd_eq, hx0, hx1, hx2, hx3, hx4, hx5, hx6, hy0, hy1, hy2,
    hy3, hy4, hy5, hy6, five_lt, gfMul_lt, gfAdd_lt]

theorem bF_dec {x y : N7} (hx : Lt49 x) (hy : Lt49 y) : gfDec (bF x y) = bfC x.dec y.dec := by
  rw [bF_eq hx hy, bfN_dec]

theorem hDiag_dec {x : N7} (hx : Lt49 x) : gfDec (hDiag x) = herC x.dec x.dec := by
  obtain ⟨hx0, hx1, hx2, hx3, hx4, hx5, hx6⟩ := hx
  simp only [hDiag, fNorm_eq, fMul_eq, fAdd_eq, hx0, hx1, hx2, hx3, hx4, hx5, hx6, five_lt,
    gfMul_lt, gfAdd_lt, gfDec_add, gfDec_mul, gfDec_conj, gfDec_five]
  simp only [herC, bfC, tauC, N7.dec, conj49]
  ring

theorem hF_dec {x y : N7} (hx : Lt49 x) (hy : Lt49 y) : gfDec (hF x y) = herC x.dec y.dec := by
  obtain ⟨hx0, hx1, hx2, hx3, hx4, hx5, hx6⟩ := hx
  obtain ⟨hy0, hy1, hy2, hy3, hy4, hy5, hy6⟩ := hy
  simp only [hF, fConj_eq, fMul_eq, fAdd_eq, hx0, hx1, hx2, hx3, hx4, hx5, hx6, hy0, hy1, hy2,
    hy3, hy4, hy5, hy6, five_lt, gfMul_lt, gfAdd_lt, gfConj_lt, gfDec_add, gfDec_mul, gfDec_conj,
    gfDec_five]
  simp only [herC, bfC, tauC, N7.dec, conj49]
  ring


theorem herC_swap (x y : V7) : herC y x = star (herC x y) := by
  simp only [herC, bfC, tauC, conj49, star_add, star_mul', star_neg, star_star, star_ofNat]
  ring

theorem eq_iff_dec {a b : Nat} (ha : a < 49) (hb : b < 49) : a = b ↔ gfDec a = gfDec b :=
  ⟨fun h => by rw [h], gfDec_inj ha hb⟩

theorem adjF_eq_colN {u v : N7} (hu : Lt49 u) (hv : Lt49 v) :
    adjF u v (hDiag u) (hDiag v) = colN u v := by
  rw [Bool.eq_iff_iff, colN_iff]
  unfold adjF colC
  simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq]
  have e1 : gfDec (fMul (hDiag u) (hDiag v)) = herC u.dec u.dec * herC v.dec v.dec := by
    rw [fMul_eq (hDiag_lt u) (hDiag_lt v), gfDec_mul, hDiag_dec hu, hDiag_dec hv]
  have e2 : gfDec (fNorm (hF u v)) = herC u.dec v.dec * star (herC u.dec v.dec) := by
    rw [fNorm_eq (hF_lt u v), gfDec_mul, gfDec_conj, hF_dec hu hv]
  have e3 : gramC u.dec v.dec =
      herC u.dec u.dec * herC v.dec v.dec - herC u.dec v.dec * star (herC u.dec v.dec) := by
    rw [gramC, herC_swap u.dec v.dec]
  rw [eq_zero_iff_of_lt (bF_lt u v), bF_dec hu hv, eq_iff_dec (fMul_lt _ _) (fNorm_lt _), e1, e2,
    e3, sub_eq_zero]


theorem lt49_candN {c : N7} {n1 n2 n4 n5 n6 : Nat} (h1 : n1 < 49) (h2 : n2 < 49) (h4 : n4 < 49)
    (h5 : n5 < 49) (h6 : n6 < 49) : Lt49 (candN c n1 n2 n4 n5 n6) :=
  ⟨gfNeg_lt _, h1, h2, by simp [candN], h4, h5, h6⟩

theorem candN_mem_A {c : N7} {x2 x5 x6 : Nat} (h2 : x2 < 49) (h5 : x5 < 49) (h6 : x6 < 49) :
    candN c 1 x2 (gfAdd (gfNeg (gfMul x2 x5)) (gfMul x6 x6)) x5 x6 ∈ q7Cands c := by
  simp only [q7Cands, candsA, List.mem_append, List.mem_flatMap, List.mem_map, List.mem_range]
  exact Or.inl (Or.inl (Or.inl ⟨x2, h2, x5, h5, x6, h6, rfl⟩))

theorem candN_mem_B {c : N7} {x4 x6 : Nat} (h4 : x4 < 49) (h6 : x6 < 49) :
    candN c 0 1 x4 (gfMul x6 x6) x6 ∈ q7Cands c := by
  simp only [q7Cands, candsB, List.mem_append, List.mem_flatMap, List.mem_map, List.mem_range]
  exact Or.inl (Or.inl (Or.inr ⟨x4, h4, x6, h6, rfl⟩))

theorem candN_mem_C {c : N7} {x5 : Nat} (h5 : x5 < 49) : candN c 0 0 1 x5 0 ∈ q7Cands c := by
  simp only [q7Cands, candsC, List.mem_append, List.mem_map, List.mem_range]
  exact Or.inl (Or.inr ⟨x5, h5, rfl⟩)

theorem candN_mem_D (c : N7) : candN c 0 0 0 1 0 ∈ q7Cands c := by
  simp [q7Cands, candsD]

theorem mem_q7Pts_iff {c b : N7} (hb : b ∈ q7Cands c) :
    b ∈ q7Pts c ↔ (isFFN b = true ∧ colN e0N b = true ∧ colN c b = true) := by
  unfold q7Pts
  rw [List.mem_filter]
  simp only [Bool.and_eq_true, and_assoc]
  exact ⟨fun h => h.2, fun h => ⟨hb, h⟩⟩

theorem herC_e0_e0 : herC e0C e0C = 1 := by
  simp [herC, bfC, tauC, e0C, conj49]

theorem herC_e0_left (B : V7) : herC e0C B = star B.x0 := by
  simp [herC, bfC, tauC, e0C, conj49]

theorem herC_e0_right (B : V7) : herC B e0C = B.x0 := by
  simp [herC, bfC, tauC, e0C, conj49]

theorem vert_iff_vtxF {c b : N7} (hc : Lt49 c) (hc3 : c.x3 = 1) {n1 n2 n4 n5 n6 : Nat}
    (hb : b = candN c n1 n2 n4 n5 n6) (h1 : n1 < 49) (h2 : n2 < 49) (h4 : n4 < 49)
    (h5 : n5 < 49) (h6 : n6 < 49)
    (hq : gfDec n1 * gfDec n4 + gfDec n2 * gfDec n5 = gfDec n6 ^ 2) :
    (isFFN b = true ∧ colN e0N b = true ∧ colN c b = true) ↔
      vtxF c (herN c c) b (hDiag b) = true := by
  have hbL : Lt49 b := hb ▸ lt49_candN h1 h2 h4 h5 h6
  have hB : b.dec = candV c.dec (gfDec n1) (gfDec n2) (gfDec n4) (gfDec n5) (gfDec n6) := by
    rw [hb, candN_dec]
  have hB3 : b.dec.x3 = 0 := by rw [hB]; rfl
  have hC3 : c.dec.x3 = 1 := by simp [N7.dec, hc3, gfDec_one]
  have F1 : bfC b.dec b.dec = 0 := by
    rw [hB]
    simp only [bfC, candV]
    linear_combination 2 * hq
  have F2 : bfC e0C b.dec = 0 := by rw [bfC_e0C, hB3]
  have F3 : bfC c.dec b.dec = 0 := by
    rw [hB]
    simp only [bfC, candV, hC3]
    ring
  have e0 : gfDec (hDiag b) = herC b.dec b.dec := hDiag_dec hbL
  have eγ : gfDec (herN c c) = herC c.dec c.dec := herN_dec c c
  have eh : gfDec (hF c b) = herC c.dec b.dec := hF_dec hc hbL
  have hG0 : gramC e0C b.dec = herC b.dec b.dec - star b.dec.x0 * b.dec.x0 := by
    rw [gramC, herC_e0_e0, herC_e0_left, herC_e0_right, one_mul]
  have hG1 : gramC c.dec b.dec =
      herC c.dec c.dec * herC b.dec b.dec - herC c.dec b.dec * star (herC c.dec b.dec) := by
    rw [gramC, herC_swap c.dec b.dec]
  rw [isFFN_iff, colN_iff, colN_iff, e0N_dec]
  unfold isFFC colC vtxF
  simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq]
  rw [eq_zero_iff_of_lt (hDiag_lt b), eq_iff_dec (hDiag_lt b) (fNorm_lt _),
    eq_iff_dec (fMul_lt _ _) (fNorm_lt _), e0, fNorm_eq (hbL.1), gfDec_mul, gfDec_conj,
    fMul_eq (herN_lt c c) (hDiag_lt b), gfDec_mul, eγ, e0, fNorm_eq (hF_lt c b), gfDec_mul,
    gfDec_conj, eh, hG0, hG1, F1, F2, F3, sub_eq_zero, sub_eq_zero]
  simp only [true_and]
  have e : star b.dec.x0 * b.dec.x0 = gfDec b.x0 * star (gfDec b.x0) := mul_comm _ _
  rw [e, and_assoc]


theorem one_lt_49 : (1 : Nat) < 49 := by norm_num

theorem zero_lt_49 : (0 : Nat) < 49 := by norm_num

theorem lt49_mkA (c : N7) {x2 x5 x6 : Nat} (h2 : x2 < 49) (h5 : x5 < 49) (h6 : x6 < 49) :
    Lt49 (mkA c x2 x5 x6) :=
  ⟨b0F_lt _ _ _ _ _ _, one_lt_49, h2, zero_lt_49, fAdd_lt _ _, h5, h6⟩

theorem lt49_mkB (c : N7) {x4 x6 : Nat} (h4 : x4 < 49) (h6 : x6 < 49) : Lt49 (mkB c x4 x6) :=
  ⟨b0F_lt _ _ _ _ _ _, zero_lt_49, one_lt_49, zero_lt_49, h4, fMul_lt _ _, h6⟩

theorem lt49_mkC (c : N7) {x5 : Nat} (h5 : x5 < 49) : Lt49 (mkC c x5) :=
  ⟨b0F_lt _ _ _ _ _ _, zero_lt_49, zero_lt_49, zero_lt_49, one_lt_49, h5, zero_lt_49⟩

theorem lt49_mkD (c : N7) : Lt49 (mkD c) :=
  ⟨b0F_lt _ _ _ _ _ _, zero_lt_49, zero_lt_49, zero_lt_49, zero_lt_49, one_lt_49, zero_lt_49⟩

theorem mkA_eq {c : N7} (hc : Lt49 c) {x2 x5 x6 : Nat} (h2 : x2 < 49) (h5 : x5 < 49)
    (h6 : x6 < 49) :
    mkA c x2 x5 x6 = candN c 1 x2 (gfAdd (gfNeg (gfMul x2 x5)) (gfMul x6 x6)) x5 x6 := by
  obtain ⟨hc0, hc1, hc2, hc3, hc4, hc5, hc6⟩ := hc
  simp only [mkA, b0F, candN, gfKappa, fMul_eq, fAdd_eq, fNeg_eq, hc1, hc2, hc4, hc5, hc6, h2, h5,
    h6, five_lt, one_lt_49, gfMul_lt, gfAdd_lt, gfNeg_lt]

theorem mkB_eq {c : N7} (hc : Lt49 c) {x4 x6 : Nat} (h4 : x4 < 49) (h6 : x6 < 49) :
    mkB c x4 x6 = candN c 0 1 x4 (gfMul x6 x6) x6 := by
  obtain ⟨hc0, hc1, hc2, hc3, hc4, hc5, hc6⟩ := hc
  simp only [mkB, b0F, candN, gfKappa, fMul_eq, fAdd_eq, fNeg_eq, hc1, hc2, hc4, hc5, hc6, h4, h6,
    five_lt, one_lt_49, zero_lt_49, gfMul_lt, gfAdd_lt]

theorem mkC_eq {c : N7} (hc : Lt49 c) {x5 : Nat} (h5 : x5 < 49) :
    mkC c x5 = candN c 0 0 1 x5 0 := by
  obtain ⟨hc0, hc1, hc2, hc3, hc4, hc5, hc6⟩ := hc
  simp only [mkC, b0F, candN, gfKappa, fMul_eq, fAdd_eq, fNeg_eq, hc1, hc2, hc4, hc5, hc6, h5,
    five_lt, one_lt_49, zero_lt_49, gfMul_lt, gfAdd_lt]

theorem mkD_eq {c : N7} (hc : Lt49 c) : mkD c = candN c 0 0 0 1 0 := by
  obtain ⟨hc0, hc1, hc2, hc3, hc4, hc5, hc6⟩ := hc
  simp only [mkD, b0F, candN, gfKappa, fMul_eq, fAdd_eq, fNeg_eq, hc1, hc2, hc4, hc5, hc6,
    five_lt, one_lt_49, zero_lt_49, gfMul_lt, gfAdd_lt]

theorem mkA_mem_iff {c : N7} (hc : Lt49 c) (hc3 : c.x3 = 1) {x2 x5 x6 : Nat} (h2 : x2 < 49)
    (h5 : x5 < 49) (h6 : x6 < 49) :
    mkA c x2 x5 x6 ∈ q7Pts c ↔
      vtxF c (herN c c) (mkA c x2 x5 x6) (hDiag (mkA c x2 x5 x6)) = true := by
  have e := mkA_eq hc h2 h5 h6
  rw [mem_q7Pts_iff (by rw [e]; exact candN_mem_A h2 h5 h6)]
  refine vert_iff_vtxF hc hc3 e one_lt_49 h2 (gfAdd_lt _ _) h5 h6 ?_
  simp only [gfDec_one, gfDec_add, gfDec_neg, gfDec_mul]
  ring

theorem mkB_mem_iff {c : N7} (hc : Lt49 c) (hc3 : c.x3 = 1) {x4 x6 : Nat} (h4 : x4 < 49)
    (h6 : x6 < 49) :
    mkB c x4 x6 ∈ q7Pts c ↔
      vtxF c (herN c c) (mkB c x4 x6) (hDiag (mkB c x4 x6)) = true := by
  have e := mkB_eq hc h4 h6
  rw [mem_q7Pts_iff (by rw [e]; exact candN_mem_B h4 h6)]
  refine vert_iff_vtxF hc hc3 e zero_lt_49 one_lt_49 h4 (gfMul_lt _ _) h6 ?_
  simp only [gfDec_zero, gfDec_one, gfDec_mul]
  ring

theorem mkC_mem_iff {c : N7} (hc : Lt49 c) (hc3 : c.x3 = 1) {x5 : Nat} (h5 : x5 < 49) :
    mkC c x5 ∈ q7Pts c ↔
      vtxF c (herN c c) (mkC c x5) (hDiag (mkC c x5)) = true := by
  have e := mkC_eq hc h5
  rw [mem_q7Pts_iff (by rw [e]; exact candN_mem_C h5)]
  refine vert_iff_vtxF hc hc3 e zero_lt_49 zero_lt_49 one_lt_49 h5 zero_lt_49 ?_
  simp only [gfDec_zero, gfDec_one]
  ring

theorem mkD_mem_iff {c : N7} (hc : Lt49 c) (hc3 : c.x3 = 1) :
    mkD c ∈ q7Pts c ↔ vtxF c (herN c c) (mkD c) (hDiag (mkD c)) = true := by
  have e := mkD_eq hc
  rw [mem_q7Pts_iff (by rw [e]; exact candN_mem_D c)]
  refine vert_iff_vtxF hc hc3 e zero_lt_49 zero_lt_49 zero_lt_49 one_lt_49 zero_lt_49 ?_
  simp only [gfDec_zero, gfDec_one]
  ring

end CFSG.ClassicalInvolution.PhanB3.S.Std.Q7
