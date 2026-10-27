module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup

public section

namespace CFSG.LocalAnalysis.ComponentInitial

open Matrix

@[expose] def smallLinearEncH (d0 d1 d2 d3 d4 d5 d6 d7 d8 : ℕ) : ℕ :=
  d0 + 2 * (d1 + 2 * (d2 + 2 * (d3 + 2 * (d4 + 2 * (d5 + 2 * (d6 + 2 * (d7 + 2 * d8)))))))

@[expose] def smallLinearMulAH (n : ℕ) : ℕ :=
  smallLinearEncH (n % 2) ((n % 2 + n / 2 % 2) % 2) (n / 4 % 2) (n / 8 % 2)
    ((n / 8 % 2 + n / 16 % 2) % 2) (n / 32 % 2) (n / 64 % 2) ((n / 64 % 2 + n / 128 % 2) % 2)
    (n / 256 % 2)

@[expose] def smallLinearMulBH (n : ℕ) : ℕ :=
  smallLinearEncH (n / 2 % 2) (n / 4 % 2) (n % 2) (n / 16 % 2) (n / 32 % 2) (n / 8 % 2)
    (n / 128 % 2) (n / 256 % 2) (n / 64 % 2)

@[expose] def smallLinearEnc7 (p q r s : ℕ) : ℕ :=
  p + 7 * (q + 7 * (r + 7 * s))

@[expose] def smallLinearNeg7 (x : ℕ) : ℕ :=
  (7 - x) % 7

@[expose] def smallLinearNorm7 (p q r s : ℕ) : ℕ :=
  min (smallLinearEnc7 p q r s)
    (smallLinearEnc7 (smallLinearNeg7 p) (smallLinearNeg7 q) (smallLinearNeg7 r)
      (smallLinearNeg7 s))

@[expose] def smallLinearMulAG (n : ℕ) : ℕ :=
  smallLinearNorm7 (n / 7 % 7) (smallLinearNeg7 (n % 7)) (n / 343 % 7)
    (smallLinearNeg7 (n / 49 % 7))

@[expose] def smallLinearMulBG (n : ℕ) : ℕ :=
  smallLinearNorm7 (n / 7 % 7) ((smallLinearNeg7 (n % 7) + n / 7 % 7) % 7) (n / 343 % 7)
    ((smallLinearNeg7 (n / 49 % 7) + n / 343 % 7) % 7)

@[expose] def smallLinearMul : Bool → ℕ × ℕ → ℕ × ℕ
  | false, c => (smallLinearMulAH c.1, smallLinearMulAG c.2)
  | true, c => (smallLinearMulBH c.1, smallLinearMulBG c.2)

structure SmallLinearEntry where
  code : ℕ × ℕ
  depth : ℕ
  parent : ℕ × ℕ
  gen : Bool

@[expose] def smallLinearTable : List SmallLinearEntry := [
  ⟨(84, 1236), 13, (212, 1198), false⟩,
  ⟨(85, 984), 13, (215, 462), false⟩,
  ⟨(86, 570), 13, (165, 1254), true⟩,
  ⟨(87, 167), 12, (213, 1076), false⟩,
  ⟨(92, 813), 12, (204, 941), false⟩,
  ⟨(93, 725), 13, (179, 120), true⟩,
  ⟨(94, 847), 12, (181, 1083), true⟩,
  ⟨(95, 1339), 11, (205, 527), false⟩,
  ⟨(98, 97), 2, (140, 434), true⟩,
  ⟨(99, 1115), 9, (142, 606), true⟩,
  ⟨(102, 393), 3, (141, 351), true⟩,
  ⟨(103, 953), 8, (143, 926), true⟩,
  ⟨(106, 777), 3, (156, 638), true⟩,
  ⟨(107, 451), 8, (158, 758), true⟩,
  ⟨(110, 537), 7, (157, 1168), true⟩,
  ⟨(111, 358), 4, (159, 92), true⟩,
  ⟨(114, 1171), 9, (242, 897), false⟩,
  ⟨(115, 1206), 11, (241, 1242), false⟩,
  ⟨(116, 611), 10, (244, 773), false⟩,
  ⟨(117, 1298), 10, (247, 864), false⟩,
  ⟨(122, 675), 8, (234, 425), false⟩,
  ⟨(123, 1034), 15, (233, 161), false⟩,
  ⟨(124, 119), 14, (236, 690), false⟩,
  ⟨(125, 895), 9, (239, 1135), false⟩,
  ⟨(140, 434), 1, (273, 344), true⟩,
  ⟨(141, 351), 2, (275, 91), true⟩,
  ⟨(142, 606), 8, (158, 758), false⟩,
  ⟨(143, 926), 7, (157, 1168), false⟩,
  ⟨(156, 638), 2, (140, 434), false⟩,
  ⟨(157, 1168), 6, (307, 1023), true⟩,
  ⟨(158, 758), 7, (309, 657), true⟩,
  ⟨(159, 92), 3, (141, 351), false⟩,
  ⟨(161, 1348), 13, (266, 566), true⟩,
  ⟨(163, 514), 13, (270, 1148), true⟩,
  ⟨(165, 1254), 12, (267, 1368), true⟩,
  ⟨(167, 1222), 13, (165, 1254), false⟩,
  ⟨(169, 869), 12, (282, 1088), true⟩,
  ⟨(171, 959), 12, (286, 886), true⟩,
  ⟨(172, 997), 11, (281, 524), true⟩,
  ⟨(174, 1048), 13, (285, 165), true⟩,
  ⟨(177, 697), 13, (179, 120), false⟩,
  ⟨(179, 120), 12, (302, 796), true⟩,
  ⟨(181, 1083), 11, (299, 628), true⟩,
  ⟨(183, 574), 12, (181, 1083), false⟩,
  ⟨(185, 788), 13, (171, 959), false⟩,
  ⟨(187, 1283), 11, (318, 972), true⟩,
  ⟨(188, 471), 10, (313, 754), true⟩,
  ⟨(190, 163), 14, (174, 1048), false⟩,
  ⟨(204, 941), 11, (401, 915), true⟩,
  ⟨(205, 527), 10, (403, 1145), true⟩,
  ⟨(206, 1279), 13, (94, 847), false⟩,
  ⟨(207, 124), 14, (93, 725), false⟩,
  ⟨(212, 1198), 12, (417, 1041), true⟩,
  ⟨(213, 1076), 11, (419, 162), true⟩,
  ⟨(214, 1110), 13, (421, 616), true⟩,
  ⟨(215, 462), 12, (423, 739), true⟩,
  ⟨(225, 555), 10, (99, 1115), false⟩,
  ⟨(226, 386), 3, (98, 97), false⟩,
  ⟨(229, 829), 9, (103, 953), false⟩,
  ⟨(230, 644), 4, (102, 393), false⟩,
  ⟨(233, 161), 14, (410, 1181), true⟩,
  ⟨(234, 425), 7, (412, 379), true⟩,
  ⟨(236, 690), 13, (409, 122), true⟩,
  ⟨(239, 1135), 8, (415, 987), true⟩,
  ⟨(241, 1242), 10, (426, 1357), true⟩,
  ⟨(242, 897), 8, (428, 1317), true⟩,
  ⟨(244, 773), 9, (425, 663), true⟩,
  ⟨(247, 864), 9, (431, 1105), true⟩,
  ⟨(249, 1007), 9, (107, 451), false⟩,
  ⟨(250, 589), 4, (106, 777), false⟩,
  ⟨(253, 93), 5, (111, 358), false⟩,
  ⟨(254, 1359), 8, (110, 537), false⟩,
  ⟨(266, 566), 12, (282, 1088), false⟩,
  ⟨(267, 1368), 11, (281, 524), false⟩,
  ⟨(270, 1148), 12, (286, 886), false⟩,
  ⟨(271, 1062), 13, (285, 165), false⟩,
  ⟨(273, 344), 0, (273, 344), false⟩,
  ⟨(275, 91), 1, (273, 344), false⟩,
  ⟨(277, 859), 10, (99, 1115), true⟩,
  ⟨(279, 1313), 9, (103, 953), true⟩,
  ⟨(281, 524), 10, (114, 1171), true⟩,
  ⟨(282, 1088), 11, (116, 611), true⟩,
  ⟨(285, 165), 12, (115, 1206), true⟩,
  ⟨(286, 886), 11, (117, 1298), true⟩,
  ⟨(298, 123), 13, (92, 813), true⟩,
  ⟨(299, 628), 10, (313, 754), false⟩,
  ⟨(302, 796), 11, (318, 972), false⟩,
  ⟨(303, 1230), 12, (95, 1339), true⟩,
  ⟨(305, 489), 4, (106, 777), true⟩,
  ⟨(307, 1023), 5, (305, 489), false⟩,
  ⟨(309, 657), 6, (311, 401), false⟩,
  ⟨(311, 401), 5, (111, 358), true⟩,
  ⟨(313, 754), 9, (122, 675), true⟩,
  ⟨(314, 718), 14, (298, 123), false⟩,
  ⟨(317, 1190), 13, (303, 1230), false⟩,
  ⟨(318, 972), 10, (125, 895), true⟩,
  ⟨(330, 164), 13, (212, 1198), true⟩,
  ⟨(331, 837), 14, (214, 1110), true⟩,
  ⟨(334, 1189), 9, (478, 1273), false⟩,
  ⟨(335, 669), 10, (477, 417), false⟩,
  ⟨(337, 433), 4, (226, 386), true⟩,
  ⟨(339, 743), 5, (230, 644), true⟩,
  ⟨(340, 1328), 11, (225, 555), true⟩,
  ⟨(342, 125), 10, (229, 829), true⟩,
  ⟨(345, 978), 9, (242, 897), true⟩,
  ⟨(346, 460), 10, (244, 773), true⟩,
  ⟨(348, 551), 8, (460, 1093), false⟩,
  ⟨(351, 633), 7, (461, 769), false⟩,
  ⟨(354, 1294), 9, (482, 842), false⟩,
  ⟨(355, 917), 13, (481, 1132), false⟩,
  ⟨(358, 1010), 8, (486, 480), false⟩,
  ⟨(359, 704), 12, (485, 121), false⟩,
  ⟨(369, 95), 8, (234, 425), true⟩,
  ⟨(370, 805), 13, (498, 935), false⟩,
  ⟨(372, 1069), 12, (500, 166), false⟩,
  ⟨(375, 491), 8, (501, 1330), false⟩,
  ⟨(377, 1120), 5, (250, 589), true⟩,
  ⟨(379, 1248), 9, (254, 1359), true⟩,
  ⟨(380, 1158), 10, (249, 1007), true⟩,
  ⟨(382, 365), 6, (253, 93), true⟩,
  ⟨(394, 1260), 12, (340, 1328), true⟩,
  ⟨(395, 711), 11, (342, 125), true⟩,
  ⟨(396, 96), 5, (337, 433), true⟩,
  ⟨(397, 442), 6, (339, 743), true⟩,
  ⟨(401, 915), 10, (354, 1294), true⟩,
  ⟨(403, 1145), 9, (358, 1010), true⟩,
  ⟨(405, 947), 14, (355, 917), true⟩,
  ⟨(407, 821), 13, (359, 704), true⟩,
  ⟨(409, 122), 12, (395, 711), false⟩,
  ⟨(410, 1181), 13, (394, 1260), false⟩,
  ⟨(412, 379), 6, (396, 96), false⟩,
  ⟨(415, 987), 7, (397, 442), false⟩,
  ⟨(417, 1041), 11, (419, 162), false⟩,
  ⟨(419, 162), 10, (334, 1189), true⟩,
  ⟨(421, 616), 12, (423, 739), false⟩,
  ⟨(423, 739), 11, (335, 669), true⟩,
  ⟨(425, 663), 8, (443, 409), false⟩,
  ⟨(426, 1357), 9, (348, 551), true⟩,
  ⟨(428, 1317), 7, (444, 881), false⟩,
  ⟨(431, 1105), 8, (351, 633), true⟩,
  ⟨(442, 501), 10, (426, 1357), false⟩,
  ⟨(443, 409), 7, (382, 365), true⟩,
  ⟨(444, 881), 6, (377, 1120), true⟩,
  ⟨(445, 585), 9, (431, 1105), false⟩,
  ⟨(458, 1020), 11, (346, 460), false⟩,
  ⟨(459, 804), 10, (345, 978), false⟩,
  ⟨(460, 1093), 7, (465, 601), true⟩,
  ⟨(461, 769), 6, (467, 681), true⟩,
  ⟨(465, 601), 6, (339, 743), false⟩,
  ⟨(467, 681), 5, (337, 433), false⟩,
  ⟨(468, 504), 12, (340, 1328), false⟩,
  ⟨(470, 732), 11, (342, 125), false⟩,
  ⟨(473, 1302), 13, (498, 935), true⟩,
  ⟨(474, 1055), 12, (500, 166), true⟩,
  ⟨(477, 417), 9, (499, 372), true⟩,
  ⟨(478, 1273), 8, (501, 1330), true⟩,
  ⟨(481, 1132), 12, (458, 1020), true⟩,
  ⟨(482, 842), 8, (460, 1093), true⟩,
  ⟨(485, 121), 11, (459, 804), true⟩,
  ⟨(486, 480), 7, (461, 769), true⟩,
  ⟨(489, 1214), 10, (379, 1248), false⟩,
  ⟨(491, 540), 6, (377, 1120), false⟩,
  ⟨(492, 906), 11, (380, 1158), false⟩,
  ⟨(494, 94), 7, (382, 365), false⟩,
  ⟨(498, 935), 12, (492, 906), true⟩,
  ⟨(499, 372), 8, (494, 94), true⟩,
  ⟨(500, 166), 11, (489, 1214), true⟩,
  ⟨(501, 1330), 7, (491, 540), true⟩

]

@[expose] def smallLinearMemDepth (c : ℕ × ℕ) (d : ℕ) : List SmallLinearEntry → Bool
  | [] => false
  | e :: t => (Nat.beq e.code.1 c.1 && Nat.beq e.code.2 c.2 && Nat.ble e.depth d) ||
      smallLinearMemDepth c d t

@[expose] def smallLinearNotMem (x : ℕ) : List ℕ → Bool
  | [] => true
  | y :: t => !Nat.beq y x && smallLinearNotMem x t

@[expose] def smallLinearDistinct : List ℕ → Bool
  | [] => true
  | x :: t => smallLinearNotMem x t && smallLinearDistinct t

theorem smallLinearTable_closure : smallLinearTable.all (fun e =>
    smallLinearMemDepth (smallLinearMul false e.code) (e.depth + 1) smallLinearTable &&
      smallLinearMemDepth (smallLinearMul true e.code) (e.depth + 1) smallLinearTable) = true := by
  decide +kernel

theorem smallLinearTable_parent : smallLinearTable.all (fun e => Nat.beq e.depth 0 ||
    (Nat.beq (smallLinearMul e.gen e.parent).1 e.code.1 &&
      Nat.beq (smallLinearMul e.gen e.parent).2 e.code.2 &&
      smallLinearMemDepth e.parent (e.depth - 1) smallLinearTable)) = true := by
  decide +kernel

theorem smallLinearTable_distinct_fst :
    smallLinearDistinct (smallLinearTable.map fun e => e.code.1) = true := by
  decide +kernel

theorem smallLinearTable_distinct_snd :
    smallLinearDistinct (smallLinearTable.map fun e => e.code.2) = true := by
  decide +kernel

theorem smallLinearTable_depth : smallLinearTable.all (fun e =>
    Nat.ble e.depth 15 && (!Nat.beq e.depth 0 || (Nat.beq e.code.1 273 && Nat.beq e.code.2 344)))
    = true := by
  decide +kernel

theorem smallLinearTable_counts : (List.range 16).map (fun r =>
    (smallLinearTable.filter fun e => Nat.ble e.depth r).length) =
    [1, 3, 6, 10, 15, 22, 31, 43, 59, 76, 95, 115, 138, 160, 167, 168] := by
  decide +kernel

theorem smallLinearMemDepth_iff {c : ℕ × ℕ} {d : ℕ} {l : List SmallLinearEntry} :
    smallLinearMemDepth c d l = true ↔ ∃ e ∈ l, e.code = c ∧ e.depth ≤ d := by
  induction l with
  | nil => simp [smallLinearMemDepth]
  | cons e t ih =>
    simp only [smallLinearMemDepth, Bool.or_eq_true, Bool.and_eq_true, Nat.beq_eq, Nat.ble_eq, ih,
      List.mem_cons, exists_eq_or_imp]
    constructor
    · rintro (⟨⟨h1, h2⟩, h3⟩ | h)
      · exact Or.inl ⟨Prod.ext h1 h2, h3⟩
      · exact Or.inr h
    · rintro (⟨hc, hd⟩ | h)
      · exact Or.inl ⟨⟨by rw [hc], by rw [hc]⟩, hd⟩
      · exact Or.inr h

theorem smallLinearNotMem_iff {x : ℕ} {l : List ℕ} : smallLinearNotMem x l = true ↔ x ∉ l := by
  induction l with
  | nil => simp [smallLinearNotMem]
  | cons y t ih =>
    rw [smallLinearNotMem, Bool.and_eq_true, ih, List.mem_cons, not_or, Bool.not_eq_true',
      Bool.eq_false_iff, ne_eq, Nat.beq_eq]
    exact and_congr_left' ⟨fun h h' => h h'.symm, fun h h' => h h'.symm⟩

theorem nodup_of_smallLinearDistinct {l : List ℕ} (h : smallLinearDistinct l = true) :
    l.Nodup := by
  induction l with
  | nil => exact List.nodup_nil
  | cons x t ih =>
    simp only [smallLinearDistinct, Bool.and_eq_true] at h
    exact List.nodup_cons.mpr ⟨smallLinearNotMem_iff.mp h.1, ih h.2⟩

theorem smallLinearTable_nodup_fst : (smallLinearTable.map fun e => e.code.1).Nodup :=
  nodup_of_smallLinearDistinct smallLinearTable_distinct_fst

theorem smallLinearTable_nodup_snd : (smallLinearTable.map fun e => e.code.2).Nodup :=
  nodup_of_smallLinearDistinct smallLinearTable_distinct_snd

theorem smallLinearTable_nodup_code : (smallLinearTable.map fun e => e.code).Nodup :=
  List.Nodup.of_map Prod.fst (by rw [List.map_map]; exact smallLinearTable_nodup_fst)

@[expose] def smallLinearCodes (r : ℕ) : Set (ℕ × ℕ) :=
  {c | ∃ e ∈ smallLinearTable, e.code = c ∧ e.depth ≤ r}

theorem smallLinearCodes_mono {r s : ℕ} (h : r ≤ s) : smallLinearCodes r ⊆ smallLinearCodes s :=
  fun _ ⟨e, he, hc, hd⟩ => ⟨e, he, hc, hd.trans h⟩

theorem smallLinearCodes_zero : smallLinearCodes 0 = {(273, 344)} := by
  ext c
  simp only [smallLinearCodes, Set.mem_ofPred_eq, Set.mem_singleton_iff, Nat.le_zero]
  constructor
  · rintro ⟨e, he, rfl, hd⟩
    have h := List.all_eq_true.mp smallLinearTable_depth e he
    rw [hd] at h
    simp only [Bool.and_eq_true, Bool.or_eq_true, Nat.beq_eq] at h
    rcases h.2 with h' | h'
    · exact absurd h' (by decide)
    · exact Prod.ext h'.1 h'.2
  · rintro rfl
    have h : smallLinearMemDepth (273, 344) 0 smallLinearTable = true := by decide +kernel
    obtain ⟨e, he, hc, hd⟩ := smallLinearMemDepth_iff.mp h
    exact ⟨e, he, hc, Nat.le_zero.mp hd⟩

theorem smallLinearCodes_succ (r : ℕ) : smallLinearCodes (r + 1) = smallLinearCodes r ∪
    smallLinearMul false '' smallLinearCodes r ∪ smallLinearMul true '' smallLinearCodes r := by
  refine Set.Subset.antisymm ?_ ?_
  · rintro c ⟨e, he, rfl, hd⟩
    rcases Nat.lt_or_ge e.depth (r + 1) with h | h
    · exact Or.inl (Or.inl ⟨e, he, rfl, by omega⟩)
    have hp := List.all_eq_true.mp smallLinearTable_parent e he
    simp only [Bool.or_eq_true, Bool.and_eq_true, Nat.beq_eq] at hp
    rcases hp with h0 | ⟨⟨h1, h2⟩, hmem⟩
    · omega
    obtain ⟨e', he', hc', hd'⟩ := smallLinearMemDepth_iff.mp hmem
    have hpar : e.parent ∈ smallLinearCodes r := ⟨e', he', hc', by omega⟩
    have hcode : smallLinearMul e.gen e.parent = e.code := Prod.ext h1 h2
    cases hg : e.gen
    · rw [hg] at hcode
      exact Or.inl (Or.inr ⟨e.parent, hpar, hcode⟩)
    · rw [hg] at hcode
      exact Or.inr ⟨e.parent, hpar, hcode⟩
  · have hcl : ∀ (b : Bool) (e : SmallLinearEntry), e ∈ smallLinearTable → e.depth ≤ r →
        smallLinearMul b e.code ∈ smallLinearCodes (r + 1) := by
      intro b e he hd
      have h := List.all_eq_true.mp smallLinearTable_closure e he
      simp only [Bool.and_eq_true] at h
      have hm : smallLinearMemDepth (smallLinearMul b e.code) (e.depth + 1)
          smallLinearTable = true := by
        cases b
        · exact h.1
        · exact h.2
      obtain ⟨e', he', hc', hd'⟩ := smallLinearMemDepth_iff.mp hm
      exact ⟨e', he', hc', by omega⟩
    rintro c ((hc | ⟨c', ⟨e, he, rfl, hd⟩, rfl⟩) | ⟨c', ⟨e, he, rfl, hd⟩, rfl⟩)
    · exact smallLinearCodes_mono (Nat.le_succ r) hc
    · exact hcl false e he hd
    · exact hcl true e he hd

theorem smallLinearCodes_of_le {r : ℕ} (hr : 15 ≤ r) : smallLinearCodes r = smallLinearCodes 15 :=
  Set.Subset.antisymm (fun _ ⟨e, he, hc, _⟩ => ⟨e, he, hc, by
    have h := List.all_eq_true.mp smallLinearTable_depth e he
    simp only [Bool.and_eq_true, Nat.ble_eq] at h
    exact h.1⟩) (smallLinearCodes_mono hr)

theorem ncard_smallLinearCodes (r : ℕ) : (smallLinearCodes r).ncard =
    (smallLinearTable.filter fun e => Nat.ble e.depth r).length := by
  have hnd : ((smallLinearTable.filter fun e => Nat.ble e.depth r).map fun e => e.code).Nodup :=
    smallLinearTable_nodup_code.sublist ((List.filter_sublist).map _)
  have hset : smallLinearCodes r =
      ↑((smallLinearTable.filter fun e => Nat.ble e.depth r).map fun e => e.code).toFinset := by
    ext c
    simp only [smallLinearCodes, Set.mem_ofPred_eq, Finset.mem_coe, List.mem_toFinset,
      List.mem_map, List.mem_filter, Nat.ble_eq]
    exact ⟨fun ⟨e, he, hc, hd⟩ => ⟨e, ⟨he, hd⟩, hc⟩, fun ⟨e, ⟨he, hd⟩, hc⟩ => ⟨e, he, hc, hd⟩⟩
  rw [hset, Set.ncard_coe_finset, List.toFinset_card_of_nodup hnd, List.length_map]

theorem smallLinearEncH_digits {n d0 d1 d2 d3 d4 d5 d6 d7 d8 : ℕ}
    (hn : n = smallLinearEncH d0 d1 d2 d3 d4 d5 d6 d7 d8) (h0 : d0 < 2) (h1 : d1 < 2)
    (h2 : d2 < 2) (h3 : d3 < 2) (h4 : d4 < 2) (h5 : d5 < 2) (h6 : d6 < 2) (h7 : d7 < 2)
    (h8 : d8 < 2) :
    n % 2 = d0 ∧ n / 2 % 2 = d1 ∧ n / 4 % 2 = d2 ∧ n / 8 % 2 = d3 ∧ n / 16 % 2 = d4 ∧
      n / 32 % 2 = d5 ∧ n / 64 % 2 = d6 ∧ n / 128 % 2 = d7 ∧ n / 256 % 2 = d8 := by
  subst hn
  unfold smallLinearEncH
  refine ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega,
    by omega⟩

theorem smallLinearEnc7_digits {n p q r s : ℕ} (hn : n = smallLinearEnc7 p q r s) (hp : p < 7)
    (hq : q < 7) (hr : r < 7) (hs : s < 7) :
    n % 7 = p ∧ n / 7 % 7 = q ∧ n / 49 % 7 = r ∧ n / 343 % 7 = s := by
  subst hn
  unfold smallLinearEnc7
  refine ⟨by omega, by omega, by omega, by omega⟩

theorem smallLinearNeg7_lt (x : ℕ) : smallLinearNeg7 x < 7 :=
  Nat.mod_lt _ (by norm_num)

theorem smallLinearNeg7_neg7 {x : ℕ} (hx : x < 7) : smallLinearNeg7 (smallLinearNeg7 x) = x := by
  unfold smallLinearNeg7
  omega

theorem smallLinearNorm7_neg {w x y z : ℕ} (hw : w < 7) (hx : x < 7) (hy : y < 7) (hz : z < 7) :
    smallLinearNorm7 (smallLinearNeg7 w) (smallLinearNeg7 x) (smallLinearNeg7 y)
      (smallLinearNeg7 z) = smallLinearNorm7 w x y z := by
  rw [smallLinearNorm7, smallLinearNorm7, smallLinearNeg7_neg7 hw, smallLinearNeg7_neg7 hx,
    smallLinearNeg7_neg7 hy, smallLinearNeg7_neg7 hz, min_comm]

theorem smallLinearMulAG_norm7 {p q r s : ℕ} (hp : p < 7) (hq : q < 7) (hr : r < 7)
    (hs : s < 7) : smallLinearMulAG (smallLinearNorm7 p q r s) =
      smallLinearNorm7 q (smallLinearNeg7 p) s (smallLinearNeg7 r) := by
  rcases min_choice (smallLinearEnc7 p q r s) (smallLinearEnc7 (smallLinearNeg7 p)
    (smallLinearNeg7 q) (smallLinearNeg7 r) (smallLinearNeg7 s)) with h | h <;>
    rw [smallLinearNorm7, h]
  · obtain ⟨h0, h1, h2, h3⟩ := smallLinearEnc7_digits rfl hp hq hr hs
    rw [smallLinearMulAG, h0, h1, h2, h3]
  · obtain ⟨h0, h1, h2, h3⟩ := smallLinearEnc7_digits rfl (smallLinearNeg7_lt p)
      (smallLinearNeg7_lt q) (smallLinearNeg7_lt r) (smallLinearNeg7_lt s)
    rw [smallLinearMulAG, h0, h1, h2, h3]
    exact smallLinearNorm7_neg hq (smallLinearNeg7_lt p) hs (smallLinearNeg7_lt r)

theorem smallLinearMulBG_norm7 {p q r s : ℕ} (hp : p < 7) (hq : q < 7) (hr : r < 7)
    (hs : s < 7) : smallLinearMulBG (smallLinearNorm7 p q r s) =
      smallLinearNorm7 q ((smallLinearNeg7 p + q) % 7) s ((smallLinearNeg7 r + s) % 7) := by
  rcases min_choice (smallLinearEnc7 p q r s) (smallLinearEnc7 (smallLinearNeg7 p)
    (smallLinearNeg7 q) (smallLinearNeg7 r) (smallLinearNeg7 s)) with h | h <;>
    rw [smallLinearNorm7, h]
  · obtain ⟨h0, h1, h2, h3⟩ := smallLinearEnc7_digits rfl hp hq hr hs
    rw [smallLinearMulBG, h0, h1, h2, h3]
  · obtain ⟨h0, h1, h2, h3⟩ := smallLinearEnc7_digits rfl (smallLinearNeg7_lt p)
      (smallLinearNeg7_lt q) (smallLinearNeg7_lt r) (smallLinearNeg7_lt s)
    rw [smallLinearMulBG, h0, h1, h2, h3, ← smallLinearNorm7_neg hq (Nat.mod_lt _ (by norm_num))
      hs (Nat.mod_lt _ (by norm_num))]
    have key : ∀ x y : ℕ, x < 7 → y < 7 → (smallLinearNeg7 (smallLinearNeg7 x) +
        smallLinearNeg7 y) % 7 = smallLinearNeg7 ((smallLinearNeg7 x + y) % 7) := by
      intro x y hx hy
      unfold smallLinearNeg7
      omega
    rw [key p q hp hq, key r s hr hs]

@[expose] def smallLinearA : GL (Fin 3) (ZMod 2) :=
  ⟨!![1, 1, 0; 0, 1, 0; 0, 0, 1], !![1, 1, 0; 0, 1, 0; 0, 0, 1], by decide, by decide⟩

@[expose] def smallLinearB : GL (Fin 3) (ZMod 2) :=
  ⟨!![0, 0, 1; 1, 0, 0; 0, 1, 0], !![0, 1, 0; 0, 0, 1; 1, 0, 0], by decide, by decide⟩

@[expose] def smallLinearSLa : SpecialLinearGroup (Fin 2) (ZMod 7) :=
  ⟨!![0, -1; 1, 0], by decide⟩

@[expose] def smallLinearSLb : SpecialLinearGroup (Fin 2) (ZMod 7) :=
  ⟨!![0, -1; 1, 1], by decide⟩

@[expose] def smallLinearGenA :
    GL (Fin 3) (ZMod 2) × ProjectiveSpecialLinearGroup (Fin 2) (ZMod 7) :=
  (smallLinearA, QuotientGroup.mk smallLinearSLa)

@[expose] def smallLinearGenB :
    GL (Fin 3) (ZMod 2) × ProjectiveSpecialLinearGroup (Fin 2) (ZMod 7) :=
  (smallLinearB, QuotientGroup.mk smallLinearSLb)

@[expose] def smallLinearBFS :
    ℕ → Set (GL (Fin 3) (ZMod 2) × ProjectiveSpecialLinearGroup (Fin 2) (ZMod 7))
  | 0 => {1}
  | r + 1 => smallLinearBFS r ∪ (fun x => x * smallLinearGenA) '' smallLinearBFS r ∪
      (fun x => x * smallLinearGenB) '' smallLinearBFS r

theorem smallLinear_center_eq : (Subgroup.center (SpecialLinearGroup (Fin 2) (ZMod 7)) :
    Set (SpecialLinearGroup (Fin 2) (ZMod 7))) = {1, -1} := by
  ext A
  rw [SetLike.mem_coe, SpecialLinearGroup.mem_center_iff, Set.mem_insert_iff,
    Set.mem_singleton_iff, Fintype.card_fin]
  constructor
  · rintro ⟨r, hr, hA⟩
    have h : ∀ r : ZMod 7, r ^ 2 = 1 → r = 1 ∨ r = -1 := by decide
    rcases h r hr with rfl | rfl
    · left
      refine Subtype.ext ?_
      rw [← hA, SpecialLinearGroup.coe_one, map_one]
    · right
      refine Subtype.ext ?_
      rw [← hA, SpecialLinearGroup.coe_neg, SpecialLinearGroup.coe_one, map_neg, map_one]
  · rintro (rfl | rfl)
    · exact ⟨1, one_pow _, by rw [SpecialLinearGroup.coe_one, map_one]⟩
    · refine ⟨-1, by decide, ?_⟩
      rw [SpecialLinearGroup.coe_neg, SpecialLinearGroup.coe_one, map_neg, map_one]

@[expose] def smallLinearCodeH (M : Matrix (Fin 3) (Fin 3) (ZMod 2)) : ℕ :=
  smallLinearEncH (M 0 0).val (M 0 1).val (M 0 2).val (M 1 0).val (M 1 1).val (M 1 2).val
    (M 2 0).val (M 2 1).val (M 2 2).val

@[expose] def smallLinearCode7 (M : Matrix (Fin 2) (Fin 2) (ZMod 7)) : ℕ :=
  smallLinearEnc7 (M 0 0).val (M 0 1).val (M 1 0).val (M 1 1).val

@[expose] def smallLinearCodeSL (M : SpecialLinearGroup (Fin 2) (ZMod 7)) : ℕ :=
  smallLinearNorm7 ((M : Matrix (Fin 2) (Fin 2) (ZMod 7)) 0 0).val
    ((M : Matrix (Fin 2) (Fin 2) (ZMod 7)) 0 1).val ((M : Matrix (Fin 2) (Fin 2) (ZMod 7)) 1 0).val
    ((M : Matrix (Fin 2) (Fin 2) (ZMod 7)) 1 1).val

theorem smallLinearCodeSL_eq (M : SpecialLinearGroup (Fin 2) (ZMod 7)) :
    smallLinearCodeSL M = min (smallLinearCode7 M) (smallLinearCode7 (-M)) := by
  simp only [smallLinearCodeSL, smallLinearNorm7, smallLinearCode7, Matrix.neg_apply,
    ZMod.neg_val', smallLinearNeg7]

theorem smallLinearCodeSL_neg (M : SpecialLinearGroup (Fin 2) (ZMod 7)) :
    smallLinearCodeSL (-M) = smallLinearCodeSL M := by
  rw [smallLinearCodeSL_eq, smallLinearCodeSL_eq, SpecialLinearGroup.coe_neg, neg_neg, min_comm]

theorem smallLinear_neg_one_mem_center :
    (-1 : SpecialLinearGroup (Fin 2) (ZMod 7)) ∈ Subgroup.center _ := by
  rw [← SetLike.mem_coe, smallLinear_center_eq]
  exact Or.inr rfl

theorem smallLinearCodeSL_eq_of_mem_center {M M' : SpecialLinearGroup (Fin 2) (ZMod 7)}
    (h : M⁻¹ * M' ∈ Subgroup.center _) : smallLinearCodeSL M = smallLinearCodeSL M' := by
  rw [← SetLike.mem_coe, smallLinear_center_eq] at h
  rcases h with h | h
  · rw [inv_mul_eq_one.mp h]
  · rw [eq_mul_of_inv_mul_eq h, mul_neg_one, smallLinearCodeSL_neg]

@[expose] def smallLinearCodeG (γ : ProjectiveSpecialLinearGroup (Fin 2) (ZMod 7)) : ℕ :=
  Quotient.lift smallLinearCodeSL
    (fun _ _ h => smallLinearCodeSL_eq_of_mem_center (QuotientGroup.leftRel_apply.mp h)) γ

theorem smallLinearCodeG_mk (M : SpecialLinearGroup (Fin 2) (ZMod 7)) :
    smallLinearCodeG (QuotientGroup.mk M) = smallLinearCodeSL M :=
  rfl

@[expose] def smallLinearCode
    (x : GL (Fin 3) (ZMod 2) × ProjectiveSpecialLinearGroup (Fin 2) (ZMod 7)) : ℕ × ℕ :=
  (smallLinearCodeH x.1, smallLinearCodeG x.2)

theorem smallLinearCode_one : smallLinearCode 1 = (273, 344) := by
  rw [smallLinearCode, Prod.fst_one, Prod.snd_one, ← QuotientGroup.mk_one, smallLinearCodeG_mk]
  decide

theorem smallLinearCodeH_mul_A (M : Matrix (Fin 3) (Fin 3) (ZMod 2)) :
    smallLinearCodeH (M * (smallLinearA : Matrix (Fin 3) (Fin 3) (ZMod 2))) =
      smallLinearMulAH (smallLinearCodeH M) := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩ := smallLinearEncH_digits
    (n := smallLinearCodeH M) rfl (M 0 0).val_lt (M 0 1).val_lt (M 0 2).val_lt (M 1 0).val_lt
    (M 1 1).val_lt (M 1 2).val_lt (M 2 0).val_lt (M 2 1).val_lt (M 2 2).val_lt
  rw [smallLinearMulAH, h0, h1, h2, h3, h4, h5, h6, h7, h8]
  simp [smallLinearCodeH, smallLinearA, Matrix.mul_apply, Fin.sum_univ_three, ZMod.val_add]

theorem smallLinearCodeH_mul_B (M : Matrix (Fin 3) (Fin 3) (ZMod 2)) :
    smallLinearCodeH (M * (smallLinearB : Matrix (Fin 3) (Fin 3) (ZMod 2))) =
      smallLinearMulBH (smallLinearCodeH M) := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩ := smallLinearEncH_digits
    (n := smallLinearCodeH M) rfl (M 0 0).val_lt (M 0 1).val_lt (M 0 2).val_lt (M 1 0).val_lt
    (M 1 1).val_lt (M 1 2).val_lt (M 2 0).val_lt (M 2 1).val_lt (M 2 2).val_lt
  rw [smallLinearMulBH, h0, h1, h2, h3, h4, h5, h6, h7, h8]
  simp [smallLinearCodeH, smallLinearB, Matrix.mul_apply, Fin.sum_univ_three]

theorem smallLinearSL_mul_apply (M N : SpecialLinearGroup (Fin 2) (ZMod 7)) (i j : Fin 2) :
    ((M * N : SpecialLinearGroup (Fin 2) (ZMod 7)) : Matrix (Fin 2) (Fin 2) (ZMod 7)) i j =
      ∑ k, (M : Matrix (Fin 2) (Fin 2) (ZMod 7)) i k * (N : Matrix (Fin 2) (Fin 2) (ZMod 7)) k j :=
  rfl

theorem smallLinearCodeG_mul_a (γ : ProjectiveSpecialLinearGroup (Fin 2) (ZMod 7)) :
    smallLinearCodeG (γ * QuotientGroup.mk smallLinearSLa) =
      smallLinearMulAG (smallLinearCodeG γ) := by
  obtain ⟨M, rfl⟩ := QuotientGroup.mk_surjective γ
  rw [← QuotientGroup.mk_mul]
  change smallLinearCodeSL (M * smallLinearSLa) = smallLinearMulAG (smallLinearCodeSL M)
  rw [smallLinearCodeSL, smallLinearCodeSL, smallLinearMulAG_norm7 (ZMod.val_lt _)
    (ZMod.val_lt _) (ZMod.val_lt _) (ZMod.val_lt _)]
  simp only [smallLinearSL_mul_apply]
  simp [smallLinearSLa, Fin.sum_univ_two, ZMod.neg_val', smallLinearNeg7]

theorem smallLinearCodeG_mul_b (γ : ProjectiveSpecialLinearGroup (Fin 2) (ZMod 7)) :
    smallLinearCodeG (γ * QuotientGroup.mk smallLinearSLb) =
      smallLinearMulBG (smallLinearCodeG γ) := by
  obtain ⟨M, rfl⟩ := QuotientGroup.mk_surjective γ
  rw [← QuotientGroup.mk_mul]
  change smallLinearCodeSL (M * smallLinearSLb) = smallLinearMulBG (smallLinearCodeSL M)
  rw [smallLinearCodeSL, smallLinearCodeSL, smallLinearMulBG_norm7 (ZMod.val_lt _)
    (ZMod.val_lt _) (ZMod.val_lt _) (ZMod.val_lt _)]
  simp only [smallLinearSL_mul_apply]
  simp [smallLinearSLb, Fin.sum_univ_two, ZMod.neg_val', smallLinearNeg7, ZMod.val_add]

theorem smallLinearCode_mul_genA
    (x : GL (Fin 3) (ZMod 2) × ProjectiveSpecialLinearGroup (Fin 2) (ZMod 7)) :
    smallLinearCode (x * smallLinearGenA) = smallLinearMul false (smallLinearCode x) := by
  rw [smallLinearCode, smallLinearCode, smallLinearMul, smallLinearGenA, Prod.fst_mul,
    Prod.snd_mul, Units.val_mul, smallLinearCodeH_mul_A, smallLinearCodeG_mul_a]

theorem smallLinearCode_mul_genB
    (x : GL (Fin 3) (ZMod 2) × ProjectiveSpecialLinearGroup (Fin 2) (ZMod 7)) :
    smallLinearCode (x * smallLinearGenB) = smallLinearMul true (smallLinearCode x) := by
  rw [smallLinearCode, smallLinearCode, smallLinearMul, smallLinearGenB, Prod.fst_mul,
    Prod.snd_mul, Units.val_mul, smallLinearCodeH_mul_B, smallLinearCodeG_mul_b]

theorem smallLinearCodeH_injective : Function.Injective smallLinearCodeH := by
  intro M M' h
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8⟩ := smallLinearEncH_digits
    (n := smallLinearCodeH M) rfl (M 0 0).val_lt (M 0 1).val_lt (M 0 2).val_lt (M 1 0).val_lt
    (M 1 1).val_lt (M 1 2).val_lt (M 2 0).val_lt (M 2 1).val_lt (M 2 2).val_lt
  obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7, b8⟩ := smallLinearEncH_digits
    (n := smallLinearCodeH M') rfl (M' 0 0).val_lt (M' 0 1).val_lt (M' 0 2).val_lt
    (M' 1 0).val_lt (M' 1 1).val_lt (M' 1 2).val_lt (M' 2 0).val_lt (M' 2 1).val_lt
    (M' 2 2).val_lt
  rw [h] at a0 a1 a2 a3 a4 a5 a6 a7 a8
  ext i j
  fin_cases i <;> fin_cases j
  · exact ZMod.val_injective _ (a0.symm.trans b0)
  · exact ZMod.val_injective _ (a1.symm.trans b1)
  · exact ZMod.val_injective _ (a2.symm.trans b2)
  · exact ZMod.val_injective _ (a3.symm.trans b3)
  · exact ZMod.val_injective _ (a4.symm.trans b4)
  · exact ZMod.val_injective _ (a5.symm.trans b5)
  · exact ZMod.val_injective _ (a6.symm.trans b6)
  · exact ZMod.val_injective _ (a7.symm.trans b7)
  · exact ZMod.val_injective _ (a8.symm.trans b8)

theorem smallLinearCode7_injective : Function.Injective smallLinearCode7 := by
  intro M M' h
  obtain ⟨a0, a1, a2, a3⟩ := smallLinearEnc7_digits (n := smallLinearCode7 M) rfl
    (M 0 0).val_lt (M 0 1).val_lt (M 1 0).val_lt (M 1 1).val_lt
  obtain ⟨b0, b1, b2, b3⟩ := smallLinearEnc7_digits (n := smallLinearCode7 M') rfl
    (M' 0 0).val_lt (M' 0 1).val_lt (M' 1 0).val_lt (M' 1 1).val_lt
  rw [h] at a0 a1 a2 a3
  ext i j
  fin_cases i <;> fin_cases j
  · exact ZMod.val_injective _ (a0.symm.trans b0)
  · exact ZMod.val_injective _ (a1.symm.trans b1)
  · exact ZMod.val_injective _ (a2.symm.trans b2)
  · exact ZMod.val_injective _ (a3.symm.trans b3)

theorem smallLinearCodeG_injective : Function.Injective smallLinearCodeG := by
  intro γ γ' h
  obtain ⟨M, rfl⟩ := QuotientGroup.mk_surjective γ
  obtain ⟨M', rfl⟩ := QuotientGroup.mk_surjective γ'
  rw [smallLinearCodeG_mk, smallLinearCodeG_mk, smallLinearCodeSL_eq,
    smallLinearCodeSL_eq] at h
  have key : M = M' ∨ M = -M' := by
    rcases min_choice (smallLinearCode7 M) (smallLinearCode7 (-M)) with h1 | h1 <;>
      rcases min_choice (smallLinearCode7 M') (smallLinearCode7 (-M')) with h2 | h2 <;>
      rw [h1, h2] at h
    · exact Or.inl (Subtype.ext (smallLinearCode7_injective h))
    · refine Or.inr (Subtype.ext ?_)
      rw [smallLinearCode7_injective h, SpecialLinearGroup.coe_neg]
    · refine Or.inr (Subtype.ext ?_)
      rw [SpecialLinearGroup.coe_neg, ← smallLinearCode7_injective h, neg_neg]
    · exact Or.inl (Subtype.ext (neg_injective (smallLinearCode7_injective h)))
  rw [QuotientGroup.eq]
  rcases key with rfl | rfl
  · rw [inv_mul_cancel]
    exact Subgroup.one_mem _
  · rw [← mul_neg_one M', _root_.mul_inv_rev, mul_assoc, inv_mul_cancel, mul_one]
    exact Subgroup.inv_mem _ smallLinear_neg_one_mem_center

theorem smallLinearCode_injective : Function.Injective smallLinearCode := fun _ _ h =>
  Prod.ext (Units.ext (smallLinearCodeH_injective (congrArg Prod.fst h)))
    (smallLinearCodeG_injective (congrArg Prod.snd h))

theorem smallLinearCode_image_BFS (r : ℕ) :
    smallLinearCode '' smallLinearBFS r = smallLinearCodes r := by
  induction r with
  | zero => rw [smallLinearBFS, Set.image_singleton, smallLinearCode_one, smallLinearCodes_zero]
  | succ r ih =>
    rw [smallLinearBFS, Set.image_union, Set.image_union, Set.image_image, Set.image_image,
      smallLinearCodes_succ, ← ih]
    simp only [smallLinearCode_mul_genA, smallLinearCode_mul_genB]
    rw [← Set.image_image (smallLinearMul false), ← Set.image_image (smallLinearMul true)]

theorem ncard_smallLinearBFS (r : ℕ) : (smallLinearBFS r).ncard =
    (smallLinearTable.filter fun e => Nat.ble e.depth r).length := by
  rw [← Set.ncard_image_of_injective _ smallLinearCode_injective, smallLinearCode_image_BFS,
    ncard_smallLinearCodes]

theorem smallLinearBFS_sixteen : smallLinearBFS 16 = smallLinearBFS 15 :=
  Set.image_injective.mpr smallLinearCode_injective (by
    rw [smallLinearCode_image_BFS, smallLinearCode_image_BFS, smallLinearCodes_of_le (by norm_num)])

theorem smallLinearBFS_subset_succ (r : ℕ) : smallLinearBFS r ⊆ smallLinearBFS (r + 1) :=
  fun _ hx => Or.inl (Or.inl hx)

theorem smallLinearBFS_mono {r s : ℕ} (h : r ≤ s) : smallLinearBFS r ⊆ smallLinearBFS s := by
  induction s, h using Nat.le_induction with
  | base => exact le_rfl
  | succ s _ ih => exact ih.trans (smallLinearBFS_subset_succ s)

theorem smallLinearGenA_mul_self : smallLinearGenA * smallLinearGenA = 1 := by
  refine Prod.ext (Units.ext (by decide)) ?_
  change QuotientGroup.mk smallLinearSLa * QuotientGroup.mk smallLinearSLa = (1 :
    ProjectiveSpecialLinearGroup (Fin 2) (ZMod 7))
  rw [← QuotientGroup.mk_mul, QuotientGroup.eq_one_iff]
  convert smallLinear_neg_one_mem_center using 1
  exact Subtype.ext (by decide)

theorem smallLinearGenB_mul_self_mul_self :
    smallLinearGenB * (smallLinearGenB * smallLinearGenB) = 1 := by
  refine Prod.ext (Units.ext (by decide)) ?_
  change QuotientGroup.mk smallLinearSLb * (QuotientGroup.mk smallLinearSLb *
    QuotientGroup.mk smallLinearSLb) = (1 : ProjectiveSpecialLinearGroup (Fin 2) (ZMod 7))
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq_one_iff]
  convert smallLinear_neg_one_mem_center using 1
  exact Subtype.ext (by decide)

theorem smallLinearBFS_subset_closure (r : ℕ) : smallLinearBFS r ⊆
    (Subgroup.closure {smallLinearGenA, smallLinearGenB} : Set _) := by
  induction r with
  | zero =>
    rw [smallLinearBFS, Set.singleton_subset_iff]
    exact Subgroup.one_mem _
  | succ r ih =>
    rintro x ((hx | ⟨y, hy, rfl⟩) | ⟨y, hy, rfl⟩)
    · exact ih hx
    · exact Subgroup.mul_mem _ (ih hy) (Subgroup.subset_closure (Set.mem_insert _ _))
    · exact Subgroup.mul_mem _ (ih hy)
        (Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl))

theorem smallLinearBFS_fifteen : smallLinearBFS 15 =
    (Subgroup.closure {smallLinearGenA, smallLinearGenB} : Set _) := by
  refine Set.Subset.antisymm (smallLinearBFS_subset_closure 15) fun x hx => ?_
  have hmul : ∀ y ∈ smallLinearBFS 15, ∀ g ∈ ({smallLinearGenA, smallLinearGenB} : Set _),
      y * g ∈ smallLinearBFS 15 := by
    rintro y hy g (rfl | rfl)
    · rw [← smallLinearBFS_sixteen]
      exact Or.inl (Or.inr ⟨y, hy, rfl⟩)
    · rw [← smallLinearBFS_sixteen]
      exact Or.inr ⟨y, hy, rfl⟩
  refine Subgroup.closure_induction_right (p := fun x _ => x ∈ smallLinearBFS 15)
    (smallLinearBFS_mono (Nat.zero_le 15) rfl) (fun y _ g hg hy => hmul y hy g hg)
    (fun y _ g hg hy => ?_) (SetLike.mem_coe.mp hx)
  rcases hg with rfl | rfl
  · rw [inv_eq_of_mul_eq_one_right smallLinearGenA_mul_self]
    exact hmul y hy _ (Set.mem_insert _ _)
  · rw [inv_eq_of_mul_eq_one_right smallLinearGenB_mul_self_mul_self, ← mul_assoc]
    exact hmul _ (hmul y hy _ (Set.mem_insert_of_mem _ rfl)) _ (Set.mem_insert_of_mem _ rfl)

theorem smallLinear_natCard_eq_ncard {G : Type*} [Group G] (K : Subgroup G) :
    Nat.card K = (K : Set G).ncard :=
  Nat.card_coe_set_eq (K : Set G)

theorem smallLinearCode_mem_codes {x : GL (Fin 3) (ZMod 2) ×
    ProjectiveSpecialLinearGroup (Fin 2) (ZMod 7)} (hx : x ∈ smallLinearBFS 15) :
    smallLinearCode x ∈ smallLinearCodes 15 :=
  smallLinearCode_image_BFS 15 ▸ Set.mem_image_of_mem _ hx

theorem smallLinearBFS_injOn_fst : Set.InjOn Prod.fst (smallLinearBFS 15) := by
  intro x hx y hy hxy
  obtain ⟨e, he, hec, -⟩ := smallLinearCode_mem_codes hx
  obtain ⟨e', he', hec', -⟩ := smallLinearCode_mem_codes hy
  have h1 : e.code.1 = e'.code.1 := by
    rw [hec, hec']
    exact congrArg (fun h : GL (Fin 3) (ZMod 2) => smallLinearCodeH h) hxy
  have hee : e = e' := List.inj_on_of_nodup_map smallLinearTable_nodup_fst he he' h1
  exact smallLinearCode_injective (by rw [← hec, ← hec', hee])

theorem smallLinearBFS_injOn_snd : Set.InjOn Prod.snd (smallLinearBFS 15) := by
  intro x hx y hy hxy
  obtain ⟨e, he, hec, -⟩ := smallLinearCode_mem_codes hx
  obtain ⟨e', he', hec', -⟩ := smallLinearCode_mem_codes hy
  have h2 : e.code.2 = e'.code.2 := by
    rw [hec, hec']
    exact congrArg smallLinearCodeG hxy
  have hee : e = e' := List.inj_on_of_nodup_map smallLinearTable_nodup_snd he he' h2
  exact smallLinearCode_injective (by rw [← hec, ← hec', hee])

theorem small_linear_paired_generator_certificate :
    (Subgroup.center (SpecialLinearGroup (Fin 2) (ZMod 7)) :
        Set (SpecialLinearGroup (Fin 2) (ZMod 7))) = {1, -1} ∧
    Nat.card (Subgroup.closure {smallLinearGenA, smallLinearGenB}) = 168 ∧
    Nat.card ((Subgroup.closure {smallLinearGenA, smallLinearGenB}).map
      (MonoidHom.fst (GL (Fin 3) (ZMod 2)) (ProjectiveSpecialLinearGroup (Fin 2) (ZMod 7)))) =
      168 ∧
    Nat.card ((Subgroup.closure {smallLinearGenA, smallLinearGenB}).map
      (MonoidHom.snd (GL (Fin 3) (ZMod 2)) (ProjectiveSpecialLinearGroup (Fin 2) (ZMod 7)))) =
      168 ∧
    (List.range 16).map (fun r => (smallLinearBFS r).ncard) =
      [1, 3, 6, 10, 15, 22, 31, 43, 59, 76, 95, 115, 138, 160, 167, 168] ∧
    smallLinearBFS 16 = smallLinearBFS 15 ∧
    smallLinearBFS 15 = (Subgroup.closure {smallLinearGenA, smallLinearGenB} : Set _) := by
  have h15 : (smallLinearBFS 15).ncard = 168 := by
    rw [ncard_smallLinearBFS]
    decide +kernel
  refine ⟨smallLinear_center_eq, ?_, ?_, ?_, ?_, smallLinearBFS_sixteen, smallLinearBFS_fifteen⟩
  · rw [smallLinear_natCard_eq_ncard, ← smallLinearBFS_fifteen, h15]
  · rw [smallLinear_natCard_eq_ncard, Subgroup.coe_map, ← smallLinearBFS_fifteen, MonoidHom.coe_fst,
      smallLinearBFS_injOn_fst.ncard_image, h15]
  · rw [smallLinear_natCard_eq_ncard, Subgroup.coe_map, ← smallLinearBFS_fifteen,
      MonoidHom.coe_snd,
      smallLinearBFS_injOn_snd.ncard_image, h15]
  · rw [List.map_congr_left fun r _ => ncard_smallLinearBFS r]
    exact smallLinearTable_counts

end CFSG.LocalAnalysis.ComponentInitial
