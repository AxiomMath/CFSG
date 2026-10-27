module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81EightThirteenKnownOrthTools
public import CFSG.RankThree.PartTwo.Sec4.RonanK432RowSp82
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81EightThirteenKnownCore

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.OrthPlanes

open CFSG.Quasithin.SteinbergCB.G2Two CFSG.Open Matrix
open CFSG.StandardType.SpEight (Idx Vec tvGL tvGL_mem_statedSp)
open CFSG.RankThree.PartTwo.Sec4.RonanK432 (H8 sp8Z sp8T mk8 sm8 wreathFacts_sp8)
open CFSG.RankThree.PartTwo.Sec4.Item434Kit (baseA card_baseA isElemAbelian_baseA
  isElemAbelian_sup_zpowers sup_zpowers_le_baseA)

namespace Symp

private abbrev eS : Idx ≃ Fin (4 + 4) := finSumFinEquiv

private def tvS (c : ℕ) : H8 := ⟨tvGL (pt eS c), tvGL_mem_statedSp _⟩

private def swapM : Matrix (Fin 8) (Fin 8) (ZMod 2) :=
  !![1, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 1, 0, 0, 0, 0, 0;
    0, 1, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 1, 0, 0, 0, 0;
    0, 0, 0, 0, 1, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 1, 0;
    0, 0, 0, 0, 0, 1, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 1]

private theorem swapM_check : sm8 swapM * sm8 swapM = 1 ∧ sm8 swapM * sm8 swapM = 1 ∧
    (sm8 swapM)ᵀ * Matrix.fromBlocks 0 1 (-1) 0 * sm8 swapM = Matrix.fromBlocks 0 1 (-1) 0 := by
  decide +kernel

private def swap12 : H8 := mk8 swapM swapM swapM_check

private abbrev X₁ : Subgroup H8 := Subgroup.zpowers (sp8Z 1) ⊔ Subgroup.zpowers (sp8Z 2)
private abbrev X₂ : Subgroup H8 := Subgroup.zpowers (sp8Z 0) ⊔ Subgroup.zpowers (sp8Z 1)

private def genS : List H8 :=
  [swap12, tvS 8, tvS 200, tvS 140, tvS 76, tvS 204, tvS 129, tvS 145]

private theorem swap12_conj : swap12 * sp8Z 1 * swap12⁻¹ = sp8Z 2 ∧
    swap12 * sp8Z 2 * swap12⁻¹ = sp8Z 1 := by
  decide +kernel

private theorem tvS_comm₁ : ∀ c ∈ [8, 129, 145], tvS c * sp8Z 1 = sp8Z 1 * tvS c ∧
    tvS c * sp8Z 2 = sp8Z 2 * tvS c := by
  decide +kernel

private theorem tvS_comm₂ : ∀ c ∈ [200, 140, 76, 204], tvS c * sp8Z 0 = sp8Z 0 * tvS c ∧
    tvS c * sp8Z 1 = sp8Z 1 * tvS c := by
  decide +kernel

private theorem mem_normalizer_of_comm {i j : Fin 3} {g : H8} (hi : g * sp8Z i = sp8Z i * g)
    (hj : g * sp8Z j = sp8Z j * g) :
    g ∈ Subgroup.normalizer
      ((Subgroup.zpowers (sp8Z i) ⊔ Subgroup.zpowers (sp8Z j) : Subgroup H8) : Set H8) := by
  refine mem_normalizer_sup_zpowers ?_ ?_
  · rw [hi, mul_inv_cancel_right]
    exact Subgroup.mem_sup_left (Subgroup.mem_zpowers _)
  · rw [hj, mul_inv_cancel_right]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers _)

private theorem swap12_mem : swap12 ∈ Subgroup.normalizer (X₁ : Set H8) := by
  refine mem_normalizer_sup_zpowers ?_ ?_
  · rw [swap12_conj.1]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
  · rw [swap12_conj.2]
    exact Subgroup.mem_sup_left (Subgroup.mem_zpowers _)

private theorem tvS_mem₁ {c : ℕ} (hc : c ∈ [8, 129, 145]) :
    tvS c ∈ Subgroup.normalizer (X₁ : Set H8) :=
  mem_normalizer_of_comm (tvS_comm₁ c hc).1 (tvS_comm₁ c hc).2

private theorem tvS_mem₂ {c : ℕ} (hc : c ∈ [200, 140, 76, 204]) :
    tvS c ∈ Subgroup.normalizer (X₂ : Set H8) :=
  mem_normalizer_of_comm (tvS_comm₂ c hc).1 (tvS_comm₂ c hc).2

private def gensS : List (List ℕ) :=
   [[1, 4, 2, 8, 16, 64, 32, 128], [1, 2, 4, 8, 16, 32, 64, 136], [1, 2, 204, 192, 16, 32, 64, 72],
    [1, 2, 4, 132, 16, 32, 204, 12], [1, 2, 72, 8, 16, 32, 12, 204],
    [1, 2, 200, 196, 16, 32, 140, 76], [1, 2, 4, 137, 145, 32, 64, 128],
    [144, 2, 4, 153, 129, 32, 64, 128]]

private def certS : List (ℕ × ℕ × ℕ) :=
   [(192, 2, 8), (132, 3, 8), (196, 5, 8), (137, 6, 8), (153, 7, 8), (160, 0, 192), (200, 1, 192),
    (130, 0, 132), (140, 1, 132), (162, 0, 196), (204, 1, 196), (136, 4, 196), (129, 1, 137),
    (197, 4, 137), (145, 1, 153), (213, 4, 153), (168, 1, 160), (104, 2, 160), (44, 3, 160),
    (236, 4, 160), (108, 5, 160), (68, 3, 200), (4, 5, 200), (73, 6, 200), (89, 7, 200),
    (138, 1, 130), (74, 2, 130), (14, 3, 130), (206, 4, 130), (78, 5, 130), (64, 5, 140),
    (13, 6, 140), (29, 7, 140), (170, 1, 162), (106, 2, 162), (46, 3, 162), (238, 4, 162),
    (110, 5, 162), (128, 4, 204), (77, 6, 204), (93, 7, 204), (9, 6, 136), (25, 7, 136),
    (205, 4, 129), (16, 7, 129), (163, 0, 197), (84, 7, 197), (221, 4, 145), (179, 0, 213),
    (228, 4, 168), (41, 6, 168), (57, 7, 168), (36, 4, 104), (233, 6, 104), (249, 7, 104),
    (96, 4, 44), (173, 6, 44), (189, 7, 44), (234, 0, 236), (109, 6, 236), (125, 7, 236),
    (237, 6, 108), (253, 7, 108), (34, 0, 68), (2, 0, 4), (72, 4, 4), (5, 4, 73), (21, 4, 89),
    (198, 4, 138), (11, 6, 138), (27, 7, 138), (6, 4, 74), (203, 6, 74), (219, 7, 74), (66, 4, 14),
    (143, 6, 14), (159, 7, 14), (174, 0, 206), (79, 6, 206), (95, 7, 206), (207, 6, 78),
    (223, 7, 78), (32, 0, 64), (12, 4, 64), (65, 4, 13), (81, 4, 29), (230, 4, 170), (43, 6, 170),
    (59, 7, 170), (38, 4, 106), (235, 6, 106), (251, 7, 106), (98, 4, 46), (175, 6, 46),
    (191, 7, 46), (111, 6, 238), (127, 7, 238), (239, 6, 110), (255, 7, 110), (76, 5, 128),
    (193, 2, 9), (133, 3, 9), (209, 2, 25), (149, 3, 25), (171, 0, 205), (107, 2, 163),
    (47, 3, 163), (50, 7, 163), (156, 2, 84), (216, 3, 84), (187, 0, 221), (123, 2, 179),
    (63, 3, 179), (226, 0, 228), (40, 5, 228), (225, 2, 41), (165, 3, 41), (229, 5, 41),
    (241, 2, 57), (181, 3, 57), (245, 5, 57), (232, 5, 36), (101, 3, 233), (37, 5, 233),
    (117, 3, 249), (53, 5, 249), (172, 5, 96), (97, 5, 173), (113, 5, 189), (102, 3, 234),
    (161, 5, 109), (177, 5, 125), (201, 6, 72), (217, 7, 72), (3, 0, 5), (148, 7, 5), (19, 0, 21),
    (166, 0, 198), (10, 5, 198), (195, 2, 11), (135, 3, 11), (199, 5, 11), (211, 2, 27),
    (151, 3, 27), (215, 5, 27), (202, 5, 6), (71, 3, 203), (7, 5, 203), (87, 3, 219), (23, 5, 219),
    (142, 5, 66), (67, 5, 143), (83, 5, 159), (131, 5, 79), (147, 5, 95), (141, 6, 12),
    (157, 7, 12), (33, 0, 65), (208, 7, 65), (49, 0, 81), (42, 5, 230), (227, 2, 43), (167, 3, 43),
    (231, 5, 43), (243, 2, 59), (183, 3, 59), (247, 5, 59), (70, 0, 38), (103, 3, 235),
    (39, 5, 235), (119, 3, 251), (55, 5, 251), (100, 0, 98), (99, 5, 175), (115, 5, 191),
    (80, 7, 193), (20, 7, 133), (154, 0, 156), (184, 0, 216), (224, 2, 40), (164, 3, 40),
    (169, 6, 40), (185, 7, 40), (112, 7, 225), (52, 7, 165), (116, 7, 229), (105, 6, 232),
    (121, 7, 232), (244, 7, 101), (180, 7, 37), (45, 6, 172), (61, 7, 172), (240, 7, 97),
    (48, 7, 161), (69, 3, 201), (85, 3, 217), (146, 7, 3), (24, 3, 148), (194, 2, 10), (134, 3, 10),
    (139, 6, 10), (155, 7, 10), (82, 7, 195), (22, 7, 135), (86, 7, 199), (75, 6, 202),
    (91, 7, 202), (214, 7, 71), (150, 7, 7), (15, 6, 142), (31, 7, 142), (210, 7, 67), (18, 7, 131),
    (176, 7, 33), (114, 7, 227), (54, 7, 167), (118, 7, 231), (246, 7, 103), (182, 7, 39),
    (242, 7, 99), (220, 3, 80), (28, 4, 80), (88, 4, 20), (252, 3, 112), (60, 4, 112),
    (188, 5, 112), (120, 4, 52), (248, 5, 52), (56, 5, 244), (35, 0, 69), (212, 7, 69), (51, 0, 85),
    (90, 2, 146), (30, 3, 146), (222, 4, 146), (94, 5, 146), (158, 5, 82), (218, 5, 22),
    (26, 5, 214), (124, 5, 176), (254, 3, 114), (62, 4, 114), (190, 5, 114), (122, 4, 54),
    (250, 5, 54), (186, 4, 246), (58, 5, 246), (144, 4, 220), (178, 7, 35), (152, 4, 212),
    (92, 0, 58), (17, 6, 144), (1, 7, 144), (126, 5, 178)]

private theorem genS_act : ∀ k < 8, ∀ x < 2 ^ (4 + 4),
    (((genS.getD k 1 : H8) : GL Idx (ZMod 2)) : Matrix Idx Idx (ZMod 2)) *ᵥ pt eS x =
      pt eS (mApp (gensS.getD k []) x) := by
  decide +kernel

private theorem certS_ok : certOK (4 + 4) gensS [8] certS = true := by
  decide +kernel

private theorem certS_cover : ∀ x < 2 ^ (4 + 4), pt eS x ≠ 0 → x = 8 ∨ x ∈ certS.map Prod.fst := by
  decide +kernel

private theorem genS_mem : ∀ k < 8, genS.getD k 1 ∈ Subgroup.normalizer (X₁ : Set H8) ⊔
    Subgroup.normalizer (X₂ : Set H8) := by
  intro k hk
  interval_cases k
  · exact Subgroup.mem_sup_left swap12_mem
  · exact Subgroup.mem_sup_left (tvS_mem₁ (by decide))
  · exact Subgroup.mem_sup_right (tvS_mem₂ (by decide))
  · exact Subgroup.mem_sup_right (tvS_mem₂ (by decide))
  · exact Subgroup.mem_sup_right (tvS_mem₂ (by decide))
  · exact Subgroup.mem_sup_right (tvS_mem₂ (by decide))
  · exact Subgroup.mem_sup_left (tvS_mem₁ (by decide))
  · exact Subgroup.mem_sup_left (tvS_mem₁ (by decide))

private theorem sup_normalizer_eq_top :
    Subgroup.normalizer (X₁ : Set H8) ⊔ Subgroup.normalizer (X₂ : Set H8) = ⊤ := by
  refine sup_normalizer_eq_top_of_tvGL (w₀ := pt eS 8)
    (Subgroup.mem_map_of_mem _ (Subgroup.mem_sup_left (tvS_mem₁ (c := 8) (by decide)))) ?_
  refine exists_mem_mulVec_of_certOK eS (gens := gensS) ?_ (by decide) certS_ok
    (P := fun w => w ≠ 0) certS_cover
  intro k hk
  exact ⟨_, Subgroup.mem_map_of_mem _ (genS_mem k hk), genS_act k hk⟩

end Symp

open Symp in
theorem threePlaneGen_H8 : ThreePlaneGen H8 :=
  ⟨baseA sp8Z, X₁, X₂, 3, isElemAbelian_baseA wreathFacts_sp8, le_rfl,
    by rw [card_baseA wreathFacts_sp8]; norm_num, sup_zpowers_le_baseA 1 2,
    by rw [(isElemAbelian_sup_zpowers wreathFacts_sp8 (by decide : (1 : Fin 3) ≠ 2)).2]; norm_num,
    sup_zpowers_le_baseA 0 1,
    by rw [(isElemAbelian_sup_zpowers wreathFacts_sp8 (by decide : (0 : Fin 3) ≠ 1)).2]; norm_num,
    sup_normalizer_eq_top⟩

end CFSG.LocalAnalysis.RankThreeTheoremC.OrthPlanes
