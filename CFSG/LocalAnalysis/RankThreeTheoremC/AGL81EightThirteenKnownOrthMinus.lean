module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81EightThirteenKnownOrthTools
public import CFSG.RankThree.PartTwo.Sec4.Ronan148RH1Om8
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81EightThirteenKnownCore

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.OrthPlanes

open CFSG.Quasithin.SteinbergCB.G2Two CFSG.Open Matrix
open scoped commutatorElement
open CFSG.RankThree.PartTwo.Sec4.RonanK429F (Om8)
open CFSG.RankThree.PartTwo.Sec4.RonanK429F.Om8 (ι Q8)
open CFSG.RankThree.PartTwo.Sec4.Ronan148R.Om8Data (T tw wreathFacts)
open CFSG.RankThree.PartTwo.Sec4.Item434Kit (baseA card_baseA isElemAbelian_baseA
  isElemAbelian_sup_zpowers sup_zpowers_le_baseA)

namespace Minus

private abbrev eM : ι ≃ Fin (4 - 1 + (4 - 1 + 2)) :=
  (Equiv.sumCongr (Equiv.refl _) finSumFinEquiv).trans finSumFinEquiv

private noncomputable abbrev qM : QuadraticForm (ZMod 2) (ι → ZMod 2) :=
  CFSG.LieType.Universal.Spin.quadMinus 4 (ZMod 2) 1 1

private theorem hqM : ⇑qM = Q8 := CFSG.LieType.Universal.Spin.coe_quadMinus 4 (ZMod 2) 1 1

private noncomputable def rf (c : ℕ) : GL ι (ZMod 2) := reflGL qM Q8 hqM (pt eM c)

private theorem rf_mem {c : ℕ} (hc : Q8 (pt eM c) = 1) :
    rf c ∈ CFSG.MatrixModel.isometryCore Q8 :=
  reflGL_mem_isometryCore hqM hc

private noncomputable def rot (ca cb : ℕ) (ha : Q8 (pt eM ca) = 1) (hb : Q8 (pt eM cb) = 1) :
    Om8 :=
  ⟨⁅rf ca, rf cb⁆, Subgroup.commutator_mem_commutator (rf_mem ha) (rf_mem hb)⟩

private noncomputable def g₁ : Om8 :=
  rot 36 68 (by decide +kernel) (by decide +kernel) * rot 64 128 (by decide +kernel)
    (by decide +kernel)

private noncomputable def g₂ : Om8 :=
  rot 72 176 (by decide +kernel) (by decide +kernel) * rot 123 170 (by decide +kernel)
    (by decide +kernel)

private abbrev X₁ : Subgroup Om8 := Subgroup.zpowers (T 0) ⊔ Subgroup.zpowers (T 1)
private abbrev X₂ : Subgroup Om8 := Subgroup.zpowers (T 1) ⊔ Subgroup.zpowers (T 2)

private theorem g₁_conj : g₁ * T 0 * g₁⁻¹ = T 0 ∧ g₁ * T 1 * g₁⁻¹ = T 1 := by
  decide +kernel

private theorem g₂_conj : g₂ * T 1 * g₂⁻¹ = T 2 ∧ g₂ * T 2 * g₂⁻¹ = T 1 := by
  decide +kernel

private theorem g₁_mem : g₁ ∈ Subgroup.normalizer (X₁ : Set Om8) := by
  refine mem_normalizer_sup_zpowers ?_ ?_
  · rw [g₁_conj.1]
    exact Subgroup.mem_sup_left (Subgroup.mem_zpowers _)
  · rw [g₁_conj.2]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers _)

private theorem g₂_mem : g₂ ∈ Subgroup.normalizer (X₂ : Set Om8) := by
  refine mem_normalizer_sup_zpowers ?_ ?_
  · rw [g₂_conj.1]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
  · rw [g₂_conj.2]
    exact Subgroup.mem_sup_left (Subgroup.mem_zpowers _)

private def gensM : List (List ℕ) :=
   [[1, 2, 100, 8, 16, 4, 132, 64], [122, 211, 55, 105, 147, 32, 18, 25]]

private def certM : List (ℕ × ℕ × ℕ) :=
   [(96, 0, 36), (23, 1, 36), (128, 0, 96), (50, 1, 96), (119, 0, 23), (13, 1, 23), (64, 0, 128),
    (25, 1, 128), (22, 0, 50), (247, 0, 119), (63, 1, 119), (109, 0, 13), (132, 0, 64), (18, 1, 64),
    (118, 0, 22), (183, 0, 247), (38, 1, 247), (123, 0, 63), (68, 1, 63), (237, 0, 109),
    (46, 1, 132), (246, 0, 118), (69, 1, 118), (51, 0, 183), (52, 1, 183), (98, 0, 38),
    (196, 1, 38), (155, 0, 123), (97, 1, 123), (224, 0, 68), (37, 1, 68), (173, 0, 237),
    (15, 1, 237), (106, 0, 46), (182, 0, 246), (92, 1, 246), (225, 0, 69), (95, 1, 69), (26, 1, 51),
    (112, 0, 52), (130, 0, 98), (160, 0, 196), (60, 1, 196), (91, 0, 155), (74, 1, 155),
    (129, 0, 97), (72, 1, 97), (192, 0, 224), (43, 1, 224), (41, 0, 173), (29, 1, 173),
    (111, 0, 15), (138, 0, 106), (136, 1, 106), (78, 1, 182), (248, 0, 92), (223, 1, 92),
    (193, 0, 225), (81, 1, 225), (251, 0, 95), (144, 0, 112), (161, 1, 112), (66, 0, 130),
    (202, 1, 130), (57, 1, 160), (120, 0, 60), (159, 0, 91), (65, 1, 91), (142, 0, 74),
    (168, 1, 74), (99, 1, 129), (140, 0, 72), (11, 1, 192), (125, 0, 29), (239, 0, 111),
    (197, 1, 111), (163, 1, 138), (234, 0, 78), (216, 0, 248), (209, 1, 248), (187, 0, 223),
    (113, 1, 193), (149, 0, 81), (219, 0, 251), (80, 0, 144), (67, 1, 161), (134, 0, 66),
    (206, 0, 202), (177, 1, 202), (152, 0, 120), (200, 1, 120), (133, 0, 65), (104, 1, 65),
    (148, 1, 142), (76, 0, 168), (131, 0, 99), (44, 0, 140), (71, 1, 140), (253, 0, 125),
    (175, 0, 239), (220, 1, 239), (70, 1, 197), (145, 1, 234), (241, 1, 216), (213, 0, 209),
    (226, 1, 209), (53, 0, 149), (199, 1, 149), (88, 1, 219), (135, 0, 67), (170, 0, 206),
    (85, 0, 177), (208, 1, 177), (227, 1, 152), (204, 0, 200), (84, 1, 133), (189, 1, 148),
    (232, 0, 76), (176, 1, 131), (126, 1, 44), (156, 1, 253), (184, 0, 220), (198, 1, 220),
    (240, 1, 145), (194, 1, 241), (254, 1, 53), (39, 0, 135), (212, 0, 208), (195, 0, 227),
    (162, 0, 198), (190, 0, 254), (58, 0, 190), (30, 0, 58), (9, 1, 58), (19, 1, 9)]

private theorem g₁_act : ∀ x < 2 ^ (4 - 1 + (4 - 1 + 2)),
    ((g₁ : GL ι (ZMod 2)) : Matrix ι ι (ZMod 2)) *ᵥ pt eM x = pt eM (mApp (gensM.getD 0 []) x) := by
  decide +kernel

private theorem g₂_act : ∀ x < 2 ^ (4 - 1 + (4 - 1 + 2)),
    ((g₂ : GL ι (ZMod 2)) : Matrix ι ι (ZMod 2)) *ᵥ pt eM x = pt eM (mApp (gensM.getD 1 []) x) := by
  decide +kernel

private theorem certM_ok : certOK (4 - 1 + (4 - 1 + 2)) gensM [36] certM = true := by
  decide +kernel

private theorem certM_cover : ∀ x < 2 ^ (4 - 1 + (4 - 1 + 2)),
    Q8 (pt eM x) = 1 → x = 36 ∨ x ∈ certM.map Prod.fst := by
  decide +kernel

private theorem rf_conj_T : ∀ i, rf 36 * (T i : GL ι (ZMod 2)) * (rf 36)⁻¹ = T i := by
  decide +kernel

private theorem le_comap (i j : Fin 3) (hv : Q8 (pt eM 36) = 1) :
    Subgroup.zpowers (T i) ⊔ Subgroup.zpowers (T j) ≤
      (Subgroup.zpowers (T i) ⊔ Subgroup.zpowers (T j)).comap
        (conjOmega (rf 36) (rf_mem hv)) := by
  have hfix : ∀ k, conjOmega (rf 36) (rf_mem hv) (T k) = T k := fun k =>
    Subtype.ext (by rw [coe_conjOmega]; exact rf_conj_T k)
  refine le_comap_sup_zpowers _ ?_ ?_
  · rw [hfix]
    exact Subgroup.mem_sup_left (Subgroup.mem_zpowers _)
  · rw [hfix]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers _)

private theorem sup_normalizer_eq_top :
    Subgroup.normalizer (X₁ : Set Om8) ⊔ Subgroup.normalizer (X₂ : Set Om8) = ⊤ := by
  have hv : Q8 (pt eM 36) = 1 := by decide +kernel
  refine sup_normalizer_eq_top_of_reflect hqM
    (CFSG.LieType.Universal.Spin.nondegenerate_polarBilin_quadMinus 4 (ZMod 2)
      (by decide)) (by decide) hv (le_comap 0 1 hv) (le_comap 1 2 hv) ?_
  refine exists_mem_mulVec_of_certOK eM (gens := gensM) ?_ (by decide) certM_ok certM_cover
  intro k hk
  have hk2 : k < 2 := hk
  interval_cases k
  · exact ⟨_, Subgroup.mem_map_of_mem _ (Subgroup.mem_sup_left g₁_mem), g₁_act⟩
  · exact ⟨_, Subgroup.mem_map_of_mem _ (Subgroup.mem_sup_right g₂_mem), g₂_act⟩

end Minus

open Minus in
theorem threePlaneGen_Om8 : ThreePlaneGen Om8 :=
  ⟨baseA T, X₁, X₂, 3, isElemAbelian_baseA wreathFacts, le_rfl,
    by rw [card_baseA wreathFacts]; norm_num, sup_zpowers_le_baseA 0 1,
    by rw [(isElemAbelian_sup_zpowers wreathFacts (by decide : (0 : Fin 3) ≠ 1)).2]; norm_num,
    sup_zpowers_le_baseA 1 2,
    by rw [(isElemAbelian_sup_zpowers wreathFacts (by decide : (1 : Fin 3) ≠ 2)).2]; norm_num,
    sup_normalizer_eq_top⟩

end CFSG.LocalAnalysis.RankThreeTheoremC.OrthPlanes
