module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81EightThirteenKnownOrthTools
public import CFSG.RankThree.PartTwo.Sec4.RonanK429RowEO8Inner
public import CFSG.RankThree.PartTwo.Sec5.Tools
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81EightThirteenKnownCore

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.OrthPlanes

open CFSG.Quasithin.SteinbergCB.G2Two CFSG.Open Matrix
open scoped commutatorElement
open CFSG.RankThree.PartTwo.Sec4.RonanK429E.O8 (ι8 Q8 OM)

namespace Plus

private noncomputable abbrev qP : QuadraticForm (ZMod 2) (ι8 → ZMod 2) :=
  CFSG.LieType.Universal.Spin.quadPlus 4 (ZMod 2)

private theorem hqP : ⇑qP = Q8 := CFSG.LieType.Universal.Spin.coe_quadPlus 4 (ZMod 2)

private abbrev eP : ι8 ≃ Fin (4 + 4) := finSumFinEquiv

private noncomputable def rf (c : ℕ) : GL ι8 (ZMod 2) := reflGL qP Q8 hqP (pt eP c)

private theorem rf_mem {c : ℕ} (hc : Q8 (pt eP c) = 1) :
    rf c ∈ CFSG.MatrixModel.isometryCore Q8 :=
  reflGL_mem_isometryCore hqP hc

private noncomputable def rot (ca cb : ℕ) (ha : Q8 (pt eP ca) = 1) (hb : Q8 (pt eP cb) = 1) :
    OM :=
  ⟨⁅rf ca, rf cb⁆, Subgroup.commutator_mem_commutator (rf_mem ha) (rf_mem hb)⟩

private noncomputable def t₁ : OM := rot 17 35 (by decide +kernel) (by decide +kernel)
private noncomputable def t₂ : OM := rot 19 34 (by decide +kernel) (by decide +kernel)
private noncomputable def t₃ : OM := rot 68 140 (by decide +kernel) (by decide +kernel)
private noncomputable def t₄ : OM := rot 76 136 (by decide +kernel) (by decide +kernel)

private noncomputable def s : OM := t₂ * (t₃ * t₄)

private noncomputable def g₁ : OM :=
  rot 77 168 (by decide +kernel) (by decide +kernel) * rot 109 137 (by decide +kernel)
    (by decide +kernel)

private noncomputable def g₂ : OM :=
  rot 17 50 (by decide +kernel) (by decide +kernel) * rot 23 46 (by decide +kernel)
    (by decide +kernel)

private noncomputable abbrev X₁ : Subgroup OM := Subgroup.zpowers t₁ ⊔ Subgroup.zpowers t₂
private noncomputable abbrev X₂ : Subgroup OM := Subgroup.zpowers t₁ ⊔ Subgroup.zpowers s
private noncomputable abbrev E : Subgroup OM := X₁ ⊔ Subgroup.zpowers (t₃ * t₄)

private def fixSub (w : ι8 → ZMod 2) : Subgroup OM where
  carrier := {g | ((g : GL ι8 (ZMod 2)) : Matrix ι8 ι8 (ZMod 2)) *ᵥ w = w}
  mul_mem' {a b} ha hb := by
    simp only [Set.mem_setOf_eq, Subgroup.coe_mul, Units.val_mul, ← Matrix.mulVec_mulVec] at *
    rw [hb, ha]
  one_mem' := by simp
  inv_mem' {a} ha := by
    simp only [Set.mem_setOf_eq] at *
    calc (((a⁻¹ : OM) : GL ι8 (ZMod 2)) : Matrix ι8 ι8 (ZMod 2)) *ᵥ w
        = (((a⁻¹ : OM) : GL ι8 (ZMod 2)) : Matrix ι8 ι8 (ZMod 2)) *ᵥ
            ((((a : OM) : GL ι8 (ZMod 2)) : Matrix ι8 ι8 (ZMod 2)) *ᵥ w) := by rw [ha]
      _ = w := by
          rw [Matrix.mulVec_mulVec, ← Units.val_mul, ← Subgroup.coe_mul, inv_mul_cancel]
          simp

private theorem t_pow : t₁ ^ 3 = 1 ∧ t₂ ^ 3 = 1 ∧ (t₃ * t₄) ^ 3 = 1 ∧ s ^ 3 = 1 := by
  decide +kernel

private theorem t_comm : t₁ * t₂ = t₂ * t₁ ∧ t₁ * (t₃ * t₄) = t₃ * t₄ * t₁ ∧
    t₂ * (t₃ * t₄) = t₃ * t₄ * t₂ ∧ t₁ * s = s * t₁ := by
  decide +kernel

private theorem fix_facts : t₁ ∈ fixSub (pt eP 34) ∧ t₂ ∉ fixSub (pt eP 34) ∧
    s ∉ fixSub (pt eP 34) ∧ t₁ ∈ fixSub (pt eP 68) ∧ t₂ ∈ fixSub (pt eP 68) ∧
    t₃ * t₄ ∉ fixSub (pt eP 68) := by
  simp only [fixSub, Subgroup.mem_mk, Submonoid.mem_mk, Subsemigroup.mem_mk, Set.mem_setOf_eq]
  decide +kernel

private theorem t₁_ne_one : t₁ ≠ 1 := by
  decide +kernel

private theorem isElemAbelian_zpowers_t₁ : IsElemAbelian 3 (Subgroup.zpowers t₁) := by
  refine ⟨inferInstance, fun x hx => ?_⟩
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  rw [← zpow_natCast, ← _root_.zpow_mul, mul_comm, _root_.zpow_mul, zpow_natCast, t_pow.1,
    _root_.one_zpow]

private theorem card_zpowers_t₁ : Nat.card (Subgroup.zpowers t₁) = 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rw [Nat.card_zpowers]
  exact orderOf_eq_prime t_pow.1 t₁_ne_one

private theorem zpowers_t₁_le_fix : Subgroup.zpowers t₁ ≤ fixSub (pt eP 34) :=
  Subgroup.zpowers_le.2 fix_facts.1

private theorem X₁_le_fix : X₁ ≤ fixSub (pt eP 68) :=
  sup_le (Subgroup.zpowers_le.2 fix_facts.2.2.2.1) (Subgroup.zpowers_le.2 fix_facts.2.2.2.2.1)

private theorem X₁_facts : IsElemAbelian 3 X₁ ∧ Nat.card X₁ = 9 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h := CFSG.RankThree.PartTwo.Sec5.isElemAbelian_sup_zpowers isElemAbelian_zpowers_t₁
    (fun hm => fix_facts.2.1 (zpowers_t₁_le_fix hm)) t_pow.2.1 (fun a ha => by
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
      exact (Commute.zpow_left t_comm.1 k).eq)
  exact ⟨h.1, by rw [h.2, card_zpowers_t₁]⟩

private theorem X₂_facts : IsElemAbelian 3 X₂ ∧ Nat.card X₂ = 9 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h := CFSG.RankThree.PartTwo.Sec5.isElemAbelian_sup_zpowers isElemAbelian_zpowers_t₁
    (fun hm => fix_facts.2.2.1 (zpowers_t₁_le_fix hm)) t_pow.2.2.2 (fun a ha => by
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
      exact (Commute.zpow_left t_comm.2.2.2 k).eq)
  exact ⟨h.1, by rw [h.2, card_zpowers_t₁]⟩

private theorem E_facts : IsElemAbelian 3 E ∧ Nat.card E = 27 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h := CFSG.RankThree.PartTwo.Sec5.isElemAbelian_sup_zpowers X₁_facts.1
    (fun hm => fix_facts.2.2.2.2.2 (X₁_le_fix hm)) t_pow.2.2.1 (fun a ha => by
      have hc : X₁ ≤ Subgroup.centralizer ({t₃ * t₄} : Set OM) := by
        refine sup_le (Subgroup.zpowers_le.2 ?_) (Subgroup.zpowers_le.2 ?_)
        · exact Subgroup.mem_centralizer_singleton_iff.2 t_comm.2.1
        · exact Subgroup.mem_centralizer_singleton_iff.2 t_comm.2.2.1
      exact Subgroup.mem_centralizer_singleton_iff.1 (hc ha))
  exact ⟨h.1, by rw [h.2, X₁_facts.2]⟩

private theorem X₂_le_E : X₂ ≤ E := by
  refine sup_le (Subgroup.zpowers_le.2 ?_) (Subgroup.zpowers_le.2 ?_)
  · exact Subgroup.mem_sup_left (Subgroup.mem_sup_left (Subgroup.mem_zpowers _))
  · exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.mem_sup_right
      (Subgroup.mem_zpowers _))) (Subgroup.mem_sup_right (Subgroup.mem_zpowers _))

private theorem g₁_conj : g₁ * t₁ * g₁⁻¹ = t₂ ^ 2 ∧ g₁ * t₂ * g₁⁻¹ = t₁ ^ 2 := by
  decide +kernel

private theorem g₂_conj : g₂ * t₁ * g₂⁻¹ = t₁ ∧ g₂ * s * g₂⁻¹ = s := by
  decide +kernel

private theorem g₁_mem : g₁ ∈ Subgroup.normalizer (X₁ : Set OM) := by
  refine mem_normalizer_sup_zpowers ?_ ?_
  · rw [g₁_conj.1]
    exact Subgroup.pow_mem _ (Subgroup.mem_sup_right (Subgroup.mem_zpowers _)) 2
  · rw [g₁_conj.2]
    exact Subgroup.pow_mem _ (Subgroup.mem_sup_left (Subgroup.mem_zpowers _)) 2

private theorem g₂_mem : g₂ ∈ Subgroup.normalizer (X₂ : Set OM) := by
  refine mem_normalizer_sup_zpowers ?_ ?_
  · rw [g₂_conj.1]
    exact Subgroup.mem_sup_left (Subgroup.mem_zpowers _)
  · rw [g₂_conj.2]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers _)

private def gensP : List (List ℕ) :=
   [[1, 3, 72, 204, 48, 32, 12, 8], [41, 30, 4, 8, 10, 5, 87, 174]]

private def certP : List (ℕ × ℕ × ℕ) :=
   [(49, 0, 17), (35, 1, 17), (38, 1, 49), (34, 0, 35), (50, 1, 35), (107, 0, 38), (31, 1, 38),
    (27, 1, 34), (19, 0, 50), (226, 0, 107), (109, 1, 107), (182, 0, 31), (254, 0, 27), (53, 1, 27),
    (61, 1, 19), (39, 0, 226), (169, 0, 109), (119, 1, 109), (83, 0, 182), (187, 1, 182),
    (147, 0, 254), (228, 1, 254), (89, 0, 53), (149, 0, 61), (42, 1, 61), (106, 0, 39), (54, 1, 39),
    (229, 0, 169), (138, 1, 169), (86, 0, 119), (62, 0, 83), (214, 0, 187), (158, 1, 187),
    (58, 0, 147), (108, 0, 228), (248, 1, 228), (241, 0, 89), (124, 1, 89), (113, 0, 149),
    (137, 1, 149), (239, 0, 42), (227, 0, 106), (68, 1, 106), (91, 0, 54), (21, 1, 54),
    (209, 1, 229), (199, 0, 138), (184, 1, 138), (71, 1, 86), (151, 0, 62), (29, 1, 62),
    (127, 0, 214), (233, 1, 214), (191, 0, 158), (223, 0, 58), (25, 1, 58), (168, 0, 108),
    (94, 1, 108), (216, 0, 248), (152, 0, 124), (84, 1, 124), (197, 0, 137), (143, 1, 137),
    (162, 0, 239), (203, 1, 227), (242, 0, 91), (98, 1, 91), (121, 0, 21), (218, 1, 209),
    (78, 0, 199), (202, 1, 199), (212, 0, 184), (70, 0, 71), (100, 1, 71), (114, 0, 151),
    (181, 0, 29), (47, 1, 29), (154, 0, 127), (99, 1, 127), (221, 1, 233), (178, 0, 223),
    (200, 1, 223), (253, 0, 25), (43, 1, 25), (163, 1, 168), (79, 1, 94), (251, 1, 216),
    (244, 0, 152), (172, 1, 152), (116, 0, 84), (77, 0, 197), (142, 0, 143), (198, 1, 203),
    (23, 0, 242), (232, 1, 242), (76, 1, 98), (139, 0, 78), (69, 1, 78), (247, 1, 212),
    (81, 0, 181), (140, 1, 181), (166, 0, 47), (46, 0, 99), (101, 1, 99), (177, 0, 221),
    (145, 0, 253), (211, 1, 253), (238, 0, 43), (156, 1, 163), (201, 1, 251), (92, 0, 244),
    (167, 1, 172), (188, 1, 142), (122, 0, 23), (57, 1, 23), (136, 0, 76), (141, 1, 145),
    (196, 1, 211), (173, 1, 188)]

private theorem g₁_act : ∀ x < 2 ^ (4 + 4),
    ((g₁ : GL ι8 (ZMod 2)) : Matrix ι8 ι8 (ZMod 2)) *ᵥ pt eP x =
      pt eP (mApp (gensP.getD 0 []) x) := by
  decide +kernel

private theorem g₂_act : ∀ x < 2 ^ (4 + 4),
    ((g₂ : GL ι8 (ZMod 2)) : Matrix ι8 ι8 (ZMod 2)) *ᵥ pt eP x =
      pt eP (mApp (gensP.getD 1 []) x) := by
  decide +kernel

private theorem certP_ok : certOK (4 + 4) gensP [17] certP = true := by
  decide +kernel

private theorem certP_cover : ∀ x < 2 ^ (4 + 4),
    Q8 (pt eP x) = 1 → x = 17 ∨ x ∈ certP.map Prod.fst := by
  decide +kernel

private theorem rf_conj :
    rf 17 * (t₁ : GL ι8 (ZMod 2)) * (rf 17)⁻¹ = ((t₁ ^ 2 : OM) : GL ι8 (ZMod 2)) ∧
    rf 17 * (t₂ : GL ι8 (ZMod 2)) * (rf 17)⁻¹ = t₂ ∧
    rf 17 * (s : GL ι8 (ZMod 2)) * (rf 17)⁻¹ = s := by
  decide +kernel

private theorem sup_normalizer_eq_top :
    Subgroup.normalizer (X₁ : Set OM) ⊔ Subgroup.normalizer (X₂ : Set OM) = ⊤ := by
  have hv : Q8 (pt eP 17) = 1 := by decide +kernel
  have h₁ : conjOmega (rf 17) (rf_mem hv) t₁ = t₁ ^ 2 := Subtype.ext rf_conj.1
  have h₂ : conjOmega (rf 17) (rf_mem hv) t₂ = t₂ := Subtype.ext rf_conj.2.1
  have h₃ : conjOmega (rf 17) (rf_mem hv) s = s := Subtype.ext rf_conj.2.2
  refine sup_normalizer_eq_top_of_reflect hqP
    (CFSG.LieType.Universal.Spin.nondegenerate_polarBilin_quadPlus 4 (ZMod 2)) (by decide) hv
    (le_comap_sup_zpowers _ ?_ ?_) (le_comap_sup_zpowers _ ?_ ?_) ?_
  · change conjOmega (rf 17) (rf_mem hv) t₁ ∈ X₁
    rw [h₁]
    exact Subgroup.pow_mem _ (Subgroup.mem_sup_left (Subgroup.mem_zpowers _)) 2
  · change conjOmega (rf 17) (rf_mem hv) t₂ ∈ X₁
    rw [h₂]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
  · change conjOmega (rf 17) (rf_mem hv) t₁ ∈ X₂
    rw [h₁]
    exact Subgroup.pow_mem _ (Subgroup.mem_sup_left (Subgroup.mem_zpowers _)) 2
  · change conjOmega (rf 17) (rf_mem hv) s ∈ X₂
    rw [h₃]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
  refine exists_mem_mulVec_of_certOK eP (gens := gensP) ?_ (by decide) certP_ok
    (P := fun w => Q8 w = 1) certP_cover
  intro k hk
  have hk2 : k < 2 := hk
  interval_cases k
  · exact ⟨_, Subgroup.mem_map_of_mem _ (Subgroup.mem_sup_left g₁_mem), g₁_act⟩
  · exact ⟨_, Subgroup.mem_map_of_mem _ (Subgroup.mem_sup_right g₂_mem), g₂_act⟩

end Plus

open Plus in
theorem threePlaneGen_OM : ThreePlaneGen OM :=
  ⟨E, X₁, X₂, 3, E_facts.1, le_rfl, by rw [E_facts.2]; norm_num, le_sup_left,
    by rw [X₁_facts.2]; norm_num, X₂_le_E, by rw [X₂_facts.2]; norm_num, sup_normalizer_eq_top⟩

end CFSG.LocalAnalysis.RankThreeTheoremC.OrthPlanes
