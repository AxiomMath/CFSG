module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R166FamA8Two2
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R166FamA8Two
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R166LayerData
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R166Layer
public import CFSG.LargeExtraspecial.DW37Input
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2EUp
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2Tab.TablesHolds
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2Tab.UpperShared
public import Certificates.Certificate63001
public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec8ExcAction
public import CFSG.LocalAnalysis.GLTheoremA.S10.Lemma106107
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15ACoreArith
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15ACorePerm
public import CFSG.Quasithin.Background.F918D5

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F

open Matrix CFSG.Open CFSG.RankThree.PartTwo.Census CFSG.Assembly.LowTwoRank
open scoped commutatorElement

local notation "𝔽₂" => ZMod 2

namespace SLNineTwo

open F2Block

private def LW : Subgroup (Matrix.SpecialLinearGroup W7 𝔽₂) := (jHom5.comp jHom3).range

private theorem bHomW_comm_jHom5_jHom3 (a : Fin 2 → ZMod 3) (A : Matrix.SpecialLinearGroup W3 𝔽₂) :
    bHomW (eHom23 (Multiplicative.ofAdd a)) * jHom5 (jHom3 A) =
      jHom5 (jHom3 A) * bHomW (eHom23 (Multiplicative.ofAdd a)) := by
  apply Subtype.ext
  change bMatW (extend23 a) * fromBlocks 1 0 0 (fromBlocks 1 0 0 (A : Matrix W3 W3 𝔽₂)) =
    fromBlocks 1 0 0 (fromBlocks 1 0 0 (A : Matrix W3 W3 𝔽₂)) * bMatW (extend23 a)
  simp [bMatW, extend23, Matrix.fromBlocks_multiply]

private theorem LW_le_centralizer_EJW : LW ≤ Subgroup.centralizer (EJW : Set _) := by
  rintro l ⟨A, rfl⟩
  rw [Subgroup.mem_centralizer_iff]
  rintro _ ⟨a, rfl⟩
  change bHomW (eHom23 a) * jHom5 (jHom3 A) =
    jHom5 (jHom3 A) * bHomW (eHom23 a)
  simpa only [ofAdd_toAdd] using bHomW_comm_jHom5_jHom3 a.toAdd A

private theorem zmod3_val_one : ((1 : ZMod 3)).val = 1 := by decide

private theorem b2W_eq_bHomW : b2W = bHomW (Multiplicative.ofAdd (Pi.single (0 : Fin 3) (1 : ZMod 3))) := by
  apply Subtype.ext
  change (xBlock (Q := W5) : Matrix W7 W7 𝔽₂) =
    bMatW (Pi.single (0 : Fin 3) (1 : ZMod 3))
  simp [xBlock, coe_xBlock, bMatW, Pi.single_eq_same, fromBlocks_one]
  rw [zmod3_val_one, pow_one]
  rfl

private theorem b3W_eq_bHomW : b3W = bHomW (Multiplicative.ofAdd (Pi.single (1 : Fin 3) (1 : ZMod 3))) := by
  apply Subtype.ext
  change fromBlocks 1 0 0 (xBlockMat (Q := W3)) =
    bMatW (Pi.single (1 : Fin 3) (1 : ZMod 3))
  simp [bMatW, xBlockMat, Pi.single_eq_same, Pi.single_eq_of_ne, fromBlocks_one]
  rw [zmod3_val_one, pow_one]

private theorem b2W_comm_b3W : b2W * b3W = b3W * b2W := by
  rw [b2W_eq_bHomW, b3W_eq_bHomW, ← bHomW.map_mul, ← bHomW.map_mul]
  exact congrArg bHomW (mul_comm _ _)

private theorem eHom23_single0 : eHom23 (Multiplicative.ofAdd (Pi.single (0 : Fin 2) (1 : ZMod 3))) =
    Multiplicative.ofAdd (Pi.single (0 : Fin 3) (1 : ZMod 3)) := by
  apply Multiplicative.toAdd.injective
  funext i
  fin_cases i <;> simp [eHom23, extend23, Pi.single_apply]

private theorem eHom23_single1 : eHom23 (Multiplicative.ofAdd (Pi.single (1 : Fin 2) (1 : ZMod 3))) =
    Multiplicative.ofAdd (Pi.single (1 : Fin 3) (1 : ZMod 3)) := by
  apply Multiplicative.toAdd.injective
  funext i
  fin_cases i <;> simp [eHom23, extend23, Pi.single_apply]

private theorem b2W_mem_EJW : b2W ∈ EJW := by
  rw [b2W_eq_bHomW, ← eHom23_single0]
  exact ⟨_, rfl⟩

private theorem b3W_mem_EJW : b3W ∈ EJW := by
  rw [b3W_eq_bHomW, ← eHom23_single1]
  exact ⟨_, rfl⟩

private def J5 : Subgroup (Matrix.SpecialLinearGroup W7 𝔽₂) := jHom5.range

private def J3 : Subgroup (Matrix.SpecialLinearGroup W5 𝔽₂) := jHom3.range

private theorem centralizer_b2W_le (g : Matrix.SpecialLinearGroup W7 𝔽₂)
    (hg : g ∈ Subgroup.centralizer ({b2W} : Set _)) :
    g ∈ J5 ⊔ Subgroup.zpowers b2W := by
  have h := centralizer_xBlock_le (Q := W5) g (by simpa [b2W] using hg)
  simpa [J5, jHom5, b2W] using h

private theorem centralizer_xBlock_W3_le (B : Matrix.SpecialLinearGroup W5 𝔽₂)
    (hB : B ∈ Subgroup.centralizer ({xBlock (Q := W3)} : Set _)) :
    B ∈ J3 ⊔ Subgroup.zpowers (xBlock (Q := W3)) := by
  have h := centralizer_xBlock_le (Q := W3) B hB
  simpa [J3, jHom3] using h

private theorem b2W_comm_jHom5 (B : Matrix.SpecialLinearGroup W5 𝔽₂) :
    jHom5 B * b2W = b2W * jHom5 B := by
  apply Subtype.ext
  simp [jHom5, b2W, coe_jBlockHom, coe_xBlock, xBlockMat, Matrix.fromBlocks_multiply]

private theorem comm_J5_zpowers_b2W :
    CFSG.ClassicalInvolution.Generic.Commutes J5 (Subgroup.zpowers b2W) := by
  intro x hx y hy
  change x ∈ jHom5.range at hx
  obtain ⟨B, rfl⟩ := hx
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hy
  rw [← hn]
  exact (Commute.zpow_right (show Commute (jHom5 B) b2W from b2W_comm_jHom5 B) n).eq

private theorem xBlock_comm_jHom3 (B : Matrix.SpecialLinearGroup W3 𝔽₂) :
    jHom3 B * xBlock (Q := W3) = xBlock (Q := W3) * jHom3 B := by
  apply Subtype.ext
  change (jBlockHom (Q := W3) B : Matrix W5 W5 𝔽₂) *
      (fromBlocks (threeCycleMat 𝔽₂) 0 0 1) =
    (fromBlocks (threeCycleMat 𝔽₂) 0 0 1) *
      (jBlockHom (Q := W3) B : Matrix W5 W5 𝔽₂)
  rw [coe_jBlockHom]
  simp [Matrix.fromBlocks_multiply]

private theorem comm_J3_zpowers_xBlock :
    CFSG.ClassicalInvolution.Generic.Commutes J3 (Subgroup.zpowers (xBlock (Q := W3))) := by
  intro x hx y hy
  change x ∈ jHom3.range at hx
  obtain ⟨B, rfl⟩ := hx
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hy
  rw [← hn]
  exact (Commute.zpow_right (show Commute (jHom3 B) (xBlock (Q := W3)) from xBlock_comm_jHom3 B) n).eq

private theorem centralizer_EJW_le_sup :
    Subgroup.centralizer (EJW : Set _) ≤
      LW ⊔ (Subgroup.zpowers b2W ⊔ Subgroup.zpowers b3W) := by
  intro g hg
  have hg2 : g ∈ Subgroup.centralizer ({b2W} : Set _) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (Subgroup.mem_centralizer_iff.1 hg b2W b2W_mem_EJW).symm
  have hg3 : g ∈ Subgroup.centralizer ({b3W} : Set _) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (Subgroup.mem_centralizer_iff.1 hg b3W b3W_mem_EJW).symm
  obtain ⟨j, hj, k, hk, hgjk⟩ :=
    CFSG.ClassicalInvolution.Asc77.exists_mul_of_mem_sup_of_commutes
      (A := J5) (B := Subgroup.zpowers b2W) comm_J5_zpowers_b2W
      (centralizer_b2W_le g hg2)
  rw [hgjk] at hg3 ⊢
  change j ∈ jHom5.range at hj
  obtain ⟨A, rfl⟩ := hj
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hk
  have hk3 : k * b3W = b3W * k := by
    rw [← hn]
    exact (Commute.zpow_left (show Commute b2W b3W from b2W_comm_b3W) n).eq
  have hj3 : jHom5 A * b3W = b3W * jHom5 A := by
    have h := Subgroup.mem_centralizer_singleton_iff.mp hg3
    have h' : (jHom5 A * b3W) * k = (b3W * jHom5 A) * k := by
      calc (jHom5 A * b3W) * k = jHom5 A * (b3W * k) := by group
        _ = jHom5 A * (k * b3W) := by rw [hk3]
        _ = (jHom5 A * k) * b3W := by group
        _ = b3W * (jHom5 A * k) := h
        _ = (b3W * jHom5 A) * k := by group
    exact mul_right_cancel h'
  have hA3 : A * xBlock (Q := W3) = xBlock (Q := W3) * A := by
    apply jHom5_injective
    simpa [b3W, map_mul] using hj3
  have hAc : A ∈ Subgroup.centralizer ({xBlock (Q := W3)} : Set _) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact hA3
  obtain ⟨l, hl, m, hm, hAlm⟩ :=
    CFSG.ClassicalInvolution.Asc77.exists_mul_of_mem_sup_of_commutes
      (A := J3) (B := Subgroup.zpowers (xBlock (Q := W3))) comm_J3_zpowers_xBlock
      (centralizer_xBlock_W3_le A hAc)
  change l ∈ jHom3.range at hl
  have hA : A = l * m := hAlm
  have hjl : jHom5 l ∈ LW := by
    obtain ⟨C, rfl⟩ := hl
    exact ⟨C, rfl⟩
  have hjm : jHom5 m ∈ Subgroup.zpowers b3W := by
    obtain ⟨r, hr⟩ := Subgroup.mem_zpowers_iff.mp hm
    refine ⟨r, ?_⟩
    rw [show b3W = jHom5 (xBlock (Q := W3)) from rfl, ← hr, map_zpow]
  have hj' : jHom5 A ∈ LW ⊔ Subgroup.zpowers b3W := by
    rw [hA, map_mul]
    exact Subgroup.mul_mem_sup hjl hjm
  have hmem : jHom5 A * k ∈ (LW ⊔ Subgroup.zpowers b3W) ⊔ Subgroup.zpowers b2W :=
    Subgroup.mul_mem_sup hj' hk
  simpa [sup_assoc, sup_comm, sup_left_comm] using hmem

private theorem le_normalizer_of_le_sup_central {G : Type} [Group G] {H L K : Subgroup G}
    (hH : H ≤ L ⊔ K) (hK : K ≤ Subgroup.centralizer (L : Set G)) :
    H ≤ Subgroup.normalizer (L : Set G) := by
  refine CFSG.subgroup_le_normalizer_of_conj_mem L H ?_
  intro r h hh
  have hcomm : CFSG.ClassicalInvolution.Generic.Commutes L K := fun l hl k hk =>
    Subgroup.mem_centralizer_iff.1 (hK hk) l hl
  obtain ⟨l, hl, k, hk, hrlk⟩ :=
    CFSG.ClassicalInvolution.Asc77.exists_mul_of_mem_sup_of_commutes
      (A := L) (B := K) hcomm (hH r.2)
  rw [hrlk]
  have hkh : k * h = h * k := (Subgroup.mem_centralizer_iff.1 (hK hk) h hh).symm
  have hcalc : (l * k) * h * (l * k)⁻¹ = l * h * l⁻¹ := by
    calc (l * k) * h * (l * k)⁻¹ = l * (k * h * k⁻¹) * l⁻¹ := by group
      _ = l * (h * k * k⁻¹) * l⁻¹ := by rw [hkh]
      _ = l * h * l⁻¹ := by group
  rw [hcalc]
  exact L.mul_mem (L.mul_mem hl hh) (L.inv_mem hl)

private theorem zpowers_b2W_le_centralizer_LW :
    Subgroup.zpowers b2W ≤
      Subgroup.centralizer (LW : Set (Matrix.SpecialLinearGroup W7 𝔽₂)) := by
  intro x hx
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hx
  rw [Subgroup.mem_centralizer_iff]
  intro l hl
  rw [← hn]
  exact (Commute.zpow_right
    (show Commute l b2W from
      (Subgroup.mem_centralizer_iff.1 (LW_le_centralizer_EJW hl) b2W b2W_mem_EJW).symm) n).eq

private theorem zpowers_b3W_le_centralizer_LW :
    Subgroup.zpowers b3W ≤
      Subgroup.centralizer (LW : Set (Matrix.SpecialLinearGroup W7 𝔽₂)) := by
  intro x hx
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hx
  rw [Subgroup.mem_centralizer_iff]
  intro l hl
  rw [← hn]
  exact (Commute.zpow_right
    (show Commute l b3W from
      (Subgroup.mem_centralizer_iff.1 (LW_le_centralizer_EJW hl) b3W b3W_mem_EJW).symm) n).eq

private theorem sup_zpowers_le_centralizer_LW :
    (Subgroup.zpowers b2W ⊔ Subgroup.zpowers b3W) ≤
      Subgroup.centralizer (LW : Set (Matrix.SpecialLinearGroup W7 𝔽₂)) :=
  sup_le zpowers_b2W_le_centralizer_LW zpowers_b3W_le_centralizer_LW

private theorem centralizer_EJW_le_normalizer_LW :
    Subgroup.centralizer (EJW : Set (Matrix.SpecialLinearGroup W7 𝔽₂)) ≤
      Subgroup.normalizer (LW : Set (Matrix.SpecialLinearGroup W7 𝔽₂)) :=
  le_normalizer_of_le_sup_central centralizer_EJW_le_sup sup_zpowers_le_centralizer_LW

private theorem LW_normal_in_centralizer_EJW :
    (LW.subgroupOf (Subgroup.centralizer
      (EJW : Set (Matrix.SpecialLinearGroup W7 𝔽₂)))).Normal :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer LW_le_centralizer_EJW).2
    centralizer_EJW_le_normalizer_LW

private theorem isQuasisimple_LW : CFSG.IsQuasisimple ↥LW := by
  let eIdx : Fin 3 ≃ W3 := (Fintype.equivFinOfCardEq (by simp [W3])).symm
  let e1 : Matrix.SpecialLinearGroup (Fin 3) 𝔽₂ ≃* Matrix.SpecialLinearGroup W3 𝔽₂ :=
    slReindex 𝔽₂ eIdx
  let e2 : ↥(StatedSL 3 𝔽₂) ≃* Matrix.SpecialLinearGroup (Fin 3) 𝔽₂ :=
    (specialLinearGroupEquivStatedSL 3 𝔽₂).symm
  let e3 : Matrix.SpecialLinearGroup W3 𝔽₂ ≃* ↥LW :=
    MonoidHom.ofInjective (f := jHom5.comp jHom3)
      (jHom5_injective.comp jHom3_injective)
  have h := CFSG.Open.StatedAPI.isQuasisimple_statedSL_of_two_le (m := 2) (by norm_num) 𝔽₂
  exact CFSG.LocalCores.isQuasisimple_of_mulEquiv (e2.trans (e1.trans e3)) h

private theorem center_LW_eq_bot : Subgroup.center ↥LW = ⊥ := by
  let eIdx : Fin 3 ≃ W3 := (Fintype.equivFinOfCardEq (by simp [W3])).symm
  let e1 : Matrix.SpecialLinearGroup (Fin 3) 𝔽₂ ≃* Matrix.SpecialLinearGroup W3 𝔽₂ :=
    slReindex 𝔽₂ eIdx
  let e3 : Matrix.SpecialLinearGroup W3 𝔽₂ ≃* ↥LW :=
    MonoidHom.ofInjective (f := jHom5.comp jHom3)
      (jHom5_injective.comp jHom3_injective)
  have h3 : Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) 𝔽₂) = ⊥ :=
    CFSG.LargeExtraspecial.DW.center_specialLinearGroup_zmod_two_eq_bot 3
  exact (center_eq_bot_congr (e1.trans e3)).2 h3

private def b4W : Matrix.SpecialLinearGroup W7 𝔽₂ :=
  bHomW (Multiplicative.ofAdd (Pi.single (2 : Fin 3) (1 : ZMod 3)))

private theorem b4W_eq : b4W = jHom5 (jHom3 (xBlock (Q := Fin 1))) := by
  apply Subtype.ext
  change bMatW (Pi.single (2 : Fin 3) (1 : ZMod 3)) =
    fromBlocks 1 0 0 (fromBlocks 1 0 0 (xBlockMat (Q := Fin 1)))
  simp [bMatW, xBlockMat, Pi.single_eq_same, Pi.single_eq_of_ne, fromBlocks_one]
  rw [zmod3_val_one, pow_one]

private theorem b4W_pow_three : b4W ^ 3 = 1 := by
  rw [b4W, ← map_pow, pow_three_multiplicative_pi3, map_one]

private theorem b4W_ne_one : b4W ≠ 1 := by
  intro h
  change b4W = 1 at h
  have h' : Multiplicative.ofAdd (Pi.single (2 : Fin 3) (1 : ZMod 3)) = 1 :=
    bHomW_injective (by simpa [b4W] using h)
  have h'' : (Pi.single (2 : Fin 3) (1 : ZMod 3) : Fin 3 → ZMod 3) = 0 :=
    Multiplicative.toAdd.injective h'
  have h2 := congrFun h'' 2
  exact one_ne_zero h2

private theorem b4W_mem_LW : b4W ∈ LW := by
  rw [b4W_eq]
  exact ⟨xBlock (Q := Fin 1), rfl⟩

private theorem orderOf_b4W : orderOf b4W = 3 :=
  orderOf_eq_prime b4W_pow_three b4W_ne_one

private theorem three_dvd_card_LW : 3 ∣ Nat.card LW := by
  have h := Subgroup.orderOf_dvd_natCard LW b4W_mem_LW
  rwa [orderOf_b4W] at h

private theorem three_dvd_card_quotient_center_LW :
    3 ∣ Nat.card (↥LW ⧸ Subgroup.center ↥LW) := by
  have h := three_dvd_card_LW
  have hq : Nat.card (↥LW ⧸ Subgroup.center ↥LW) = Nat.card LW := by
    rw [center_LW_eq_bot]
    exact Nat.card_congr (QuotientGroup.quotientBot).toEquiv
  rwa [hq]

private theorem isQuasisimple_LW_open : CFSG.Open.IsQuasisimple ↥LW := by
  rcases isQuasisimple_LW with ⟨hperf, hsimple, -⟩
  exact ⟨Group.isPerfect_def.1 hperf, hsimple⟩

private theorem glaPLayer_EJW_ne_bot :
    GLAPLayer 3 (Subgroup.centralizer (EJW : Set (Matrix.SpecialLinearGroup W7 𝔽₂))) ≠ ⊥ :=
  glaPLayer_ne_bot_of_normal_quasisimple Nat.prime_three LW_le_centralizer_EJW
    LW_normal_in_centralizer_EJW isQuasisimple_LW_open three_dvd_card_quotient_center_LW

private theorem layerData_W7 : LayerData166 (Matrix.SpecialLinearGroup W7 𝔽₂) 3 3 :=
  ⟨BJW, SJW, EJW, isElemAbelian_BJW, card_BJW, isPGroup_two_SJW, BJW_le_normalizer_SJW,
    BJW_inf_centralizer_SJW_eq_bot, EJW_le_BJW, card_EJW, glaPLayer_EJW_ne_bot⟩

theorem layerData_J : LayerData166 ↥J 3 3 :=
  LayerData166.of_mulEquiv (MonoidHom.ofInjective (f := jHom) jHom_injective).symm
    layerData_W7 Nat.prime_three


end SLNineTwo

section Certs


namespace SLNineTwo

private theorem center_f2Model_eq_bot : Subgroup.center (Matrix.SpecialLinearGroup Ix 𝔽₂) = ⊥ := by
  let eIdx : Fin 9 ≃ Ix := (Fintype.equivFinOfCardEq (by simp [Ix])).symm
  have h9 : Subgroup.center (Matrix.SpecialLinearGroup (Fin 9) 𝔽₂) = ⊥ :=
    CFSG.LargeExtraspecial.DW.center_specialLinearGroup_zmod_two_eq_bot 9
  exact (center_eq_bot_congr (slReindex 𝔽₂ eIdx)).2 h9

private theorem evenRank_f2Model : evenRank (Matrix.SpecialLinearGroup Ix 𝔽₂) = 4 := by
  have hlab : Rk2IsLabel (Matrix.SpecialLinearGroup Ix 𝔽₂) ⟨.A, 8, 1⟩ := hasLabel_f2Model
  have hlow : 4 ≤ evenRank (Matrix.SpecialLinearGroup Ix 𝔽₂) := by
    have h := (rk2Lower_holds (Matrix.SpecialLinearGroup Ix 𝔽₂) ⟨.A, 8, 1⟩ hlab).a_one rfl rfl
    norm_num at h
    exact h
  have hup : evenRank (Matrix.SpecialLinearGroup Ix 𝔽₂) ≤ 4 :=
    (rk2_eUpAt_of_tables rk2KRank rk2Upper_holds
      (K := Matrix.SpecialLinearGroup Ix 𝔽₂) (lab := ⟨.A, 8, 1⟩) hlab).a8 rfl
  exact le_antisymm hup hlow

theorem concl166S_f2Model :
    ∃ (q : ℕ) (B' : Subgroup (Matrix.SpecialLinearGroup Ix 𝔽₂))
      (x' : Matrix.SpecialLinearGroup Ix 𝔽₂) (J : Subgroup (Matrix.SpecialLinearGroup Ix 𝔽₂)),
      Concl166S (Matrix.SpecialLinearGroup Ix 𝔽₂) 7 q B' x' J := by
  have hmult_data := linearSevenTwo_mult (J := ↥SLNineTwo.J) hasLabel_J
    CFSG.ComponentClassification.TBLit.griessMultipliersAllModels_holds
  have hZJ : Subgroup.center ↥SLNineTwo.J = ⊥ := hmult_data.1.1
  have hmult : TrivialMultiplierT ↥SLNineTwo.J := hmult_data.1.2
  have hm2 : evenRank (Matrix.SpecialLinearGroup Ix 𝔽₂) + 2 ≤ twoRank ↥SLNineTwo.J := by
    have h12 : 12 ≤ twoRank ↥SLNineTwo.J := hmult_data.2.2.1
    rw [evenRank_f2Model]
    omega
  have hdvd : 7 * 3 ∣ Nat.card (↥SLNineTwo.J ⧸ Subgroup.center ↥SLNineTwo.J) := by
    have h21 : 21 ∣ Nat.card (↥SLNineTwo.J ⧸ Subgroup.center ↥SLNineTwo.J) := hmult_data.2.2.2
    simpa [show 7 * 3 = 21 by norm_num] using h21
  have hshape : ∀ lab : GLALabel, HasLabel (Matrix.SpecialLinearGroup Ix 𝔽₂)
      (fun l : GLALabel => l = lab) →
      JShape lab (3 ∣ Nat.card (Subgroup.center (Matrix.SpecialLinearGroup Ix 𝔽₂)))
        ⟨.A, 6, 1⟩ := by
    intro lab hlab
    have hlabR : HasLabel (Matrix.SpecialLinearGroup Ix 𝔽₂) (· = ⟨.A, 8, 1⟩) :=
      hasLabel_f2Model
    rcases label_eq_or_BC (K := Matrix.SpecialLinearGroup Ix 𝔽₂)
      (by rw [evenRank_f2Model]) hlabR hlab with h | hBC
    · subst h
      simp [JShape]
    · exfalso
      exact hBC.1.elim (by decide) (by decide)
  obtain ⟨B', hB'⟩ := exists_concl166S_of_layerData
    (K := Matrix.SpecialLinearGroup Ix 𝔽₂) (p := 7) (q := 3) (x := xElt) (J := SLNineTwo.J)
    Nat.prime_three (by norm_num) xElt_pow_three xElt_ne_one center_f2Model_eq_bot
    (by rw [evenRank_f2Model]) J_le_centralizer_xElt isQuasisimple_J
    (fun g hg h hh => commutator_mem_J hg hh) ⟨.A, 6, 1⟩ hasLabel_J hshape hm2 hdvd hZJ hmult
    (by simpa [evenRank_f2Model] using layerData_J)
  exact ⟨3, B', xElt, J, hB'⟩

end SLNineTwo

open SLNineTwo

theorem i166On_famA8Two_of_transport
    (htr : ∀ {K R : Type} [Group K] [Finite K] [Group R] [Finite R], (K ≃* R) → ∀ {p : ℕ},
      (∃ (q : ℕ) (B' : Subgroup R) (x' : R) (J : Subgroup R), Concl166S R p q B' x' J) →
      ∃ (q : ℕ) (B' : Subgroup K) (x' : K) (J : Subgroup K), Concl166S K p q B' x' J) :
    I166On i166FamA8Two := by
  intro K _ _ lab p hlab hfam hp hp2 hns he hr
  obtain ⟨rfl, rfl⟩ := hfam
  obtain ⟨e⟩ := famA8Two_equiv_model hlab
  exact htr e concl166S_f2Model

end Certs

end CFSG.LocalAnalysis.GLTheoremA.Y10F
