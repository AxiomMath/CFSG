module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog82P29Ub
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4CSUc
public import CFSG.LocalAnalysis.ComponentClassification.BlockTwoProductAction
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4AZCore
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4CSUb
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4DiagLa
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4DiagUh
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4OrdU2
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierLinearTwo
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueUStatement
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB7Basic
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog7L2
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog82L2
public import CFSG.LocalAnalysis.ComponentClassification.NormalizedProductSylow
public import CFSG.LocalAnalysis.ComponentClassification.TwoActionFixedInvolution
public import CFSG.LocalAnalysis.ComponentClassification.TwoActionInvariantSylow
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrCentralSylowMaximality
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedGSAContainedSource
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedLayerOddCoreUnbalancingTriple
public import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.CentralInvolutionStructure
public import CFSG.LocalAnalysis.SectionRank.CentralLift
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.Open.QuasithinDefs
public import CFSG.Permutation.AlternatingAutomorphism
public import CFSG.RankThree.PartOne.KC.LinearCommutantSemi
public import CFSG.Sporadic.Th.F2Spec
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_3_3
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section3.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter2.Basic

public section

namespace CFSG.ComponentClassification.GSThmB.P29

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ComponentClassification.CatFactsL4U4 UnitaryOut UnitaryConj HBlocks StabU DiagU CSU
  ClassicalGroups.UnitaryFlag CFSG.Assembly.LowTwoRank

namespace U4M

variable {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K) (P : GL (Fin 4) K)

theorem cP_pow (g : unitarySU p f K 4) (j : ℕ) : cP P (g ^ j) = cP P g ^ j := by
  induction j with
  | zero => rw [pow_zero, pow_zero, cP_one]
  | succ j ih => rw [pow_succ, cP_mul, ih, pow_succ]

theorem thU_eq_of_cP {g g' : unitarySU p f K 4} (hg : cP P g = cP P g') :
    thU p f K g = thU p f K g' := by
  rw [eq_of_cP_eq P hg]

theorem thU_eq_of_cP_neg {g g' : unitarySU p f K 4} (hg : cP P g = -cP P g') :
    thU p f K g = thU p f K g' := by
  have hval : ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
      -((g' : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) := by
    rw [val_eq_cP P g, val_eq_cP P g', hg, Matrix.mul_neg, Matrix.neg_mul]
  have h1 : thU p f K (g'⁻¹ * g) = 1 := thU_eq_one_of_val (c := -1) (by
    rw [Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul, hval, Matrix.mul_neg, ← Units.val_mul,
      inv_mul_cancel, Units.val_one, neg_one_smul])
  rw [map_mul, map_inv, inv_mul_eq_one] at h1
  exact h1.symm

theorem commute_thU_of_cP {g g' : unitarySU p f K 4}
    (hg : cP P g * cP P g' = cP P g' * cP P g) : Commute (thU p f K g) (thU p f K g') := by
  show thU p f K g * thU p f K g' = thU p f K g' * thU p f K g
  rw [← map_mul, ← map_mul]
  exact thU_eq_of_cP P (by rw [cP_mul, cP_mul, hg])

theorem commute_thU_of_cP_neg {g g' : unitarySU p f K 4}
    (hg : cP P g * cP P g' = -(cP P g' * cP P g)) : Commute (thU p f K g) (thU p f K g') := by
  show thU p f K g * thU p f K g' = thU p f K g' * thU p f K g
  rw [← map_mul, ← map_mul]
  exact thU_eq_of_cP_neg P (by rw [cP_mul, cP_mul, hg])

theorem cP_eq_smul_of_mem_scal {g : unitarySU p f K 4} (hg : g ∈ scal p f K) :
    ∃ c : Kˣ, cP P g = (c : K) • 1 := by
  obtain ⟨c, hc⟩ := val_of_mem_scal hg
  refine ⟨c, ?_⟩
  rw [cP, hc, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, ← Units.val_mul, inv_mul_cancel,
    Units.val_one]

theorem cP_of_thU_eq {g g' : unitarySU p f K 4} (hgg : thU p f K g = thU p f K g') :
    ∃ c : Kˣ, cP P g' = (c : K) • cP P g := by
  rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hgg
  obtain ⟨c, hc⟩ := cP_eq_smul_of_mem_scal P hgg
  refine ⟨c, ?_⟩
  rw [show g' = g * (g⁻¹ * g') by group, cP_mul, hc, Matrix.mul_smul, Matrix.mul_one]

theorem cP_of_thU_eq_one {g : unitarySU p f K 4} (hg : thU p f K g = 1) :
    ∃ c : Kˣ, cP P g = (c : K) • 1 := by
  obtain ⟨c, hc⟩ := cP_of_thU_eq P (g := 1) (g' := g) (by rw [map_one, hg])
  exact ⟨c, by rw [hc, cP_one]⟩

theorem thU_ne_one_of_cP {g : unitarySU p f K 4} (h00 : cP P g 0 0 = 0) : thU p f K g ≠ 1 := by
  intro h1
  obtain ⟨c, hc⟩ := cP_of_thU_eq_one P h1
  have := congrFun (congrFun hc 0) 0
  rw [h00, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one] at this
  exact c.ne_zero this.symm

theorem thU_ne_one_of_cP' {g : unitarySU p f K 4} (h01 : cP P g 0 0 ≠ cP P g 1 1) :
    thU p f K g ≠ 1 := by
  intro h1
  obtain ⟨c, hc⟩ := cP_of_thU_eq_one P h1
  apply h01
  rw [hc]
  simp

variable (hP : uStar h (P : Matrix (Fin 4) (Fin 4) K) * (P : Matrix (Fin 4) (Fin 4) K) = stdG)
  {z w : K} (hzw : z * w = 1) (hbz : h.bar z = -z) (hbw : h.bar w = -w)
  {l : K} (hl : l ^ 2 = -1) (hbl : h.bar l = l)

@[expose] noncomputable def mA : unitarySU p f K 4 :=
  hypSU h P hP (aH z w) (unitary_aH h hzw hbz hbw) (det_aH hzw)

@[expose] noncomputable def mT : unitarySU p f K 4 :=
  hypSU h P hP (tH z w) (unitary_tH h hzw hbz hbw) (det_tH hzw)

@[expose] noncomputable def mW : unitarySU p f K 4 := hypSU h P hP Wm (unitary_Wm h) det_Wm

@[expose] noncomputable def mK : unitarySU p f K 4 :=
  hypSU h P hP (kH l) (unitary_kH h hbl hl) (det_kH hl)

theorem cP_mA : cP P (mA h P hP hzw hbz hbw) = aH z w := cP_hypSU h P hP _ _ _

theorem cP_mT : cP P (mT h P hP hzw hbz hbw) = tH z w := cP_hypSU h P hP _ _ _

theorem cP_mW : cP P (mW h P hP) = Wm := cP_hypSU h P hP _ _ _

theorem cP_mK : cP P (mK h P hP hl hbl) = kH l := cP_hypSU h P hP _ _ _

theorem cP_mT_inv : cP P (mT h P hP hzw hbz hbw)⁻¹ = tiH z w :=
  cP_inv_of P (by rw [cP_mT]; exact mul_eq_one_comm.mp (tH_mul_tiH hzw))

theorem cP_mW_inv : cP P (mW h P hP)⁻¹ = -Wm :=
  cP_inv_of P (by rw [cP_mW]; exact neg_Wm_mul_Wm)

theorem cP_conj_mA : cP P ((mT h P hP hzw hbz hbw)⁻¹ * mA h P hP hzw hbz hbw *
    mT h P hP hzw hbz hbw) = apH z w := by
  rw [cP_mul, cP_mul, cP_mT_inv, cP_mA, cP_mT, tiH_aH_tH hzw]

theorem cP_conj_mW : cP P ((mT h P hP hzw hbz hbw)⁻¹ * mW h P hP * mT h P hP hzw hbz hbw) =
    wpH z w := by
  rw [cP_mul, cP_mul, cP_mT_inv, cP_mW, cP_mT, tiH_Wm_tH]

theorem thU_mA_half {m : ℕ} (hm : 2 ≤ m) (hzl : z ^ 2 ^ (m - 1) = l ∨ z ^ 2 ^ (m - 1) = -l) :
    thU p f K (mA h P hP hzw hbz hbw) ^ 2 ^ (m - 1) = thU p f K (mK h P hP hl hbl) := by
  rw [← map_pow]
  have hev : Even (2 ^ (m - 1)) := (Nat.even_pow' (by omega)).mpr even_two
  have hcP : cP P (mA h P hP hzw hbz hbw ^ 2 ^ (m - 1)) =
      dg (z ^ 2 ^ (m - 1)) (w ^ 2 ^ (m - 1)) (w ^ 2 ^ (m - 1)) (z ^ 2 ^ (m - 1)) := by
    rw [cP_pow, cP_mA, aH, dg_pow, hev.neg_pow, hev.neg_pow]
  rcases hzl with hz | hz
  · have hw : w ^ 2 ^ (m - 1) = -l := by
      have h1 : l * w ^ 2 ^ (m - 1) = 1 := by rw [← hz, ← mul_pow, hzw, one_pow]
      linear_combination (-l) * h1 + w ^ 2 ^ (m - 1) * hl
    apply thU_eq_of_cP P
    rw [hcP, hz, hw, cP_mK, kH]
  · have hw : w ^ 2 ^ (m - 1) = l := by
      have h1 : -l * w ^ 2 ^ (m - 1) = 1 := by rw [← hz, ← mul_pow, hzw, one_pow]
      linear_combination l * h1 + w ^ 2 ^ (m - 1) * hl
    apply thU_eq_of_cP_neg P
    rw [hcP, hz, hw, cP_mK, kH, ← dg_neg, neg_neg]

theorem thU_mK_mul : thU p f K (mK h P hP hl hbl) * thU p f K (mK h P hP hl hbl) = 1 := by
  rw [← map_mul, ← map_one (thU p f K)]
  apply thU_eq_of_cP_neg P
  rw [cP_mul, cP_mK, kH_mul_kH hl, cP_one]

theorem thU_mK_ne_one (hp2 : p ≠ 2) : thU p f K (mK h P hP hl hbl) ≠ 1 := by
  apply thU_ne_one_of_cP' P
  rw [cP_mK, kH]
  simp only [dg, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one]
  intro h1
  have hl0 : l ≠ 0 := by
    rintro rfl
    rw [zero_pow (by norm_num)] at hl
    exact one_ne_zero (by linear_combination hl : (1 : K) = 0)
  have h2 : (2 : K) * l = 0 := by linear_combination h1
  exact (mul_ne_zero (two_ne_zero_of_odd h hp2) hl0) h2

include hl hbl in
theorem thU_mA_pow {m : ℕ} (hm : 2 ≤ m) (hzl : z ^ 2 ^ (m - 1) = l ∨ z ^ 2 ^ (m - 1) = -l) :
    thU p f K (mA h P hP hzw hbz hbw) ^ 2 ^ m = 1 := by
  have e : 2 ^ m = 2 ^ (m - 1) * 2 := by
    rw [← pow_succ]
    congr 1
    omega
  rw [e, pow_mul, thU_mA_half h P hP hzw hbz hbw hl hbl hm hzl, sq, thU_mK_mul]

include hl hbl in
theorem orderOf_thU_mA (hp2 : p ≠ 2) {m : ℕ} (hm : 2 ≤ m)
    (hzl : z ^ 2 ^ (m - 1) = l ∨ z ^ 2 ^ (m - 1) = -l) :
    orderOf (thU p f K (mA h P hP hzw hbz hbw)) = 2 ^ m := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have e : m = m - 1 + 1 := by omega
  have h1 := orderOf_eq_prime_pow (p := 2) (x := thU p f K (mA h P hP hzw hbz hbw)) (n := m - 1)
    (by rw [thU_mA_half h P hP hzw hbz hbw hl hbl hm hzl]; exact thU_mK_ne_one h P hP hl hbl hp2)
    (by rw [← e]; exact thU_mA_pow h P hP hzw hbz hbw hl hbl hm hzl)
  rwa [← e] at h1

theorem thU_mW_mul : thU p f K (mW h P hP) * thU p f K (mW h P hP) = 1 := by
  rw [← map_mul, ← map_one (thU p f K)]
  apply thU_eq_of_cP_neg P
  rw [cP_mul, cP_mW, Wm_mul_Wm, cP_one]

theorem thU_mW_conj : thU p f K (mW h P hP) * thU p f K (mA h P hP hzw hbz hbw) *
    (thU p f K (mW h P hP))⁻¹ = (thU p f K (mA h P hP hzw hbz hbw))⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  rw [← map_inv, ← map_mul, ← map_mul, ← map_mul, ← map_one (thU p f K)]
  apply thU_eq_of_cP P
  rw [cP_mul, cP_mul, cP_mul, cP_mW, cP_mA, cP_mW_inv, cP_one, Matrix.mul_neg, Matrix.neg_mul,
    Wm_aH_Wm_aH hzw, neg_neg]

theorem thU_mW_mul_pow_ne_one (i : ℕ) :
    thU p f K (mW h P hP) * thU p f K (mA h P hP hzw hbz hbw) ^ i ≠ 1 := by
  rw [← map_pow, ← map_mul]
  apply thU_ne_one_of_cP P
  rw [cP_mul, cP_mW, cP_pow, cP_mA, aH, dg_pow]
  exact Wm_mul_dg_apply _ _ _ _

theorem iota_eqU {Y : unitarySU p f K 4} (hY : cP P Y = X1 l) :
    thU p f K Y = (thU p f K (mT h P hP hzw hbz hbw))⁻¹ * thU p f K (mK h P hP hl hbl) *
      thU p f K (mT h P hP hzw hbz hbw) := by
  rw [← map_inv, ← map_mul, ← map_mul]
  apply thU_eq_of_cP P
  rw [hY, cP_mul, cP_mul, cP_mT_inv, cP_mK, cP_mT, tiH_kH_tH hzw]

theorem mT_sqU {Y : unitarySU p f K 4} (hY : cP P Y = X1 l) :
    thU p f K (mT h P hP hzw hbz hbw) * thU p f K (mT h P hP hzw hbz hbw) =
      thU p f K Y * thU p f K (mK h P hP hl hbl) := by
  rw [← map_mul, ← map_mul]
  apply thU_eq_of_cP_neg P
  rw [cP_mul, cP_mul, cP_mT, hY, cP_mK]
  exact tH_sq_eq hzw hl

theorem not_conjU (hp2 : p ≠ 2) (hq : p ^ f % 4 = 1) {Y : unitarySU p f K 4}
    (hY : cP P Y = X1 l) (g : StatedProj (StatedSU 4 (p ^ f) K)) :
    g * thU p f K Y * g⁻¹ ≠ thU p f K Y * thU p f K (mK h P hP hl hbl) := by
  intro hg
  obtain ⟨G, rfl⟩ := thU_surjective g
  rw [← map_inv, ← map_mul, ← map_mul, ← map_mul, QuotientGroup.mk'_apply,
    QuotientGroup.mk'_apply, QuotientGroup.eq] at hg
  obtain ⟨c, hc⟩ := val_of_mem_scal hg
  have hbc : h.bar (c : K) * c = 1 := by
    have hu := ((mem_unitarySU_iff h).1 ((G * Y * G⁻¹)⁻¹ * (Y * mK h P hP hl hbl)).2).2
    rw [hc] at hu
    have := congrFun (congrFun hu 0) 0
    simpa [Matrix.mul_apply, Fin.sum_univ_four] using this
  have hcs : cP P ((G * Y * G⁻¹)⁻¹ * (Y * mK h P hP hl hbl)) = (c : K) • 1 := by
    rw [cP, hc, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, ← Units.val_mul, inv_mul_cancel,
      Units.val_one]
  have hYK : cP P (Y * mK h P hP hl hbl) = (c : K) • cP P (G * Y * G⁻¹) := by
    rw [show Y * mK h P hP hl hbl =
        (G * Y * G⁻¹) * ((G * Y * G⁻¹)⁻¹ * (Y * mK h P hP hl hbl)) by group,
      cP_mul, hcs, Matrix.mul_smul, Matrix.mul_one]
  have hX2 : cP P (G * Y * G⁻¹) * cP P (G * Y * G⁻¹) = -1 := by
    rw [← cP_mul, show G * Y * G⁻¹ * (G * Y * G⁻¹) = G * (Y * Y) * G⁻¹ by group, cP_mul,
      cP_mul, cP_mul, hY, X1_mul_X1 hl, Matrix.mul_neg, Matrix.mul_one, Matrix.neg_mul,
      ← cP_mul, mul_inv_cancel, cP_one]
  have hY2 : cP P (Y * mK h P hP hl hbl) * cP P (Y * mK h P hP hl hbl) = 1 := by
    rw [cP_mul, hY, cP_mK]
    exact X1_kH_sq hl
  have key : cP P (Y * mK h P hP hl hbl) * cP P (Y * mK h P hP hl hbl) =
      -(((c : K) * c) • (1 : Matrix (Fin 4) (Fin 4) K)) := by
    rw [hYK, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hX2, smul_neg]
  rw [hY2] at key
  have h00 := congrFun (congrFun key 0) 0
  simp only [Matrix.one_apply_eq, Matrix.neg_apply, Matrix.smul_apply, smul_eq_mul,
    mul_one] at h00
  have hcc : (c : K) * c = -1 := by linear_combination h00
  have hbc' : h.bar (c : K) = c := by
    rw [h.bar_apply]
    obtain ⟨s, hs⟩ : ∃ s, p ^ f = 4 * s + 1 := ⟨p ^ f / 4, by omega⟩
    rw [hs, pow_succ, pow_mul,
      show (c : K) ^ 4 = 1 by linear_combination ((c : K) * c - 1) * hcc, one_pow, one_mul]
  rw [hbc', hcc] at hbc
  exact two_ne_zero_of_odd h hp2 (by linear_combination -hbc)

end U4M

end CFSG.ComponentClassification.GSThmB.P29
