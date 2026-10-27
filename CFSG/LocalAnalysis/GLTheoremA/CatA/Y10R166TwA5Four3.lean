module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R166SUBlocks3
public import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotLeviFactSU
public import CFSG.Timmesfeld.Bridge.RootStructR2Torus
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.RankThree.PartTwo.Sec19.Census194.RonanC194OmegaTorus
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels
public import CFSG.Yardstones.Md0ec50421ce4.Definitions

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F

namespace TwA5Four

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.SeitzReduction.UnitaryPilot CFSG.SeitzReduction.LinearPilot
open Matrix

variable {F : Type} [Field F]

theorem unitaryNorm_eq_one_of_pow_five {h : UnitaryFieldData 2 2 F} {z : F}
    (hz : z ^ 5 = 1) : h.norm z = 1 := by
  rw [h.norm_eq_pow]
  norm_num
  exact hz

theorem val_pow_five_of_mem_rootsOfUnity {z : rootsOfUnity 5 F} :
    (((z : Fˣ) : F)) ^ 5 = 1 := by
  have hz : ((z : rootsOfUnity 5 F) : Fˣ) ^ 5 = 1 :=
    (mem_rootsOfUnity 5 ((z : rootsOfUnity 5 F) : Fˣ)).1 z.2
  have h := congrArg (fun u : Fˣ => (u : F)) hz
  simpa [Units.val_pow_eq_pow_val] using h

theorem card_rootsOfUnity_five {h : UnitaryFieldData 2 2 F} :
    Nat.card (rootsOfUnity 5 F) = 5 := by
  haveI := h.finite
  have hK : Nat.card F = 16 := by
    rw [h.card]; norm_num
  have hcard : Nat.card Fˣ = 15 := by
    rw [Nat.card_units, hK]
  have hdvd : 5 ∣ Nat.card Fˣ := by rw [hcard]; norm_num
  exact CFSG.RankThree.PartTwo.Sec19.Census194.RonanC194.OmegaEven.card_rootsOfUnity_of_dvd'
    Nat.prime_five hdvd

@[expose] noncomputable def rootsOfUnityOfNormOne {h : UnitaryFieldData 2 2 F} (u : Fˣ)
    (hu : h.norm (u : F) = 1) : rootsOfUnity 5 F :=
  ⟨u, by
    rw [mem_rootsOfUnity]
    apply Units.ext
    rw [Units.val_pow_eq_pow_val]
    rw [h.norm_eq_pow] at hu
    norm_num at hu
    exact hu⟩

@[simp]
theorem coe_rootsOfUnityOfNormOne {h : UnitaryFieldData 2 2 F} (u : Fˣ)
    (hu : h.norm (u : F) = 1) :
    ((rootsOfUnityOfNormOne u hu : rootsOfUnity 5 F) : Fˣ) = u := rfl

private noncomputable def torusParamFourHome {h : UnitaryFieldData 2 2 F}
    (c : unitaryTorusParam h ({0, 1} : Finset (Fin 6))) : Fin 4 → rootsOfUnity 5 F :=
  fun i =>
    match i with
    | 0 => rootsOfUnityOfNormOne (c.1 0) (c.2.1 0)
    | 1 => rootsOfUnityOfNormOne (c.1 2) (c.2.1 2)
    | 2 => rootsOfUnityOfNormOne (c.1 3) (c.2.1 3)
    | 3 => rootsOfUnityOfNormOne (c.1 4) (c.2.1 4)

@[expose] noncomputable def torusParamFourInv {h : UnitaryFieldData 2 2 F}
    (v : Fin 4 → rootsOfUnity 5 F) : unitaryTorusParam h ({0, 1} : Finset (Fin 6)) :=
  let a : Fˣ := ((v 0 : rootsOfUnity 5 F) : Fˣ)
  let b : Fˣ := ((v 1 : rootsOfUnity 5 F) : Fˣ)
  let c : Fˣ := ((v 2 : rootsOfUnity 5 F) : Fˣ)
  let d : Fˣ := ((v 3 : rootsOfUnity 5 F) : Fˣ)
  let e : Fin 6 → Fˣ :=
    ![a, a, b, c, d, (a ^ 2 * b * c * d)⁻¹]
  have ha : h.norm ((a : Fˣ) : F) = 1 :=
    unitaryNorm_eq_one_of_pow_five (val_pow_five_of_mem_rootsOfUnity (z := v 0))
  have hb : h.norm ((b : Fˣ) : F) = 1 :=
    unitaryNorm_eq_one_of_pow_five (val_pow_five_of_mem_rootsOfUnity (z := v 1))
  have hc : h.norm ((c : Fˣ) : F) = 1 :=
    unitaryNorm_eq_one_of_pow_five (val_pow_five_of_mem_rootsOfUnity (z := v 2))
  have hd : h.norm ((d : Fˣ) : F) = 1 :=
    unitaryNorm_eq_one_of_pow_five (val_pow_five_of_mem_rootsOfUnity (z := v 3))
  have ha2 : h.norm ((((a : Fˣ) : F)) ^ 2) = 1 := by
    rw [pow_two, CFSG.ClassicalGroups.UnitaryFlag.norm_mul_eq h, ha, one_mul]
  ⟨e, by
    refine ⟨?_, ?_, ?_⟩
    · intro i
      fin_cases i <;>
        simp [e, ha, hb, hc, hd, ha2,
          CFSG.ClassicalGroups.UnitaryFlag.norm_mul_eq h,
          CFSG.ClassicalGroups.UnitaryFlag.norm_inv_eq h]
    · rw [Fin.prod_univ_six]
      dsimp only [e]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.cons_val_three, Matrix.cons_val_fin_one, Matrix.head_cons, Matrix.tail_cons,
        Fin.reduceFinMk]
      change a * a * b * c * d * (a ^ 2 * b * c * d)⁻¹ = 1
      simpa [pow_two] using mul_inv_cancel (a * a * b * c * d)

    · intro i hi j hj
      simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj
      rcases hi with rfl | rfl <;> rcases hj with rfl | rfl <;> rfl⟩

private noncomputable def torusParamFourEquiv {h : UnitaryFieldData 2 2 F} :
    unitaryTorusParam h ({0, 1} : Finset (Fin 6)) ≃ (Fin 4 → rootsOfUnity 5 F) where
  toFun := torusParamFourHome
  invFun := torusParamFourInv
  left_inv c := by
    apply Subtype.ext
    funext i
    have h01 : c.1 1 = c.1 0 := c.2.2.2 1 (by simp) 0 (by simp)
    have hprod := c.2.2.1
    rw [Fin.prod_univ_six] at hprod
    have hc : c.1 0 * c.1 0 * c.1 2 * c.1 3 * c.1 4 * c.1 5 = 1 := by
      simpa [h01, mul_assoc, mul_comm, mul_left_comm] using hprod
    have hA : c.1 5 = (c.1 0 ^ 2 * c.1 2 * c.1 3 * c.1 4)⁻¹ :=
      eq_inv_of_mul_eq_one_right (by
        simpa [pow_two, mul_assoc, mul_comm, mul_left_comm] using hc)
    fin_cases i
    · simp [torusParamFourInv, torusParamFourHome]
    · simp [torusParamFourInv, torusParamFourHome, h01]
    · simp [torusParamFourInv, torusParamFourHome]
    · simp [torusParamFourInv, torusParamFourHome]
    · simp [torusParamFourInv, torusParamFourHome]
    · simp [torusParamFourInv, torusParamFourHome, hA]

  right_inv v := by
    funext i
    fin_cases i <;> rfl

theorem card_unitaryTorusParam_two {h : UnitaryFieldData 2 2 F} :
    Nat.card (unitaryTorusParam h ({0, 1} : Finset (Fin 6))) = 5 ^ 4 := by
  rw [Nat.card_congr (torusParamFourEquiv (h := h)), Nat.card_fun, Nat.card_fin,
    card_rootsOfUnity_five (h := h)]

theorem torusDiagSU_injective (h : UnitaryFieldData 2 2 F) :
    Function.Injective (torusDiagSU (h := h) (n := 6)) := by
  intro c d hcd
  have hmat := congrArg (fun A : unitarySU 2 2 F 6 =>
    (((A : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F))) hcd
  simp only [coe_torusDiagSU] at hmat
  apply Subtype.ext
  funext i
  have hdiag : ((c.1 i : Fˣ) : F) = ((d.1 i : Fˣ) : F) := by
    have := congrFun (congrFun hmat i) i
    simpa [Matrix.diagonal_apply] using this
  exact Units.ext hdiag

theorem card_unitaryTorusSU_two (h : UnitaryFieldData 2 2 F) :
    Nat.card (unitaryTorusSU h ({0, 1} : Finset (Fin 6))) = 5 ^ 4 := by
  rw [unitaryTorusSU, Subgroup.card_map_of_injective (torusDiagSU_injective h),
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (unitaryTorusParam_anti h (by simp : (∅ : Finset (Fin 6)) ⊆ {0, 1}))).toEquiv]
  exact card_unitaryTorusParam_two (h := h)

theorem isElemAbelian_unitaryTorusSU_two (h : UnitaryFieldData 2 2 F) :
    IsElemAbelian 5 (unitaryTorusSU h ({0, 1} : Finset (Fin 6))) := by
  constructor
  · refine ⟨⟨fun A B => ?_⟩⟩
    obtain ⟨c, hc, hcA⟩ := (mem_unitaryTorusSU h).1 A.2
    obtain ⟨d, hd, hdA⟩ := (mem_unitaryTorusSU h).1 B.2
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hcA, ← hdA, ← map_mul, ← map_mul]
    congr 1
    exact mul_comm _ _
  · intro A hA
    obtain ⟨c, hc, hcA⟩ := (mem_unitaryTorusSU h).1 hA
    rw [← hcA]
    have hc5 : c ^ 5 = 1 := by
      apply Subtype.ext
      funext i
      apply Units.ext
      have hu : h.norm ((c.1 i : Fˣ) : F) = 1 := c.2.1 i
      have h5 : (((c.1 i : Fˣ) : F)) ^ 5 = 1 := by
        rw [h.norm_eq_pow] at hu
        norm_num at hu
        exact hu
      simpa [Units.val_pow_eq_pow_val] using h5
    rw [← map_pow, hc5, map_one]

section Zeta

variable {h : UnitaryFieldData 2 2 F} {ζu : Fˣ} (hζu : orderOf ζu = 5)

include hζu

theorem zeta_pow_five : (ζu : Fˣ) ^ 5 = 1 := by
  rw [← hζu]
  exact pow_orderOf_eq_one ζu

theorem norm_zeta : h.norm ((ζu : Fˣ) : F) = 1 :=
  unitaryNorm_eq_one_of_pow_five (by
    have h := zeta_pow_five hζu
    simpa [Units.val_pow_eq_pow_val] using congrArg (fun u : Fˣ => (u : F)) h)

theorem zeta_ne_one : (ζu : Fˣ) ≠ 1 := by
  intro h1
  have h := hζu
  rw [h1, orderOf_one] at h
  omega

@[expose] noncomputable def diagFiveParam (hζu : orderOf ζu = 5) :
    unitaryTorusParam h (∅ : Finset (Fin 6)) where
  val := ![ζu, ζu, ζu, ζu, ζu, 1]
  property := by
    have hz5 : (((ζu : Fˣ) : F)) ^ 5 = 1 := by
      simpa [Units.val_pow_eq_pow_val] using
        congrArg (fun u : Fˣ => (u : F)) (zeta_pow_five hζu)
    refine ⟨?_, ?_, ?_⟩
    · intro i
      fin_cases i <;> simp [h.norm_eq_pow, hz5, zeta_pow_five hζu]
    · rw [Fin.prod_univ_six]
      change ζu * ζu * ζu * ζu * ζu * 1 = 1
      rw [mul_one]
      have h := zeta_pow_five hζu
      simpa [pow_succ, pow_two, mul_assoc, mul_comm, mul_left_comm] using h
    · intro i hi j hj; simp at hi

private theorem mem_diagFiveParam_I : (diagFiveParam (h := h) hζu).1 ∈
    unitaryTorusParam h ({0, 1} : Finset (Fin 6)) := by
  refine ⟨(diagFiveParam (h := h) hζu).2.1, (diagFiveParam (h := h) hζu).2.2.1, ?_⟩
  intro i hi j hj
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj
  rcases hi with rfl | rfl <;> rcases hj with rfl | rfl <;> rfl

theorem diagFiveLast_mem_unitaryTorusSU :
    diagFiveLast h (ζu : Fˣ) (norm_zeta hζu) ∈
      unitaryTorusSU h ({0, 1} : Finset (Fin 6)) := by
  have hz5 : (((ζu : Fˣ) : F)) ^ 5 = 1 := by
    simpa [Units.val_pow_eq_pow_val] using
      congrArg (fun u : Fˣ => (u : F)) (zeta_pow_five hζu)
  refine (mem_unitaryTorusSU h).2 ⟨diagFiveParam hζu, mem_diagFiveParam_I hζu, ?_⟩
  apply Subtype.ext
  apply Units.ext
  rw [coe_torusDiagSU, coe_diagFiveLast]
  ext i j
  by_cases hij : i = j
  · subst hij
    simp only [Matrix.diagonal_apply, if_pos rfl]
    by_cases hi : i = (5 : Fin 6)
    · subst hi
      simp only [diagFiveLastEntries, if_pos rfl]
      change (1 : F) = ((((ζu : Fˣ) : F)) ^ 5)⁻¹
      rw [hz5, inv_one]
    · fin_cases i
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · exact absurd rfl hi
  · simp only [Matrix.diagonal_apply, if_neg hij]

theorem diagFiveLast_ne_one : diagFiveLast h (ζu : Fˣ) (norm_zeta hζu) ≠ 1 := by
  intro h1
  have hmat := congrArg (fun A : unitarySU 2 2 F 6 =>
    (((A : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F))) h1
  rw [coe_diagFiveLast] at hmat
  have h00 := congrFun (congrFun hmat 0) 0
  simp [Matrix.diagonal_apply, diagFiveLastEntries, zeta_ne_one hζu] at h00

theorem exists_diag_of_mem_unitaryTorusSU {A : unitarySU 2 2 F 6}
    (hA : A ∈ unitaryTorusSU h ({0, 1} : Finset (Fin 6))) :
    ∃ (d : Fin 6 → F) (hd : ∀ i, h.norm (d i) = 1) (hdet : ∏ i, d i = 1) (n : ℕ),
      A = diagSU h d hd hdet ∧ d 0 = d 1 ∧ d 0 = ((ζu ^ n : Fˣ) : F) := by
  obtain ⟨c, hc, rfl⟩ := (mem_unitaryTorusSU h).1 hA
  haveI := h.finite
  have hc0 : c.1 0 ∈ rootsOfUnity 5 F :=
    (rootsOfUnityOfNormOne (c.1 0) (c.2.1 0)).2
  have hzmem : ζu ∈ rootsOfUnity 5 F := by
    rw [mem_rootsOfUnity]
    exact zeta_pow_five hζu
  have heq : Subgroup.zpowers ζu = rootsOfUnity 5 F := by
    refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 hzmem) ?_
    rw [Nat.card_zpowers, hζu, card_rootsOfUnity_five (h := h)]
  have hc0mem : c.1 0 ∈ Subgroup.zpowers ζu := by rw [heq]; exact hc0
  obtain ⟨n, hn⟩ := CFSG.Timmesfeld.Bridge.exists_pow_eq_of_mem_zpowers hc0mem
  refine ⟨fun i => (c.1 i : F), c.2.1, ?_, n, rfl, ?_, ?_⟩
  · rw [← Units.coe_prod, c.2.2.1, Units.val_one]
  · exact congrArg (fun u : Fˣ => (u : F)) (hc.2.2 0 (by simp) 1 (by simp))
  · simpa using congrArg (fun u : Fˣ => (u : F)) hn.symm

theorem unitaryTorusSU_le_normalizer_lineRadical :
    unitaryTorusSU h ({0, 1} : Finset (Fin 6)) ≤
      Subgroup.normalizer (unitaryLineRadical h : Set (unitarySU 2 2 F 6)) := by
  rintro A hA
  obtain ⟨d, hd, hdet, -, rfl, hd0, -⟩ := exists_diag_of_mem_unitaryTorusSU hζu hA
  exact diagSU_mem_normalizer_unitaryLineRadical h hd hdet hd0

theorem inf_centralizer_lineRadical_eq_zpowers :
    unitaryTorusSU h ({0, 1} : Finset (Fin 6)) ⊓
        Subgroup.centralizer (unitaryLineRadical h : Set (unitarySU 2 2 F 6)) =
      Subgroup.zpowers (diagFiveLast h (ζu : Fˣ) (norm_zeta hζu)) := by
  refine le_antisymm ?_ ?_
  · exact inf_centralizer_unitaryLineRadical_le_zpowers h (norm_zeta hζu)
      (fun A hA => exists_diag_of_mem_unitaryTorusSU hζu hA)
  · rintro z hz
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz
    refine ⟨?_, ?_⟩
    ·
      exact Subgroup.zpow_mem _ (diagFiveLast_mem_unitaryTorusSU hζu) k
    · refine Subgroup.mem_centralizer_iff.2 ?_
      intro s hs
      have hSJ : s ∈ unitaryBlock h ({0, 1, 2, 3, 4} : Finset (Fin 6)) := by
        have := unitaryLineRadical_le_unitaryBlock (h := h) hs
        simpa [show ((Finset.univ : Finset (Fin 6)).erase 5) = ({0, 1, 2, 3, 4} : Finset (Fin 6))
          from by decide] using this
      have hC := centralizer_diagFiveLast (h := h) (norm_zeta hζu) (by
        intro h6
        have h6' : ((ζu : Fˣ) : F) ^ 5 * ((ζu : Fˣ) : F) = 1 := by
          simpa [pow_succ] using h6
        rw [show (((ζu : Fˣ) : F) ^ 5) = 1 from by
          simpa [Units.val_pow_eq_pow_val] using congrArg (fun u : Fˣ => (u : F))
            (zeta_pow_five hζu), one_mul] at h6'
        exact zeta_ne_one hζu (Units.ext h6'))
      have hmem : s ∈ Subgroup.centralizer
          ({diagFiveLast h (ζu : Fˣ) (norm_zeta hζu)} : Set (unitarySU 2 2 F 6)) := by
        rw [hC]
        exact unitaryBlock_le_unitaryBlockDiag h _ hSJ
      have hcomm : Commute s (diagFiveLast h (ζu : Fˣ) (norm_zeta hζu)) :=
        Subgroup.mem_centralizer_singleton_iff.1 hmem
      exact Commute.zpow_right hcomm k

end Zeta


section TorusParamFourApply

variable {h : UnitaryFieldData 2 2 F}

@[simp] theorem torusParamFourInv_apply_zero (v : Fin 4 → rootsOfUnity 5 F) :
    (torusParamFourInv (h := h) v).1 0 = (v 0 : Fˣ) := rfl

@[simp] theorem torusParamFourInv_apply_one (v : Fin 4 → rootsOfUnity 5 F) :
    (torusParamFourInv (h := h) v).1 1 = (v 0 : Fˣ) := rfl

@[simp] theorem torusParamFourInv_apply_two (v : Fin 4 → rootsOfUnity 5 F) :
    (torusParamFourInv (h := h) v).1 2 = (v 1 : Fˣ) := rfl

@[simp] theorem torusParamFourInv_apply_three (v : Fin 4 → rootsOfUnity 5 F) :
    (torusParamFourInv (h := h) v).1 3 = (v 2 : Fˣ) := rfl

@[simp] theorem torusParamFourInv_apply_four (v : Fin 4 → rootsOfUnity 5 F) :
    (torusParamFourInv (h := h) v).1 4 = (v 3 : Fˣ) := rfl

@[simp] theorem torusParamFourInv_apply_five (v : Fin 4 → rootsOfUnity 5 F) :
    (torusParamFourInv (h := h) v).1 5 =
      (((v 0 : Fˣ) ^ 2 * (v 1 : Fˣ) * (v 2 : Fˣ) * (v 3 : Fˣ))⁻¹) := rfl

end TorusParamFourApply

end TwA5Four

end CFSG.LocalAnalysis.GLTheoremA.Y10F
