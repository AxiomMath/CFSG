module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD1912Core
public import CFSG.LocalAnalysis.GLTheoremA.PartI.LevelLieU4E6
public import CFSG.Quasithin.Vol2.GoldschmidtTDOutAbs
public import CFSG.GroupTheory.PCore.SelfCentralizing
public import CFSG.GroupTheory.PCore.QuasisimpleNormalCore
public import CFSG.GroupTheory.PCore.FixedSubgroupCore
public import CFSG.GroupTheory.CenterlessInnerCentralizer
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHeldSmallCoreLinear
public import CFSG.Monster.B.Fischer.Fi22Order
public import CFSG.RankThree.PartTwo.Sec4.Item47Unitary

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD1912

open CFSG.Open
open CFSG.HardMathSupport.Solomon.LocalBalance
open CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIVU48
open CFSG.RankThree.PartTwo.KFacts.KS21.U58 (K hK card_K card_units_K card_ringAut_K)
open CFSG.LocalAnalysis.GLTheoremA.LevelLieU4E
open CFSG.LocalAnalysis.GLTheoremA.CatB.U48
open CFSG.LieType.Universal.Unitary
open Matrix

private theorem exists_isPrimitiveRoot_three : ∃ ζ : K, IsPrimitiveRoot ζ 3 := by
  have h3 : 3 ∣ Nat.card Kˣ := by rw [card_units_K]; norm_num
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := Kˣ) 3 h3
  refine ⟨(x : K), IsPrimitiveRoot.iff_orderOf.mpr ?_⟩
  change orderOf ((Units.coeHom K) x) = 3
  rw [orderOf_injective (Units.coeHom K) Units.val_injective x, hx]

private noncomputable abbrev C211 (ζ : K) (hζ : IsPrimitiveRoot ζ 3) : Subgroup SU4 :=
  Subgroup.centralizer ({c211 ζ hζ} : Set SU4)

private noncomputable abbrev C022 (ζ : K) (hζ : IsPrimitiveRoot ζ 3) : Subgroup SU4 :=
  Subgroup.centralizer ({c022 ζ hζ} : Set SU4)

private theorem diagChar_pow_nine {c : SU4} {d : Fin 4 → K} (hc : mat c = diagonal d)
    {k : Fin 4} (hk : ∀ j, j ≠ k → d j ≠ d k)
    (x : ↥(Subgroup.centralizer ({c} : Set SU4))) :
    (diagChar hc hk x) ^ 9 = 1 := by
  have hU : conjTr σ4 (mat (x : SU4)) * mat (x : SU4) = 1 :=
    (LieType.Universal.Unitary.mem_SUid.1 (x : SU4).2).2
  have hz : ∀ j : Fin 4, j ≠ k → mat (x : SU4) j k = 0 := fun j hj =>
    entry_zero_of_mem_centralizer hc x.2 (hk j hj)
  have hsum : (∑ j : Fin 4, conjTr σ4 (mat (x : SU4)) k j * mat (x : SU4) j k) =
      conjTr σ4 (mat (x : SU4)) k k * mat (x : SU4) k k := by
    refine Finset.sum_eq_single k ?_ ?_
    · intro j _ hj
      rw [hz j hj, mul_zero]
    · intro h
      exact absurd (Finset.mem_univ k) h
  have hkk : conjTr σ4 (mat (x : SU4)) k k * mat (x : SU4) k k = 1 := by
    have h := congrFun (congrFun hU k) k
    simpa [Matrix.mul_apply, hsum] using h
  have h8 : conjTr σ4 (mat (x : SU4)) k k = (mat (x : SU4) k k) ^ 8 := by
    rw [conjTr, Matrix.transpose_apply]
    change σ4 (mat (x : SU4) k k) = (mat (x : SU4) k k) ^ 8
    rw [CFSG.LieType.BorelTits.unitaryInvolution_apply]
    norm_num
  rw [h8] at hkk
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, Units.val_one]
  show (mat (x : SU4) k k) ^ 9 = 1
  calc (mat (x : SU4) k k) ^ 9 = (mat (x : SU4) k k) ^ 8 * mat (x : SU4) k k := by ring
    _ = 1 := hkk

private noncomputable abbrev char211 (ζ : K) (hζ : IsPrimitiveRoot ζ 3) :
    ↥(C211 ζ hζ) →* Kˣ × Kˣ :=
  (diagChar (mat_c211 ζ hζ) (c211_eig_ne ζ hζ).1).prod
    (diagChar (mat_c211 ζ hζ) (c211_eig_ne ζ hζ).2)

private theorem char211_ker (ζ : K) (hζ : IsPrimitiveRoot ζ 3) :
    (char211 ζ hζ).ker = W0.subgroupOf (C211 ζ hζ) := by
  ext x
  constructor
  · intro hx
    rw [Subgroup.mem_subgroupOf]
    have hx2 : mat (x : SU4) 2 2 = 1 := by
      have h2 : diagChar (mat_c211 ζ hζ) (c211_eig_ne ζ hζ).1 x = 1 := by
        simpa using congrArg Prod.fst hx
      have := congrArg (fun u : Kˣ => (u : K)) h2
      simpa [diagChar] using this
    have hx3 : mat (x : SU4) 3 3 = 1 := by
      have h3 : diagChar (mat_c211 ζ hζ) (c211_eig_ne ζ hζ).2 x = 1 := by
        simpa using congrArg Prod.snd hx
      have := congrArg (fun u : Kˣ => (u : K)) h3
      simpa [diagChar] using this
    rw [mem_W0_iff]
    constructor
    · funext i
      rw [smul_single_eq, Pi.single_apply]
      by_cases hi : i = 2
      · subst hi
        rw [hx2, if_pos rfl]
      · rw [entry_zero_of_mem_centralizer (mat_c211 ζ hζ) x.2 ((c211_eig_ne ζ hζ).1 i hi),
          if_neg hi]
    · funext i
      rw [smul_single_eq, Pi.single_apply]
      by_cases hi : i = 3
      · subst hi
        rw [hx3, if_pos rfl]
      · rw [entry_zero_of_mem_centralizer (mat_c211 ζ hζ) x.2 ((c211_eig_ne ζ hζ).2 i hi),
          if_neg hi]
  · intro hx
    rw [Subgroup.mem_subgroupOf] at hx
    obtain ⟨h2, h3⟩ := (mem_W0_iff (x : SU4)).1 hx
    have e2 : mat (x : SU4) 2 2 = 1 := by
      have := congrFun h2 2
      rwa [smul_single_eq, Pi.single_apply, if_pos rfl] at this
    have e3 : mat (x : SU4) 3 3 = 1 := by
      have := congrFun h3 3
      rwa [smul_single_eq, Pi.single_apply, if_pos rfl] at this
    apply Prod.ext
    · apply Units.ext
      simpa [char211, diagChar] using e2
    · apply Units.ext
      simpa [char211, diagChar] using e3

private theorem char211_range_pow_nine (ζ : K) (hζ : IsPrimitiveRoot ζ 3)
    (y : ↥(char211 ζ hζ).range) : (y : Kˣ × Kˣ) ^ 9 = 1 := by
  obtain ⟨x, hx⟩ := y.2
  rw [← hx]
  apply Prod.ext
  · simpa [char211] using diagChar_pow_nine (mat_c211 ζ hζ) (c211_eig_ne ζ hζ).1 x
  · simpa [char211] using diagChar_pow_nine (mat_c211 ζ hζ) (c211_eig_ne ζ hζ).2 x

private theorem odd_card_char211_range (ζ : K) (hζ : IsPrimitiveRoot ζ 3) :
    Odd (Nat.card ↥(char211 ζ hζ).range) := by
  have hexp : ∀ y : ↥(char211 ζ hζ).range, y ^ 9 = 1 := by
    intro y
    apply Subtype.ext
    simpa using char211_range_pow_nine ζ hζ y
  have hpg : IsPGroup 3 ↥(char211 ζ hζ).range := by
    intro y
    exact ⟨2, by simpa using hexp y⟩
  obtain ⟨n, hn⟩ :=
    (isPGroup_iff_card_dvd_pow (p := 3) (G := ↥(char211 ζ hζ).range)).1 hpg
  exact (Odd.pow (by norm_num : Odd 3)).of_dvd_nat hn

private theorem relIndex_W0_C211 (ζ : K) (hζ : IsPrimitiveRoot ζ 3) :
    W0.relIndex (C211 ζ hζ) =
      Nat.card ↥(char211 ζ hζ).range := by
  show Nat.card (C211 ζ hζ ⧸ W0.subgroupOf (C211 ζ hζ)) = _
  rw [← char211_ker ζ hζ]
  exact Nat.card_congr (QuotientGroup.quotientKerEquivRange (char211 ζ hζ)).toEquiv

private theorem odd_card_gLAPPrimeCoreOf_C211 (ζ : K) (hζ : IsPrimitiveRoot ζ 3) :
    Odd (Nat.card (GLAPPrimeCoreOf 3 (C211 ζ hζ))) := by
  have hW0le : W0 ≤ C211 ζ hζ := W0_le_centralizer_c211 ζ hζ
  have hW0n : (W0.subgroupOf (C211 ζ hζ)).Normal := by
    rw [← char211_ker ζ hζ]
    exact MonoidHom.normal_ker _
  have hi : Odd (W0.relIndex (C211 ζ hζ)) := by
    rw [relIndex_W0_C211 ζ hζ]
    exact odd_card_char211_range ζ hζ
  have hW0core : Odd (Nat.card (GLAPPrimeCoreOf 3 W0)) := by
    have hbot : GLAPPrimeCoreOf 3 W0 = ⊥ :=
      (gLAPPrimeCoreOf_eq_bot_iff_pPrimeCore).mpr
        (gLAPPrimeCore_eq_bot_of_isSimpleGroup_of_dvd_card Nat.prime_three
          isSimpleGroup_W0 three_dvd_W0)
    rw [hbot, Subgroup.card_bot]
    exact odd_one
  exact odd_card_gLAPPrimeCoreOf_of_odd_relIndex hW0le hW0n hi hW0core

private theorem blkA_eq_one_of_mem_W1 {x : SU4} (hx : x ∈ W1) : blkA x = 1 := by
  obtain ⟨h0, h1⟩ := (mem_W1_iff x).1 hx
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [blkA, row_of_fix x 0 h0, row_of_fix x 1 h1]

private theorem W1_le_KA (ζ : K) (hζ : IsPrimitiveRoot ζ 3) : W1 ≤ KA ζ hζ := by
  intro w hw
  refine ⟨W1_le_centralizer_c022 ζ hζ hw, ?_⟩
  rw [blkA_eq_one_of_mem_W1 hw, Matrix.det_one]

private theorem piA_eq_one_of_mem_W1 (ζ : K) (hζ : IsPrimitiveRoot ζ 3)
    {y : KA ζ hζ} (hy : (y : SU4) ∈ W1) : piA ζ hζ y = 1 := by
  have hb : blkA (y : SU4) = 1 := blkA_eq_one_of_mem_W1 hy
  have hθ : thetaA ζ hζ y = 1 := by
    apply Subtype.ext
    apply Units.ext
    exact hb
  show (CFSG.ClassicalInvolution.Phan.blockEmb K 2 3 4 2 0 (by norm_num))
      (thetaA ζ hζ y) = 1
  rw [hθ, map_one]

private theorem piA_ker_eq (ζ : K) (hζ : IsPrimitiveRoot ζ 3) :
    (piA ζ hζ).ker = W1.subgroupOf (KA ζ hζ) := by
  ext y
  rw [Subgroup.mem_subgroupOf]
  constructor
  · intro hy
    exact piA_ker y hy
  · intro hy
    rw [MonoidHom.mem_ker]
    exact piA_eq_one_of_mem_W1 ζ hζ hy

private theorem detA_pow_nine (ζ : K) (hζ : IsPrimitiveRoot ζ 3) (x : ↥(C022 ζ hζ)) :
    (detA ζ hζ x) ^ 9 = 1 := by
  have hU := blkA_unitary (ζ := ζ) (hζ := hζ) x.2
  have hdet := congrArg Matrix.det hU
  rw [Matrix.det_mul, Matrix.det_one] at hdet
  have hconj : (conjTr σ4 (blkA (x : SU4))).det = σ4 ((blkA (x : SU4)).det) := by
    rw [conjTr, Matrix.det_transpose]
    exact (RingEquiv.map_det σ4 ((blkA (x : SU4)))).symm
  rw [hconj, CFSG.LieType.BorelTits.unitaryInvolution_apply] at hdet
  have h9 : (blkA (x : SU4)).det ^ 9 = 1 := by
    calc (blkA (x : SU4)).det ^ 9 = (blkA (x : SU4)).det ^ 8 * (blkA (x : SU4)).det := by ring
      _ = 1 := hdet
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, Units.val_one]
  show (blkA (x : SU4)).det ^ 9 = 1
  exact h9

private theorem detA_range_pow_nine (ζ : K) (hζ : IsPrimitiveRoot ζ 3)
    (y : ↥(detA ζ hζ).range) : (y : Kˣ) ^ 9 = 1 := by
  obtain ⟨x, hx⟩ := y.2
  rw [← hx]
  exact detA_pow_nine ζ hζ x

private theorem odd_card_detA_range (ζ : K) (hζ : IsPrimitiveRoot ζ 3) :
    Odd (Nat.card ↥(detA ζ hζ).range) := by
  have hexp : ∀ y : ↥(detA ζ hζ).range, y ^ 9 = 1 := by
    intro y
    apply Subtype.ext
    simpa using detA_range_pow_nine ζ hζ y
  have hpg : IsPGroup 3 ↥(detA ζ hζ).range := by
    intro y
    exact ⟨2, by simpa using hexp y⟩
  obtain ⟨n, hn⟩ :=
    (isPGroup_iff_card_dvd_pow (p := 3) (G := ↥(detA ζ hζ).range)).1 hpg
  exact (Odd.pow (by norm_num : Odd 3)).of_dvd_nat hn

private theorem detA_ker_eq (ζ : K) (hζ : IsPrimitiveRoot ζ 3) :
    (detA ζ hζ).ker = (KA ζ hζ).subgroupOf (C022 ζ hζ) := by
  ext x
  constructor
  · intro hx
    rw [Subgroup.mem_subgroupOf]
    rw [MonoidHom.mem_ker] at hx
    have hd : (blkA (x : SU4)).det = 1 := by
      have := congrArg (fun u : Kˣ => (u : K)) hx
      simpa [detA] using this
    exact ⟨x.2, hd⟩
  · intro hx
    rw [Subgroup.mem_subgroupOf] at hx
    rw [MonoidHom.mem_ker]
    apply Units.ext
    simpa [detA] using hx.2

private theorem relIndex_KA_C022 (ζ : K) (hζ : IsPrimitiveRoot ζ 3) :
    (KA ζ hζ).relIndex (C022 ζ hζ) = Nat.card ↥(detA ζ hζ).range := by
  show Nat.card (C022 ζ hζ ⧸ (KA ζ hζ).subgroupOf (C022 ζ hζ)) = _
  rw [← detA_ker_eq ζ hζ]
  exact Nat.card_congr (QuotientGroup.quotientKerEquivRange (detA ζ hζ)).toEquiv

private theorem pPrimeCore_bot_KA (ζ : K) (hζ : IsPrimitiveRoot ζ 3) :
    pPrimeCore 3 ↥(KA ζ hζ) = ⊥ := by
  have hW1KA : W1 ≤ KA ζ hζ := W1_le_KA ζ hζ
  have hN : (W1.subgroupOf (KA ζ hζ)).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hW1KA]
    intro w x hw hx
    exact W1_normal_c022 (KA_le_C ζ hζ hx) hw
  have hW1core : pPrimeCore 3 ↥(W1.subgroupOf (KA ζ hζ)) = ⊥ := by
    haveI : IsSimpleGroup ↥W0 := isSimpleGroup_W0
    have hsimpleW1 : IsSimpleGroup ↥W1 := W1equivW0.isSimpleGroup
    have h3W1 : 3 ∣ Nat.card ↥W1 := by
      rw [Nat.card_congr W1equivW0.toEquiv]
      exact three_dvd_W0
    have hbot : pPrimeCore 3 ↥W1 = ⊥ :=
      gLAPPrimeCore_eq_bot_of_isSimpleGroup_of_dvd_card Nat.prime_three hsimpleW1 h3W1
    exact pPrimeCore_eq_bot_of_mulEquiv 3 (Subgroup.subgroupOfEquivOfLe hW1KA).symm hbot
  have hquot : IsSimpleGroup (↥(KA ζ hζ) ⧸ W1.subgroupOf (KA ζ hζ)) := by
    let e : ↥(KA ζ hζ) ⧸ W1.subgroupOf (KA ζ hζ) ≃*
        ↥(KA ζ hζ) ⧸ (piA ζ hζ).ker :=
      QuotientGroup.quotientMulEquivOfEq (piA_ker_eq ζ hζ).symm
    let f : ↥(KA ζ hζ) ⧸ (piA ζ hζ).ker ≃* ↥(piA ζ hζ).range :=
      QuotientGroup.quotientKerEquivRange (piA ζ hζ)
    let g : ↥(piA ζ hζ).range ≃* ↥W0 := MulEquiv.subgroupCongr (piA_range ζ hζ)
    haveI : IsSimpleGroup ↥W0 := isSimpleGroup_W0
    exact (e.trans (f.trans g)).isSimpleGroup
  have hdvd : 3 ∣ Nat.card (↥(KA ζ hζ) ⧸ W1.subgroupOf (KA ζ hζ)) := by
    let e : ↥(KA ζ hζ) ⧸ W1.subgroupOf (KA ζ hζ) ≃*
        ↥(KA ζ hζ) ⧸ (piA ζ hζ).ker :=
      QuotientGroup.quotientMulEquivOfEq (piA_ker_eq ζ hζ).symm
    let f : ↥(KA ζ hζ) ⧸ (piA ζ hζ).ker ≃* ↥(piA ζ hζ).range :=
      QuotientGroup.quotientKerEquivRange (piA ζ hζ)
    let g : ↥(piA ζ hζ).range ≃* ↥W0 := MulEquiv.subgroupCongr (piA_range ζ hζ)
    rw [Nat.card_congr (e.trans (f.trans g)).toEquiv]
    exact three_dvd_W0
  exact pPrimeCore_eq_bot_of_normal_quotient_simple Nat.prime_three hW1core hquot hdvd

private theorem odd_card_gLAPPrimeCoreOf_KA (ζ : K) (hζ : IsPrimitiveRoot ζ 3) :
    Odd (Nat.card (GLAPPrimeCoreOf 3 (KA ζ hζ))) := by
  have hbot : GLAPPrimeCoreOf 3 (KA ζ hζ) = ⊥ :=
    (gLAPPrimeCoreOf_eq_bot_iff_pPrimeCore).mpr (pPrimeCore_bot_KA ζ hζ)
  rw [hbot, Subgroup.card_bot]
  exact odd_one

private theorem odd_card_gLAPPrimeCoreOf_C022 (ζ : K) (hζ : IsPrimitiveRoot ζ 3) :
    Odd (Nat.card (GLAPPrimeCoreOf 3 (C022 ζ hζ))) := by
  have hKAle : KA ζ hζ ≤ C022 ζ hζ := KA_le_C ζ hζ
  have hKAn : ((KA ζ hζ).subgroupOf (C022 ζ hζ)).Normal := by
    rw [← detA_ker_eq ζ hζ]
    exact MonoidHom.normal_ker _
  have hi : Odd ((KA ζ hζ).relIndex (C022 ζ hζ)) := by
    rw [relIndex_KA_C022 ζ hζ]
    exact odd_card_detA_range ζ hζ
  exact odd_card_gLAPPrimeCoreOf_of_odd_relIndex hKAle hKAn hi
    (odd_card_gLAPPrimeCoreOf_KA ζ hζ)

private theorem fixSub_conj_eq_centralizer (g : SU4) :
    CFSG.LocalAnalysis.GLTheoremA.CatB.U48.fixSub (MulAut.conj g) = Subgroup.centralizer ({g} : Set SU4) := by
  ext x
  rw [Subgroup.mem_centralizer_singleton_iff]
  change (MulAut.conj g) x = x ↔ x * g = g * x
  constructor
  · intro h
    have hgx : g * x * g⁻¹ = x := h
    have h' : g * x = x * g := by
      calc g * x = (g * x * g⁻¹) * g := by group
        _ = x * g := by rw [hgx]
    exact h'.symm
  · intro h
    calc g * x * g⁻¹ = (x * g) * g⁻¹ := by rw [h.symm]
      _ = x := mul_inv_cancel_right _ _

private theorem odd_card_gLAPPrimeCoreOf_centralizer_conj (p : ℕ) (g k : SU4) :
    Odd (Nat.card (GLAPPrimeCoreOf p
      (Subgroup.centralizer ({k * g * k⁻¹} : Set SU4)))) ↔
      Odd (Nat.card (GLAPPrimeCoreOf p
        (Subgroup.centralizer ({g} : Set SU4)))) := by
  have hmap : Subgroup.centralizer ({k * g * k⁻¹} : Set SU4) =
      (Subgroup.centralizer ({g} : Set SU4)).map
        (MulAut.conj k : SU4 →* SU4) := by
    simpa using (CFSG.centralizer_singleton_map (MulAut.conj k : SU4 ≃* SU4) g).symm
  rw [hmap]
  rw [card_gLAPPrimeCoreOf_map_of_injective p (MulAut.conj k : SU4 →* SU4)
    (MulAut.conj k).injective (Subgroup.centralizer ({g} : Set SU4))]

private theorem odd_card_gLAPPrimeCoreOf_Cstd (t : μ3) (ht : (t : Kˣ) ≠ 1) :
    Odd (Nat.card (GLAPPrimeCoreOf 3
      (Subgroup.centralizer ({yStd t} : Set SU4)))) := by
  have hbot : GLAPPrimeCoreOf 3
      (Subgroup.centralizer ({yStd t} : Set SU4)) = ⊥ :=
    (gLAPPrimeCoreOf_eq_bot_iff_pPrimeCore).mpr (pPrimeCore_Cstd ht)
  rw [hbot, Subgroup.card_bot]
  exact odd_one

private theorem odd_card_gLAPPrimeCoreOf_centralizer_of_order_three (g : SU4)
    (hg3 : g ^ 3 = 1) (hg1 : g ≠ 1) :
    Odd (Nat.card (GLAPPrimeCoreOf 3
      (Subgroup.centralizer ({g} : Set SU4)))) := by
  obtain ⟨ζ, hζ⟩ := exists_isPrimitiveRoot_three
  obtain ⟨h, hcases⟩ := normal_form g hg3 ζ hζ
  have hodd : Odd (Nat.card (GLAPPrimeCoreOf 3
      (Subgroup.centralizer ({h * g * h⁻¹} : Set SU4)))) := by
    rcases hcases with h1 | h2 | h3 | h4 | h5
    · exfalso
      apply hg1
      calc g = h⁻¹ * (h * g * h⁻¹) * h := by group
        _ = 1 := by rw [h1]; group
    · rw [h2]
      exact odd_card_gLAPPrimeCoreOf_Cstd (zetaU ζ hζ) (zetaU_ne_one ζ hζ)
    · rw [h3]
      exact odd_card_gLAPPrimeCoreOf_Cstd (zetaU ζ hζ ^ 2) (zetaU_sq_ne_one ζ hζ)
    · rw [h4]
      exact odd_card_gLAPPrimeCoreOf_C211 ζ hζ
    · rw [h5]
      exact odd_card_gLAPPrimeCoreOf_C022 ζ hζ
  exact (odd_card_gLAPPrimeCoreOf_centralizer_conj 3 g h).mp hodd

private theorem odd_card_gLAPPrimeCoreOf_fixSub_of_outer {α : MulAut SU4}
    (hα3 : α ^ 3 = 1) (hα1 : fieldFactor4 α ≠ 1) :
    Odd (Nat.card (GLAPPrimeCoreOf 3 (CFSG.LocalAnalysis.GLTheoremA.CatB.U48.fixSub α))) := by
  obtain ⟨hcat, hcard⟩ := catalogIs_fixSub hα3 hα1
  have hsimple : IsSimpleGroup ↥(CFSG.LocalAnalysis.GLTheoremA.CatB.U48.fixSub α) :=
    CFSG.LocalAnalysis.GLTheoremA.S10.isSimple_of_isU4two hcat
  have hdvd : 3 ∣ Nat.card ↥(CFSG.LocalAnalysis.GLTheoremA.CatB.U48.fixSub α) := by
    rw [hcard]
    norm_num
  have hbot : GLAPPrimeCore 3 ↥(CFSG.LocalAnalysis.GLTheoremA.CatB.U48.fixSub α) = ⊥ :=
    gLAPPrimeCore_eq_bot_of_isSimpleGroup_of_dvd_card Nat.prime_three hsimple hdvd
  rw [(gLAPPrimeCoreOf_eq_bot_iff_pPrimeCore).mpr hbot, Subgroup.card_bot]
  exact odd_one

private theorem twoNilpotent_outer_SU4 :
    CFSG.Quasithin.H13.Ch838.TwoNilpotent
      (CFSG.ComponentClassification.OuterAutomorphisms.Outer SU4) := by
  have hsurj : Function.Surjective fieldFactor4 :=
    (CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.primeFormFieldFactor_surjective
      hK (CFSG.RankThree.PartTwo.Sec4.isPrimeFormGram_one_GL) hn4 hq4).comp
      (MulAut.congr ePU4.symm).surjective
  have hker : CFSG.ComponentClassification.OuterAutomorphisms.inner SU4 =
      fieldFactor4.ker := by
    ext α
    constructor
    · rintro ⟨g, hg⟩
      rw [MonoidHom.mem_ker, ← hg]
      exact fieldFactor4_conj g
    · intro h
      exact mem_range_conj_of_fieldFactor4_eq_one h
  let e : CFSG.ComponentClassification.OuterAutomorphisms.Outer SU4 ≃* (K ≃+* K) :=
    (QuotientGroup.quotientMulEquivOfEq hker).trans
      (QuotientGroup.quotientKerEquivOfSurjective fieldFactor4 hsurj)
  have hcycAut : IsCyclic (K ≃+* K) := by
    obtain ⟨σ, -, -, htop, -, -⟩ :=
      CFSG.LocalAnalysis.ComponentInitial.finite_field_automorphism_fixed_field_cardinality
        (F := K) Nat.prime_two (n := 6) (by norm_num) (by rw [card_K]; norm_num)
    exact isCyclic_iff_exists_zpowers_eq_top.mpr ⟨σ, htop⟩
  haveI : IsCyclic (CFSG.ComponentClassification.OuterAutomorphisms.Outer SU4) :=
    (MulEquiv.isCyclic e).mpr hcycAut
  exact CFSG.Quasithin.H13.OutTwoNilp.twoNilpotent_of_isCyclic

private theorem oddCoreFact_three_SU4 : OddCoreFact 3 SU4 := by
  constructor
  · exact CFSG.Quasithin.H13.OutTwoNilp.outTwoNilpotent_of_twoNilpotent_outer
      twoNilpotent_outer_SU4
  · intro α hα
    have hα3 : α ^ 3 = 1 :=
      orderOf_dvd_iff_pow_eq_one.mp (by rw [hα])
    have hα1 : α ≠ 1 := by
      intro h
      rw [h, orderOf_one] at hα
      norm_num at hα
    rw [odd_card_gLAPPrimeCoreOf_innerAut_inf_centralizer_iff center_SU4 3 α]
    change Odd (Nat.card (GLAPPrimeCoreOf 3 (CFSG.LocalAnalysis.GLTheoremA.CatB.U48.fixSub α)))
    by_cases hff : fieldFactor4 α = 1
    · obtain ⟨g, rfl⟩ := mem_range_conj_of_fieldFactor4_eq_one hff
      have hg : orderOf g = 3 := by
        rw [← orderOf_injective (MulAut.conj : SU4 →* MulAut SU4)
          (CFSG.mulAutConj_injective_of_center_eq_bot center_SU4) g]
        exact hα
      have hg3 : g ^ 3 = 1 :=
        orderOf_dvd_iff_pow_eq_one.mp (by rw [hg])
      have hg1 : g ≠ 1 := by
        intro h
        rw [h, orderOf_one] at hg
        norm_num at hg
      rw [fixSub_conj_eq_centralizer g]
      exact odd_card_gLAPPrimeCoreOf_centralizer_of_order_three g hg3 hg1
    · exact odd_card_gLAPPrimeCoreOf_fixSub_of_outer hα3 hff

theorem oddCoreFact_three_of_twistedA3_eight {S : Type} [Group S]
    (q : TauCeti.PrimePower) (hq : q.card = 8)
    (hv : (TauCeti.LieTypeIndex.twistedA 3 q).Valid)
    (e : S ≃* (TauCeti.CFSGIndex.lie ⟨.twistedA 3 q, hv⟩).Group) :
    OddCoreFact 3 S := by
  have hcat : CFSG.Yardstones.Md0ec50421ce4.catalogIs S
      CFSG.LocalAnalysis.GLTheoremA.S9.isU4eight :=
    ⟨.lie ⟨.twistedA 3 q, hv⟩, hq, ⟨e⟩⟩
  obtain ⟨eB⟩ := CFSG.LocalAnalysis.GLTheoremA.bridge_u4eight hcat
  exact (oddCoreFact_congr (p := 3) (eB.trans equivSU4)).mpr oddCoreFact_three_SU4

end CFSG.LocalAnalysis.GLTheoremA.KD1912
