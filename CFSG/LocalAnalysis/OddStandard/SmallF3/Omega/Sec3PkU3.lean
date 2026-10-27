module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3PkAbs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2OddCoreL3U3
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2Pocket
public import CFSG.GH74.GLS.Stage4.SDWLayerFieldU
public import CFSG.GH74.GLS.Stage1.Main.BrG2AutC
public import CFSG.ClassicalInvolution.Orders.Classical

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint CFSG.Open CFSG.GH74.GLS.IVK CFSG.GH74.GLS.IVK.Proofs2
  CFSG.GH74.GLS.Stage4.Rest.FieldU3 CFSG.GH74.GLS.Stage1.Main CFSG.LocalAnalysis.ComponentInitial
  CFSG.ClassicalGroups.UnitaryFlag CFSG.ComponentClassification.UnbalancedCatalog.EvenCatalog

section Algebra

variable {F : Type} [Field F]

theorem det_eq_one_of_fin_two_central (h2 : (2 : F) ≠ 0) {M : Matrix (Fin 2) (Fin 2) F}
    (hc1 : M * !![1, 0; 0, -1] = !![1, 0; 0, -1] * M)
    (hc2 : M * !![0, 1; 1, 0] = !![0, 1; 1, 0] * M) (hMM : M * M = 1) : M.det = 1 := by
  rw [Matrix.eta_fin_two M, Matrix.mul_fin_two, Matrix.mul_fin_two, fin_two_eq_iff] at hc1 hc2
  obtain ⟨-, hc01, hc10, -⟩ := hc1
  obtain ⟨hd00, hd01, -, -⟩ := hc2
  have hy : M 0 1 = 0 := by
    have : (2 : F) * M 0 1 = 0 := by linear_combination (-1 : F) * hc01
    exact (mul_eq_zero.mp this).resolve_left h2
  have hz : M 1 0 = 0 := by
    have : (2 : F) * M 1 0 = 0 := by linear_combination hc10
    exact (mul_eq_zero.mp this).resolve_left h2
  have hw : M 1 1 = M 0 0 := by linear_combination -hd01
  rw [Matrix.eta_fin_two M, Matrix.mul_fin_two, Matrix.one_fin_two, fin_two_eq_iff] at hMM
  obtain ⟨h00, -, -, -⟩ := hMM
  rw [Matrix.det_fin_two, hy, hz, hw]
  rw [hy, hz] at h00
  linear_combination h00

end Algebra

theorem mem_ker_sdwUDet_of_central {F : Type} [Field F] (h : UnitaryFieldData 3 1 F)
    {w : ↥(GU2Stated (3 ^ 1) F)} (hw : ∀ g : ↥(GU2Stated (3 ^ 1) F), g * w = w * g)
    (hw2 : w * w = 1) : w ∈ (sdwUDet (3 ^ 1) F).ker := by
  let a : ↥(GU2Stated (3 ^ 1) F) := ⟨gl2OfSq !![1, 0; 0, -1] diag_mul_self,
    (Lemma41aU3.mem_GU2Stated_iff h).mpr (unitary_diag h)⟩
  let b : ↥(GU2Stated (3 ^ 1) F) := ⟨gl2OfSq !![0, 1; 1, 0] swap_mul_self,
    (Lemma41aU3.mem_GU2Stated_iff h).mpr (unitary_swap h)⟩
  have hca := matrix_commute (hw a).symm
  have hcb := matrix_commute (hw b).symm
  have hMM : ((w : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *
      ((w : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = 1 := by
    have := congrArg (fun u : ↥(GU2Stated (3 ^ 1) F) =>
      ((u : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)) hw2
    simpa using this
  have hdet := det_eq_one_of_fin_two_central (two_ne_zero_of_unitaryFieldData h) hca hcb hMM
  rw [sdwU_mem_ker_iff h]
  change (w : GL (Fin 2) F) ∈ unitarySU 3 1 F 2
  rw [mem_unitarySU_iff h]
  exact ⟨hdet, (Lemma41aU3.mem_GU2Stated_iff h).mp w.2⟩

theorem isSL23Mod_ker_sdwUDet {F : Type} [Field F] (h : UnitaryFieldData 3 1 F) :
    IsSL23Mod ↥(sdwUDet (3 ^ 1) F).ker := by
  obtain ⟨k, ik, ikFin, hkcard, ⟨e⟩⟩ := sdwU_exists_ker_equiv h
  have hk3 : Nat.card k = 3 := by rw [hkcard]; norm_num
  haveI := Fintype.ofFinite k
  have hk : Fintype.card k = 3 := by rw [← Nat.card_eq_fintype_card, hk3]
  exact isSL23Mod_of_mulEquiv
    ((sl2EquivOfRingEquiv (ZMod.ringEquivOfPrime k Nat.prime_three hk).symm).symm.trans e.symm)
    isSL23Mod_sl2f3

theorem nonempty_centralizer_equiv_gu2_of_lieModel_psu33 {Y : Type} [Group Y] [Finite Y]
    (h : LieModel Y .PSU 3 3 1) {z : Y} (hz : orderOf z = 2) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 9 ∧
      Nonempty (↥(centralizer ({z} : Set Y)) ≃* ↥(GU2Stated (3 ^ 1) F)) := by
  have hclass : StatedClassicalModel Y .PSU 3 3 1 :=
    LieModel.statedClassicalModel_of_ne_zero (by norm_num) h
  obtain ⟨-, F, hFfield, hFfin, hFcard, ⟨e⟩⟩ := hclass
  have hLn : IsLnEps 3 Y (-1) (3 ^ 1) := Or.inr ⟨rfl, F, hFfield, hFfin, hFcard, ⟨e⟩⟩
  obtain ⟨F', hF'field, hF'fin, N, hN, hF'card, hNcard, ⟨e'⟩⟩ :=
    ivk_4_1a_U3 Y 3 1 Nat.prime_three (by norm_num) hLn z hz
  have hF9 : Nat.card F' = 9 := by rw [hF'card]; norm_num
  have hNbot : N = ⊥ := le_bot_iff.mp
    ((oddCore_gu2_eq_bot hF9) ▸ le_oddCore_of_normal hN (odd_of_card_one_or_three hNcard))
  exact ⟨F', hF'field, hF'fin, hF9, ⟨e'.trans ((QuotientGroup.quotientMulEquivOfEq hNbot).trans
    QuotientGroup.quotientBot)⟩⟩

theorem isI4PlusIn_top_of_lieModel_psu33 {Y : Type} [Group Y] [Finite Y]
    (h : LieModel Y .PSU 3 3 1) {z : Y} (hz : orderOf z = 2) :
    IsI4PlusIn (⊤ : Subgroup Y) z := by
  obtain ⟨F, iF, iFin, hF9, ⟨ψ⟩⟩ := nonempty_centralizer_equiv_gu2_of_lieModel_psu33 h hz
  have hud : UnitaryFieldData 3 1 F := ⟨Nat.prime_three, le_rfl, by rw [hF9]; norm_num⟩
  have hz0 : (⟨z, mem_centralizer_self z⟩ : ↥(centralizer ({z} : Set Y))) *
      ⟨z, mem_centralizer_self z⟩ = 1 :=
    Subtype.ext (by simpa [sq, hz] using pow_orderOf_eq_one z)
  refine isI4PlusIn_top_of_centralizer_equiv hz ψ (sdwUDet (3 ^ 1) F).ker ?_
    (isSL23Mod_ker_sdwUDet hud)
  refine mem_ker_sdwUDet_of_central hud (fun g => ?_) (by rw [← map_mul, hz0, map_one])
  obtain ⟨c, rfl⟩ := ψ.surjective g
  rw [← map_mul, ← map_mul]
  exact congrArg ψ (Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp c.2))

theorem exists_involution_of_lieModel_psu33 {Y : Type} [Group Y] [Finite Y]
    (h : LieModel Y .PSU 3 3 1) : ∃ z : Y, orderOf z = 2 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcard : Nat.card Y = 6048 := by
    rw [(CFSG.ClassicalInvolution.card_statedClassicalModel_of_ne_two (G := Y)
      (show (3 : ℕ) ≠ 2 by norm_num) (h.statedClassicalModel_of_ne_zero (by norm_num))).2.1 rfl]
    decide +kernel
  exact exists_prime_orderOf_dvd_card' 2 (by rw [hcard]; norm_num)

theorem exists_isI4PlusIn_of_lieModel_psu33 {Y : Type} [Group Y] [Finite Y]
    (h : LieModel Y .PSU 3 3 1) : ∃ q : Y, IsI4PlusIn (⊤ : Subgroup Y) q := by
  obtain ⟨z, hz⟩ := exists_involution_of_lieModel_psu33 h
  exact ⟨z, isI4PlusIn_top_of_lieModel_psu33 h hz⟩

end CFSG.OddStandard.SmallF3.Omega
