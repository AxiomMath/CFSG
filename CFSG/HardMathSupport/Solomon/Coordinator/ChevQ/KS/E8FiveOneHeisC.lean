module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KS.E8FiveOneHeisB
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KS.E8FiveOneSwap

public noncomputable section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ

namespace KSE8Five

namespace One

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Lattice
  CFSG.RankThree.PartOne.KE8F CFSG.RankThree.PartOne.KE CFSG.RankThree.E6 Matrix
  CFSG.LieType.SeitzGeneration.ExcHigh CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.SeitzExcOpenRest4Griess
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.SeitzExcOpenRest4Twist
  CFSG.HardMathSupport.Foote.Coordinator.SplitFrame
  CFSG.HardMathSupport.Timmesfeld.Torality
open scoped MatrixGroups commutatorElement
open Fin.NatCast

set_option linter.unusedSectionVars false


section Conj

variable {K : Type} [Field K] [Finite K]

theorem rhoA_diagSLn_mem_torus (e : Fin 5 → Kˣ) (he : ∏ i, (e i : K) = 1) :
    rhoA K (diagSLn e he) ∈ torusGroup Tag.E8 K :=
  rhoA_diagonal _ fun i j hij => by simp [coe_diagSLn, Matrix.diagonal_apply_ne _ hij]

theorem conj_yA_mem_torus (a : Fin Tag.E8.rank → Kˣ)
    (hd : ∏ i, ((rootChar a (wbE8A4 e8VA i) : Kˣ) : K) = 1) (g : SL(5, K)) (δ : Fin 5 → Kˣ)
    (hδ : ∏ i, (δ i : K) = 1)
    (hg : g⁻¹ * (diagSLn (fun i => rootChar a (wbE8A4 e8VA i)) hd * coxSL5) * g =
      diagSLn δ hδ) :
    (rhoA K g)⁻¹ * (rootDiagUnit Tag.E8 a * rhoA K coxSL5) * rhoA K g ∈ torusGroup Tag.E8 K := by
  set D : SL(5, K) := diagSLn (fun i => rootChar a (wbE8A4 e8VA i)) hd with hD
  have hconj : ∀ Y : SL(5, K), (rootDiagUnit Tag.E8 a)⁻¹ * rhoA K Y * rootDiagUnit Tag.E8 a =
      rhoA K (D⁻¹ * Y * D) := by
    intro Y
    have h := rootDiagUnit_mul_rhoA a (D⁻¹ * Y * D)
    rw [conjDiagn_eq_diagSLn _ hd] at h
    have e : D * (D⁻¹ * Y * D) * D⁻¹ = Y := by group
    rw [← hD, e] at h
    calc (rootDiagUnit Tag.E8 a)⁻¹ * rhoA K Y * rootDiagUnit Tag.E8 a =
          (rootDiagUnit Tag.E8 a)⁻¹ * (rootDiagUnit Tag.E8 a * rhoA K (D⁻¹ * Y * D) *
            (rootDiagUnit Tag.E8 a)⁻¹) * rootDiagUnit Tag.E8 a := by rw [h]
      _ = rhoA K (D⁻¹ * Y * D) := by group
  have h1 : rootDiagUnit Tag.E8 a * rhoA K (D⁻¹ * g⁻¹ * D) =
      rhoA K g⁻¹ * rootDiagUnit Tag.E8 a := by
    rw [← hconj g⁻¹]
    group
  have hform : (rhoA K g)⁻¹ * (rootDiagUnit Tag.E8 a * rhoA K coxSL5) * rhoA K g =
      rootDiagUnit Tag.E8 a * rhoA K (D⁻¹ * diagSLn δ hδ) := by
    rw [← hg, ← map_inv]
    calc rhoA K g⁻¹ * (rootDiagUnit Tag.E8 a * rhoA K coxSL5) * rhoA K g
        = (rhoA K g⁻¹ * rootDiagUnit Tag.E8 a) * rhoA K coxSL5 * rhoA K g := by group
      _ = (rootDiagUnit Tag.E8 a * rhoA K (D⁻¹ * g⁻¹ * D)) * rhoA K coxSL5 * rhoA K g := by
          rw [h1]
      _ = _ := by simp only [map_mul, map_inv, mul_assoc]
  rw [hform]
  refine mul_mem (rootDiagUnit_mem_torus_E8 a) ?_
  rw [map_mul, map_inv]
  exact mul_mem (inv_mem (rhoA_diagSLn_mem_torus _ hd)) (rhoA_diagSLn_mem_torus _ hδ)

theorem conj_yB {y : ModGL Tag.E8 K} (du : Fin 5 → Kˣ)
    (hdu : ∀ A : SL(5, K), y * rhoA K A * y⁻¹ = rhoA K (conjDiagn du A)) (g : SL(5, K)) :
    (rhoA K g)⁻¹ * y * rhoA K g = y * rhoA K (conjDiagn (fun i => (du i)⁻¹) g⁻¹ * g) := by
  have h1 : y⁻¹ * rhoA K g⁻¹ * y = rhoA K (conjDiagn (fun i => (du i)⁻¹) g⁻¹) := by
    have h := hdu (conjDiagn (fun i => (du i)⁻¹) g⁻¹)
    have e : conjDiagn du (conjDiagn (fun i => (du i)⁻¹) g⁻¹) = g⁻¹ :=
      conjDiagn_conjDiagn_inv du g⁻¹
    rw [e] at h
    calc y⁻¹ * rhoA K g⁻¹ * y = y⁻¹ * (y * rhoA K (conjDiagn (fun i => (du i)⁻¹) g⁻¹) * y⁻¹) *
          y := by rw [h]
      _ = _ := by group
  calc (rhoA K g)⁻¹ * y * rhoA K g = y * (y⁻¹ * rhoA K g⁻¹ * y) * rhoA K g := by
        rw [map_inv]
        group
    _ = y * rhoA K (conjDiagn (fun i => (du i)⁻¹) g⁻¹) * rhoA K g := by rw [h1]
    _ = y * rhoA K (conjDiagn (fun i => (du i)⁻¹) g⁻¹ * g) := by rw [map_mul]; group

theorem exists_rhoA_rotSL_mul_diag (s : ℕ) (r : Fin 5 → Kˣ) (hr : ∏ i, (r i : K) = 1) :
    ∃ hm : rhoA K (rotSL ^ s * diagSLn r hr) ∈ monomialSubgroup Tag.E8 K,
      weylQuotientHom Tag.E8 K ⟨rhoA K (rotSL ^ s * diagSLn r hr), hm⟩ = (e8FiveG1 ^ 4) ^ s := by
  obtain ⟨hmA, hρ⟩ := exists_mA (K := K)
  set S := diagSLn (fun i : Fin 5 => if i = 4 then (1 : Kˣ) else -1) prod_sgn_eq_one with hS
  have hrot : (rotSL : SL(5, K)) = coxSL5 * S⁻¹ := by
    rw [hS, coxSL5_eq_rotSL_mul]
    group
  have hST : (rhoA K S)⁻¹ ∈ monomialSubgroup Tag.E8 K :=
    inv_mem (torusGroup_le_monomialSubgroup (rhoA_diagSLn_mem_torus _ _))
  have hDT : rhoA K (diagSLn r hr) ∈ monomialSubgroup Tag.E8 K :=
    torusGroup_le_monomialSubgroup (rhoA_diagSLn_mem_torus _ _)
  set nM : monomialSubgroup Tag.E8 K := ⟨rhoA K coxSL5, hmA⟩ with hnM
  set nS : monomialSubgroup Tag.E8 K := ⟨(rhoA K S)⁻¹, hST⟩ with hnS
  set nD : monomialSubgroup Tag.E8 K := ⟨rhoA K (diagSLn r hr), hDT⟩ with hnD
  have hval : rhoA K (rotSL ^ s * diagSLn r hr) =
      (((nM * nS) ^ s * nD : monomialSubgroup Tag.E8 K) : ModGL Tag.E8 K) := by
    rw [map_mul, map_pow, hrot, map_mul, map_inv]
    rfl
  have hmem : rhoA K (rotSL ^ s * diagSLn r hr) ∈ monomialSubgroup Tag.E8 K := by
    rw [hval]
    exact ((nM * nS) ^ s * nD).2
  refine ⟨hmem, ?_⟩
  have e : (⟨rhoA K (rotSL ^ s * diagSLn r hr), hmem⟩ : monomialSubgroup Tag.E8 K) =
      (nM * nS) ^ s * nD := Subtype.ext hval
  have hnS1 : weylQuotientHom Tag.E8 K nS = 1 :=
    weylQuotientHom_eq (mapsRootLines_of_mem_torusGroup (inv_mem (rhoA_diagSLn_mem_torus _ _)))
  have hnD1 : weylQuotientHom Tag.E8 K nD = 1 :=
    weylQuotientHom_eq (mapsRootLines_of_mem_torusGroup (rhoA_diagSLn_mem_torus _ _))
  rw [e, map_mul, map_pow, map_mul, hnS1, hnD1, mul_one, mul_one]
  have : weylQuotientHom Tag.E8 K nM = e8FiveG1 ^ 4 := hρ
  rw [this]

end Conj

section HeisMain

theorem g1_pow4_mem_sylowW : e8FiveG1 ^ 4 ∈ sylowW :=
  pow_mem (Subgroup.subset_closure (by simp)) 4

theorem g2_mem_sylowW : e8FiveG2 ∈ sylowW := Subgroup.subset_closure (by simp)

theorem heisReduction_holds : HeisReduction := by
  intro K _ _ h5 ω hω E hE hc hEN hW
  classical
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨yA, hyAE, hyAN, hyA⟩ := mem_wImg.1
    (show e8FiveG1 ^ 4 ∈ wImg K E by rw [hW]; exact g1_pow4_mem_sylowW)
  obtain ⟨yB, hyBE, hyBN, hyB⟩ := mem_wImg.1
    (show e8FiveG2 ∈ wImg K E by rw [hW]; exact g2_mem_sylowW)
  have hyAM : ((yA : adjointGroup Tag.E8 K) : ModGL Tag.E8 K) ∈ monomialSubgroup Tag.E8 K :=
    hyAN
  have hyBM : ((yB : adjointGroup Tag.E8 K) : ModGL Tag.E8 K) ∈ monomialSubgroup Tag.E8 K :=
    hyBN
  have hyAw : weylQuotientHom Tag.E8 K ⟨_, hyAM⟩ = e8FiveG1 ^ 4 := hyA
  have hyBw : weylQuotientHom Tag.E8 K ⟨_, hyBM⟩ = e8FiveG2 := hyB
  obtain ⟨a, ha⟩ := exists_eq_rootDiagUnit_mul_mA hyAM hyAw
  obtain ⟨hmA, hρmA⟩ := exists_mA (K := K)
  have hyA5 : ((yA : adjointGroup Tag.E8 K) : ModGL Tag.E8 K) ^ 5 = 1 := by
    have h := congrArg (fun g : adjointGroup Tag.E8 K => (g : ModGL Tag.E8 K)) (hE.2 yA hyAE)
    simpa using h
  have hmA5 : (rhoA K coxSL5) ^ 5 = 1 := by rw [← map_pow, coxSL5_pow_five, map_one]
  have hnorm := prod_rootChar_wbA_eq_one hmA hρmA hmA5 (a := a) (by rw [← ha]; exact hyA5)
  have hd : ∏ i : Fin 5, ((rootChar a (wbE8A4 e8VA i) : Kˣ) : K) = 1 := by
    have h := congrArg Units.val hnorm
    simpa [Units.coe_prod] using h
  obtain ⟨du, hdu⟩ := exists_fix_scalar hyBM hyBw
  have hcomm : ((yA : adjointGroup Tag.E8 K) : ModGL Tag.E8 K) *
      ((yB : adjointGroup Tag.E8 K) : ModGL Tag.E8 K) =
      ((yB : adjointGroup Tag.E8 K) : ModGL Tag.E8 K) *
        ((yA : adjointGroup Tag.E8 K) : ModGL Tag.E8 K) := by
    have h := hE.1.is_comm.comm ⟨yA, hyAE⟩ ⟨yB, hyBE⟩
    have h' := congrArg (fun g : E => ((g : adjointGroup Tag.E8 K) : ModGL Tag.E8 K)) h
    simpa using h'
  obtain ⟨s, hs⟩ := du_geometric hω hyAM hyAw du hdu hcomm
  obtain ⟨g, δ, hδ, r, hr, hg1, hg2⟩ := swap_matrix hω (fun i => rootChar a (wbE8A4 e8VA i)) hd
    (du 0) s du hs
  have hΦmem : (rhoA K g)⁻¹ ∈ adjointGroup Tag.E8 K := inv_mem (rhoA_mem_adjoint g)
  set Φ : adjointGroup Tag.E8 K := ⟨(rhoA K g)⁻¹, hΦmem⟩ with hΦ
  have hΦc : ∀ x : adjointGroup Tag.E8 K, ((Φ * x * Φ⁻¹ : adjointGroup Tag.E8 K) : ModGL Tag.E8 K) =
      (rhoA K g)⁻¹ * (x : ModGL Tag.E8 K) * rhoA K g := fun x => by
    show (rhoA K g)⁻¹ * (x : ModGL Tag.E8 K) * ((rhoA K g)⁻¹)⁻¹ = _
    rw [inv_inv]
  set w₂ : WeylGroup Tag.E8 := e8FiveG2 * (e8FiveG1 ^ 4) ^ (s : ℕ) with hw₂
  have hA : ∃ h : Φ * yA * Φ⁻¹ ∈ monomialN K, rhoN K ⟨Φ * yA * Φ⁻¹, h⟩ = 1 := by
    have hT : ((Φ * yA * Φ⁻¹ : adjointGroup Tag.E8 K) : ModGL Tag.E8 K) ∈ torusGroup Tag.E8 K := by
      rw [hΦc, ha]
      exact conj_yA_mem_torus a hd g δ hδ hg1
    exact ⟨torusGroup_le_monomialSubgroup hT,
      weylQuotientHom_eq (mapsRootLines_of_mem_torusGroup hT)⟩
  have hB : ∃ h : Φ * yB * Φ⁻¹ ∈ monomialN K, rhoN K ⟨Φ * yB * Φ⁻¹, h⟩ = w₂ := by
    have hval : ((Φ * yB * Φ⁻¹ : adjointGroup Tag.E8 K) : ModGL Tag.E8 K) =
        ((yB : adjointGroup Tag.E8 K) : ModGL Tag.E8 K) *
          rhoA K (rotSL ^ (s : ℕ) * diagSLn r hr) := by
      rw [hΦc, conj_yB du hdu g, hg2]
    obtain ⟨hmR, hρR⟩ := exists_rhoA_rotSL_mul_diag (K := K) (s : ℕ) r hr
    have hM : ((Φ * yB * Φ⁻¹ : adjointGroup Tag.E8 K) : ModGL Tag.E8 K) ∈
        monomialSubgroup Tag.E8 K := by
      rw [hval]
      exact mul_mem hyBM hmR
    refine ⟨hM, ?_⟩
    have e : (⟨((Φ * yB * Φ⁻¹ : adjointGroup Tag.E8 K) : ModGL Tag.E8 K), hM⟩ :
        monomialSubgroup Tag.E8 K) = ⟨_, hyBM⟩ * ⟨_, hmR⟩ := Subtype.ext hval
    rw [rhoN_apply, e, map_mul, hyBw, hρR]
  have hT : ∀ (e : adjointGroup Tag.E8 K) (he : e ∈ E), rhoN K ⟨e, hEN he⟩ = 1 →
      Φ * e * Φ⁻¹ = e := by
    intro e he hρ
    have hem : (e : ModGL Tag.E8 K) ∈ monomialSubgroup Tag.E8 K := hEN he
    have hTe : (e : ModGL Tag.E8 K) ∈ torusGroup Tag.E8 K :=
      (Four.weylQuotientHom_eq_one_iff hem).1 hρ
    obtain ⟨b, hb⟩ :=
      CFSG.LieType.SeitzGeneration.ExcHighThree.exists_rootDiagUnit_of_mem_torusGroup hTe
    have hcomm' : ((yA : adjointGroup Tag.E8 K) : ModGL Tag.E8 K) * rootDiagUnit Tag.E8 b =
        rootDiagUnit Tag.E8 b * ((yA : adjointGroup Tag.E8 K) : ModGL Tag.E8 K) := by
      have h := hE.1.is_comm.comm ⟨yA, hyAE⟩ ⟨e, he⟩
      have h' := congrArg (fun g : E => ((g : adjointGroup Tag.E8 K) : ModGL Tag.E8 K)) h
      simp only [Subgroup.coe_mul] at h'
      rw [hb]
      exact h'
    have hc2 := rootDiagUnit_comm_rhoA hyAM hyAw hcomm' g
    apply Subtype.ext
    rw [hΦc, ← hb]
    calc (rhoA K g)⁻¹ * rootDiagUnit Tag.E8 b * rhoA K g =
          (rhoA K g)⁻¹ * (rootDiagUnit Tag.E8 b * rhoA K g) := by group
      _ = (rhoA K g)⁻¹ * (rhoA K g * rootDiagUnit Tag.E8 b) := by rw [hc2]
      _ = rootDiagUnit Tag.E8 b := by group
  obtain ⟨hle, hwle⟩ := cj_le_of_swap hEN hW hyAE hyBE hyA hyB hA hB hT
  have hw₂S : w₂ ∈ sylowW :=
    mul_mem g2_mem_sylowW (pow_mem g1_pow4_mem_sylowW _)
  have hw₂5 : w₂ ^ 5 = 1 := by
    have hc0 : Commute e8FiveG1 e8FiveG2 := e8Five_comm
    have e1 : w₂ = e8FiveG1 ^ (4 * (s : ℕ)) * e8FiveG2 ^ 1 := by
      rw [hw₂, pow_one, ← pow_mul]
      exact ((hc0.pow_left (4 * (s : ℕ))).eq).symm
    rw [e1]
    exact exp_pow_five _ _
  refine ⟨Φ, hle, hwle.trans (Subgroup.zpowers_le.2 hw₂S), ?_⟩
  have hcard : Nat.card (wImg K (cj Φ E)) ≤ Nat.card (Subgroup.zpowers w₂) :=
    Subgroup.card_le_of_le hwle
  rw [Nat.card_zpowers] at hcard
  exact hcard.trans (Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one hw₂5))

end HeisMain

end One

end KSE8Five

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ
