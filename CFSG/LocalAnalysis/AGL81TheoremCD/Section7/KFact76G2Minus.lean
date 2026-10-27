module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section7.KFact76G2Roots
import CFSG.LocalAnalysis.AGL81TheoremCD.Section7.KFact76G2Bruhat
import CFSG.LocalAnalysis.AGL81TheoremCD.Section7.KFact76G2Gen
import CFSG.LocalAnalysis.AGL81TheoremCD.Section7.KFact76G2Lin
import CFSG.LocalAnalysis.AGL81TheoremCD.Section7.KFact76G2RankOne

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section7.G2Max

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint RootOps
  CFSG.HardMathSupport.Seitz.G2Anisotropic.ExceptionsTransport
open scoped commutatorElement

theorem zr_mem_adjointGroup
    {K : Type} [Field K] : zr K ∈ adjointGroup .G2 K := by
  unfold zr
  exact mul_mem (weylElt_mem_adjointGroup _ _) (xUnit_mem_adjointGroup _ _)

variable
  {K : Type} [Field K]

local notation "X" => pinnedX Tag.G2 K

theorem commute_pinnedX_c_zr (s : K) : Commute (X gC s) (zr K) :=
  (mul_inv_eq_iff_eq_mul.1 (zr_Z_fixed _ (X_mem_Zg s))).symm

theorem zr_eq_pinnedX : zr K = X gR 1 * X (-gR) (-1) * X gR 1 * X gR 1 := by
  unfold zr
  rw [weylElt_one_eq, xUnit_iR, yUnit_iR]

theorem commute_pinnedX_negC_zr (s : K) : Commute (X (-gC) s) (zr K) := by
  have h1 := (commute_r_negC 1 s).symm
  rw [zr_eq_pinnedX]
  exact ((h1.mul_right (commute_negR_negC (-1) s).symm).mul_right h1).mul_right h1

theorem commute_torusElt_c_zr (ν : Kˣ) :
    Commute (torusElt .G2 K iA (ν ^ 2) * torusElt .G2 K iR ν) (zr K) := by
  have hr := commute_torus2_pinnedX (K := K) (t₁ := ν ^ 2) (t₂ := ν) isRoot_gR (by
    rw [show ∑ j, Tag.G2.cartan iA j * gR j = -1 by decide,
      show ∑ j, Tag.G2.cartan iR j * gR j = 2 by decide]
    group)
  have hnr := commute_torus2_pinnedX (K := K) (t₁ := ν ^ 2) (t₂ := ν) (IsRoot.neg isRoot_gR) (by
    rw [show ∑ j, Tag.G2.cartan iA j * (-gR) j = 1 by decide,
      show ∑ j, Tag.G2.cartan iR j * (-gR) j = -2 by decide]
    group)
  rw [zr_eq_pinnedX]
  exact (((hr 1).mul_right (hnr (-1))).mul_right (hr 1)).mul_right (hr 1)

theorem adjointGroup_le_of_overgroup_zr (hK : ∀ s : K, s ^ 2 + s + 1 ≠ 0)
    (ht : ∃ t₀ : K, t₀ ≠ 0 ∧ t₀ ≠ 1) {H : Subgroup (ModGL .G2 K)}
    (hC : ∀ g ∈ adjointGroup .G2 K, Commute g (zr K) → g ∈ H)
    {x : ModGL .G2 K} (hx : x ∈ adjointGroup .G2 K) (hxH : x ∈ H)
    (h1 : ¬ Commute (x * X gC 1 * x⁻¹) (X gC 1)) (h2 : ¬ Commute (x * X gC 1 * x⁻¹) (zr K)) :
    adjointGroup .G2 K ≤ H := by
  have h3 : (3 : K) ≠ 0 := by
    have h := hK 1
    rwa [show (1 : K) ^ 2 + 1 + 1 = 3 by norm_num] at h
  have hXc : ∀ s : K, X gC s ∈ H := fun s =>
    hC _ (pinnedX_mem_adjointGroup _ _) (commute_pinnedX_c_zr s)
  have hXnc : ∀ s : K, X (-gC) s ∈ H := fun s =>
    hC _ (pinnedX_mem_adjointGroup _ _) (commute_pinnedX_negC_zr s)
  have hhc : ∀ ν : Kˣ, torusElt .G2 K iA (ν ^ 2) * torusElt .G2 K iR ν ∈ H := fun ν =>
    hC _ (mul_mem (torusElt_mem_adjointGroup _ _) (torusElt_mem_adjointGroup _ _))
      (commute_torusElt_c_zr ν)
  have hzr : zr K ∈ H := hC _ zr_mem_adjointGroup (Commute.refl _)
  have hA : ∀ d ∈ g2QCoords H, Nmat (Xmat 1 d) ∈ g2QCoords H := fun d hd =>
    map_mem_g2QCoords (M := fun c => Nmat (Xmat 1 c)) hzr zr_normalizes
      (fun g hg c hc => clsT_conj_vec hg c hc) hd
  have hfixQ : ∀ q ∈ Qg K, clsT (zr K * q * (zr K)⁻¹) = clsT q → Commute q (zr K) :=
    fun q hq h => (mul_inv_eq_iff_eq_mul.1
      (conj_eq_self_of_clsT_eq h3 zr_pow_three zr_Z_fixed hq (zr_normalizes q hq) h)).symm
  have hCA : ∀ d, Nmat (Xmat 1 d) = d → d ∈ g2QCoords H := fun d hd =>
    ⟨g2QWord d, hC _ (Qg_le_adjointGroup (g2QWord_mem d)) (hfixQ _ (g2QWord_mem d) (by
      rw [clsT_conj_vec (g2QWord_mem d) d (clsT_g2QWord d), hd, clsT_g2QWord])),
      g2QWord_mem d, clsT_g2QWord d⟩
  obtain ⟨q, hq, κ, hform⟩ := exists_conj_pinnedX_c_forms hx h1
  have hR : ∀ s : K, x * X gC s * x⁻¹ ∈ H := fun s =>
    H.mul_mem (H.mul_mem hxH (hXc s)) (H.inv_mem hxH)
  have hκ : (κ : K) * 1 ≠ 0 := mul_ne_zero κ.ne_zero one_ne_zero
  obtain ⟨w, hwW, hwA⟩ : ∃ w ∈ g2QCoords H, Nmat (Xmat 1 w) ≠ w := by
    rcases hform with hf | hf | ⟨t, hf⟩
    ·
      obtain ⟨t₀, ht0, ht1⟩ := ht
      obtain ⟨d, hd⟩ := exists_clsT_eq_vec hq
      refine ⟨d, mem_g2QCoords_of_conj_negC (t := Units.mk0 t₀ ht0) ht1 hXc hhc hq hκ
        (by rw [← hf 1]; exact hR 1) hd, fun hfix => h2 ?_⟩
      have hqz : Commute q (zr K) := hfixQ q hq (by rw [clsT_conj_vec hq d hd, hfix, hd])
      rw [hf 1]
      exact (hqz.mul_left (commute_pinnedX_negC_zr _)).mul_left hqz.inv_left
    ·
      obtain ⟨ε, hε, hc⟩ := comm_negA_c (K := K)
      have hqc : Commute q (X gC 1) := classTwoG2.central q hq _ (X_mem_Zg 1)
      have e : ⁅x * X gC 1 * x⁻¹, X gC 1⁆ = q * X gB (ε * ((κ : K) * 1) * 1) * q⁻¹ := by
        rw [hf 1, commutatorElement_conj_of_commute hqc, hc]
      have hb := X_mem_Qg (K := K) isQRoot_b (ε * ((κ : K) * 1) * 1)
      refine ⟨(0, 0, 0, ε * ((κ : K) * 1) * 1), ⟨⁅x * X gC 1 * x⁻¹, X gC 1⁆, ?_, ?_, ?_⟩,
        fun hfix => ?_⟩
      · rw [commutatorElement_def]
        exact H.mul_mem (H.mul_mem (H.mul_mem (hR 1) (hXc 1)) (H.inv_mem (hR 1)))
          (H.inv_mem (hXc 1))
      · rw [e]
        exact mul_mem (mul_mem hq hb) (inv_mem hq)
      · rw [e, clsT_conj_of_mem_Qg hq hb, ← clsT_g2QWord]
        simp [g2QWord, pinnedX_zero .G2 K]
      · have h4 := congrArg (fun v => v.2.2.2) hfix
        simp only [Xmat, Nmat] at h4
        exact mul_ne_zero (mul_ne_zero (left_ne_zero_of_mul_eq_one hε) hκ) one_ne_zero h4.symm
    ·
      obtain ⟨ε, hε, hmem⟩ := exists_Xmat_mem_g2QCoords_of_conj_negB hq t ((κ : K) * 1)
        (by rw [← hf 1]; exact hR 1) (hXc 1)
      refine ⟨_, hmem, fun hfix => ?_⟩
      have h2' := congrArg (fun v => v.2.1) hfix
      simp only [Xmat, Nmat] at h2'
      refine hK t (mul_left_cancel₀ (mul_ne_zero (left_ne_zero_of_mul_eq_one hε) hκ) ?_)
      linear_combination -h2'
  exact adjointGroup_le_of_Qg_le H (Qg_le_of_forall_mem_g2QCoords
    (forall_mem_of_ne_fixedA hK (fun d hd d' hd' => add_mem_g2QCoords hd hd')
      (fun k d hd => smul_mem_g2QCoords hhc k hd) hA hCA hwW hwA) hXc) hXnc

end CFSG.LocalAnalysis.AGL81TheoremCD.Section7.G2Max
