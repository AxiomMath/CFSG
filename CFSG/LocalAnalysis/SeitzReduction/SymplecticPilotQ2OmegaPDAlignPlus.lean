module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2OmegaPDAlignMinus

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup Matrix Module QuadraticMap CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.LieType.Universal.Spin (quadPlus coe_quadPlus quadMinus coe_quadMinus)
open CFSG.SeitzReduction.F4Pilot (centralizerPerfectCore)
open CFSG.SeitzReduction.UnitaryPilot (modelToG)
open CFSG.Quasithin (perfectCore le_perfectCore_of_perfect)

section Overlap

variable {K : Type} [Field K] [CharP K 2] {r' : ℕ}

theorem pcOPMat_mulVec_pdMA (k : Fin (r' + 1 + 1)) (l' : Fin (r' + 1)) :
    pcOPMat K k *ᵥ pdMA K l' = pdPA K (k.succAbove l') := by
  rw [pdMA, Matrix.mulVec_add, pcOPMat_mulVec_vec k, Matrix.mulVec_single_one]
  congr 1
  funext a
  simp [pcOPMat, pcOPCol]

theorem pcOPMat_mulVec_pdMB (k : Fin (r' + 1 + 1)) (l' : Fin (r' + 1)) :
    pcOPMat K k *ᵥ pdMB K l' = pdPB K (k.succAbove l') := by
  rw [pdMB, Matrix.mulVec_add, pcOPMat_mulVec_vec k, Matrix.mulVec_single_one]
  congr 1
  funext a
  simp [pcOPMat, pcOPCol]

variable [Finite K]

theorem pcOPExt_mem_range_iff (hK : Nat.card K = 2) (hr' : 3 ≤ r') (k : Fin (r' + 1 + 1))
    (l' : Fin (r' + 1)) (a : StatedOmega (StatedQuadPlus (r' + 1 + 1) K)) :
    pcOPExt k a ∈ (pcOPExt (K := K) (k.succAbove l')).range ↔
      a ∈ (pcOMExt (K := K) l').range := by
  rw [mem_pcOPExt_range_iff (k.succAbove l') hK (by omega), mem_pcOMExt_range_iff l' hK hr',
    coe_pcOPExt, ← pcOPMat_mulVec_pdMA, ← pcOPMat_mulVec_pdMB,
    pcExtMat_mulVec_M (pcOPProj_mul_pcOPMat k), pcExtMat_mulVec_M (pcOPProj_mul_pcOPMat k),
    pd_mulVec_eq_iff (pcOPProj_mul_pcOPMat k), pd_mulVec_eq_iff (pcOPProj_mul_pcOPMat k)]

omit [Finite K] in
theorem pdP_polar_frame {k l : Fin (r' + 1 + 1)} (hkl : k ≠ l) :
    polar (quadMinus (r' + 1 + 1 + 1) K 1 1) (pdPA K k) (pdPA K l) = 0 ∧
      polar (quadMinus (r' + 1 + 1 + 1) K 1 1) (pdPA K k) (pdPB K l) = 0 ∧
      polar (quadMinus (r' + 1 + 1 + 1) K 1 1) (pdPB K k) (pdPA K l) = 0 ∧
      polar (quadMinus (r' + 1 + 1 + 1) K 1 1) (pdPB K k) (pdPB K l) = 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [pdP_polar_a]
    simp [pdPA, kOmMVec]
  · rw [pdP_polar_b]
    simp [pdPA, kOmMVec, hkl]
  · rw [pdP_polar_a]
    simp [pdPB, kOmMVec, hkl]
  · rw [pdP_polar_b]
    simp [pdPB, kOmMVec]

theorem pdPRot_mem_pcOPExt_range (hK : Nat.card K = 2) (hr' : 3 ≤ r') {k l : Fin (r' + 1 + 1)}
    (hkl : k ≠ l) : pdPRot l hK (by omega) ∈ (pcOPExt (K := K) k).range := by
  obtain ⟨h1, h2, h3, h4⟩ := pdP_polar_frame (K := K) hkl
  rw [mem_pcOPExt_range_iff k hK (by omega), coe_pdPRot]
  exact ⟨pdRotMat_mulVec_of_polar h1 h2, pdRotMat_mulVec_of_polar h3 h4⟩

end Overlap

section Param

variable {G : Type} [Group G] {L : Subgroup G} {K : Type} [Field K] [Finite K] [CharP K 2]
  {r : ℕ} {hK : Nat.card K = 2} {e : L ≃* StatedSp (r + 1) K} {t : G} {k : Fin (r + 1)}

theorem IsNsOmPlusParam.coe_eq_of_pcOPExt_eq_iota {hr : 2 ≤ r} {hr3 : 3 ≤ r}
    {Φ : StatedOmega (StatedQuadPlus (r + 1) K) ≃*
      centralizerPerfectCore (modelToG e (nsTorusSp K k))}
    (hΦ : IsNsOmPlusParam hK hr hr3 e t k Φ) {y : StatedSp (r + 1) K}
    {b : StatedOmega (StatedQuadPlus (r + 1) K)}
    (hb : pcOPExt k b = q2OmMIota (r := r + 1) (by omega) (q2Omega_irreducible_one_one hK) hK y) :
    ((Φ b : centralizerPerfectCore (modelToG e (nsTorusSp K k))) : G) = ((e.symm y : L) : G) := by
  have hirr := q2Omega_irreducible_one_one hK
  have hfix : pcOPExt k b ∈ fixedSubgroup (kOmMBetaC K (r + 1) 1 1) := by
    rw [hb, ← range_q2OmMIota (r := r + 1) (by omega) hirr hK]
    exact ⟨y, rfl⟩
  rw [mem_fixedSubgroup_kOmMBetaC_iff K (by omega) hirr, coe_pcOPExt, ← pcOPMat_mulVec_vec k,
    pcExtMat_mulVec_M (pcOPProj_mul_pcOPMat k), pd_mulVec_eq_iff (pcOPProj_mul_pcOPMat k)] at hfix
  have hb' : b ∈ fixedSubgroup (kOmegaBetaC K r) :=
    (mem_fixedSubgroup_kOmegaBetaC_iff K hr b).2 hfix
  rw [← range_q2OmIota hr hK hr3] at hb'
  obtain ⟨x, rfl⟩ := hb'
  rw [pcOPExt_q2OmIota k hK hr3 x] at hb
  have hy := q2OmMIota_injective (r := r + 1) (by omega) hirr hK hb
  rw [hΦ.2 x, hy]

end Param

section Edge

variable {G : Type} [Group G] {L : Subgroup G} {K : Type} [Field K] [Finite K]
  [CharP K 2] {r' : ℕ} {hK : Nat.card K = 2} {e : L ≃* StatedSp (r' + 1 + 1) K} {t : G}

theorem IsNsOmPlusParam.exists_edge_twist (hr' : 3 ≤ r') {hr : 2 ≤ r' + 1} {hr3 : 3 ≤ r' + 1}
    {k l : Fin (r' + 1 + 1)} (hkl : k ≠ l)
    {Φ : StatedOmega (StatedQuadPlus (r' + 1 + 1) K) ≃*
      centralizerPerfectCore (modelToG e (nsTorusSp K k))}
    {Ψ : StatedOmega (StatedQuadPlus (r' + 1 + 1) K) ≃*
      centralizerPerfectCore (modelToG e (nsTorusSp K l))}
    (hΦ : IsNsOmPlusParam hK hr hr3 e t k Φ) (hΨ : IsNsOmPlusParam hK hr hr3 e t l Ψ) :
    ∃ δ : Bool, ∀ a b, pcOPExt k a = pcOPExt l b →
      ((Φ a : centralizerPerfectCore (modelToG e (nsTorusSp K k))) : G) =
        ((Ψ (if δ then kOmegaBetaC K (r' + 1) b else b) :
          centralizerPerfectCore (modelToG e (nsTorusSp K l))) : G) := by
  have hirr := q2Omega_irreducible_one_one hK
  obtain ⟨l', rfl⟩ := Fin.exists_succAbove_eq (Ne.symm hkl)
  set φk := (centralizerPerfectCore (modelToG e (nsTorusSp K k))).subtype.comp Φ.toMonoidHom
    with hφkdef
  set φl := (centralizerPerfectCore (modelToG e (nsTorusSp K (k.succAbove l')))).subtype.comp
    Ψ.toMonoidHom with hφldef
  have hφk : Function.Injective φk := Subtype.val_injective.comp Φ.injective
  have hφl : Function.Injective φl := Subtype.val_injective.comp Ψ.injective
  obtain ⟨yl, hyl⟩ := pdPRot_mem_pcOPExt_range hK hr' hkl
  obtain ⟨yk, hyk⟩ := pdPRot_mem_pcOPExt_range hK hr' (Ne.symm hkl)
  have hφyl : φk yl = ((e.symm (nsElt (k.succAbove l')) : L) : G) :=
    hΦ.coe_eq_of_pcOPExt_eq_iota (hyl.trans (q2OmMIota_nsElt_eq _ hK (by omega)).symm)
  have hφyk : φl yk = ((e.symm (nsElt k) : L) : G) :=
    hΨ.coe_eq_of_pcOPExt_eq_iota (hyk.trans (q2OmMIota_nsElt_eq _ hK (by omega)).symm)
  have hrk : φk.range ≤ centralizer {((e.symm (nsElt k) : L) : G)} := by
    rintro _ ⟨a, rfl⟩
    have h1 := F4Pilot.centralizerPerfectCore_le_centralizer _ (Φ a).2
    rw [mem_centralizer_singleton_iff]
    exact ((mem_centralizer_iff.1 h1) _
      (UnitaryPilot.symm_mem_modelToG e (nsElt_mem_nsTorusSp k))).symm
  have hrl : ∀ P : Subgroup G, ⁅P, P⁆ = P →
      P ≤ centralizer {((e.symm (nsElt (k.succAbove l')) : L) : G)} → P ≤ φl.range := by
    intro P hP hPc g hg
    have hgE : g ∈ centralizerPerfectCore (modelToG e (nsTorusSp K (k.succAbove l'))) := by
      rw [F4Pilot.centralizerPerfectCore_def]
      exact le_perfectCore_of_perfect (hPc.trans (pd_centralizer_le_modelToG _)) hP hg
    exact ⟨Ψ.symm ⟨g, hgE⟩, by simp [hφldef]⟩
  have hLa : (pcOPExt (K := K) (k.succAbove l')).range ≤ centralizer {pcOPExt k yl} := by
    rw [hyl]
    exact pcOPExt_range_le_centralizer _ _ _
  have hLb : ∀ P : Subgroup (StatedOmega (StatedQuadMinus (r' + 1 + 1 + 1) K 1 1)), ⁅P, P⁆ = P →
      P ≤ centralizer {pcOPExt (k.succAbove l') yk} → P ≤ (pcOPExt (K := K) k).range := by
    intro P hP hPc
    rw [hyk] at hPc
    exact le_pcOPExt_range_of_perfect k hK (by omega) hP hPc
  have hperf : ⁅(⊤ : Subgroup (StatedOmega (StatedQuadMinus (r' + 1) K 1 1))),
      (⊤ : Subgroup (StatedOmega (StatedQuadMinus (r' + 1) K 1 1)))⁆ = ⊤ :=
    (CFSG.LieType.Universal.Spin.isPerfect_statedOmega_quadMinus (by omega) hirr).commutator_eq_top
  have hagree : ∀ x ∈ (fixedSubgroup (kOmMBetaC K r' 1 1) : Set _), ∀ b,
      pcOPExt (k.succAbove l') b = pcOPExt k (pcOMExt l' x) → φk (pcOMExt l' x) = φl b := by
    intro x hx b hb
    have hx' : x ∈ fixedSubgroup (kOmMBetaC K r' 1 1) := hx
    rw [← range_q2OmMIota (r := r') (by omega) hirr hK] at hx'
    obtain ⟨z, rfl⟩ := hx'
    have h1 := pcOMExt_q2OmMIota l' hK (by omega : 3 ≤ r') z
    have h2 := pcOPExt_q2OmIota k hK (by omega : 3 ≤ r' + 1) (complSpEquiv l' z)
    rw [h1, h2] at hb
    change ((Φ (pcOMExt l' (q2OmMIota _ hirr hK z)) : centralizerPerfectCore _) : G) = _
    rw [h1, hΦ.2]
    exact (hΨ.coe_eq_of_pcOPExt_eq_iota hb).symm
  have htw' : ∀ α : MulAut (StatedOmega (StatedQuadMinus (r' + 1) K 1 1)),
      (∀ x ∈ (fixedSubgroup (kOmMBetaC K r' 1 1) : Set _), α x = x) →
      (∀ x, α (kOmMBetaC K r' 1 1 x) = kOmMBetaC K r' 1 1 (α x)) →
        α = 1 ∨ ∀ x, α x = kOmMBetaC K r' 1 1 x := by
    intro α hfix _
    rcases eq_one_or_eq_kOmMBetaC_of_fix hK hr' hirr α hfix with h | h
    · exact Or.inl h
    · exact Or.inr fun x => by rw [h]
  exact exists_edge_twist_of_overlap (pcOPExt_injective k) (pcOPExt_injective _) hφk hφl hrk hrl
    hφyk hφyl hLa hLb (pcOMExt_injective l') (pcOPExt_mem_range_iff hK hr' k l') hperf
    (pcOPExt_kOmegaBetaC k) (pcOPExt_kOmegaBetaC _) (pcOMExt_kOmMBetaC l') hagree
    (fun a => (hΦ.1 a).symm) (fun b => (hΨ.1 b).symm) htw'

end Edge

section Align

theorem kOmegaBetaC_kOmegaBetaC {K : Type} [Field K] [CharP K 2] {r : ℕ}
    (a : StatedOmega (StatedQuadPlus (r + 1) K)) : kOmegaBetaC K r (kOmegaBetaC K r a) = a := by
  have h1 : ∀ b : StatedOmega (StatedQuadPlus (r + 1) K),
      ((kOmegaBetaC K r b : StatedOmega (StatedQuadPlus (r + 1) K)) :
        GL (Fin (r + 1) ⊕ Fin (r + 1)) K) =
        pdSym (quadPlus (r + 1) K) (kOmegaVec K r) * (b : GL _ K) *
          pdSym (quadPlus (r + 1) K) (kOmegaVec K r) := fun b =>
    pd_coe_omegaSymmetryAut _ (quadPlus (r + 1) K) (coe_quadPlus (r + 1) K)
      (kOmega_matrixDerivedScalars_eq_bot K r) (kOmega_quadPlus_vec K r) b
  apply Subtype.ext
  rw [h1, h1]
  set S := pdSym (quadPlus (r + 1) K) (kOmegaVec K r)
  have hS : S * S = 1 := pdSym_mul_self _ _
  calc S * (S * (a : GL (Fin (r + 1) ⊕ Fin (r + 1)) K) * S) * S =
        (S * S) * (a : GL (Fin (r + 1) ⊕ Fin (r + 1)) K) * (S * S) := by group
    _ = (a : GL (Fin (r + 1) ⊕ Fin (r + 1)) K) := by rw [hS, one_mul, mul_one]

variable {G : Type} [Group G] {L : Subgroup G} {K : Type} [Field K] [Finite K]
  [CharP K 2] {r' : ℕ} {hK : Nat.card K = 2} {e : L ≃* StatedSp (r' + 1 + 1) K} {t : G}

theorem exists_nsOmPlusAligned (hr' : 3 ≤ r') {hr : 2 ≤ r' + 1} {hr3 : 3 ≤ r' + 1}
    (Φ : ∀ k : Fin (r' + 1 + 1), StatedOmega (StatedQuadPlus (r' + 1 + 1) K) ≃*
      centralizerPerfectCore (modelToG e (nsTorusSp K k)))
    (hΦ : ∀ k, IsNsOmPlusParam hK hr hr3 e t k (Φ k)) :
    ∃ ε : Fin (r' + 1 + 1) → Bool, NsOmPlusAligned e fun k =>
      if ε k then (kOmegaBetaC K (r' + 1)).trans (Φ k) else Φ k := by
  obtain ⟨ε, hε⟩ := exists_twist_aligned_of_edge (fun k => pcOPExt (K := K) k)
    (fun k => pcOPExt_injective k) (β := kOmegaBetaC K (r' + 1))
    (κ := kOmMBetaC K (r' + 1 + 1) 1 1) kOmegaBetaC_kOmegaBetaC
    (fun k a => pcOPExt_kOmegaBetaC k a)
    (fun k g => ((Φ k g : centralizerPerfectCore (modelToG e (nsTorusSp K k))) : G))
    (fun k => Subtype.val_injective.comp (Φ k).injective) 0
    (fun k l hkl => (hΦ k).exists_edge_twist hr' hkl (hΦ l))
    (fun k l hko hlo hkl => exists_triple_pcOPExt hK (by omega) (Ne.symm hko) (Ne.symm hlo) hkl)
  refine ⟨ε, fun k l g h hgh => ?_⟩
  have h1 := hε k l g h hgh
  cases hk : ε k <;> cases hl : ε l <;>
    simp only [hk, hl, Bool.false_eq_true, ite_false, ite_true, MulEquiv.trans_apply] at h1 ⊢ <;>
    exact h1

end Align

theorem spTwoOmegaPlusAlignInput_holds : SpTwoOmegaPlusAlignInput := by
  intro G _ _ L _ r K _ _ _ hK hr e t _ _ _ Φ hΦ
  obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
  exact exists_nsOmPlusAligned (hK := hK) (by omega) Φ hΦ

end CFSG.SeitzReduction.SymplecticPilot
