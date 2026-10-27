module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2EightOnMinusSix
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2EightOmKind
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2OmegaPDAlignPlus

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup Matrix Module QuadraticMap CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.LieType.Universal.Spin (quadPlus coe_quadPlus quadMinus coe_quadMinus)
open CFSG.SeitzReduction.F4Pilot (centralizerPerfectCore)
open CFSG.SeitzReduction.UnitaryPilot (modelToG)
open CFSG.Quasithin (perfectCore le_perfectCore_of_perfect)

section Overlap

variable {K : Type} [Field K] [CharP K 2] [Finite K]

theorem onPcOPExt_mem_range_iff_two (hK : Nat.card K = 2) (k : Fin (2 + 1 + 1))
    (l' : Fin (2 + 1)) (a : StatedOmega (StatedQuadPlus (2 + 1 + 1) K)) :
    pcOPExt k a ∈ (pcOPExt (K := K) (k.succAbove l')).range ↔
      a ∈ (pcOMExt (K := K) l').range := by
  rw [mem_pcOPExt_range_iff (k.succAbove l') hK (by omega), onMem_pcOMExt_range_iff_two hK l',
    coe_pcOPExt, ← pcOPMat_mulVec_pdMA, ← pcOPMat_mulVec_pdMB,
    pcExtMat_mulVec_M (pcOPProj_mul_pcOPMat k), pcExtMat_mulVec_M (pcOPProj_mul_pcOPMat k),
    pd_mulVec_eq_iff (pcOPProj_mul_pcOPMat k), pd_mulVec_eq_iff (pcOPProj_mul_pcOPMat k)]

theorem onPdPRot_mem_pcOPExt_range_two (hK : Nat.card K = 2) {k l : Fin (2 + 1 + 1)}
    (hkl : k ≠ l) : pdPRot l hK (by omega) ∈ (pcOPExt (K := K) k).range := by
  obtain ⟨h1, h2, h3, h4⟩ := pdP_polar_frame (K := K) hkl
  rw [mem_pcOPExt_range_iff k hK (by omega), coe_pdPRot]
  exact ⟨pdRotMat_mulVec_of_polar h1 h2, pdRotMat_mulVec_of_polar h3 h4⟩

end Overlap

section Edge

variable {G : Type} [Group G] {L : Subgroup G} {K : Type} [Field K] [Finite K]
  [CharP K 2] {hK : Nat.card K = 2} {e : L ≃* StatedSp (2 + 1 + 1) K} {t : G}

theorem IsNsOmPlusParam.exists_edge_twist_two {hr : 2 ≤ 2 + 1} {hr3 : 3 ≤ 2 + 1}
    {k l : Fin (2 + 1 + 1)} (hkl : k ≠ l)
    {Φ : StatedOmega (StatedQuadPlus (2 + 1 + 1) K) ≃*
      centralizerPerfectCore (modelToG e (nsTorusSp K k))}
    {Ψ : StatedOmega (StatedQuadPlus (2 + 1 + 1) K) ≃*
      centralizerPerfectCore (modelToG e (nsTorusSp K l))}
    (hΦ : IsNsOmPlusParam hK hr hr3 e t k Φ) (hΨ : IsNsOmPlusParam hK hr hr3 e t l Ψ) :
    ∃ δ : Bool, ∀ a b, pcOPExt k a = pcOPExt l b →
      ((Φ a : centralizerPerfectCore (modelToG e (nsTorusSp K k))) : G) =
        ((Ψ (if δ then kOmegaBetaC K (2 + 1) b else b) :
          centralizerPerfectCore (modelToG e (nsTorusSp K l))) : G) := by
  have hirr := q2Omega_irreducible_one_one hK
  obtain ⟨l', rfl⟩ := Fin.exists_succAbove_eq (Ne.symm hkl)
  set φk := (centralizerPerfectCore (modelToG e (nsTorusSp K k))).subtype.comp Φ.toMonoidHom
    with hφkdef
  set φl := (centralizerPerfectCore (modelToG e (nsTorusSp K (k.succAbove l')))).subtype.comp
    Ψ.toMonoidHom with hφldef
  have hφk : Function.Injective φk := Subtype.val_injective.comp Φ.injective
  have hφl : Function.Injective φl := Subtype.val_injective.comp Ψ.injective
  obtain ⟨yl, hyl⟩ := onPdPRot_mem_pcOPExt_range_two hK hkl
  obtain ⟨yk, hyk⟩ := onPdPRot_mem_pcOPExt_range_two hK (Ne.symm hkl)
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
  have hLb : ∀ P : Subgroup (StatedOmega (StatedQuadMinus (2 + 1 + 1 + 1) K 1 1)), ⁅P, P⁆ = P →
      P ≤ centralizer {pcOPExt (k.succAbove l') yk} → P ≤ (pcOPExt (K := K) k).range := by
    intro P hP hPc
    rw [hyk] at hPc
    exact le_pcOPExt_range_of_perfect k hK (by omega) hP hPc
  have hperf := on_commutator_statedOmega_quadMinus_three hK
  have hagree : ∀ x ∈ (fixedSubgroup (kOmMBetaC K 2 1 1) : Set _), ∀ b,
      pcOPExt (k.succAbove l') b = pcOPExt k (pcOMExt l' x) → φk (pcOMExt l' x) = φl b := by
    intro x hx b hb
    have hx' : kOmMBetaC K 2 1 1 x = x := hx
    have hfa : pcOMExt l' x ∈ fixedSubgroup (kOmegaBetaC K (2 + 1)) := by
      change kOmegaBetaC K (2 + 1) (pcOMExt l' x) = pcOMExt l' x
      rw [← pcOMExt_kOmMBetaC, hx']
    rw [← range_q2OmIota (r := 2 + 1) hr hK hr3] at hfa
    obtain ⟨z, hz⟩ := hfa
    have h2 := pcOPExt_q2OmIota k hK hr3 z
    rw [← hz, h2] at hb
    change ((Φ (pcOMExt l' x) : centralizerPerfectCore _) : G) = _
    rw [← hz, hΦ.2]
    exact (hΨ.coe_eq_of_pcOPExt_eq_iota hb).symm
  have htw' : ∀ α : MulAut (StatedOmega (StatedQuadMinus (2 + 1) K 1 1)),
      (∀ x ∈ (fixedSubgroup (kOmMBetaC K 2 1 1) : Set _), α x = x) →
      (∀ x, α (kOmMBetaC K 2 1 1 x) = kOmMBetaC K 2 1 1 (α x)) →
        α = 1 ∨ ∀ x, α x = kOmMBetaC K 2 1 1 x := by
    intro α hfix hcomm
    rcases omegaMinusOverlapTwist_two hK α hfix hcomm with h | h
    · exact Or.inl h
    · exact Or.inr fun x => by rw [h]
  exact exists_edge_twist_of_overlap (pcOPExt_injective k) (pcOPExt_injective _) hφk hφl hrk hrl
    hφyk hφyl hLa hLb (pcOMExt_injective l') (onPcOPExt_mem_range_iff_two hK k l') hperf
    (pcOPExt_kOmegaBetaC k) (pcOPExt_kOmegaBetaC _) (pcOMExt_kOmMBetaC l') hagree
    (fun a => (hΦ.1 a).symm) (fun b => (hΨ.1 b).symm) htw'

end Edge

section Align

variable {G : Type} [Group G] {L : Subgroup G} {K : Type} [Field K] [Finite K]
  [CharP K 2] {hK : Nat.card K = 2} {e : L ≃* StatedSp (2 + 1 + 1) K} {t : G}

theorem exists_nsOmPlusAligned_two {hr : 2 ≤ 2 + 1} {hr3 : 3 ≤ 2 + 1}
    (Φ : ∀ k : Fin (2 + 1 + 1), StatedOmega (StatedQuadPlus (2 + 1 + 1) K) ≃*
      centralizerPerfectCore (modelToG e (nsTorusSp K k)))
    (hΦ : ∀ k, IsNsOmPlusParam hK hr hr3 e t k (Φ k)) :
    ∃ ε : Fin (2 + 1 + 1) → Bool, NsOmPlusAligned e fun k =>
      if ε k then (kOmegaBetaC K (2 + 1)).trans (Φ k) else Φ k := by
  obtain ⟨ε, hε⟩ := exists_twist_aligned_of_edge (fun k => pcOPExt (K := K) k)
    (fun k => pcOPExt_injective k) (β := kOmegaBetaC K (2 + 1))
    (κ := kOmMBetaC K (2 + 1 + 1) 1 1) kOmegaBetaC_kOmegaBetaC
    (fun k a => pcOPExt_kOmegaBetaC k a)
    (fun k g => ((Φ k g : centralizerPerfectCore (modelToG e (nsTorusSp K k))) : G))
    (fun k => Subtype.val_injective.comp (Φ k).injective) 0
    (fun k l hkl => (hΦ k).exists_edge_twist_two hkl (hΦ l))
    (fun k l hko hlo hkl => exists_triple_pcOPExt hK (by omega) (Ne.symm hko) (Ne.symm hlo) hkl)
  refine ⟨ε, fun k l g h hgh => ?_⟩
  have h1 := hε k l g h hgh
  cases hk : ε k <;> cases hl : ε l <;>
    simp only [hk, hl, Bool.false_eq_true, ite_false, ite_true, MulEquiv.trans_apply] at h1 ⊢ <;>
    exact h1

end Align

theorem spTwoOmegaPlusAlignEightInput_holds : SpTwoOmegaPlusAlignEightInput := by
  intro G _ _ L _ K _ _ _ hK e t _ _ _ Φ hΦ
  exact exists_nsOmPlusAligned_two (hK := hK) Φ hΦ

end CFSG.SeitzReduction.SymplecticPilot
