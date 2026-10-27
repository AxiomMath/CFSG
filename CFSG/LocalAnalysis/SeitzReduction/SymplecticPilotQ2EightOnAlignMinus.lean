module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2EightOnTwistMat
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2EightOmKind

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup Matrix Module QuadraticMap CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.LieType.Universal.Spin (quadPlus coe_quadPlus quadMinus coe_quadMinus)
open CFSG.SeitzReduction.F4Pilot (centralizerPerfectCore)
open CFSG.SeitzReduction.UnitaryPilot (modelToG)
open CFSG.Quasithin (perfectCore le_perfectCore_of_perfect)

section Overlap

variable {K : Type} [Field K] [CharP K 2] [Finite K] {r' : ℕ}

theorem onPcOMExt_mem_range_iff (hK : Nat.card K = 2) (hr' : 2 ≤ r') (k : Fin (r' + 1 + 1))
    (l' : Fin (r' + 1)) (a : StatedOmega (StatedQuadMinus (r' + 1 + 1) K 1 1)) :
    pcOMExt k a ∈ (pcOMExt (K := K) (k.succAbove l')).range ↔
      a ∈ (pcOPExt (K := K) l').range := by
  rw [mem_pcOMExt_range_iff (k.succAbove l') hK (by omega), mem_pcOPExt_range_iff l' hK
    (by omega), coe_pcOMExt, ← pcOMMat_mulVec_pdPA, ← pcOMMat_mulVec_pdPB,
    pcExtMat_mulVec_M (pcOMProj_mul_pcOMMat k), pcExtMat_mulVec_M (pcOMProj_mul_pcOMMat k),
    pd_mulVec_eq_iff (pcOMProj_mul_pcOMMat k), pd_mulVec_eq_iff (pcOMProj_mul_pcOMMat k)]

theorem onPdMRot_mem_pcOMExt_range (hK : Nat.card K = 2) (hr' : 2 ≤ r')
    {k l : Fin (r' + 1 + 1)} (hkl : k ≠ l) :
    pdMRot l (by omega) ∈ (pcOMExt (K := K) k).range := by
  obtain ⟨h1, h2, h3, h4⟩ := pdM_polar_frame (K := K) hkl
  rw [mem_pcOMExt_range_iff k hK (by omega), coe_pdMRot]
  exact ⟨pdRotMat_mulVec_of_polar h1 h2, pdRotMat_mulVec_of_polar h3 h4⟩

end Overlap

section Edge

variable {G : Type} [Group G] {L : Subgroup G} {K : Type} [Field K] [Finite K]
  [CharP K 2] {r' : ℕ} {hK : Nat.card K = 2} {e : L ≃* StatedSp (r' + 1 + 1) K} {t : G}

theorem IsNsOmMinusParam.exists_edge_twist_on (hr' : 2 ≤ r') (htw : OmegaPlusOverlapTwist r')
    {hr3 : 3 ≤ r' + 1} {k l : Fin (r' + 1 + 1)} (hkl : k ≠ l)
    {Φ : StatedOmega (StatedQuadMinus (r' + 1 + 1) K 1 1) ≃*
      centralizerPerfectCore (modelToG e (nsTorusSp K k))}
    {Ψ : StatedOmega (StatedQuadMinus (r' + 1 + 1) K 1 1) ≃*
      centralizerPerfectCore (modelToG e (nsTorusSp K l))}
    (hΦ : IsNsOmMinusParam hK hr3 e t k Φ) (hΨ : IsNsOmMinusParam hK hr3 e t l Ψ) :
    ∃ δ : Bool, ∀ a b, pcOMExt k a = pcOMExt l b →
      ((Φ a : centralizerPerfectCore (modelToG e (nsTorusSp K k))) : G) =
        ((Ψ (if δ then kOmMBetaC K (r' + 1) 1 1 b else b) :
          centralizerPerfectCore (modelToG e (nsTorusSp K l))) : G) := by
  have hirr := q2Omega_irreducible_one_one hK
  obtain ⟨l', rfl⟩ := Fin.exists_succAbove_eq (Ne.symm hkl)
  set φk := (centralizerPerfectCore (modelToG e (nsTorusSp K k))).subtype.comp Φ.toMonoidHom
    with hφkdef
  set φl := (centralizerPerfectCore (modelToG e (nsTorusSp K (k.succAbove l')))).subtype.comp
    Ψ.toMonoidHom with hφldef
  have hφk : Function.Injective φk := Subtype.val_injective.comp Φ.injective
  have hφl : Function.Injective φl := Subtype.val_injective.comp Ψ.injective
  obtain ⟨yl, hyl⟩ := onPdMRot_mem_pcOMExt_range hK hr' hkl
  obtain ⟨yk, hyk⟩ := onPdMRot_mem_pcOMExt_range hK hr' (Ne.symm hkl)
  have hφyl : φk yl = ((e.symm (nsElt (k.succAbove l')) : L) : G) :=
    hΦ.coe_eq_of_pcOMExt_eq_iota (hyl.trans (q2OmIota_nsElt_eq _ hK (by omega)).symm)
  have hφyk : φl yk = ((e.symm (nsElt k) : L) : G) :=
    hΨ.coe_eq_of_pcOMExt_eq_iota (hyk.trans (q2OmIota_nsElt_eq _ hK (by omega)).symm)
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
  have hLa : (pcOMExt (K := K) (k.succAbove l')).range ≤ centralizer {pcOMExt k yl} := by
    rw [hyl]
    exact pcOMExt_range_le_centralizer _ _
  have hLb : ∀ P : Subgroup (StatedOmega (StatedQuadPlus (r' + 1 + 2) K)), ⁅P, P⁆ = P →
      P ≤ centralizer {pcOMExt (k.succAbove l') yk} → P ≤ (pcOMExt (K := K) k).range := by
    intro P hP hPc
    rw [hyk] at hPc
    exact le_pcOMExt_range_of_perfect k hK (by omega) hP hPc
  have hperf : ⁅(⊤ : Subgroup (StatedOmega (StatedQuadPlus (r' + 1) K))),
      (⊤ : Subgroup (StatedOmega (StatedQuadPlus (r' + 1) K)))⁆ = ⊤ :=
    (CFSG.LieType.Universal.Spin.isPerfect_statedOmega_quadPlus (by omega)).commutator_eq_top
  have hagree : ∀ x ∈ (fixedSubgroup (kOmegaBetaC K r') : Set _), ∀ b,
      pcOMExt (k.succAbove l') b = pcOMExt k (pcOPExt l' x) → φk (pcOPExt l' x) = φl b := by
    intro x hx b hb
    have hx' : kOmegaBetaC K r' x = x := hx
    have hfa : pcOPExt l' x ∈ fixedSubgroup (kOmMBetaC K (r' + 1) 1 1) := by
      change kOmMBetaC K (r' + 1) 1 1 (pcOPExt l' x) = pcOPExt l' x
      rw [← pcOPExt_kOmegaBetaC, hx']
    rw [← range_q2OmMIota (r := r' + 1) hr3 hirr hK] at hfa
    obtain ⟨z, hz⟩ := hfa
    have h2 := pcOMExt_q2OmMIota k hK hr3 z
    rw [← hz, h2] at hb
    change ((Φ (pcOPExt l' x) : centralizerPerfectCore _) : G) = _
    rw [← hz, hΦ.2]
    exact (hΨ.coe_eq_of_pcOMExt_eq_iota hb).symm
  have htw' : ∀ α : MulAut (StatedOmega (StatedQuadPlus (r' + 1) K)),
      (∀ x ∈ (fixedSubgroup (kOmegaBetaC K r') : Set _), α x = x) →
      (∀ x, α (kOmegaBetaC K r' x) = kOmegaBetaC K r' (α x)) →
        α = 1 ∨ ∀ x, α x = kOmegaBetaC K r' x := by
    intro α hfix hcomm
    rcases htw K hK α hfix hcomm with h | h
    · exact Or.inl h
    · exact Or.inr fun x => by rw [h]
  exact exists_edge_twist_of_overlap (pcOMExt_injective k) (pcOMExt_injective _) hφk hφl hrk hrl
    hφyk hφyl hLa hLb (pcOPExt_injective l') (onPcOMExt_mem_range_iff hK hr' k l') hperf
    (pcOMExt_kOmMBetaC k) (pcOMExt_kOmMBetaC _) (pcOPExt_kOmegaBetaC l') hagree
    (fun a => (hΦ.1 a).symm) (fun b => (hΨ.1 b).symm) htw'

end Edge

section Align

variable {G : Type} [Group G] {L : Subgroup G} {K : Type} [Field K] [Finite K]
  [CharP K 2] {r' : ℕ} {hK : Nat.card K = 2} {e : L ≃* StatedSp (r' + 1 + 1) K} {t : G}

theorem exists_nsOmMinusAligned_on (hr' : 2 ≤ r') (htw : OmegaPlusOverlapTwist r')
    {hr3 : 3 ≤ r' + 1}
    (Φ : ∀ k : Fin (r' + 1 + 1), StatedOmega (StatedQuadMinus (r' + 1 + 1) K 1 1) ≃*
      centralizerPerfectCore (modelToG e (nsTorusSp K k)))
    (hΦ : ∀ k, IsNsOmMinusParam hK hr3 e t k (Φ k)) :
    ∃ ε : Fin (r' + 1 + 1) → Bool, NsOmMinusAligned e fun k =>
      if ε k then (kOmMBetaC K (r' + 1) 1 1).trans (Φ k) else Φ k := by
  obtain ⟨ε, hε⟩ := exists_twist_aligned_of_edge (fun k => pcOMExt (K := K) k)
    (fun k => pcOMExt_injective k) (β := kOmMBetaC K (r' + 1) 1 1)
    (κ := kOmegaBetaC K (r' + 1 + 1)) kOmMBetaC_kOmMBetaC (fun k a => pcOMExt_kOmMBetaC k a)
    (fun k g => ((Φ k g : centralizerPerfectCore (modelToG e (nsTorusSp K k))) : G))
    (fun k => Subtype.val_injective.comp (Φ k).injective) 0
    (fun k l hkl => (hΦ k).exists_edge_twist_on hr' htw hkl (hΦ l))
    (fun k l hko hlo hkl => exists_triple_pcOMExt hK (by omega) (Ne.symm hko) (Ne.symm hlo) hkl)
  refine ⟨ε, fun k l g h hgh => ?_⟩
  have h1 := hε k l g h hgh
  cases hk : ε k <;> cases hl : ε l <;>
    simp only [hk, hl, Bool.false_eq_true, ite_false, ite_true, MulEquiv.trans_apply] at h1 ⊢ <;>
    exact h1

end Align

theorem spTwoOmegaMinusAlignEightInput_holds : SpTwoOmegaMinusAlignEightInput := by
  intro G _ _ L _ K _ _ _ hK e t _ _ _ Φ hΦ
  exact exists_nsOmMinusAligned_on (r' := 2) (hK := hK) le_rfl omegaPlusOverlapTwist_two Φ hΦ

end CFSG.SeitzReduction.SymplecticPilot
