module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2OmegaPDPlus
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2OmegaPDAbstract
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2OmegaPCAlign

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup Matrix Module QuadraticMap CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.LieType.Universal.Spin (quadPlus coe_quadPlus quadMinus coe_quadMinus)
open CFSG.SeitzReduction.F4Pilot (centralizerPerfectCore)
open CFSG.SeitzReduction.UnitaryPilot (modelToG)
open CFSG.Quasithin (perfectCore le_perfectCore_of_perfect)

section Generic

variable {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] {K : Type}
  [Field K]

theorem pcExtMat_mulVec_M {M : Matrix κ ι K} {R : Matrix ι κ K} (hRM : R * M = 1)
    (g : Matrix ι ι K) (w : ι → K) : pcExtMat M R g *ᵥ (M *ᵥ w) = M *ᵥ (g *ᵥ w) := by
  have hRw : R *ᵥ (M *ᵥ w) = w := by rw [Matrix.mulVec_mulVec, hRM, Matrix.one_mulVec]
  rw [pcExtMat_mulVec, hRw, Matrix.mulVec_sub, add_sub_cancel]

omit [DecidableEq κ] in
theorem pd_mulVec_eq_iff {M : Matrix κ ι K} {R : Matrix ι κ K} (hRM : R * M = 1)
    {w w' : ι → K} : M *ᵥ w = M *ᵥ w' ↔ w = w' := by
  refine ⟨fun h => ?_, fun h => h ▸ rfl⟩
  have h1 := congrArg (R *ᵥ ·) h
  simp only [Matrix.mulVec_mulVec, hRM, Matrix.one_mulVec] at h1
  exact h1

end Generic

section Overlap

variable {K : Type} [Field K] [CharP K 2] {r' : ℕ}

omit [CharP K 2] in
theorem pcOMMat_mulVec_pdPA (k : Fin (r' + 1 + 1)) (l' : Fin (r' + 1)) :
    pcOMMat K k *ᵥ pdPA K l' = pdMA K (k.succAbove l') := by
  rw [pdPA, Matrix.mulVec_add, pcOMMat_mulVec_vec k, Matrix.mulVec_single_one]
  rfl

omit [CharP K 2] in
theorem pcOMMat_mulVec_pdPB (k : Fin (r' + 1 + 1)) (l' : Fin (r' + 1)) :
    pcOMMat K k *ᵥ pdPB K l' = pdMB K (k.succAbove l') := by
  rw [pdPB, Matrix.mulVec_add, pcOMMat_mulVec_vec k, Matrix.mulVec_single_one]
  rfl

variable [Finite K]

theorem pcOMExt_mem_range_iff (hK : Nat.card K = 2) (hr' : 3 ≤ r') (k : Fin (r' + 1 + 1))
    (l' : Fin (r' + 1)) (a : StatedOmega (StatedQuadMinus (r' + 1 + 1) K 1 1)) :
    pcOMExt k a ∈ (pcOMExt (K := K) (k.succAbove l')).range ↔
      a ∈ (pcOPExt (K := K) l').range := by
  rw [mem_pcOMExt_range_iff (k.succAbove l') hK (by omega), mem_pcOPExt_range_iff l' hK
    (by omega), coe_pcOMExt, ← pcOMMat_mulVec_pdPA, ← pcOMMat_mulVec_pdPB,
    pcExtMat_mulVec_M (pcOMProj_mul_pcOMMat k), pcExtMat_mulVec_M (pcOMProj_mul_pcOMMat k),
    pd_mulVec_eq_iff (pcOMProj_mul_pcOMMat k), pd_mulVec_eq_iff (pcOMProj_mul_pcOMMat k)]

omit [Finite K] in
theorem pdM_polar_frame {k l : Fin (r' + 1 + 1)} (hkl : k ≠ l) :
    polar (quadPlus (r' + 1 + 2) K) (pdMA K k) (pdMA K l) = 0 ∧
      polar (quadPlus (r' + 1 + 2) K) (pdMA K k) (pdMB K l) = 0 ∧
      polar (quadPlus (r' + 1 + 2) K) (pdMB K k) (pdMA K l) = 0 ∧
      polar (quadPlus (r' + 1 + 2) K) (pdMB K k) (pdMB K l) = 0 := by
  have hkN : ∀ j : Fin (r' + 1 + 1), j.castSucc ≠ Fin.last (r' + 1 + 1) := Fin.castSucc_ne_last
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [pdM_polar_a]
    simp [pdMA, kOmegaVec, hkN, CharTwo.add_self_eq_zero]
  · rw [pdM_polar_b]
    simp [pdMA, kOmegaVec, hkN, hkl, CharTwo.add_self_eq_zero]
  · rw [pdM_polar_a]
    simp [pdMB, kOmegaVec, hkN, hkl, CharTwo.add_self_eq_zero]
  · rw [pdM_polar_b]
    simp [pdMB, kOmegaVec, hkN, CharTwo.add_self_eq_zero]

theorem pdMRot_mem_pcOMExt_range (hK : Nat.card K = 2) (hr' : 3 ≤ r') {k l : Fin (r' + 1 + 1)}
    (hkl : k ≠ l) : pdMRot l (by omega) ∈ (pcOMExt (K := K) k).range := by
  obtain ⟨h1, h2, h3, h4⟩ := pdM_polar_frame (K := K) hkl
  rw [mem_pcOMExt_range_iff k hK (by omega), coe_pdMRot]
  exact ⟨pdRotMat_mulVec_of_polar h1 h2, pdRotMat_mulVec_of_polar h3 h4⟩

end Overlap

section Param

variable {G : Type} [Group G] {L : Subgroup G} {K : Type} [Field K] [Finite K] [CharP K 2]
  {r : ℕ} {hK : Nat.card K = 2} {e : L ≃* StatedSp (r + 1) K} {t : G} {k : Fin (r + 1)}

theorem IsNsOmMinusParam.coe_eq_of_pcOMExt_eq_iota {hr3 : 3 ≤ r}
    {Φ : StatedOmega (StatedQuadMinus (r + 1) K 1 1) ≃*
      centralizerPerfectCore (modelToG e (nsTorusSp K k))}
    (hΦ : IsNsOmMinusParam hK hr3 e t k Φ) {y : StatedSp (r + 1) K}
    {b : StatedOmega (StatedQuadMinus (r + 1) K 1 1)}
    (hb : pcOMExt k b = q2OmIota (r := r + 1) (by omega) hK (by omega) y) :
    ((Φ b : centralizerPerfectCore (modelToG e (nsTorusSp K k))) : G) = ((e.symm y : L) : G) := by
  have hirr := q2Omega_irreducible_one_one hK
  have hfix : pcOMExt k b ∈ fixedSubgroup (kOmegaBetaC K (r + 1)) := by
    rw [hb, ← range_q2OmIota (r := r + 1) (by omega) hK (by omega)]
    exact ⟨y, rfl⟩
  rw [mem_fixedSubgroup_kOmegaBetaC_iff K (by omega), coe_pcOMExt, ← pcOMMat_mulVec_vec k,
    pcExtMat_mulVec_M (pcOMProj_mul_pcOMMat k), pd_mulVec_eq_iff (pcOMProj_mul_pcOMMat k)] at hfix
  have hb' : b ∈ fixedSubgroup (kOmMBetaC K r 1 1) :=
    (mem_fixedSubgroup_kOmMBetaC_iff K hr3 hirr b).2 hfix
  rw [← range_q2OmMIota hr3 hirr hK] at hb'
  obtain ⟨x, rfl⟩ := hb'
  rw [pcOMExt_q2OmMIota k hK hr3 x] at hb
  have hy := q2OmIota_injective (r := r + 1) (by omega) hK (by omega) hb
  rw [hΦ.2 x, hy]

end Param

@[expose] def OmegaPlusOverlapTwist (r' : ℕ) : Prop :=
  ∀ (K : Type) [Field K] [Finite K] [CharP K 2], Nat.card K = 2 →
    ∀ α : MulAut (StatedOmega (StatedQuadPlus (r' + 1) K)),
      (∀ g ∈ fixedSubgroup (kOmegaBetaC K r'), α g = g) →
      (∀ g, α (kOmegaBetaC K r' g) = kOmegaBetaC K r' (α g)) → α = 1 ∨ α = kOmegaBetaC K r'

theorem omegaPlusOverlapTwist_of_four_le {r' : ℕ} (hr : 4 ≤ r') : OmegaPlusOverlapTwist r' :=
  fun _ _ _ _ hK α hfix _ => eq_one_or_eq_kOmegaBetaC_of_fix hK hr α hfix

section Edge

variable {G : Type} [Group G] {L : Subgroup G} {K : Type} [Field K] [Finite K]
  [CharP K 2] {r' : ℕ} {hK : Nat.card K = 2} {e : L ≃* StatedSp (r' + 1 + 1) K} {t : G}

omit [Finite K] [CharP K 2] in
theorem pd_centralizer_le_modelToG (y : StatedSp (r' + 1 + 1) K) :
    centralizer {((e.symm y : L) : G)} ≤ centralizer (modelToG e (zpowers y) : Set G) := by
  intro g hg
  rw [mem_centralizer_iff]
  intro h hh
  obtain ⟨x, hx, rfl⟩ := (UnitaryPilot.mem_modelToG e).1 hh
  obtain ⟨n, rfl⟩ := mem_zpowers_iff.1 hx
  have hc : Commute g ((e.symm y : L) : G) := mem_centralizer_singleton_iff.1 hg
  rw [map_zpow, Subgroup.coe_zpow]
  exact (hc.zpow_right n).symm.eq

theorem IsNsOmMinusParam.exists_edge_twist (hr' : 3 ≤ r') (htw : OmegaPlusOverlapTwist r')
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
  obtain ⟨l', rfl⟩ := Fin.exists_succAbove_eq (Ne.symm hkl)
  set φk := (centralizerPerfectCore (modelToG e (nsTorusSp K k))).subtype.comp Φ.toMonoidHom
    with hφkdef
  set φl := (centralizerPerfectCore (modelToG e (nsTorusSp K (k.succAbove l')))).subtype.comp
    Ψ.toMonoidHom with hφldef
  have hφk : Function.Injective φk := Subtype.val_injective.comp Φ.injective
  have hφl : Function.Injective φl := Subtype.val_injective.comp Ψ.injective
  obtain ⟨yl, hyl⟩ := pdMRot_mem_pcOMExt_range hK hr' hkl
  obtain ⟨yk, hyk⟩ := pdMRot_mem_pcOMExt_range hK hr' (Ne.symm hkl)
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
    have hx' : x ∈ fixedSubgroup (kOmegaBetaC K r') := hx
    rw [← range_q2OmIota (r := r') (by omega) hK (by omega)] at hx'
    obtain ⟨z, rfl⟩ := hx'
    have h1 := pcOPExt_q2OmIota l' hK (by omega : 3 ≤ r') z
    have h2 := pcOMExt_q2OmMIota k hK (by omega : 3 ≤ r' + 1) (complSpEquiv l' z)
    rw [h1, h2] at hb
    change ((Φ (pcOPExt l' (q2OmIota _ hK _ z)) : centralizerPerfectCore _) : G) = _
    rw [h1, hΦ.2]
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
    hφyk hφyl hLa hLb (pcOPExt_injective l') (pcOMExt_mem_range_iff hK hr' k l') hperf
    (pcOMExt_kOmMBetaC k) (pcOMExt_kOmMBetaC _) (pcOPExt_kOmegaBetaC l') hagree
    (fun a => (hΦ.1 a).symm) (fun b => (hΨ.1 b).symm) htw'

end Edge

section Align

open CFSG.ComponentClassification.CatalogueBOrthogonalPointData (minusIndexEquiv)

theorem kOmMBetaC_kOmMBetaC {K : Type} [Field K] [CharP K 2] {r : ℕ}
    (a : StatedOmega (StatedQuadMinus (r + 1) K 1 1)) :
    kOmMBetaC K r 1 1 (kOmMBetaC K r 1 1 a) = a := by
  have h1 : ∀ b : StatedOmega (StatedQuadMinus (r + 1) K 1 1),
      ((kOmMBetaC K r 1 1 b : StatedOmega (StatedQuadMinus (r + 1) K 1 1)) :
        GL (Fin (r + 1 - 1) ⊕ Fin (r + 1 - 1) ⊕ Fin 2) K) =
        pdSym (quadMinus (r + 1) K 1 1) (kOmMVec K r) * (b : GL _ K) *
          pdSym (quadMinus (r + 1) K 1 1) (kOmMVec K r) := fun b =>
    pd_coe_omegaSymmetryAut _ (quadMinus (r + 1) K 1 1) (coe_quadMinus (r + 1) K 1 1)
      (kOmM_matrixDerivedScalars_eq_bot K r 1 1) (kOmM_quadMinus_vec K r) b
  apply Subtype.ext
  rw [h1, h1]
  set S := pdSym (quadMinus (r + 1) K 1 1) (kOmMVec K r)
  have hS : S * S = 1 := pdSym_mul_self _ _
  calc S * (S * (a : GL (Fin (r + 1 - 1) ⊕ Fin (r + 1 - 1) ⊕ Fin 2) K) * S) * S =
        (S * S) * (a : GL (Fin (r + 1 - 1) ⊕ Fin (r + 1 - 1) ⊕ Fin 2) K) * (S * S) := by group
    _ = (a : GL (Fin (r + 1 - 1) ⊕ Fin (r + 1 - 1) ⊕ Fin 2) K) := by rw [hS, one_mul, mul_one]

variable {G : Type} [Group G] {L : Subgroup G} {K : Type} [Field K] [Finite K]
  [CharP K 2] {r' : ℕ} {hK : Nat.card K = 2} {e : L ≃* StatedSp (r' + 1 + 1) K} {t : G}

theorem exists_nsOmMinusAligned (hr' : 3 ≤ r') (htw : OmegaPlusOverlapTwist r') {hr3 : 3 ≤ r' + 1}
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
    (fun k l hkl => (hΦ k).exists_edge_twist hr' htw hkl (hΦ l))
    (fun k l hko hlo hkl => exists_triple_pcOMExt hK (by omega) (Ne.symm hko) (Ne.symm hlo) hkl)
  refine ⟨ε, fun k l g h hgh => ?_⟩
  have h1 := hε k l g h hgh
  cases hk : ε k <;> cases hl : ε l <;>
    simp only [hk, hl, Bool.false_eq_true, ite_false, ite_true, MulEquiv.trans_apply] at h1 ⊢ <;>
    exact h1

theorem spTwoOmegaMinusAlignInput_of_twist (htw : OmegaPlusOverlapTwist 3) :
    SpTwoOmegaMinusAlignInput := by
  intro G _ _ L _ r K _ _ _ hK hr e t _ _ _ Φ hΦ
  obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
  refine exists_nsOmMinusAligned (hK := hK) (by omega) ?_ Φ hΦ
  rcases (show r' = 3 ∨ 4 ≤ r' by omega) with rfl | h4
  · exact htw
  · exact omegaPlusOverlapTwist_of_four_le h4

end Align

end CFSG.SeitzReduction.SymplecticPilot
