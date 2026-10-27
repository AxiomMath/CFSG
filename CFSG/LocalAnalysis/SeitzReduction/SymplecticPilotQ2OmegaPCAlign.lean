module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2OmegaPCPlusFrame
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2OmegaPCAut

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.SeitzReduction.F4Pilot (centralizerPerfectCore)
open CFSG.SeitzReduction.UnitaryPilot (modelToG)

section Aligned

variable {G : Type} [Group G] {L : Subgroup G} {K : Type} [Field K] [Finite K] [CharP K 2]
  {r : ℕ}

@[expose] def NsOmMinusAligned (e : L ≃* StatedSp (r + 1) K)
    (Φ : ∀ k : Fin (r + 1), StatedOmega (StatedQuadMinus (r + 1) K 1 1) ≃*
      centralizerPerfectCore (modelToG e (nsTorusSp K k))) : Prop :=
  ∀ (k l : Fin (r + 1)) (g h : StatedOmega (StatedQuadMinus (r + 1) K 1 1)),
    pcOMExt k g = pcOMExt l h →
      ((Φ k g : centralizerPerfectCore (modelToG e (nsTorusSp K k))) : G) =
        ((Φ l h : centralizerPerfectCore (modelToG e (nsTorusSp K l))) : G)

@[expose] def NsOmPlusAligned (e : L ≃* StatedSp (r + 1) K)
    (Φ : ∀ k : Fin (r + 1), StatedOmega (StatedQuadPlus (r + 1) K) ≃*
      centralizerPerfectCore (modelToG e (nsTorusSp K k))) : Prop :=
  ∀ (k l : Fin (r + 1)) (g h : StatedOmega (StatedQuadPlus (r + 1) K)),
    pcOPExt k g = pcOPExt l h →
      ((Φ k g : centralizerPerfectCore (modelToG e (nsTorusSp K k))) : G) =
        ((Φ l h : centralizerPerfectCore (modelToG e (nsTorusSp K l))) : G)

variable {hK : Nat.card K = 2} {e : L ≃* StatedSp (r + 1) K} {t : G} {k : Fin (r + 1)}

theorem IsNsOmMinusParam.coe_eq_of_pcOMExt_eq {hr3 : 3 ≤ r}
    {Φ : StatedOmega (StatedQuadMinus (r + 1) K 1 1) ≃*
      centralizerPerfectCore (modelToG e (nsTorusSp K k))}
    (hΦ : IsNsOmMinusParam hK hr3 e t k Φ) {y : StatedSp (r + 1) K} (hy : y ∈ complSp K k)
    {g : StatedOmega (StatedQuadMinus (r + 1) K 1 1)}
    (hg : pcOMExt k g = q2OmIota (r := r + 1) (by omega) hK (by omega) y) :
    ((Φ g : centralizerPerfectCore (modelToG e (nsTorusSp K k))) : G) = ((e.symm y : L) : G) := by
  obtain ⟨x, hx⟩ := (complSpEquiv (K := K) k).surjective ⟨y, hy⟩
  have hy' : y = ((complSpEquiv (K := K) k x : complSp K k) : StatedSp (r + 1) K) := by
    rw [hx]
  have hgx : g = q2OmMIota hr3 (q2Omega_irreducible_one_one hK) hK x := by
    apply pcOMExt_injective k
    rw [hg, pcOMExt_q2OmMIota k hK hr3 x, hy']
  rw [hgx, hΦ.2 x, hy']

theorem IsNsOmPlusParam.coe_eq_of_pcOPExt_eq {hr : 2 ≤ r} {hr3 : 3 ≤ r}
    {Φ : StatedOmega (StatedQuadPlus (r + 1) K) ≃*
      centralizerPerfectCore (modelToG e (nsTorusSp K k))}
    (hΦ : IsNsOmPlusParam hK hr hr3 e t k Φ) {y : StatedSp (r + 1) K} (hy : y ∈ complSp K k)
    {g : StatedOmega (StatedQuadPlus (r + 1) K)}
    (hg : pcOPExt k g = q2OmMIota (r := r + 1) (by omega) (q2Omega_irreducible_one_one hK) hK y) :
    ((Φ g : centralizerPerfectCore (modelToG e (nsTorusSp K k))) : G) = ((e.symm y : L) : G) := by
  obtain ⟨x, hx⟩ := (complSpEquiv (K := K) k).surjective ⟨y, hy⟩
  have hy' : y = ((complSpEquiv (K := K) k x : complSp K k) : StatedSp (r + 1) K) := by
    rw [hx]
  have hgx : g = q2OmIota hr hK hr3 x := by
    apply pcOPExt_injective k
    rw [hg, pcOPExt_q2OmIota k hK hr3 x, hy']
  rw [hgx, hΦ.2 x, hy']

theorem IsNsOmMinusParam.agree_on_iota {hr3 : 3 ≤ r} {l : Fin (r + 1)}
    {Φ : StatedOmega (StatedQuadMinus (r + 1) K 1 1) ≃*
      centralizerPerfectCore (modelToG e (nsTorusSp K k))}
    {Ψ : StatedOmega (StatedQuadMinus (r + 1) K 1 1) ≃*
      centralizerPerfectCore (modelToG e (nsTorusSp K l))}
    (hΦ : IsNsOmMinusParam hK hr3 e t k Φ) (hΨ : IsNsOmMinusParam hK hr3 e t l Ψ)
    {y : StatedSp (r + 1) K} (hyk : y ∈ complSp K k) (hyl : y ∈ complSp K l)
    {g h : StatedOmega (StatedQuadMinus (r + 1) K 1 1)}
    (hg : pcOMExt k g = q2OmIota (r := r + 1) (by omega) hK (by omega) y)
    (hh : pcOMExt l h = q2OmIota (r := r + 1) (by omega) hK (by omega) y) :
    ((Φ g : centralizerPerfectCore (modelToG e (nsTorusSp K k))) : G) =
      ((Ψ h : centralizerPerfectCore (modelToG e (nsTorusSp K l))) : G) :=
  (hΦ.coe_eq_of_pcOMExt_eq hyk hg).trans (hΨ.coe_eq_of_pcOMExt_eq hyl hh).symm

theorem IsNsOmPlusParam.agree_on_iota {hr : 2 ≤ r} {hr3 : 3 ≤ r} {l : Fin (r + 1)}
    {Φ : StatedOmega (StatedQuadPlus (r + 1) K) ≃*
      centralizerPerfectCore (modelToG e (nsTorusSp K k))}
    {Ψ : StatedOmega (StatedQuadPlus (r + 1) K) ≃*
      centralizerPerfectCore (modelToG e (nsTorusSp K l))}
    (hΦ : IsNsOmPlusParam hK hr hr3 e t k Φ) (hΨ : IsNsOmPlusParam hK hr hr3 e t l Ψ)
    {y : StatedSp (r + 1) K} (hyk : y ∈ complSp K k) (hyl : y ∈ complSp K l)
    {g h : StatedOmega (StatedQuadPlus (r + 1) K)}
    (hg : pcOPExt k g = q2OmMIota (r := r + 1) (by omega) (q2Omega_irreducible_one_one hK) hK y)
    (hh : pcOPExt l h = q2OmMIota (r := r + 1) (by omega) (q2Omega_irreducible_one_one hK) hK y) :
    ((Φ g : centralizerPerfectCore (modelToG e (nsTorusSp K k))) : G) =
      ((Ψ h : centralizerPerfectCore (modelToG e (nsTorusSp K l))) : G) :=
  (hΦ.coe_eq_of_pcOPExt_eq hyk hg).trans (hΨ.coe_eq_of_pcOPExt_eq hyl hh).symm

end Aligned

@[expose] def SpTwoOmegaMinusAlignInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), SeitzSetting G L →
    ∀ (r : ℕ) (K : Type) [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = 2) (hr : 4 ≤ r)
    (e : L ≃* StatedSp (r + 1) K) (t : G), orderOf t = 2 →
      centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t →
      (∀ k : Fin (r + 1), NsKindSp e t k .omegaMinus) →
      ∀ Φ : ∀ k : Fin (r + 1), StatedOmega (StatedQuadMinus (r + 1) K 1 1) ≃*
          centralizerPerfectCore (modelToG e (nsTorusSp K k)),
        (∀ k, IsNsOmMinusParam hK (by omega) e t k (Φ k)) →
        ∃ ε : Fin (r + 1) → Bool, NsOmMinusAligned e fun k =>
          if ε k then (kOmMBetaC K r 1 1).trans (Φ k) else Φ k

@[expose] def SpTwoOmegaMinusPlaceInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), SeitzSetting G L →
    ∀ (r : ℕ) (K : Type) [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = 2) (hr : 4 ≤ r)
    (e : L ≃* StatedSp (r + 1) K) (t : G), orderOf t = 2 →
      centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t →
      (∀ k : Fin (r + 1), NsKindSp e t k .omegaMinus) →
      ∀ Φ : ∀ k : Fin (r + 1), StatedOmega (StatedQuadMinus (r + 1) K 1 1) ≃*
          centralizerPerfectCore (modelToG e (nsTorusSp K k)),
        (∀ k, IsNsOmMinusParam hK (by omega) e t k (Φ k)) → NsOmMinusAligned e Φ →
          NsOmegaCTData e .omegaMinus

@[expose] def SpTwoOmegaPlusAlignInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), SeitzSetting G L →
    ∀ (r : ℕ) (K : Type) [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = 2) (hr : 4 ≤ r)
    (e : L ≃* StatedSp (r + 1) K) (t : G), orderOf t = 2 →
      centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t →
      (∀ k : Fin (r + 1), NsKindSp e t k .omegaPlus) →
      ∀ Φ : ∀ k : Fin (r + 1), StatedOmega (StatedQuadPlus (r + 1) K) ≃*
          centralizerPerfectCore (modelToG e (nsTorusSp K k)),
        (∀ k, IsNsOmPlusParam hK (by omega) (by omega) e t k (Φ k)) →
        ∃ ε : Fin (r + 1) → Bool, NsOmPlusAligned e fun k =>
          if ε k then (kOmegaBetaC K r).trans (Φ k) else Φ k

@[expose] def SpTwoOmegaPlusPlaceInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), SeitzSetting G L →
    ∀ (r : ℕ) (K : Type) [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = 2) (hr : 4 ≤ r)
    (e : L ≃* StatedSp (r + 1) K) (t : G), orderOf t = 2 →
      centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t →
      (∀ k : Fin (r + 1), NsKindSp e t k .omegaPlus) →
      ∀ Φ : ∀ k : Fin (r + 1), StatedOmega (StatedQuadPlus (r + 1) K) ≃*
          centralizerPerfectCore (modelToG e (nsTorusSp K k)),
        (∀ k, IsNsOmPlusParam hK (by omega) (by omega) e t k (Φ k)) → NsOmPlusAligned e Φ →
          NsOmegaCTData e .omegaPlus

theorem spTwoOmegaMinusParamCTInput_of_align_place (hA : SpTwoOmegaMinusAlignInput)
    (hP : SpTwoOmegaMinusPlaceInput) : SpTwoOmegaMinusParamCTInput := by
  intro G _ _ L hset r K _ _ _ hK hr e t ht hKt hroot Φ hΦ
  obtain ⟨ε, hε⟩ := hA G L hset r K hK hr e t ht hKt hroot Φ hΦ
  refine hP G L hset r K hK hr e t ht hKt hroot _ (fun k => ?_) hε
  split_ifs
  · exact (hΦ k).comp_betaC
  · exact hΦ k

theorem spTwoOmegaPlusParamCTInput_of_align_place (hA : SpTwoOmegaPlusAlignInput)
    (hP : SpTwoOmegaPlusPlaceInput) : SpTwoOmegaPlusParamCTInput := by
  intro G _ _ L hset r K _ _ _ hK hr e t ht hKt hroot Φ hΦ
  obtain ⟨ε, hε⟩ := hA G L hset r K hK hr e t ht hKt hroot Φ hΦ
  refine hP G L hset r K hK hr e t ht hKt hroot _ (fun k => ?_) hε
  split_ifs
  · exact (hΦ k).comp_betaC
  · exact hΦ k

end CFSG.SeitzReduction.SymplecticPilot
