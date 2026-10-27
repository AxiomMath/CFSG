module

public import CFSG.LocalAnalysis.RankThreeUC.TheoremDResidual
public import CFSG.LocalAnalysis.RankThreeUC.TheoremDThompsonCore
public import CFSG.Quasithin.Background.Basic
import CFSG.LocalAnalysis.RankThreeUC.TheoremDReductions
import CFSG.LocalAnalysis.RankThreeUC.TheoremDSolvableQuotient
import CFSG.LocalAnalysis.RankThreeUC.TIModule

public section

namespace CFSG.LocalAnalysis.RankThreeUC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup
open CFSG.LocalAnalysis.AGL81TheoremCD (StandingGen)

variable {G : Type} [Group G] [Finite G]

private theorem le_of_isPGroup_of_le_normalizer {M T V : Subgroup G}
    (hT : CFSG.ABGLocalTools.IsSylowOf 2 T M) (hV2 : IsPGroup 2 V) (hVM : V ≤ M)
    (hMV : M ≤ normalizer (V : Set G)) : V ≤ T := by
  have hsup := hT.isPGroup.to_sup_of_normal_right' hV2 (hT.le.trans hMV)
  exact sup_eq_left.mp (hT.eq_of_le le_sup_left (sup_le hT.le hVM) hsup)

namespace IsWitness

variable {p : ℕ} {P : Sylow p G} {M : Subgroup G}

theorem
    _root_.CFSG.LocalAnalysis.RankThreeUC.IsWitnessGen.normalizer_le_or_isTI_of_normalizer_le
    (hS : StandingGen G) (hp : IsWitnessPrime p P) (hw : IsWitnessGen p P M) {T V : Subgroup G}
    (hT : CFSG.ABGLocalTools.IsSylowOf 2 T M)
    (hV : IsElemAbelian 2 V) (hV1 : V ≠ ⊥) (hVT : V ≤ T) (hMV : M ≤ normalizer (V : Set G))
    (hN : normalizer (T : Set G) ≤
      normalizer ((T ⊓ centralizer (V : Set G) : Subgroup G) : Set G)) :
    normalizer (T : Set G) ≤ M ∨
      (2 ≤ CFSG.Open.pRank p (M ⊓ centralizer (V : Set G)) ∧ CFSG.CGT.Timmesfeld75.IsTI V) := by
  rcases hw.two_le_pRank_normalizer_or_centralizer hS hp hMV hT with h | h
  · left
    have hVC : V ≤ T ⊓ centralizer (V : Set G) := le_inf hVT fun v hv =>
      mem_centralizer_iff.mpr fun w hw' => congrArg Subtype.val (hV.1.is_comm.comm ⟨w, hw'⟩ ⟨v, hv⟩)
    exact hw.normalizer_le_of_two_le_pRank_normalizer hS hp hT
      (fun h' => hV1 (le_bot_iff.mp (h' ▸ hVC))) inf_le_left hN
      (h.trans (pRank_mono p hp.prime.one_lt inf_le_right))
  · exact Or.inr ⟨h, hw.isTI_of_two_le_pRank hp.prime (elementary_isPGroup 2 V hV) hMV h⟩

theorem
    _root_.CFSG.LocalAnalysis.RankThreeUC.IsWitnessGen.normalizer_le_of_normalizer_le_inf_centralizer_uCore
    (hS : StandingGen G) (hp : IsWitnessPrime p P) (hw : IsWitnessGen p P M) {T : Subgroup G}
    (hT : CFSG.ABGLocalTools.IsSylowOf 2 T M)
    (hN : normalizer (T : Set G) ≤
      normalizer ((T ⊓ centralizer (uCore M T : Set G) : Subgroup G) : Set G)) :
    normalizer (T : Set G) ≤ M := by
  have hT1 : T ≠ ⊥ := ne_bot_of_isSylowOf_two hw.maxLocal.1 hT
  have hZ1 := CFSG.RankThree.PartOne.Sec15Final.omegaOneCenterIn_ne_bot hT.isPGroup hT1
  obtain ⟨hUM, hUe⟩ := uCore_le_and_isElemAbelian hS.charTwo hw.maxLocal.1 hT
  have hU2 := elementary_isPGroup 2 _ hUe
  have hUM' : uCore M T ≤ M := hUM.trans (inf_le_left.trans (pCoreOf_le 2 M))
  rcases hw.normalizer_le_or_isTI_of_normalizer_le hS hp hT hUe
    (fun h => hZ1 (le_bot_iff.mp (h ▸ omegaOneCenterIn_le_uCore M T)))
    (le_of_isPGroup_of_le_normalizer hT hU2 hUM' (le_normalizer_uCore M T))
    (le_normalizer_uCore M T) hN with h | ⟨-, hTI⟩
  · exact h
  · exact hw.normalizer_le_of_isTI_uCore hS hT hTI

theorem
    _root_.CFSG.LocalAnalysis.RankThreeUC.IsWitnessGen.normalizer_le_of_forall_conj_two_le_pRank
    (hp : p.Prime) (hw : IsWitnessGen p P M) {T Y : Subgroup G}
    (hT : CFSG.ABGLocalTools.IsSylowOf 2 T M) (hY1 : Y ≠ ⊥) (hYT : Y ≤ T)
    (h : ∀ n ∈ normalizer (T : Set G), 2 ≤ CFSG.Open.pRank p
      (M ⊓ normalizer ((Y.map (MulAut.conj n).toMonoidHom : Subgroup G) : Set G))) :
    normalizer (T : Set G) ≤ M := by
  intro n hn
  have h1 : normalizer ((Y.map (MulAut.conj n).toMonoidHom : Subgroup G) : Set G) ≤ M := by
    refine hw.u2 _ ⟨Y.map (MulAut.conj n).toMonoidHom, ?_, (hT.isPGroup.to_le hYT).map _, rfl⟩ ?_
    · exact (Subgroup.map_eq_bot_iff_of_injective Y (MulAut.conj n).injective).not.mpr hY1
    · rw [inf_comm]
      exact h n hn
  have h2 : normalizer (Y : Set G) ≤ M.map (MulAut.conj n⁻¹).toMonoidHom := by
    intro x hx
    have hx' : n * x * n⁻¹ ∈
        normalizer ((Y.map (MulAut.conj n).toMonoidHom : Subgroup G) : Set G) := by
      rw [← map_equiv_normalizer_eq Y (MulAut.conj n)]
      exact mem_map_of_mem _ hx
    exact ⟨n * x * n⁻¹, h1 hx', by simp [mul_assoc]⟩
  have h3 : 2 ≤ CFSG.Open.pRank p (M ⊓ normalizer (Y : Set G)) := by
    have h1' : Y.map (MulAut.conj (1 : G)).toMonoidHom = Y := by
      ext x
      simp
    have := h 1 (one_mem _)
    rwa [h1'] at this
  have h4 : M.map (MulAut.conj n⁻¹).toMonoidHom ≤ M := by
    refine hw.u2 _ (twoLocal_map_automorphism M hw.maxLocal.1 _) ?_
    refine h3.trans (pRank_mono p ?_ ?_)
    · exact hp.one_lt
    · exact le_inf (inf_le_right.trans h2) inf_le_left
  have h5 : M.map (MulAut.conj n⁻¹).toMonoidHom = M :=
    Subgroup.eq_of_le_of_card_ge h4 (Subgroup.card_map_of_injective (MulAut.conj n⁻¹).injective).ge
  have h6 : n⁻¹ ∈ M := by
    rw [← maxTwoLocal_self_normalizing M hw.maxLocal]
    exact mem_normalizer_iff_map_conj_eq.mpr h5
  simpa using M.inv_mem h6

theorem normalizer_le_of_forall_conj_two_le_pRank (hp : p ∈ rankThreeSigmaA G)
    (hw : IsWitness p P M) {T Y : Subgroup G}
    (hT : CFSG.ABGLocalTools.IsSylowOf 2 T M) (hY1 : Y ≠ ⊥) (hYT : Y ≤ T)
    (h : ∀ n ∈ normalizer (T : Set G), 2 ≤ CFSG.Open.pRank p
      (M ⊓ normalizer ((Y.map (MulAut.conj n).toMonoidHom : Subgroup G) : Set G))) :
    normalizer (T : Set G) ≤ M :=
  IsWitnessGen.normalizer_le_of_forall_conj_two_le_pRank (sigmaA_prime p hp) hw.toGen hT hY1
    hYT h

end IsWitness

@[expose] def AGL81Residual2Gen (G : Type) [Group G] [Finite G]
    (W : ∀ p : ℕ, Sylow p G → Subgroup G → Prop) : Prop :=
  ∀ (p : ℕ) (P : Sylow p G) (M : Subgroup G), W p P M → ∀ T : Subgroup G,
    CFSG.ABGLocalTools.IsSylowOf 2 T M →
      ¬ thompsonSubgroup T ≤ centralizer (uCore M T : Set G) →
      ¬ CFSG.CGT.Timmesfeld75.IsTI (uCore M T) →
      (∀ C : Subgroup G, C ≠ ⊥ → C ≤ T → (C.subgroupOf T).Characteristic →
        CFSG.Open.pRank p (normalizer (C : Set G)) ≤ 1) →
      (p = 3 ∨ ¬ Group.IsSolvable ↥(CFSG.Quasithin.autOn M (uCore M T))) →
      normalizer (T : Set G) ≤ M
theorem agl81ResidualGen_of_residual2Gen (hS : StandingGen G)
    {W : ∀ p : ℕ, Sylow p G → Subgroup G → Prop}
    (hW : ∀ (p : ℕ) (P : Sylow p G) (M : Subgroup G), W p P M →
      IsWitnessPrime p P ∧ IsWitnessGen p P M)
    (hR : AGL81Residual2Gen G W) : AGL81ResidualGen G W := by
  intro p P M hw T hT hJ hTI hC
  obtain ⟨hp, hw'⟩ := hW p P M hw
  by_cases h3 : p = 3
  · exact hR p P M hw T hT hJ hTI hC (Or.inl h3)
  by_cases hsolv : Group.IsSolvable ↥(CFSG.Quasithin.autOn M (uCore M T))
  · have hp4 : p ≠ 4 := by
      rintro rfl
      exact absurd hp.prime (by decide)
    have hp5 : 5 ≤ p := by
      have h2 : 2 ≤ p := hp.prime.two_le
      have hodd : p ≠ 2 := hp.odd
      omega
    exact hw'.normalizer_le_of_solvable_quotient hS hp hp5 hT hsolv
  · exact hR p P M hw T hT hJ hTI hC (Or.inr hsolv)

theorem agl81TheoremDGen_of_residual2Gen (hS : StandingGen G)
    {W : ∀ p : ℕ, Sylow p G → Subgroup G → Prop}
    (hW : ∀ (p : ℕ) (P : Sylow p G) (M : Subgroup G), W p P M →
      IsWitnessPrime p P ∧ IsWitnessGen p P M)
    (hR : AGL81Residual2Gen G W) : AGL81TheoremDGen G W :=
  agl81TheoremDGen_of_residualGen hS hW (agl81ResidualGen_of_residual2Gen hS hW hR)

@[expose] def AGL81Residual3Gen (G : Type) [Group G] [Finite G]
    (W : ∀ p : ℕ, Sylow p G → Subgroup G → Prop) : Prop :=
  ∀ (p : ℕ) (P : Sylow p G) (M : Subgroup G), W p P M → ∀ T : Subgroup G,
    CFSG.ABGLocalTools.IsSylowOf 2 T M →
      ¬ thompsonSubgroup T ≤ centralizer (uCore M T : Set G) →
      ¬ CFSG.Quasithin.thompsonJ T ≤ centralizer (uCore M T : Set G) →
      ¬ CFSG.CGT.Timmesfeld75.IsTI (uCore M T) →
      (∀ C : Subgroup G, C ≠ ⊥ → C ≤ T → (C.subgroupOf T).Characteristic →
        CFSG.Open.pRank p (normalizer (C : Set G)) ≤ 1) →
      (p = 3 ∨ ¬ Group.IsSolvable ↥(CFSG.Quasithin.autOn M (uCore M T))) →
      ¬ normalizer (T : Set G) ≤
        normalizer ((T ⊓ centralizer (uCore M T : Set G) : Subgroup G) : Set G) →
      (∀ Y : Subgroup G, Y ≠ ⊥ → Y ≤ T → ∃ n ∈ normalizer (T : Set G),
        CFSG.Open.pRank p
          (M ⊓ normalizer ((Y.map (MulAut.conj n).toMonoidHom : Subgroup G) : Set G)) ≤ 1) →
      2 ≤ CFSG.Open.pRank p (thompsonCore M T) →
      2 ≤ CFSG.Open.pRank p (CFSG.Quasithin.thompsonJ M) →
      normalizer (T : Set G) ≤ M
theorem agl81Residual2Gen_of_residual3Gen (hS : StandingGen G)
    {W : ∀ p : ℕ, Sylow p G → Subgroup G → Prop}
    (hW : ∀ (p : ℕ) (P : Sylow p G) (M : Subgroup G), W p P M →
      IsWitnessPrime p P ∧ IsWitnessGen p P M)
    (hR : AGL81Residual3Gen G W) : AGL81Residual2Gen G W := by
  intro p P M hw T hT hJ hTI hC hsol
  obtain ⟨hp, hw'⟩ := hW p P M hw
  by_cases hJe : CFSG.Quasithin.thompsonJ T ≤ centralizer (uCore M T : Set G)
  · exact hw'.normalizer_le_of_thompsonJ_le_centralizer hS hp hT hJe
  by_cases hN : normalizer (T : Set G) ≤
      normalizer ((T ⊓ centralizer (uCore M T : Set G) : Subgroup G) : Set G)
  · exact hw'.normalizer_le_of_normalizer_le_inf_centralizer_uCore hS hp hT hN
  by_cases hY : ∃ Y : Subgroup G, Y ≠ ⊥ ∧ Y ≤ T ∧ ∀ n ∈ normalizer (T : Set G),
      2 ≤ CFSG.Open.pRank p
        (M ⊓ normalizer ((Y.map (MulAut.conj n).toMonoidHom : Subgroup G) : Set G))
  · obtain ⟨Y, hY1, hYT, hYn⟩ := hY
    exact hw'.normalizer_le_of_forall_conj_two_le_pRank hp.prime hT hY1 hYT hYn
  by_cases hCore : CFSG.Open.pRank p (thompsonCore M T) ≤ 1
  · exact hw'.normalizer_le_of_pRank_thompsonCore_le_one hS hp hT hCore
  by_cases hJM : CFSG.Open.pRank p (CFSG.Quasithin.thompsonJ M) ≤ 1
  · exact hw'.normalizer_le_of_pRank_thompsonJ_le_one hS hp hT hJM
  refine hR p P M hw T hT hJ hJe hTI hC hsol hN ?_ (by omega) (by omega)
  intro Y hY1 hYT
  by_contra hcon
  refine hY ⟨Y, hY1, hYT, fun n hn => ?_⟩
  by_contra hlt
  exact hcon ⟨n, hn, by omega⟩

theorem agl81TheoremDGen_of_residual3Gen (hS : StandingGen G)
    {W : ∀ p : ℕ, Sylow p G → Subgroup G → Prop}
    (hW : ∀ (p : ℕ) (P : Sylow p G) (M : Subgroup G), W p P M →
      IsWitnessPrime p P ∧ IsWitnessGen p P M)
    (hR : AGL81Residual3Gen G W) : AGL81TheoremDGen G W :=
  agl81TheoremDGen_of_residual2Gen hS hW (agl81Residual2Gen_of_residual3Gen hS hW hR)

end CFSG.LocalAnalysis.RankThreeUC
