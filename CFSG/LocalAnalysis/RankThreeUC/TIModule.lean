module

public import CFSG.LocalAnalysis.RankThreeUC.ModuleRank
public import CFSG.CGT.Timmesfeld75.Defs

public section

namespace CFSG.LocalAnalysis.RankThreeUC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.LocalAnalysis.RankThreeTheoremC Subgroup
open CFSG.CGT.Timmesfeld75 (IsTI conjSubgroup)

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem isTI_of_forall {V : Subgroup G}
    (h : ∀ g : G, V ⊓ V.map (MulAut.conj g).toMonoidHom = ⊥ ∨
      V.map (MulAut.conj g).toMonoidHom = V) : IsTI V := fun g =>
  (h g).imp id fun hg => by
    change V ⊓ V.map (MulAut.conj g).toMonoidHom = V
    rw [hg, inf_idem]

theorem map_conj_eq_of_isTI {V : Subgroup G} (hV : IsTI V) {g : G}
    (hne : V ⊓ V.map (MulAut.conj g).toMonoidHom ≠ ⊥) : V.map (MulAut.conj g).toMonoidHom = V := by
  rcases hV g with h | h
  · exact absurd h hne
  · have hle : V ≤ V.map (MulAut.conj g).toMonoidHom := by
      change V ⊓ V.map (MulAut.conj g).toMonoidHom = V at h
      exact inf_eq_left.mp h
    exact (eq_of_le_of_card_ge hle (card_map_of_injective (MulAut.conj g).injective).le).symm

theorem IsWitnessGen.isTI_of_two_le_pRank {p : ℕ} {P : Sylow p G} {M : Subgroup G}
    (hp : p.Prime) (hw : IsWitnessGen p P M) {V : Subgroup G} (hV2 : IsPGroup 2 V)
    (hMV : M ≤ normalizer (V : Set G)) (h2 : 2 ≤ pRank p (M ⊓ centralizer (V : Set G))) :
    IsTI V :=
  isTI_of_forall (hw.conj_eq_or_inf_eq_bot hp hV2 hMV h2)

theorem IsWitnessGen.pRank_normalizer_of_not_isTI
    (hS : CFSG.LocalAnalysis.AGL81TheoremCD.StandingGen G) {p : ℕ} {P : Sylow p G}
    {M : Subgroup G} (hp : IsWitnessPrime p P) (hw : IsWitnessGen p P M) {V T : Subgroup G}
    (hV2 : IsPGroup 2 V) (hMV : M ≤ normalizer (V : Set G))
    (hT : CFSG.ABGLocalTools.IsSylowOf 2 T M) (hnTI : ¬ IsTI V) :
    pRank p (M ⊓ centralizer (V : Set G)) ≤ 1 ∧
      2 ≤ pRank p (M ⊓ normalizer ((T ⊓ centralizer (V : Set G) : Subgroup G) : Set G)) ∧
      ∀ H : Subgroup G, rankThreeIsMaxTwoLocal H →
        M ⊓ normalizer ((T ⊓ centralizer (V : Set G) : Subgroup G) : Set G) ≤ H → H = M := by
  have h1 : pRank p (M ⊓ centralizer (V : Set G)) ≤ 1 := by
    by_contra h
    exact hnTI (hw.isTI_of_two_le_pRank hp.prime hV2 hMV (by omega))
  have h2 := (hw.two_le_pRank_normalizer_or_centralizer hS hp hMV hT).resolve_right (by omega)
  exact ⟨h1, h2, fun H hH hNH => hw.eq_of_le_of_two_le_pRank hp.prime inf_le_left h2 hH hNH⟩

theorem IsWitness.pRank_normalizer_of_not_isTI (hS : Standing G) {p : ℕ} {P : Sylow p G}
    {M : Subgroup G} (hp : p ∈ rankThreeSigmaA G) (hw : IsWitness p P M) {V T : Subgroup G}
    (hV2 : IsPGroup 2 V) (hMV : M ≤ normalizer (V : Set G))
    (hT : CFSG.ABGLocalTools.IsSylowOf 2 T M) (hnTI : ¬ IsTI V) :
    pRank p (M ⊓ centralizer (V : Set G)) ≤ 1 ∧
      2 ≤ pRank p (M ⊓ normalizer ((T ⊓ centralizer (V : Set G) : Subgroup G) : Set G)) ∧
      ∀ H : Subgroup G, rankThreeIsMaxTwoLocal H →
        M ⊓ normalizer ((T ⊓ centralizer (V : Set G) : Subgroup G) : Set G) ≤ H → H = M :=
  IsWitnessGen.pRank_normalizer_of_not_isTI hS.toGen
    (IsWitnessPrime.of_mem_sigmaA hS hp P) hw.toGen hV2 hMV hT hnTI

theorem centralizer_le_of_isTI {M U : Subgroup G} (hM : rankThreeIsMaxTwoLocal M) (hU : U ≠ ⊥)
    (hU2 : IsPGroup 2 U) (hMU : M ≤ normalizer (U : Set G)) (hTI : IsTI U) {u : G} (huU : u ∈ U)
    (hu : u ≠ 1) : centralizer ({u} : Set G) ≤ M := by
  intro g hg
  rw [← normalizer_eq_of_isMaxTwoLocal hM hU hU2 hMU]
  refine mem_normalizer_iff_map_conj_eq.mpr (map_conj_eq_of_isTI hTI fun hbot => hu ?_)
  have hgu : g * u * g⁻¹ = u := by
    rw [mem_centralizer_singleton_iff.mp hg, mul_inv_cancel_right]
  have hmem : u ∈ U ⊓ U.map (MulAut.conj g).toMonoidHom :=
    ⟨huU, ⟨u, huU, by simpa [MulAut.conj_apply] using hgu⟩⟩
  rw [hbot] at hmem
  exact (mem_bot.mp hmem)

end CFSG.LocalAnalysis.RankThreeUC
