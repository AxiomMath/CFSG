module

public import CFSG.LocalAnalysis.RankThreeTheoremC.ParabCensus.Index
public import CFSG.LocalAnalysis.AGLEmbedding.ToralCensusLinThreeSetup
public import CFSG.LargeExtraspecial.A2ModSLModel

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.ParabCensus

open CFSG.AGLEmbedding CFSG.AGLEmbedding.LeviBlock Subgroup

theorem hasLeviCensus_of_comap_eq_flagStabilizer {X : Type} [Group X] {L J : Subgroup X}
    (hJL : J ≤ L) {n : ℕ} (hn : 1 ≤ n) {K : Type} [Field K] [Finite K] [CharP K 2]
    (ρ : Matrix.SpecialLinearGroup (Fin n) K →* ↥L) (hρ : Function.Surjective ρ)
    (hker : ρ.ker ≤ center (Matrix.SpecialLinearGroup (Fin n) K)) {I : Set ℕ}
    (hcomap : (J.subgroupOf L).comap ρ =
      CFSG.LocalAnalysis.ComponentInitial.LinearFlag.flagStabilizer n K I) :
    HasLeviCensus ↥J IsWBlock := by
  classical
  set β : ↥((J.subgroupOf L).comap ρ) →* ∀ a : Fin n, GL (Fin (linBlockLen n I a)) K :=
    (linLeviHom K n I).comp (MulEquiv.subgroupCongr hcomap).toMonoidHom with hβdef
  have hβrange : β.range = (linLeviHom K n I).range := by
    rw [hβdef, MonoidHom.range_comp,
      MonoidHom.range_eq_top.mpr (MulEquiv.subgroupCongr hcomap).surjective, Subgroup.map_top]
  refine hasLeviCensus_of_cover (S := linBlockSL K n I) hJL ρ hρ hker ?_ β ?_ ?_ ?_ ?_ ?_ ?_
  ·
    refine Odd.of_dvd_nat ?_ (Subgroup.card_dvd_of_le hker)
    rw [← Nat.not_even_iff_odd, even_iff_two_dvd]
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mp
      (CFSG.RankThree.PartTwo.Census.coprime_card_center_SL hn).symm
  ·
    have hβeq : β.ker = (linLeviHom K n I).ker.comap
        (MulEquiv.subgroupCongr hcomap).toMonoidHom := by
      rw [hβdef]
      ext x
      simp only [MonoidHom.mem_ker, MonoidHom.comp_apply, Subgroup.mem_comap]
    rw [hβeq]
    exact IsPGroup.comap_of_injective (isPGroup_ker_linLeviHom hn)
      (MulEquiv.subgroupCongr hcomap).toMonoidHom (MulEquiv.subgroupCongr hcomap).injective
  · rw [hβrange]
    exact pi_le_range_linLeviHom
  · rw [hβrange]
    exact le_normalizer_of_commutator_le pi_le_range_linLeviHom commutator_range_linLeviHom_le
  ·
    have h : ¬ 2 ∣ (Subgroup.pi Set.univ (linBlockSL K n I)).relIndex
        (linLeviHom K n I).range := by
      refine not_two_dvd_relIndex_pi (S := linBlockSL K n I) (T := fun _ => ⊤) (fun _ => le_top)
        pi_le_range_linLeviHom ?_ ?_
      · rw [Subgroup.pi_top]
        exact le_top
      · intro a
        rw [Subgroup.relIndex_top_right]
        exact not_two_dvd_index_range_toGL (K := K) (linBlockLen n I a)
    rwa [hβrange]
  ·
    intro a
    rcases range_toGL_cases (K := K) (linBlockLen n I a) with h | ⟨-, -, h⟩ | ⟨hq, ho⟩
    · exact Or.inl h
    · exact Or.inr (Or.inr h)
    · exact Or.inr (Or.inl ⟨hq, ho⟩)
  ·
    intro a hna z hz hmem
    rcases range_toGL_cases (K := K) (linBlockLen n I a) with hbot | ⟨hK, -, -⟩ | ⟨hq, -⟩
    · have hbot' : linBlockSL K n I a = ⊥ := hbot
      have h1 : β z ∈ (⊥ : Subgroup (∀ j, GL (Fin (linBlockLen n I j)) K)) := by
        rw [hbot', Subgroup.map_bot] at hmem
        exact hmem
      exact Subgroup.mem_bot.mp h1
    ·
      have hcent : center (Matrix.SpecialLinearGroup (Fin n) K) = ⊥ :=
        CFSG.LargeExtraspecial.A2Mod.sl_center_eq_bot_of_card_two hK
      have hz1 : (z : Matrix.SpecialLinearGroup (Fin n) K) = 1 := by
        have h := hker (MonoidHom.mem_ker.mpr hz)
        rwa [hcent, Subgroup.mem_bot] at h
      rw [show z = 1 from Subtype.ext hz1, map_one]
    · exact absurd hq hna


theorem hasLeviCensus_idxA (hGA : CFSG.Open.GriessAllModelsStatement) {X : Type} [Group X]
    [Finite X] {L J : Subgroup X} (hCP : CompParab L J) (h : IsLieOf IdxA (↥L ⧸ center ↥L)) :
    HasLeviCensus ↥J IsWBlock := by
  obtain ⟨n, f, ρ, -, I, hn3, -, hρs, hρk, -, -, -, -, hcomap⟩ :=
    CFSG.AGLEmbedding.ToralCensus.exists_cover_comap_eq_flagStabilizer hGA hCP h
  exact hasLeviCensus_of_comap_eq_flagStabilizer hCP.parab.1 (by omega) ρ hρs hρk hcomap

end CFSG.LocalAnalysis.RankThreeTheoremC.ParabCensus
