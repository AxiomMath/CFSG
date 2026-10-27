module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFactParabolicLeviSubOPData
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFactParabolicLeviSubOPFlag

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

namespace KPLeviSub

open CFSG.Open Subgroup CFSG.AGLEmbedding.LeviBlock CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit CFSG.LieType.Universal.Spin
open CFSG.ComponentClassification.CatalogueBOrthogonalPointPlusBorel
  (native_partialBorel_eq_fullBorel)

variable {K : Type} [Field K] [Finite K] [CharP K 2] {r : ℕ}

theorem leviAt_plusFlagStab (hr : 3 ≤ r) {D : Finset ℕ} (hD : ∀ d ∈ D, 1 ≤ d ∧ d ≤ r)
    (hr1 : r - 1 ∈ D → r ∈ D) {K₀ : Subgroup ↥(orthElementaryGroup (quadPlus r K))}
    (hK₀ : K₀.map (orthElementaryGroup (quadPlus r K)).subtype = plusFlagStab K r D) (p : ℕ) :
    LeviAt K₀ p := by
  intro hB hp h5 hrank hpar hne hsyl
  haveI := finite_plusAut (K := K) r
  have hpq2 : ¬ p ∣ Nat.card K ^ 2 - 1 := orthPlus_not_dvd_sq_sub_one_of_pRank_le_one hr hp hrank
  have hpK : ¬ p ∣ Nat.card K - 1 := fun h =>
    hpq2 (h.trans (Nat.sub_one_dvd_pow_sub_one (Nat.card K) 2))
  have hle : plusFlagStab K r D ≤ orthElementaryGroup (quadPlus r K) := inf_le_left
  let ρ : ↥(plusFlagStab K r D) →* ↥(orthElementaryGroup (quadPlus r K)) :=
    Subgroup.inclusion hle
  have hρinj : Function.Injective ρ := Subgroup.inclusion_injective hle
  have hρK : ρ.range ≤ K₀ := by
    rintro _ ⟨y, rfl⟩
    have hy : (y : (Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K)) ∈
        K₀.map (orthElementaryGroup (quadPlus r K)).subtype := by
      rw [hK₀]
      exact y.2
    obtain ⟨k, hk, hky⟩ := hy
    have hρy : ρ y = k := Subtype.ext hky.symm
    rw [hρy]
    exact hk
  have hpQ : p ∣ Nat.card ↥(plusFlagStab K r D) := by
    have h1 := dvd_card_of_sylow_hyp hp hsyl
    have e : ↥K₀ ≃* ↥(plusFlagStab K r D) :=
      (K₀.equivMapOfInjective _ (Subgroup.subtype_injective _)).trans
        (MulEquiv.subgroupCongr hK₀)
    rwa [Nat.card_congr e.toEquiv] at h1
  exact orthPlus_leviAt_of_leviData ρ hρK hρinj hp h5 hpQ
    (leviData_plusFlagStab hr hD hr1 hp h5 hpK) (two_le_pRank_three_plusElementary hr)

theorem leviAt_orthPlus (hr : 4 ≤ r) (K₀ : Subgroup ↥(orthElementaryGroup (quadPlus r K))) (p : ℕ)
    (hB : borel r K ≤ K₀.map (orthElementaryGroup (quadPlus r K)).subtype) : LeviAt K₀ p := by
  obtain ⟨e, D, hD, hr1, hKD⟩ := exists_plusFlagStab_of_borel_le hr hB
  exact LeviAt.of_map e (leviAt_plusFlagStab (by omega) hD hr1 hKD p)

theorem leviSubAt_orthPlus (hr : 4 ≤ r) :
    LeviSubAt ↥(orthElementaryGroup (quadPlus r K)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨⟨T₀, hT₀⟩, hN, -⟩ :=
    orthogonal_geometry_split_Sylow_flag_normalizer (K := K) 2 (by omega : 3 ≤ r)
  refine leviSubAt_of_standard_sylow T₀ fun K₀ p hNK => leviAt_orthPlus hr K₀ p ?_
  rw [hT₀, hN] at hNK
  intro b hb
  have hbE : b ∈ orthElementaryGroup (quadPlus r K) := borel_le hb
  have h1 : (⟨b, hbE⟩ : ↥(orthElementaryGroup (quadPlus r K))) ∈
      (flagStab r K).subgroupOf (orthElementaryGroup (quadPlus r K)) := by
    rw [Subgroup.mem_subgroupOf, native_partialBorel_eq_fullBorel r K (by omega)]
    exact hb
  exact ⟨_, hNK h1, rfl⟩

theorem leviSubAt_of_pomegaPlus {S : Type} [Group S] [Finite S] {n f : ℕ}
    (h : StatedClassicalModel S .POmegaPlus n 2 f) : LeviSubAt S := by
  obtain ⟨hadm, K, hKf, hKfin, hcard, ⟨e⟩⟩ := h
  have hn4 : 4 ≤ n := by
    obtain ⟨-, -, h4⟩ := hadm
    exact h4
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI := Fintype.ofFinite K
  haveI : CharP K 2 := charP_of_card_eq_prime_pow (f := f)
    (by rw [← Nat.card_eq_fintype_card]; exact hcard)
  exact LeviSubAt.of_mulEquiv (e.trans (statedProjOmegaPlusEquiv (by omega)))
    (leviSubAt_orthPlus hn4)

end KPLeviSub

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty
