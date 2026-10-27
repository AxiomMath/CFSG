module

public import CFSG.LocalAnalysis.RankThreeUC.Assembly
public import CFSG.LocalAnalysis.RankThreeUC.WitnessGen
import CFSG.LocalAnalysis.RankThreeUC.ModuleRank
import CFSG.GroupTheory.Gorenstein.MaxOrderThompson

public section

namespace CFSG.LocalAnalysis.RankThreeUC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup
open CFSG.LocalAnalysis.AGL81TheoremCD (StandingGen)

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem thompsonSubgroup_le' (S : Subgroup G) : Open.thompsonSubgroup S ≤ S :=
  CFSG.ambientMaxCardThompson_le S

omit [Finite G] in
theorem normalizer_le_normalizer_thompsonSubgroup [Finite G] (S : Subgroup G) :
    normalizer (S : Set G) ≤ normalizer (Open.thompsonSubgroup S : Set G) :=
  CFSG.Open.normalizer_le_normalizer_thompsonSubgroup S

theorem exists_isMulCommutative_card_max (T : Subgroup G) :
    ∃ A : Subgroup G, A ≤ T ∧ IsMulCommutative A ∧
      ∀ B : Subgroup G, B ≤ T → IsMulCommutative B → Nat.card B ≤ Nat.card A := by
  obtain ⟨A, ⟨hAT, hA⟩, hmax⟩ := Set.exists_max_image {A : Subgroup G | A ≤ T ∧ IsMulCommutative A}
    (fun A => Nat.card A) (Set.toFinite _)
    ⟨⊥, bot_le, ⟨⟨fun _ _ => Subsingleton.elim _ _⟩⟩⟩
  exact ⟨A, hAT, hA, fun B hBT hB => hmax B ⟨hBT, hB⟩⟩

omit [Finite G] in
theorem le_thompsonSubgroup {A T : Subgroup G} (hAT : A ≤ T) (hA : IsMulCommutative A)
    (hmax : ∀ B : Subgroup G, B ≤ T → IsMulCommutative B → Nat.card B ≤ Nat.card A) :
    A ≤ Open.thompsonSubgroup T :=
  CFSG.le_ambientMaxCardThompson ⟨hAT, hA, hmax⟩

theorem thompsonSubgroup_eq_of_le {S T : Subgroup G} (hST : S ≤ T)
    (hJ : Open.thompsonSubgroup T ≤ S) : Open.thompsonSubgroup S = Open.thompsonSubgroup T := by
  obtain ⟨A₀, hA₀T, hA₀c, hA₀max⟩ := exists_isMulCommutative_card_max T
  have hA₀J := le_thompsonSubgroup hA₀T hA₀c hA₀max
  apply le_antisymm
  · rw [CFSG.Open.thompsonSubgroup_eq_iSup S]
    refine iSup_le fun A => iSup_le fun hAS => iSup_le fun hA => iSup_le fun hmax => ?_
    exact le_thompsonSubgroup (hAS.trans hST) hA fun B hBT hB =>
      (hA₀max B hBT hB).trans (hmax A₀ (hA₀J.trans hJ) hA₀c)
  · rw [CFSG.Open.thompsonSubgroup_eq_iSup T]
    refine iSup_le fun A => iSup_le fun hAT => iSup_le fun hA => iSup_le fun hmax => ?_
    exact le_thompsonSubgroup ((le_thompsonSubgroup hAT hA hmax).trans hJ) hA fun B hBS hB =>
      hmax B (hBS.trans hST) hB

theorem thompsonSubgroup_ne_bot {T : Subgroup G} (hT : T ≠ ⊥) : Open.thompsonSubgroup T ≠ ⊥ :=
  CFSG.Open.thompsonSubgroup_ne_bot_of_finite hT

theorem IsWitnessGen.normalizer_le_of_normalizer_le {p : ℕ} {P : Sylow p G} {M : Subgroup G}
    (hw : IsWitnessGen p P M) {T C : Subgroup G} (hT : IsPGroup 2 T) (hCT : C ≤ T)
    (hC1 : C ≠ ⊥) (hN : normalizer (T : Set G) ≤ normalizer (C : Set G))
    (h2 : 2 ≤ CFSG.Open.pRank p (M ⊓ normalizer (C : Set G))) : normalizer (T : Set G) ≤ M :=
  hN.trans (hw.u2 _ ⟨C, hC1, hT.to_le hCT, rfl⟩ (by rwa [inf_comm]))

omit [Finite G] in
theorem normalizer_le_normalizer_omegaOneCenterIn (T : Subgroup G) :
    normalizer (T : Set G) ≤
      normalizer (CFSG.RankThree.PartOne.omegaOneCenterIn T : Set G) := by
  have key : ∀ g ∈ normalizer (T : Set G), ∀ z ∈ CFSG.RankThree.PartOne.omegaOneCenterIn T,
      g * z * g⁻¹ ∈ CFSG.RankThree.PartOne.omegaOneCenterIn T := by
    intro g hg z hz
    obtain ⟨hzT, hzc, hz2⟩ := CFSG.RankThree.PartOne.Sec15Final.mem_omegaOneCenterIn_iff.mp hz
    refine CFSG.RankThree.PartOne.Sec15Final.mem_omegaOneCenterIn_iff.mpr
      ⟨(mem_normalizer_iff.mp hg z).mp hzT, fun k hk => ?_, ?_⟩
    · have hk' : g⁻¹ * k * g ∈ T := by
        have := (mem_normalizer_iff.mp (inv_mem hg) k).mp hk
        simpa using this
      have h := hzc _ hk'
      calc k * (g * z * g⁻¹) = g * ((g⁻¹ * k * g) * z) * g⁻¹ := by group
        _ = g * (z * (g⁻¹ * k * g)) * g⁻¹ := by rw [h]
        _ = g * z * g⁻¹ * k := by group
    · calc (g * z * g⁻¹) ^ 2 = g * z ^ 2 * g⁻¹ := by rw [sq, sq]; group
        _ = 1 := by rw [hz2]; group
  intro g hg
  rw [mem_normalizer_iff]
  intro z
  refine ⟨key g hg z, fun h => ?_⟩
  have := key g⁻¹ (inv_mem hg) _ h
  simpa [mul_assoc] using this

theorem IsWitnessGen.normalizer_sylow_two_le_of_thompson (hS : StandingGen G) {p : ℕ}
    {P : Sylow p G} (hp : IsWitnessPrime p P) {M : Subgroup G} (hw : IsWitnessGen p P M)
    {T U : Subgroup G} (hT : CFSG.ABGLocalTools.IsSylowOf 2 T M)
    (hMU : M ≤ normalizer (U : Set G))
    (hZU : CFSG.RankThree.PartOne.omegaOneCenterIn T ≤ U)
    (hJ : Open.thompsonSubgroup T ≤ centralizer (U : Set G)) : normalizer (T : Set G) ≤ M := by
  have hprime := hp.prime
  have hT1 : T ≠ ⊥ := ne_bot_of_isSylowOf_two hw.maxLocal.1 hT
  have hT2 : IsPGroup 2 T := hT.isPGroup
  rcases hw.two_le_pRank_normalizer_or_centralizer hS hp hMU hT with h | h
  ·
    have hJS : Open.thompsonSubgroup T ≤ T ⊓ centralizer (U : Set G) :=
      le_inf (thompsonSubgroup_le' T) hJ
    have hJeq := thompsonSubgroup_eq_of_le (inf_le_left : T ⊓ centralizer (U : Set G) ≤ T) hJS
    have hNS : normalizer ((T ⊓ centralizer (U : Set G) : Subgroup G) : Set G) ≤
        normalizer (Open.thompsonSubgroup T : Set G) :=
      hJeq ▸ normalizer_le_normalizer_thompsonSubgroup _
    have h2 : 2 ≤ CFSG.Open.pRank p (M ⊓ normalizer (Open.thompsonSubgroup T : Set G)) :=
      h.trans (pRank_mono p hprime.one_lt (inf_le_inf_left M hNS))
    exact hw.normalizer_le_of_normalizer_le hT2 (thompsonSubgroup_le' T)
      (thompsonSubgroup_ne_bot hT1) (normalizer_le_normalizer_thompsonSubgroup T) h2
  ·
    have hCN : centralizer (U : Set G) ≤
        normalizer (CFSG.RankThree.PartOne.omegaOneCenterIn T : Set G) := by
      intro g hg
      rw [mem_normalizer_iff]
      intro z
      have hcomm : ∀ z ∈ CFSG.RankThree.PartOne.omegaOneCenterIn T, g * z * g⁻¹ = z := by
        intro z hz
        rw [← mem_centralizer_iff.mp hg z (hZU hz), mul_inv_cancel_right]
      constructor
      · intro hz
        rwa [hcomm z hz]
      · intro hz
        have h1 := hcomm _ hz
        have h2 : z = g * z * g⁻¹ := by
          calc z = g⁻¹ * (g * z * g⁻¹) * g := by group
            _ = g⁻¹ * (g * (g * z * g⁻¹) * g⁻¹) * g := by rw [h1]
            _ = g * z * g⁻¹ := by group
        rwa [h2]
    have h2 : 2 ≤ CFSG.Open.pRank p
        (M ⊓ normalizer (CFSG.RankThree.PartOne.omegaOneCenterIn T : Set G)) :=
      h.trans (pRank_mono p hprime.one_lt (inf_le_inf_left M hCN))
    exact hw.normalizer_le_of_normalizer_le hT2
      (CFSG.RankThree.PartOne.Sec15Final.omegaOneCenterIn_le T)
      (CFSG.RankThree.PartOne.Sec15Final.omegaOneCenterIn_ne_bot hT2 hT1)
      (normalizer_le_normalizer_omegaOneCenterIn T) h2

@[expose] def AGL81TheoremDGen (G : Type) [Group G] [Finite G]
    (W : ∀ p : ℕ, Sylow p G → Subgroup G → Prop) : Prop :=
  ∀ (p : ℕ) (P : Sylow p G) (M : Subgroup G), W p P M →
    ∀ T : Subgroup G, CFSG.ABGLocalTools.IsSylowOf 2 T M → normalizer (T : Set G) ≤ M

theorem agl81TheoremD_iff_gen :
    AGL81TheoremD G ↔ (rankThreeUC G → AGL81TheoremDGen G (witnessThree G)) := by
  constructor
  · intro hD hUC p P M hw T hT
    exact hD hUC p hw.1 P M hw.2 T hT
  · intro h hUC p hp P M hw T hT
    exact h hUC p P M ⟨hp, hw⟩ T hT

end CFSG.LocalAnalysis.RankThreeUC
