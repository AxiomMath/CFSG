module

public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVL34FFComp
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.QuasithinUnique.GammaFamiliesBasic

public section

namespace CFSG.AGLEmbeddingD2.Tits.MsidePrelim

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers CFSG.AGLEmbedding
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M H R : Subgroup G}
  {Rbar : Sylow 3 (H ⧸ primeComplementCore (G := H) 3)}
  {K : Subgroup (H ⧸ primeComplementCore (G := H) 3)}

structure L34Ctx (M H R : Subgroup G) (Rbar : Sylow 3 (H ⧸ primeComplementCore (G := H) 3))
    (K : Subgroup (H ⧸ primeComplementCore (G := H) 3)) : Prop where
  normal : K.Normal
  simple : IsSimpleGroup K
  nonab : ∃ a b : K, a * b ≠ b * a
  center : Subgroup.center K = ⊥
  sylow : ∃ T₁ : Sylow 3 K, (T₁ : Subgroup K).map K.subtype =
    (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) 3)) ⊓ K
  rbar : (Rbar : Subgroup _) = (R.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore 3))
  inf_ne_bot : (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) 3)) ⊓ K ≠ ⊥
  mapX : ((d1LiftX 3 H R K).subgroupOf H).map
    (QuotientGroup.mk' (primeComplementCore (G := H) 3)) =
      (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) 3)) ⊓ K
  isPGroup : IsPGroup 3 R
  le_inf : R ≤ H ⊓ M
  primeCore_le : GLBPrimeCore 3 H ≤ M
  twoCore_le : pCoreOf 2 H ≤ M
  ne_top : H ≠ ⊤
  twoLocal : IsTwoLocal H
  kProper : Open.IsKProper G
  charTwo : IsCharTwoType G
  centralizer_eq_bot : Subgroup.centralizer (K : Set (H ⧸ primeComplementCore (G := H) 3)) = ⊥

omit [Finite G] in
theorem L34Ctx.isSimpleGroup (hd : L34Ctx M H R Rbar K) :
    IsSimpleGroup K ∧ ∃ a b : K, a * b ≠ b * a := ⟨hd.simple, hd.nonab⟩

omit [Finite G] in
theorem L34Ctx.toCore (hd : L34Ctx M H R Rbar K) : L34FF.Core H R Rbar K :=
  ⟨hd.normal, hd.isSimpleGroup, hd.mapX, hd.inf_ne_bot, hd.isPGroup⟩

theorem L34Ctx.map_threeComp (hd : L34Ctx M H R Rbar K) :
    ((L34FF.threeComp H R K).subgroupOf H).map
      (QuotientGroup.mk' (primeComplementCore (G := H) 3)) = K :=
  hd.toCore.map_threeComp

theorem L34Ctx.threeComp_dichotomy (hd : L34Ctx M H R Rbar K)
    {N : Subgroup G} (hNL : N ≤ L34FF.threeComp H R K)
    (hLN : L34FF.threeComp H R K ≤ Subgroup.normalizer (N : Set G)) :
    N ≤ L34FF.threeCompCore H R K ∨ L34FF.threeComp H R K ≤ N :=
  hd.toCore.threeComp_dichotomy hNL hLN

theorem L34Ctx.not_threeComp_le_threeCompCore (hd : L34Ctx M H R Rbar K) :
    ¬ L34FF.threeComp H R K ≤ L34FF.threeCompCore H R K :=
  hd.toCore.not_threeComp_le_threeCompCore

theorem L34Ctx.glbPrimeCore_le_inf (hd : L34Ctx M H R Rbar K) :
    GLBPrimeCore 3 H ≤ GLBPrimeCore 3 (H ⊓ M) :=
  le_glbPrimeCore (_root_.le_inf (glbPrimeCore_le 3 H) hd.primeCore_le)
    (inf_le_left.trans (le_normalizer_glbPrimeCore 3 H)) (glbPrimeCore_coprime 3 H)

theorem L34Ctx.twoCore_le_of_isSylowTwoOf (hd : L34Ctx M H R Rbar K)
    {D₀ V : Subgroup G} (hD₀H : D₀ ≤ H) (hOD : GLBPrimeCore 3 H ≤ D₀)
    (hV : IsSylowTwoOf V D₀) : pCoreOf 2 H ≤ V := by
  have hS2 := RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 H
  have hHS := CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H
  have hcop : Nat.Coprime 3 (Nat.card (pCoreOf 2 H)) := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hS2
    rw [hn]
    exact Nat.Coprime.pow_right n (by norm_num)
  have hSD : pCoreOf 2 H ≤ D₀ :=
    (le_glbPrimeCore (RankThreeCoreUniqueness.Helpers.pCoreOf_le 2 H) hHS hcop).trans hOD
  exact hV.le_of_normalizes hSD (hD₀H.trans hHS) hS2

theorem L34Ctx.omegaOneCenterOf_le_twoCore (hd : L34Ctx M H R Rbar K)
    {D₀ V : Subgroup G} (hD₀H : D₀ ≤ H) (hOD : GLBPrimeCore 3 H ≤ D₀)
    (hV : IsSylowTwoOf V D₀) :
    omegaOneCenterOf V ≤ omegaOneCenterOf (pCoreOf 2 H) := by
  have hSV := hd.twoCore_le_of_isSylowTwoOf hD₀H hOD hV
  have hVH : V ≤ H := hV.1.trans hD₀H
  refine (Subgroup.closure_le _).mpr ?_
  rintro x ⟨⟨hxV, hxC⟩, hx2⟩
  have hxCS : x ∈ Subgroup.centralizer (pCoreOf 2 H : Set G) := Subgroup.centralizer_le hSV hxC
  have hxS : x ∈ pCoreOf 2 H :=
    hd.charTwo H hd.twoLocal ⟨hVH hxV, hxCS⟩
  exact Subgroup.subset_closure ⟨⟨hxS, hxCS⟩, hx2⟩

end CFSG.AGLEmbeddingD2.Tits.MsidePrelim
