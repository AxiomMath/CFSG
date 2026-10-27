module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.LayerPermutable
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.LayerSylowMax
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.LayerSylowAbstract

public section

namespace CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape

open CFSG.Open CFSG.AGLEmbedding CFSG.AGLEmbeddingD2 CFSG.QuasithinUnique
open CFSG.RankThreeCoreUniqueness.Helpers
open scoped Pointwise

@[expose] def InvariantSylowStmt : Prop :=
  ∀ (M : Type) [Group M] [Finite M] (A S X : Subgroup M), IsPGroup 3 A → ¬ 3 ∣ Nat.card S →
    A ≤ Subgroup.normalizer (S : Set M) → X ≤ S → IsPGroup 2 X →
    A ≤ Subgroup.normalizer (X : Set M) →
    ∃ P : Subgroup M, P ≤ S ∧ IsPGroup 2 P ∧ ¬ 2 ∣ (P.subgroupOf S).index ∧ X ≤ P ∧
      A ≤ Subgroup.normalizer (P : Set M)

@[expose] def D2L34BetaInvariantTwoInCore : Prop :=
  ∀ (d : TauCeti.ValidLieTypeIndex) (G : Type) [Group G] [Finite G] (P : Sylow 3 G)
    (M A H R : Subgroup G) (Rbar : Sylow 3 (H ⧸ primeComplementCore (G := H) 3))
    (K : Subgroup (H ⧸ primeComplementCore (G := H) 3)), D2L34BetaConf d P M A H R Rbar K →
    GLBStronglyEmbedded 3 M → D2L34AllResidue P M → D2L34Kmax H →
    ∀ X : Subgroup G, X ≤ H ⊓ M → IsPGroup 2 X → A ≤ Subgroup.normalizer (X : Set G) →
      X ≤ GLBPrimeCore 3 (H ⊓ M)

theorem isSylowTwoOf_starImg_inf_of_escape (hS : InvariantSylowStmt) {G : Type} [Group G]
    [Finite G] {P : Sylow 3 G} {M A H R : Subgroup G} (hesc : D2Escape 3 P M A H R)
    (hinv : ∀ X : Subgroup G, X ≤ H ⊓ M → IsPGroup 2 X → A ≤ Subgroup.normalizer (X : Set G) →
      X ≤ GLBPrimeCore 3 (H ⊓ M))
    {U : Subgroup G} (hU : IsBetaBase H M U) (hAU : A ≤ Subgroup.normalizer (U : Set G))
    (hNHU : Subgroup.normalizer (U : Set G) ≤ H) (hUQ : IsSylowTwoOf U (GLBPrimeCore 3 (H ⊓ M)))
    {L : Subgroup G} (hlay : IsRankTwoLayer M L)
    (hcent : ∀ a ∈ A, ∀ l ∈ L, a * l * a⁻¹ * l⁻¹ ∈ GLBPrimeCore 3 M) :
    IsSylowTwoOf (starImg M U ⊓ starImg M L) (starImg M L) := by
  have hLn : (L.subgroupOf M).Normal := hlay.2.2.1
  have hUM : U ≤ M := (hUQ.1.trans (glbPrimeCore_le 3 _)).trans inf_le_right
  have hAM : A ≤ M := hesc.A_le.trans hesc.le_M
  have hA3 : IsPGroup 3 A := IsPGroup.of_card (n := 2) (by rw [hesc.card_A])
  have hU2 : IsPGroup 2 U := hU.1
  have hmaxG : ∀ S : Subgroup G, S ≤ M → IsPGroup 2 S → U ≤ S →
      A ≤ Subgroup.normalizer (S : Set G) → S ≤ U := fun S hSM hS2 hUS hAS =>
    le_of_maximal M H A U (GLBPrimeCore 3 (H ⊓ M)) hUQ.1 hU2 hUQ.2.2 hAU hNHU
      hinv S hSM hS2 hUS hAS
  set Dm : Subgroup ↥M := (GLBPrimeCore 3 M).subgroupOf M with hDm
  set Lm : Subgroup ↥M := L.subgroupOf M with hLm
  set Um : Subgroup ↥M := U.subgroupOf M with hUm
  set Am : Subgroup ↥M := A.subgroupOf M with hAm
  have : Lm.Normal := hLn
  have hDM : GLBPrimeCore 3 M ≤ M := glbPrimeCore_le 3 M
  have hD3 : ¬ 3 ∣ Nat.card Dm := by
    rw [hDm, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDM).toEquiv]
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp (glbPrimeCore_coprime 3 M)
  have hUm2 : IsPGroup 2 Um := hU2.of_equiv (Subgroup.subgroupOfEquivOfLe hUM).symm
  have hAm3 : IsPGroup 3 Am := hA3.of_equiv (Subgroup.subgroupOfEquivOfLe hAM).symm
  have hAUm : Am ≤ Subgroup.normalizer (Um : Set ↥M) := by
    intro a ha
    rw [Subgroup.mem_normalizer_iff]
    intro g
    have := Subgroup.mem_normalizer_iff.mp (hAU (show (a : G) ∈ A from ha)) (g : G)
    exact this
  have hAcM : ∀ a ∈ Am, ∀ l ∈ Lm, a * l * a⁻¹ * l⁻¹ ∈ Dm := fun a ha l hl =>
    hcent (a : G) ha (l : G) hl
  have hmaxM : ∀ S : Subgroup ↥M, IsPGroup 2 S → Um ≤ S →
      Am ≤ Subgroup.normalizer (S : Set ↥M) → S ≤ Um := by
    intro S hS2 hUS hAS
    set SG : Subgroup G := S.map M.subtype with hSG
    have hSGM : SG ≤ M := by rintro _ ⟨x, -, rfl⟩; exact x.2
    have hSG2 : IsPGroup 2 SG := hS2.map _
    have hUSG : U ≤ SG := fun u hu =>
      ⟨⟨u, hUM hu⟩, hUS (show (⟨u, hUM hu⟩ : ↥M) ∈ U.subgroupOf M from hu), rfl⟩
    have hASG : A ≤ Subgroup.normalizer (SG : Set G) := by
      intro a ha
      rw [Subgroup.mem_normalizer_iff]
      intro g
      have haM : a ∈ M := hAM ha
      have hAa := Subgroup.mem_normalizer_iff.mp
        (hAS (show (⟨a, haM⟩ : ↥M) ∈ A.subgroupOf M from ha))
      constructor
      · rintro ⟨s, hs, rfl⟩
        exact ⟨_, (hAa s).mp hs, rfl⟩
      · rintro ⟨s', hs', hs'g⟩
        have hs'g' : (s' : G) = a * g * a⁻¹ := hs'g
        have hgM : g ∈ M := by
          have : g = a⁻¹ * (s' : G) * a := by rw [hs'g']; group
          rw [this]
          exact M.mul_mem (M.mul_mem (M.inv_mem haM) s'.2) haM
        have h1 : (⟨g, hgM⟩ : ↥M) ∈ S := by
          refine (hAa ⟨g, hgM⟩).mpr ?_
          have : (⟨a, haM⟩ : ↥M) * ⟨g, hgM⟩ * (⟨a, haM⟩ : ↥M)⁻¹ = s' := Subtype.ext hs'g'.symm
          rw [this]; exact hs'
        exact ⟨_, h1, rfl⟩
    have hle := hmaxG SG hSGM hSG2 hUSG hASG
    intro s hs
    exact hle ⟨s, hs, rfl⟩
  have hres := sylow_mod_of_maximal Dm Lm Um Am hD3 hUm2 hAUm hAcM hmaxM
    (fun S X h3 hAS hXS hX2 hAX => hS ↥M Am S X hAm3 h3 hAS hXS hX2 hAX)
  refine ⟨inf_le_right, ?_, hres⟩
  exact ((hUm2.map (QuotientGroup.mk' Dm))).to_le inf_le_left

theorem d2L34BetaLayerSylow_of (hinvH : D2L34BetaInvariantTwoInCore)
    (hCent : D2L34BetaLayerCentralized) (hS : InvariantSylowStmt) : D2L34BetaLayerSylow := by
  intro d G _ _ P M A H R Rbar K hc hstr hAll hKmax hcon U hU hAU hNHU hsylU hUQ L hlay
  exact isSylowTwoOf_starImg_inf_of_escape hS hc.esc
    (hinvH d G P M A H R Rbar K hc hstr hAll hKmax) hU hAU hNHU hUQ hlay (hCent d G P M A H R Rbar K hc hstr hAll hKmax hcon L hlay)

end CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape
