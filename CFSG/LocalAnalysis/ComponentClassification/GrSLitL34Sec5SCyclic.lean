module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5SFixed
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5Inputs217

public section

namespace CFSG.ComponentClassification.GrSLit.L34Sec5S

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedGS
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)

@[expose] def L34CyclicPumpUpExclusion : Prop :=
  ∀ (G : Type) [Group G] [Finite G], L34BaseSetting G →
    ∀ (a b : G) (M T : Subgroup G), orderOf a = 2 → orderOf b = 2 → a * b = b * a →
      M ≤ centralizer ({b} : Set G) →
      IsPComponent 2 (M.subgroupOf (centralizer ({b} : Set G))) →
      conjugate M a = M → T ≤ M ⊓ centralizer ({a} : Set G) →
      IsPComponent 2 (T.subgroupOf (M ⊓ centralizer ({a} : Set G))) →
      (pPrimeCore 2 T).index < (pPrimeCore 2 M).index →
      IsL34Type (T ⧸ Open.fusionZStar T) → pRank 2 ↥(Open.fusionZStar ↥T) ≤ 1 → False

@[expose] def L34CyclicProperFixedCatalog : Prop :=
  ∀ (Q : Type) [Group Q] [Finite Q], IsQuasisimple Q → IsPGroup 2 (center Q) →
    Blueprint.Catalog (Q ⧸ center Q) → ∀ σ : MulAut Q, (∀ y, σ (σ y) = y) →
    ∀ P : Subgroup Q, P ≤ fixedSubgroup σ → IsPComponent 2 (P.subgroupOf (fixedSubgroup σ)) →
      P ≠ ⊤ → IsL34Type (P ⧸ Open.fusionZStar P) → pRank 2 ↥(Open.fusionZStar ↥P) ≤ 1 →
      Blueprint.NativeSporadic.IsSporadic (Q ⧸ center Q) .Suz ∨
        Blueprint.NativeSporadic.IsSporadic (Q ⧸ center Q) .ONan ∨
        Blueprint.LieModel (Q ⧸ center Q) .PSL 3 2 4

@[expose] def L34SuzONanFieldPumpUpExclusion : Prop :=
  ∀ (G : Type) [Group G] [Finite G], L34BaseSetting G →
    ∀ (a b : G) (M T : Subgroup G), orderOf a = 2 → orderOf b = 2 → a * b = b * a →
      M ≤ centralizer ({b} : Set G) →
      IsPComponent 2 (M.subgroupOf (centralizer ({b} : Set G))) →
      conjugate M a = M → T ≤ M ⊓ centralizer ({a} : Set G) →
      IsPComponent 2 (T.subgroupOf (M ⊓ centralizer ({a} : Set G))) →
      (pPrimeCore 2 T).index < (pPrimeCore 2 M).index →
      IsL34Type (T ⧸ Open.fusionZStar T) → pRank 2 ↥(Open.fusionZStar ↥T) ≤ 1 →
      (Blueprint.NativeSporadic.IsSporadic
          ((M ⧸ pPrimeCore 2 M) ⧸ center (M ⧸ pPrimeCore 2 M)) .Suz ∨
        Blueprint.NativeSporadic.IsSporadic
          ((M ⧸ pPrimeCore 2 M) ⧸ center (M ⧸ pPrimeCore 2 M)) .ONan ∨
        Blueprint.LieModel ((M ⧸ pPrimeCore 2 M) ⧸ center (M ⧸ pPrimeCore 2 M)) .PSL 3 2 4) →
      False

theorem l34CyclicPumpUpExclusion_of_catalog (hcat : L34CyclicProperFixedCatalog)
    (hex : L34SuzONanFieldPumpUpExclusion) : L34CyclicPumpUpExclusion := by
  intro G _ _ hG a b M T ha hb hab hMb hMp hMa hTM hTp hlt htype hrank
  obtain ⟨hsimple, hna, hK, -, -, -, -, -⟩ := id hG
  have := hsimple
  have hbtop : centralizer ({b} : Set G) ≠ ⊤ := by
    intro htop
    have hZ := CatLeaf.center_eq_bot_of_simple hna
    have hbZ : b ∈ center G :=
      mem_center_iff.mpr fun g => mem_centralizer_singleton_iff.mp (htop ▸ mem_top g)
    rw [hZ, mem_bot] at hbZ
    rw [hbZ, orderOf_one] at hb
    omega
  obtain ⟨σ, P, hσ, hPF, hP, hPne, ⟨eZ⟩, ⟨eO⟩⟩ :=
    exists_quotient_fixed_component ha hMa hTM hTp hlt
  have hMq : IsQuasisimple (M ⧸ pPrimeCore 2 M) :=
    ((CatalogueBPrimeJoin.pComponent_subgroupOf_iff 2 M _ hMb).1 hMp).2.2
  obtain ⟨eS⟩ := nonempty_quotient_center_equiv_fusionZStar M
  have hcatQ : Blueprint.Catalog ((M ⧸ pPrimeCore 2 M) ⧸ center (M ⧸ pPrimeCore 2 M)) :=
    SectionRank.catalog_of_mulEquiv eS (catalog_fusionZStar_of_isPComponent hK hbtop hMb hMp)
  have hrankP : pRank 2 ↥(Open.fusionZStar ↥P) ≤ 1 := by
    rw [← pRank_fusionZStar_congr eO]
    exact hrank
  exact hex G hG a b M T ha hb hab hMb hMp hMa hTM hTp hlt htype hrank
    (hcat _ hMq (HeK.isPGroup_center_quotient M) hcatQ σ hσ P hPF hP hPne
      (LieType.CurtisTits.lieModel_of_mulEquiv eZ htype) hrankP)

theorem gsWeakMaximalComponent_of_cyclicExclusion (hS : SchreierFor Blueprint.Catalog)
    (hCT : L34ProperFixedCenterTrivial) (hPFS : L34ProperFixedSimpleRank)
    (hEx : L34CyclicPumpUpExclusion) {G : Type} [Group G] [Finite G] (hG : L34BaseSetting G)
    {b : G} {K : Subgroup G} (hb : orderOf b = 2) (hKb : K ≤ centralizer ({b} : Set G))
    (hKp : IsPComponent 2 (K.subgroupOf (centralizer ({b} : Set G))))
    (htype : IsL34Type (K ⧸ Open.fusionZStar K)) : GSWeakMaximalComponent K := by
  obtain ⟨hsimple, hna, hK, -, -, -, hHe, -⟩ := id hG
  have := hsimple
  have hZ := CatLeaf.center_eq_bot_of_simple hna
  refine ⟨⟨b, hb, hKb, hKp⟩, fun M hM => ?_⟩
  induction hM with
  | refl => exact ⟨MulEquiv.refl _⟩
  | @tail L' M' _ hst ih =>
    obtain ⟨a', b', hC⟩ := hst
    obtain ⟨e₁⟩ := ih
    have hb'Z : b' ∉ center G := by
      rw [hZ, mem_bot]
      intro h1
      have h2 := hC.2.1
      rw [h1, orderOf_one] at h2
      omega
    have htypeL : IsL34Type (L' ⧸ Open.fusionZStar L') :=
      LieType.CurtisTits.lieModel_of_mulEquiv e₁ htype
    rcases gsWeakCorr_type_dichotomy hS hK hC hb'Z with he | ⟨hMa, hTM, hTp, hlt, ⟨e⟩⟩
    · obtain ⟨e₂⟩ := he
      exact ⟨e₁.trans e₂⟩
    · exfalso
      have htypeT := LieType.CurtisTits.lieModel_of_mulEquiv e htypeL
      by_cases hr : pRank 2 ↥(Open.fusionZStar ↥(gsFixedLayer L' b')) ≤ 1
      · exact hEx G hG a' b' M' _ hC.1 hC.2.1 hC.2.2.1 hC.2.2.2.2.2.1 hC.2.2.2.2.2.2.1 hMa hTM hTp
          hlt htypeT hr
      · have hbtop : centralizer ({b'} : Set G) ≠ ⊤ := fun htop =>
          hb'Z (mem_center_iff.mpr fun g => mem_centralizer_singleton_iff.mp (htop ▸ mem_top g))
        exact false_of_proper_fixed_rank hCT hPFS hK hC.1 hbtop hC.2.2.2.2.2.1
          hC.2.2.2.2.2.2.1 ⟨fun eH => hHe ⟨b', M', hC.2.1, hC.2.2.2.2.2.1, hC.2.2.2.2.2.2.1, ⟨eH⟩⟩⟩
          hMa hTM hTp hlt htypeT (by omega)

theorem l34Cor217ComponentStep_of_cyclicExclusion (hS : SchreierFor Blueprint.Catalog)
    (hCT : L34ProperFixedCenterTrivial) (hPFS : L34ProperFixedSimpleRank)
    (hEx : L34CyclicPumpUpExclusion) : L34Cor217ComponentStep :=
  fun _ _ _ _ _ _ _ hset _ _ hu2 _ hK₁ hK₁p _ htype =>
    gsWeakMaximalComponent_of_cyclicExclusion hS hCT hPFS hEx hset.1 hu2 hK₁ hK₁p htype

end CFSG.ComponentClassification.GrSLit.L34Sec5S
