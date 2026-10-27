module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4KSwNormC2
public import Certificates.Kernel.ThCent.Leaves
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4KSwNormB10

public section

namespace CFSG.ComponentClassification.GrSLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ComponentClassification.UnbalancedGS

@[expose] def L34Lemma43TwistedInnerStep : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (a x : G) (J S A : Subgroup G), L34Sec4Setting G a x J S →
    (∀ s ∈ S, s * a = a * s) → L34Sec4Running J A → IsThreeConnected (S ⊓ withKernel J) →
    S ⊓ zStarIn J = ⊥ →
    ∀ W : Subgroup G, W ≠ ⊥ → Odd (Nat.card W) →
      (∀ B : Subgroup G, B ≤ S ⊓ withKernel J → IsAbelianTwoOfRank 3 B → wGroup B = W) →
      normalizer (J : Set G) ≤ normalizer (W : Set G) →
      ∀ K : Subgroup G, K ≤ normalizer (W : Set G) →
        IsPComponent 2 (K.subgroupOf (normalizer (W : Set G))) →
        IsL34Type (K ⧸ Open.fusionZStar K) →
        J ⊔ oddIn (normalizer (W : Set G)) = K ⊔ oddIn (normalizer (W : Set G)) →
        ¬ oddIn K ≤ J →
        ∀ T : Subgroup G, IsSylowTwoIn T (normalizer (W : Set G)) → S ≤ T →
          (∃ P : Sylow 2 G, (P : Subgroup G) = T) →
          ∀ t ∈ T, t ∉ normalizer (K : Set G) →
          (∀ m ∈ normalizer (W : Set G), conjugate K m = K ∨ conjugate K m = conjugate K t) →
          (∀ y ∈ T, y ∈ coreActionKernel K → y ∈ coreActionKernel (conjugate K t) → y = 1) →
          (∀ y ∈ normalizer (W : Set G), orderOf y = 2 → y ∈ normalizer (K : Set G)) →
          (∃ u ∈ T, u ∉ normalizer (K : Set G) ∧ u ^ 4 = 1) →
          (∀ u ∈ T, u ∉ normalizer (K : Set G) → u ^ 4 = 1 →
            ¬ ∃ F ≤ T ⊓ centralizer ({u} : Set G), IsEightGroup F ∧
              ∃ w ∈ T ⊓ centralizer ({u} : Set G), w * w = 1 ∧ (∀ e ∈ F, w * e = e * w) ∧
                w ∉ F) →
          a ∈ conjugate K t →
          ¬ oddIn J ≤ centralizer (J : Set G) →
          (∀ y ∈ K ⊔ conjugate K t ⊔ oddIn (normalizer (W : Set G)),
            y * y = 1 → y ≠ 1 → ∃ g ∈ normalizer (W : Set G), g⁻¹ * y * g = a ∨
              (g⁻¹ * y * g)⁻¹ * a * (t⁻¹ * a * t) ∈ oddIn (normalizer (W : Set G))) →
          (∀ w ∈ T ⊓ normalizer (K : Set G), w * w ∈ K ⊔ conjugate K t) →
          (∀ v ∈ T, v ∉ normalizer (K : Set G) → v * v ∉ withKernel K) →
          (∀ v ∈ T, v ∉ normalizer (K : Set G) →
            (∀ y ∈ T, y ∉ normalizer (K : Set G) → orderOf v ≤ orderOf y) →
            ∃ g : G, g⁻¹ * v * g ∈ T ⊓ normalizer (K : Set G)) →
          (∀ v ∈ T, v ∉ normalizer (K : Set G) →
            (∀ y ∈ T, y ∉ normalizer (K : Set G) → orderOf v ≤ orderOf y) →
            ¬ ∃ F ≤ T ⊓ centralizer ({v * v} : Set G), IsEightGroup F ∧
              ∃ w ∈ T ⊓ centralizer ({v * v} : Set G), w * w = 1 ∧
                (∀ e ∈ F, w * e = e * w) ∧ w ∉ F) →
          False

theorem l34Lemma43TwistedUnitaryStep_of_inner
    (hMax : MaximalTwoComponentInput) (h : L34Lemma43TwistedInnerStep) :
    L34Lemma43TwistedUnitaryStep := by
  intro G _ _ a x J S A hset hcent hrun h3 hZ1 W hW hWodd hWB hNJ K hKM hKc hKL hsup hOK T hTsyl
    hST hTG t htT htK hr2 hQ hinv hu hno hE1 hE2 hE3 hE4 hE5 hE6 hE7
  rcases hE1 with haKt | hout
  · exact h G a x J S A hset hcent hrun h3 hZ1 W hW hWodd hWB hNJ K hKM hKc hKL hsup hOK T hTsyl
      hST hTG t htT htK hr2 hQ hinv hu hno haKt (hE2 haKt) (hE3 haKt) hE4 hE5 hE6 (hE7 haKt)
  obtain ⟨hbase, hU3, hL34, hmax, hSsyl, haS, -⟩ := id hset
  obtain ⟨hsimple, hnab, hK, -, hUo, -, -, -⟩ := id hbase
  have : IsSimpleGroup G := hsimple
  have ha2 : orderOf a = 2 := hU3.1
  have hJa : J ≤ centralizer ({a} : Set G) := hU3.2.2.2.1
  have hJc := hU3.2.2.2.2.1
  have hgs : GSMaximalSetting G a J := ⟨hsimple, hnab, hK, hUo, ha2, hJa, hJc, hmax,
    GrS5.three_le_pRank_of_l34 hL34, Sol78.not_psp4_of_l34 hL34, Or.inl ⟨hL34, hset.1⟩⟩
  have hs : SingleComponentSetting G a J W K :=
    { toGSMaximalSetting := hgs, ne_bot := hW, odd_card := hWodd, normalizer_le := hNJ,
      normalizer_ne_top := GrS4.normalizer_ne_top_of_odd hW hWodd ha2, le_normalizer := hKM,
      isPComponent_K := hKc, sup_eq := hsup }
  have hT2 := GrS4.isPGroup_of_isSylowTwoIn hTsyl
  have hTM := hTsyl.1
  have haT : a ∈ T := hST haS
  have hKZ := KSw.zStarIn_eq_oddIn_of_zOne hs hSsyl hZ1
  have hTZ : T ⊓ zStarIn K = ⊥ := KSw.inf_zStarIn_eq_bot_of_zOne hs hSsyl hZ1 hT2
  have haK : a ∈ coreActionKernel K := GrS4.mem_coreActionKernel_of_singleComponentSetting hMax hs
  have hH1 : ∀ e ∈ T, ∀ e' ∈ T, conjugate K e = K ∨ conjugate K e' = K ∨
      conjugate K e = conjugate K e' := by
    intro e he e' he'
    rcases hr2 e (hTM he) with h1 | h1
    · exact Or.inl h1
    · rcases hr2 e' (hTM he') with h2 | h2
      · exact Or.inr (Or.inl h2)
      · exact Or.inr (Or.inr (h1.trans h2.symm))
  have hWT := GrS5S.l34TSylowWStep_of_certs hMax G a x J S A hset hcent
    (fun h => (h hZ1).elim) hrun h3 W hW hWodd hWB hNJ K hKM hKc hKL (Or.inl hsup) T hTsyl hST
    hH1 (Or.inl hTZ)
  obtain ⟨F, hFP, hF, s, hsS, hss, hsF, hsn⟩ := GrS5S.exists_eight_not_isolated hset h3
  have hFa : F ≤ T ⊓ centralizer ({a} : Set G) := fun e he =>
    mem_inf.mpr ⟨hST (mem_inf.mp (hFP he)).1,
      mem_centralizer_singleton_iff.mpr (hcent e (mem_inf.mp (hFP he)).1)⟩
  have hsa : s ∈ T ⊓ centralizer ({a} : Set G) :=
    mem_inf.mpr ⟨hST (mem_inf.mp hsS).1, mem_centralizer_singleton_iff.mpr
      (hcent s (mem_inf.mp hsS).1)⟩
  exact KSw.false_of_outer_conj hnab hKL hKZ hTsyl hTG hWT htT htK hr2 hinv haT ha2 haK hout hFa
    hF hsa hss hsF hsn

end CFSG.ComponentClassification.GrSLit
