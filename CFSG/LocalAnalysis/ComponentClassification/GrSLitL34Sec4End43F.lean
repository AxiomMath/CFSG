module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4HeldDiag
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4InputsEnd43F
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4End43N2
public import CFSG.GH74.Generic.S45.LSporHe
public import CFSG.Sporadic.Schreier.J4SProfileNode
public import Certificates.Kernel.ThCent.Leaves

public section

namespace CFSG.ComponentClassification.GrSLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ComponentClassification.UnbalancedGS

theorem l34Lemma43HeldNormalStep_of_factor
    (hMax : MaximalTwoComponentInput) (h2A : L34Lemma43HeldFactor2AStep)
    (h2B : L34Lemma43HeldFactor2BStep) (hOut : L34Lemma43HeldFactorOuterStep) :
    L34Lemma43HeldNormalStep := by
  intro G _ _ a x J S A hset hcent hrun h3 W hW hWodd hWB hNJ K hKM hKc he hJK
  obtain ⟨e⟩ := he
  obtain ⟨hbase, hU3, hL34, hmax, -, -, -⟩ := id hset
  obtain ⟨hsimple, hnab, hK, -, hUo, -, hHe, -⟩ := hbase
  obtain ⟨ha2, -, -, hJa, hJc, -, -⟩ := hU3
  have hgs : GSMaximalSetting G a J := ⟨hsimple, hnab, hK, hUo, ha2, hJa, hJc,
    hmax, GrS5.three_le_pRank_of_l34 hL34, Sol78.not_psp4_of_l34 hL34, Or.inl ⟨hL34, hset.1⟩⟩
  set M : Subgroup G := normalizer (W : Set G) with hM
  have hCa : centralizer ({a} : Set G) ≤ M :=
    (GrS4.centralizer_le_normalizer_of_gsMaximalSetting hMax hgs).trans hNJ
  have haa : a * a = 1 := by rw [← pow_two, ← ha2, pow_orderOf_eq_one]
  have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_right haa
  have haM : a ∈ M := hCa (mem_centralizer_singleton_iff.mpr rfl)
  have hno : ∀ L : Subgroup G, L ≤ centralizer ({a} : Set G) →
      IsPComponent 2 (L.subgroupOf (centralizer ({a} : Set G))) →
      ¬ Nonempty (↥L ⧸ pPrimeCore 2 ↥L ≃* Blueprint.NativeSporadic.He) :=
    fun L h1 h2 h3 => hHe ⟨a, L, ha2, h1, h2, h3⟩
  intro m hm
  by_contra hmK
  have hK'ne : conjugate K m ≠ K := fun h => hmK (GrS4.mem_normalizer_of_conjugate_eq h)
  set KX : Subgroup ↥M := conjugate (K.subgroupOf M) ⟨m, hm⟩ with hKX
  have hKXmap : KX.map M.subtype = conjugate K m := by
    rw [hKX, GrS4.map_conjugate_subtype, GrS4.map_subgroupOf_subtype hKM]
  have hK'M : conjugate K m ≤ M := hKXmap ▸ map_subtype_le KX
  have hK'c : IsPComponent 2 ((conjugate K m).subgroupOf M) := by
    have h1 : (conjugate K m).subgroupOf M = KX := by
      rw [← hKXmap]
      exact comap_map_eq_self_of_injective M.subtype_injective KX
    rw [h1]
    exact LocalAnalysis.ComponentInitial.isPComponent_map_of_isPComponent 2
      (MulAut.conj (⟨m, hm⟩ : ↥M)⁻¹) hKc
  have e' : ↥(conjugate K m) ⧸ pPrimeCore 2 ↥(conjugate K m) ≃* Blueprint.NativeSporadic.He :=
    (Sol78.coreQuotCongr (K.equivMapOfInjective _ (MulAut.conj m⁻¹).injective)).symm.trans e
  by_cases haN : a ∈ normalizer (conjugate K m : Set G)
  · by_cases haC : a ∈ coreActionKernel (conjugate K m)
    ·
      obtain ⟨L, h1, h2, h3⟩ := GrS4.exists_held_of_mem_coreActionKernel haa hCa hK'c e' haC
      exact hno L h1 h2 h3
    ·
      set α := GrS4.heldQuotConj (conjugate K m) ⟨a, haN⟩ with hα
      have hα2 : α * α = 1 := by
        rw [hα, ← map_mul,
          show (⟨a, haN⟩ : ↥(normalizer (conjugate K m : Set G))) * ⟨a, haN⟩ = 1 from
            Subtype.ext haa, map_one]
      have hα1 : α ≠ 1 := by
        intro h1
        apply haC
        refine mem_coreActionKernel.mpr ⟨haN, fun j hj => ?_⟩
        have h2 : α (QuotientGroup.mk ⟨j, hj⟩) = QuotientGroup.mk ⟨j, hj⟩ := by
          rw [h1]
          rfl
        have h4 : ((⟨j, hj⟩ : ↥(conjugate K m))⁻¹ *
            LocalAnalysis.ComponentInitial.normalizerConjHom (conjugate K m) ⟨a, haN⟩ ⟨j, hj⟩) ∈
            pPrimeCore 2 ↥(conjugate K m) := QuotientGroup.eq.mp h2.symm
        have h5 : j⁻¹ * (a * j * a⁻¹) ∈ (pPrimeCore 2 ↥(conjugate K m)).map
            (conjugate K m).subtype := ⟨_, h4, rfl⟩
        rw [hai] at h5 ⊢
        simpa only [mul_assoc] using h5
      have hcount := GrS4.card_inf_centralizer_eq haN haa
      rcases CFSG.GH74.Generic.S45.he_fixed_card e' α hα2 hα1 with h | h | h
      · exact h2A G a x J S A hset hcent hrun h3 W hW hWodd hWB hNJ K hKM hKc ⟨e⟩ hJK m hm
          hK'ne haN (by rw [hcount, h])
      · exact h2B G a x J S A hset hcent hrun h3 W hW hWodd hWB hNJ K hKM hKc ⟨e⟩ hJK m hm
          hK'ne haN (by rw [hcount, h])
      · exact hOut G a x J S A hset hcent hrun h3 W hW hWodd hWB hNJ K hKM hKc ⟨e⟩ hJK m hm
          hK'ne haN (by rw [hcount, h])
  ·
    obtain ⟨L, h1, h2, h3⟩ :=
      GrS4.exists_held_of_not_mem_normalizer haM haa hCa hK'M hK'c e' haN
    exact hno L h1 h2 h3

end CFSG.ComponentClassification.GrSLit
