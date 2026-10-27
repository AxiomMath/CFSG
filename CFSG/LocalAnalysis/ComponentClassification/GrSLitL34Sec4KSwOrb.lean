module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4KSwZOne
import CFSG.LocalAnalysis.ComponentClassification.CatLeafAlt
public import Certificates.Kernel.ThCent.Leaves

public section

namespace CFSG.ComponentClassification.GrSLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer

@[expose] def L34UnitaryFusionAt {G : Type} [Group G] (a : G) (J S W : Subgroup G) : Prop :=
  ∀ g : G, g⁻¹ * a * g ∈ S → IsL34Unitary J (g⁻¹ * a * g) →
    ∃ m ∈ normalizer (W : Set G), g⁻¹ * a * g = m⁻¹ * a * m

@[expose] def L34Lemma43UnitaryStep : Prop :=
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
        IsSylowTwoIn S (normalizer (W : Set G)) → (∃ P : Sylow 2 G, (P : Subgroup G) = S) →
        S ≤ normalizer (K : Set G) → ¬ normalizer (W : Set G) ≤ normalizer (K : Set G) →
        ¬ oddIn K ≤ J →
        L34UnitaryFusionAt a J S W

end CFSG.ComponentClassification.GrSLit

namespace CFSG.ComponentClassification.GrSLit.KSwOrb

open CFSG Subgroup CFSG.ComponentClassification CFSG.ComponentClassification.UnbalancedLayer

theorem fusion_of_unitaryFusion
    (hMax : MaximalTwoComponentInput) {G : Type} [Group G]
    [Finite G] {a x : G} {J S W : Subgroup G} (hset : L34Sec4Setting G a x J S)
    (hcent : ∀ s ∈ S, s * a = a * s) (h3 : IsThreeConnected (S ⊓ withKernel J))
    (hWB : ∀ B : Subgroup G, B ≤ S ⊓ withKernel J → IsAbelianTwoOfRank 3 B → wGroup B = W)
    (hNJ : normalizer (J : Set G) ≤ normalizer (W : Set G)) (hUF : L34UnitaryFusionAt a J S W)
    (hSM : IsSylowTwoIn S (normalizer (W : Set G))) (hSyl : ∃ P : Sylow 2 G, (P : Subgroup G) = S)
    {g : G} (hg : g⁻¹ * a * g ∈ normalizer (W : Set G)) :
    ∃ m ∈ normalizer (W : Set G), g⁻¹ * a * g = m⁻¹ * a * m := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, hU3, hL34, -, hS, haS, -⟩ := id hset
  have hJa : J ≤ centralizer ({a} : Set G) := hU3.2.2.2.1
  have hJper : ⁅J, J⁆ = J := UnbalancedCorr.commutator_eq_of_isPComponent hJa hU3.2.2.2.2.1
  have ha2 : orderOf a = 2 := hU3.1
  have haK : a ∈ coreActionKernel J := GrS4.mem_coreActionKernel_of_le_centralizer hJa
  have hS2 : IsPGroup 2 S := GrS4.isPGroup_of_isSylowTwoIn hS
  have hy2 : IsPGroup 2 (zpowers (g⁻¹ * a * g)) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, pow_one]
    have := orderOf_injective (MulAut.conj g⁻¹).toMonoidHom (MulAut.conj g⁻¹).injective a
    simpa [MulAut.conj_apply, ha2] using this
  obtain ⟨m₁, hm₁M, hm₁⟩ := GrS4.exists_conj_mem_of_isSylowTwoIn hSM (zpowers_le.mpr hg) hy2
  have hbS : (g * m₁)⁻¹ * a * (g * m₁) ∈ S := by
    have := hm₁ _ (mem_zpowers _)
    rwa [show m₁⁻¹ * (g⁻¹ * a * g) * m₁ = (g * m₁)⁻¹ * a * (g * m₁) by group] at this
  suffices hmain : ∃ m ∈ normalizer (W : Set G), (g * m₁)⁻¹ * a * (g * m₁) = m⁻¹ * a * m by
    obtain ⟨m, hm, hbm⟩ := hmain
    refine ⟨m * m₁⁻¹, mul_mem hm (inv_mem hm₁M), ?_⟩
    calc g⁻¹ * a * g = m₁ * ((g * m₁)⁻¹ * a * (g * m₁)) * m₁⁻¹ := by group
      _ = (m * m₁⁻¹)⁻¹ * a * (m * m₁⁻¹) := by rw [hbm]; group
  generalize g * m₁ = k at hbS ⊢
  by_cases hka : k⁻¹ * a * k = a
  · exact ⟨1, one_mem _, by rw [hka]; group⟩
  by_cases hkK : k⁻¹ * a * k ∈ withKernel J
  · exact GrS5S.exists_conj_of_mem_withKernel hset hcent h3 hWB hNJ hSyl hbS hkK
  obtain ⟨c, hc, E, hES, hE, hbE, haE, -, hE4⟩ := GrS5S.exists_eight_of_conj hset hcent hbS hka
  have hcN : c ∈ normalizer (J : Set G) := (mem_inf.mp hc).1
  have hkc : (k * c)⁻¹ * a * (k * c) = c⁻¹ * (k⁻¹ * a * k) * c := by group
  suffices hmain : ∃ m ∈ normalizer (W : Set G), (k * c)⁻¹ * a * (k * c) = m⁻¹ * a * m by
    obtain ⟨m, hm, hbm⟩ := hmain
    refine ⟨m * c⁻¹, mul_mem hm (hNJ (inv_mem hcN)), ?_⟩
    calc k⁻¹ * a * k = c * ((k * c)⁻¹ * a * (k * c)) * c⁻¹ := by group
      _ = (m * c⁻¹)⁻¹ * a * (m * c⁻¹) := by rw [hbm]; group
  have hb'E : (k * c)⁻¹ * a * (k * c) ∈ E := hkc ▸ hbE
  have hb'K : (k * c)⁻¹ * a * (k * c) ∉ withKernel J := by
    rw [hkc]
    intro h
    apply hkK
    have := GrS4.map_conj_withKernel_le hcN (mem_map_of_mem (MulAut.conj c).toMonoidHom h)
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at this
    rwa [show c * (c⁻¹ * (k⁻¹ * a * k) * c) * c⁻¹ = k⁻¹ * a * k by group] at this
  by_cases hiso : ∀ s ∈ S, s * s = 1 → (∀ e ∈ E, s * e = e * s) → s ∈ E
  ·
    have hEC : 2 ≤ Nat.card ↥(E ⊓ coreActionKernel J) := by
      have := Subgroup.card_le_of_le (zpowers_le.mpr (mem_inf.mpr ⟨haE, haK⟩) :
        zpowers a ≤ E ⊓ coreActionKernel J)
      rwa [Nat.card_zpowers, ha2] at this
    obtain ⟨⟨-, hbad, hEJ⟩, -⟩ := GrS5S.l34WCriterionDFact_of_certs G J S hJper hL34
      (GrS4.isSylowTwoIn_inf hS) hS2 hS.1 E hES hE (hE4 hkK) hEC
      fun s hs hss hsc => hiso s (mem_inf.mp hs).1 hss hsc
    rcases hbad with ⟨-, hU⟩ | ⟨hZ16, hF⟩
    · exact hUF (k * c) (hES hb'E) (hU _ hb'E hb'K)
    · have hZ : S ⊓ zStarIn J ≠ ⊥ := fun h => by
        rw [h, Subgroup.card_bot] at hZ16
        norm_num at hZ16
      have haJ : a ∈ J := hEJ hZ (mem_inf.mpr ⟨haE, mem_sup_right haK⟩)
      have hZJ : zStarIn J = J ⊓ coreActionKernel J := GSThmB.map_fusionZStar_eq J
      have haZ : a ∈ zStarIn J := by
        rw [hZJ]
        exact mem_inf.mpr ⟨haJ, haK⟩
      exact GrS5S.exists_conj_of_field hMax hset hcent h3 hWB hNJ hSyl (hES hb'E) hZ16
        (hF _ hb'E hb'K) (mem_inf.mpr ⟨haS, haZ⟩)
  · push Not at hiso
    obtain ⟨s₀, hs₀S, hs₀2, hs₀E, hs₀n⟩ := hiso
    exact GrS5S.exists_conj_of_not_isolated hset hcent hWB hSyl hES hE
      (fun e he => hE.1.1 e he _ hb'E) hs₀S hs₀2 hs₀E hs₀n (hs₀E _ hb'E)

theorem false_of_fusion
    (hMax : MaximalTwoComponentInput)
    (hHS : RankThree.PartTwo.Sec21.HoltUniqueFixedPointSimple) {G : Type} [Group G] [Finite G]
    {a x : G} {J S A W : Subgroup G} (hset : L34Sec4Setting G a x J S)
    (hcent : ∀ s ∈ S, s * a = a * s) (hrun : L34Sec4Running J A) (hW : W ≠ ⊥)
    (hWodd : Odd (Nat.card W)) (hNJ : normalizer (J : Set G) ≤ normalizer (W : Set G))
    (hSyl : ∃ P : Sylow 2 G, (P : Subgroup G) = S)
    (hfus : ∀ g : G, g⁻¹ * a * g ∈ normalizer (W : Set G) →
      ∃ m ∈ normalizer (W : Set G), g⁻¹ * a * g = m⁻¹ * a * m) : False := by
  obtain ⟨hbase, hU3, hL34, hmax, -, haS, -⟩ := id hset
  obtain ⟨hsimple, hnab, hK, -, hUo, -, -, -⟩ := hbase
  have : IsSimpleGroup G := hsimple
  have ha2 : orderOf a = 2 := hU3.1
  have hJa : J ≤ centralizer ({a} : Set G) := hU3.2.2.2.1
  have hJc := hU3.2.2.2.2.1
  set M : Subgroup G := normalizer (W : Set G) with hM
  have hgs : GSMaximalSetting G a J := ⟨hsimple, hnab, hK, hUo, ha2, hJa, hJc,
    hmax, GrS5.three_le_pRank_of_l34 hL34, Sol78.not_psp4_of_l34 hL34, Or.inl ⟨hL34, hset.1⟩⟩
  have hMtop : M ≠ ⊤ := GrS4.normalizer_ne_top_of_odd hW hWodd ha2
  have hCaN : centralizer ({a} : Set G) ≤ normalizer (J : Set G) :=
    GrS4.centralizer_le_normalizer_of_gsMaximalSetting hMax hgs
  have hCaM : centralizer ({a} : Set G) ≤ M := hCaN.trans hNJ
  have haM : a ∈ M := hCaM (mem_centralizer_singleton_iff.mpr rfl)
  obtain ⟨T, hTS⟩ := hSyl
  have hfix : ∃! ω : G ⧸ M, a • ω = ω := by
    refine ⟨QuotientGroup.mk 1, ?_, fun ω' hω' => ?_⟩
    · show a • (QuotientGroup.mk 1 : G ⧸ M) = QuotientGroup.mk 1
      rw [MulAction.Quotient.smul_mk, smul_eq_mul, QuotientGroup.eq]
      simpa using inv_mem haM
    induction ω' using QuotientGroup.induction_on with
    | H g =>
    have h : a • (QuotientGroup.mk g : G ⧸ M) = QuotientGroup.mk g := hω'
    rw [MulAction.Quotient.smul_mk, smul_eq_mul, QuotientGroup.eq] at h
    rw [QuotientGroup.eq, mul_one]
    have h1 : g⁻¹ * a * g ∈ M := by
      have h2 := inv_mem h
      rwa [show ((a * g)⁻¹ * g)⁻¹ = g⁻¹ * a * g by group] at h2
    obtain ⟨m, hm, hgm⟩ := hfus g h1
    have hc : g * m⁻¹ ∈ centralizer ({a} : Set G) := by
      rw [mem_centralizer_singleton_iff]
      calc g * m⁻¹ * a = g * (m⁻¹ * a * m) * m⁻¹ := by group
        _ = g * (g⁻¹ * a * g) * m⁻¹ := by rw [← hgm]
        _ = a * (g * m⁻¹) := by group
    have h3 := mul_mem (hCaM hc) hm
    rw [inv_mul_cancel_right] at h3
    exact inv_mem h3
  have hTa : ∃ T' : Sylow 2 G, a ∈ (T' : Subgroup G) ∧
      (T' : Subgroup G) ≤ centralizer ({a} : Set G) :=
    ⟨T, by rw [hTS]; exact haS, by
      rw [hTS]
      exact fun s hs => mem_centralizer_singleton_iff.mpr (hcent s hs)⟩
  rcases hHS G hnab M hMtop a ha2 hTa hfix with ⟨M', hM'⟩ | ⟨n, -, ⟨e⟩⟩
  · obtain ⟨-, ⟨hAe, hA8⟩, -⟩ := hrun
    obtain ⟨V, hVA, hV4⟩ := exists_le_card_four hAe.isPGroup (by omega)
    have hJ1 : J ≠ ⊥ := by
      intro hJb
      have hd : Nat.card (↥J ⧸ Open.fusionZStar ↥J) ∣ Nat.card ↥J :=
        Subgroup.card_quotient_dvd_card _
      rw [CatLeaf.card_of_isL34Type hL34, hJb, Subgroup.card_bot] at hd
      norm_num at hd
    exact GrS5S.false_of_isStronglyEmbedded_perfect hM' hV4
      (fun v hv => by rw [pow_two]; exact hAe.2 v (hVA hv)) ha2 hJa
      (GSThmB.commutator_eq_self_of_isPComponent hJa hJc) hJ1
  · exact GrS5S.false_of_mulEquiv_alternatingGroup_l34 e ha2 hJa hCaN hJc hL34

end CFSG.ComponentClassification.GrSLit.KSwOrb

namespace CFSG.ComponentClassification.GrSLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)

theorem l34Lemma43OddOrbitStep_of_unitary
    (hMax : MaximalTwoComponentInput)
    (hHS : RankThree.PartTwo.Sec21.HoltUniqueFixedPointSimple) (hR3 : L34Lemma43UnitaryStep) :
    L34Lemma43OddOrbitStep := by
  intro G _ _ a x J S A hset hcent hrun h3 hZ1 W hW hWodd hWB hNJ K hKM hKc hKL hsup hSM hSyl
    hSK hKn hOK
  exfalso
  have hUF := hR3 G a x J S A hset hcent hrun h3 hZ1 W hW hWodd hWB hNJ K hKM hKc hKL hsup hSM
    hSyl hSK hKn hOK
  exact KSwOrb.false_of_fusion hMax hHS hset hcent hrun hW hWodd hNJ hSyl
    fun g hg => KSwOrb.fusion_of_unitaryFusion hMax hset hcent h3 hWB hNJ hUF hSM hSyl hg

theorem l34Lemma43ZOneResidue_of_unitary
    (hMax : MaximalTwoComponentInput)
    (hS : SchreierFor Blueprint.Catalog)
    (hHS : RankThree.PartTwo.Sec21.HoltUniqueFixedPointSimple) (hCoset : L34CosetInvolutionFact)
    (hG2 : L34Lemma43TwistedStep) (hR3 : L34Lemma43UnitaryStep) : L34Lemma43ZOneResidue :=
  l34Lemma43ZOneResidue_of_twisted hMax hS hHS hCoset hG2
    (l34Lemma43OddOrbitStep_of_unitary hMax hHS hR3)

end CFSG.ComponentClassification.GrSLit
