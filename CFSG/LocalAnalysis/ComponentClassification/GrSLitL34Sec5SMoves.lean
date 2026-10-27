module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5SBlock
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5SOrbit
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5SPair
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5SUniq
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5Cor217Invt
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsDischarges
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsUnbal

public section

namespace CFSG.ComponentClassification.GrSLit.GrS5S

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ComponentClassification.UnbalancedGS
  CFSG.ComponentClassification.GrSLit CFSG.ComponentClassification.GrSLit.GrS5
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)

variable {G : Type} [Group G] [Finite G]

theorem false_of_moves_center
    (hS : SchreierFor Blueprint.Catalog)
    (hU : CatalogueU.CatalogAlmostSimpleUnbalancedOutcome) (hheld : KProperRelativeB.HeldInput)
    (hSol : SolomonCommutingCoreInput) (hGW : GorensteinWalterConnectedInput)
    (hMax : MaximalTwoComponentInput) (hL34 : L34InvolutionCentralizerFact) (h58 : L34Lemma58)
    (h59 : L34Lemma59) (hSC : L34AutSylowCenterFact) (hComp : L34Cor217ComponentStep)
    {L : Subgroup G} {t : G} {S T : Subgroup G} (hset : L34Sec5Setting G L t S T)
    (hexp : ∀ y ∈ S ⊓ coreActionKernel L ⊓ L, y * y = 1)
    (hΩ : ∃ z : G, orderOf z = 2 ∧ z ≠ t ∧
      omegaOne (S ⊓ coreActionKernel L) = zpowers t ⊔ zpowers z)
    (hZnc : ∃ y ∈ S ⊓ coreActionKernel L ⊓ L, ∃ s ∈ S, s * y ≠ y * s) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hset' := hset
  obtain ⟨hbase, ⟨⟨-, -, -, -, -, hto, -, -⟩, htypeL, -⟩, -, hSyl, htS, -, -⟩ := hset'
  obtain ⟨-, hLt, hLpt⟩ := eq_of_mem_inf_centralizer hS hU hheld hSol hGW hset
  have hZS := mem_center_of_setting hS hU hheld hSol hGW hset
  have ht2 : t * t = 1 := by rw [← pow_two, ← hto, pow_orderOf_eq_one]
  obtain ⟨w, s, hwZ, hs, hsw⟩ : ∃ w s : G, w ∈ S ⊓ coreActionKernel L ⊓ L ∧ s ∈ S ∧
      s * w * s⁻¹ = t * w := by
    obtain ⟨z, hzo, hzt, hΩeq⟩ := hΩ
    obtain ⟨y, hy, s, hs, hsy⟩ := hZnc
    have hz2 : z * z = 1 := by rw [← pow_two, ← hzo, pow_orderOf_eq_one]
    have hzS : z ∈ S := by
      have h : z ∈ omegaOne (S ⊓ coreActionKernel L) := by
        rw [hΩeq]
        exact mem_sup_right (mem_zpowers z)
      exact (mem_inf.mp (omegaOne_le _ h)).1
    have htz : t * z = z * t := (hZS z hzS).symm
    have hfour : ∀ x ∈ S ⊓ coreActionKernel L ⊓ L, x = 1 ∨ x = t ∨ x = z ∨ x = t * z := by
      intro x hx
      have hxΩ : x ∈ omegaOne (S ⊓ coreActionKernel L) :=
        subset_closure ⟨(mem_inf.mp hx).1, hexp x hx⟩
      rw [hΩeq] at hxΩ
      exact mem_four_of_mem_sup ht2 hz2 htz hxΩ
    obtain ⟨⟨hyS, hyK⟩, hyL⟩ := mem_inf.mp hy
    have hconj : s * y * s⁻¹ ∈ S ⊓ coreActionKernel L ⊓ L := by
      refine mem_inf.mpr ⟨mem_inf.mpr ⟨mul_mem (mul_mem hs hyS) (inv_mem hs), ?_⟩, ?_⟩
      · exact (mem_normalizer_iff.mp (normalizer_le_normalizer_coreActionKernel L (hSyl.1 hs))
          y).mp hyK
      · exact (mem_normalizer_iff.mp (hSyl.1 hs) y).mp hyL
    have hy1 : y ≠ 1 := fun h => hsy (by rw [h, mul_one, one_mul])
    have hyt : y ≠ t := fun h => hsy (by rw [h]; exact hZS s hs)
    have hcy : s * y * s⁻¹ ≠ y := fun h => hsy (by
      calc s * y = s * y * s⁻¹ * s := by group
        _ = y * s := by rw [h])
    have hc1 : s * y * s⁻¹ ≠ 1 := fun h => hy1 (by
      calc y = s⁻¹ * (s * y * s⁻¹) * s := by group
        _ = 1 := by rw [h]; group)
    have hct : s * y * s⁻¹ ≠ t := fun h => hyt (by
      calc y = s⁻¹ * (s * y * s⁻¹) * s := by group
        _ = s⁻¹ * t * s := by rw [h]
        _ = t := by rw [mul_assoc, ← hZS s hs, ← mul_assoc, inv_mul_cancel, one_mul])
    refine ⟨y, s, hy, hs, ?_⟩
    rcases hfour y hy with h | h | h | h
    · exact absurd h hy1
    · exact absurd h hyt
    · rcases hfour _ hconj with h' | h' | h' | h'
      · exact absurd h' hc1
      · exact absurd h' hct
      · exact absurd (h'.trans h.symm) hcy
      · rw [h', h]
    · rcases hfour _ hconj with h' | h' | h' | h'
      · exact absurd h' hc1
      · exact absurd h' hct
      · rw [h', h, ← mul_assoc, ht2, one_mul]
      · exact absurd (h'.trans h.symm) hcy
  have hwS : w ∈ S := (mem_inf.mp (mem_inf.mp hwZ).1).1
  have hperfL : ⁅L, L⁆ = L := GSThmB.commutator_eq_self_of_isPComponent hLt hLpt
  have hZsub : ∀ x ∈ S ⊓ zStarIn L, x ∈ S ⊓ coreActionKernel L ⊓ L := fun x hx =>
    mem_inf.mpr ⟨mem_inf.mpr ⟨(mem_inf.mp hx).1, zStarIn_le_coreActionKernel L (mem_inf.mp hx).2⟩,
      map_subtype_le _ (mem_inf.mp hx).2⟩
  obtain ⟨y, hySL, hyZ, hy2, hyc⟩ := l34SylowCentralLiftFact G L S hperfL htypeL hSyl
    (fun x hx => hexp x (hZsub x hx))
  obtain ⟨hyS, hyL⟩ := mem_inf.mp hySL
  have hy1 : y ≠ 1 := fun h => hyZ (h ▸ one_mem _)
  have hyo : orderOf y = 2 := orderOf_eq_prime (by rw [pow_two, hy2]) hy1
  have hyK : y ∉ coreActionKernel L := fun hK =>
    hyZ (inf_coreActionKernel_le_zStarIn L (mem_inf.mpr ⟨hyL, hK⟩))
  obtain ⟨-, u₁, hu₁, hu₁n⟩ := l34Lemma53_of_inputs hS hU hheld hSol hGW G L t S T hset y hyS hyo
    hyK (mem_sup_left hyL)
  obtain ⟨u, hu, huc⟩ : ∃ u ∈ L34UnbalancingSet L t S, ∀ g ∈ S, g * u = u * g := by
    have hyt : y * t = t * y := hZS y hyS
    rcases hu₁ with rfl | rfl
    · exact ⟨u₁, ⟨mem_sup_left hySL, hyo, hu₁n⟩, hyc⟩
    · have htK : t ∈ coreActionKernel L := mem_coreActionKernel_of_commute fun l hl =>
        (mem_centralizer_singleton_iff.mp (hLt hl) : l * t = t * l).symm
      have hyne : y ≠ t := fun h => hyK (h ▸ htK)
      have hyto : orderOf (y * t) = 2 := by
        refine orderOf_eq_prime ?_ ?_
        · calc (y * t) ^ 2 = y * (t * y) * t := by rw [pow_two]; group
            _ = y * y * (t * t) := by rw [← hyt]; group
            _ = 1 := by rw [hy2, ht2, one_mul]
        · intro h
          apply hyne
          rw [mul_eq_one_iff_eq_inv.mp h, inv_eq_of_mul_eq_one_right ht2]
      refine ⟨y * t, ⟨mul_mem (mem_sup_left hySL) (mem_sup_right (mem_zpowers t)), hyto, hu₁n⟩,
        fun g hg => ?_⟩
      calc g * (y * t) = (g * y) * t := by group
        _ = y * (g * t) := by rw [hyc g hg]; group
        _ = y * (t * g) := by rw [hZS g hg]
        _ = y * t * g := by group
  have hu' := hu
  obtain ⟨huS₀, hu2, hun⟩ := hu'
  have huS : u ∈ S := (sup_le inf_le_left (zpowers_le.mpr htS) : S ⊓ L ⊔ zpowers t ≤ S) huS₀
  have htu : t * u = u * t := (hZS u huS).symm
  have hYD : oddIn L ⊓ centralizer ({u} : Set G) ≤
      oddIn (centralizer ({t} : Set G)) ⊓ centralizer ({u} : Set G) :=
    inf_le_inf_right _ (GSLit.map_pPrimeCore_le_of_isPComponent hLt hLpt)
  by_cases h34 : ∃ K₁ : Subgroup G, K₁ ≤ centralizer ({u} : Set G) ∧
      IsPComponent 2 (K₁.subgroupOf (centralizer ({u} : Set G))) ∧
      ¬ ⁅K₁, oddIn L ⊓ centralizer ({u} : Set G)⁆ ≤ oddIn K₁ ∧
      IsL34Type (K₁ ⧸ Open.fusionZStar K₁)
  · obtain ⟨K₁, hK₁u, hK₁p, hK₁n, htype⟩ := h34
    have hSN : S ≤ normalizer (K₁ : Set G) := fun g hg =>
      l34Sec5ComponentInvariantStep_of_comp hMax hComp G L t S T hset u huS₀ hu2 K₁ hK₁u hK₁p hK₁n
        htype (mem_inf.mpr ⟨hg, mem_centralizer_singleton_iff.mpr (huc g hg)⟩)
    have hT := gsUnbalancingTriple_of_not_le hSol hto hu2 htu hK₁u hK₁p hYD hK₁n
    exact false_of_unitary_conj (GSThmB.commutator_eq_self_of_isPComponent hK₁u hK₁p) htype
      (L34Facts.l34UnbalancingUnitaryStep G u t K₁ hT htype) (hSN hs) (hSN hwS) hsw
  · have hall : ∀ K₁ : Subgroup G, K₁ ≤ centralizer ({u} : Set G) →
        IsPComponent 2 (K₁.subgroupOf (centralizer ({u} : Set G))) →
        ¬ ⁅K₁, oddIn L ⊓ centralizer ({u} : Set G)⁆ ≤ oddIn K₁ →
        IsL2Type 5 (K₁ ⧸ pPrimeCore 2 K₁) ∨ IsL2Type 7 (K₁ ⧸ pPrimeCore 2 K₁) := by
      intro K₁ hK₁u hK₁p hK₁n
      rcases hbase.2.2.2.2.2.2.2 u t K₁
        (gsUnbalancingTriple_of_not_le hSol hto hu2 htu hK₁u hK₁p hYD hK₁n) with h | h | h
      · exact Or.inl h
      · exact Or.inr h
      · exact (h34 ⟨K₁, hK₁u, hK₁p, hK₁n, h⟩).elim
    obtain ⟨K₁, hK₁u, hK₁p, hK₁n⟩ := exists_isPComponent_not_le hSol hto hu2 htu hYD hun
    have hSN := HSFLit.L34Uniq.l34Lemma511UniqueStepC_of_inputs hS hU hheld hSol hGW hMax hL34
      h58 h59 hSC (HSFLit.L34Uniq.l34Lemma511OrbitStepC_of_inputs hS hU hheld hSol hGW hMax hL34)
      (HSFLit.L34Uniq.l34Lemma511PairStepC_of_inputs hS hU hheld hSol hGW hMax hL34)
      G L t S T hset u hu huc hall K₁ hK₁u hK₁p hK₁n
    exact false_of_l2_conj (gsUnbalancingTriple_of_not_le hSol hto hu2 htu hK₁u hK₁p hYD hK₁n)
      (hall K₁ hK₁u hK₁p hK₁n) (GrS5.IsSylowTwoIn.isPGroup hSyl) hSN
      (fun g hg => mem_centralizer_singleton_iff.mpr (hZS g hg)) hs hwS hsw

end CFSG.ComponentClassification.GrSLit.GrS5S
