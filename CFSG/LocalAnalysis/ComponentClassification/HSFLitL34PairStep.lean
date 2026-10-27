module

public import CFSG.LocalAnalysis.ComponentClassification.HSFLitL34PairIndex
public import CFSG.LocalAnalysis.ComponentClassification.HSFLitL34PairSq
public import CFSG.LocalAnalysis.ComponentClassification.HSFLitL34UniqInputs
public import CFSG.LocalAnalysis.ComponentClassification.HSFLitAutL34Make
public import CFSG.LocalAnalysis.ComponentClassification.HSFLitL34UniqComp

public section

namespace CFSG.ComponentClassification.HSFLit.L34Uniq

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ComponentClassification.UnbalancedGS
  CFSG.ComponentClassification.GrSLit CFSG.ComponentClassification.GrSLit.GrS5
  CFSG.ComponentClassification.HSFLit.L34Inv
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)

theorem l34Lemma511PairStep_of_inputs
    (hS : SchreierFor Blueprint.Catalog)
    (hU : CatalogueU.CatalogAlmostSimpleUnbalancedOutcome) (hheld : KProperRelativeB.HeldInput)
    (hSol : SolomonCommutingCoreInput) (hGW : GorensteinWalterConnectedInput)
    (hMax : MaximalTwoComponentInput) (hL34 : L34InvolutionCentralizerFact) :
    L34Lemma511PairStep := by
  intro G _ _ L t S T hset u hu huc _ hall K₁ hK₁u hK₁p hK₁n s hs hsK horb e₁ he₁ he₁o _ _ hZQ
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hset' := hset
  obtain ⟨-, ⟨⟨-, -, -, -, -, hto, -, -⟩, htypeL, -⟩, -, hSyl, htS, -, -⟩ := hset'
  have hS2 : IsPGroup 2 S := GrS5.IsSylowTwoIn.isPGroup hSyl
  obtain ⟨-, hLt, hLpt⟩ := eq_of_mem_inf_centralizer hS hU hheld hSol hGW hset
  have hZS := mem_center_of_setting hS hU hheld hSol hGW hset
  have ht2 : t * t = 1 := by rw [← pow_two, ← hto, pow_orderOf_eq_one]
  have hu' := hu
  obtain ⟨huS₀, hu2, -⟩ := hu'
  have huS : u ∈ S := (sup_le inf_le_left (zpowers_le.mpr htS) : S ⊓ L ⊔ zpowers t ≤ S) huS₀
  have htu : t * u = u * t := (hZS u huS).symm
  have hYD : oddIn L ⊓ centralizer ({u} : Set G) ≤
      oddIn (centralizer ({t} : Set G)) ⊓ centralizer ({u} : Set G) :=
    inf_le_inf_right _ (GSLit.map_pPrimeCore_le_of_isPComponent hLt hLpt)
  obtain ⟨hK₂u, hK₂p, hK₂n⟩ := conj_component hS hU hheld hSol hGW hMax hset hu huc hK₁u hK₁p
    hK₁n hs
  set K₂ := conjugate K₁ s with hK₂
  have htype₁ := hall K₁ hK₁u hK₁p hK₁n
  have htype₂ := hall K₂ hK₂u hK₂p hK₂n
  have hT₁ := gsUnbalancingTriple_of_not_le hSol hto hu2 htu hK₁u hK₁p hYD hK₁n
  have hT₂ := gsUnbalancingTriple_of_not_le hSol hto hu2 htu hK₂u hK₂p hYD hK₂n
  have htC₁ : t ∉ coreActionKernel K₁ := by
    simpa using AutL2.l2UnbalancingOuter G u t K₁ hT₁ htype₁ 1 (one_mem _)
  have htC₂ : t ∉ coreActionKernel K₂ := by
    simpa using AutL2.l2UnbalancingOuter G u t K₂ hT₂ htype₂ 1 (one_mem _)
  set N := S ⊓ normalizer (K₁ : Set G) ⊓ normalizer (K₂ : Set G) with hN
  have hNS : N ≤ S := inf_le_left.trans inf_le_left
  have hN2 : IsPGroup 2 N := hS2.to_le hNS
  have htN₁ : t ∈ normalizer (K₁ : Set G) := (((solomon_involutions hSol hto hu2 htu).2 K₁ hK₁u
    hK₁p).2 fun h => hK₁n ((commutator_mono le_rfl hYD).trans h)).1
  have htN₂ : t ∈ normalizer (K₂ : Set G) := (((solomon_involutions hSol hto hu2 htu).2 K₂ hK₂u
    hK₂p).2 fun h => hK₂n ((commutator_mono le_rfl hYD).trans h)).1
  have htN : t ∈ N := mem_inf.mpr ⟨mem_inf.mpr ⟨htS, htN₁⟩, htN₂⟩
  have htc : ∀ n ∈ N, n * t = t * n := fun n hn => hZS n (hNS hn)
  have hle₁ : N ≤ normalizer (K₁ : Set G) ⊓ centralizer ({t} : Set G) := fun n hn =>
    mem_inf.mpr ⟨(mem_inf.mp (mem_inf.mp hn).1).2, mem_centralizer_singleton_iff.mpr (htc n hn)⟩
  have hle₂ : N ≤ normalizer (K₂ : Set G) ⊓ centralizer ({t} : Set G) := fun n hn =>
    mem_inf.mpr ⟨(mem_inf.mp hn).2, mem_centralizer_singleton_iff.mpr (htc n hn)⟩
  obtain ⟨hsq₁, h4₁⟩ := (AutL2.l2UnbalancingAutFact G u t K₁ N hT₁ htype₁ hN2).1 hle₁
  obtain ⟨hsq₂, h4₂⟩ := (AutL2.l2UnbalancingAutFact G u t K₂ N hT₂ htype₂ hN2).1 hle₂
  have htCL : t ∈ centralizer (L : Set G) := mem_centralizer_iff.mpr fun h hh =>
    mem_centralizer_singleton_iff.mp (hLt hh)
  have htL : t ∈ coreActionKernel L := by
    refine mem_coreActionKernel.mpr ⟨centralizer_le_normalizer _ htCL, fun j hj => ?_⟩
    have hjt : j * t = t * j := mem_centralizer_singleton_iff.mp (hLt hj)
    rw [show j⁻¹ * t⁻¹ * j * t = 1 by
      calc j⁻¹ * t⁻¹ * j * t = j⁻¹ * t⁻¹ * (j * t) := by group
        _ = j⁻¹ * t⁻¹ * (t * j) := by rw [hjt]
        _ = 1 := by group]
    exact one_mem _
  have hkey : ∀ K : Subgroup G, S ⊓ coreActionKernel L ⊓ coreActionKernel K = ⊥ →
      ∀ q ∈ S ⊓ coreActionKernel L,
        (q ∈ coreActionKernel K ∨ q * t ∈ coreActionKernel K) ↔ (q = 1 ∨ q = t) := by
    intro K hK q hq
    have hbot : ∀ x ∈ S ⊓ coreActionKernel L, x ∈ coreActionKernel K → x = 1 := by
      intro x hx hxK
      have h1 : x ∈ S ⊓ coreActionKernel L ⊓ coreActionKernel K := mem_inf.mpr ⟨hx, hxK⟩
      rw [hK] at h1
      exact h1
    constructor
    · rintro (h | h)
      · exact Or.inl (hbot q hq h)
      · right
        have h1 := hbot _ (mul_mem hq (mem_inf.mpr ⟨htS, htL⟩)) h
        calc q = q * t * t := by rw [mul_assoc, ht2, mul_one]
          _ = t := by rw [h1, one_mul]
    · rintro (h | h) <;> rw [h]
      · exact Or.inl (one_mem _)
      · exact Or.inr (by rw [ht2]; exact one_mem _)
  have hQ₁ := inf_coreActionKernel_eq_bot hS hU hheld hSol hGW hMax hL34 hset hu hK₁u hK₁p hK₁n
    htype₁
  have hQ₂ := inf_coreActionKernel_eq_bot hS hU hheld hSol hGW hMax hL34 hset hu hK₂u hK₂p hK₂n
    htype₂
  have hPsq : ∀ g ∈ S, g * g ∈ N ∧
      ((g * g ∈ coreActionKernel K₁ ∨ g * g * t ∈ coreActionKernel K₁) ↔
        (g * g ∈ coreActionKernel K₂ ∨ g * g * t ∈ coreActionKernel K₂)) := by
    intro g hg
    have hgt : g⁻¹ * t * g = t := by
      rw [mul_assoc, ← hZS g hg, ← mul_assoc, inv_mul_cancel, one_mul]
    rcases conj_pair hs hsK horb hg with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · have hgN : g ∈ N := mem_inf.mpr ⟨mem_inf.mpr ⟨hg, mem_normalizer_of_conjugate_eq h1⟩,
        mem_normalizer_of_conjugate_eq h2⟩
      exact ⟨mul_mem hgN hgN, ⟨fun _ => Or.inl (hsq₂ g hgN), fun _ => Or.inl (hsq₁ g hgN)⟩⟩
    · have hgg₁ : conjugate K₁ (g * g) = K₁ := by rw [← conjugate_conjugate'', h1, h2]
      have hgg₂ : conjugate K₂ (g * g) = K₂ := by rw [← conjugate_conjugate'', h2, h1]
      have hg2N : g * g ∈ N := mem_inf.mpr ⟨mem_inf.mpr ⟨mul_mem hg hg,
        mem_normalizer_of_conjugate_eq hgg₁⟩, mem_normalizer_of_conjugate_eq hgg₂⟩
      refine ⟨hg2N, ?_⟩
      have e1 : g⁻¹ * (g * g) * g = g * g := by group
      have e2 : g⁻¹ * (g * g * t) * g = g * g * t := by
        rw [show g⁻¹ * (g * g * t) * g = g * g * (g⁻¹ * t * g) by group, hgt]
      have hc₁ : ∀ x ∈ coreActionKernel K₁, g⁻¹ * x * g ∈ coreActionKernel K₂ := fun x hx => by
        have h3 := GSLit.conj_mem_coreActionKernel_conjugate hx g
        rwa [h1] at h3
      have hc₂ : ∀ x ∈ coreActionKernel K₂, g⁻¹ * x * g ∈ coreActionKernel K₁ := fun x hx => by
        have h3 := GSLit.conj_mem_coreActionKernel_conjugate hx g
        rwa [h2] at h3
      constructor
      · rintro (h | h)
        · exact Or.inl (by rw [← e1]; exact hc₁ _ h)
        · exact Or.inr (by rw [← e2]; exact hc₁ _ h)
      · rintro (h | h)
        · exact Or.inl (by rw [← e1]; exact hc₂ _ h)
        · exact Or.inr (by rw [← e2]; exact hc₂ _ h)
  have he₁S : e₁ ∈ S := (mem_inf.mp he₁).1
  have he₁K : e₁ ∈ K₁ := (mem_inf.mp he₁).2
  have he₁2 : e₁ * e₁ = 1 := by rw [← pow_two, ← he₁o, pow_orderOf_eq_one]
  have he₁C₂ : e₁ ∈ coreActionKernel K₂ :=
    le_coreActionKernel_of_ne hK₂u hK₁u hK₂p hK₁p hsK he₁K
  have he₁N : e₁ ∈ N := mem_inf.mpr ⟨mem_inf.mpr ⟨he₁S, le_normalizer he₁K⟩,
    (mem_coreActionKernel.mp he₁C₂).1⟩
  have he₁C₁ : ¬ (e₁ ∈ coreActionKernel K₁ ∨ e₁ * t ∈ coreActionKernel K₁) := by
    rintro (h | h)
    · have h1 := odd_orderOf_inner_l2 htype₁ he₁K h
      rw [he₁o] at h1
      exact absurd h1 (by decide)
    · apply AutL2.l2UnbalancingOuter G u t K₁ hT₁ htype₁ e₁ he₁K
      rw [inv_eq_of_mul_eq_one_right he₁2]
      exact h
  have hperfL : ⁅L, L⁆ = L := GSThmB.commutator_eq_self_of_isPComponent hLt hLpt
  obtain ⟨ρ⟩ := AutL34.exists_real hperfL htypeL
  have hZN : S ⊓ L ⊓ centralizer ((S ⊓ L : Subgroup G) : Set G) ≤
      normalizer ((S ⊓ coreActionKernel L : Subgroup G) : Set G) := fun g hg =>
    mem_normalizer_inf' (le_normalizer (mem_inf.mp (mem_inf.mp hg).1).1)
      (normalizer_le_normalizer_coreActionKernel L (hSyl.1 (mem_inf.mp (mem_inf.mp hg).1).1))
  have hZQ' : e₁ ∈ ((S ⊓ L ⊓ centralizer ((S ⊓ L : Subgroup G) : Set G) ⊔
      S ⊓ coreActionKernel L : Subgroup G) : Set G) := hZQ
  rw [coe_mul_of_left_le_normalizer_right _ _ hZN] at hZQ'
  obtain ⟨a, ha, q, hq, hae⟩ := hZQ'
  obtain ⟨g, hg, hgk⟩ := ρ.exists_sq_of_center hSyl ha
  have hgS : g ∈ S := (mem_inf.mp hg).1
  have hcQ : a⁻¹ * (g * g) ∈ S ⊓ coreActionKernel L := mem_inf.mpr
    ⟨mul_mem (inv_mem (mem_inf.mp (mem_inf.mp ha).1).1) (mul_mem hgS hgS), hgk⟩
  set q' := (a⁻¹ * (g * g))⁻¹ * q with hq'
  have hq'Q : q' ∈ S ⊓ coreActionKernel L := mul_mem (inv_mem hcQ) hq
  have he : e₁ = g * g * q' := by rw [hq', ← hae]; group
  obtain ⟨hg2N, hPg⟩ := hPsq g hgS
  have hq'N : q' ∈ N := by
    have h1 := mul_mem (inv_mem hg2N) he₁N
    rwa [he, show (g * g)⁻¹ * (g * g * q') = q' by group] at h1
  have h1 := twoClass_mul htN ht2 htc htC₁ h4₁ hg2N hq'N
  have h2 := twoClass_mul htN ht2 htc htC₂ h4₂ hg2N hq'N
  rw [← he] at h1 h2
  have h3 := (hkey K₁ hQ₁ q' hq'Q).trans (hkey K₂ hQ₂ q' hq'Q).symm
  apply he₁C₁
  rw [h1, hPg, h3, ← h2]
  exact Or.inl he₁C₂

end CFSG.ComponentClassification.HSFLit.L34Uniq
