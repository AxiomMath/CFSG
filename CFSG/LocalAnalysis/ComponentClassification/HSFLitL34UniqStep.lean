module

public import CFSG.LocalAnalysis.ComponentClassification.HSFLitL34UniqE16
public import CFSG.LocalAnalysis.ComponentClassification.HSFLitL34UniqInputs
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5Inputs510
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5Tools510
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5Lemma55
public import CFSG.LocalAnalysis.ComponentClassification.HSFLitL34UniqU1

public section

namespace CFSG.ComponentClassification.HSFLit.L34Uniq

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ComponentClassification.UnbalancedGS
  CFSG.ComponentClassification.GrSLit CFSG.ComponentClassification.GrSLit.GrS5
  CFSG.ComponentClassification.HSFLit.L34Inv
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)

variable {G : Type} [Group G] [Finite G]

theorem l34Lemma511UniqueStep_of_inputs
    (hS : SchreierFor Blueprint.Catalog)
    (hU : CatalogueU.CatalogAlmostSimpleUnbalancedOutcome) (hheld : KProperRelativeB.HeldInput)
    (hSol : SolomonCommutingCoreInput) (hGW : GorensteinWalterConnectedInput)
    (hMax : MaximalTwoComponentInput) (hL34 : L34InvolutionCentralizerFact) (h58 : L34Lemma58)
    (h59 : L34Lemma59) (hSC : L34AutSylowCenterFact) (hCenter : L34Lemma511CenterStep)
    (hPair : L34Lemma511PairStep) : L34Lemma511UniqueStep := by
  intro G _ _ L t S T hset u hu huc hmax hall K₁ hK₁u hK₁p hK₁n
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hN
  obtain ⟨s, hs, hsK⟩ : ∃ s ∈ S, conjugate K₁ s ≠ K₁ := by
    by_contra h
    push Not at h
    exact hN fun g hg => mem_normalizer_of_conjugate_eq (h g hg)
  have hset' := hset
  obtain ⟨hbase, ⟨⟨-, -, -, -, -, hto, -, -⟩, htypeL, -⟩, -, hSyl, htS, -, -⟩ := hset'
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
  set C := centralizer ({u} : Set G) with hC
  set Q := S ⊓ coreActionKernel L with hQ
  have hcomp : ∀ g ∈ S, conjugate K₁ g ≤ C ∧ IsPComponent 2 ((conjugate K₁ g).subgroupOf C) ∧
      ¬ ⁅conjugate K₁ g, oddIn L ⊓ C⁆ ≤ oddIn (conjugate K₁ g) := fun g hg =>
    conj_component hS hU hheld hSol hGW hMax hset hu huc hK₁u hK₁p hK₁n hg
  have hcard₁ := card_inf_component hS hU hheld hSol hGW hMax hset hu huc hK₁u hK₁p hK₁n
    (hall K₁ hK₁u hK₁p hK₁n)
  obtain ⟨e₁, he₁, he₁1⟩ : ∃ e ∈ S ⊓ K₁, e ≠ 1 := by
    have : Nontrivial ↥(S ⊓ K₁) := Finite.one_lt_card_iff_nontrivial.mp (by omega)
    obtain ⟨x, hx⟩ := exists_ne (1 : ↥(S ⊓ K₁))
    exact ⟨x, x.2, fun h => hx (Subtype.ext h)⟩
  have he₁2 : e₁ * e₁ = 1 := by
    have h1 : orderOf e₁ ∣ 2 := hcard₁ ▸ Subgroup.orderOf_dvd_natCard _ he₁
    rw [← pow_two]
    exact orderOf_dvd_iff_pow_eq_one.mp h1
  have hconjS : ∀ g ∈ S, g⁻¹ * e₁ * g ∈ S := fun g hg =>
    mul_mem (mul_mem (inv_mem hg) (mem_inf.mp he₁).1) hg
  have hconjK : ∀ g : G, g⁻¹ * e₁ * g ∈ conjugate K₁ g := by
    intro g
    rw [mem_conjugate_iff, show g * (g⁻¹ * e₁ * g) * g⁻¹ = e₁ by group]
    exact (mem_inf.mp he₁).2
  have hinv : ∀ g : G, g⁻¹ * e₁ * g * (g⁻¹ * e₁ * g) = 1 := by
    intro g
    rw [show g⁻¹ * e₁ * g * (g⁻¹ * e₁ * g) = g⁻¹ * (e₁ * e₁) * g by group, he₁2]
    group
  have hne1 : ∀ g : G, g⁻¹ * e₁ * g ≠ 1 := fun g h => he₁1 (by
    calc e₁ = g * (g⁻¹ * e₁ * g) * g⁻¹ := by group
      _ = 1 := by rw [h]; group)
  have hcomm : ∀ g ∈ S, ∀ g' ∈ S, g⁻¹ * e₁ * g * (g'⁻¹ * e₁ * g') =
      g'⁻¹ * e₁ * g' * (g⁻¹ * e₁ * g) := by
    intro g hg g' hg'
    by_cases hKK : conjugate K₁ g = conjugate K₁ g'
    · have hc := card_inf_component hS hU hheld hSol hGW hMax hset hu huc (hcomp g' hg').1
        (hcomp g' hg').2.1 (hcomp g' hg').2.2 (hall _ (hcomp g' hg').1 (hcomp g' hg').2.1
          (hcomp g' hg').2.2)
      have h1 : g⁻¹ * e₁ * g ∈ S ⊓ conjugate K₁ g' :=
        mem_inf.mpr ⟨hconjS g hg, hKK ▸ hconjK g⟩
      have h2 : g'⁻¹ * e₁ * g' ∈ S ⊓ conjugate K₁ g' := mem_inf.mpr ⟨hconjS g' hg', hconjK g'⟩
      rw [eq_of_card_two hc h1 h2 (hne1 g) (hne1 g')]
    · exact commute_of_ne (hcomp g hg).1 (hcomp g' hg').1 (hcomp g hg).2.1 (hcomp g' hg').2.1
        hKK hS2 (hconjS g hg) (hconjK g) (hconjS g' hg') (hconjK g')
  have hout : ∀ g ∈ S, g⁻¹ * e₁ * g ∉ coreActionKernel (conjugate K₁ g) := by
    intro g hg hK
    have h1 := odd_orderOf_inner_l2 (hall _ (hcomp g hg).1 (hcomp g hg).2.1 (hcomp g hg).2.2)
      (hconjK g) hK
    rw [orderOf_eq_prime (by rw [pow_two]; exact hinv g) (hne1 g)] at h1
    exact absurd h1 (by decide)
  have hT₁ : GSUnbalancingTriple u t K₁ :=
    gsUnbalancingTriple_of_not_le hSol hto hu2 htu hK₁u hK₁p hYD hK₁n
  have houter := AutL2.l2UnbalancingOuter G u t K₁ hT₁ (hall K₁ hK₁u hK₁p hK₁n)
  have hCN : S ≤ normalizer ((coreActionKernel L : Subgroup G) : Set G) := fun g hg =>
    normalizer_le_normalizer_coreActionKernel L (hSyl.1 hg)
  have hQN : S ≤ normalizer (Q : Set G) := fun g hg => mem_normalizer_inf' (le_normalizer hg)
    (hCN hg)
  have hperfL : ⁅L, L⁆ = L := GSThmB.commutator_eq_self_of_isPComponent hLt hLpt
  have hexp : ∀ x ∈ S ⊓ zStarIn L, x * x = 1 := by
    intro x hx
    by_cases hZ : S ⊓ coreActionKernel L ⊓ L = ⊥
    · have : x ∈ S ⊓ coreActionKernel L ⊓ L := mem_inf.mpr ⟨mem_inf.mpr ⟨(mem_inf.mp hx).1,
        zStarIn_le_coreActionKernel L (mem_inf.mp hx).2⟩, map_subtype_le _ (mem_inf.mp hx).2⟩
      rw [hZ, mem_bot] at this
      rw [this, one_mul]
    · exact ((h58 G L t S T hset).2 hZ).2 x (mem_inf.mpr ⟨mem_inf.mpr ⟨(mem_inf.mp hx).1,
        zStarIn_le_coreActionKernel L (mem_inf.mp hx).2⟩, map_subtype_le _ (mem_inf.mp hx).2⟩)
  by_cases h3 : ∃ s' ∈ S, conjugate K₁ s' ≠ K₁ ∧ conjugate K₁ s' ≠ conjugate K₁ s
  swap
  · push Not at h3
    have horb : ∀ s' ∈ S, conjugate K₁ s' = K₁ ∨ conjugate K₁ s' = conjugate K₁ s := by
      intro s' hs'
      by_cases h : conjugate K₁ s' = K₁
      · exact Or.inl h
      · exact Or.inr (h3 s' hs' h)
    have hidx := card_le_two_of_two_conj hs horb
    have hcen : ∀ n ∈ S ⊓ normalizer (K₁ : Set G), n⁻¹ * e₁⁻¹ * n * e₁ ∈ coreActionKernel L := by
      intro n hn
      obtain ⟨hnS, hnN⟩ := mem_inf.mp hn
      have h1 : n * e₁ * n⁻¹ ∈ S ⊓ K₁ := mem_inf.mpr ⟨mul_mem (mul_mem hnS (mem_inf.mp he₁).1)
        (inv_mem hnS), (mem_normalizer_iff.mp hnN e₁).mp (mem_inf.mp he₁).2⟩
      have h2 : n * e₁ * n⁻¹ ≠ 1 := fun h => he₁1 (by
        calc e₁ = n⁻¹ * (n * e₁ * n⁻¹) * n := by group
          _ = 1 := by rw [h]; group)
      have h3' := eq_of_card_two hcard₁ h1 he₁ h2 he₁1
      have h4 : n⁻¹ * e₁⁻¹ * n * e₁ = 1 := by
        calc n⁻¹ * e₁⁻¹ * n * e₁ = n⁻¹ * e₁⁻¹ * (n * e₁ * n⁻¹) * n := by group
          _ = 1 := by rw [h3']; group
      rw [h4]
      exact one_mem _
    have hZQ := (hSC G L S hperfL htypeL hSyl hexp).1 e₁ (mem_inf.mp he₁).1 _ inf_le_left hidx
      hcen
    have hnQ : e₁ ∉ coreActionKernel L := by
      intro he₁C
      have hYodd : Odd (Nat.card ↥(oddIn L ⊓ C)) := by
        have h1 : Odd (Nat.card (oddIn L)) := by
          rw [oddIn, card_map_of_injective (subtype_injective _)]
          exact Nat.coprime_two_left.mp pPrimeCore_coprime_card
        exact Odd.of_dvd_nat h1 (Subgroup.card_dvd_of_le inf_le_left)
      have hinX : ∀ (g : G), g ∈ S → g⁻¹ * e₁ * g ∈ coreActionKernel L →
          oddIn L ⊓ C ≤ conjugate K₁ g := by
        intro g hg hgC
        have hgQ : g⁻¹ * e₁ * g ∈ S ⊓ coreActionKernel L := mem_inf.mpr ⟨hconjS g hg, hgC⟩
        have hgt : g⁻¹ * e₁ * g ≠ t := by
          intro h
          apply houter t _ (by rw [inv_mul_cancel]; exact one_mem _)
          have h1 : e₁ = g * t * g⁻¹ := by rw [← h]; group
          have h2 : g * t * g⁻¹ = t := by rw [hZS g hg]; group
          rw [← h2, ← h1]
          exact (mem_inf.mp he₁).2
        have hgo : orderOf (g⁻¹ * e₁ * g) = 2 :=
          orderOf_eq_prime (by rw [pow_two]; exact hinv g) (hne1 g)
        have hinv' := conj_eq_inv_of_setting hS hU hheld hSol hGW hMax hL34 hset hgQ hgo hgt
        obtain ⟨hDN, -⟩ := (solomon_involutions hSol hto hu2 htu).2 _ (hcomp g hg).1
          (hcomp g hg).2.1
        exact le_of_conj_eq_inv (hconjK g) (fun d hd => hDN (hYD hd))
          (fun d hd => hinv' d (mem_inf.mp hd).1) hYodd
      have hX₁ : oddIn L ⊓ C ≤ K₁ := by
        have := hinX 1 (one_mem _) (by simpa using he₁C)
        rwa [conjugate_one] at this
      have hX₂ : oddIn L ⊓ C ≤ conjugate K₁ s := hinX s hs (by
        have h1 := conj_mem_coreActionKernel (hSyl.1 (inv_mem hs)) he₁C
        rwa [inv_inv] at h1)
      apply hK₁n
      have h1 := commutator_le_inf_oddIn hK₁u (hcomp s hs).1 hK₁p (hcomp s hs).2.1 hsK.symm
      exact (commutator_mono le_rfl hX₂).trans (h1.trans inf_le_left)
    exact hPair G L t S T hset u hu huc hmax hall K₁ hK₁u hK₁p hK₁n s hs hsK horb e₁ he₁
      (orderOf_eq_prime (by rw [pow_two]; exact he₁2) he₁1) hcard₁ hnQ hZQ
  obtain ⟨s₃, hs₃, h3a, h3b⟩ := h3
  obtain ⟨s₄, hs₄, h4a, h4b, h4c⟩ := exists_fourth_conjugate hS2 hs hs₃ hsK h3a h3b
  refine hCenter G L t S T hset u hu huc hmax hall K₁ hK₁u hK₁p hK₁n s hs s₃ hs₃ s₄ hs₄ hsK h3a
    h4a h3b h4b h4c e₁ he₁ (orderOf_eq_prime (by rw [pow_two]; exact he₁2) he₁1) ?_
  have hs1 : (1 : G) ∈ S := one_mem _
  have hc1 : conjugate K₁ 1 = K₁ := conjugate_one K₁
  have he1' : (1 : G)⁻¹ * e₁ * 1 = e₁ := by group
  obtain ⟨hE, hE16, hWK⟩ := card_four (C := C) hS2 hK₁u (hcomp s hs).1 (hcomp s₃ hs₃).1
    (hcomp s₄ hs₄).1 hK₁p (hcomp s hs).2.1 (hcomp s₃ hs₃).2.1 (hcomp s₄ hs₄).2.1 hsK.symm
    h3a.symm h4a.symm h3b.symm h4b.symm h4c.symm (mem_inf.mp he₁).1 (hconjS s hs)
    (hconjS s₃ hs₃) (hconjS s₄ hs₄) (mem_inf.mp he₁).2 (hconjK s) (hconjK s₃) (hconjK s₄) he₁2
    (hinv s) (hinv s₃) (hinv s₄) (by simpa [he1', hc1] using hout 1 hs1) (hout s hs)
    (hout s₃ hs₃) (hout s₄ hs₄)
  set W := zpowers (s₄⁻¹ * e₁ * s₄) ⊔ (zpowers (s₃⁻¹ * e₁ * s₃) ⊔ zpowers (s⁻¹ * e₁ * s))
    with hW
  set E₄ := zpowers e₁ ⊔ W with hE₄
  have htE : t ∉ E₄ := by
    intro htE
    have hc : ∀ y ∈ W, e₁ * y = y * e₁ := by
      intro y hy
      exact hE.1 e₁ (mem_sup_left (mem_zpowers e₁)) y (mem_sup_right hy)
    obtain ⟨i, w, hw, htw⟩ := mem_zpowers_sup hc htE
    apply houter (e₁ ^ i) (zpow_mem (mem_inf.mp he₁).2 i)
    rw [htw, ← mul_assoc, inv_mul_cancel, one_mul]
    exact hWK hw
  obtain ⟨z, hz, hzt, hΩ, -, -⟩ := h59 G L t S T hset
  have hz2 : z * z = 1 := by rw [← pow_two, ← hz, pow_orderOf_eq_one]
  have hzS : z ∈ S := by
    have : z ∈ omegaOne Q := by rw [hΩ]; exact mem_sup_right (mem_zpowers z)
    exact (mem_inf.mp (omegaOne_le _ this)).1
  have htz : t * z = z * t := (hZS z hzS).symm
  have hEQ : Nat.card ↥(E₄ ⊓ Q) ≤ 2 := by
    have hmem : ∀ x ∈ E₄ ⊓ Q, x = 1 ∨ x = z ∨ x = t * z := by
      intro x hx
      have hxΩ : x ∈ omegaOne Q := subset_closure ⟨(mem_inf.mp hx).2, hE.2 x (mem_inf.mp hx).1⟩
      rw [hΩ] at hxΩ
      rcases mem_four_of_mem_sup ht2 hz2 htz hxΩ with h | h | h | h
      · exact Or.inl h
      · exact absurd (h ▸ (mem_inf.mp hx).1) htE
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)
    have hc2 : ∀ y : G, y * y = 1 → Nat.card (zpowers y) ≤ 2 := fun y hy => by
      rw [Nat.card_zpowers]
      exact Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hy))
    by_cases htzE : t * z ∈ E₄ ⊓ Q
    · have hle : E₄ ⊓ Q ≤ zpowers (t * z) := by
        intro x hx
        rcases hmem x hx with h | h | h
        · rw [h]; exact one_mem _
        · exfalso
          apply htE
          have h1 := mul_mem (mem_inf.mp htzE).1 (mem_inf.mp (h ▸ hx)).1
          rwa [mul_assoc, hz2, mul_one] at h1
        · rw [h]; exact mem_zpowers _
      exact (Subgroup.card_le_of_le hle).trans (hc2 _ (by
        calc t * z * (t * z) = t * (z * t) * z := by group
          _ = t * (t * z) * z := by rw [htz]
          _ = (t * t) * (z * z) := by group
          _ = 1 := by rw [ht2, hz2, one_mul]))
    · have hle : E₄ ⊓ Q ≤ zpowers z := by
        intro x hx
        rcases hmem x hx with h | h | h
        · rw [h]; exact one_mem _
        · rw [h]; exact mem_zpowers _
        · exact absurd (h ▸ hx) htzE
      exact (Subgroup.card_le_of_le hle).trans (hc2 z hz2)
  set E := closure (conjSet S e₁) with hEdef
  have hEel : IsElemTwo E := isElemTwo_closure (fun x hx => by
      obtain ⟨g, -, rfl⟩ := hx
      exact hinv g)
    fun x hx y hy => by
      obtain ⟨g, hg, rfl⟩ := hx
      obtain ⟨g', hg', rfl⟩ := hy
      exact hcomm g hg g' hg'
  have hES : E ≤ S := (closure_le _).mpr fun x hx => by
    obtain ⟨g, hg, rfl⟩ := hx
    exact hconjS g hg
  have hSE : S ≤ normalizer (E : Set G) := le_normalizer_closure_conjSet S e₁
  have hE₄E : E₄ ≤ E := by
    have hgen : ∀ g ∈ S, g⁻¹ * e₁ * g ∈ E := fun g hg => subset_closure ⟨g, hg, rfl⟩
    refine sup_le (zpowers_le.mpr (by simpa using hgen 1 hs1))
      (sup_le (zpowers_le.mpr (hgen s₄ hs₄))
        (sup_le (zpowers_le.mpr (hgen s₃ hs₃)) (zpowers_le.mpr (hgen s hs))))
  have hEQS : E ⊔ Q ≤ S := sup_le hES inf_le_left
  have hcard : 8 * Nat.card Q ≤ Nat.card ↥(E ⊔ Q) := by
    have h1 := card_le_of_inf_le_two hE16 hEQ (fun g hg => hQN (hES (hE₄E hg)))
    exact h1.trans (Subgroup.card_le_of_le (sup_le_sup_right hE₄E Q))
  have hZle := (hSC G L S hperfL htypeL hSyl hexp).2 (E ⊔ Q) le_sup_right hEQS
    (fun g hg => mem_normalizer_sup (hSE hg) (hQN hg)) (comm_sq_mem_of_le_sup hEel inf_le_right
      (fun g hg => hCN (hES hg)) (fun g hg => hQN (hES hg))) hcard
  exact hZle

end CFSG.ComponentClassification.HSFLit.L34Uniq
