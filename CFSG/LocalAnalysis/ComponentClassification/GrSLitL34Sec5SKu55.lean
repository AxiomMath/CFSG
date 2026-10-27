module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5Lemma55
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5SKuDefs

public section

namespace CFSG.ComponentClassification.GrSLit.GrS5

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ComponentClassification.UnbalancedGS
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

theorem normalizer_of_setting_ku
    (hS : SchreierFor Blueprint.Catalog)
    (hU : CatalogueU.CatalogAlmostSimpleUnbalancedOutcome) (hheld : KProperRelativeB.HeldInput)
    (hSol : SolomonCommutingCoreInput) (hGW : GorensteinWalterConnectedInput)
    (hMax : MaximalTwoComponentInput) (hL34 : L34InvolutionCentralizerFact)
    (hKu : GrS5S.L34Sec5KuOddStep)
    {L : Subgroup G} {t : G} {S T : Subgroup G} (hset : L34Sec5Setting G L t S T) {u : G}
    (hu : u ∈ L34UnbalancingSet L t S) {K₁ : Subgroup G} (hK₁K : K₁ ≤ l34K L u)
    (hK₁ : IsPComponent 2 (K₁.subgroupOf (l34K L u))) :
    omegaOne (S ⊓ coreActionKernel L) ≤ normalizer (K₁ : Set G) ∧
      S ⊓ coreActionKernel L ⊓ coreActionKernel K₁ = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hset' := hset
  obtain ⟨-, hLt, hLpt⟩ := eq_of_mem_inf_centralizer hS hU hheld hSol hGW hset
  have hZS := mem_center_of_setting hS hU hheld hSol hGW hset
  have h54 := l34Notation54_of_inputs hS hU hheld hSol hGW hMax G L t S T hset u hu
  obtain ⟨-, h54b, -, -⟩ := h54
  obtain ⟨hK₁C, hK₁p, -⟩ := h54b K₁ hK₁K hK₁
  have hXK : ¬ oddIn L ⊓ K₁ ≤ oddIn K₁ := hKu G L t S T hset u hu K₁ hK₁K hK₁
  obtain ⟨-, hfam, -, hSyl, htS, -, -⟩ := hset
  obtain ⟨⟨-, -, -, -, -, hto, -, -⟩, -, -, -, -⟩ := hfam
  obtain ⟨huU, huo, -⟩ := hu
  have huS : u ∈ S := (sup_le inf_le_left (zpowers_le.mpr htS)) huU
  have htu : t * u = u * t := (hZS u huS).symm
  have ht2 : t * t = 1 := by rw [← pow_two, ← hto, pow_orderOf_eq_one]
  have htL : t ∈ centralizer (L : Set G) := mem_centralizer_iff.mpr fun l hl =>
    mem_centralizer_singleton_iff.mp (hLt hl)
  have htK : t ∈ coreActionKernel L := mem_coreActionKernel_of_commute fun l hl =>
    ((mem_centralizer_iff.mp htL) l hl).symm
  set C := centralizer ({u} : Set G) with hC
  set Y := oddIn L ⊓ C with hY
  have hYD : Y ≤ oddIn (centralizer ({t} : Set G)) ⊓ C :=
    inf_le_inf_right C (GSLit.map_pPrimeCore_le_of_isPComponent hLt hLpt)
  have hgen := not_commutator_le_of_le_l34K hK₁K hK₁C hK₁p
  obtain ⟨-, h2⟩ := solomon_involutions hSol hto huo htu
  obtain ⟨-, hnot⟩ := h2 K₁ hK₁C hK₁p
  obtain ⟨htN, -, htK₁⟩ := hnot fun h => hgen ((commutator_mono le_rfl hYD).trans h)
  obtain ⟨x, hxXK, hxO⟩ : ∃ x ∈ oddIn L ⊓ K₁, x ∉ oddIn K₁ := by
    by_contra hall
    push Not at hall
    exact hXK fun y hy => hall y hy
  obtain ⟨hxX, hxK₁⟩ := mem_inf.mp hxXK
  have hoddL : Odd (Nat.card (oddIn L)) := by
    rw [oddIn, card_map_of_injective (subtype_injective _)]
    exact Nat.coprime_two_left.mp pPrimeCore_coprime_card
  have hxo : Odd (orderOf x) := hoddL.of_dvd_nat (Subgroup.orderOf_dvd_natCard _ hxX)
  have hinv : ∀ w ∈ S ⊓ coreActionKernel L, orderOf w = 2 → w ≠ t →
      ∀ y ∈ oddIn L, w * y * w⁻¹ = y⁻¹ := fun w hwQ hw hwt =>
    conj_eq_inv_of_setting hS hU hheld hSol hGW hMax hL34 hset' hwQ hw hwt
  refine ⟨closure_le _ |>.mpr fun w ⟨hwQ, hw2⟩ => ?_, ?_⟩
  ·
    by_cases hw1 : w = 1
    · rw [hw1]
      exact one_mem _
    by_cases hwt : w = t
    · rw [hwt]
      exact htN
    have hwo : orderOf w = 2 := orderOf_eq_prime (by rw [pow_two, hw2]) hw1
    have hwu : w * u = u * w := commute_of_mem_unbalancingSet hS hU hheld hSol hGW hset' hwQ huU
    have hwC : w ∈ C := mem_centralizer_singleton_iff.mpr hwu
    obtain ⟨hK₁wC, hK₁wp⟩ := GSThmB.isPComponent_conjugate_centralizer_singleton hK₁C hK₁p hwC
    by_contra hwN
    have hne : K₁ ≠ conjugate K₁ w := fun h => hwN (mem_normalizer_of_conjugate_eq h.symm)
    have hwinv : w⁻¹ = w := inv_eq_of_mul_eq_one_right hw2
    have hxw : x⁻¹ ∈ K₁ ⊓ conjugate K₁ w := by
      refine mem_inf.mpr ⟨inv_mem hxK₁, ⟨x, hxK₁, ?_⟩⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
      have := hinv w hwQ hwo hwt x hxX
      rw [hwinv] at this ⊢
      exact this
    have h1 := inf_le_zStarIn_of_ne hK₁C hK₁wC hK₁p hK₁wp hne hxw
    have h2 := mem_oddIn_of_mem_zStarIn h1 (by rw [orderOf_inv]; exact hxo)
    exact hxO (by simpa using inv_mem h2)
  ·
    by_contra hne
    set P₀ := S ⊓ coreActionKernel L ⊓ coreActionKernel K₁ with hP₀
    have hP₀p : IsPGroup 2 P₀ := (IsSylowTwoIn.isPGroup hSyl).to_le (inf_le_left.trans inf_le_left)
    have hnt : Nontrivial P₀ := (Subgroup.nontrivial_iff_ne_bot P₀).mpr hne
    have h2 : 2 ∣ Nat.card P₀ := by
      obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := 2) (G := ↥P₀)).mp hP₀p
      rcases n with _ | n
      · rw [pow_zero] at hn
        exact absurd (Finite.one_lt_card_iff_nontrivial.mpr hnt) (by rw [hn]; omega)
      · rw [hn, pow_succ]
        exact dvd_mul_left 2 _
    obtain ⟨w', hw'⟩ := exists_prime_orderOf_dvd_card' (G := ↥P₀) 2 h2
    set w : G := (w' : G) with hw
    have hwo : orderOf w = 2 := by rw [hw, Subgroup.orderOf_coe, hw']
    have hwP : w ∈ P₀ := w'.2
    obtain ⟨hwQ, hwK₁⟩ := mem_inf.mp hwP
    by_cases hwt : w = t
    ·
      apply hxO
      have htK₁' : t ∈ coreActionKernel K₁ := hwt ▸ hwK₁
      have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
      have hle : ⁅K₁, zpowers t⁆ ≤ oddIn K₁ := by
        rw [commutator_le]
        intro k hk s hs
        rcases eq_one_or_eq_of_mem_zpowers' ht2 hs with h | h
        · rw [h, commutatorElement_one_right]
          exact one_mem _
        · have h1 := (mem_coreActionKernel.mp htK₁').2 k⁻¹ (inv_mem hk)
          rw [inv_inv, htinv] at h1
          rw [h, commutatorElement_def, htinv]
          exact h1
      exact ((le_of_eq htK₁.symm).trans (sup_le le_rfl hle)) hxK₁
    ·
      apply hxO
      have h1 := conj_mem_oddIn_of_mem_coreActionKernel hwK₁ x hxK₁
      rw [hinv w hwQ hwo hwt x hxX] at h1
      have h3 : x * x ∈ oddIn K₁ := by
        have := inv_mem h1
        rwa [mul_inv_rev, inv_inv] at this
      exact mem_of_mul_self_mem_of_odd hxo h3

theorem isElemTwo_omegaOne_of_setting_ku
    (hS : SchreierFor Blueprint.Catalog)
    (hU : CatalogueU.CatalogAlmostSimpleUnbalancedOutcome) (hheld : KProperRelativeB.HeldInput)
    (hSol : SolomonCommutingCoreInput) (hGW : GorensteinWalterConnectedInput)
    (hMax : MaximalTwoComponentInput) (hL34 : L34InvolutionCentralizerFact)
    (hKu : GrS5S.L34Sec5KuOddStep)
    (hFour : L34UnbalancingFourFact)
    {L : Subgroup G} {t : G} {S T : Subgroup G} (hset : L34Sec5Setting G L t S T) :
    IsElemTwo (omegaOne (S ⊓ coreActionKernel L)) ∧
      Nat.card ↥(omegaOne (S ⊓ coreActionKernel L)) ≤ 4 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hset' := hset
  obtain ⟨-, hLt, hLpt⟩ := eq_of_mem_inf_centralizer hS hU hheld hSol hGW hset
  have hZS := mem_center_of_setting hS hU hheld hSol hGW hset
  have hQr := (l34Sec5Basics_of_inputs hS hU hheld hSol hGW G L t S T hset).1
  obtain ⟨u, hu⟩ := l34UnbalancingSetNonempty_of_inputs hS hU hheld hSol hGW G L t S T hset
  obtain ⟨hbase, hfam, -, hSyl, htS, -, -⟩ := hset
  obtain ⟨-, -, -, -, -, -, -, hUtypes⟩ := hbase
  obtain ⟨⟨-, -, -, -, -, hto, -, -⟩, -, -, -, -⟩ := hfam
  have hu' := hu
  obtain ⟨huU, huo, huX⟩ := hu'
  have huS : u ∈ S := (sup_le inf_le_left (zpowers_le.mpr htS)) huU
  have htu : t * u = u * t := (hZS u huS).symm
  have ht2 : t * t = 1 := by rw [← pow_two, ← hto, pow_orderOf_eq_one]
  have htL : t ∈ centralizer (L : Set G) := mem_centralizer_iff.mpr fun l hl =>
    mem_centralizer_singleton_iff.mp (hLt hl)
  have htK : t ∈ coreActionKernel L := mem_coreActionKernel_of_commute fun l hl =>
    ((mem_centralizer_iff.mp htL) l hl).symm
  set C := centralizer ({u} : Set G) with hC
  set Y := oddIn L ⊓ C with hY
  have hYD : Y ≤ oddIn (centralizer ({t} : Set G)) ⊓ C :=
    inf_le_inf_right C (GSLit.map_pPrimeCore_le_of_isPComponent hLt hLpt)
  obtain ⟨K₁, hK₁C, hK₁p, hK₁Y⟩ := exists_isPComponent_not_le hSol hto huo htu hYD huX
  have hK₁K : K₁ ≤ l34K L u := le_l34K hK₁C hK₁p hK₁Y
  have hK₁' : IsPComponent 2 (K₁.subgroupOf (l34K L u)) := by
    have h1 := CatalogueBPrimeJoin.pComponent_restrict_overgroup 2 hK₁p
      (show K₁.subgroupOf C ≤ (l34K L u).subgroupOf C from fun x hx => hK₁K hx)
    exact (LieType.AlgebraicGroups.isPComponent_subgroupOf_subgroupOf_iff
      (l34K_le_centralizer L u) 2 Nat.prime_two).mp h1
  have hU₁ : GSUnbalancingTriple u t K₁ :=
    gsUnbalancingTriple_of_not_le hSol hto huo htu hK₁C hK₁p hYD hK₁Y
  obtain ⟨hFN, hF0⟩ := normalizer_of_setting_ku hS hU hheld hSol hGW hMax hL34 hKu hset' hu
    hK₁K hK₁'
  set Q := S ⊓ coreActionKernel L with hQ
  have hFQ : omegaOne Q ≤ Q := omegaOne_le Q
  have hSp : IsPGroup 2 S := IsSylowTwoIn.isPGroup hSyl
  refine hFour G u t K₁ (omegaOne Q) hU₁ (hUtypes u t K₁ hU₁) (le_inf hFN ?_)
    (hSp.to_le (hFQ.trans inf_le_left)) (subset_closure ⟨mem_inf.mpr ⟨htS, htK⟩, ht2⟩)
    (omegaOne_omegaOne Q).symm ?_ ((pRank_le_of_le hFQ).trans hQr)
  · intro x hx
    exact mem_centralizer_singleton_iff.mpr (hZS x ((hFQ.trans inf_le_left) hx))
  · apply le_bot_iff.mp
    rw [← hF0]
    exact inf_le_inf_right _ hFQ

end CFSG.ComponentClassification.GrSLit.GrS5
