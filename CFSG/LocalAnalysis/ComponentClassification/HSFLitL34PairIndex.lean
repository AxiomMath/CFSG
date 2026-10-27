module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5Tools510
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5Lemma55
public import CFSG.LocalAnalysis.ComponentClassification.HSFLitAutL2Outer

public section

namespace CFSG.ComponentClassification.HSFLit.L34Uniq

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ComponentClassification.UnbalancedGS
  CFSG.ComponentClassification.GrSLit CFSG.ComponentClassification.GrSLit.GrS5
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem mul_mem_iff_of_relIndex_le_two {H N : Subgroup G} (h : H.relIndex N ≤ 2) {x y : G}
    (hx : x ∈ N) (hy : y ∈ N) : x * y ∈ H ↔ (x ∈ H ↔ y ∈ H) := by
  have hpos : H.relIndex N ≠ 0 := by
    intro h0
    have h1 := relIndex_mul_card H N
    rw [h0, zero_mul] at h1
    exact Nat.card_pos.ne' h1.symm
  rcases (show H.relIndex N = 1 ∨ H.relIndex N = 2 by omega) with h1 | h2
  · have hle := relIndex_eq_one.mp h1
    exact ⟨fun _ => ⟨fun _ => hle hy, fun _ => hle hx⟩, fun _ => hle (mul_mem hx hy)⟩
  · have := mul_mem_iff_of_index_two (H := H.subgroupOf N) h2 (a := ⟨x, hx⟩) (b := ⟨y, hy⟩)
    simpa [mem_subgroupOf] using this

theorem relIndex_sup_le_two {N C : Subgroup G} {t : G} (htN : t ∈ N) (htC : t ∉ C)
    (h4 : Nat.card N ≤ 4 * Nat.card ↥(N ⊓ C)) : (zpowers t ⊔ N ⊓ C).relIndex N ≤ 2 := by
  have hAB : N ⊓ C ≤ zpowers t ⊔ N ⊓ C := le_sup_right
  have hBN : zpowers t ⊔ N ⊓ C ≤ N := sup_le (zpowers_le.mpr htN) inf_le_left
  have hAN : (N ⊓ C).relIndex N ≤ 4 := by
    have h1 := relIndex_mul_card (N ⊓ C) N
    rw [inf_eq_left.mpr inf_le_left] at h1
    have hpos : 0 < Nat.card ↥(N ⊓ C) := Nat.card_pos
    nlinarith
  have hmul := relIndex_mul_relIndex (N ⊓ C) (zpowers t ⊔ N ⊓ C) N hAB hBN
  have hAB2 : 2 ≤ (N ⊓ C).relIndex (zpowers t ⊔ N ⊓ C) := by
    have hne1 : (N ⊓ C).relIndex (zpowers t ⊔ N ⊓ C) ≠ 1 := fun h1 =>
      htC (mem_inf.mp (relIndex_eq_one.mp h1 (mem_sup_left (mem_zpowers t)))).2
    have hne0 : (N ⊓ C).relIndex (zpowers t ⊔ N ⊓ C) ≠ 0 := by
      intro h0
      have h1 := relIndex_mul_card (N ⊓ C) (zpowers t ⊔ N ⊓ C)
      rw [h0, zero_mul] at h1
      exact Nat.card_pos.ne' h1.symm
    omega
  nlinarith

omit [Finite G] in
theorem mem_zpowers_sup_inf_iff {N C : Subgroup G} {t : G} (htN : t ∈ N) (ht2 : t * t = 1)
    (htc : ∀ n ∈ N, n * t = t * n) {x : G} (hx : x ∈ N) :
    x ∈ zpowers t ⊔ N ⊓ C ↔ x ∈ C ∨ x * t ∈ C := by
  constructor
  · intro h
    obtain ⟨i, w, hw, rfl⟩ := mem_zpowers_sup (fun y hy => (htc y (mem_inf.mp hy).1).symm) h
    have hti : t ^ i = 1 ∨ t ^ i = t := by
      obtain ⟨k, rfl | rfl⟩ := Int.even_or_odd' i
      · left
        rw [zpow_mul, zpow_two, ht2, one_zpow]
      · right
        rw [zpow_add, zpow_mul, zpow_two, ht2, one_zpow, one_mul, zpow_one]
    rcases hti with h1 | h1
    · rw [h1, one_mul]
      exact Or.inl (mem_inf.mp hw).2
    · right
      rw [h1, mul_assoc, htc w (mem_inf.mp hw).1, ← mul_assoc, ht2, one_mul]
      exact (mem_inf.mp hw).2
  · rintro (h | h)
    · exact mem_sup_right (mem_inf.mpr ⟨hx, h⟩)
    · have h1 : x = t * (x * t) := by
        rw [← mul_assoc, ← htc x hx, mul_assoc, ht2, mul_one]
      rw [h1]
      exact mul_mem (mem_sup_left (mem_zpowers t))
        (mem_sup_right (mem_inf.mpr ⟨mul_mem hx htN, h⟩))

theorem twoClass_mul {N C : Subgroup G} {t : G} (htN : t ∈ N) (ht2 : t * t = 1)
    (htc : ∀ n ∈ N, n * t = t * n) (htC : t ∉ C) (h4 : Nat.card N ≤ 4 * Nat.card ↥(N ⊓ C))
    {x y : G} (hx : x ∈ N) (hy : y ∈ N) :
    (x * y ∈ C ∨ x * y * t ∈ C) ↔ ((x ∈ C ∨ x * t ∈ C) ↔ (y ∈ C ∨ y * t ∈ C)) := by
  rw [← mem_zpowers_sup_inf_iff htN ht2 htc hx, ← mem_zpowers_sup_inf_iff htN ht2 htc hy,
    ← mem_zpowers_sup_inf_iff htN ht2 htc (mul_mem hx hy)]
  exact mul_mem_iff_of_relIndex_le_two (relIndex_sup_le_two htN htC h4) hx hy

omit [Finite G] in
theorem conj_pair {S K₁ : Subgroup G} {s : G} (hs : s ∈ S) (hsK : conjugate K₁ s ≠ K₁)
    (horb : ∀ s' ∈ S, conjugate K₁ s' = K₁ ∨ conjugate K₁ s' = conjugate K₁ s) {g : G}
    (hg : g ∈ S) :
    (conjugate K₁ g = K₁ ∧ conjugate (conjugate K₁ s) g = conjugate K₁ s) ∨
      (conjugate K₁ g = conjugate K₁ s ∧ conjugate (conjugate K₁ s) g = K₁) := by
  have hinj : ∀ A B : Subgroup G, conjugate A g = conjugate B g → A = B := by
    intro A B h
    have h1 := congrArg (fun H => conjugate H g⁻¹) h
    simpa only [conjugate_conjugate'', mul_inv_cancel, conjugate_one] using h1
  have h2 := horb (s * g) (mul_mem hs hg)
  rw [← conjugate_conjugate''] at h2
  rcases horb g hg with h1 | h1
  · exact Or.inl ⟨h1, h2.resolve_left fun h => hsK (hinj _ _ (h.trans h1.symm))⟩
  · exact Or.inr ⟨h1, h2.resolve_right fun h => hsK (hinj _ _ (h.trans h1.symm))⟩

omit [Finite G] in
theorem commutator_le_oddIn_of_le {K Y : Subgroup G} (h : Y ≤ coreActionKernel K) :
    ⁅K, Y⁆ ≤ oddIn K := by
  rw [commutator_le]
  intro k hk y hy
  have h1 := (mem_coreActionKernel.mp (h (inv_mem hy))).2 k⁻¹ (inv_mem hk)
  rw [inv_inv, inv_inv] at h1
  rw [commutatorElement_def]
  exact h1

theorem inf_coreActionKernel_eq_bot
    (hS : SchreierFor Blueprint.Catalog)
    (hU : CatalogueU.CatalogAlmostSimpleUnbalancedOutcome) (hheld : KProperRelativeB.HeldInput)
    (hSol : SolomonCommutingCoreInput) (hGW : GorensteinWalterConnectedInput)
    (hMax : MaximalTwoComponentInput) (hL34 : L34InvolutionCentralizerFact) {L : Subgroup G}
    {t : G} {S T : Subgroup G} (hset : L34Sec5Setting G L t S T) {u : G}
    (hu : u ∈ L34UnbalancingSet L t S) {K : Subgroup G} (hKu : K ≤ centralizer ({u} : Set G))
    (hKp : IsPComponent 2 (K.subgroupOf (centralizer ({u} : Set G))))
    (hKn : ¬ ⁅K, oddIn L ⊓ centralizer ({u} : Set G)⁆ ≤ oddIn K)
    (htype : IsL2Type 5 (K ⧸ pPrimeCore 2 K) ∨ IsL2Type 7 (K ⧸ pPrimeCore 2 K)) :
    S ⊓ coreActionKernel L ⊓ coreActionKernel K = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, hLt, hLpt⟩ := eq_of_mem_inf_centralizer hS hU hheld hSol hGW hset
  have hZS := mem_center_of_setting hS hU hheld hSol hGW hset
  have hset' := hset
  obtain ⟨-, ⟨⟨-, -, -, -, -, hto, -, -⟩, -⟩, -, hSyl, htS, -, -⟩ := hset'
  obtain ⟨huS₀, hu2, -⟩ := hu
  have huS : u ∈ S := (sup_le inf_le_left (zpowers_le.mpr htS) : S ⊓ L ⊔ zpowers t ≤ S) huS₀
  have htu : t * u = u * t := (hZS u huS).symm
  have hYD : oddIn L ⊓ centralizer ({u} : Set G) ≤
      oddIn (centralizer ({t} : Set G)) ⊓ centralizer ({u} : Set G) :=
    inf_le_inf_right _ (GSLit.map_pPrimeCore_le_of_isPComponent hLt hLpt)
  have hT := gsUnbalancingTriple_of_not_le hSol hto hu2 htu hKu hKp hYD hKn
  have htK : t ∉ coreActionKernel K := by
    simpa using AutL2.l2UnbalancingOuter G u t K hT htype 1 (one_mem _)
  have hS2 : IsPGroup 2 S := GrS5.IsSylowTwoIn.isPGroup hSyl
  by_contra hne
  set Q' := S ⊓ coreActionKernel L ⊓ coreActionKernel K with hQ'
  have hQ'2 : IsPGroup 2 Q' := hS2.to_le (inf_le_left.trans inf_le_left)
  obtain ⟨y, hy⟩ : ∃ y : Q', orderOf y = 2 := by
    obtain ⟨n, hn⟩ := hQ'2.exists_card_eq
    rcases n with _ | n
    · exact absurd (card_eq_one.mp (by rw [hn, pow_zero])) hne
    · exact exists_prime_orderOf_dvd_card' 2 (by rw [hn, pow_succ]; exact dvd_mul_left 2 _)
  have hyo : orderOf (y : G) = 2 := by rw [orderOf_coe]; exact hy
  obtain ⟨hySL, hyK⟩ := mem_inf.mp y.2
  obtain ⟨hyS, hyL⟩ := mem_inf.mp hySL
  have hyt : (y : G) ≠ t := fun h => htK (h ▸ hyK)
  have hinv := conj_eq_inv_of_setting hS hU hheld hSol hGW hMax hL34 hset
    (mem_inf.mpr ⟨hyS, hyL⟩) hyo hyt
  obtain ⟨hDN, -⟩ := (solomon_involutions hSol hto hu2 htu).2 K hKu hKp
  have hYodd : Odd (Nat.card ↥(oddIn L ⊓ centralizer ({u} : Set G))) := by
    have h1 : Odd (Nat.card (oddIn L)) := by
      rw [oddIn, card_map_of_injective (subtype_injective _)]
      exact Nat.coprime_two_left.mp pPrimeCore_coprime_card
    exact Odd.of_dvd_nat h1 (Subgroup.card_dvd_of_le inf_le_left)
  have hle := le_of_conj_eq_inv hyK
    (fun d hd => normalizer_le_normalizer_coreActionKernel K (hDN (hYD hd)))
    (fun d hd => hinv d (mem_inf.mp hd).1) hYodd
  exact hKn (commutator_le_oddIn_of_le hle)

end CFSG.ComponentClassification.HSFLit.L34Uniq
