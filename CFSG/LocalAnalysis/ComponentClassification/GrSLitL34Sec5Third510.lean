module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5Tools510
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5InputsCov
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5InputsRank
public import CFSG.SignalizerFunctorTheorem.McBride.Prelim.Generation
public import CFSG.GroupTheory.QuasisimpleCommutingProductBound
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5Lemma551
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5Sylow

public section

namespace CFSG.ComponentClassification.GrSLit.GrS5

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ComponentClassification.UnbalancedGS
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem centralizer_normalized_of_mem_normalizer {X : Subgroup G} {g : G}
    (hg : g ∈ normalizer (X : Set G)) :
    g ∈ normalizer (centralizer (X : Set G) : Set G) := by
  have key : ∀ g ∈ normalizer (X : Set G), ∀ h ∈ centralizer (X : Set G),
      g * h * g⁻¹ ∈ centralizer (X : Set G) := by
    intro g hg h hh
    rw [mem_centralizer_iff]
    intro x hx
    have hx' : g⁻¹ * x * g ∈ X := by
      have := (mem_normalizer_iff.mp (inv_mem hg) x).mp hx
      rwa [inv_inv] at this
    have h1 := mem_centralizer_iff.mp hh _ hx'
    calc x * (g * h * g⁻¹) = g * ((g⁻¹ * x * g) * h) * g⁻¹ := by group
      _ = g * (h * (g⁻¹ * x * g)) * g⁻¹ := by rw [h1]
      _ = g * h * g⁻¹ * x := by group
  rw [mem_normalizer_iff]
  intro h
  refine ⟨key g hg h, fun hh => ?_⟩
  have h1 := key g⁻¹ (inv_mem hg) _ hh
  rwa [show g⁻¹ * (g * h * g⁻¹) * g⁻¹⁻¹ = h by group] at h1

omit [Finite G] in
theorem commute_zpow_mul_iff {x t a : G} (hxt : x * t = t * x) (i : ℤ) :
    x * (t ^ i * a) = t ^ i * a * x ↔ x * a = a * x := by
  have hc : Commute x t := hxt
  have hci : Commute x (t ^ i) := hc.zpow_right i
  constructor
  · intro h
    have h1 := (hci.inv_right.mul_right (show Commute x (t ^ i * a) from h)).eq
    rwa [inv_mul_cancel_left] at h1
  · intro h
    exact (hci.mul_right (show Commute x a from h)).eq

theorem false_of_oddIn_inf_le_component
    (hS : SchreierFor Blueprint.Catalog)
    (hU : CatalogueU.CatalogAlmostSimpleUnbalancedOutcome) (hheld : KProperRelativeB.HeldInput)
    (hSol : SolomonCommutingCoreInput) (hGW : GorensteinWalterConnectedInput)
    (h58 : L34Lemma58) (hERank : L34ElementaryRankFact) (hMaxE : L34MaxElementaryThreeFact)
    {L : Subgroup G} {t : G} {S T : Subgroup G} (hset : L34Sec5Setting G L t S T) {u : G}
    (hmax : ∀ v ∈ L34UnbalancingSet L t S, Nat.card ↥(oddIn L ⊓ centralizer ({v} : Set G)) ≤
      Nat.card ↥(oddIn L ⊓ centralizer ({u} : Set G))) {K₁ : Subgroup G} (hperf₁ : ⁅K₁, K₁⁆ = K₁)
    (hO : ∀ x ∈ oddIn K₁, ∀ k ∈ K₁, x * k = k * x) (htK : t ∉ coreActionKernel K₁)
    (hrk : ∀ E : Subgroup G, E ≤ S → IsElemTwo E →
      Nat.card E ≤ 8 * Nat.card ↥(E ⊓ coreActionKernel K₁))
    (hXK : oddIn L ⊓ centralizer ({u} : Set G) ≤ K₁) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, hLt, hLpt⟩ := eq_of_mem_inf_centralizer hS hU hheld hSol hGW hset
  have hZS := mem_center_of_setting hS hU hheld hSol hGW hset
  have hset' := hset
  obtain ⟨-, ⟨⟨-, -, -, -, -, hto, -, -⟩, htypeL, -, hX, -⟩, -, hSyl, htS, -, -⟩ := hset'
  have hS2 : IsPGroup 2 S := IsSylowTwoIn.isPGroup hSyl
  have ht2 : t * t = 1 := by rw [← pow_two, ← hto, pow_orderOf_eq_one]
  have ht1 : t ≠ 1 := by rintro rfl; simp at hto
  have htKL : t ∈ coreActionKernel L := mem_coreActionKernel_of_commute fun l hl =>
    (mem_centralizer_singleton_iff.mp (hLt hl)).symm
  have hperf : ⁅L, L⁆ = L := GSThmB.commutator_eq_self_of_isPComponent hLt hLpt
  have hS₀ : IsSylowTwoIn (S ⊓ L) L := isSylowTwoIn_inf_of_isSubnormal hSyl le_normalizer
    (Subgroup.Normal.isSubnormal Subgroup.normal_in_normalizer)
  have hXodd : Odd (Nat.card (oddIn L)) := by
    rw [oddIn, card_map_of_injective (subtype_injective _)]
    exact Nat.coprime_two_left.mp pPrimeCore_coprime_card
  have hXt : ∀ x ∈ oddIn L, x * t = t * x := fun x hx =>
    mem_centralizer_singleton_iff.mp (hLt (map_subtype_le _ hx))
  have hZ2 : ∀ y ∈ S ⊓ L ⊓ zStarIn L, y * y = 1 := by
    intro y hy
    obtain ⟨hy1, hyZ⟩ := mem_inf.mp hy
    have hyQL : y ∈ S ⊓ coreActionKernel L ⊓ L := mem_inf.mpr ⟨mem_inf.mpr ⟨(mem_inf.mp hy1).1,
      zStarIn_le_coreActionKernel L hyZ⟩, (mem_inf.mp hy1).2⟩
    by_cases hZ : S ⊓ coreActionKernel L ⊓ L = ⊥
    · rw [hZ, mem_bot] at hyQL
      rw [hyQL, mul_one]
    · exact ((h58 G L t S T hset).2 hZ).2 y hyQL
  obtain ⟨A, hAS₀, hA, hAc⟩ := hERank G L (S ⊓ L) hperf htypeL hS₀ hZ2
  obtain ⟨-, -, -, -, -, A₀, hA₀A, hA₀c, hA₀Z, -, -⟩ :=
    hMaxE G L (S ⊓ L) A hperf htypeL hS₀ hZ2 hAS₀ hA hAc
  have hA₀S₀ : A₀ ≤ S ⊓ L := hA₀A.trans hAS₀
  have hA₀el : IsElemTwo A₀ := hA.mono hA₀A
  have hA₀K : ∀ a ∈ A₀, a ≠ 1 → a ∉ coreActionKernel L := fun a ha ha1 haK => by
    have h1 : a ∈ A₀ ⊓ zStarIn L := mem_inf.mpr ⟨ha, inf_coreActionKernel_le_zStarIn L
      (mem_inf.mpr ⟨(mem_inf.mp (hA₀S₀ ha)).2, haK⟩)⟩
    rw [hA₀Z, mem_bot] at h1
    exact ha1 h1
  have htA₀ : t ∉ A₀ := fun h => hA₀K t h ht1 htKL
  have htcomm : ∀ y ∈ A₀, t * y = y * t := fun y hy => (hZS y (mem_inf.mp (hA₀S₀ hy)).1).symm
  obtain ⟨hEel, hEc⟩ := elemTwo_zpowers_sup ht2 hA₀el htcomm htA₀
  set E := zpowers t ⊔ A₀ with hE
  have hES : E ≤ S := sup_le (zpowers_le.mpr htS) (hA₀S₀.trans inf_le_left)
  set B := E ⊓ coreActionKernel K₁ with hB
  have hB4 : 2 ^ 2 ≤ Nat.card B := by
    have h1 := hrk E hES hEel
    rw [hEc, hA₀c, ← hB] at h1
    norm_num
    omega
  have hBel : IsElemTwo B := hEel.mono inf_le_left
  have hCb : ∀ b ∈ B, b ≠ 1 →
      oddIn L ⊓ centralizer ({b} : Set G) = oddIn L ⊓ centralizer ({u} : Set G) := by
    intro b hb hb1
    have hbE : b ∈ E := (mem_inf.mp hb).1
    have hbK : b ∈ coreActionKernel K₁ := (mem_inf.mp hb).2
    have hbc := commute_of_mem_coreActionKernel_of_central hperf₁ hO hbK
    have hle : oddIn L ⊓ centralizer ({u} : Set G) ≤ oddIn L ⊓ centralizer ({b} : Set G) :=
      fun d hd => mem_inf.mpr ⟨(mem_inf.mp hd).1,
        mem_centralizer_singleton_iff.mpr (hbc d (hXK hd)).symm⟩
    obtain ⟨i, a, haA, hba⟩ := mem_zpowers_sup htcomm hbE
    have ha1 : a ≠ 1 := by
      rintro rfl
      rw [mul_one] at hba
      rcases eq_one_or_eq_of_mem_zpowers' ht2 (hba ▸ zpow_mem (mem_zpowers t) i) with h | h
      · exact hb1 h
      · exact htK (h ▸ hbK)
    have haS₀ := hA₀S₀ haA
    have hao : orderOf a = 2 := orderOf_eq_prime (by rw [pow_two]; exact hA₀el.2 a haA) ha1
    obtain ⟨-, a', ha', ha'n⟩ := l34Lemma53_of_inputs hS hU hheld hSol hGW G L t S T hset a
      (mem_inf.mp haS₀).1 hao (hA₀K a haA ha1) (mem_sup_left (mem_inf.mp haS₀).2)
    have hCa : ∀ j : ℤ, oddIn L ⊓ centralizer ({t ^ j * a} : Set G) =
        oddIn L ⊓ centralizer ({a} : Set G) := fun j => by
      ext x
      simp only [mem_inf, mem_centralizer_singleton_iff]
      exact ⟨fun ⟨h1, h2⟩ => ⟨h1, (commute_zpow_mul_iff (hXt x h1) j).mp h2⟩,
        fun ⟨h1, h2⟩ => ⟨h1, (commute_zpow_mul_iff (hXt x h1) j).mpr h2⟩⟩
    have hat' : a * t = t * a := hZS a (mem_inf.mp haS₀).1
    have hat : a * t = t ^ (1 : ℤ) * a := by
      rw [zpow_one]
      exact hat'
    have ha'U : a' ∈ L34UnbalancingSet L t S := by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha'
      rcases ha' with rfl | rfl
      · exact ⟨mem_sup_left haS₀, hao, ha'n⟩
      · refine ⟨mul_mem (mem_sup_left haS₀) (mem_sup_right (mem_zpowers t)), ?_, ha'n⟩
        refine orderOf_eq_prime ?_ ?_
        · rw [pow_two, show a * t * (a * t) = (a * a) * (t * t) by
            rw [mul_assoc, ← mul_assoc t a t, ← hat']; group,
            hA₀el.2 a haA, ht2, one_mul]
        · intro h
          apply hA₀K a haA ha1
          rw [show a = t⁻¹ by rw [← mul_eq_one_iff_eq_inv.mp h]]
          exact inv_mem htKL
    have hCa' : oddIn L ⊓ centralizer ({a'} : Set G) = oddIn L ⊓ centralizer ({a} : Set G) := by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha'
      rcases ha' with rfl | rfl
      · rfl
      · rw [hat]
        exact hCa 1
    have hcard : Nat.card ↥(oddIn L ⊓ centralizer ({b} : Set G)) ≤
        Nat.card ↥(oddIn L ⊓ centralizer ({u} : Set G)) := by
      rw [hba, hCa i, ← hCa']
      exact hmax a' ha'U
    exact (Subgroup.eq_of_le_of_card_ge hle hcard).symm
  have hBX : B ≤ normalizer (oddIn L : Set G) := fun b hb =>
    normalizer_le_normalizer_oddIn L (hSyl.1 (hES (mem_inf.mp hb).1))
  have hgen := CFSG.SignalizerFunctorTheorem.McBride.iSup_centralizer_nonidentity Nat.prime_two
    hBel.isElemAbelian hB4 hBX (Nat.coprime_two_left.mpr hXodd)
  have hXu : oddIn L ≤ centralizer ({u} : Set G) := by
    rw [← hgen]
    refine iSup_le fun b => iSup_le fun hb => iSup_le fun hb1 => ?_
    rw [hCb b hb hb1]
    exact inf_le_right
  have hBXc : ∀ b ∈ B, b ≠ 1 → oddIn L ≤ centralizer ({b} : Set G) := fun b hb hb1 => by
    have h1 : oddIn L ≤ oddIn L ⊓ centralizer ({u} : Set G) := le_inf le_rfl hXu
    rw [← hCb b hb hb1] at h1
    exact h1.trans inf_le_right
  obtain ⟨a, haB, haA₀, ha1⟩ : ∃ a ∈ B, a ∈ A₀ ∧ a ≠ 1 := by
    by_contra h
    push Not at h
    have hbot : B ⊓ A₀ = ⊥ := eq_bot_iff.mpr fun x hx =>
      mem_bot.mpr (h x (mem_inf.mp hx).1 (mem_inf.mp hx).2)
    obtain ⟨hprod, -⟩ := CFSG.GroupTheory.card_sup_mul_card_inf_of_commute B A₀
      fun x hx y hy => hEel.1 x (mem_inf.mp hx).1 y (mem_sup_right hy)
    rw [hbot, card_bot, mul_one, hA₀c] at hprod
    have h1 : Nat.card ↥(B ⊔ A₀) ≤ Nat.card E := card_le_of_le (sup_le inf_le_left le_sup_right)
    rw [hEc, hA₀c] at h1
    omega
  have haL : a ∈ L := (mem_inf.mp (hA₀S₀ haA₀)).2
  have haZ : a ∉ zStarIn L := fun h => by
    have h1 : a ∈ A₀ ⊓ zStarIn L := mem_inf.mpr ⟨haA₀, h⟩
    rw [hA₀Z, mem_bot] at h1
    exact ha1 h1
  have haC : a ∈ centralizer (oddIn L : Set G) := mem_centralizer_iff.mpr fun x hx =>
    (mem_centralizer_singleton_iff.mp (hBXc a haB ha1 hx))
  have hq : IsQuasisimple (L ⧸ pPrimeCore 2 L) :=
    ((CatalogueBPrimeJoin.pComponent_subgroupOf_iff 2 L _ hLt).mp hLpt).2.2
  have hLN : L ≤ normalizer ((L ⊓ centralizer (oddIn L : Set G) : Subgroup G) : Set G) := by
    intro l hl
    have h1 := mem_normalizer_iff.mp (le_normalizer hl)
    have h2 := mem_normalizer_iff.mp
      (centralizer_normalized_of_mem_normalizer
        (normalizer_le_normalizer_oddIn L (le_normalizer hl)))
    rw [mem_normalizer_iff]
    intro h
    simp only [mem_inf]
    exact ⟨fun ⟨a, b⟩ => ⟨(h1 h).mp a, (h2 h).mp b⟩, fun ⟨a, b⟩ => ⟨(h1 h).mpr a, (h2 h).mpr b⟩⟩
  have hcov := le_sup_oddIn_of_normal hq inf_le_left hLN fun h =>
    haZ (h (mem_inf.mpr ⟨haL, haC⟩))
  exact hX (oddIn_le_center_of_le_sup hperf hcov)

end CFSG.ComponentClassification.GrSLit.GrS5
