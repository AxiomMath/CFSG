module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5Third510

public section

namespace CFSG.ComponentClassification.GrSLit.GrS5S

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ComponentClassification.UnbalancedGS
  CFSG.ComponentClassification.GrSLit CFSG.ComponentClassification.GrSLit.GrS5
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)

variable {G : Type} [Group G] [Finite G]

theorem false_of_four_le_centralizer
    (hS : SchreierFor Blueprint.Catalog)
    (hU : CatalogueU.CatalogAlmostSimpleUnbalancedOutcome) (hheld : KProperRelativeB.HeldInput)
    (hSol : SolomonCommutingCoreInput) (hGW : GorensteinWalterConnectedInput)
    {L : Subgroup G} {t : G} {S T : Subgroup G} (hset : L34Sec5Setting G L t S T) {u : G}
    (hmax : ∀ v ∈ L34UnbalancingSet L t S, Nat.card ↥(oddIn L ⊓ centralizer ({v} : Set G)) ≤
      Nat.card ↥(oddIn L ⊓ centralizer ({u} : Set G)))
    {B : Subgroup G} (hBS : B ≤ S ⊓ L) (hBel : IsElemTwo B) (hB4 : 4 ≤ Nat.card B)
    (hBK : ∀ b ∈ B, b ≠ 1 → b ∉ coreActionKernel L)
    (hBu : ∀ b ∈ B, oddIn L ⊓ centralizer ({u} : Set G) ≤ centralizer ({b} : Set G)) :
    False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, hLt, hLpt⟩ := eq_of_mem_inf_centralizer hS hU hheld hSol hGW hset
  have hZS := mem_center_of_setting hS hU hheld hSol hGW hset
  have hset' := hset
  obtain ⟨-, ⟨⟨-, -, -, -, -, hto, -, -⟩, -, -, hX, -⟩, -, hSyl, -, -, -⟩ := hset'
  have ht2 : t * t = 1 := by rw [← pow_two, ← hto, pow_orderOf_eq_one]
  have htKL : t ∈ coreActionKernel L := mem_coreActionKernel_of_commute fun l hl =>
    (mem_centralizer_singleton_iff.mp (hLt hl)).symm
  have hperf : ⁅L, L⁆ = L := GSThmB.commutator_eq_self_of_isPComponent hLt hLpt
  have hXodd : Odd (Nat.card (oddIn L)) := by
    rw [oddIn, card_map_of_injective (subtype_injective _)]
    exact Nat.coprime_two_left.mp pPrimeCore_coprime_card
  have hXt : ∀ x ∈ oddIn L, x * t = t * x := fun x hx =>
    mem_centralizer_singleton_iff.mp (hLt (map_subtype_le _ hx))
  have hCb : ∀ b ∈ B, b ≠ 1 →
      oddIn L ⊓ centralizer ({b} : Set G) = oddIn L ⊓ centralizer ({u} : Set G) := by
    intro b hb hb1
    have hle : oddIn L ⊓ centralizer ({u} : Set G) ≤ oddIn L ⊓ centralizer ({b} : Set G) :=
      le_inf inf_le_left (hBu b hb)
    obtain ⟨hbS, hbL⟩ := mem_inf.mp (hBS hb)
    have hbo : orderOf b = 2 := orderOf_eq_prime (by rw [pow_two]; exact hBel.2 b hb) hb1
    obtain ⟨-, b', hb', hb'n⟩ := l34Lemma53_of_inputs hS hU hheld hSol hGW G L t S T hset b
      hbS hbo (hBK b hb hb1) (mem_sup_left hbL)
    have hbt' : b * t = t * b := hZS b hbS
    have hbt : b * t = t ^ (1 : ℤ) * b := by
      rw [zpow_one]
      exact hbt'
    have hCt : oddIn L ⊓ centralizer ({t ^ (1 : ℤ) * b} : Set G) =
        oddIn L ⊓ centralizer ({b} : Set G) := by
      ext x
      simp only [mem_inf, mem_centralizer_singleton_iff]
      exact ⟨fun ⟨h1, h2⟩ => ⟨h1, (commute_zpow_mul_iff (hXt x h1) 1).mp h2⟩,
        fun ⟨h1, h2⟩ => ⟨h1, (commute_zpow_mul_iff (hXt x h1) 1).mpr h2⟩⟩
    have hb'U : b' ∈ L34UnbalancingSet L t S := by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hb'
      rcases hb' with rfl | rfl
      · exact ⟨mem_sup_left (hBS hb), hbo, hb'n⟩
      · refine ⟨mul_mem (mem_sup_left (hBS hb)) (mem_sup_right (mem_zpowers t)), ?_, hb'n⟩
        refine orderOf_eq_prime ?_ ?_
        · rw [pow_two, show b * t * (b * t) = (b * b) * (t * t) by
            rw [mul_assoc, ← mul_assoc t b t, ← hbt']; group,
            hBel.2 b hb, ht2, one_mul]
        · intro h
          apply hBK b hb hb1
          rw [show b = t⁻¹ by rw [← mul_eq_one_iff_eq_inv.mp h]]
          exact inv_mem htKL
    have hCb' : oddIn L ⊓ centralizer ({b'} : Set G) = oddIn L ⊓ centralizer ({b} : Set G) := by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hb'
      rcases hb' with rfl | rfl
      · rfl
      · rw [hbt]
        exact hCt
    have hcard : Nat.card ↥(oddIn L ⊓ centralizer ({b} : Set G)) ≤
        Nat.card ↥(oddIn L ⊓ centralizer ({u} : Set G)) := by
      rw [← hCb']
      exact hmax b' hb'U
    exact (Subgroup.eq_of_le_of_card_ge hle hcard).symm
  have hBX : B ≤ normalizer (oddIn L : Set G) := fun b hb =>
    normalizer_le_normalizer_oddIn L (hSyl.1 (mem_inf.mp (hBS hb)).1)
  have hgen := CFSG.SignalizerFunctorTheorem.McBride.iSup_centralizer_nonidentity Nat.prime_two
    hBel.isElemAbelian ((by norm_num : (2 : ℕ) ^ 2 = 4).trans_le hB4) hBX
    (Nat.coprime_two_left.mpr hXodd)
  have hXu : oddIn L ≤ centralizer ({u} : Set G) := by
    rw [← hgen]
    refine iSup_le fun b => iSup_le fun hb => iSup_le fun hb1 => ?_
    rw [hCb b hb hb1]
    exact inf_le_right
  obtain ⟨a, haB, ha1⟩ : ∃ a ∈ B, a ≠ 1 := by
    by_contra h
    push Not at h
    have hbot : B = ⊥ := eq_bot_iff.mpr fun x hx => mem_bot.mpr (h x hx)
    rw [hbot, card_bot] at hB4
    omega
  have haL : a ∈ L := (mem_inf.mp (hBS haB)).2
  have haZ : a ∉ zStarIn L := fun h => hBK a haB ha1 (zStarIn_le_coreActionKernel L h)
  have haC : a ∈ centralizer (oddIn L : Set G) := by
    have h1 : oddIn L ≤ oddIn L ⊓ centralizer ({u} : Set G) := le_inf le_rfl hXu
    rw [← hCb a haB ha1] at h1
    exact mem_centralizer_iff.mpr fun x hx =>
      mem_centralizer_singleton_iff.mp (mem_inf.mp (h1 hx)).2
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

end CFSG.ComponentClassification.GrSLit.GrS5S
