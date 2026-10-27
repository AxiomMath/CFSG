module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.Numeric
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.PerfectCommutator
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.BlockBridge
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.AltSevenBound

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.AGLEmbedding
  CFSG.RankThreeCoreUniqueness.Helpers
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem commutator_blockV_le_blockU {S L : Subgroup G} (hL : ⁅L, L⁆ = L)
    (hVL : ∀ v ∈ blockV S L, ∀ l ∈ L, v * l * v⁻¹ ∈ L) : ⁅blockV S L, L⁆ ≤ blockU L := by
  set V := blockV S L with hV
  have hLV : L ≤ Subgroup.normalizer (V : Set G) := le_normalizer_blockV S L
  have hVe := isElemAbelian_blockV S L
  have hVc : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hVe.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hXV : ⁅V, L⁆ ≤ V := commutator_le_of_le_normalizer hLV
  have hXL : ⁅V, L⁆ ≤ L := by
    rw [Subgroup.commutator_le]
    intro v hv l hl
    have e : ⁅v, l⁆ = (v * l * v⁻¹) * l⁻¹ := by simp [commutatorElement_def, mul_assoc]
    rw [e]
    exact L.mul_mem (hVL v hv l hl) (L.inv_mem hl)
  have hVLcore : V ⊓ L ≤ pCoreOf 2 L := by
    refine normal_pGroup_le_pCoreOf 2 (V ⊓ L) L inf_le_right ?_
      ((elementary_isPGroup 2 V hVe).to_le inf_le_left)
    refine (Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_right).mpr ?_
    intro ℓ hℓ
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · rintro ⟨hxV, hxL⟩
      exact ⟨(Subgroup.mem_normalizer_iff.mp (hLV hℓ) x).mp hxV,
        L.mul_mem (L.mul_mem hℓ hxL) (L.inv_mem hℓ)⟩
    · rintro ⟨hxV, hxL⟩
      refine ⟨(Subgroup.mem_normalizer_iff.mp (hLV hℓ) x).mpr hxV, ?_⟩
      have := L.mul_mem (L.mul_mem (L.inv_mem hℓ) hxL) hℓ
      simpa [mul_assoc] using this
  have hXcore : ⁅V, L⁆ ≤ pCoreOf 2 L := fun x hx => hVLcore ⟨hXV hx, hXL hx⟩
  exact (commutator_le_commutator_commutator_of_perfect hL hLV hVc).trans
    (Subgroup.commutator_mono_left hXcore)

omit [Finite G] in
theorem exists_surjective_barM {M L : Subgroup G} (hLM : L ≤ M) :
    ∃ F : ↥L →* ↥(barM M L), Function.Surjective F := by
  let F₀ : ↥L →* (↥M ⧸ CFSG.pCore 2 ↥M) :=
    (QuotientGroup.mk' (CFSG.pCore 2 ↥M)).comp
      ((Subgroup.inclusion hLM : ↥L →* ↥M))
  have hrange : F₀.range = barM M L := by
    ext z
    simp only [MonoidHom.mem_range, barM, Subgroup.mem_map, Subgroup.mem_subgroupOf]
    constructor
    · rintro ⟨l, rfl⟩
      exact ⟨⟨l, hLM l.2⟩, l.2, rfl⟩
    · rintro ⟨m, hm, rfl⟩
      exact ⟨⟨m, hm⟩, rfl⟩
  refine ⟨F₀.codRestrict (barM M L) (fun l => hrange ▸ ⟨l, rfl⟩), fun z => ?_⟩
  obtain ⟨l, hl⟩ : (z : ↥M ⧸ CFSG.pCore 2 ↥M) ∈ F₀.range := by
    rw [hrange]; exact z.2
  exact ⟨l, Subtype.ext hl⟩

theorem three_dvd_card_inf_centralizer_of_nineThreeFive {M S L : Subgroup G} (hLM : L ≤ M)
    (hL : ⁅L, L⁆ = L) (h5 : NineThreeFive M L)
    (hVL : ∀ v ∈ blockV S L, ∀ l ∈ L, v * l * v⁻¹ ∈ L) {y : G} (hy : y ∈ blockV S L) :
    3 ∣ Nat.card (L ⊓ Subgroup.centralizer ({y} : Set G) : Subgroup G) := by
  obtain ⟨-, ⟨e⟩, hU⟩ := h5
  obtain ⟨F, hF⟩ := exists_surjective_barM hLM
  have hn : Nat.card ↥(⁅blockV S L, L⁆ : Subgroup G) ≤ 2 ^ 4 :=
    hU ▸ Subgroup.card_le_of_le (commutator_blockV_le_blockU hL hVL)
  refine three_dvd_card_inf_centralizer_of_quotient_bound hy (e.toMonoidHom.comp F)
    (e.surjective.comp hF) hn (c := 140)
    (fun H hH => card_le_of_not_three_dvd_alt_seven H hH) ?_
  rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
  simp [Nat.factorial]

end CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData
