module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.EightTenFour.ShortBlockCommutator
public import CFSG.LocalAnalysis.AGLEmbedding.WeakBlockBasic

public section

namespace CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.EightTenFour

open Subgroup CFSG CFSG.Open CFSG.AGLEmbedding CFSG.QuasithinUnique
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem blockU_eq_commutator {M L V : Subgroup G} (hLs : IsTwoPrimeComponent M L)
    (hVQ : V ≤ pCoreOf 2 M) (hVL : V ≤ Subgroup.normalizer (L : Set G))
    (hLV : L ≤ Subgroup.normalizer (V : Set G)) (hQV : ⁅pCoreOf 2 M, L⁆ ≤ V) :
    blockU L = ⁅V, L⁆ := by
  have hO : pCoreOf 2 L = L ⊓ pCoreOf 2 M := hLs.inf_twoCore.symm
  have hOQ : pCoreOf 2 L ≤ pCoreOf 2 M := hO ▸ inf_le_right
  have hU : blockU L = ⁅pCoreOf 2 L, L⁆ := rfl
  apply le_antisymm
  · have hUV : blockU L ≤ V := by
      rw [hU]; exact (Subgroup.commutator_mono hOQ le_rfl).trans hQV
    calc blockU L = ⁅blockU L, L⁆ :=
          (CFSG.AGLEmbeddingD2.McLaughlin.OrdinaryProofs.commutator_blockU_eq
            hLs.perfect).symm
      _ ≤ ⁅V, L⁆ := Subgroup.commutator_mono hUV le_rfl
  · have hWL : ⁅V, L⁆ ≤ L := by
      rw [Subgroup.commutator_le]
      intro v hv l hl
      have h1 : v * l * v⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp (hVL hv) l).mp hl
      rw [commutatorElement_def]
      exact L.mul_mem h1 (L.inv_mem hl)
    have hWV : ⁅V, L⁆ ≤ V := by
      rw [Subgroup.commutator_le]
      intro v hv l hl
      have h1 : l * v⁻¹ * l⁻¹ ∈ V :=
        (Subgroup.mem_normalizer_iff.mp (hLV hl) v⁻¹).mp (V.inv_mem hv)
      have : ⁅v, l⁆ = v * (l * v⁻¹ * l⁻¹) := by rw [commutatorElement_def]; group
      rw [this]; exact V.mul_mem hv h1
    have hWO : ⁅V, L⁆ ≤ pCoreOf 2 L := hO ▸ le_inf hWL (hWV.trans hVQ)
    calc ⁅V, L⁆ = ⁅⁅V, L⁆, L⁆ := (commutator_commutator_eq_of_perfect' hLs.perfect hLV hVL).symm
      _ ≤ ⁅pCoreOf 2 L, L⁆ := Subgroup.commutator_mono hWO le_rfl

theorem pRank_two_of_card_sixteen {A : Type} [Group A] (hcomm : ∀ a b : A, a * b = b * a)
    (hpow : ∀ a : A, a ^ 2 = 1) [Finite A] (hcard : Nat.card A = 16) : CFSG.pRank 2 A = 4 := by
  rw [CFSG.SectionRank.pRank_eq_open_pRank_top]
  unfold CFSG.Open.pRank
  have hmem : (4 : ℕ) ∈ {k : ℕ | ∃ E : Subgroup A, E ≤ ⊤ ∧ CFSG.Open.IsElemAbelian 2 E ∧
      Nat.card E = 2 ^ k} := by
    refine ⟨⊤, le_rfl, ⟨⟨⟨fun a b => Subtype.ext (hcomm a b)⟩⟩, fun x _ => hpow x⟩, ?_⟩
    rw [Subgroup.card_top, hcard]; norm_num
  have hbound : ∀ k ∈ {k : ℕ | ∃ E : Subgroup A, E ≤ ⊤ ∧ CFSG.Open.IsElemAbelian 2 E ∧
      Nat.card E = 2 ^ k}, k ≤ 4 := by
    rintro k ⟨E, -, -, hE⟩
    have h1 : Nat.card E ≤ Nat.card A := Subgroup.card_le_card_group E
    rw [hE, hcard] at h1
    by_contra h
    have : 2 ^ 5 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  exact le_antisymm (csSup_le ⟨4, hmem⟩ hbound) (le_csSup ⟨4, hbound⟩ hmem)

end CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.EightTenFour
