module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5SKuActDefs
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5SKuDefs
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5Notation54

public section

namespace CFSG.ComponentClassification.GrSLit.GrS5S

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)
open scoped commutatorElement

theorem l34Sec5KuOddStep_of_action
    (hS : SchreierFor Blueprint.Catalog)
    (hU : CatalogueU.CatalogAlmostSimpleUnbalancedOutcome) (hheld : KProperRelativeB.HeldInput)
    (hSol : SolomonCommutingCoreInput) (hGW : GorensteinWalterConnectedInput)
    (hMax : MaximalTwoComponentInput) (hA : L34KuActionL25 ∧ L34KuActionL27 ∧
        L34KuActionL34) : L34Sec5KuOddStep := by
  intro G _ _ L t S T hset u hu K₁ hK₁K hK₁ h
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, hLt, hLpt⟩ := GrS5.eq_of_mem_inf_centralizer hS hU hheld hSol hGW hset
  have hZS := GrS5.mem_center_of_setting hS hU hheld hSol hGW hset
  have hCN := GrS5.centralizer_le_normalizer_of_setting hS hU hheld hSol hGW hMax hset
  obtain ⟨-, h54b, -, -⟩ :=
    GrS5.l34Notation54_of_inputs hS hU hheld hSol hGW hMax G L t S T hset u hu
  obtain ⟨hK₁C, hK₁p, -⟩ := h54b K₁ hK₁K hK₁
  obtain ⟨hbase, hfam, -, -, htS, -, -⟩ := hset
  obtain ⟨-, -, -, -, -, -, -, hUtypes⟩ := hbase
  obtain ⟨⟨-, -, -, -, -, hto, -, -⟩, -, -, -, -⟩ := hfam
  obtain ⟨huU, huo, -⟩ := hu
  have huS : u ∈ S := (sup_le inf_le_left (zpowers_le.mpr htS)) huU
  have htu : t * u = u * t := (hZS u huS).symm
  set C := centralizer ({u} : Set G) with hC
  set Y := oddIn L ⊓ C with hY
  have hYD : Y ≤ oddIn (centralizer ({t} : Set G)) ⊓ C :=
    inf_le_inf_right C (GSLit.map_pPrimeCore_le_of_isPComponent hLt hLpt)
  have hJY : ¬ ⁅K₁, Y⁆ ≤ oddIn K₁ := GrS5.not_commutator_le_of_le_l34K hK₁K hK₁C hK₁p
  have hU₁ : GSUnbalancingTriple u t K₁ :=
    GrS5.gsUnbalancingTriple_of_not_le hSol hto huo htu hK₁C hK₁p hYD hJY
  have hYN : Y ≤ normalizer (K₁ : Set G) :=
    hYD.trans ((GrS5.solomon_involutions hSol hto huo htu).2 K₁ hK₁C hK₁p).1
  have hYt : Y ≤ centralizer ({t} : Set G) := (inf_le_left.trans (map_subtype_le _)).trans hLt
  have hYodd : Odd (Nat.card Y) := by
    refine Odd.of_dvd_nat ?_ (card_dvd_of_le inf_le_left)
    rw [oddIn, card_map_of_injective (subtype_injective _)]
    exact Nat.coprime_two_left.mp pPrimeCore_coprime_card
  have hcomm : ⁅K₁ ⊓ centralizer ({t} : Set G), Y⁆ ≤ oddIn L ⊓ K₁ := by
    rw [commutator_le]
    intro c hc y hy
    have hyX : y ∈ oddIn L := (mem_inf.mp hy).1
    refine mem_inf.mpr ⟨?_, ?_⟩
    · have hcX : c ∈ normalizer (oddIn L : Set G) :=
        GrS5.normalizer_le_normalizer_oddIn L (hCN (mem_inf.mp hc).2)
      have h1 : c * y * c⁻¹ ∈ oddIn L := (mem_normalizer_iff.mp hcX y).mp hyX
      rw [commutatorElement_def]
      exact mul_mem h1 (inv_mem hyX)
    · have h1 : y * c⁻¹ * y⁻¹ ∈ K₁ :=
        (mem_normalizer_iff.mp (hYN hy) c⁻¹).mp (inv_mem (mem_inf.mp hc).1)
      have e : ⁅c, y⁆ = c * (y * c⁻¹ * y⁻¹) := by
        rw [commutatorElement_def]
        group
      rw [e]
      exact mul_mem (mem_inf.mp hc).1 h1
  obtain ⟨h25, h27, h34⟩ := hA
  have hrow : ¬ ⁅K₁ ⊓ centralizer ({t} : Set G), Y⁆ ≤ oddIn K₁ := by
    rcases hUtypes u t K₁ hU₁ with h5 | h7 | hL
    · exact h25 G u t K₁ Y hU₁ h5 hYodd hYN hYt hJY
    · exact h27 G u t K₁ Y hU₁ h7 hYodd hYN hYt hJY
    · exact h34 G u t K₁ Y hU₁ hL hYodd hYN hYt hJY
  exact hrow (hcomm.trans h)

end CFSG.ComponentClassification.GrSLit.GrS5S
