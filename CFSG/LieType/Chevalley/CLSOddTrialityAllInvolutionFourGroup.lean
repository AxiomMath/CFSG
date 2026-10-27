module

public import CFSG.LieType.Chevalley.OddTrialityCosetInvolutions
public import CFSG.LieType.Chevalley.CLSOddDiagramFourGroup
public import CFSG.LieType.Chevalley.OddExceptionalOuterTwoRank
public import CFSG.LocalAnalysis.ComponentInitial.InvolutionFixedFourGroupTransport

public noncomputable section

namespace CFSG.LieType.Chevalley.OddTrialityAllInvolution

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.FixedFourGroup
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.Assembly.LowTwoRank (StatedLieTag)

theorem _root_.CFSG.LieType.Chevalley.odd_triality_all_involution_fixed_four_group
    (L : Type)
    [Group L] [Finite L] [IsSimpleGroup L] (hLnab : ∃ a b : L, a * b ≠ b * a) {p f : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f) (hL : ChevalleyExceptionalModel L .trialityD4 p f)
    (α : MulAut L) (hα : α ^ 2 = 1) :
    ∃ V : Subgroup L, V ≤ fixedSubgroup α ∧ IsElementaryAbelian 2 V ∧ Nat.card V = 4 := by
  classical
  by_cases hin : α ∈ inner L
  · obtain ⟨g, rfl⟩ := hin
    exact exists_four_group_le_fixedSubgroup_conj hLnab g hα
  have hm : TwistedChevalleyModel L .D4 (p ^ f) := hL.2
  obtain ⟨K, _, _, σ, hK, hσ, ⟨e⟩⟩ := exists_mulEquiv_graphFixedRootGroup_card .D4 hp hf hm
  have hK3 : Nat.card K = (p ^ f) ^ 3 := hK
  set β := MulAut.congr e α with hβdef
  have hβ2 : β ^ 2 = 1 := by rw [hβdef, ← map_pow, hα, map_one]
  have hβo : β ∉ inner (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := by
    rw [hβdef, congr_mem_inner_iff]
    exact hin
  obtain ⟨hcoe, hNF, ⟨Θ, hΘ, -, hker, hinv⟩, -⟩ :=
    odd_triality_exact_automorphism_normal_form hp hp2 hf K hK3 σ hσ
  obtain ⟨⟨g, δ⟩, hgδ, -⟩ := hNF β
  change β = MulAut.conj g * fieldActor σ δ at hgδ
  have hΘβ : Θ β = δ := hΘ β g δ hgδ
  have hδ1 : Θ β ≠ 1 := fun h1 => hβo (by
    rw [← MonoidHom.mem_ker, hker] at h1
    exact h1)
  obtain ⟨⟨a, ha⟩, hδc⟩ := (hinv β hβ2).resolve_left hδ1
  rw [hΘβ] at hδc
  have hodd : Odd (p ^ a) := (hp.eq_two_or_odd'.resolve_left hp2).pow
  have hK6 : Nat.card K = (p ^ a) ^ 6 := by
    rw [hK3, ha, ← pow_mul, ← pow_mul]
    ring_nf
  have hσr : ∀ c, σ c = c ^ ((p ^ a) ^ 2) := fun c => by
    rw [hσ, ha, ← pow_mul]
    ring_nf
  have hδr : ∀ c, δ c = c ^ ((p ^ a) ^ 3) := fun c => by
    rw [hδc, ha, ← pow_mul, show 3 * (a + a) / 2 = a * 3 by omega]
  have hβ2' : (MulAut.conj g * fieldActor σ δ) ^ 2 = 1 := by rw [← hgδ]; exact hβ2
  obtain ⟨-, ⟨ψ, hψ⟩, -⟩ := odd_triality_field_coset_involution_fixed_p_components
    (hp.isPrimePow.pow (by omega)) hodd K hK6 σ hσr δ hδr g hβ2'
  have hK' : Nat.card K = p ^ (3 * f) := by rw [hK3, ← pow_mul, mul_comm]
  have : CharP K p := finite_field_prime_power_characteristic hp (by omega) hK'
  have hKc : ringChar K ≠ 2 := by rw [ringChar.eq K p]; exact hp2
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨A, hAle, hAab, hAcard, hAfix, -, -⟩ :=
    odd_diagram_coordinate_fields_fixed_four_group TwistTag.D4 K hKc σ.toRingHom
  set V₁ := A.subgroupOf (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) with hV₁
  have hV₁ab : IsElementaryAbelian 2 V₁ := IsElementaryAbelian.subgroupOf hAle
  have hV₁card : Nat.card V₁ = 4 := by
    rw [hV₁, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAle).toEquiv]
    exact hAcard
  have hV₁fix : V₁ ≤ fixedSubgroup (MulAut.congr ψ β) := by
    intro v hv
    change MulAut.congr ψ β v = v
    rw [congr_eq_conj, hgδ, hψ]
    refine Subtype.ext ?_
    rw [hcoe]
    exact Units.ext (hAfix δ.toRingHom _ hv)
  obtain ⟨V₂, hV₂fix, hV₂ab, hV₂card⟩ :=
    exists_four_group_le_fixedSubgroup_of_congr ψ β hV₁fix hV₁ab hV₁card
  exact exists_four_group_le_fixedSubgroup_of_congr e α hV₂fix hV₂ab hV₂card

end CFSG.LieType.Chevalley.OddTrialityAllInvolution
