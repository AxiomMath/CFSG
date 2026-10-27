module

public import CFSG.ClassicalInvolution.Asc77.WP3FrameBootChain
public import CFSG.ClassicalInvolution.Asc77.WP3FrameBootCtx
import CFSG.ClassicalInvolution.Asc77.AscT3Conj
import CFSG.ClassicalInvolution.Asc77.AscE187Img

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG CFSG.Open CFSG.ComponentClassification CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Generic.DeltaClosure
  CFSG.ClassicalInvolution.Generic.CoreAssembly CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Balance.Bootstrap CFSG.ClassicalInvolution.Asc77.ExactLayer
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.RouteD
open CFSG.Assembly.LowTwoRank

section AEmpty

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem aEmpty_of_twinSet_subset (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : HypOmegaMod p f Ω)
    {K : Subgroup G} (hK : K ∈ Ω) (hno : ∀ M ∈ twinSet Ω K, M = K) : AEmpty Ω K := by
  by_contra hn
  obtain ⟨J, zK, zJ, hv⟩ := T3.not_aEmpty_iff.mp hn
  obtain ⟨a, -, -, hΩ', hz', hne⟩ := hv.exists_twin (l6_2 p f) hp hq hΩ hK
  exact hne (hno _ ⟨hΩ', zK, hv.hzK, hz'⟩)

end AEmpty

section Twins

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {z : G}

theorem eq_cases_of_card_two {n : ℕ} (hn : n = 2) {a b : Fin n} (hab : a ≠ b) (j : Fin n) :
    j = a ∨ j = b := by
  have hj := j.2
  have h0 := a.2
  have h1 := b.2
  have n01 : a.val ≠ b.val := fun e => hab (Fin.ext e)
  by_contra hcon
  push Not at hcon
  have a1 : j.val ≠ a.val := fun e => hcon.1 (Fin.ext e)
  have a2 : j.val ≠ b.val := fun e => hcon.2 (Fin.ext e)
  omega

theorem XCtx.eq_of_twin (X : XCtx p f Ω z) {i₀ : Fin X.D.card}
    (hA : ∀ j : Fin X.D.card, (X.D.tag j = .PSL ∧ X.D.rank j = 2) → j = i₀)
    {M : Subgroup G} (hM : M ∈ Ω) (hMz : IsUniqueInvolution M z) : M = X.K := by
  by_contra hne
  have hzC := XCtx.hzC z
  have hc := X.hΩ.comm_le_oddCore_of_twin X.hK hM (Ne.symm hne) X.hKz hMz
  have hMcl : IsClassicalMember p f M z := isClassicalMember_of_twin X.hΩ hM hMz
  obtain ⟨j, hj, hjK⟩ := X.exists_A1_of_member X.hK X.K_cl
  obtain ⟨j', hj', hjM⟩ := X.exists_A1_of_member hM hMcl
  have e1 : j = i₀ := hA j hj
  have e2 : j' = i₀ := hA j' hj'
  rw [e1] at hj hjK
  rw [e2] at hj' hjM
  refine X.range_not_comm_of_A1 i₀ hj ?_ ?_
  · rw [← hjK]
    exact oddQuotMk_mem_modOdd X.K_cl.mem hzC
  · intro a ha b hb
    rw [← hjK] at ha
    rw [← hjM] at hb
    obtain ⟨k, hk, rfl⟩ := ha
    obtain ⟨y, hy, rfl⟩ := hb
    have hcomm : (k : G) * (y : G) * (k : G)⁻¹ * (y : G)⁻¹ ∈ ⁅X.K, M⁆ :=
      Subgroup.commutator_mem_commutator hk hy
    have hO : (k : G) * (y : G) * (k : G)⁻¹ * (y : G)⁻¹ ∈ oddCoreIn (Subgroup.centralizer
        ({z} : Set G)) :=
      oddCoreIn_le_of_isSubnormal X.K_cl.subnormal (hc hcomm).1
    obtain ⟨w, hw, hwc⟩ := hO
    have hweq : w = k * y * k⁻¹ * y⁻¹ := Subtype.ext hwc
    have h1 : oddQuotMk z w = 1 := oddQuotMk_eq_one_iff.mpr hw
    rw [hweq, map_mul, map_mul, map_mul, map_inv, map_inv] at h1
    exact commutatorElement_eq_one_iff_mul_comm.mp h1

theorem eq_of_twin_of_chainShape (hΩ : HypOmegaMod p f Ω) (hp : p ≠ 2) (hq : 5 ≤ p ^ f)
    {K : Subgroup G} (hK : K ∈ Ω) (hKz : IsUniqueInvolution K z) (hs : ChainShape p f Ω z)
    {M : Subgroup G} (hM : M ∈ Ω) (hMz : IsUniqueInvolution M z) : M = K := by
  obtain ⟨D, hcard, i₀, i₁, hne, ht₀, hr₀, ht₁, hr₁⟩ := hs
  let X : XCtx p f Ω z := { K := K, hK := hK, hKz := hKz, hΩ := hΩ, hp := hp, hq := hq, D := D }
  have hnotA₁ : ¬ (D.tag i₁ = .PSL ∧ D.rank i₁ = 2) := by
    rintro ⟨h1, h2⟩
    rcases hr₁ with h | h <;> omega
  refine X.eq_of_twin (i₀ := i₀) ?_ hM hMz
  intro j hj
  rcases eq_cases_of_card_two hcard hne j with h | h
  · exact h
  · exact absurd (h ▸ hj) hnotA₁

end Twins

section Chain

variable {p f : ℕ} [Fact p.Prime]

theorem noTwinsChain_of_hypOmega (hΩall : HypOmegaModAll p f) : NoTwinsChain p f := by
  intro G _ _ _ hnab hp2 hq K z hz hBelow hshape M hM M' hM'
  have hΩ : HypOmegaMod p f (CoreAssembly.conjClass K) := hΩall G hnab hp2 hq K z hz hBelow
  have hKz : IsUniqueInvolution K z :=
    ConnectedA2.isUniqueInvolution_of_isClassicalMember hp2 hq hz
  obtain ⟨g, rfl⟩ := hM
  obtain ⟨hM'Ω, w, hMw, hM'w⟩ := hM'
  have hconj : IsUniqueInvolution (conjSub g⁻¹ M') (g⁻¹ * w * g⁻¹⁻¹) := hM'w.conj g⁻¹
  have hK' : IsUniqueInvolution K (g⁻¹ * w * g⁻¹⁻¹) := by
    have := hMw.conj g⁻¹
    rwa [conjSub_inv_conjSub] at this
  have hzw : g⁻¹ * w * g⁻¹⁻¹ = z := hK'.eq hKz
  rw [hzw] at hconj
  have h := eq_of_twin_of_chainShape hΩ hp2 hq (CoreAssembly.mem_conjClass_self K) hKz hshape
    (hΩ.conjInvariant g⁻¹ M' hM'Ω) hconj
  have h2 : M' = conjSub g (conjSub g⁻¹ M') := (conjSub_conjSub_inv g M').symm
  rw [h2, h]

theorem aEmptyChain_of_hypOmega (hΩall : HypOmegaModAll p f) : AEmptyChain p f := by
  intro G _ _ _ hnab hp2 hq K z hz hBelow hshape M hM
  have hΩ : HypOmegaMod p f (CoreAssembly.conjClass K) := hΩall G hnab hp2 hq K z hz hBelow
  exact aEmpty_of_twinSet_subset hp2 hq hΩ hM
    (fun M' hM' => noTwinsChain_of_hypOmega hΩall G hnab hp2 hq K z hz hBelow hshape M hM M' hM')

theorem chainFrame_exists_on_of_lemma52'' (hΩ : HypOmegaModAll p f) (hGen : ChainFrameGenT p f)
    (h51t : ChainFrameHyp51t p f) (h51zt : ChainFrameHyp51zt p f) :
    FrameExistsOnE p f (ChainShapePred (p := p) (f := f)) :=
  chainFrame_exists_on_of_lemma52' hΩ (aEmptyChain_of_hypOmega hΩ) (noTwinsChain_of_hypOmega hΩ)
    hGen h51t h51zt lemma52

end Chain

end CFSG.ClassicalInvolution.Asc77
