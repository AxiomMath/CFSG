module

public import CFSG.LocalAnalysis.ComponentClassification.Asc76YSec4D13

public section

namespace CFSG.ComponentClassification.Asc76.Sec4

open Subgroup CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
  CFSG.ComponentClassification.AS76b CFSG.ComponentClassification.AschbacherTheorem3

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

@[expose] def HallDihedralFusion : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (Ω : Set (Subgroup G)), Assumption41 Ω →
    (∀ K ∈ Ω, ∀ R, IsSylowOf 2 R K → IsTwoNil K R) →
    (∃ K₀ ∈ Ω, ∀ K ∈ Ω, ∃ g : G, K = AschbacherTightEmbedding.rightConjugate K₀ g) →
    ∀ S K R U : Subgroup G, IsSylowOf 2 S ⊤ → K ∈ Ω → IsSylowOf 2 R K → R ≤ S →
      IsDihedralRot U R → sec4W Ω S = U →
      ∀ t : G, IsZInv Ω t → t ∈ S → t ∉ U → K.Normal

theorem exists_isSylowOf_le_of_mem (hΩ : Assumption41 Ω) {S : Subgroup G} (hS : IsSylowOf 2 S ⊤)
    {K₁ : Subgroup G} (hK₁ : K₁ ∈ Ω) : ∃ K R : Subgroup G, K ∈ Ω ∧ IsSylowOf 2 R K ∧ R ≤ S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨R₁, hR₁⟩ := exists_isSylowOf 2 K₁
  obtain ⟨S₀, hS₀, hRS₀⟩ := exists_isSylowOf_le hR₁.isPGroup (le_top : R₁ ≤ ⊤)
  obtain ⟨k, -, hk⟩ := L26.IsSylowOf.exists_conj_mem hS hS₀
  refine ⟨_, _, hΩ.conj_mem K₁ hK₁ k, isSylowOf_rightConjugate hR₁ k, fun y hy => ?_⟩
  rw [mem_rightConjugate_iff] at hy
  have h1 := (hk _).mp (hRS₀ hy)
  have e : k⁻¹ * (k * y * k⁻¹) * k = y := by group
  rwa [e] at h1

theorem MinCounter.mem_sec4W_of_isZInv (h22 : Asc76Lemma22) (hHall : HallDihedralFusion)
    {S : Subgroup G} (hM : MinCounter Ω S) (hdis : ∃ K ∈ Ω, ∃ J ∈ Ω, J ∉ dStarComp Ω K)
    {t : G} (htZ : IsZInv Ω t) (htW : t ∈ normalizer (sec4W Ω S : Set G)) : t ∈ sec4W Ω S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hΩ := hM.assumption
  have hS := hM.sylow
  set W := sec4W Ω S with hWdef
  by_contra htW'
  by_cases htwo : ∃ a b : G, a ∈ W ∧ IsZInv Ω a ∧ b ∈ W ∧ IsZInv Ω b ∧ a ≠ b
  · obtain ⟨J, hJ, T₀, V₀, hT₀, hV₀, htV, ht1, htt⟩ := htZ
    obtain ⟨a, b, haW, haZ, hbW, hbZ, hab⟩ := htwo
    exact hM.false_of_two_mem_sec4W h22 hdis hJ hT₀ hV₀ htV ht1 htt htW htW' haW haZ hbW hbZ hab
  push Not at htwo
  obtain ⟨K₁, hK₁, -⟩ := hM.single
  obtain ⟨K, R, hK, hR, hRS⟩ := exists_isSylowOf_le_of_mem hΩ hS hK₁
  obtain ⟨U, hU⟩ := Assumption41.exists_rot hΩ hK hR
  have hUW : U ≤ W := le_sec4W (hU.le.trans hRS) (isRot_of hK hR hU)
  obtain ⟨z, hzU, hz1, hzz, -, -⟩ := hU.exists_involution
  have hzZ : IsZInv Ω z := ⟨K, hK, R, U, hR, hU, hzU, hz1, hzz⟩
  have hWU : W = U := by
    refine le_antisymm ?_ hUW
    refine iSup_le fun U' => iSup_le fun hU'S => iSup_le fun hU' => ?_
    obtain ⟨K', hK', R', hR', hU'R'⟩ := IsRot.exists_isDihedralRot hΩ hU'
    have hU'W : U' ≤ W := le_sec4W hU'S hU'
    obtain ⟨z', hz'U', hz'1, hz'z', -, -⟩ := hU'R'.exists_involution
    have hz'z : z' = z := htwo z' z (hU'W hz'U') ⟨K', hK', R', U', hR', hU'R', hz'U', hz'1, hz'z'⟩
      (hUW hzU) hzZ
    have hKK' : K' = K := eq_of_mem_of_mem hΩ hK' hK (hz'z ▸ hR'.le (hU'R'.le hz'U'))
      (hR.le (hU.le hzU)) hz1 hzz
    rw [hKK'] at hR'
    exact (rot_eq_of_le_sec4W hΩ hS hK hR' hU'R' hR hU hU'W hUW).le
  have hSN : IsSylowOf 2 S (normalizer (W : Set G)) :=
    hS.of_le (le_normalizer_sec4W hΩ.conj_mem S) le_top
  obtain ⟨J, hJ, T₀, V₀, hT₀, hV₀, htV, ht1, htt⟩ := id htZ
  have htP : IsPGroup 2 (zpowers t) :=
    isPGroup_zpowers_of_pow_eq_one (n := 1) (by rw [pow_one, pow_two]; exact htt)
  obtain ⟨P, hP, htP'⟩ := exists_isSylowOf_le htP ((zpowers_le).mpr htW)
  obtain ⟨n, hnN, hn⟩ := L26.IsSylowOf.exists_conj_mem hSN hP
  have ht'S : n⁻¹ * t * n ∈ S := (hn t).mp (htP' (mem_zpowers t))
  have ht'U : n⁻¹ * t * n ∉ U := by
    rw [← hWU]
    intro h
    apply htW'
    have := (mem_normalizer_iff.mp hnN _).mp h
    have e : n * (n⁻¹ * t * n) * n⁻¹ = t := by group
    rwa [e] at this
  exact hM.not_normal_member hK
    (hHall G Ω hΩ hM.twoNil hM.single S K R U hS hK hR hRS hU hWU _ (htZ.conj hΩ n) ht'S ht'U)

end CFSG.ComponentClassification.Asc76.Sec4
