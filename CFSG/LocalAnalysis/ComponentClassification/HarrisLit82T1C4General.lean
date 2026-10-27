module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1C4Spin

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.T1

open CFSG Subgroup Assembly.LowTwoRank CFSG.ComponentClassification.UnbalancedLayer
open scoped MatrixGroups

variable {G : Type} [Group G] [Finite G]

theorem mem_fusionZStar_of_mem_center {X : Type*} [Group X] {x : X} (hx : x ∈ center X) :
    x ∈ Open.fusionZStar X := by
  unfold Open.fusionZStar
  rw [mem_comap, mem_center_iff]
  intro g
  obtain ⟨g₀, rfl⟩ := QuotientGroup.mk_surjective g
  rw [QuotientGroup.mk'_apply, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul,
    mem_center_iff.mp hx g₀]

section Certified


theorem false_of_general (hI : C3Inputs) (h54 : Harris82Lemma54) (h58 : Harris82Lemma58b)
    [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a)
    (hK : Assembly.KProper Blueprint.Catalog G) (hcat : ¬ Blueprint.Catalog G) {z : G}
    (hz : orderOf z = 2) {L : Subgroup G} (hL : IsTwoComponentIn L (centralizer {z}))
    (hzL : z ∈ L) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hM : IsMTypeSchur p ↥L)
    {τ : StatedLieTag} {n f : ℕ} (hlie : Blueprint.LieModel (↥L ⧸ Open.fusionZStar ↥L) τ n p f)
    (h5 : 5 ≤ p ^ f) (hpsl : ¬ Blueprint.LieModel (↥L ⧸ Open.fusionZStar ↥L) .PSL 2 p f) :
    False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hzc : (⟨z, hzL⟩ : ↥L) ∈ center ↥L := mem_center_of_le_centralizer hL.1 hzL
  have hz' : orderOf (⟨z, hzL⟩ : ↥L) = 2 := by rw [Subgroup.orderOf_mk]; exact hz
  have hzZ : (⟨z, hzL⟩ : ↥L) ∈ Open.fusionZStar ↥L := mem_fusionZStar_of_mem_center hzc
  obtain ⟨u', hu'2, hu'Z, J₁, J₂, hJ₁, hJ₂, -, huJ₁, hs₁, ⟨τ₂, n₂, hlie₂⟩, hzJ₂⟩ :=
    h54 ↥L hL.2.2 p hp hp2 hM τ n f hlie h5 hpsl ⟨z, hzL⟩ hz' hzZ
  set u : G := (u' : G) with hudef
  have huL : u ∈ L := u'.2
  have hu : orderOf u = 2 := by rw [hudef, Subgroup.orderOf_coe]; exact hu'2
  have huz : u ∈ centralizer ({z} : Set G) := hL.1 huL
  have hcomm : u * z = z * u := mem_centralizer_singleton_iff.mp huz
  have hzu : z ≠ u := fun h1 => hu'Z (by
    have h2 : u' = ⟨z, hzL⟩ := Subtype.ext h1.symm
    rw [h2]
    exact hzZ)
  have hJmap : ∀ {J : Subgroup ↥L}, IsTwoComponentIn J (centralizer {u'}) →
      IsTwoComponentIn (J.map L.subtype) (centralizer {z} ⊓ centralizer {u}) := by
    intro J hJ
    have h1 := L35.isTwoComponentIn_map_of_injective L.subtype L.subtype_injective hJ
    rw [map_subtype_centralizer_mem] at h1
    exact isTwoComponentIn_inf_of_subnormal hL.1 hL.2.1 (centralizer {u}) h1
  let eJ₁ : ↥J₁ ≃* ↥(J₁.map L.subtype) := J₁.equivMapOfInjective _ L.subtype_injective
  let eJ₂ : ↥J₂ ≃* ↥(J₂.map L.subtype) := J₂.equivMapOfInjective _ L.subtype_injective
  have hs₁' : IsSLTwoOver (p ^ f) (↥(J₁.map L.subtype) ⧸ pPrimeCore 2 ↥(J₁.map L.subtype)) :=
    isSLTwoOver_of_mulEquiv' (QuotientGroup.congr _ _ eJ₁ (pPrimeCore_map_iso 2 eJ₁)) hs₁
  obtain ⟨eZ₂⟩ := nonempty_fusionZStar_equiv eJ₂
  have hlie₂' : Blueprint.LieModel (↥(J₂.map L.subtype) ⧸ Open.fusionZStar ↥(J₂.map L.subtype))
      τ₂ n₂ p f := GSThmB.OddQuot.lieModel_of_equiv eZ₂ hlie₂
  have huJ₁' : u ∈ J₁.map L.subtype := ⟨u', huJ₁, rfl⟩
  have finish : ∀ z₂ : G, orderOf z₂ = 2 → u ≠ z₂ → u * z₂ = z₂ * u →
      centralizer ({z} : Set G) ⊓ centralizer {u} = centralizer {u} ⊓ centralizer {z₂} →
      z₂ ∈ J₂.map L.subtype → False := by
    intro z₂ hz₂ hne hc hC hz₂J
    obtain ⟨K, hKc, huK, -, m, -, -, hcov, -⟩ := fourGroup_spinOdd hI h58 hnonab hK hcat hu hz₂
      hne hc (hC ▸ hJmap hJ₁) (hC ▸ hJmap hJ₂) huJ₁' hz₂J hp hp2 h5 hs₁' (.inr ⟨τ₂, n₂, hlie₂'⟩)
    exact false_of_spinOdd hI h58 hnonab hK hcat hu hKc huK hp hp2 h5 hcov
  rcases hzJ₂ with hzJ | hzuJ
  · exact finish z hz (Ne.symm hzu) hcomm (inf_comm _ _) ⟨⟨z, hzL⟩, hzJ, rfl⟩
  · have huz2 : orderOf (u * z) = 2 := orderOf_mul_of_commute hu hz hcomm hzu
    have hne : u ≠ u * z := fun h1 => by
      have h2 : z = 1 := by
        calc z = u⁻¹ * (u * z) := by group
          _ = 1 := by rw [← h1, inv_mul_cancel]
      rw [h2, orderOf_one] at hz
      exact absurd hz (by norm_num)
    have hc : u * (u * z) = u * z * u := by rw [mul_assoc, ← hcomm, ← mul_assoc]
    have hC : centralizer ({z} : Set G) ⊓ centralizer {u} =
        centralizer {u} ⊓ centralizer {u * z} := by
      rw [T23.centralizer_inf_mul, inf_comm]
    refine finish (u * z) huz2 hne hc hC ?_
    rw [hcomm]
    exact ⟨⟨z, hzL⟩ * u', hzuJ, rfl⟩

end Certified

end CFSG.ComponentClassification.HarrisLit.T1
