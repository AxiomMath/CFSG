module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4End46R2
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4InputsEnd46F
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4InputsEndS4

public section

namespace CFSG.ComponentClassification.GrSLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
open scoped Pointwise

namespace GrS4

variable {G : Type} [Group G] [Finite G]

theorem three_le_pRank_centralizer_of_mem_withKernel
    (hSqC : L34SquareCenterFact) {J S : Subgroup G} (hJ : ⁅J, J⁆ = J)
    (hL : IsL34Type (J ⧸ Open.fusionZStar J)) (hS : IsSylowTwoIn S (normalizer (J : Set G)))
    (hnc : ¬ IsCyclic ↥(S ⊓ zStarIn J)) {t : G} (htS : t ∈ S) (htK : t ∈ withKernel J)
    (htt : t * t = 1) : 3 ≤ pRank 2 ↥(S ⊓ J ⊓ centralizer ({t} : Set G)) := by
  have hS2 : IsPGroup 2 S := isPGroup_of_isSylowTwoIn hS
  have hP : IsSylowTwoIn (S ⊓ J) J := isSylowTwoIn_inf hS
  have hZK : ∀ {z : G}, z ∈ zStarIn J → z ∈ coreActionKernel J := fun hz => by
    have h : zStarIn J = J ⊓ coreActionKernel J := GSThmB.map_fusionZStar_eq J
    rw [h] at hz
    exact (mem_inf.mp hz).2
  have hZab : ∀ x ∈ S ⊓ zStarIn J, ∀ y ∈ S ⊓ zStarIn J, x * y = y * x := fun x hx y hy =>
    mul_comm_of_mem_coreActionKernel hS2 (mem_inf.mp hx).1 (hZK (mem_inf.mp hx).2)
      (mem_inf.mp hy).1 (map_subtype_le _ (mem_inf.mp hy).2)
  obtain ⟨a₁, ha₁, a₂, ha₂, h11, h22, h1, h2, h12⟩ :=
    exists_two_involutions_of_not_isCyclic (hS2.to_le inf_le_left) hZab hnc
  have hKN : S ⊓ coreActionKernel J ≤ normalizer ((S ⊓ J : Subgroup G) : Set G) := by
    intro s hs
    obtain ⟨hsS, hsK⟩ := mem_inf.mp hs
    rw [mem_normalizer_iff]
    intro y
    rw [mem_inf, mem_inf, ← mem_normalizer_iff.mp (mem_coreActionKernel.mp hsK).1 y]
    constructor
    · rintro ⟨hyS, hyJ⟩
      exact ⟨mul_mem (mul_mem hsS hyS) (inv_mem hsS), hyJ⟩
    · rintro ⟨hyS, hyJ⟩
      refine ⟨?_, hyJ⟩
      have h := mul_mem (mul_mem (inv_mem hsS) hyS) hsS
      rwa [show s⁻¹ * (s * y * s⁻¹) * s = y by group] at h
  have htm : t ∈ ((S ⊓ J : Subgroup G) : Set G) * ((S ⊓ coreActionKernel J : Subgroup G) :
      Set G) := by
    rw [← coe_mul_of_right_le_normalizer_left _ _ hKN]
    exact inf_withKernel_le hS (mem_inf.mpr ⟨htS, htK⟩)
  obtain ⟨u, hu, k, hk, rfl⟩ := htm
  have hkc : ∀ p ∈ S ⊓ J, k * p = p * k := fun p hp =>
    mul_comm_of_mem_coreActionKernel hS2 (mem_inf.mp hk).1 (mem_inf.mp hk).2 (mem_inf.mp hp).1
      (mem_inf.mp hp).2
  have hu2 : u * u ∈ zStarIn J := by
    have huk := hkc u hu
    have h1 : u * u = (k * k)⁻¹ := by
      rw [eq_inv_iff_mul_eq_one]
      calc u * u * (k * k) = u * (u * k) * k := by group
        _ = u * (k * u) * k := by rw [huk]
        _ = u * k * (u * k) := by group
        _ = 1 := htt
    have h : zStarIn J = J ⊓ coreActionKernel J := GSThmB.map_fusionZStar_eq J
    rw [h]
    refine mem_inf.mpr ⟨mul_mem (mem_inf.mp hu).2 (mem_inf.mp hu).2, ?_⟩
    rw [h1]
    exact inv_mem (mul_mem (mem_inf.mp hk).2 (mem_inf.mp hk).2)
  have htr : S ⊓ J ⊓ centralizer ({u} : Set G) ≤ S ⊓ J ⊓ centralizer ({u * k} : Set G) := by
    intro p hp
    obtain ⟨hpP, hpu⟩ := mem_inf.mp hp
    refine mem_inf.mpr ⟨hpP, mem_centralizer_singleton_iff.mpr ?_⟩
    have h1 := mem_centralizer_singleton_iff.mp hpu
    calc p * (u * k) = p * u * k := by group
      _ = u * p * k := by rw [h1]
      _ = u * (p * k) := by group
      _ = u * (k * p) := by rw [hkc p hpP]
      _ = u * k * p := by group
  have hpow : ∀ E : Subgroup G, E ≤ S ⊓ J ⊓ centralizer ({u * k} : Set G) → IsElemTwo E →
      8 ≤ Nat.card E → 3 ≤ pRank 2 ↥(S ⊓ J ⊓ centralizer ({u * k} : Set G)) := by
    intro E hE hE2 hE8
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨m, hm⟩ := hE2.isPGroup.exists_card_eq
    have h3 : 3 ≤ m := by
      by_contra hlt
      push Not at hlt
      have : 2 ^ m ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    exact h3.trans (le_pRank_of_isElemTwo hE hE2 hm)
  by_cases huZ : u ∈ zStarIn J
  · obtain ⟨E, hEP, hE, hE8⟩ := exists_eight_le_of_l34 hL hP
    refine hpow E (fun e he => mem_inf.mpr ⟨hEP he, ?_⟩) hE hE8
    have heu : e * u = u * e := (mul_comm_of_mem_coreActionKernel hS2 (mem_inf.mp hu).1
      (hZK huZ) (mem_inf.mp (hEP he)).1 (mem_inf.mp (hEP he)).2).symm
    exact (htr (mem_inf.mpr ⟨hEP he, mem_centralizer_singleton_iff.mpr heu⟩)).2
  · obtain ⟨E, hE, hE2, hE8⟩ := exists_eight_of_sq_mem hSqC hJ hL hS2 hP ha₁ ha₂ h11 h22 h1 h2
      h12 hu huZ hu2
    exact hpow E (hE.trans htr) hE2 (by rw [hE8]; norm_num)

end GrS4

theorem l34Lemma46SquareRankStep_of_inputs
    (hOut : L34OutSquareFact) (hSqC : L34SquareCenterFact) : L34Lemma46SquareRankStep := by
  intro G _ _ a x J S A hset hcent hZ hrun hn3 hexp hnc W hW hWodd hWx hNJ hMO hNS hSyl v hvS
    hva
  obtain ⟨-, hU3, hL34, -, hS, -, -⟩ := id hset
  obtain ⟨ha2, -, -, hJa, hJc, -, -⟩ := hU3
  have hJ : ⁅J, J⁆ = J := GSThmB.commutator_eq_self_of_isPComponent hJa hJc
  have hS2 : IsPGroup 2 S := GrS4.isPGroup_of_isSylowTwoIn hS
  have hvv : v * v ∈ withKernel J :=
    hOut G J hJ hL34 v (hS.1 hvS) (hS2.to_le (zpowers_le.mpr hvS))
  have haa : a * a = 1 := by rw [← pow_two, ← ha2, pow_orderOf_eq_one]
  obtain ⟨g, hg⟩ := hva
  have htt : v * v * (v * v) = 1 := by
    rw [hg, show g⁻¹ * a * g * (g⁻¹ * a * g) = g⁻¹ * (a * a) * g by group, haa]
    group
  exact GrS4.three_le_pRank_centralizer_of_mem_withKernel hSqC hJ hL34 hS hnc (mul_mem hvS hvS)
    hvv htt

end CFSG.ComponentClassification.GrSLit
