module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P54Tools
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1SpinCover

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.T1.P54

open CFSG Subgroup Assembly.LowTwoRank CFSG.LieType.Universal.Spin CFSG.ClassicalGroups.Orthogonal

theorem card_center_eq_two_of_spinOdd {Y : Type} [Group Y] [Finite Y] {n p f : ℕ}
    (h5 : 5 ≤ p ^ f) (hq : IsQuasisimple Y) (hZ2 : IsPGroup 2 (center Y)) (hZ : center Y ≠ ⊥)
    (hm : Blueprint.LieModel (Y ⧸ center Y) .POmegaOdd n p f) : Nat.card (center Y) = 2 := by
  rcases hm with ⟨-, ⟨hp, -, hn, hp2⟩, K, _, _, hK, ⟨e⟩⟩ | ⟨-, h, -⟩ | ⟨-, h, -⟩ | ⟨-, h, -⟩
  rotate_left
  · exact absurd h (by decide)
  · exact absurd h (by decide)
  · exact absurd h (by decide)
  have hodd : Odd (Nat.card K) := hK ▸ (hp.odd_of_ne_two hp2).pow
  have h2 : (2 : K) ≠ 0 := CFSG.Semidihedral.OddFieldSL2.two_ne_zero_of_odd_card K hodd
  have h5K : 5 ≤ Nat.card K := hK ▸ h5
  have : Finite (spinGroup (quadOdd n K)) :=
    LieType.Steinberg.finite_spinGroup_of_ker _ (coe_ker_spinMatrix_quadOdd h2)
  have : Group.IsPerfect Y := hq.1
  obtain ⟨hβs, -, -⟩ := spinToStatedProj_quadOdd h2 hn
  set β := spinToStatedProj (quadOdd n K) (range_spinMatrix_quadOdd h2 hn) with hβ
  set η : Y →* StatedProj (StatedOmega (StatedQuadOdd n K)) :=
    e.toMonoidHom.comp (QuotientGroup.mk' (center Y)) with hη
  have hηs : Function.Surjective η := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hηker : η.ker = center Y := by
    ext y
    rw [MonoidHom.mem_ker, hη, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  obtain ⟨α, -, -, hker⟩ := LieType.Steinberg.exists_surjective_of_isPerfect
    (fun E _ _ π hπ hcen _ =>
      LieType.Steinberg.CentralExt.SpinOddClosed.spinOdd_exists_section_of_central h2 hn h5K
        hπ hcen)
    hβs hηs (hηker ▸ le_rfl) (hηker ▸ hZ2)
  have hβcard : Nat.card β.ker = 2 :=
    LieType.Steinberg.CentralExt.SpinOddClosed.card_ker_spinToStatedProj_quadOdd h2 hn
  have hdvd : Nat.card (center Y) ∣ 2 := by
    rw [← hηker, hker, ← hβcard]
    exact Subgroup.card_dvd_of_surjective (α.subgroupMap_surjective β.ker)
  rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h1
  · exact absurd ((Subgroup.card_eq_one).mp h1) hZ
  · exact h1

theorem rowB : RowB := by
  intro Y _ _ hq hZ p hp hp2 τ n f hτ hlie h5 hpsl hc t ht htZ
  subst hτ
  have ht1 : t ≠ 1 := fun h => by rw [h, orderOf_one] at ht; exact absurd ht (by norm_num)
  have hZne : center Y ≠ ⊥ := fun h => ht1 (by rw [h, mem_bot] at htZ; exact htZ)
  have hcov : IsCoverOf .POmegaOdd n p f 2 Y :=
    ⟨hq, card_center_eq_two_of_spinOdd h5 hq hZ hZne hlie, hlie⟩
  obtain ⟨z, hz2, hZz, u, J₁, J₂, hu2, huZ, hJ₁, hJ₂, hs₁, hs₂, hc₁, hc₂⟩ :=
    lemma412_of_isCoverOf h5 hcov
  have htz : t = z := (eq_one_or_eq_of_mem_zpowers hz2 (hZz ▸ htZ)).resolve_left ht1
  subst htz
  have hu1 : u ≠ 1 := fun h => by rw [h, orderOf_one] at hu2; exact absurd hu2 (by norm_num)
  have huu : u * u = 1 := by rw [← sq, ← hu2, pow_orderOf_eq_one]
  have htt : t * t = 1 := by rw [← sq, ← ht, pow_orderOf_eq_one]
  have hut : u * t = t * u := mem_center_iff.mp htZ u
  have mem_of : ∀ {J : Subgroup Y} {w : Y}, (center ↥J).map J.subtype = zpowers w → w ∈ J := by
    intro J w hJw
    have h1 : w ∈ (center ↥J).map J.subtype := hJw ▸ mem_zpowers w
    obtain ⟨x, -, rfl⟩ := h1
    exact x.2
  have hne : J₁ ≠ J₂ := by
    intro h
    subst h
    have h1 : u ∈ zpowers (u * t) := by
      rw [← hc₂, hc₁]
      exact mem_zpowers u
    have hw : (u * t) * (u * t) = 1 := by
      calc u * t * (u * t) = u * (t * u) * t := by group
        _ = 1 := by rw [← hut, ← mul_assoc, huu, one_mul, htt]
    have hw1 : u * t ≠ 1 := fun h2 => huZ (by
      rw [show u = t⁻¹ from eq_inv_of_mul_eq_one_left h2]
      exact inv_mem htZ)
    have hw2 : orderOf (u * t) = 2 := orderOf_eq_prime (by rw [sq, hw]) hw1
    rcases eq_one_or_eq_of_mem_zpowers hw2 h1 with h2 | h2
    · exact hu1 h2
    · exact ht1 (mul_left_cancel (h2.symm.trans (mul_one u).symm))
  refine ⟨u, hu2, not_mem_fusionZStar hq ht huZ, J₁, J₂, hJ₁, hJ₂, hne, mem_of hc₁,
    isSLTwoOver_quot hp hp2 h5 hs₁, ⟨.PSL, 2, lieModel_psl_of_isSLTwoOver hp hp2 h5 hs₂⟩,
    .inr ?_⟩
  rw [← hut]
  exact mem_of hc₂

end CFSG.ComponentClassification.HarrisLit.T1.P54
