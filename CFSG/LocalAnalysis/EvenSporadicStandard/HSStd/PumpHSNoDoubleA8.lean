module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.PumpHSLift
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.PumpHSThree
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.OuterPumpChainA8
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.InnerCoverAltBlock
public import CFSG.RankThree.PartOne.Mult.Alternating

public section

namespace CFSG.EvenSporadicStandard.HSStd.PumpHS

open Subgroup CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.QuasithinUnique.Ch1
  CFSG.LocalAnalysis CFSG.EvenSporadicStandard.HSStd.Zassenhaus.Outer
  CFSG.EvenSporadicStandard.HSStd.Zassenhaus

theorem noDoubleA8_core
    {M K : Type} [Group M]
    [Finite M] [Group K] (hMq : CFSG.IsQuasisimple M) (hHS : IsSporadic (M ⧸ center M) .HS)
    (ι : K →* M) (hι : Function.Injective ι) (hKq : CFSG.IsQuasisimple K)
    (e : K ⧸ center K ≃* alternatingGroup (Fin 8)) : center K = ⊥ := by
  classical
  by_contra hne
  have : Finite K := Finite.of_injective ι hι
  have hKperf : Group.IsPerfect K := hKq.1
  have hMperf : Group.IsPerfect M := hMq.1
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let π : M →* M ⧸ center M := QuotientGroup.mk' (center M)
  let f : K →* M ⧸ center M := π.comp ι
  have hkerM : ∀ k ∈ f.ker, ι k ∈ center M := fun k hk =>
    (QuotientGroup.eq_one_iff _).1 hk
  have hkerC : f.ker ≤ center K := by
    intro k hk
    rw [Subgroup.mem_center_iff]
    intro g
    apply hι
    rw [map_mul, map_mul]
    exact Subgroup.mem_center_iff.1 (hkerM k hk) (ι g)
  have hkerCard : Nat.card f.ker ≤ 2 := by
    have hZ : Nat.card (center M) ≤ 2 := by
      by_cases h : center M = ⊥
      · rw [h]
        simp
      · have := Zassenhaus.card_center_eq_two_of_ne_bot hMperf hHS h
        omega
    refine le_trans (Nat.card_le_card_of_injective
      (fun k : f.ker => (⟨ι k.1, hkerM k.1 k.2⟩ : center M)) ?_) hZ
    intro a b h
    exact Subtype.ext (hι (congrArg Subtype.val h))
  have hKcard : Nat.card K = 20160 * Nat.card (center K) := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (center K)
    rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_fin] at h1
    rw [h1]
    norm_num [Nat.factorial]
  have hKge : 20160 ≤ Nat.card K := by
    rw [hKcard]
    have : 0 < Nat.card (center K) := Nat.card_pos
    omega
  have hrange : Nat.card K = Nat.card f.ker * Nat.card f.range :=
    (Subgroup.card_ker_mul_card_range f).symm
  have hrangeC : ∀ z ∈ center K, f.range ≤ centralizer ({f z} : Set (M ⧸ center M)) := by
    intro z hz
    rintro _ ⟨k, rfl⟩
    rw [mem_centralizer_singleton_iff, ← map_mul, ← map_mul, Subgroup.mem_center_iff.1 hz k]
  have hprime : ∀ p : ℕ, p.Prime → p ∣ Nat.card (center K) → p = 2 := by
    intro p hp hpd
    by_contra hp2
    by_cases hp3 : p = 3
    · subst hp3
      obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := center K) 3 hpd
      have hz3 : (z : K) ^ 3 = 1 := by
        have := pow_orderOf_eq_one z
        rw [hz] at this
        exact congrArg Subtype.val this
      have hfz : f z ≠ 1 := by
        intro h1
        have hmem : (z : K) ∈ f.ker := h1
        have hd := Subgroup.orderOf_dvd_natCard f.ker hmem
        rw [Subgroup.orderOf_coe, hz] at hd
        have := Nat.le_of_dvd Nat.card_pos hd
        omega
      have hfo : orderOf (f z) = 3 := orderOf_eq_prime (by rw [← map_pow, hz3, map_one]) hfz
      have hle := Subgroup.card_le_of_le (hrangeC z z.2)
      have h720 := card_centralizer_three_le hHS hfo
      have hK2 : Nat.card K ≤ 2 * 720 := hrange ▸ Nat.mul_le_mul hkerCard (hle.trans h720)
      omega
    · have hp5 : 3 < p := by
        have := hp.two_le
        omega
      exact CFSG.RankThree.PartOne.Mult.alternating_center_small_primes (n := 8) (by norm_num) e
        hp hp5 hpd
  have hpow2 : IsPGroup 2 (center K) := by
    have hpos : Nat.card (center K) ≠ 0 := Nat.card_pos.ne'
    exact IsPGroup.of_card (Nat.eq_prime_pow_of_unique_prime_dvd hpos fun hp hd =>
      hprime _ hp hd)
  let η : K →* alternatingGroup (Fin 8) := e.toMonoidHom.comp (QuotientGroup.mk' (center K))
  have hηs : Function.Surjective η := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hηker : η.ker = center K := by
    ext x
    rw [MonoidHom.mem_ker]
    show e (QuotientGroup.mk x) = 1 ↔ x ∈ center K
    rw [MulEquiv.map_eq_one_iff, QuotientGroup.eq_one_iff]
  have hcard2 : Nat.card (center K) ≤ 2 := by
    have := ComponentInitial.alternating_perfect_central_two_kernel_order_at_most_two
      (n := 8) (by norm_num) η hηs hηker.le (hηker ▸ hpow2)
    rwa [hηker] at this
  have hcardne : Nat.card (center K) ≠ 1 := fun h => hne (Subgroup.card_eq_one.1 h)
  have hcard : Nat.card (center K) = 2 := by
    have : 0 < Nat.card (center K) := Nat.card_pos
    omega
  have hsq : ∀ g ∈ center K, g ^ 2 = 1 := by
    intro g hg
    have h := pow_card_eq_one' (G := center K) (x := (⟨g, hg⟩ : center K))
    rw [hcard] at h
    exact congrArg Subtype.val h
  have hfZ : ∀ g ∈ center K, f g = 1 := by
    intro g hg
    by_contra hfg
    have hgsq : (f g) ^ 2 = 1 := by rw [← map_pow, hsq g hg, map_one]
    have hgo : orderOf (f g) = 2 := orderOf_eq_prime hgsq hfg
    have hle := Subgroup.card_le_of_le (hrangeC g hg)
    have h7680 : Nat.card ↥(centralizer ({f g} : Set (M ⧸ center M))) ≤ 7680 := by
      rcases Zassenhaus.card_centralizer_of_involution_hs hHS (f g) hgo with h | h <;> omega
    have hK2 : Nat.card K ≤ 2 * 7680 := hrange ▸ Nat.mul_le_mul hkerCard (hle.trans h7680)
    omega
  have hkerZ : f.ker = center K := le_antisymm hkerC fun g hg => hfZ g hg
  obtain ⟨⟨z0, hz0⟩, hz01'⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hne
  have hz01 : z0 ≠ 1 := fun h => hz01' (Subtype.ext h)
  have hZM : center M ≠ ⊥ := by
    intro h
    have h1 : ι z0 ∈ center M := hkerM z0 (by rw [hkerZ]; exact hz0)
    rw [h, Subgroup.mem_bot] at h1
    exact hz01 (hι (h1.trans (map_one ι).symm))
  have hZMcard : Nat.card (center M) = 2 := Zassenhaus.card_center_eq_two_of_ne_bot hMperf hHS hZM
  obtain ⟨x, z, hxη, hx3, hzc, hz1, hz2, hxx⟩ := alt_cover_structure (m := 6) (by norm_num) η
    hηs hηker.le (hηker ▸ hpow2) (by rw [hηker]; exact hne)
  have hzK : z ∈ f.ker := by rw [hkerZ]; exact hzc
  have hfz1 : f z = 1 := hzK
  have hy3 : ∀ i, (f (x i)) ^ 3 = 1 := fun i => by rw [← map_pow, hx3 i, map_one]
  have hyy : ∀ i j, i ≠ j → orderOf (f (x i) * f (x j)) = 2 := by
    intro i j hij
    refine orderOf_eq_prime ?_ ?_
    · rw [← map_mul, ← map_pow, hxx i j hij, hfz1]
    · intro h1
      rw [← map_mul] at h1
      have hm : x i * x j ∈ center K := by rw [← hkerZ]; exact h1
      have := hsq _ hm
      rw [hxx i j hij] at this
      exact hz1 this
  have hy1 : ∀ i, f (x i) ≠ 1 := by
    intro i h1
    obtain ⟨j, hj⟩ := exists_ne i
    have hij := hyy i j (Ne.symm hj)
    rw [h1, one_mul] at hij
    have h3 := hy3 j
    have h2 : (f (x j)) ^ 2 = 1 := by rw [← hij]; exact pow_orderOf_eq_one _
    have : f (x j) = 1 := by
      calc f (x j) = (f (x j)) ^ 3 * ((f (x j)) ^ 2)⁻¹ := by group
        _ = 1 := by rw [h3, h2]; simp
    rw [this] at hij
    simp at hij
  have hyo : ∀ i, orderOf (f (x i)) = 3 := fun i => orderOf_eq_prime (hy3 i) (hy1 i)
  have hclique := card_centralizer_four_clique hHS (hyo 0) (hyo 1) (hyo 2) (hyo 3)
    (hyy 0 1 (by decide)) (hyy 0 2 (by decide)) (hyy 0 3 (by decide)) (hyy 1 2 (by decide))
    (hyy 1 3 (by decide)) (hyy 2 3 (by decide))
  have hmk : (QuotientGroup.mk (ι (x 0 * x 1)) : M ⧸ center M) = f (x 0) * f (x 1) := by
    rw [map_mul, QuotientGroup.mk_mul]
    rfl
  have hsqM := sq_eq_one_of_card_centralizer hMperf hZMcard hHS (m := ι (x 0 * x 1))
    (by rw [hmk]; exact hyy 0 1 (by decide)) (by rw [hmk]; exact hclique)
  have hsqK : (x 0 * x 1) ^ 2 = 1 := by
    apply hι
    rw [map_pow, map_one]
    exact hsqM
  rw [hxx 0 1 (by decide)] at hsqK
  exact hz1 hsqK

theorem kgHSNoDoubleA8_proved :
    KGHSNoDoubleA8 := by
  intro G _ _ M K hMq _ hHS hKM hKq he
  exact noDoubleA8_core (M := ↥M) (K := ↥K) hMq hHS (Subgroup.inclusion hKM)
    (Subgroup.inclusion_injective hKM) hKq he.some

end CFSG.EvenSporadicStandard.HSStd.PumpHS
