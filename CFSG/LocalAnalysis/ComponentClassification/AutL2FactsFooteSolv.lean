module

public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsTransport
public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsShape
public import CFSG.Walter.PSL2Facts.Odd
public import CFSG.LinearAlgebra.LinearGroups.TameProjectiveSubgroups
public import CFSG.LocalAnalysis.ComponentInitial.TwoPrimeSolvable

public noncomputable section

namespace CFSG.ComponentClassification.AutL2Facts

open CFSG Subgroup

theorem isSolvable_centralizer_of_equiv {G H : Type*} [Group G] [Group H] (e : G ≃* H) (g : G)
    (h : Group.IsSolvable (centralizer ({e g} : Set H))) :
    Group.IsSolvable (centralizer ({g} : Set G)) := by
  have hmap : (centralizer ({g} : Set G)).map e.toMonoidHom = centralizer {e g} :=
    map_centralizer_singleton e g
  let φ : centralizer ({g} : Set G) ≃* centralizer ({e g} : Set H) :=
    ((centralizer ({g} : Set G)).equivMapOfInjective e.toMonoidHom e.injective).trans
      (MulEquiv.subgroupCongr hmap)
  exact Group.isSolvable_of_isSolvable_injective (f := φ.toMonoidHom) φ.injective

theorem a7_involution_cycleType (x : alternatingGroup (Fin 7)) (hx2 : x ^ 2 = 1)
    (hx1 : x ≠ 1) : (x : Equiv.Perm (Fin 7)).cycleType = {2, 2} := by
  let g : Equiv.Perm (Fin 7) := x
  have hgpow : g ^ 2 = 1 := congrArg Subtype.val hx2
  have htypes : ∀ n, n ∈ Equiv.Perm.cycleType g → n = 2 :=
    Equiv.Perm.pow_prime_eq_one_iff.mp hgpow
  rw [← Multiset.eq_replicate_card] at htypes
  have hsupport := g.support.card_le_univ
  rw [← Equiv.Perm.sum_cycleType, htypes, Multiset.sum_replicate, smul_eq_mul] at hsupport
  norm_num at hsupport
  have hcard : Multiset.card g.cycleType ≤ 3 := by omega
  have hsign : Equiv.Perm.sign g = 1 := Equiv.Perm.mem_alternatingGroup.mp x.property
  rw [Equiv.Perm.sign_of_cycleType, htypes] at hsign
  simp at hsign
  rw [pow_add, pow_mul, Int.units_pow_two, one_mul, neg_one_pow_eq_one_iff_even] at hsign
  swap
  · decide
  interval_cases h : Multiset.card g.cycleType
  · exfalso
    apply hx1
    apply Subtype.ext
    exact Equiv.Perm.card_cycleType_eq_zero.mp h
  · simp at hsign
  · simpa [g, h] using htypes
  · contradiction

theorem isSolvable_centralizer_a7 (x : alternatingGroup (Fin 7)) (hx : orderOf x = 2) :
    Group.IsSolvable (centralizer ({x} : Set (alternatingGroup (Fin 7)))) := by
  have hx2 : x ^ 2 = 1 := orderOf_dvd_iff_pow_eq_one.mp (by rw [hx])
  have hx1 : x ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hx
    norm_num at hx
  have hc := a7_involution_cycleType x hx2 hx1
  have h48 : Nat.card (centralizer ({(x : Equiv.Perm (Fin 7))} : Set (Equiv.Perm (Fin 7)))) =
      48 := by
    rw [Equiv.Perm.nat_card_centralizer, hc]
    norm_num
  have hdvd : Nat.card (centralizer ({x} : Set (alternatingGroup (Fin 7)))) ∣ 48 := by
    rw [← h48, ← Subgroup.card_map_of_injective (alternatingGroup (Fin 7)).subtype_injective]
    apply Subgroup.card_dvd_of_le
    rintro _ ⟨y, hy, rfl⟩
    exact Subgroup.mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp hy))
  apply CFSG.LocalAnalysis.ComponentInitial.isSolvable_of_card_primeFactors_le_two
  calc (Nat.card (centralizer ({x} : Set (alternatingGroup (Fin 7))))).primeFactors.card ≤
      (48 : ℕ).primeFactors.card :=
        Finset.card_le_card (Nat.primeFactors_mono hdvd (by norm_num))
    _ = 2 := by
      rw [show (48 : ℕ) = 2 ^ 4 * 3 by norm_num, Nat.primeFactors_mul (by norm_num) (by norm_num),
        Nat.primeFactors_prime_pow (by norm_num) Nat.prime_two,
        Nat.Prime.primeFactors Nat.prime_three]
      decide

theorem footeInvolutionSolvable :
    ∀ (S : Type) [Group S] [Finite S],
      (Nonempty (S ≃* alternatingGroup (Fin 7)) ∨
        ∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧ Blueprint.LieModel S .PSL 2 p f) →
      ∀ s : S, orderOf s = 2 → Group.IsSolvable ↥(centralizer ({s} : Set S)) := by
  intro S _ _ hS s hs
  rcases hS with hA | ⟨p, f, hp, hp2, hf, hL⟩
  · obtain ⟨e⟩ := hA
    apply isSolvable_centralizer_of_equiv e s
    exact isSolvable_centralizer_a7 (e s) (by rwa [MulEquiv.orderOf_eq])
  · obtain ⟨-, -, -, h3, F, _, _, hF, ⟨e⟩⟩ := lieModel_psl2_data hL
    apply isSolvable_centralizer_of_equiv e s
    have : Fact p.Prime := ⟨hp⟩
    have hodd : Odd p := hp.odd_of_ne_two hp2
    have hes : orderOf (e s) = 2 := by rwa [MulEquiv.orderOf_eq]
    obtain ⟨h1, h3'⟩ := CFSG.Walter.psl2_centralizer_involution F hF hodd (by omega) hes
    have hqodd : Odd (p ^ f) := hodd.pow
    have hq3 : 3 ≤ p ^ f := by
      have := hp.two_le
      have : p ≤ p ^ f := by
        calc p = p ^ 1 := (pow_one p).symm
          _ ≤ p ^ f := Nat.pow_le_pow_right (by omega) hf
      rcases hodd with ⟨m, hm⟩
      omega
    have hq5 : 5 ≤ p ^ f := by
      rcases hqodd with ⟨m, hm⟩
      omega
    obtain ⟨m, hm⟩ := hqodd
    rcases Nat.even_or_odd m with ⟨k, hk⟩ | ⟨k, hk⟩
    · obtain ⟨-, ⟨φ⟩⟩ := h1 (by omega)
      have : NeZero ((p ^ f - 1) / 2) := ⟨by omega⟩
      have := CFSG.LinearGroups.isSolvable_dihedralGroup ((p ^ f - 1) / 2)
      exact Group.isSolvable_of_isSolvable_injective (f := φ.toMonoidHom) φ.injective
    · obtain ⟨-, ⟨φ⟩⟩ := h3' (by omega)
      have : NeZero ((p ^ f + 1) / 2) := ⟨by omega⟩
      have := CFSG.LinearGroups.isSolvable_dihedralGroup ((p ^ f + 1) / 2)
      exact Group.isSolvable_of_isSolvable_injective (f := φ.toMonoidHom) φ.injective

end CFSG.ComponentClassification.AutL2Facts
