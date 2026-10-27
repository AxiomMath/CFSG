module

public import CFSG.HardMathSupport.Solomon.Coordinator.L3C143AltExc
public import CFSG.RankThree.PartTwo.KFacts.L34Sylow

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.HardMathSupport.Solomon.LocalBalance Equiv

theorem exists_commuting_three_five :
    ∃ x y : alternatingGroup (Fin 8), x ^ 3 = 1 ∧ x ≠ 1 ∧ y ^ 5 = 1 ∧ y ≠ 1 ∧ x * y = y * x := by
  refine ⟨⟨swap 0 1 * swap 1 2, Perm.mem_alternatingGroup.2 (by decide +kernel)⟩,
    ⟨swap 3 4 * swap 4 5 * swap 5 6 * swap 6 7, Perm.mem_alternatingGroup.2 (by decide +kernel)⟩,
    ?_, ?_, ?_, ?_, ?_⟩
  · exact Subtype.ext (by decide +kernel)
  · intro h
    have := congrArg Subtype.val h
    revert this
    decide +kernel
  · exact Subtype.ext (by decide +kernel)
  · intro h
    have := congrArg Subtype.val h
    revert this
    decide +kernel
  · exact Subtype.ext (by decide +kernel)

theorem false_of_projectiveSL_alt_eight {F : Type} [Field F] (hF : Nat.card F = 4)
    (ε : CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL 3 F ≃*
      alternatingGroup (Fin 8)) : False := by
  obtain ⟨x, y, hx3, hx1, hy5, hy1, hxy⟩ := exists_commuting_three_five
  have hcardA : Nat.card (alternatingGroup (Fin 8)) = 20160 := by
    have := two_mul_nat_card_alternatingGroup (α := Fin 8)
    rw [Nat.card_perm, Nat.card_fin] at this
    have h8 : (8 : ℕ).factorial = 40320 := by decide
    omega
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hox : orderOf x = 3 := orderOf_eq_prime hx3 hx1
  have hoy : orderOf y = 5 := orderOf_eq_prime hy5 hy1
  obtain ⟨P, hP⟩ := IsPGroup.exists_le_sylow (p := 3) (G := alternatingGroup (Fin 8))
    (P := Subgroup.zpowers x)
    (IsPGroup.of_card (p := 3) (n := 1) (by rw [Nat.card_zpowers, hox]; norm_num))
  have hPcard : Nat.card P = 9 := by
    rw [Sylow.card_eq_multiplicity, hcardA]
    have : (20160 : ℕ).factorization 3 = 2 := by
      have h : (20160 : ℕ) = 3 ^ 2 * 2240 := by norm_num
      exact CFSG.RankThree.Asc83Table.factorization_eq_of_eq Nat.prime_three h (by norm_num)
    rw [this]
    norm_num
  have hEcard : Nat.card ((P : Subgroup (alternatingGroup (Fin 8))).map ε.symm.toMonoidHom) = 9 := by
    rw [← Nat.card_congr ((P : Subgroup (alternatingGroup (Fin 8))).equivMapOfInjective
      ε.symm.toMonoidHom ε.symm.injective).toEquiv]
    exact hPcard
  have hxE : ε.symm x ∈ (P : Subgroup (alternatingGroup (Fin 8))).map ε.symm.toMonoidHom :=
    ⟨x, hP (Subgroup.mem_zpowers x), rfl⟩
  have hx1' : ε.symm x ≠ 1 := fun h => hx1 (ε.symm.injective (h.trans (map_one _).symm))
  have hC := CFSG.RankThree.PartTwo.KFacts.L34.centralizer_eq_of_card_eq_nine hF hEcard hxE hx1'
  have hyC : ε.symm y ∈ Subgroup.centralizer ({ε.symm x} : Set _) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    rw [← map_mul, ← map_mul, hxy]
  rw [hC] at hyC
  have hdvd := Subgroup.orderOf_dvd_natCard _ hyC
  rw [hEcard, MulEquiv.orderOf_eq, hoy] at hdvd
  omega

theorem false_of_alt {K : Type} [Group K] [Finite K] (hq : CFSG.Open.IsQuasisimple K)
    (h : IsSLThreeExc K ∨ IsSUThreeExc K) {β : Type} [Fintype β] [DecidableEq β]
    (hβ : 5 ≤ Nat.card β) (e : (K ⧸ Subgroup.center K) ≃* alternatingGroup β) : False := by
  obtain ⟨h1, h2, h3⟩ := exc_facts hq h
  set L := Nat.card (K ⧸ Subgroup.center K) with hLdef
  have hLβ : L = Nat.card (alternatingGroup β) := Nat.card_congr e.toEquiv
  have hnt : Nontrivial β := by
    rw [← Finite.one_lt_card_iff_nontrivial]
    omega
  have h2L : 2 * L = (Nat.card β).factorial := by
    rw [hLβ, two_mul_nat_card_alternatingGroup, Nat.card_perm]
  set b := Nat.card β with hb
  have hb8 : b ≤ 8 := by
    by_contra hlt
    have h9 : (9 : ℕ).factorial ∣ b.factorial := Nat.factorial_dvd_factorial (by omega)
    have h81 : 3 ^ 4 ∣ 2 * L := by
      rw [h2L]
      exact (show 3 ^ 4 ∣ (9 : ℕ).factorial by decide).trans h9
    have h81' : 3 ^ 4 ∣ L :=
      (Nat.Coprime.pow_left 4 (by norm_num : Nat.Coprime 3 2)).dvd_of_dvd_mul_left h81
    have hL0 : L ≠ 0 := by omega
    have := (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_three hL0).1 h81'
    omega
  have hb8' : b = 8 := by
    by_contra hne
    have h7 : b ≤ 7 := by omega
    have : L ≤ 2520 := by
      have hfac : b.factorial ≤ (7 : ℕ).factorial := Nat.factorial_le h7
      have : (7 : ℕ).factorial = 5040 := by decide
      omega
    omega
  have hL20 : L = 20160 := by
    have : (8 : ℕ).factorial = 40320 := by decide
    rw [hb8'] at h2L
    omega
  obtain ⟨F, hF, hfin, hF4, ⟨e2⟩⟩ := h3 hL20
  have hcard : Fintype.card β = 8 := by rw [← Nat.card_eq_fintype_card]; exact hb8'
  exact false_of_projectiveSL_alt_eight hF4
    ((e2.symm.trans e).trans (Equiv.altCongrHom (Fintype.equivFinOfCardEq hcard)))

end CFSG.HardMathSupport.Solomon.Coordinator
