module

public import CFSG.LocalAnalysis.LyonsUnitaryFour.FiveColumns.ActualColumns
public import CFSG.LocalAnalysis.LyonsUnitaryFour.FiveColumns.ColumnConfiguration
public import CFSG.LocalAnalysis.LyonsUnitaryFour.FiveColumns.GaloisColumns
public import CFSG.LocalAnalysis.LyonsUnitaryFour.FiveColumns.LyonsGalois
public import CFSG.LocalAnalysis.LyonsUnitaryFour.FiveColumns.InvolutionData
public import CFSG.LocalAnalysis.LyonsUnitaryFour.SylowColumns.OrderFourColumn
public import CFSG.LocalAnalysis.LyonsUnitaryFour.SylowColumns.Congruences

public section

open scoped BigOperators

namespace CFSG.LyonsUnitaryFour

open CFSG.TwoRankLowerBound.Helpers CFSG.Wreathed CFSG.RankTwoShapes

variable {G : Type} [Group G] [Fintype G]

theorem lyons_actual_column_facts [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a)
    {T : Type} [Group T] (hT : CFSG.Assembly.LowTwoRank.StatedClassicalModel T .PSU 3 2 2)
    (S : Sylow 2 G) (U : Sylow 2 T) (hSU : Nonempty ((S : Subgroup G) ≃* (U : Subgroup T)))
    (basis : FiniteIrreducibleCharacterBasis G) (ideal : Ideal ComplexAlgebraicIntegers)
    [ideal.IsMaximal] [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2] (principal : basis.index)
    (hprincipal : (basis.representation principal).character = 1)
    {z : G} (hzZ : z ∈ (Subgroup.center (S : Subgroup G)).map (S : Subgroup G).subtype)
    (hz1 : z ≠ 1) {t : G} (htS : t ∈ (S : Subgroup G)) (ht4 : orderOf t = 4)
    {L : Type} [Group L] [Fintype L] {S₀ : Subgroup L} {h : L} (hL : UnitaryFourByFive S₀ h)
    (π : Subgroup.centralizer (Subgroup.zpowers z : Set G) →* L) (hπ : Function.Surjective π)
    (hker : ¬ 2 ∣ Nat.card π.ker)
    (hz₀ : π (centralizerSelf z) ∈ (Subgroup.center S₀).map S₀.subtype)
    (y : Subgroup.centralizer (Subgroup.zpowers z : Set G)) (hy : π y = h)
    (hyodd : Nat.Coprime 2 (orderOf (y : G))) :
    (∀ χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal,
      ((actualDt basis t χ : ℤ) : ℂ) = (basis.representation χ).character t) ∧
    (∀ χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal, ∀ i : Fin 5,
      ((actualD basis z y i χ : ℤ) : ℂ) =
        fiveFourier (basis.representation χ).character lyonsZeta z y i) ∧
    (∀ χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal,
      ((∑ i, actualD basis z y i χ : ℤ) : ℂ) = (basis.representation χ).character z) ∧
    ∑ χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal,
      actualDt basis t χ * actualDt basis t χ = 16 ∧
    (∀ i, ∑ χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal,
      actualDt basis t χ * actualD basis z y i χ = 0) ∧
    (∀ i l, ∑ χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal,
      actualD basis z y i χ * actualD basis z y l χ = if i = l then 16 else 12) ∧
    ∑ χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal,
      actualDt basis t χ * labelDegree basis χ = 0 ∧
    (∀ i, ∑ χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal,
      actualD basis z y i χ * labelDegree basis χ = 0) ∧
    (∀ χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal,
      actualDt basis t χ ≡ ∑ i, actualD basis z y i χ [ZMOD 4]) ∧
    (∀ χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal,
      ∑ i, actualD basis z y i χ ≠ 0) ∧
    (∃ τ : Equiv.Perm basis.index,
      (∀ χ, τ χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal ↔
        χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal) ∧
      (∀ χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal,
        actualDt basis t (τ χ) = actualDt basis t χ) ∧
      (∀ χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal, ∀ i,
        actualD basis z y i (τ χ) = actualD basis z y (3 * i) χ) ∧
      (∀ χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal,
        labelDegree basis (τ χ) = labelDegree basis χ)) ∧
    actualDt basis t principal = 1 ∧
    (∀ i, actualD basis z y i principal = if i = 0 then 1 else 0) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hcard, -, hsqZ, -⟩ := lyons_unitary_four_fusion_and_centralizers hnonab hT S U hSU
  have hZS : (Subgroup.center (S : Subgroup G)).map (S : Subgroup G).subtype ≤
      (S : Subgroup G) := Subgroup.map_subtype_le _
  have hz2 : z ^ 2 = 1 := (hsqZ z (hZS hzZ)).mpr hzZ
  have hzord : orderOf z ∣ 2 ^ 1 := orderOf_dvd_of_pow_eq_one (by rw [pow_one]; exact hz2)
  have htord : orderOf t ∣ 2 ^ 2 := by rw [ht4]; norm_num
  have hzt : ¬ IsConj z t := by
    intro hconj
    obtain ⟨c, hc⟩ := isConj_iff.mp hconj
    have ht2 : t ^ 2 = 1 := by rw [← hc, conj_pow, hz2, mul_one, mul_inv_cancel]
    have := orderOf_dvd_of_pow_eq_one ht2
    rw [ht4] at this
    exact absurd (Nat.le_of_dvd (by norm_num) this) (by norm_num)
  have hzy : Commute z (y : G) :=
    (mem_centralizer_zpowers_iff.mp y.2)
  obtain ⟨localBasis⟩ := finiteIrreducibleCharacterBasis_exists
    (G := Subgroup.centralizer (Subgroup.zpowers z : Set G))
  obtain ⟨localPrincipal, hlocalPrincipal⟩ := finiteIrreducibleCharacterBasis_contains_irreducible
    localBasis (principalFiniteComplexRepresentation _)
    (principalFiniteComplexRepresentation_isIrreducible _)
  rw [principalFiniteComplexRepresentation_character] at hlocalPrincipal
  obtain ⟨quotientBasis⟩ := finiteIrreducibleCharacterBasis_exists (G := L)
  have hζ := lyonsZeta_isPrimitiveRoot
  obtain ⟨-, -, htint, -, htt, hwt, -⟩ :=
    lyons_order_four_principal_column hT S U hSU basis ideal principal hprincipal htS ht4
  have hdt : ∀ χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal,
      ((actualDt basis t χ : ℤ) : ℂ) = (basis.representation χ).character t :=
    fun χ _ => actualDt_spec basis t χ (htint χ)
  have hd : ∀ χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal,
      ∀ i : Fin 5, ((actualD basis z y i χ : ℤ) : ℂ) =
        fiveFourier (basis.representation χ).character lyonsZeta z y i :=
    fun χ hχ i => actualD_spec basis z y i χ (global_fiveFourier_integer basis ideal principal
      hprincipal hz2 localBasis localPrincipal hlocalPrincipal hL quotientBasis π hπ hker hz₀ y
      hy hyodd hζ χ hχ i)
  have hsum : ∀ χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal,
      ((∑ i, actualD basis z y i χ : ℤ) : ℂ) = (basis.representation χ).character z := by
    intro χ hχ
    push_cast
    rw [← sum_fiveFourier (basis.representation χ).character hζ z (y : G),
      ← Fin.sum_univ_eq_sum_range (fun i => fiveFourier (basis.representation χ).character
        lyonsZeta z (y : G) i)]
    exact Finset.sum_congr rfl fun i _ => hd χ hχ i
  have hconj : ∀ n : ℤ, starRingEnd ℂ (n : ℂ) = n := fun n => map_intCast _ n
  refine ⟨hdt, hd, hsum, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    apply Int.cast_injective (α := ℂ)
    push_cast
    rw [← htt]
    refine Finset.sum_congr rfl fun χ hχ => ?_
    rw [hdt χ hχ, pow_two]
  ·
    intro i
    have hmix := global_fiveFourier_mixed basis ideal principal hzord htord hzt hyodd hzy
      lyonsZeta i
    apply Int.cast_injective (α := ℂ)
    push_cast
    rw [← hmix]
    refine Finset.sum_congr rfl fun χ hχ => ?_
    rw [← hdt χ hχ, hconj, hd χ hχ i]
  ·
    intro i l
    have hgram := global_fiveFourier_gram basis ideal principal hprincipal hz2 localBasis
      localPrincipal hlocalPrincipal hL quotientBasis π hπ hker hz₀ y hy hyodd hζ i.isLt l.isLt
    apply Int.cast_injective (α := ℂ)
    push_cast
    have hcond : ((i : ℕ) = (l : ℕ)) ↔ i = l := Fin.val_eq_val _ _
    rw [show (if i = l then (16 : ℂ) else 12) = if (i : ℕ) = (l : ℕ) then 16 else 12 by
      simp only [hcond], ← hgram]
    refine Finset.sum_congr rfl fun χ hχ => ?_
    rw [← hd χ hχ i, ← hd χ hχ l, hconj]
  ·
    apply Int.cast_injective (α := ℂ)
    push_cast
    rw [← hwt]
    refine Finset.sum_congr rfl fun χ hχ => ?_
    rw [hdt χ hχ, labelDegree_cast, mul_comm]
  ·
    intro i
    have hdeg := global_fiveFourier_degree basis ideal principal hzord hz1 hyodd hzy lyonsZeta i
    apply Int.cast_injective (α := ℂ)
    push_cast
    rw [← hdeg]
    refine Finset.sum_congr rfl fun χ hχ => ?_
    rw [hd χ hχ i, labelDegree_cast, mul_comm]
  ·
    intro χ hχ
    obtain ⟨-, -, -, k, hk⟩ := (lyons_sylow_character_congruences_and_degree_bound hnonab hT S
      U hSU).1 (basis.representation χ).vector (basis.representation χ).representation z hzZ hz1
      t htS ht4
    rw [Int.modEq_iff_dvd]
    refine ⟨k, Int.cast_injective (α := ℂ) ?_⟩
    have h1 := hsum χ hχ
    have h2 := hdt χ hχ
    push_cast at h1 h2 ⊢
    rw [h1, h2]
    exact hk
  ·
    intro χ hχ hzero
    apply principal_block_character_ne_zero_of_centralizes_sylow basis ideal 2 principal
      hprincipal χ hχ S z (Subgroup.mem_centralizer_iff.mpr fun s hs =>
        (mem_map_center_iff.mp hzZ).2 s hs)
    rw [← hsum χ hχ, hzero, Int.cast_zero]
  ·
    have h2 : 2 ∣ Nat.card G := by
      have := Subgroup.card_subgroup_dvd_card (S : Subgroup G)
      rw [hcard] at this
      exact (by norm_num : 2 ∣ 64).trans this
    have h5 : 5 ∣ Nat.card G := by
      have hy5 : 5 ∣ orderOf y := by
        rw [← hL.orderOf_h, ← hy]
        exact orderOf_map_dvd π y
      rw [← Subgroup.orderOf_coe] at hy5
      exact hy5.trans (orderOf_dvd_natCard (y : G))
    obtain ⟨k, τ, hk2, hk5, hτ, hτdim, hτblock, hτtwo⟩ := exists_lyons_galois_perm basis ideal h2 h5
    refine ⟨τ, fun χ => hτblock principal χ hprincipal, fun χ _ => ?_, fun χ hχ i => ?_,
      fun χ _ => ?_⟩
    · unfold actualDt
      rw [hτtwo χ t 2 (by rw [show (2 : ℕ) ^ 2 = 4 by norm_num, ← ht4]; exact pow_orderOf_eq_one t)]
    · unfold actualD
      rw [global_fiveFourier_galois basis ideal principal hprincipal hz2 localBasis localPrincipal
        hlocalPrincipal hL quotientBasis π hπ hker y hy hyodd hζ τ k hk2 hk5 hτ χ hχ i,
        fiveFourier_mod _ hζ, fiveFourier_mod _ hζ _ _ ((3 * i : Fin 5) : ℕ), Fin.val_mul]
      congr 2
      simp
    · unfold labelDegree
      rw [hτdim χ]
  ·
    unfold actualDt
    rw [hprincipal, Pi.one_apply, ← Int.cast_one, intPart_intCast]
  · intro i
    unfold actualD
    rw [hprincipal]
    have h1 := fiveFourier_one (X := G) hζ z (y : G) i.isLt
    rw [show (1 : G → ℂ) = fun _ => (1 : ℂ) from rfl, h1]
    by_cases hi : i = 0
    · subst hi
      simp only [Fin.val_zero, ite_true]
      exact_mod_cast intPart_intCast 1
    · have hi' : (i : ℕ) ≠ 0 := fun h0 => hi (Fin.ext h0)
      simp only [hi', hi, ite_false]
      exact_mod_cast intPart_intCast 0

theorem lyons_actual_column_configuration [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    {T : Type} [Group T] (hT : CFSG.Assembly.LowTwoRank.StatedClassicalModel T .PSU 3 2 2)
    (S : Sylow 2 G) (U : Sylow 2 T) (hSU : Nonempty ((S : Subgroup G) ≃* (U : Subgroup T)))
    (basis : FiniteIrreducibleCharacterBasis G) (ideal : Ideal ComplexAlgebraicIntegers)
    [ideal.IsMaximal] [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2] (principal : basis.index)
    (hprincipal : (basis.representation principal).character = 1)
    {z : G} (hzZ : z ∈ (Subgroup.center (S : Subgroup G)).map (S : Subgroup G).subtype)
    (hz1 : z ≠ 1) {t : G} (htS : t ∈ (S : Subgroup G)) (ht4 : orderOf t = 4)
    {L : Type} [Group L] [Fintype L] {S₀ : Subgroup L} {h : L} (hL : UnitaryFourByFive S₀ h)
    (π : Subgroup.centralizer (Subgroup.zpowers z : Set G) →* L) (hπ : Function.Surjective π)
    (hker : ¬ 2 ∣ Nat.card π.ker)
    (hz₀ : π (centralizerSelf z) ∈ (Subgroup.center S₀).map S₀.subtype)
    (y : Subgroup.centralizer (Subgroup.zpowers z : Set G)) (hy : π y = h)
    (hyodd : Nat.Coprime 2 (orderOf (y : G))) :
    (coefficientBlock basis (localizedComplexIntegerRing ideal) principal).val.map
      (normalizedColumnRow (actualDt basis t) (actualD basis z y)) ∈ lyonsConfigurations := by
  classical
  obtain ⟨-, -, -, htt, htd, hdd, hwt, hwd, hcong, hnz, ⟨τ, hτB, hτt, hτd, -⟩, hpt, hpd⟩ :=
    lyons_actual_column_facts hnonab hT S U hSU basis ideal principal hprincipal hzZ hz1 htS ht4
      hL π hπ hker hz₀ y hy hyodd
  exact lyons_column_data_mem_configurations _ (labelDegree basis) (actualDt basis t)
    (actualD basis z y) (fun χ _ => (labelDegree_pos basis χ).ne') htt htd hdd hwt hwd hcong hnz
    τ hτB hτt hτd (coefficientBlock_self_mem _ _ _) hpt hpd

end CFSG.LyonsUnitaryFour
