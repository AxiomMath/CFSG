module

public import CFSG.LocalAnalysis.LyonsUnitaryFour.FiveColumns.ActualColumns
public import CFSG.LocalAnalysis.LyonsUnitaryFour.FiveColumns.GlobalOrderSums
public import CFSG.LocalAnalysis.LyonsUnitaryFour.FiveColumns.InvolutionData
public import CFSG.LocalAnalysis.LyonsUnitaryFour.SylowColumns.OrderFourColumn
public import CFSG.LocalAnalysis.LyonsUnitaryFour.SylowColumns.OrderFifteenRestriction

public section

open scoped BigOperators

namespace CFSG.LyonsUnitaryFour

open CFSG.TwoRankLowerBound.Helpers CFSG.Wreathed CFSG.RankTwoShapes

variable {G : Type} [Group G] [Fintype G]

theorem lyons_actual_multiplicities [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a)
    {T : Type} [Group T] (hT : CFSG.Assembly.LowTwoRank.StatedClassicalModel T .PSU 3 2 2)
    (S : Sylow 2 G) (U : Sylow 2 T) (hSU : Nonempty ((S : Subgroup G) ≃* (U : Subgroup T)))
    (hd : (((S : Subgroup G) ⊔ Subgroup.centralizer ((S : Subgroup G) : Set G)).subgroupOf
      (Subgroup.normalizer ((S : Subgroup G) : Set G))).index = 15)
    (basis : FiniteIrreducibleCharacterBasis G) (principal : basis.index)
    (hprincipal : (basis.representation principal).character = 1)
    {z : G} (hzZ : z ∈ (Subgroup.center (S : Subgroup G)).map (S : Subgroup G).subtype)
    (hz1 : z ≠ 1) {t : G} (htS : t ∈ (S : Subgroup G)) (ht4 : orderOf t = 4)
    (χ : basis.index) (u s : ℤ) (hu : (u : ℂ) = (basis.representation χ).character t)
    (hs : (s : ℂ) = (basis.representation χ).character z) :
    ∃ a b c : ℕ, labelDegree basis χ = a + 15 * b + 12 * c ∧ s = a + 15 * b - 4 * c ∧
      u = a - b ∧ (χ ≠ principal → 1 ≤ c) := by
  obtain ⟨-, -, hmult⟩ :=
    lyons_order_fifteen_sylow_restriction_multiplicities hnonab hT S U hSU hd
  obtain ⟨a, b, c, -, -, hvals, hirr⟩ := hmult (basis.representation χ).vector
    (basis.representation χ).representation
  obtain ⟨h1, hz, ht, -⟩ := hvals z hzZ hz1 t htS ht4
  refine ⟨a, b, c, ?_, ?_, ?_, ?_⟩
  · have h := labelDegree_cast basis χ
    rw [FiniteComplexRepresentation.character, h1] at h
    exact_mod_cast h
  · rw [FiniteComplexRepresentation.character, hz] at hs
    exact_mod_cast hs
  · rw [FiniteComplexRepresentation.character, ht] at hu
    exact_mod_cast hu
  · intro hχ
    refine (hirr (basis.irreducible χ) fun h1' => hχ (basis.distinct ?_)).1
    exact h1'.trans hprincipal.symm

theorem lyons_actual_degree_facts [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a)
    {T : Type} [Group T] (hT : CFSG.Assembly.LowTwoRank.StatedClassicalModel T .PSU 3 2 2)
    (S : Sylow 2 G) (U : Sylow 2 T) (hSU : Nonempty ((S : Subgroup G) ≃* (U : Subgroup T)))
    (basis : FiniteIrreducibleCharacterBasis G) (principal : basis.index)
    (hprincipal : (basis.representation principal).character = 1) :
    (∀ χ, χ ≠ principal → 12 ≤ labelDegree basis χ) ∧
    ∀ χ, (labelDegree basis χ).natAbs ∣ Nat.card G := by
  refine ⟨fun χ hχ => ?_, fun χ => ?_⟩
  · have h := (lyons_sylow_character_congruences_and_degree_bound hnonab hT S U hSU).2
      (basis.representation χ).vector (basis.representation χ).representation
      (basis.irreducible χ) fun h1 => hχ (basis.distinct (h1.trans hprincipal.symm))
    unfold labelDegree
    exact_mod_cast h
  · have : (basis.representation χ).representation.IsIrreducible := basis.irreducible χ
    unfold labelDegree
    rw [Int.natAbs_natCast]
    exact CFSG.Theory.Character.irreducible_dimension_dvd_group_order
      (basis.representation χ).representation

theorem lyons_actual_reciprocal_sums [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a)
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
    (hSC : (S : Subgroup G) ≤ Subgroup.centralizer (Subgroup.zpowers z : Set G))
    (hcentral : ∀ v (hv : v ∈ (Subgroup.center (S : Subgroup G)).map (S : Subgroup G).subtype),
      π ⟨v, hSC (Subgroup.map_subtype_le _ hv)⟩ ∈ (Subgroup.center S₀).map S₀.subtype)
    (hinj : ∀ v (hv : v ∈ (Subgroup.center (S : Subgroup G)).map (S : Subgroup G).subtype)
      v' (hv' : v' ∈ (Subgroup.center (S : Subgroup G)).map (S : Subgroup G).subtype),
      π ⟨v, hSC (Subgroup.map_subtype_le _ hv)⟩ = π ⟨v', hSC (Subgroup.map_subtype_le _ hv')⟩ →
        v = v')
    (y : Subgroup.centralizer (Subgroup.zpowers z : Set G)) (hy : π y = h)
    (hyodd : Nat.Coprime 2 (orderOf (y : G)))
    (dt : basis.index → ℤ) (d : Fin 5 → basis.index → ℤ)
    (hdt : ∀ χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal,
      ((dt χ : ℤ) : ℂ) = (basis.representation χ).character t)
    (hd : ∀ χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal,
      ∀ i : Fin 5, ((d i χ : ℤ) : ℂ) =
        fiveFourier (basis.representation χ).character lyonsZeta z y i) :
    ∑ χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal,
        ((∑ j, d j χ : ℤ) : ℚ) ^ 2 * dt χ / labelDegree basis χ = 0 ∧
    ∀ i : Fin 5, ∑ χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal,
        ((∑ j, d j χ : ℤ) : ℚ) ^ 2 * d i χ / labelDegree basis χ =
      128 * (Nat.card (Subgroup.centralizer ({z} : Set G)) : ℚ) ^ 3 /
        (Nat.card G * (Nat.card (Subgroup.centralizer
          (((Subgroup.center (S : Subgroup G)).map (S : Subgroup G).subtype : Subgroup G) :
            Set G)) : ℚ) ^ 2) := by
  classical
  obtain ⟨-, -, hsqZ, hZcard, -, -, -, -, -, -, hall, -⟩ :=
    lyons_unitary_four_fusion_and_centralizers hnonab hT S U hSU
  have hZS : (Subgroup.center (S : Subgroup G)).map (S : Subgroup G).subtype ≤
      (S : Subgroup G) := Subgroup.map_subtype_le _
  have hZcardG : Nat.card ((Subgroup.center (S : Subgroup G)).map (S : Subgroup G).subtype) =
      4 := by
    rw [Subgroup.card_map_of_injective (Subgroup.subtype_injective _), hZcard]
  have hsq : ∀ x ∈ (S : Subgroup G), x * x = 1 ↔
      x ∈ (Subgroup.center (S : Subgroup G)).map (S : Subgroup G).subtype := by
    intro x hx
    rw [← pow_two]
    exact hsqZ x hx
  have hz2 : z * z = 1 := (hsq z (hZS hzZ)).mpr hzZ
  have hsum : ∀ χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal,
      ((∑ j, d j χ : ℤ) : ℂ) = (basis.representation χ).character z := by
    intro χ hχ
    push_cast
    rw [← sum_fiveFourier (basis.representation χ).character lyonsZeta_isPrimitiveRoot z (y : G),
      ← Fin.sum_univ_eq_sum_range (fun i => fiveFourier (basis.representation χ).character
        lyonsZeta z (y : G) i)]
    exact Finset.sum_congr rfl fun i _ => hd χ hχ i
  refine ⟨?_, fun i => ?_⟩
  ·
    have hcol := ((lyons_order_four_principal_column hT S U hSU basis ideal principal hprincipal
      htS ht4).2.2.2.2.2.2 z hz2).2
    apply Rat.cast_injective (α := ℂ)
    push_cast
    rw [← hcol]
    refine Finset.sum_congr rfl fun χ hχ => ?_
    have h1 := hsum χ hχ
    push_cast at h1
    rw [h1, hdt χ hχ, labelDegree_cast]
  obtain ⟨w, hwZ, hw1, hwz⟩ := exists_third_mem_four hZcardG z
  have hcentral' : ∀ v (hv : v ∈ (Subgroup.center (S : Subgroup G)).map
      (S : Subgroup G).subtype), π ⟨v, hSC (hZS hv)⟩ ∈ Subgroup.center L :=
    fun v hv => hL.center_le_center (hcentral v hv)
  obtain ⟨hN, hNz, hNw, hNzw⟩ := lyons_involution_counts S _ hZS hsq hZcardG hall hzZ hz1 π hSC
    hcentral' hinj hwZ hw1 hwz
  obtain ⟨localBasis⟩ := finiteIrreducibleCharacterBasis_exists
    (G := Subgroup.centralizer (Subgroup.zpowers z : Set G))
  obtain ⟨localPrincipal, hlocalPrincipal⟩ := finiteIrreducibleCharacterBasis_contains_irreducible
    localBasis (principalFiniteComplexRepresentation _)
    (principalFiniteComplexRepresentation_isIrreducible _)
  rw [principalFiniteComplexRepresentation_character] at hlocalPrincipal
  obtain ⟨quotientBasis⟩ := finiteIrreducibleCharacterBasis_exists (G := L)
  have hzc : centralizerSelf z = ⟨z, hSC (hZS hzZ)⟩ := rfl
  have hone : ∀ v (hv : v ∈ (Subgroup.center (S : Subgroup G)).map (S : Subgroup G).subtype),
      v ≠ 1 → π ⟨v, hSC (hZS hv)⟩ ≠ 1 := by
    intro v hv hv1 hπv
    apply hv1
    refine hinj v hv 1 (Subgroup.one_mem _) ?_
    rw [hπv]
    exact (map_one π).symm
  have hsq' : ∀ v (hv : v ∈ (Subgroup.center (S : Subgroup G)).map (S : Subgroup G).subtype),
      π ⟨v, hSC (hZS hv)⟩ * π ⟨v, hSC (hZS hv)⟩ = 1 := by
    intro v hv
    rw [← map_mul]
    have : (⟨v, hSC (hZS hv)⟩ * ⟨v, hSC (hZS hv)⟩ :
        Subgroup.centralizer (Subgroup.zpowers z : Set G)) = 1 :=
      Subtype.ext ((hsq v (hZS hv)).mpr hv)
    rw [this, map_one]
  set n : ℂ := ((Finset.univ.filter fun x : Subgroup.centralizer (Subgroup.zpowers z : Set G) =>
      IsConj (x : G) z ∧ π x = π ⟨w, hSC (hZS hwZ)⟩).card : ℂ) with hn
  have hDpos : (Nat.card (Subgroup.centralizer
      (((Subgroup.center (S : Subgroup G)).map (S : Subgroup G).subtype : Subgroup G) :
        Set G)) : ℂ) ≠ 0 := by
    exact_mod_cast Nat.card_pos.ne'
  have hNzw' : ((Finset.univ.filter fun x : Subgroup.centralizer (Subgroup.zpowers z : Set G) =>
      IsConj (x : G) z ∧ π x = π (centralizerSelf z) * π ⟨w, hSC (hZS hwZ)⟩).card : ℂ) = n :=
    mul_right_cancel₀ hDpos (hNzw.trans hNw.symm)
  have hE := global_order_sum_fourier basis ideal principal hprincipal hz2 localBasis
    localPrincipal hlocalPrincipal hL quotientBasis π hπ hker y hy hyodd
    (by rw [hzc]; exact hcentral z hzZ) (hcentral w hwZ) (by rw [hzc]; exact hsq' z hzZ)
    (hsq' w hwZ) (by rw [hzc]; exact hone z hzZ hz1) (hone w hwZ hw1)
    (fun hwz' => hwz (hinj w hwZ z hzZ (by rw [hwz']; rfl))) n hN hNz rfl hNzw'
    lyonsZeta i
  have hCC : Nat.card (Subgroup.centralizer (Subgroup.zpowers z : Set G)) =
      Nat.card (Subgroup.centralizer ({z} : Set G)) := by
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  rw [hCC, hL.card_eq] at hE
  rw [hCC] at hNw
  have hGpos : (Nat.card G : ℂ) ≠ 0 := by exact_mod_cast Nat.card_pos.ne'
  have hCpos : (Nat.card (Subgroup.centralizer ({z} : Set G)) : ℂ) ≠ 0 := by
    exact_mod_cast Nat.card_pos.ne'
  apply Rat.cast_injective (α := ℂ)
  push_cast
  have hrw : ∑ χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal,
      (∑ j, (d j χ : ℂ)) ^ 2 * (d i χ : ℂ) / (labelDegree basis χ : ℂ) =
      ∑ χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal,
        (basis.representation χ).character z * (basis.representation χ).character z *
          fiveFourier (basis.representation χ).character lyonsZeta z (y : G) i /
            (basis.representation χ).character 1 := by
    refine Finset.sum_congr rfl fun χ hχ => ?_
    have h1 := hsum χ hχ
    push_cast at h1
    rw [h1, hd χ hχ i, labelDegree_cast, pow_two]
  rw [hrw]
  apply mul_left_cancel₀ hGpos
  rw [hE]
  have hn' : n = (Nat.card (Subgroup.centralizer ({z} : Set G)) : ℂ) /
      (Nat.card (Subgroup.centralizer
        (((Subgroup.center (S : Subgroup G)).map (S : Subgroup G).subtype : Subgroup G) :
          Set G)) : ℂ) := by
    rw [eq_div_iff hDpos]
    exact hNw
  rw [hn']
  field_simp
  ring

end CFSG.LyonsUnitaryFour
