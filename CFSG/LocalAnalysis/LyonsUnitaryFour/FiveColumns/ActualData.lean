module

public import CFSG.LocalAnalysis.LyonsUnitaryFour.FiveColumns.ActualColumnFacts
public import CFSG.LocalAnalysis.LyonsUnitaryFour.FiveColumns.SignedDegreeConstruction
public import CFSG.LocalAnalysis.LyonsUnitaryFour.FiveColumns.Isolation
public import CFSG.LocalAnalysis.LyonsUnitaryFour.OrderFifteen.LocalData

public section

open scoped BigOperators

namespace CFSG.LyonsUnitaryFour

open CFSG.TwoRankLowerBound.Helpers CFSG.Wreathed CFSG.RankTwoShapes

variable {G : Type} [Group G] [Fintype G]

omit [Fintype G] in
theorem unitary_four_exists_orderOf_eq_four {T : Type} [Group T]
    (hT : CFSG.Assembly.LowTwoRank.StatedClassicalModel T .PSU 3 2 2) (S : Sylow 2 G)
    (U : Sylow 2 T) (hSU : Nonempty ((S : Subgroup G) ≃* (U : Subgroup T))) :
    ∃ t ∈ (S : Subgroup G), orderOf t = 4 := by
  obtain ⟨hcard, -, hsq, hsqZ, hZcard⟩ := unitary_four_sylow_structure hT S U hSU
  obtain ⟨y, hy⟩ : ∃ y : (S : Subgroup G), y ∉ Subgroup.center (S : Subgroup G) := by
    by_contra hall
    push Not at hall
    have htop : Subgroup.center (S : Subgroup G) = ⊤ := eq_top_iff.mpr fun y _ => hall y
    rw [htop, Subgroup.card_top, hcard] at hZcard
    norm_num at hZcard
  refine ⟨y, y.2, ?_⟩
  rw [Subgroup.orderOf_coe]
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h4 : orderOf y = 2 ^ (1 + 1) := orderOf_eq_prime_pow
    (by rw [pow_one]; exact fun h => hy ((hsq y).mp h))
    (by rw [show 2 ^ (1 + 1) = 2 * 2 from rfl, pow_mul]; exact (hsq (y ^ 2)).mpr (hsqZ y))
  simpa using h4

theorem lyons_order_fifteen_actual_data [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a)
    {T : Type} [Group T] (hT : CFSG.Assembly.LowTwoRank.StatedClassicalModel T .PSU 3 2 2)
    (S : Sylow 2 G) (U : Sylow 2 T) (hSU : Nonempty ((S : Subgroup G) ≃* (U : Subgroup T)))
    (hd : (((S : Subgroup G) ⊔ Subgroup.centralizer ((S : Subgroup G) : Set G)).subgroupOf
      (Subgroup.normalizer ((S : Subgroup G) : Set G))).index = 15)
    (basis : FiniteIrreducibleCharacterBasis G) (ideal : Ideal ComplexAlgebraicIntegers)
    [ideal.IsMaximal] [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2] (principal : basis.index)
    (hprincipal : (basis.representation principal).character = 1)
    {z : G} (hzZ : z ∈ (Subgroup.center (S : Subgroup G)).map (S : Subgroup G).subtype)
    (hz1 : z ≠ 1) :
    ∃ (row : basis.index → LyonsRow) (f : basis.index → ℤ) (P : ℚ),
      LyonsSignedDegreeData (coefficientBlock basis (localizedComplexIntegerRing ideal) principal)
        row f principal (Nat.card G) P ∧
      (coefficientBlock basis (localizedComplexIntegerRing ideal) principal).val.map row ∈
        lyonsConfigurations ∧
      P * (Nat.card G * (Nat.card (Subgroup.centralizer
        (((Subgroup.center (S : Subgroup G)).map (S : Subgroup G).subtype : Subgroup G) :
          Set G)) : ℚ) ^ 2) =
        128 * (Nat.card (Subgroup.centralizer ({z} : Set G)) : ℚ) ^ 3 ∧
      (∀ χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal,
        ((f χ).natAbs : ℂ) = (basis.representation χ).character 1) ∧
      (∀ χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal,
        (∀ ψ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal,
          row ψ = row χ → ψ = χ) → (row χ).rotate = row χ →
        ∀ g, ∃ q : ℚ, (basis.representation χ).character g = q) := by
  classical
  obtain ⟨L, _, _, S₀, h, π, hSC, hL, hπ, hker, hcen, hinj⟩ :=
    lyons_order_fifteen_local_data hnonab hT S U hSU hd hzZ hz1
  obtain ⟨y, hy, hyodd⟩ := exists_lift_coprime_two_orderOf π hπ hker hL.orderOf_h
  obtain ⟨t, htS, ht4⟩ := unitary_four_exists_orderOf_eq_four hT S U hSU
  have hz₀ : π (centralizerSelf z) ∈ (Subgroup.center S₀).map S₀.subtype := hcen z hzZ
  obtain ⟨hdt, hdd, hsum, htt, htd, hgram, hwt, hwd, hcong, hnz, ⟨τ, hτB, hτt, hτd, hτdeg⟩,
    hpt, hpd⟩ := lyons_actual_column_facts hnonab hT S U hSU basis ideal principal hprincipal
      hzZ hz1 htS ht4 hL π hπ hker hz₀ y hy hyodd
  have hmem := lyons_actual_column_configuration hnonab hT S U hSU basis ideal principal
    hprincipal hzZ hz1 htS ht4 hL π hπ hker hz₀ y hy hyodd
  obtain ⟨hrec_t, hrec_d⟩ := lyons_actual_reciprocal_sums hnonab hT S U hSU basis ideal principal
    hprincipal hzZ hz1 htS ht4 hL π hπ hker hSC hcen hinj y hy hyodd (actualDt basis t)
    (actualD basis z y) hdt hdd
  obtain ⟨hdeg_ge, hdvd⟩ := lyons_actual_degree_facts hnonab hT S U hSU basis principal hprincipal
  have hp : principal ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal :=
    coefficientBlock_self_mem _ _ _
  have hpdeg : labelDegree basis principal = 1 := by
    have h1 := labelDegree_cast basis principal
    rw [hprincipal, Pi.one_apply] at h1
    exact_mod_cast h1
  set P : ℚ := 128 * (Nat.card (Subgroup.centralizer ({z} : Set G)) : ℚ) ^ 3 /
    (Nat.card G * (Nat.card (Subgroup.centralizer
      (((Subgroup.center (S : Subgroup G)).map (S : Subgroup G).subtype : Subgroup G) :
        Set G)) : ℚ) ^ 2) with hPdef
  have hPpos : 0 < P := by
    rw [hPdef]
    have : (0 : ℚ) < Nat.card (Subgroup.centralizer ({z} : Set G)) := by exact_mod_cast Nat.card_pos
    have : (0 : ℚ) < Nat.card G := by exact_mod_cast Nat.card_pos
    have : (0 : ℚ) < Nat.card (Subgroup.centralizer
      (((Subgroup.center (S : Subgroup G)).map (S : Subgroup G).subtype : Subgroup G) :
        Set G)) := by exact_mod_cast Nat.card_pos
    positivity
  have hmult : ∀ χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal,
      ∃ a b c : ℕ, labelDegree basis χ = a + 15 * b + 12 * c ∧
        ∑ i, actualD basis z y i χ = a + 15 * b - 4 * c ∧ actualDt basis t χ = a - b ∧
        (χ ≠ principal → 1 ≤ c) := fun χ hχ =>
    lyons_actual_multiplicities hnonab hT S U hSU hd basis principal hprincipal hzZ hz1 htS ht4 χ
      _ _ (hdt χ hχ) (hsum χ hχ)
  have hdata := signedDegreeData_of_columns
    (coefficientBlock basis (localizedComplexIntegerRing ideal) principal) hp
    (actualDt basis t) (labelDegree basis) (actualD basis z y) (Nat.card G) P hpt hpd hpdeg hnz
    (fun χ _ => labelDegree_pos basis χ) (fun χ _ hχ => hdeg_ge χ hχ) Nat.card_pos
    (fun χ _ => hdvd χ) hmult
    (by rw [← hwt]; exact Finset.sum_congr rfl fun χ _ => mul_comm _ _)
    (fun i => by rw [← hwd i]; exact Finset.sum_congr rfl fun χ _ => mul_comm _ _)
    hrec_t hrec_d hPpos τ ⟨fun χ hχ => (hτB χ).mpr hχ, τ.injective.injOn, fun χ hχ =>
      ⟨τ.symm χ, (hτB _).mp (by rwa [Equiv.apply_symm_apply]), Equiv.apply_symm_apply τ χ⟩⟩
    hτt hτd hτdeg
    (fun χ hχ hχp huniq q hq hqG => lyons_isolated_column_prime_bound basis ideal principal
      hprincipal z t y (actualDt basis t) (actualD basis z y) hdt hdd hχ
      ((by norm_num : (4 : ℤ) ≤ 12).trans (hdeg_ge χ hχp)) huniq hq hqG)
  refine ⟨_, _, P, hdata, hmem, ?_, ?_, ?_⟩
  · rw [hPdef]
    field_simp
  · intro χ hχ
    rw [← labelDegree_cast]
    have hsign : columnSign (actualDt basis t) (actualD basis z y) χ = 1 ∨
        columnSign (actualDt basis t) (actualD basis z y) χ = -1 := by
      unfold columnSign; split_ifs <;> simp
    have hpos := labelDegree_pos basis χ
    rcases hsign with hs | hs <;> rw [hs] <;> simp [abs_of_pos hpos]
  · intro χ hχ huniq hrot g
    exact lyons_isolated_rotation_fixed_rational basis ideal principal hprincipal z t y
      (actualDt basis t) (actualD basis z y) hdt hdd hχ huniq hrot g

end CFSG.LyonsUnitaryFour
