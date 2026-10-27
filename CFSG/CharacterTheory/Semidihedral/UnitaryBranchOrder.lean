module

public import CFSG.CharacterTheory.Semidihedral.UnitaryBranchLocalData
public import CFSG.CharacterTheory.Semidihedral.SimpleLayerFrontierOrder
public import CFSG.CharacterTheory.Semidihedral.Principal.FieldFactorOneFixedCoreRegular

public section

namespace CFSG.Semidihedral.UnitaryBranch

open CFSG.Open CFSG.Semidihedral CFSG.Semidihedral.ActualSimpleLayerLocalPackage
open CFSG.ComponentClassification.CatalogueSchreierLinearTwo
open CFSG.Semidihedral.Principal
  (actual_field_factor_one_nontrivial_fixed_core_is_regular_and_has_no_inverted_odd_factor)

theorem coprime_half_succ_pred {q : ℕ} (hq : q % 4 = 1) : Nat.Coprime ((q + 1) / 2) (q - 1) := by
  obtain ⟨m, rfl⟩ : ∃ m, q = 4 * m + 1 := ⟨q / 4, by omega⟩
  have h1 : (4 * m + 1 + 1) / 2 = 2 * m + 1 := by omega
  have h2 : 4 * m + 1 - 1 = 2 * (2 * m) := by omega
  rw [h1, h2]
  apply Nat.Coprime.mul_right
  · exact Nat.coprime_two_right.mpr (by exact odd_two_mul_add_one m)
  · have : 2 * m + 1 = 2 * m + 1 := rfl
    rw [Nat.coprime_comm]
    exact Nat.coprime_self_add_right.mpr (Nat.coprime_one_right _)

theorem unitary_order_formulas
    (G : Type) [Group G] [Finite G] [IsSimpleGroup G]
    (hGnonab : ∃ a b : G, a * b ≠ b * a)
    (hrecognition : PerfectLayerNormalization.OriginalSmallerSimpleRecognition G)
    (n : ℕ) (hn : 4 ≤ n) (S : Sylow 2 G) (fS : SemidihedralGroup n ≃* (S : Subgroup G))
    (t : G) (ht : t = (fS (r n) : G) ^ 2 ^ (n - 2))
    [IsSimpleGroup (CFSG.generalizedFitting (Gamma t))]
    (hnonab : ∃ a b : CFSG.generalizedFitting (Gamma t), a * b ≠ b * a)
    (hcentral : Subgroup.centralizer (CFSG.generalizedFitting (Gamma t) : Set (Gamma t)) = ⊥)
    (hnc : ∀ U : Sylow 2 (CFSG.generalizedFitting (Gamma t)), ¬ IsCyclic U)
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f) (hq1 : p ^ f % 4 = 1)
    (hq5 : 5 < p ^ f)
    (hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (CFSG.generalizedFitting (Gamma t)) .PSL 2 p f)
    (hcov : EscapingLocalEigensubgroups.allLocalPrimeStationaryCovers t (fS (s n) : G))
    (hY : (((CFSG.generalizedFitting (Gamma t)).comap (barKappa t)).comap (nu t)).index = 2)
    (hA₀ : (N t).map (C t).subtype ⊓ Subgroup.centralizer {(fS (s n) : G)} ≠ ⊥) :
    N t ≠ ⊥ ∧ N t ≤ Subgroup.center (C t) ∧ IsCyclic (N t) ∧
      Nat.Coprime (Nat.card (N t)) (p * (p ^ f - 1)) ∧ Nat.card (N t) ∣ (p ^ f + 1) / 2 ∧
      (∃ (F : Type) (_ : Field F) (_ : Finite F) (κ : C t →* Equiv.Perm (Omega F)),
        UnitaryLocalData t p f F κ) ∧
      Nat.card (C t) = 2 * Nat.card (N t) * (p ^ f * ((p ^ f) ^ 2 - 1)) ∧
      Nat.card ↥(C t ⊓ Subgroup.centralizer {(fS (s n) : G)}) =
        2 * Nat.card (N t) * (p ^ f + 1) ∧
      Nat.card G = 2 * Nat.card (N t) * (p ^ f) ^ 3 * (p ^ f - 1) * ((p ^ f) ^ 3 + 1) := by
  classical
  have hG : ∀ U : Subgroup G, U.index ≠ 2 :=
    PerfectLayerNormalization.nonabelian_simple_has_no_subgroup_index_two hGnonab
  obtain ⟨hz, ht2, -, hsC, hs2, hst⟩ := Principal.supplied_t_s_facts hn fS ht
  obtain ⟨hval, -, hNA, hNne, hNcyc, hNdvd, hNp⟩ :=
    actual_field_factor_one_nontrivial_fixed_core_is_regular_and_has_no_inverted_odd_factor
      G hGnonab hrecognition n hn S fS t ht hnonab hcentral hnc p f hp hpodd hf hq5 hmodel hcov hY
      hA₀
  have hNdvd' : Nat.card (N t) ∣ (p ^ f + 1) / 2 := by
    have h : (if p ^ f % 4 = 1 then p ^ f + 1 else p ^ f - 1) = p ^ f + 1 := ite_eq_left_iff.mpr
      (fun h => absurd hq1 h)
    rw [h] at hNdvd
    exact hNdvd
  have hcop : Nat.Coprime (Nat.card (N t)) (p * (p ^ f - 1)) := by
    apply Nat.Coprime.mul_right
    · rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd hp]
      exact hNp
    · exact Nat.Coprime.coprime_dvd_left hNdvd' (coprime_half_succ_pred hq1)
  have hcover := EscapingLocalEigensubgroups.all_stationary_covers_give_original_layer_coverage
    t (fS (s n) : G) hcov
  obtain ⟨-, -, -, hYJN, -, -⟩ :=
    Local.all_local_prime_covers_split_actual_layer_except_central_three_at_nine n hn S fS hG t ht2
      hnonab hcentral hnc p f hp hpodd hf hq5.le hmodel (Or.inl hcover)
  set T₀ := (CFSG.generalizedFitting (Gamma t)).comap (barKappa t)
  set Y := T₀.comap (nu t)
  set H₀ := Y ⊓ Subgroup.centralizer (N t : Set (C t))
  set J := (CFSG.perfectResidual H₀).map H₀.subtype
  let sC : C t := ⟨(fS (s n) : G), hsC⟩
  have hsC2 : orderOf sC = 2 := by
    rw [← hs2, ← Subgroup.orderOf_coe]
  have hsCt : sC ≠ tInC t := fun h => hst (congrArg Subtype.val h)
  have hsY : sC ∉ Y :=
    SimpleLayerFrontier.noncentral_involution_not_mem_layer_preimage n hn S fS hG t ht2 hnonab sC
      hsC2 hsCt
  obtain ⟨gN, hgN⟩ := IsCyclic.exists_generator (α := N t)
  have hNcomm : ∀ y ∈ N t, ∀ y' ∈ N t, y * y' = y' * y := by
    intro y hy y' hy'
    obtain ⟨i, hi⟩ := hgN ⟨y, hy⟩
    obtain ⟨j, hj⟩ := hgN ⟨y', hy'⟩
    have h1 : y = (gN : C t) ^ i := by
      have := congrArg Subtype.val hi
      simpa using this.symm
    have h2 : y' = (gN : C t) ^ j := by
      have := congrArg Subtype.val hj
      simpa using this.symm
    rw [h1, h2, ← zpow_add, ← zpow_add, add_comm]
  have hNcent : N t ≤ Subgroup.center (C t) := by
    intro y hy
    rw [Subgroup.mem_center_iff]
    intro c
    have htop : Subgroup.centralizer ({y} : Set (C t)) = ⊤ := by
      refine SimpleLayerFrontier.eq_top_of_index_two_le hY ?_ (x := sC) ?_ hsY
      · rw [hYJN]
        refine sup_le ?_ ?_
        · intro j hj
          rw [Subgroup.mem_centralizer_singleton_iff]
          obtain ⟨j', -, rfl⟩ := hj
          exact (Subgroup.mem_centralizer_iff.mp (j' : H₀).2.2 y hy).symm
        · intro y' hy'
          rw [Subgroup.mem_centralizer_singleton_iff]
          exact hNcomm y' hy' y hy
      · rw [Subgroup.mem_centralizer_singleton_iff]
        have hyNa : (y : G) ∈ (N t).map (C t).subtype := ⟨y, hy, rfl⟩
        rw [hNA] at hyNa
        have hyc := Subgroup.mem_centralizer_singleton_iff.mp hyNa.2
        exact Subtype.ext hyc.symm
    have hc : c ∈ Subgroup.centralizer ({y} : Set (C t)) := htop ▸ Subgroup.mem_top c
    exact Subgroup.mem_centralizer_singleton_iff.mp hc
  have hdata := exists_unitaryLocalData hGnonab n hn S fS t ht hnonab hcentral hnc p f hp hpodd
    hf hq1 hmodel hY hNcent hNcyc hcop
  obtain ⟨F, hF, hFfin, κ, hD⟩ := hdata
  have hCcard := (unitaryLocalData_card hD).2
  refine ⟨hNne, hNcent, hNcyc, hcop, hNdvd', ⟨F, hF, hFfin, κ, hD⟩, hCcard, ?_⟩
  let : Fintype G := Fintype.ofFinite G
  obtain ⟨h, -, -, hCcard', hDcard, hGcard, -⟩ :=
    SimpleLayerFrontier.frontier_regular_order hGnonab n hn S fS t ht hnonab hcentral hnc p f hp
      hpodd hf hmodel hval
  have hCN :
      ((Subgroup.centralizer {(fS (s n) : G)}).comap (C t).subtype).subgroupOf (N t) = ⊤ := by
    rw [eq_top_iff]
    intro x _
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_comap]
    have hxNa : ((x : C t) : G) ∈ (N t).map (C t).subtype := ⟨x, x.2, rfl⟩
    rw [hNA] at hxNa
    exact hxNa.2
  rw [hCN, Subgroup.card_top] at hCcard' hDcard hGcard
  rw [Subgroup.index_top] at hCcard' hGcard
  have he : (if p ^ f % 4 = 1 then (1 : ℤ) else -1) = 1 := ite_eq_left_iff.mpr
    (fun h => absurd hq1 h)
  rw [he] at hDcard hGcard
  set a := Nat.card (N t)
  set q := p ^ f with hqdef
  have hq1' : 1 < q := Nat.one_lt_pow (by omega) hp.one_lt
  have hh : h = 1 := by
    have hpos : 0 < 2 * a * (q * (q ^ 2 - 1)) := by
      have : 0 < q ^ 2 - 1 := by
        have : 1 < q ^ 2 := Nat.one_lt_pow (by norm_num) hq1'
        omega
      have : 0 < a := Nat.card_pos
      positivity
    have h1 : 2 * a * 1 * h * q * (q ^ 2 - 1) = 2 * a * (q * (q ^ 2 - 1)) * h := by ring
    rw [hCcard, h1] at hCcard'
    have h2 : 2 * a * (q * (q ^ 2 - 1)) * 1 = 2 * a * (q * (q ^ 2 - 1)) * h := by
      rw [mul_one]
      exact hCcard'
    exact (Nat.eq_of_mul_eq_mul_left hpos h2).symm
  subst hh
  constructor
  · have : (Nat.card ↥(C t ⊓ Subgroup.centralizer {(fS (s n) : G)}) : ℤ) =
        ((2 * a * (q + 1) : ℕ) : ℤ) := by
      rw [hDcard]
      push_cast
      ring
    exact_mod_cast this
  · have hq1z : (1 : ℤ) ≤ q := by exact_mod_cast hq1'.le
    have : (Nat.card G : ℤ) = ((2 * a * q ^ 3 * (q - 1) * (q ^ 3 + 1) : ℕ) : ℤ) := by
      rw [hGcard]
      push_cast [Nat.cast_sub hq1'.le]
      ring
    exact_mod_cast this


end CFSG.Semidihedral.UnitaryBranch
