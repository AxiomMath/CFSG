module

public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3Model

open Subgroup

private lemma factorization_177408000_eleven : (177408000 : ℕ).factorization 11 = 1 := by
  have h : (177408000 : ℕ) = 11 * 16128000 := by norm_num
  rw [h, Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
    Nat.Prime.factorization_self (by decide : Nat.Prime 11),
    Nat.factorization_eq_zero_of_not_dvd (by norm_num)]

theorem isConj_of_orderOf_eleven {G : Type} [Group G] [Finite G]
    (hG : Nat.card G = 177408000)
    (hC : ∀ x : G, orderOf x = 11 → Nat.card ↥(Subgroup.centralizer ({x} : Set G)) = 22)
    {x y : G} (hx : orderOf x = 11) (hy : orderOf y = 11) : IsConj x y := by
  classical
  haveI : Fact (Nat.Prime 11) := ⟨by decide⟩
  haveI : Fintype G := Fintype.ofFinite G
  set P : Subgroup G := Subgroup.zpowers x with hP
  set Q : Subgroup G := Subgroup.zpowers y with hQ
  have hSylx : Nat.card ↥P = 11 ^ (Nat.card G).factorization 11 := by
    rw [hP, Nat.card_zpowers, hx, hG, factorization_177408000_eleven, pow_one]
  have hSyly : Nat.card ↥Q = 11 ^ (Nat.card G).factorization 11 := by
    rw [hQ, Nat.card_zpowers, hy, hG, factorization_177408000_eleven, pow_one]
  let Px : Sylow 11 G := Sylow.ofCard P hSylx
  let Py : Sylow 11 G := Sylow.ofCard Q hSyly
  have hPx_coe : (Px : Subgroup G) = P := Sylow.coe_ofCard P hSylx
  have hPy_coe : (Py : Subgroup G) = Q := Sylow.coe_ofCard Q hSyly
  haveI : Finite (Sylow 11 G) := Sylow.finite_of_finiteIndex Px
  set N : Subgroup G := Subgroup.normalizer (P : Set G) with hN
  set C : Subgroup G := Subgroup.centralizer ({x} : Set G) with hCdef
  set n : ℕ := Nat.card (Sylow 11 G) with hn
  have hxP : x ∈ P := by rw [hP]; exact Subgroup.mem_zpowers x
  let xp : P := ⟨x, hxP⟩
  have hindex : n = N.index := by
    rw [hn, Sylow.card_eq_index_normalizer Px, ← Sylow.coe_coe Px, hPx_coe, hN]
  have hNcard : n * Nat.card ↥N = Nat.card G := by
    rw [hindex]
    simpa [mul_comm] using Subgroup.card_mul_index N
  have hmod : n ≡ 1 [MOD 11] := by
    rw [hn]
    exact card_sylow_modEq_one 11 G
  have hCN : C ≤ N := by
    have h := Subgroup.normalizer_le_normalizer_closure ({x} : Set G)
    rw [Subgroup.normalizer_singleton] at h
    have h2 : Subgroup.normalizer (closure ({x} : Set G)) = N := by
      rw [hN, hP, ← Subgroup.zpowers_eq_closure x]
    rw [hCdef, ← h2]
    exact h
  have hstab : MulAction.stabilizer N xp = C.subgroupOf N := by
    ext m
    rw [MulAction.mem_stabilizer_iff, Subgroup.mem_subgroupOf]
    constructor
    · intro hm
      rw [Subgroup.mem_centralizer_singleton_iff]
      have h1 : (m : G) * x * (m : G)⁻¹ = x := by
        have h := congrArg (Subtype.val) hm
        change (m : G) * x * (m : G)⁻¹ = x at h
        simpa [xp] using h
      calc (m : G) * x = ((m : G) * x * (m : G)⁻¹) * (m : G) := by group
        _ = x * (m : G) := by rw [h1]
    · intro hm
      rw [Subgroup.mem_centralizer_singleton_iff] at hm
      apply Subtype.ext
      show (m : G) * x * (m : G)⁻¹ = x
      calc (m : G) * x * (m : G)⁻¹ = x * (m : G) * (m : G)⁻¹ := by rw [hm]
        _ = x := by group
  have hs : Nat.card ↥(MulAction.stabilizer N xp) = 22 := by
    rw [hstab]
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hCN).toEquiv]
    exact hC x hx
  have hos0 : Nat.card ↥(MulAction.orbit N xp) *
      Nat.card ↥(MulAction.stabilizer N xp) = Nat.card ↥N := by
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
    exact MulAction.card_orbit_mul_card_stabilizer_eq_card_group N xp
  set o : ℕ := Nat.card ↥(MulAction.orbit N xp) with ho
  have hoN : o * 22 = Nat.card ↥N := by
    rw [← hs]
    exact hos0
  have hno : n * o * 22 = 177408000 := by
    rw [← hG, ← hNcard, ← hoN]
    ring
  have hno' : n * o = 8064000 := by
    have h : n * o * 22 = 8064000 * 22 := by nlinarith [hno]
    exact Nat.mul_right_cancel (by norm_num : 0 < 22) h
  have h1 : o ≡ n * o [MOD 11] := by
    have h := hmod.mul (Nat.ModEq.refl o)
    simpa using h.symm
  have h2 : n * o ≡ (8064000 : ℕ) [MOD 11] := by rw [hno']
  have h3 : (8064000 : ℕ) ≡ 10 [MOD 11] := by norm_num [Nat.ModEq]
  have hmod_o : o ≡ 10 [MOD 11] := h1.trans (h2.trans h3)
  set S : Set P := {p : P | orderOf p = 11} with hSdef
  have hS_card : Nat.card S = 10 := by
    haveI : IsCyclic P := by rw [hP]; exact Subgroup.isCyclic_zpowers x
    have hdvd : 11 ∣ Fintype.card P := by
      rw [← Nat.card_eq_fintype_card, hP, Nat.card_zpowers, hx]
    have h1 := IsCyclic.card_orderOf_eq_totient (α := P) (d := 11) hdvd
    rw [Nat.card_eq_fintype_card]
    change Fintype.card {p : P // orderOf p = 11} = 10
    rw [Fintype.card_subtype, h1, Nat.totient_prime (by decide : Nat.Prime 11)]
  have horbit_sub : MulAction.orbit N xp ⊆ S := by
    intro p hp
    rw [MulAction.mem_orbit_iff] at hp
    obtain ⟨m, rfl⟩ := hp
    show orderOf (m • xp) = 11
    rw [← Subgroup.orderOf_coe (m • xp)]
    change orderOf ((m : G) * x * (m : G)⁻¹) = 11
    rw [← MulAut.conj_apply, MulEquiv.orderOf_eq (MulAut.conj (m : G)) x, hx]
  have h_le : o ≤ 10 := by
    rw [ho, ← hS_card]
    exact Nat.card_le_card_of_injective (Set.inclusion horbit_sub)
      (Set.inclusion_injective horbit_sub)
  have ho10 : o = 10 := Nat.ModEq.eq_of_lt_of_lt hmod_o (by omega) (by norm_num)
  have horbit_eq : MulAction.orbit N xp = S := by
    refine Set.Finite.eq_of_subset_of_card_le (Set.toFinite S) horbit_sub ?_
    rw [← ho, hS_card, ho10]
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G Py Px
  let t : G := MulAut.conj g y
  have htP : t ∈ P := by
    have hmem : MulAut.conj g y ∈ ((g • Py : Sylow 11 G) : Subgroup G) := by
      rw [Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists]
      refine ⟨y, ?_, rfl⟩
      rw [hPy_coe]
      exact Subgroup.mem_zpowers y
    have hgsub : ((g • Py : Sylow 11 G) : Subgroup G) = (Px : Subgroup G) := congrArg _ hg
    rw [hgsub, hPx_coe] at hmem
    simpa only [t] using hmem
  have htord : orderOf t = 11 := by
    dsimp only [t]
    rw [MulEquiv.orderOf_eq (MulAut.conj g) y, hy]
  have hxt : IsConj x t := by
    have htS : (⟨t, htP⟩ : P) ∈ S := by
      show orderOf (⟨t, htP⟩ : P) = 11
      rw [← Subgroup.orderOf_coe (⟨t, htP⟩ : P)]
      exact htord
    rw [← horbit_eq] at htS
    rw [MulAction.mem_orbit_iff] at htS
    obtain ⟨m, hm⟩ := htS
    refine isConj_iff.mpr ⟨m, ?_⟩
    have h1 : (↑(m • xp) : G) = t := by rw [hm]
    have h2 : (↑(m • xp) : G) = (m : G) * x * (m : G)⁻¹ := rfl
    rw [h2] at h1
    exact h1
  have hyt : IsConj y t := by
    refine isConj_iff.mpr ⟨g, ?_⟩
    simp only [t, MulAut.conj_apply]
  exact hxt.trans hyt.symm

end CFSG.EvenSporadicStandard.HNRecog.Section3Model
