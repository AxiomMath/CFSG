module

public import CFSG.CharacterTheory.Wreathed.CyclicWeakClosure
public import CFSG.GroupTheory.CyclicSylowNormalOddComplement
public import CFSG.CharacterTheory.Semidihedral.QuaternionAutomorphismLifting
public import CFSG.LocalAnalysis.SignalizerFunctor.InvariantSylowAmbient
public import CFSG.CharacterTheory.Wreathed.OriginalStructure

public section

namespace CFSG.Wreathed.SplitCyclicActor

open scoped Pointwise

universe u

theorem normal_two_complement_of_normal_cyclic_sylow {H : Type u} [Group H] [Finite H]
    (D : Subgroup H) [D.Normal] (hD : ∃ k : ℕ, D.index = 2 ^ k) (Q : Sylow 2 D)
    (hQ : IsCyclic Q) :
    ∃ N : Subgroup H, N.Normal ∧ Odd (Nat.card N) ∧ ∃ k : ℕ, N.index = 2 ^ k := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, -, -, ⟨-, hodd, hindex, -⟩, hchar⟩ := CFSG.cyclic_sylow_normal_odd_complement Q hQ
  obtain ⟨k, hk⟩ := hD
  obtain ⟨j, hj⟩ := Q.isPGroup'.exists_card_eq
  refine ⟨(CFSG.pPrimeCore 2 D).map D.subtype, ?_, ?_, j + k, ?_⟩
  · have h := CFSG.SignalizerFunctor.Helpers.characteristic_subgroup_map_normalized ⊤ D
      (by rw [Subgroup.normalizer_eq_top_iff.mpr inferInstance]) (CFSG.pPrimeCore 2 D)
    exact Subgroup.normalizer_eq_top_iff.mp (eq_top_iff.mpr h)
  · rw [Subgroup.card_map_of_injective D.subtype_injective]
    exact hodd
  · rw [Subgroup.index_map_subtype, hindex, hj, hk, pow_add]

theorem commutator_le_of_sup_eq_top {H : Type u} [Group H] (K A : Subgroup H) [K.Normal]
    (hA : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) (hKA : K ⊔ A = ⊤) : commutator H ≤ K := by
  have hsurj : ∀ q : H ⧸ K, ∃ a ∈ A, (QuotientGroup.mk a : H ⧸ K) = q := by
    intro q
    obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective q
    have hh : h ∈ K ⊔ A := hKA ▸ Subgroup.mem_top h
    obtain ⟨k, hk, a, ha, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp hh
    refine ⟨a, ha, ?_⟩
    rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff k).mpr hk, one_mul]
  have hcomm : IsMulCommutative (H ⧸ K) := by
    refine ⟨⟨fun q₁ q₂ => ?_⟩⟩
    obtain ⟨a, ha, rfl⟩ := hsurj q₁
    obtain ⟨b, hb, rfl⟩ := hsurj q₂
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, hA a ha b hb]
  exact Subgroup.Normal.quotient_commutative_iff_commutator_le.mp hcomm

theorem oddCore_sup_centralizer_eq_top_of_unique_involution {G : Type u} [Group G] [Finite G]
    (Q : Sylow 2 G)
    (huniq : ∀ a ∈ (Q : Subgroup G), ∀ b ∈ (Q : Subgroup G), orderOf a = 2 → orderOf b = 2 →
      a = b)
    (i : G) (hiQ : i ∈ (Q : Subgroup G)) (hi : orderOf i = 2) :
    CFSG.oddCore G ⊔ Subgroup.centralizer ({i} : Set G) = ⊤ := by
  have hconj : ∀ g : G, g⁻¹ * i * g ∈ (Q : Subgroup G) → g⁻¹ * i * g = i := by
    intro g hg
    refine huniq _ hg i hiQ ?_ hi
    rw [show g⁻¹ * i * g = MulAut.conj g⁻¹ i by simp, MulEquiv.orderOf_eq]
    exact hi
  have hzQ : Subgroup.zpowers i ≤ (Q : Subgroup G) := Subgroup.zpowers_le.mpr hiQ
  have hcent : Subgroup.zpowers i ≤ Subgroup.centralizer (Q : Set G) := by
    rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
    intro q hq
    have h := hconj q⁻¹ (by
      rw [inv_inv]
      exact (Q : Subgroup G).mul_mem ((Q : Subgroup G).mul_mem hq hiQ)
        ((Q : Subgroup G).inv_mem hq))
    rw [inv_inv] at h
    calc q * i = q * i * q⁻¹ * q := by group
      _ = i * q := by rw [h]
  have hi2 : i ^ 2 = 1 := by
    rw [← hi]
    exact pow_orderOf_eq_one i
  have hwc : ∀ a ∈ Subgroup.zpowers i, ∀ g : G,
      g⁻¹ * a * g ∈ (Q : Subgroup G) → g⁻¹ * a * g = a := by
    intro a ha g hg
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    obtain ⟨r, hr | hr⟩ := Int.even_or_odd' k
    · have h1 : i ^ k = 1 := by
        rw [hr, zpow_mul, zpow_ofNat, hi2, one_zpow]
      rw [h1]
      group
    · have h1 : i ^ k = i := by
        rw [hr, zpow_add, zpow_mul, zpow_ofNat, hi2, one_zpow, one_mul, zpow_one]
      rw [h1] at hg ⊢
      exact hconj g hg
  obtain ⟨-, hfac⟩ := cyclic_weakly_closed_central_sylow_subgroup_central_mod_odd_core Q
    (Subgroup.zpowers i) hzQ hcent hwc
  apply eq_top_iff.mpr
  intro g _
  obtain ⟨r, hr, c, hc, rfl⟩ := hfac g
  refine Subgroup.mul_mem_sup hr ?_
  exact Subgroup.centralizer_le (Set.singleton_subset_iff.mpr (Subgroup.mem_zpowers i)) hc

theorem base_inf_quaternion_eq_zpowers (n : ℕ) (hn : 2 ≤ n) :
    baseSubgroup (2 ^ n) ⊓ Original.Y (2 ^ n) = Subgroup.zpowers (Original.r (2 ^ n)) := by
  have hstr := wreath_center_involution_and_quaternion_coordinates n hn
  have hrU : Original.r (2 ^ n) ∈ baseSubgroup (2 ^ n) := by
    rw [Original.r_eq, element_mem_base]
  have hrY : Original.r (2 ^ n) ∈ Original.Y (2 ^ n) :=
    Subgroup.subset_closure (Set.mem_insert _ _)
  have hdY : Original.d (2 ^ n) ∈ Original.Y (2 ^ n) :=
    Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  have hdU : Original.d (2 ^ n) ∉ baseSubgroup (2 ^ n) := by
    rw [Original.d_eq, element_mem_base]
    decide
  have hle : Subgroup.zpowers (Original.r (2 ^ n)) ≤ baseSubgroup (2 ^ n) ⊓ Original.Y (2 ^ n) :=
    Subgroup.zpowers_le.mpr ⟨hrU, hrY⟩
  have hcardr : Nat.card (Subgroup.zpowers (Original.r (2 ^ n))) = 2 ^ n := by
    rw [Nat.card_zpowers, Original.orderOf_r]
  have hcardY : Nat.card (Original.Y (2 ^ n)) = 2 ^ (n + 1) := by
    rw [hstr.quaternion_card, pow_succ, mul_comm]
  have hdvd : Nat.card (baseSubgroup (2 ^ n) ⊓ Original.Y (2 ^ n) : Subgroup _) ∣ 2 ^ (n + 1) :=
    hcardY ▸ Subgroup.card_dvd_of_le inf_le_right
  obtain ⟨j, hj, hjcard⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  have hge : 2 ^ n ≤ 2 ^ j := by
    rw [← hcardr, ← hjcard]
    exact Subgroup.card_le_of_le hle
  have hjn : n ≤ j := (Nat.pow_le_pow_iff_right (by norm_num)).mp hge
  have hjne : j ≠ n + 1 := by
    intro hjeq
    apply hdU
    have heq : baseSubgroup (2 ^ n) ⊓ Original.Y (2 ^ n) = Original.Y (2 ^ n) :=
      Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [hcardY, hjcard, hjeq])
    exact (heq ▸ inf_le_left : Original.Y (2 ^ n) ≤ baseSubgroup (2 ^ n)) hdY
  have hjeq : j = n := by omega
  exact (Subgroup.eq_of_le_of_card_ge hle (by rw [hjcard, hcardr, hjeq])).symm

theorem unique_involution_of_equiv_quaternion (n : ℕ) (hn : 2 ≤ n) {P : Type*} [Group P]
    (f : P ≃* Original.Y (2 ^ n)) (a b : P) (ha : orderOf a = 2) (hb : orderOf b = 2) :
    a = b := by
  have hstr := wreath_center_involution_and_quaternion_coordinates n hn
  obtain ⟨q⟩ := hstr.quaternion
  let g : P ≃* QuaternionGroup (2 ^ n / 2) := f.trans q.symm
  have hpos : 0 < 2 ^ n / 2 := Nat.div_pos (Nat.le_self_pow (by omega) 2) two_pos
  have hga : g a = QuaternionGroup.a ((2 ^ n / 2 : ℕ) : ZMod (2 * (2 ^ n / 2))) :=
    (CFSG.Semidihedral.QuaternionAutomorphismLifting.unique_involution _ hpos (g a)).mp
      (by rw [MulEquiv.orderOf_eq]; exact ha)
  have hgb : g b = QuaternionGroup.a ((2 ^ n / 2 : ℕ) : ZMod (2 * (2 ^ n / 2))) :=
    (CFSG.Semidihedral.QuaternionAutomorphismLifting.unique_involution _ hpos (g b)).mp
      (by rw [MulEquiv.orderOf_eq]; exact hb)
  exact g.injective (hga.trans hgb.symm)

end CFSG.Wreathed.SplitCyclicActor
