module

public import CFSG.GroupTheory.HyperplaneGeneration
public import CFSG.LocalAnalysis.OddStandard.Seitz77Sec27Quot
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple

public section

namespace CFSG.OddStandard.Seitz77

open Subgroup

section FourGroup

variable {X : Type*} [Group X]

private def fourSubgroupB {a b : X} (ha : a * a = 1) (hb : b * b = 1) (hab : a * b = b * a) :
    Subgroup X where
  carrier := {1, a, b, a * b}
  mul_mem' := by
    have h1 : a * (a * b) = b := by rw [← mul_assoc, ha, one_mul]
    have h2 : b * (a * b) = a := by rw [hab, ← mul_assoc, hb, one_mul]
    have h3 : a * b * a = b := by rw [mul_assoc, ← hab, ← mul_assoc, ha, one_mul]
    have h4 : a * b * b = a := by rw [mul_assoc, hb, mul_one]
    have h5 : a * b * (a * b) = 1 := by rw [← mul_assoc, h3, hb]
    have h6 : b * a = a * b := hab.symm
    rintro x y (rfl | rfl | rfl | rfl) (rfl | rfl | rfl | rfl) <;>
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, one_mul, mul_one, ha, hb, h1, h2, h3,
        h4, h5, h6, true_or, or_true]
  one_mem' := Or.inl rfl
  inv_mem' := by
    have h5 : a * b * (a * b) = 1 := by
      rw [← mul_assoc, mul_assoc a b a, ← hab, ← mul_assoc, ha, one_mul, hb]
    rintro x (rfl | rfl | rfl | rfl)
    · simp
    · rw [inv_eq_of_mul_eq_one_right ha]
      exact Or.inr (Or.inl rfl)
    · rw [inv_eq_of_mul_eq_one_right hb]
      exact Or.inr (Or.inr (Or.inl rfl))
    · rw [inv_eq_of_mul_eq_one_right h5]
      exact Or.inr (Or.inr (Or.inr rfl))

private theorem mul_self_of_mem_fourSubgroupB {a b : X} {ha : a * a = 1} {hb : b * b = 1}
    {hab : a * b = b * a} {x : X} (hx : x ∈ fourSubgroupB ha hb hab) : x * x = 1 := by
  rcases hx with rfl | rfl | rfl | rfl
  · exact mul_one 1
  · exact ha
  · exact hb
  · rw [← mul_assoc, mul_assoc a b a, ← hab, ← mul_assoc, ha, one_mul, hb]

private theorem card_fourSubgroupB {a b : X} {ha : a * a = 1} {hb : b * b = 1}
    {hab : a * b = b * a} (ha1 : a ≠ 1) (hb1 : b ≠ 1) (hne : a ≠ b) :
    Nat.card (fourSubgroupB ha hb hab) = 4 := by
  have hab1 : a * b ≠ 1 := fun h => hne (by
    rw [← mul_one a, ← h, ← mul_assoc, ha, one_mul])
  have haab : a ≠ a * b := fun h => hb1 (by
    rw [← one_mul b, ← ha, mul_assoc, ← h, ha])
  have hbab : b ≠ a * b := fun h => ha1 (by
    rw [← mul_one a, ← hb, ← mul_assoc, ← h, hb])
  change Nat.card ({1, a, b, a * b} : Set X) = 4
  rw [Nat.card_coe_set_eq, Set.ncard_insert_of_notMem, Set.ncard_insert_of_notMem,
    Set.ncard_pair hbab]
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨hne, haab⟩
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨fun h => ha1 h.symm, fun h => hb1 h.symm, fun h => hab1 h.symm⟩

theorem le_of_forall_commute_mem_four [Finite X] {N K : Subgroup X} (hN : Odd (Nat.card N))
    {a b : X} (ha : a * a = 1) (hb : b * b = 1) (hab : a * b = b * a)
    (haN : a ∈ Subgroup.normalizer (N : Set X)) (hbN : b ∈ Subgroup.normalizer (N : Set X))
    (hK : ∀ w ∈ ({a, b, a * b} : Set X), ∀ n ∈ N, w * n = n * w → n ∈ K) : N ≤ K := by
  by_cases ha1 : a = 1
  · exact fun n hn => hK a (Or.inl rfl) n hn (by rw [ha1, one_mul, mul_one])
  by_cases hb1 : b = 1
  · exact fun n hn => hK b (Or.inr (Or.inl rfl)) n hn (by rw [hb1, one_mul, mul_one])
  by_cases hne : a = b
  · refine fun n hn => hK (a * b) (Or.inr (Or.inr rfl)) n hn ?_
    rw [hne, hb, one_mul, mul_one]
  set W := fourSubgroupB ha hb hab
  have hWN : W ≤ Subgroup.normalizer (N : Set X) := by
    rintro w (rfl | rfl | rfl | rfl)
    · exact one_mem _
    · exact haN
    · exact hbN
    · exact mul_mem haN hbN
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : MulDistribMulAction ↥W ↥N := MulDistribMulAction.compHom ↥N (Subgroup.inclusion hWN)
  have hsmul : ∀ (w : ↥W) (y : ↥N), ((w • y : ↥N) : X) = w * y * (w : X)⁻¹ := fun _ _ => rfl
  have hWinv : ∀ w : ↥W, w⁻¹ = w := fun w =>
    inv_eq_of_mul_eq_one_right (Subtype.ext (mul_self_of_mem_fourSubgroupB w.2))
  have : CFSG.IsElementaryAbelian 2 ↥W :=
    { toIsMulCommutative := ⟨⟨fun v w => by
        calc v * w = (v * w)⁻¹ := (hWinv _).symm
          _ = w⁻¹ * v⁻¹ := mul_inv_rev v w
          _ = w * v := by rw [hWinv, hWinv]⟩⟩
      exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun w => by
        rw [sq]
        exact Subtype.ext (mul_self_of_mem_fourSubgroupB w.2) }
  have hgen := CFSG.SolvableHall.coprime_centralizer_generation (p := 2) (A := ↥W) (H := ↥N)
    (by rw [card_fourSubgroupB ha1 hb1 hne]; norm_num) (fun h => (Nat.not_even_iff_odd.mpr hN)
      (even_iff_two_dvd.mpr h))
  intro n hn
  have hmem : (⟨n, hn⟩ : ↥N) ∈ ⨆ (w : ↥W) (_ : w ≠ 1),
      CFSG.fixedPointSubgroup (Subgroup.zpowers w) ↥N := by
    rw [hgen]
    exact Subgroup.mem_top _
  refine Subgroup.iSup_induction _ (C := fun z : ↥N => (z : X) ∈ K) hmem ?_ (one_mem K)
    fun _ _ hx hy => mul_mem hx hy
  intro w z hz
  by_cases hw : w = 1
  · rw [iSup_neg (not_not.mpr hw), Subgroup.mem_bot] at hz
    rw [hz]
    exact one_mem K
  rw [iSup_pos hw, CFSG.SolvableHall.mem_fixedPointSubgroup_zpowers_iff] at hz
  have hz' : (w : X) * z * (w : X)⁻¹ = z := by rw [← hsmul, hz]
  have hwmem : (w : X) ∈ ({a, b, a * b} : Set X) := by
    rcases w.2 with h | h | h | h
    · exact absurd (Subtype.ext h) hw
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  refine hK _ hwmem z z.2 ?_
  calc (w : X) * z = (w : X) * z * (w : X)⁻¹ * w := by group
    _ = z * w := by rw [hz']

end FourGroup

section A5

variable {G : Type*} [Group G]

theorem le_of_commutators_mem_of_a5 {M D Kc : Subgroup G}
    (π : ↥M →* alternatingGroup (Fin 5)) (hπ : Function.Surjective π)
    (hker : ∀ m : ↥M, π m = 1 ↔ (m : G) ∈ Kc)
    (hD : ∀ m ∈ M, ∀ d ∈ D, m * d * m⁻¹ ∈ D) (hKD : ∀ k ∈ Kc, k ∈ M → k ∈ D)
    {x : G} (hxM : x ∈ M) (hxK : x ∉ Kc)
    (hcomm : ∀ m ∈ M, m * x * m⁻¹ * x⁻¹ ∈ D) : M ≤ D := by
  have hJn : (D.subgroupOf M).Normal := by
    refine ⟨fun j hj g => ?_⟩
    rw [mem_subgroupOf] at hj ⊢
    simpa using hD (g : G) g.2 (j : G) hj
  have hJm : ((D.subgroupOf M).map π).Normal := hJn.map π hπ
  have := hJm
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((D.subgroupOf M).map π) with h0 | h1
  · exfalso
    have hcen : π ⟨x, hxM⟩ ∈ Subgroup.center (alternatingGroup (Fin 5)) := by
      rw [Subgroup.mem_center_iff]
      intro g
      obtain ⟨m, rfl⟩ := hπ g
      have hmem : (m * ⟨x, hxM⟩ * m⁻¹ * ⟨x, hxM⟩⁻¹ : ↥M) ∈ D.subgroupOf M :=
        mem_subgroupOf.mpr (hcomm m m.2)
      have h1 := mem_map_of_mem π hmem
      rw [h0, mem_bot, map_mul, map_mul, map_mul, map_inv, map_inv] at h1
      calc π m * π ⟨x, hxM⟩ = (π m * π ⟨x, hxM⟩ * (π m)⁻¹ * (π ⟨x, hxM⟩)⁻¹) *
            (π ⟨x, hxM⟩ * π m) := by group
        _ = π ⟨x, hxM⟩ * π m := by rw [h1, one_mul]
    rw [alternatingGroup.center_eq_bot (by simp), mem_bot] at hcen
    exact hxK ((hker ⟨x, hxM⟩).mp hcen)
  · intro m hm
    have hmem : π ⟨m, hm⟩ ∈ (D.subgroupOf M).map π := by
      rw [h1]
      exact mem_top _
    obtain ⟨j, hj, hjπ⟩ := hmem
    have hjD : (j : G) ∈ D := mem_subgroupOf.mp hj
    have hk : ((j⁻¹ * ⟨m, hm⟩ : ↥M) : G) ∈ Kc :=
      (hker _).mp (by rw [map_mul, map_inv, hjπ, inv_mul_cancel])
    have hkD : ((j⁻¹ * ⟨m, hm⟩ : ↥M) : G) ∈ D := hKD _ hk (j⁻¹ * ⟨m, hm⟩ : ↥M).2
    have hmj : m = (j : G) * ((j⁻¹ * ⟨m, hm⟩ : ↥M) : G) := by simp
    rw [hmj]
    exact D.mul_mem hjD hkD

end A5

section PerfectOdd

variable {G : Type*} [Group G] [Finite G]

theorem le_of_perfect_of_odd {H C Q : Subgroup G} (hH : ⁅H, H⁆ = H) (hCH : C ≤ H) (hQH : Q ≤ H)
    (hCn : ∀ h ∈ H, ∀ c ∈ C, h * c * h⁻¹ ∈ C) (hodd : Odd (Nat.card Q))
    (hHCQ : ∀ x ∈ H, ∃ c ∈ C, ∃ q ∈ Q, x = c * q) : H ≤ C := by
  have hCnorm : (C.subgroupOf H).Normal := by
    refine ⟨fun c hc h => ?_⟩
    rw [mem_subgroupOf] at hc ⊢
    simpa using hCn (h : G) h.2 (c : G) hc
  have hPerf : Group.IsPerfect ↥H := Subgroup.isPerfect_iff.mpr hH
  let f : ↥H →* ↥H ⧸ C.subgroupOf H := QuotientGroup.mk' (C.subgroupOf H)
  have hQc : Nat.card ↥(Q.subgroupOf H) = Nat.card Q :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQH).toEquiv
  have hle : (⊤ : Subgroup ↥H).map f ≤ (Q.subgroupOf H).map f := by
    rintro _ ⟨x, -, rfl⟩
    obtain ⟨c, hc, q, hq, hxcq⟩ := hHCQ x x.2
    refine ⟨⟨q, hQH hq⟩, mem_subgroupOf.mpr hq, ?_⟩
    have hx : x = ⟨c, hCH hc⟩ * ⟨q, hQH hq⟩ := Subtype.ext hxcq
    have hc1 : f ⟨c, hCH hc⟩ = 1 := (QuotientGroup.eq_one_iff _).mpr (mem_subgroupOf.mpr hc)
    rw [hx, map_mul, hc1, one_mul]
  have hoddm : Odd (Nat.card ((⊤ : Subgroup ↥H).map f)) := by
    have h1 := Subgroup.card_dvd_of_le hle
    have h2 := Subgroup.card_map_dvd (Q.subgroupOf H) f
    rw [hQc] at h2
    exact hodd.of_dvd_nat (h1.trans h2)
  have htop : ⁅(⊤ : Subgroup ↥H), ⊤⁆ = ⊤ := Subgroup.commutator_eq_self
  have hker := perfect_odd_image_trivial htop f hoddm
  intro x hx
  have h1 : (⟨x, hx⟩ : ↥H) ∈ f.ker := hker (mem_top _)
  rw [QuotientGroup.ker_mk'] at h1
  exact mem_subgroupOf.mp h1

end PerfectOdd

end CFSG.OddStandard.Seitz77
