module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.OuterAltStd
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.OuterPumpType
public import CFSG.Sporadic.He.Simple
public import CFSG.Sporadic.Ru
public import CFSG.Sporadic.Suz.Simple

public section

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus.Outer

open Subgroup Equiv CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.Assembly.LowTwoRank

theorem card_centralizer_perm_involution {n : ℕ} (g : Perm (Fin n)) (hg : orderOf g = 2) :
    ∃ a : ℕ, a ≠ 0 ∧ Nat.card (centralizer ({g} : Set (Perm (Fin n)))) =
      (n - a * 2).factorial * 2 ^ a * a.factorial := by
  have hct : ∀ m ∈ g.cycleType, m = 2 := by
    intro m hm
    have h2 : 2 ≤ m := Perm.two_le_of_mem_cycleType hm
    have hd : m ∣ orderOf g := by
      rw [← Perm.lcm_cycleType]
      exact Multiset.dvd_lcm hm
    rw [hg] at hd
    exact Nat.le_antisymm (Nat.le_of_dvd (by norm_num) hd) h2
  have hrep : g.cycleType = Multiset.replicate (Multiset.card g.cycleType) 2 :=
    Multiset.eq_replicate_card.2 hct
  set a := Multiset.card g.cycleType with ha
  have ha0 : a ≠ 0 := by
    intro h0
    have h1 : g.cycleType = 0 := Multiset.card_eq_zero.1 h0
    have h2 := Perm.cycleType_eq_zero.1 h1
    rw [h2, orderOf_one] at hg
    omega
  refine ⟨a, ha0, ?_⟩
  rw [Perm.nat_card_centralizer, hrep]
  simp [Multiset.toFinset_replicate, ha0, Multiset.count_replicate, Fintype.card_fin]

theorem card_centralizer_alternating_dvd {n : ℕ} (t : alternatingGroup (Fin n)) :
    Nat.card (centralizer ({t} : Set (alternatingGroup (Fin n)))) ∣
        Nat.card (centralizer ({(t : Perm (Fin n))} : Set (Perm (Fin n)))) ∧
      Nat.card (centralizer ({(t : Perm (Fin n))} : Set (Perm (Fin n)))) ∣
        2 * Nat.card (centralizer ({t} : Set (alternatingGroup (Fin n)))) := by
  set CS := centralizer ({(t : Perm (Fin n))} : Set (Perm (Fin n))) with hCS
  let φ : CS →* ℤˣ := (Perm.sign).comp CS.subtype
  have hmem : ∀ x : alternatingGroup (Fin n),
      x ∈ centralizer ({t} : Set (alternatingGroup (Fin n))) → (x : Perm (Fin n)) ∈ CS := by
    intro x hx
    rw [mem_centralizer_singleton_iff] at hx ⊢
    exact congrArg Subtype.val hx
  let ψ : centralizer ({t} : Set (alternatingGroup (Fin n))) → φ.ker := fun x =>
    ⟨⟨(x : alternatingGroup (Fin n)).1, hmem _ x.2⟩, by
      rw [MonoidHom.mem_ker]
      show Perm.sign (x : alternatingGroup (Fin n)).1 = 1
      exact Perm.mem_alternatingGroup.1 (x : alternatingGroup (Fin n)).2⟩
  have hψ : Function.Bijective ψ := by
    constructor
    · intro x y hxy
      have := congrArg (fun z : φ.ker => ((z : CS) : Perm (Fin n))) hxy
      exact Subtype.ext (Subtype.ext this)
    · rintro ⟨⟨c, hc⟩, hk⟩
      have hs : Perm.sign c = 1 := hk
      refine ⟨⟨⟨c, Perm.mem_alternatingGroup.2 hs⟩, ?_⟩, rfl⟩
      rw [mem_centralizer_singleton_iff] at hc ⊢
      exact Subtype.ext hc
  have hker : Nat.card φ.ker = Nat.card (centralizer ({t} : Set (alternatingGroup (Fin n)))) :=
    (Nat.card_congr (Equiv.ofBijective ψ hψ)).symm
  have h1 := Subgroup.card_ker_mul_card_range φ
  have h2 : Nat.card φ.range ≤ 2 := by
    have := Subgroup.card_le_card_group φ.range
    have h3 : Nat.card ℤˣ = 2 := by simp [Nat.card_eq_fintype_card]
    omega
  have h3 : Nat.card φ.range ∣ 2 := by
    have hp : 0 < Nat.card φ.range := Nat.card_pos
    interval_cases h : Nat.card φ.range
    · exact dvd_rfl.trans (by norm_num)
    · exact dvd_rfl
  rw [← hker, ← h1, mul_comm 2]
  exact ⟨Dvd.intro _ rfl, mul_dvd_mul_left _ h3⟩

theorem false_of_alternating_involution_centralizer {n : ℕ} (t : alternatingGroup (Fin n))
    (ht : orderOf t = 2)
    (hc : Nat.card (centralizer ({t} : Set (alternatingGroup (Fin n)))) = 177408000) : False := by
  have ht' : orderOf (t : Perm (Fin n)) = 2 := by rw [Subgroup.orderOf_coe]; exact ht
  obtain ⟨a, -, hcs⟩ := card_centralizer_perm_involution (t : Perm (Fin n)) ht'
  obtain ⟨hd1, hd2⟩ := card_centralizer_alternating_dvd t
  rw [hc] at hd1 hd2
  rw [hcs] at hd1 hd2
  have h11 : 11 ∣ (n - a * 2).factorial * 2 ^ a * a.factorial :=
    (show 11 ∣ 177408000 by norm_num).trans hd1
  have hp : Nat.Prime 11 := by norm_num
  have h81 : 81 ∣ (n - a * 2).factorial * 2 ^ a * a.factorial := by
    have h11f : 81 ∣ (11 : ℕ).factorial := by decide
    rcases (Nat.Prime.dvd_mul hp).1 h11 with h | h
    · rcases (Nat.Prime.dvd_mul hp).1 h with h | h
      · have := (hp.dvd_factorial).1 h
        exact ((h11f.trans (Nat.factorial_dvd_factorial this)).mul_right _).mul_right _
      · exact absurd (hp.dvd_of_dvd_pow h) (by norm_num)
    · have := (hp.dvd_factorial).1 h
      exact (h11f.trans (Nat.factorial_dvd_factorial this)).mul_left _
  have := h81.trans hd2
  norm_num at this

theorem false_of_isAlternating {G : Type} [Group G] {n : ℕ} (e : G ≃* alternatingGroup (Fin n))
    (ht : ∃ t : G, orderOf t = 2 ∧ Nat.card (centralizer ({t} : Set G)) = 177408000) : False := by
  obtain ⟨t, ht2, htc⟩ := ht
  refine false_of_alternating_involution_centralizer (e t) (by rw [MulEquiv.orderOf_eq]; exact ht2) ?_
  rw [← htc]
  refine (Nat.card_congr ?_).symm
  refine Equiv.subtypeEquiv e.toEquiv fun x => ?_
  rw [mem_centralizer_singleton_iff, mem_centralizer_singleton_iff]
  constructor
  · intro h
    exact by simpa using congrArg e h
  · intro h
    exact e.injective (by simpa using h)

theorem card_psl_four {Y : Type} [Group Y] {f : ℕ} (hf : 1 ≤ f) (h : LieModel Y .PSL 4 2 f) :
    Nat.card Y = (2 ^ f) ^ 6 * (((2 ^ f) ^ 2 - 1) * (((2 ^ f) ^ 3 - 1) * ((2 ^ f) ^ 4 - 1))) := by
  rcases h with ⟨-, hc⟩ | ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩
  · have h1 := (CFSG.Timmesfeld.card_statedClassicalModel_two hc).1 rfl
    rw [h1, CFSG.Open.ordA]
    have hodd : Odd (2 ^ f - 1) := by
      have := CFSG.Timmesfeld.ClassicalOrders.odd_two_pow_pow_sub_one hf (n := 1) le_rfl
      simpa using this
    have hg : Nat.gcd (3 + 1) (2 ^ f - 1) = 1 := by
      show Nat.gcd 4 (2 ^ f - 1) = 1
      exact CFSG.Timmesfeld.ClassicalOrders.gcd_four_eq_one hodd
    rw [hg, Nat.div_one]
    simp [Finset.prod_Icc_succ_top, mul_assoc]
  all_goals exact absurd h0 (by norm_num)

theorem false_of_lemmaE
    (hCo1 : Co1InvCentralizers) {G : Type} [Group G] [Finite G]
    (hHS : 44352000 ∣ Nat.card G)
    (ht : ∃ t : G, orderOf t = 2 ∧ Nat.card (centralizer ({t} : Set G)) = 177408000)
    (h : (∃ n : ℕ, 9 ≤ n ∧ Nonempty (G ≃* alternatingGroup (Fin n))) ∨
      (IsSporadic G .J2 ∨ IsSporadic G .Suz ∨ IsSporadic G .He ∨ IsSporadic G .Ru ∨
        IsSporadic G .Co1)) : False := by
  rcases h with ⟨n, -, ⟨e⟩⟩ | h | h | h | h | h
  · exact false_of_isAlternating e ht
  · obtain ⟨e⟩ := h
    have hc : Nat.card G = 604800 :=
      (Nat.card_congr e.toEquiv).trans CFSG.Sporadic.J2.card_J2
    rw [hc] at hHS
    exact absurd (Nat.le_of_dvd (by norm_num) hHS) (by norm_num)
  · obtain ⟨e⟩ := h
    have hc : Nat.card G = 448345497600 :=
      (Nat.card_congr e.toEquiv).trans CFSG.Sporadic.Suz.card_Suz
    rw [hc] at hHS
    exact absurd hHS (by norm_num)
  · obtain ⟨e⟩ := h
    have hc : Nat.card G = 4030387200 :=
      (Nat.card_congr e.toEquiv).trans CFSG.Sporadic.He.card_He
    rw [hc] at hHS
    exact absurd hHS (by norm_num)
  · obtain ⟨e⟩ := h
    have hc : Nat.card G = 145926144000 :=
      (Nat.card_congr e.toEquiv).trans CFSG.Sporadic.Ru.card_Ru
    rw [hc] at hHS
    exact absurd hHS (by norm_num)
  · obtain ⟨t, ht2, htc⟩ := ht
    exact hCo1 G h t ht2 htc

theorem false_of_lemmaE_largeAlt
    {G : Type} [Group G] [Finite G] (hHS : 44352000 ∣ Nat.card G)
    (ht : ∃ t : G, orderOf t = 2 ∧ Nat.card (centralizer ({t} : Set G)) = 177408000)
    (h : (∃ n : ℕ, 9 ≤ n ∧ Nonempty (G ≃* alternatingGroup (Fin n))) ∨
      IsSporadic G .McL ∨ IsSporadic G .Ly) : False := by
  rcases h with ⟨n, -, ⟨e⟩⟩ | h | h
  · exact false_of_isAlternating e ht
  · obtain ⟨e⟩ := h
    have hc : Nat.card G = 898128000 :=
      (Nat.card_congr e.toEquiv).trans CFSG.Sporadic.McL.card_McL
    rw [hc] at hHS
    exact not_dvd_card_McL hHS
  · obtain ⟨e⟩ := h
    have hc : Nat.card G = 51765179004000000 :=
      (Nat.card_congr e.toEquiv).trans CFSG.Sporadic.Ly.card_Ly
    rw [hc] at hHS
    exact not_dvd_card_Ly hHS

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus.Outer
