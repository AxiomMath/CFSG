module

public import CFSG.CGT.PushingUpLit.T2K.FourFourA

public section

namespace CFSG.CGT.PushingUpLit.T2K

open CFSG CFSG.RankThree.PartOne CFSG.Open CFSG.Quasithin CFSG.CGT.PushingUpLit.BHS
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem exists_central_involution {T S₀ : Subgroup G} (hT : IsPGroup 2 T) (hST : S₀ ≤ T)
    (hn : T ≤ Subgroup.normalizer (S₀ : Set G)) (hne : S₀ ≠ ⊥) :
    ∃ z : G, z ∈ S₀ ∧ z ∈ T ∧ (∀ t ∈ T, t * z = z * t) ∧ z ^ 2 = 1 ∧ z ≠ 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hnil : Group.IsNilpotent ↥T := hT.isNilpotent
  have hnormal : (S₀.subgroupOf T).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hST).2 hn
  have hbot : S₀.subgroupOf T ≠ ⊥ := by
    intro h0
    apply hne
    rw [eq_bot_iff]
    intro x hx
    have hxT : x ∈ T := hST hx
    have : (⟨x, hxT⟩ : ↥T) ∈ S₀.subgroupOf T := hx
    rw [h0, Subgroup.mem_bot] at this
    have := congrArg Subtype.val this
    simpa using this
  have hY := Group.IsNilpotent.inf_center_ne_bot_of_normal (H := S₀.subgroupOf T) hbot
  set Y : Subgroup ↥T := S₀.subgroupOf T ⊓ Subgroup.center ↥T with hYdef
  have hYp : IsPGroup 2 ↥Y := hT.to_subgroup Y
  obtain ⟨a, ha⟩ := (IsPGroup.iff_card).1 hYp
  have hev : Even (Nat.card ↥Y) := by
    have ha0 : a ≠ 0 := by
      rintro rfl
      apply hY
      refine Subgroup.eq_bot_of_card_eq _ ?_
      simpa using ha
    rw [ha]
    exact (Nat.even_pow.2 ⟨even_two, ha0⟩)
  obtain ⟨u, hu2⟩ := exists_prime_orderOf_dvd_card' 2 (even_iff_two_dvd.1 hev)
  have hord : orderOf (u : ↥T) = 2 := by rw [Subgroup.orderOf_coe]; exact hu2
  have hsq : (u : ↥T) ^ 2 = 1 := by rw [← hord]; exact pow_orderOf_eq_one _
  have hu1 : (u : ↥T) ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hord
    omega
  refine ⟨((u : ↥T) : G), u.2.1, (u : ↥T).2, fun t ht => ?_, ?_, ?_⟩
  · have := Subgroup.mem_center_iff.1 u.2.2 ⟨t, ht⟩
    exact congrArg Subtype.val this
  · have := congrArg Subtype.val hsq
    simpa using this
  · intro h1
    exact hu1 (Subtype.ext (by simpa using h1))

namespace T2Hyp

variable {L M T : Subgroup G} {n : ℕ}
variable (h : T2Hyp G L M n) (hE1 : FooteNonsolvableSimple)
  (hT : CFSG.ABGLocalTools.IsSylowOf 2 T M)
include h hE1 hT

theorem le_normalizer_inf_centralizer :
    T ≤ Subgroup.normalizer ((T ⊓ Subgroup.centralizer (L : Set G) : Subgroup G) : Set G) := by
  intro t ht
  rw [Subgroup.mem_normalizer_iff]
  intro p
  have hC : t ∈ Subgroup.normalizer (Subgroup.centralizer (L : Set G) : Set G) :=
    mem_normalizer_centralizer (h.normal hE1 (hT.le ht))
  have h1 := Subgroup.mem_normalizer_iff.1 hC p
  have h2 := Subgroup.mem_normalizer_iff.1 (Subgroup.le_normalizer ht : t ∈ Subgroup.normalizer
    (T : Set G)) p
  simp only [Subgroup.mem_inf, h1, h2]

theorem five_two (hne : T ⊓ Subgroup.centralizer (L : Set G) ≠ ⊥) :
    Subgroup.centralizer (omegaOneCenterOf T : Set G) ≤ M := by
  obtain ⟨z, hzS, hzT, hzc, hz2, hz1⟩ := exists_central_involution hT.isPGroup inf_le_left
    (h.le_normalizer_inf_centralizer hE1 hT) hne
  have hzΩ : z ∈ omegaOneCenterOf T :=
    Subgroup.subset_closure ⟨⟨hzT, Subgroup.mem_centralizer_iff.2 hzc⟩,
      hz2⟩
  have hloc := isPLocal_centralizer_of_sq hz2 hz1
  obtain ⟨N, hle, hNmax⟩ := Sec15Final.exists_isMaximalTwoLocal_ge hloc
  have hLC : L ≤ Subgroup.centralizer ({z} : Set G) := fun l hl =>
    Subgroup.mem_centralizer_singleton_iff.2 (Subgroup.mem_centralizer_iff.1 hzS.2 l hl)
  have hNM : N = M := by
    have : N ∈ maximalTwoLocalsContaining (L : Set G) := ⟨hNmax, fun x hx => hle (hLC hx)⟩
    rw [h.unique] at this
    exact this
  intro x hx
  rw [← hNM]
  exact hle (Subgroup.mem_centralizer_singleton_iff.2
    (Subgroup.mem_centralizer_iff.1 hx z hzΩ).symm)

end T2Hyp

end CFSG.CGT.PushingUpLit.T2K
