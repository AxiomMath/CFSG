module

public import CFSG.GroupTheory.BurnsideNormalComplement
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf

open Subgroup

section Generic

variable {Γ : Type} [Group Γ]

def cent203bConjEquiv (Δ : Subgroup Γ) {x : Γ} (hx : x ∈ Subgroup.normalizer (Δ : Set Γ)) :
    Δ ≃* Δ where
  toFun d := ⟨x * (d : Γ) * x⁻¹, (Subgroup.mem_normalizer_iff.mp hx (d : Γ)).mp d.2⟩
  invFun d := ⟨x⁻¹ * (d : Γ) * x⁻¹⁻¹,
    (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hx) (d : Γ)).mp d.2⟩
  left_inv d := Subtype.ext (by simp [mul_assoc])
  right_inv d := Subtype.ext (by simp [mul_assoc])
  map_mul' a b := Subtype.ext (by simp [mul_assoc])

theorem cent203b_exists_normal_complement [Finite Γ] (Δ : Subgroup Γ) {z : Γ} (hzΔ : z ∈ Δ)
    (hz1 : z ≠ 1) (hz2 : z * z = 1) (hzc : ∀ d ∈ Δ, z * d = d * z)
    (hidx : ¬ 2 ∣ (Subgroup.zpowers z).relIndex Δ) :
    ∃ Y : Subgroup Γ, Y ≤ Δ ∧ Odd (Nat.card Y) ∧
      (∀ x ∈ Subgroup.normalizer (Δ : Set Γ), ∀ y ∈ Y, x * y * x⁻¹ ∈ Y) ∧
      ∀ d ∈ Δ, d ∈ Y ⊔ Subgroup.zpowers z := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set w : Δ := ⟨z, hzΔ⟩ with hwdef
  have hw2 : w * w = 1 := Subtype.ext hz2
  have hw1 : w ≠ 1 := fun h => hz1 (congrArg Subtype.val h)
  have hordw : orderOf w = 2 := orderOf_eq_prime (by rw [sq]; exact hw2) hw1
  set P : Subgroup Δ := Subgroup.zpowers w with hPdef
  have hPcard : Nat.card P = 2 := by rw [hPdef, Nat.card_zpowers, hordw]
  have hPΔ : (Subgroup.zpowers z).subgroupOf Δ = P := by
    ext h
    rw [Subgroup.mem_subgroupOf, hPdef, Subgroup.mem_zpowers_iff, Subgroup.mem_zpowers_iff]
    constructor
    · rintro ⟨k, hk⟩
      exact ⟨k, Subtype.ext (by simp [hwdef, hk])⟩
    · rintro ⟨k, hk⟩
      exact ⟨k, by rw [← hk]; simp [hwdef]⟩
  have hPidx : ¬ 2 ∣ P.index := by
    rw [← hPΔ]
    exact hidx
  have hPp : IsPGroup 2 P := IsPGroup.of_card (n := 1) (by rw [hPcard]; norm_num)
  set S : Sylow 2 Δ := hPp.toSylow hPidx with hSdef
  have hS : (S : Subgroup Δ) = P := IsPGroup.toSylow_coe hPp hPidx
  have hSnorm : Subgroup.normalizer ((S : Subgroup Δ) : Set Δ) ≤
      Subgroup.centralizer ((S : Subgroup Δ) : Set Δ) := by
    intro g _
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    have hh' : h ∈ P := by rw [← hS]; exact hh
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh'
    have hcom : Commute w g := Subtype.ext (hzc (g : Γ) g.2)
    exact (hcom.zpow_left k).eq
  obtain ⟨K₀, -, hK₀p, hK₀idx, -, hK₀char, -⟩ :=
    CFSG.GroupTheory.burnside_normal_complement S hSnorm
  rw [hS, hPcard] at hK₀idx
  have hK₀odd : Odd (Nat.card K₀) := Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp hK₀p)
  refine ⟨K₀.map Δ.subtype, Subgroup.map_subtype_le K₀, ?_, ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective Δ.subtype_injective]
    exact hK₀odd
  · intro x hx y hy
    obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hy
    have hfix := hK₀char.fixed (cent203bConjEquiv Δ hx)
    have hu' : cent203bConjEquiv Δ hx u ∈ K₀ := by
      have : u ∈ K₀.comap (cent203bConjEquiv Δ hx).toMonoidHom := by
        rw [hfix]
        exact hu
      exact this
    exact Subgroup.mem_map.mpr ⟨cent203bConjEquiv Δ hx u, hu', rfl⟩
  · intro d hd
    have htop : K₀ ⊔ P = ⊤ := by
      have hKP : K₀ ≤ K₀ ⊔ P := le_sup_left
      have hdvd : (K₀ ⊔ P).index ∣ 2 := by
        have := Subgroup.index_dvd_of_le hKP
        rwa [hK₀idx] at this
      have hrel := Subgroup.relIndex_mul_index hKP
      rw [hK₀idx] at hrel
      rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h2
      · exact Subgroup.index_eq_one.mp h1
      · exfalso
        rw [h2] at hrel
        have hr1 : K₀.relIndex (K₀ ⊔ P) = 1 := by omega
        have hle : K₀ ⊔ P ≤ K₀ := Subgroup.relIndex_eq_one.mp hr1
        have hPK : P ≤ K₀ := le_sup_right.trans hle
        have hdvd2 := Subgroup.card_dvd_of_le hPK
        rw [hPcard] at hdvd2
        exact hK₀p hdvd2
    have hmem : (⟨d, hd⟩ : Δ) ∈ K₀ ⊔ P := by
      rw [htop]
      exact Subgroup.mem_top _
    have hm := Subgroup.mem_map_of_mem Δ.subtype hmem
    have hPmap : P.map Δ.subtype = Subgroup.zpowers z := by
      rw [hPdef, MonoidHom.map_zpowers]
      rfl
    rw [Subgroup.map_sup, hPmap] at hm
    exact hm

theorem cent203b_two_dvd_index [Finite Γ] (H : Subgroup Γ) [H.Normal] {g : Γ} (hg : g ∉ H)
    (hg2 : g * g ∈ H) : 2 ∣ H.index := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 : ((g : Γ ⧸ H)) ^ 2 = 1 := by
    rw [sq, ← QuotientGroup.mk_mul, QuotientGroup.eq_one_iff]
    exact hg2
  have h2 : ((g : Γ ⧸ H)) ≠ 1 := fun h => hg ((QuotientGroup.eq_one_iff g).mp h)
  have hd := orderOf_dvd_natCard ((g : Γ ⧸ H))
  rw [orderOf_eq_prime h1 h2, ← Subgroup.index_eq_card] at hd
  exact hd

theorem cent203b_mem_sup_three (X A B C : Subgroup Γ) (hA : A ≤ X) (hB : B ≤ X) (hC : C ≤ X)
    (hAX : X ≤ Subgroup.normalizer (A : Set Γ)) (hBX : X ≤ Subgroup.normalizer (B : Set Γ))
    (hCX : X ≤ Subgroup.normalizer (C : Set Γ)) {g : Γ} (hg : g ∈ A ⊔ B ⊔ C) :
    ∃ a ∈ A, ∃ b ∈ B, ∃ c ∈ C, g = a * b * c := by
  haveI : (A.subgroupOf X).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hA).mpr hAX
  haveI : (B.subgroupOf X).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hB).mpr hBX
  haveI : (C.subgroupOf X).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hC).mpr hCX
  have hle : A ⊔ B ⊔ C ≤ ((A.subgroupOf X ⊔ B.subgroupOf X) ⊔ C.subgroupOf X).map X.subtype := by
    refine sup_le (sup_le ?_ ?_) ?_
    · intro a ha
      exact Subgroup.mem_map.mpr ⟨⟨a, hA ha⟩, Subgroup.mem_sup_left (Subgroup.mem_sup_left
        (Subgroup.mem_subgroupOf.mpr ha)), rfl⟩
    · intro b hb
      exact Subgroup.mem_map.mpr ⟨⟨b, hB hb⟩, Subgroup.mem_sup_left (Subgroup.mem_sup_right
        (Subgroup.mem_subgroupOf.mpr hb)), rfl⟩
    · intro c hc
      exact Subgroup.mem_map.mpr ⟨⟨c, hC hc⟩, Subgroup.mem_sup_right
        (Subgroup.mem_subgroupOf.mpr hc), rfl⟩
  obtain ⟨t, ht, rfl⟩ := Subgroup.mem_map.mp (hle hg)
  rw [Subgroup.mem_sup_of_normal_right] at ht
  obtain ⟨y, hy, c', hc', hyc⟩ := ht
  rw [Subgroup.mem_sup_of_normal_right] at hy
  obtain ⟨a', ha', b', hb', hab⟩ := hy
  refine ⟨(a' : Γ), Subgroup.mem_subgroupOf.mp ha', (b' : Γ), Subgroup.mem_subgroupOf.mp hb',
    (c' : Γ), Subgroup.mem_subgroupOf.mp hc', ?_⟩
  subst hyc
  subst hab
  simp

theorem cent203b_not_two_dvd {a b m : ℕ} (hm : m = a * b) (hm0 : m ≠ 0)
    (hpad : padicValNat 2 m ≤ 1) (hb : 2 ∣ b) : ¬ 2 ∣ a := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro ha
  have h4 : 2 ^ 2 ∣ m := by
    rw [hm, show (2 : ℕ) ^ 2 = 2 * 2 from rfl]
    exact mul_dvd_mul ha hb
  have := (padicValNat_dvd_iff_le hm0).mp h4
  omega

end Generic

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf
