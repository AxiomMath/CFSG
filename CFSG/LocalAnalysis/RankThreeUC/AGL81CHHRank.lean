module

public import CFSG.LocalAnalysis.SectionRank.PRank

public section

namespace CFSG.LocalAnalysis.RankThreeUC.AGL81C

open Subgroup
open scoped commutatorElement

private theorem isPGroup_three_of_pow_three {G : Type*} [Group G] {H : Subgroup G}
    (hexp : ∀ x ∈ H, x ^ 3 = 1) : IsPGroup 3 ↥H := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rw [IsPGroup.iff_orderOf]
  intro x
  have hx : ((x : H) : G) ^ 3 = 1 := hexp (x : G) x.2
  have hx' : x ^ 3 = 1 := Subtype.ext (by simpa using hx)
  have hdvd : orderOf x ∣ 3 := orderOf_dvd_iff_pow_eq_one.mpr hx'
  rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3
  · exact ⟨0, by rw [h1, pow_zero]⟩
  · exact ⟨1, by rw [h3, pow_one]⟩

private theorem isMulCommutative_sup_of_le_centralizer {G : Type*} [Group G] {A B : Subgroup G}
    (hAB : A ≤ Subgroup.centralizer (B : Set G)) (hA : IsMulCommutative ↥A)
    (hB : IsMulCommutative ↥B) : IsMulCommutative ↥(A ⊔ B) := by
  rw [Subgroup.sup_eq_closure]
  refine Subgroup.isMulCommutative_closure ?_
  rintro x (hx | hx) y (hy | hy) _
  · show x * y = y * x
    exact congrArg Subtype.val (hA.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  · show x * y = y * x
    exact (Subgroup.mem_centralizer_iff.mp (hAB hx) y hy).symm
  · show x * y = y * x
    exact Subgroup.mem_centralizer_iff.mp (hAB hy) x hx
  · show x * y = y * x
    exact congrArg Subtype.val (hB.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)

theorem three_le_pRank_of_exponent_three {K : Type*} [Group K] [Finite K] {Q : Subgroup K}
    (hexp : ∀ x ∈ Q, x ^ 3 = 1) (hclass : ⁅Q, Q⁆ ≤ centralizer (Q : Set K))
    (hindex : 3 ^ 3 ≤ (centralizer (Q : Set K)).relIndex Q) :
    3 ≤ CFSG.Open.pRank 3 Q := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let Z : Subgroup K := Q ⊓ centralizer (Q : Set K)
  have hZle : Z ≤ Q := inf_le_left
  have hZcent : Z ≤ centralizer (Q : Set K) := inf_le_right
  have hZrI : 27 ≤ Z.relIndex Q := by
    have h := Subgroup.inf_relIndex_right (H := centralizer (Q : Set K)) (K := Q)
    rw [inf_comm] at h
    rw [h]
    simpa using hindex
  have hQcard : Nat.card Q = Nat.card Z * Z.relIndex Q := by
    have h1 : Nat.card (Z.subgroupOf Q) * (Z.subgroupOf Q).index = Nat.card ↥Q :=
      (Z.subgroupOf Q).card_mul_index
    have h2 : Nat.card (Z.subgroupOf Q) = Nat.card Z :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZle).toEquiv
    rw [h2] at h1
    exact h1.symm
  have hQ27 : 27 ≤ Nat.card Q := by
    rw [hQcard]
    calc 27 = 1 * 27 := by norm_num
      _ ≤ Nat.card Z * Z.relIndex Q :=
          Nat.mul_le_mul (Nat.one_le_iff_ne_zero.mpr (Nat.card_pos.ne')) hZrI
  have hZpow : ∃ j, Nat.card Z = 3 ^ j :=
    (isPGroup_three_of_pow_three (fun z hz => hexp z (hZle hz))).exists_card_eq
  haveI : Nontrivial ↥Q :=
    (Subgroup.nontrivial_iff_ne_bot Q).mpr (fun hbot => by
      rw [hbot, Subgroup.card_bot] at hQ27
      omega)
  haveI : Nontrivial (Subgroup.center ↥Q) :=
    (isPGroup_three_of_pow_three hexp).center_nontrivial
  have hcenter_map : (Subgroup.center ↥Q).map Q.subtype = Z := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      refine ⟨y.2, ?_⟩
      change (y : K) ∈ Subgroup.centralizer (Q : Set K)
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hy (⟨h, hh⟩ : ↥Q))
    · rintro ⟨hxQ, hxcent⟩
      change x ∈ Subgroup.centralizer (Q : Set K) at hxcent
      refine ⟨⟨x, hxQ⟩, ?_, rfl⟩
      change (⟨x, hxQ⟩ : ↥Q) ∈ Subgroup.center ↥Q
      rw [Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hxcent (g : K) g.2)
  have hZcard_center : Nat.card Z = Nat.card (Subgroup.center ↥Q) := by
    rw [← hcenter_map]
    exact Subgroup.card_map_of_injective Q.subtype_injective
  have hZ2 : 1 < Nat.card Z := by
    rw [hZcard_center]
    exact Finite.one_lt_card
  obtain ⟨j, hj⟩ := hZpow
  have hj1 : 1 ≤ j := by
    by_contra h
    have h0 : j = 0 := by omega
    rw [h0, pow_zero] at hj
    omega
  have hZ3 : 3 ≤ Nat.card Z := by
    rw [hj]
    calc 3 = 3 ^ 1 := by norm_num
      _ ≤ 3 ^ j := Nat.pow_le_pow_right (by norm_num : 0 < 3) hj1
  have hZcomm : IsMulCommutative ↥Z :=
    (Subgroup.le_centralizer_iff_isMulCommutative (K := Z)).mp
      (hZcent.trans (Subgroup.centralizer_le hZle))
  have hZ_ne_Q : Z ≠ Q := by
    intro h
    have h1 : Z.relIndex Q = 1 := by rw [h, Subgroup.relIndex_self]
    omega
  have conclude : ∀ E : Subgroup K, E ≤ Q → IsMulCommutative ↥E →
      (∀ x ∈ E, x ^ 3 = 1) → 27 ≤ Nat.card E → 3 ≤ CFSG.Open.pRank 3 Q := by
    intro E hEQ hEcomm hEexp hEcard
    obtain ⟨k, hk⟩ := (isPGroup_three_of_pow_three hEexp).exists_card_eq
    have hk3 : 3 ≤ k := by
      have hpowle : 3 ^ 3 ≤ 3 ^ k := by
        rw [← hk]
        simpa using hEcard
      exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 3)).mp hpowle
    exact hk3.trans (CFSG.SectionRank.le_pRank (p := 3) (by norm_num) hEQ
      ⟨hEcomm, hEexp⟩ hk)
  obtain ⟨x₁, hx1Q, hx1Z⟩ : ∃ x ∈ Q, x ∉ Z := by
    by_contra h
    push Not at h
    exact hZ_ne_Q (le_antisymm hZle h)
  let E₁ : Subgroup K := Z ⊔ zpowers x₁
  have hE1le : E₁ ≤ Q := sup_le hZle (Subgroup.zpowers_le.mpr hx1Q)
  have hx1E1 : x₁ ∈ E₁ := Subgroup.mem_sup_right (Subgroup.mem_zpowers x₁)
  have hZltE1 : Z < E₁ :=
    lt_of_le_of_ne le_sup_left (fun h => hx1Z (h ▸ hx1E1))
  have hE1comm : IsMulCommutative ↥E₁ := by
    refine isMulCommutative_sup_of_le_centralizer (A := Z) (B := zpowers x₁) ?_
      hZcomm inferInstance
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
    exact hZcent.trans (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hx1Q))
  by_cases hbig : 27 ≤ Nat.card E₁
  · exact conclude E₁ hE1le hE1comm (fun y hy => hexp y (hE1le hy)) hbig
  ·
    have hE1lt : Nat.card E₁ < 27 := lt_of_not_ge hbig
    obtain ⟨a, ha⟩ :=
      (isPGroup_three_of_pow_three (fun y hy => hexp y (hE1le hy))).exists_card_eq
    have ha2 : 2 ≤ a := by
      have hlt : 3 ^ 1 < 3 ^ a := by
        calc 3 ^ 1 = 3 := by norm_num
          _ ≤ Nat.card Z := hZ3
          _ < Nat.card E₁ := Subgroup.card_lt_of_lt hZltE1
          _ = 3 ^ a := ha
      have : 1 < a := (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 3)).mp hlt
      omega
    have ha_eq : a = 2 := by
      have hlt3 : 3 ^ a < 3 ^ 3 := by
        calc 3 ^ a = Nat.card E₁ := ha.symm
          _ < 27 := hE1lt
          _ = 3 ^ 3 := by norm_num
      have : a < 3 := (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 3)).mp hlt3
      omega
    have hE1eq9 : Nat.card E₁ = 9 := by
      rw [ha, ha_eq]
      norm_num
    let C : Subgroup K := Q ⊓ centralizer ({x₁} : Set K)
    let φ : ↥Q →* K := MonoidHom.mk' (fun y => ⁅x₁, (y : K)⁆) (fun p q => by
      change ⁅x₁, (p : K) * (q : K)⁆ = ⁅x₁, (p : K)⁆ * ⁅x₁, (q : K)⁆
      have hcomm : (p : K) * ⁅x₁, (q : K)⁆ = ⁅x₁, (q : K)⁆ * (p : K) :=
        (Subgroup.mem_centralizer_iff.mp
          (hclass (Subgroup.commutator_mem_commutator hx1Q q.2))) (p : K) p.2
      calc ⁅x₁, (p : K) * (q : K)⁆
          = ⁅x₁, (p : K)⁆ * (p : K) * ⁅x₁, (q : K)⁆ * (p : K)⁻¹ :=
            commutatorElement_mul_right_eq_mul_conj _ _ _
        _ = ⁅x₁, (p : K)⁆ * ((p : K) * ⁅x₁, (q : K)⁆) * (p : K)⁻¹ := by group
        _ = ⁅x₁, (p : K)⁆ * (⁅x₁, (q : K)⁆ * (p : K)) * (p : K)⁻¹ := by rw [hcomm]
        _ = ⁅x₁, (p : K)⁆ * ⁅x₁, (q : K)⁆ := by group)
    have hφker : φ.ker = C.subgroupOf Q := by
      ext y
      rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
      constructor
      · intro h
        refine ⟨y.2, ?_⟩
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact (commutatorElement_eq_one_iff_mul_comm.mp h).symm
      · rintro ⟨-, hcent⟩
        rw [Subgroup.mem_centralizer_singleton_iff] at hcent
        exact commutatorElement_eq_one_iff_mul_comm.mpr hcent.symm
    have hφker_card : Nat.card φ.ker = Nat.card C := by
      rw [hφker]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left : C ≤ Q)).toEquiv
    have hrange_le_Z : φ.range ≤ Z := by
      rintro z hz
      obtain ⟨y, rfl⟩ := MonoidHom.mem_range.mp hz
      change ⁅x₁, (y : K)⁆ ∈ Z
      refine ⟨?_, hclass (Subgroup.commutator_mem_commutator hx1Q y.2)⟩
      rw [commutatorElement_def]
      exact Q.mul_mem (Q.mul_mem (Q.mul_mem hx1Q y.2) (Q.inv_mem hx1Q)) (Q.inv_mem y.2)
    have hC27 : 27 ≤ Nat.card C := by
      have hrange_le : Nat.card φ.range ≤ Nat.card Z := Subgroup.card_le_of_le hrange_le_Z
      have hineq : 27 * Nat.card φ.range ≤ Nat.card C * Nat.card φ.range := by
        calc 27 * Nat.card φ.range ≤ Z.relIndex Q * Nat.card Z :=
              Nat.mul_le_mul hZrI hrange_le
          _ = Nat.card Z * Z.relIndex Q := by rw [Nat.mul_comm]
          _ = Nat.card Q := hQcard.symm
          _ = Nat.card φ.ker * Nat.card φ.range :=
              (Subgroup.card_ker_mul_card_range φ).symm
          _ = Nat.card C * Nat.card φ.range := by rw [hφker_card]
      exact Nat.le_of_mul_le_mul_right hineq Nat.card_pos
    have hE1leC : E₁ ≤ C := by
      refine sup_le ?_ (Subgroup.zpowers_le.mpr ?_)
      · exact le_inf hZle
          (hZcent.trans (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hx1Q)))
      · exact ⟨hx1Q, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩
    obtain ⟨x₂, hx2C, hx2E1⟩ : ∃ x ∈ C, x ∉ E₁ := by
      by_contra h
      push Not at h
      have hEq : C = E₁ := le_antisymm h hE1leC
      have : Nat.card C = 9 := by rw [hEq, hE1eq9]
      omega
    let E : Subgroup K := E₁ ⊔ zpowers x₂
    have hEle : E ≤ Q := sup_le hE1le (Subgroup.zpowers_le.mpr hx2C.1)
    have hx2E : x₂ ∈ E := Subgroup.mem_sup_right (Subgroup.mem_zpowers x₂)
    have hE1ltE : E₁ < E :=
      lt_of_le_of_ne le_sup_left (fun h => hx2E1 (h ▸ hx2E))
    have hEcomm : IsMulCommutative ↥E := by
      refine isMulCommutative_sup_of_le_centralizer (A := E₁) (B := zpowers x₂) ?_
        hE1comm inferInstance
      have hx1_cent : x₁ ∈ centralizer ({x₂} : Set K) :=
        Subgroup.mem_centralizer_singleton_iff.mpr
          (Subgroup.mem_centralizer_singleton_iff.mp hx2C.2).symm
      have hZ_cent : Z ≤ centralizer ({x₂} : Set K) :=
        hZcent.trans (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hx2C.1))
      have hsup_le : E₁ ≤ centralizer ({x₂} : Set K) :=
        sup_le hZ_cent (Subgroup.zpowers_le.mpr hx1_cent)
      rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
      exact hsup_le
    obtain ⟨b, hb⟩ :=
      (isPGroup_three_of_pow_three (fun y hy => hexp y (hEle hy))).exists_card_eq
    have hE27 : 27 ≤ Nat.card E := by
      have hlt : 3 ^ 2 < 3 ^ b := by
        calc 3 ^ 2 = Nat.card E₁ := by rw [hE1eq9]; norm_num
          _ < Nat.card E := Subgroup.card_lt_of_lt hE1ltE
          _ = 3 ^ b := hb
      have hb3 : 3 ≤ b := by
        have : 2 < b := (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 3)).mp hlt
        omega
      rw [hb]
      calc 27 = 3 ^ 3 := by norm_num
        _ ≤ 3 ^ b := Nat.pow_le_pow_right (by norm_num : 0 < 3) hb3
    exact conclude E hEle hEcomm (fun y hy => hexp y (hEle hy)) hE27

end CFSG.LocalAnalysis.RankThreeUC.AGL81C
