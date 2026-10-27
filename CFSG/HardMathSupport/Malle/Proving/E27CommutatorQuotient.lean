module

public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG.HardMathSupport.Malle.Proving

open Subgroup
open scoped commutatorElement

theorem eighty_one_dvd_inf_centralizer_of_commutator_le
    {G : Type*} [Group G] [Finite G] (P : Sylow 3 G) (N : Subgroup G)
    (hcomm : ⁅(P : Subgroup G), (P : Subgroup G)⁆ ≤ N) (h81 : 81 * Nat.card N ≤ Nat.card P)
    {s : G} (hs : s ∈ (P : Subgroup G)) :
    81 ∣ Nat.card ↥((P : Subgroup G) ⊓ Subgroup.centralizer ({s} : Set G)) := by
  set Q : Subgroup G := (P : Subgroup G) with hQ
  set C : Subgroup G := Q ⊓ Subgroup.centralizer ({s} : Set G) with hC
  have hCQ : C ≤ Q := inf_le_left
  set H : Subgroup ↥Q := C.subgroupOf Q with hH
  have hmemN : ∀ y : ↥Q, (y : G) * s * (y : G)⁻¹ * s⁻¹ ∈ N := by
    intro y
    have h1 : ⁅(y : G), s⁆ ∈ ⁅(Q : Subgroup G), (Q : Subgroup G)⁆ :=
      Subgroup.commutator_mem_commutator y.2 hs
    have h2 : ⁅(y : G), s⁆ ∈ N := hcomm h1
    rw [commutatorElement_def] at h2
    exact h2
  have hidx : H.index ≤ Nat.card N := by
    let f : (↥Q ⧸ H) → N := Quotient.lift
      (fun y : ↥Q => (⟨(y : G) * s * (y : G)⁻¹ * s⁻¹, hmemN y⟩ : N))
      (by
        intro a b hab
        apply Subtype.ext
        have hmem : (a : G)⁻¹ * (b : G) ∈ C := by
          have h1 := QuotientGroup.leftRel_apply.mp hab
          rw [Subgroup.mem_subgroupOf] at h1
          simpa using h1
        have hxs : (a : G)⁻¹ * (b : G) * s * ((a : G)⁻¹ * (b : G))⁻¹ = s := by
          have hc := (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hmem).2) s
            (Set.mem_singleton s)
          rw [mul_inv_eq_iff_eq_mul, ← hc]
        have hb : (b : G) = (a : G) * ((a : G)⁻¹ * (b : G)) := by group
        have key : (b : G) * s * (b : G)⁻¹ = (a : G) * s * (a : G)⁻¹ := by
          rw [hb]
          have e1 : (a : G) * ((a : G)⁻¹ * (b : G)) * s *
              ((a : G) * ((a : G)⁻¹ * (b : G)))⁻¹ =
              (a : G) * (((a : G)⁻¹ * (b : G)) * s * ((a : G)⁻¹ * (b : G))⁻¹) * (a : G)⁻¹ := by
            group
          rw [e1, hxs]
        show (a : G) * s * (a : G)⁻¹ * s⁻¹ = (b : G) * s * (b : G)⁻¹ * s⁻¹
        rw [key])
    have hf : Function.Injective f := by
      intro u v huv
      obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective u
      obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective v
      have h2 : (a : G) * s * (a : G)⁻¹ * s⁻¹ = (b : G) * s * (b : G)⁻¹ * s⁻¹ :=
        congrArg Subtype.val huv
      have key : (a : G) * s * (a : G)⁻¹ = (b : G) * s * (b : G)⁻¹ := mul_right_cancel h2
      have hxs : (a : G)⁻¹ * (b : G) * s * ((a : G)⁻¹ * (b : G))⁻¹ = s := by
        have e1 : (a : G)⁻¹ * (b : G) * s * ((a : G)⁻¹ * (b : G))⁻¹ =
            (a : G)⁻¹ * ((b : G) * s * (b : G)⁻¹) * (a : G) := by group
        rw [e1, ← key]
        group
      have hcx : s * ((a : G)⁻¹ * (b : G)) = ((a : G)⁻¹ * (b : G)) * s :=
        (mul_inv_eq_iff_eq_mul.mp hxs).symm
      have hmemC : (a : G)⁻¹ * (b : G) ∈ C := by
        rw [hC, Subgroup.mem_inf]
        refine ⟨?_, ?_⟩
        · exact Q.mul_mem (Q.inv_mem a.2) b.2
        · exact (Subgroup.mem_centralizer_iff).mpr fun h hh => by
            rw [Set.mem_singleton_iff.mp hh]
            exact hcx
      apply QuotientGroup.eq.mpr
      rw [hH, Subgroup.mem_subgroupOf]
      simpa using hmemC
    have := Nat.card_le_card_of_injective f hf
    exact this
  have hcard : Nat.card H = Nat.card C :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hCQ).toEquiv
  have hQcard : Nat.card ↥Q = Nat.card H * H.index := (Subgroup.card_mul_index H).symm
  have hpow : ∃ n : ℕ, Nat.card H = 3 ^ n := by
    have hQ3 : IsPGroup 3 ↥Q := P.isPGroup'
    exact IsPGroup.iff_card.mp (hQ3.to_subgroup H)
  obtain ⟨n, hn⟩ := hpow
  have hNpos : 0 < Nat.card N := Nat.card_pos
  have h81le : 81 ≤ Nat.card H := by
    have h1 : 81 * Nat.card N ≤ Nat.card H * Nat.card N := by
      calc 81 * Nat.card N ≤ Nat.card ↥Q := h81
        _ = Nat.card H * H.index := hQcard
        _ ≤ Nat.card H * Nat.card N := Nat.mul_le_mul_left _ hidx
    exact le_of_mul_le_mul_right h1 hNpos
  have h4 : 4 ≤ n := by
    by_contra hlt
    have hn3 : n ≤ 3 := by omega
    have h3 : 3 ^ n ≤ 3 ^ 3 := Nat.pow_le_pow_right (by norm_num) hn3
    rw [← hn] at h3
    omega
  have hdvd : 81 ∣ Nat.card H := by
    rw [hn]
    have h81eq : (81 : ℕ) = 3 ^ 4 := by norm_num
    rw [h81eq]
    exact pow_dvd_pow 3 h4
  rw [hcard] at hdvd
  exact hdvd

end CFSG.HardMathSupport.Malle.Proving
