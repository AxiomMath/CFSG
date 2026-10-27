module

public import CFSG.RankThree.PartOne.S12.PushingUp
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246B113Rank2

import CFSG.RankThree.PartOne.KF.BloomAut

public section

namespace CFSG.QuasithinUnique.Bridge

open Subgroup CFSG.RankThree.PartOne
open CFSG.ComponentClassification.PerfectAutomorphisms

theorem SylowAutTrivial.even_card {L : Type} [Group L] [Finite L] (h : SylowAutTrivial L)
    (hL : ∃ a b : L, a * b ≠ b * a) : Even (Nat.card L) := by
  by_contra hnot
  rw [Nat.not_even_iff_odd] at hnot
  let S : Sylow 2 L := default
  have hSbot : (S : Subgroup L) = ⊥ := by
    have hcard : Nat.card (S : Subgroup L) = 1 := by
      rw [show Nat.card (S : Subgroup L) = 2 ^ Nat.factorization (Nat.card L) 2 from
        S.card_eq_multiplicity]
      rw [Nat.factorization_eq_zero_of_not_dvd hnot.not_two_dvd_nat, pow_zero]
    have : Subsingleton ↥S := (Nat.card_eq_one_iff_unique.mp hcard).1
    exact Subgroup.eq_bot_of_subsingleton (S : Subgroup L)
  have hconj : ∀ g : L, MulAut.conj g = 1 := by
    intro g
    refine h S (MulAut.conj g) ?_ ?_
    · exact Odd.of_dvd_nat hnot
        (dvd_trans (orderOf_map_dvd MulAut.conj g) (orderOf_dvd_natCard g))
    · intro s hs
      rw [hSbot, Subgroup.mem_bot] at hs
      rw [hs]
      simp
  obtain ⟨a, b, hab⟩ := hL
  refine hab ?_
  have h1 : a * b * a⁻¹ = b := by
    simpa using congrArg (fun f : MulAut L => f b) (hconj a)
  calc a * b = a * b * a⁻¹ * a := by group
    _ = b * a := by rw [h1]

private lemma centerQuotient_fixes_image_str {K : Type} {D : Type*} [Group K] [Finite K] [Group D]
    (φ : D →* MulAut K) (P : Sylow 2 K)
    (hφ : ∀ d : D, ∀ x ∈ (P : Subgroup K), φ d x = x) (d : D)
    (x : K ⧸ Subgroup.center K)
    (hx : x ∈ (P.mapSurjective (QuotientGroup.mk'_surjective (Subgroup.center K)) :
      Subgroup (K ⧸ Subgroup.center K))) :
    (centerQuotientHom K (φ d)) x = x := by
  rw [Sylow.coe_mapSurjective] at hx
  obtain ⟨p, hp, rfl⟩ := Subgroup.mem_map.mp hx
  change (onCenterQuotient (φ d)) ((QuotientGroup.mk' (Subgroup.center K)) p) = _
  rw [onCenterQuotient_apply_mk, hφ d p hp]

private lemma centerQuotient_range_pow_order_str {K : Type} {D : Type*} [Group K] [Finite K]
    [Group D] [Finite D] (hR : SylowAutTrivial (K ⧸ Subgroup.center K)) (φ : D →* MulAut K)
    (P : Sylow 2 K) (hφ : ∀ d : D, ∀ x ∈ (P : Subgroup K), φ d x = x) :
    IsPGroup 2 ((centerQuotientHom K).comp φ).range := by
  let ψ : D →* MulAut (K ⧸ Subgroup.center K) := (centerQuotientHom K).comp φ
  let Pbar : Sylow 2 (K ⧸ Subgroup.center K) :=
    P.mapSurjective (QuotientGroup.mk'_surjective (Subgroup.center K))
  have hfix : ∀ d : D, ∀ x ∈ (Pbar : Subgroup (K ⧸ Subgroup.center K)), ψ d x = x := by
    intro d x hx
    exact centerQuotient_fixes_image_str φ P hφ d x (by
      rwa [show (Pbar : Subgroup (K ⧸ Subgroup.center K)) =
        P.map (QuotientGroup.mk' (Subgroup.center K)) from by
          simp only [Pbar, Sylow.coe_mapSurjective]])
  rw [IsPGroup.iff_orderOf]
  intro y
  have hpow : ∃ k : ℕ, orderOf (y : MulAut (K ⧸ Subgroup.center K)) = 2 ^ k := by
    obtain ⟨e, he⟩ := y.2
    rw [← he]
    have hne : orderOf (ψ e) ≠ 0 := by
      rintro h0
      exact (orderOf_pos e).ne' (Nat.eq_zero_of_zero_dvd (h0 ▸ orderOf_map_dvd ψ e))
    obtain ⟨k, m, hm, hkm⟩ := Nat.exists_eq_two_pow_mul_odd hne
    have h1 : orderOf ((ψ e) ^ 2 ^ k) = m := by
      rw [orderOf_pow_of_dvd (x := ψ e) (n := 2 ^ k) (pow_pos (by norm_num) k).ne'
        (by rw [hkm]; exact dvd_mul_right _ _)]
      rw [hkm, Nat.mul_div_cancel_left m (pow_pos (by norm_num) k)]
    have hfixpow : ∀ x ∈ (Pbar : Subgroup (K ⧸ Subgroup.center K)),
        ((ψ e) ^ 2 ^ k) x = x := by
      intro x hx
      have hpfix : ψ e x = x := hfix e x hx
      have hpowfix : ∀ n : ℕ, ((ψ e) ^ n) x = x := by
        intro n
        induction n with
        | zero => rfl
        | succ n ih => rw [pow_succ, MulAut.mul_apply, hpfix, ih]
      exact hpowfix (2 ^ k)
    have hq : (ψ e) ^ 2 ^ k = 1 := hR Pbar ((ψ e) ^ 2 ^ k) (by rw [h1]; exact hm) hfixpow
    have hm1 : m = 1 := by
      have := congrArg orderOf hq
      rwa [h1, orderOf_one] at this
    exact ⟨k, by rw [hkm, hm1, mul_one]⟩
  obtain ⟨k, hk⟩ := hpow
  refine ⟨k, ?_⟩
  rw [← orderOf_injective (ψ.range).subtype (ψ.range).subtype_injective y]
  exact hk

theorem SylowAutTrivial.eq_one_of_isPerfect {K : Type} {D : Type*} [Group K] [Finite K] [Group D]
    [Finite D] (hK : Group.IsPerfect K) (hR : SylowAutTrivial (K ⧸ center K))
    (hD : oResidualTwo D = ⊤) (φ : D →* MulAut K) (P : Sylow 2 K)
    (hφ : ∀ d : D, ∀ x ∈ (P : Subgroup K), φ d x = x) (d : D) : φ d = 1 := by
  have : Group.IsPerfect K := hK
  let ψ : D →* MulAut (K ⧸ center K) := (centerQuotientHom K).comp φ
  have h2grp : IsPGroup 2 (D ⧸ ψ.ker) := by
    have hrange : IsPGroup 2 ψ.range := centerQuotient_range_pow_order_str hR φ P hφ
    exact hrange.of_equiv (QuotientGroup.quotientKerEquivRange ψ).symm
  have hker : ψ.ker = ⊤ := by
    have hle : oResidualTwo D ≤ ψ.ker := sInf_le ⟨inferInstance, h2grp⟩
    rw [hD] at hle
    exact top_le_iff.mp hle
  have hψd : ψ d = 1 := MonoidHom.mem_ker.mp (by rw [hker]; trivial)
  exact onCenterQuotient_eq_one_imp (φ d) hψd

end CFSG.QuasithinUnique.Bridge
