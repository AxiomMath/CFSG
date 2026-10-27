module

public import CFSG.LargeExtraspecial.S10EightA

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S13

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6 CFSG.LargeExtraspecial.S10

universe u

theorem mem_normalizer_of_commute {X : Type*} [Group X] {N : Subgroup X} {x : X}
    (hx : ∀ y ∈ N, x * y = y * x) : x ∈ normalizer (N : Set X) := by
  rw [mem_normalizer_iff]
  intro y
  constructor
  · intro hy
    rw [hx y hy, mul_inv_cancel_right]
    exact hy
  · intro hy
    have h := hx _ hy
    have e : x * y * x⁻¹ = y := by
      have h' : x * (x * y * x⁻¹) = x * y := by rw [h]; group
      exact mul_left_cancel h'
    rw [e] at hy
    exact hy

theorem two_pow_dvd_of_dvd_three_mul {j m : ℕ} (h : 2 ^ j ∣ 3 * 2 ^ m) : 2 ^ j ∣ 2 ^ m :=
  (Nat.Coprime.pow_left j (by norm_num : Nat.Coprime 2 3)).dvd_of_dvd_mul_left h

variable {G : Type u} [Group G] [Finite G] {S : Setting G} {g : G} {t : S.O}

theorem Ebar_le_of_Rbar_eq (X : Hyp10 S g t) {Xb Yb : Subgroup S.O} (D : Dec108 X Xb Yb)
    (hL2 : Nat.card (S.Lbar g) = 2 * Nat.card (S.Lbar g ⊓ Xb : Subgroup S.O)) {τ : S.O}
    (hR : Rbar S g τ = (S.Lbar g ⊓ Xb) ⊔ Yb) {h : S.M} (hτ : τ ∈ S.Lbar ((h : G) * g)) :
    S.Lbar g ⊓ Xb ≤ S.Lbar ((h : G) * g) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set E := S.Lbar g ⊓ Xb with hE
  set L' := S.Lbar ((h : G) * g) with hL'
  have haQ := X.haQ
  have hc : ∀ e ∈ E, ∀ y ∈ E ⊔ Yb, y * e = e * y := by
    intro e he y hy
    have hle : E ⊔ Yb ≤ centralizer ({e} : Set S.O) := by
      refine sup_le (fun x hx => ?_) (fun x hx => ?_)
      · rw [mem_centralizer_singleton_iff]
        exact (S4.Lbar_comm S haQ he.1 hx.1).symm
      · rw [mem_centralizer_singleton_iff]
        exact (D.dec.comm e he.2 x hx).symm
    exact mem_centralizer_singleton_iff.mp (hle hy)
  have hL'R : L' ≤ E ⊔ Yb := hR ▸ Lbar_mul_le_Rbar hτ
  have hL'N : L' ≤ normalizer (E : Set S.O) := fun x hx =>
    mem_normalizer_of_commute fun e he => hc e he x (hL'R hx)
  have hYb : Nat.card Yb = 6 := by
    obtain ⟨e⟩ := D.dec.iso
    rw [Nat.card_congr e.toEquiv, Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin]
    rfl
  have hinf : E ⊓ Yb = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [← D.dec.inf]
    exact ⟨hx.1.2, hx.2⟩
  have hEY : Nat.card (E ⊔ Yb : Subgroup S.O) = 6 * Nat.card E := by
    have h1 := card_sup_mul_card_inf (A := E) (N := Yb) fun x hx =>
      mem_normalizer_of_commute fun y hy => D.dec.comm x hx.2 y hy
    rw [hinf, card_bot, mul_one, hYb] at h1
    rw [h1, mul_comm]
  have hpL' : IsPGroup 2 L' := isPGroup_Lbar S (conj_mem_QG' S h.2 haQ)
  have hpE : IsPGroup 2 E := (isPGroup_Lbar S haQ).to_le inf_le_left
  have hpT : IsPGroup 2 (L' ⊔ E : Subgroup S.O) := hpL'.to_sup_of_normal_right' hpE hL'N
  obtain ⟨j, hj⟩ := hpT.exists_card_eq
  have hTle : L' ⊔ E ≤ E ⊔ Yb := sup_le hL'R le_sup_left
  have hdvd := Subgroup.card_dvd_of_le hTle
  rw [hEY, hj] at hdvd
  have hcardL' : Nat.card L' = Nat.card (S.Lbar g) := by
    rw [hL', Lbar_mul S h g]
    exact Subgroup.card_map_of_injective (MulAut.conj (S.ρ h)).injective
  obtain ⟨m, hm⟩ := hpE.exists_card_eq
  rw [hm, show 6 * 2 ^ m = 3 * 2 ^ (m + 1) by ring] at hdvd
  have h2 := Nat.le_of_dvd (by positivity) (two_pow_dvd_of_dvd_three_mul hdvd)
  have hcardT : Nat.card (L' ⊔ E : Subgroup S.O) ≤ Nat.card L' := by
    rw [hj, hcardL', hL2, hm]
    calc 2 ^ j ≤ 2 ^ (m + 1) := h2
      _ = 2 * 2 ^ m := by ring
  have heq := Subgroup.eq_of_le_of_card_ge (le_sup_left : L' ≤ L' ⊔ E) hcardT
  exact heq ▸ le_sup_right

end CFSG.LargeExtraspecial.S13
