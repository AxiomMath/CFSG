module

public import CFSG.GH74.GLS.Stage1.Thm3.Sec8.Ctx38
public import CFSG.GH74.GLS.Stage1.Thm3.Sec8.Ctx20
public import CFSG.GH74.GLS.Stage1.Thm3.Sec8.Ctx31

public section

namespace CFSG.GH74.GLS.Stage1.Thm3.Sec8

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage1.Thm2.Recip
  CFSG.GH74.GLS.Stage1.Thm3.Sec4 CFSG.GH74.GLS.Stage1.Thm3.Sec5 CFSG.GH74.GLS.Stage1.Thm3.Sec6
open scoped commutatorElement Pointwise

namespace Setup8

variable {G : Type} [Group G] [Finite G] {z : G} {S K₁ K₂ W₁ W₂ U : Subgroup G} {u h : G}

theorem W_normS (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h) {s : G} (hsS : s ∈ S) {w : G}
    (hw : w ∈ Wsub S U) : s * w * s⁻¹ ∈ Wsub S U := by
  refine Subgroup.mem_inf.2 ⟨mul_mem (mul_mem hsS hw.1) (inv_mem hsS), Subgroup.mem_centralizer_iff.2
    (fun x hx => ?_)⟩
  have h1 : s⁻¹ * x * s ∈ U := by
    have := hs.U_norm s⁻¹ (inv_mem hsS) x hx
    simpa using this
  have h2 : w * (s⁻¹ * x * s) * w⁻¹ = s⁻¹ * x * s := hs.W_cent_U hw h1
  have h3 : w * (s⁻¹ * x * s) = (s⁻¹ * x * s) * w := by
    calc w * (s⁻¹ * x * s) = (w * (s⁻¹ * x * s) * w⁻¹) * w := by group
      _ = (s⁻¹ * x * s) * w := by rw [h2]
  calc x * (s * w * s⁻¹) = s * ((s⁻¹ * x * s) * w) * s⁻¹ := by group
    _ = s * (w * (s⁻¹ * x * s)) * s⁻¹ := by rw [h3]
    _ = (s * w * s⁻¹) * x := by group

theorem W_inf_h (hII : II4_4_4_center) (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h) :
    Wsub S U ⊓ zpowers h = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  rw [Subgroup.mem_bot]
  exact hs.S_inf_h hII hx.1.1 hx.2

theorem h_le_normalizer_W (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h) :
    zpowers h ≤ normalizer ((Wsub S U : Subgroup G) : Set G) := by
  rw [zpowers_le]
  exact hs.h_W

theorem exists_t₀ (hII : II4_4_4_center) (hq : II4_4_quat)
    (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h) (hk : Nat.card ↥(Vof S K₁ W₂) = 2 ^ (1 + 1)) :
    ∃ t₀ ∈ Pz S z, t₀ * t₀ = 1 ∧ t₀ * u * t₀⁻¹ = u * z := by
  obtain ⟨y₁, hy₁P, hy₁sq, hy₁inv, -⟩ := hs.exists_y₁ hII hq hk
  have hy := hs.y₁_conj_u hII hq hy₁P hy₁inv
  have hy₁S : y₁ ∈ S := hy₁P.1
  have hy₁Pz : y₁ ∈ Pz S z := by
    rw [hs.Pz_eq_sup hII]
    exact Subgroup.mem_sup_left hy₁P
  have hz₁ : h⁻¹ * z * h ∈ Pz S z := hs.U_le_Pz hII hq hs.hz_inv_mem_U
  exact ⟨y₁ * (h⁻¹ * z * h), mul_mem hy₁Pz hz₁, hs.t_sq hII hy₁S hy₁sq hy, hs.t_conj_u hy⟩

theorem relIndex_W_eq_two (hII : II4_4_4_center) (hq : II4_4_quat)
    (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h) (hk : Nat.card ↥(Vof S K₁ W₂) = 2 ^ (1 + 1)) :
    (Wsub S U).relIndex S = 2 := by
  obtain ⟨t₀, ht₀P, -, ht₀u⟩ := hs.exists_t₀ hII hq hk
  have hle := hs.relIndex_W_le_two hII
  have hne : (Wsub S U).relIndex S ≠ 1 := by
    intro h1
    have hall : S ≤ Wsub S U := Subgroup.relIndex_eq_one.1 h1
    have hW := (hs.mem_W_iff hII).1 (hall ht₀P.1)
    have h2 : t₀ * u * t₀⁻¹ = u := by rw [hW.2]; group
    rw [h2] at ht₀u
    apply hs.z_ne
    have := mul_left_cancel (a := u) (by simpa using ht₀u.symm : u * 1 = u * z)
    exact this.symm
  have hpos : (Wsub S U).relIndex S ≠ 0 := Basic.relIndex_ne_zero' _ _
  omega

theorem card_S_eq_two_W (hII : II4_4_4_center) (hq : II4_4_quat)
    (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h) (hk : Nat.card ↥(Vof S K₁ W₂) = 2 ^ (1 + 1)) :
    Nat.card ↥S = 2 * Nat.card ↥(Wsub S U) := by
  have h1 := Basic.card_mul_relIndex_of_le (W_le_S : Wsub S U ≤ S)
  rw [hs.relIndex_W_eq_two hII hq hk] at h1
  omega

theorem t₀_not_mem_W (hII : II4_4_4_center) (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h) {t₀ : G}
    (ht₀S : t₀ ∈ S) (ht₀u : t₀ * u * t₀⁻¹ = u * z) : t₀ ∉ Wsub S U := by
  intro hW
  have h1 := (hs.mem_W_iff hII).1 hW
  have h2 : t₀ * u * t₀⁻¹ = u := by rw [h1.2]; group
  rw [h2] at ht₀u
  apply hs.z_ne
  have := mul_left_cancel (a := u) (by simpa using ht₀u.symm : u * 1 = u * z)
  exact this.symm

theorem not_mem_M₁ (hII : II4_4_4_center) (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h) {t₀ : G}
    (ht₀S : t₀ ∈ S) (ht₀W : t₀ ∉ Wsub S U) : t₀ ∉ Wsub S U ⊔ zpowers h := by
  intro hmem
  obtain ⟨x₁, hx₁, w₁, hw₁, hx⟩ := Basic.mem_sup_of_le_normalizer' (A := zpowers h)
    (B := Wsub S U) hs.h_le_normalizer_W (sup_comm (Wsub S U) (zpowers h) ▸ hmem)
  have hx₁S : x₁ ∈ S := by
    have : x₁ = t₀ * w₁⁻¹ := by rw [hx]; group
    rw [this]
    exact mul_mem ht₀S (inv_mem hw₁.1)
  have hx1 : x₁ = 1 := hs.S_inf_h hII hx₁S hx₁
  rw [hx1, one_mul] at hx
  exact ht₀W (hx ▸ hw₁)

theorem N_decomp (hII : II4_4_4_center) (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h) {t₀ : G}
    (ht₀S : t₀ ∈ S) (ht₀W : t₀ ∉ Wsub S U) {n : G} (hn : n ∈ S ⊔ zpowers h) :
    n ∈ Wsub S U ⊔ zpowers h ∨ ∃ m ∈ Wsub S U ⊔ zpowers h, n = t₀ * m := by
  obtain ⟨s, hsS, i, rfl⟩ := hs.mem_N_decomp hn
  have hhi : h ^ i ∈ zpowers h := Subgroup.zpow_mem _ (Subgroup.mem_zpowers h) i
  by_cases hsW : s ∈ Wsub S U
  · left
    exact mul_mem (Subgroup.mem_sup_left hsW) (Subgroup.mem_sup_right hhi)
  · right
    have h1 : t₀⁻¹ * s ∈ Wsub S U :=
      hs.not_mem_W_mul hII (inv_mem ht₀S) hsS (fun h' => ht₀W (by simpa using inv_mem h')) hsW
    exact ⟨(t₀⁻¹ * s) * h ^ i, mul_mem (Subgroup.mem_sup_left h1) (Subgroup.mem_sup_right hhi),
      by group⟩

theorem M₁_norm (hII : II4_4_4_center) (hq : II4_4_quat) (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h)
    (hk : Nat.card ↥(Vof S K₁ W₂) = 2 ^ (1 + 1)) :
    ∀ n ∈ S ⊔ zpowers h, ∀ m ∈ Wsub S U ⊔ zpowers h, n * m * n⁻¹ ∈ Wsub S U ⊔ zpowers h := by
  obtain ⟨t₀, ht₀P, -, ht₀u⟩ := hs.exists_t₀ hII hq hk
  have ht₀S : t₀ ∈ S := ht₀P.1
  have ht₀W : t₀ ∉ Wsub S U := hs.t₀_not_mem_W hII ht₀S ht₀u
  have hnot := hs.not_mem_M₁ hII ht₀S ht₀W
  have hN : Wsub S U ⊔ zpowers h ≤ S ⊔ zpowers h := sup_le_sup W_le_S le_rfl
  intro n hn m hm
  rcases hs.N_decomp hII ht₀S ht₀W hn with h1 | ⟨m₀, hm₀, rfl⟩
  · exact mul_mem (mul_mem h1 hm) (inv_mem h1)
  · have hm' : m₀ * m * m₀⁻¹ ∈ Wsub S U ⊔ zpowers h := mul_mem (mul_mem hm₀ hm) (inv_mem hm₀)
    have e : t₀ * m₀ * m * (t₀ * m₀)⁻¹ = t₀ * (m₀ * m * m₀⁻¹) * t₀⁻¹ := by group
    rw [e]
    generalize m₀ * m * m₀⁻¹ = m' at hm' ⊢
    have ht₀N : t₀ ∈ S ⊔ zpowers h := Subgroup.mem_sup_left ht₀S
    have hmN : t₀ * m' * t₀⁻¹ ∈ S ⊔ zpowers h :=
      mul_mem (mul_mem ht₀N (hN hm')) (inv_mem ht₀N)
    rcases hs.N_decomp hII ht₀S ht₀W hmN with h2 | ⟨m'', hm'', h3⟩
    · exact h2
    · exfalso
      apply hnot
      have h4 : m' * t₀⁻¹ = m'' := mul_left_cancel (a := t₀) (by rw [← mul_assoc]; exact h3)
      have h5 : t₀⁻¹ = m'⁻¹ * m'' := eq_inv_mul_of_mul_eq h4
      have h6 : t₀⁻¹ ∈ Wsub S U ⊔ zpowers h := h5 ▸ mul_mem (inv_mem hm') hm''
      simpa using inv_mem h6

theorem card_M₁ (hII : II4_4_4_center) (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h) :
    Nat.card ↥(Wsub S U ⊔ zpowers h) = Nat.card ↥(Wsub S U) * Nat.card ↥(zpowers h) := by
  have h1 := Basic.card_sup_mul_card_inf' (A := Wsub S U) (B := zpowers h) hs.h_le_normalizer_W
  rw [hs.W_inf_h hII, Subgroup.card_bot, mul_one] at h1
  exact h1

theorem relIndex_h_M₁ (hII : II4_4_4_center) (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h) :
    (zpowers h).relIndex (Wsub S U ⊔ zpowers h) = Nat.card ↥(Wsub S U) := by
  have h1 := Basic.card_mul_relIndex_of_le (A := zpowers h) (B := Wsub S U ⊔ zpowers h) le_sup_right
  have hpos : 0 < Nat.card ↥(zpowers h) := Nat.card_pos
  have h2 : Nat.card ↥(zpowers h) * (zpowers h).relIndex (Wsub S U ⊔ zpowers h) =
      Nat.card ↥(zpowers h) * Nat.card ↥(Wsub S U) := by
    rw [h1, hs.card_M₁ hII, mul_comm]
  exact Nat.eq_of_mul_eq_mul_left hpos h2

theorem not_three_dvd_card_W (hII : II4_4_4_center) (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h) :
    ¬ 3 ∣ Nat.card ↥(Wsub S U) := by
  obtain ⟨a, ha⟩ := (IsPGroup.iff_card).1 ((hs.S_pgroup hII).to_le (W_le_S : Wsub S U ≤ S))
  rw [ha]
  intro h3
  have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3
  omega

end Setup8

end CFSG.GH74.GLS.Stage1.Thm3.Sec8
