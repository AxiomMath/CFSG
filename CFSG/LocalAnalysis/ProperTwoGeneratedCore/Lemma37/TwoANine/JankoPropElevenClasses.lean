module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.TwoANine.JankoPropElevenCentralizer

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37.TwoANine.JankoEleven

open Subgroup CFSG.Semidihedral.Principal.PrimewiseScalar

variable {G : Type} [Group G] {z : G} {fr : JankoFrame G z}

theorem eq_or_eq_inv_of_mem_P₁ {p q : G} (hp : p ∈ fr.P₁) (hp1 : p ≠ 1) (hq : q ∈ fr.P₁)
    (hq1 : q ≠ 1) : q = p ∨ q = p⁻¹ := by
  rw [fr.P₁_eq] at hp hq
  rcases eq_one_or_eq_or_eq_inv fr.orderOf_s₁ hp with rfl | rfl | rfl <;>
    rcases eq_one_or_eq_or_eq_inv fr.orderOf_s₁ hq with rfl | rfl | rfl
  all_goals first
    | exact absurd rfl hp1
    | exact absurd rfl hq1
    | exact Or.inl rfl
    | exact Or.inr rfl
    | exact Or.inr (inv_inv _).symm

theorem F_conj_P₁ {f p : G} (hf : f ∈ fr.F) (hp : p ∈ fr.P₁) : f * p * f⁻¹ = p := by
  rw [← Subgroup.mem_centralizer_iff.mp (fr.F_le_centralizer hf) p hp, mul_inv_cancel_right]

theorem conj_ne_one {g x : G} (hx : x ≠ 1) : g * x * g⁻¹ ≠ 1 :=
  fun h => hx (mul_eq_left.mp (mul_inv_eq_one.mp h))

theorem odd_card_F_inf_centralizer [Finite G] (p10 : JankoProp10 fr) (hz : orderOf z = 2)
    {x : G} (hx : x ∈ fr.Mbar) (hx1 : x ≠ 1) :
    Odd (Nat.card (fr.F ⊓ centralizer ({x} : Set G) : Subgroup G)) := by
  rw [← Nat.not_even_iff_odd]
  intro heven
  have hzC := z_mem_of_even (inf_le_left : fr.F ⊓ centralizer ({x} : Set G) ≤ fr.F) heven
  have h1 : z * x * z⁻¹ = x := by
    rw [mem_centralizer_singleton_iff.mp hzC.2, mul_inv_cancel_right]
  exact hx1 (eq_one_of_conj_eq_self_of_conj_eq_inv (p10.M_pow_three x (Mbar_le_M hx)) h1
    (inv_of_mem_Mbar p10 hz hx))

theorem exists_F_conj_Mbar [Finite G] (p7 : JankoProp7 fr) (p10 : JankoProp10 fr)
    (hz : orderOf z = 2) {x y : G} (hx : x ∈ fr.Mbar) (hx1 : x ≠ 1) (hy : y ∈ fr.Mbar)
    (hy1 : y ≠ 1) : ∃ f ∈ fr.F, f * x * f⁻¹ = y := by
  refine exists_conj_of_card_le (fun f hf w hw => ?_) hx hx1 ?_ hy hy1
  · exact conj_mem_of_mem_normalizer (normalizer_P₁_le_normalizer_Mbar p7 p10 hz
      (centralizer_P₁_le_normalizer_P₁ (fr.F_le_centralizer hf))) hw
  · rw [card_Mbar p10, fr.card_F]
    have h9 := fr.card_le_of_odd _ inf_le_left (odd_card_F_inf_centralizer p10 hz hx hx1)
    calc (81 - 1) * Nat.card (fr.F ⊓ centralizer ({x} : Set G) : Subgroup G) ≤ 80 * 9 :=
          Nat.mul_le_mul_left _ h9
      _ = 720 := by norm_num

theorem isConj_of_mem_Mbar [Finite G] (p7 : JankoProp7 fr) (p10 : JankoProp10 fr)
    (hz : orderOf z = 2) : ∀ x ∈ fr.Mbar, x ≠ 1 → IsConj x fr.s₃ := by
  intro x hx hx1
  have hAt : fr.At ≠ ⊥ := fun h => by
    have h9 := p10.card_At
    rw [h, Subgroup.card_bot] at h9
    norm_num at h9
  obtain ⟨⟨a, ha⟩, ha1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hAt
  have ha1' : a ≠ 1 := fun h => ha1 (Subtype.ext h)
  obtain ⟨f, -, hf⟩ := exists_F_conj_Mbar p7 p10 hz (At_le_Mbar ha) ha1' hx hx1
  exact (isConj_iff.mpr ⟨f, hf⟩).symm.trans (p10.isConj_of_mem_At a ha ha1')

theorem exists_conj_M [Finite G] (p7 : JankoProp7 fr) (p10 : JankoProp10 fr)
    (hz : orderOf z = 2) :
    ∀ x ∈ fr.M, ∀ y ∈ fr.M, x ∉ fr.P₁ → x ∉ fr.Mbar → y ∉ fr.P₁ → y ∉ fr.Mbar →
      ∃ g ∈ normalizer (fr.P₁ : Set G), g * x * g⁻¹ = y := by
  intro x hx y hy hxP hxM hyP hyM
  obtain ⟨p, hp, a, ha, rfl⟩ := exists_P₁_mul_Mbar p7 p10 hz hx
  obtain ⟨q, hq, b, hb, rfl⟩ := exists_P₁_mul_Mbar p7 p10 hz hy
  have hp1 : p ≠ 1 := fun h => hxM (by rw [h, one_mul]; exact ha)
  have ha1 : a ≠ 1 := fun h => hxP (by rw [h, mul_one]; exact hp)
  have hq1 : q ≠ 1 := fun h => hyM (by rw [h, one_mul]; exact hb)
  have hb1 : b ≠ 1 := fun h => hyP (by rw [h, mul_one]; exact hq)
  have hFN : ∀ f ∈ fr.F, f ∈ normalizer (fr.P₁ : Set G) := fun f hf =>
    centralizer_P₁_le_normalizer_P₁ (fr.F_le_centralizer hf)
  rcases eq_or_eq_inv_of_mem_P₁ hp hp1 hq hq1 with rfl | rfl
  · obtain ⟨f, hf, hfab⟩ := exists_F_conj_Mbar p7 p10 hz ha ha1 hb hb1
    exact ⟨f, hFN f hf, by rw [conj_mul_conj, F_conj_P₁ hf hp, hfab]⟩
  · have ha' : fr.t * a * fr.t⁻¹ ∈ fr.Mbar :=
      conj_mem_of_mem_normalizer (t_mem_normalizer_Mbar p7 p10 hz) ha
    obtain ⟨f, hf, hfab⟩ := exists_F_conj_Mbar p7 p10 hz ha' (conj_ne_one ha1) hb hb1
    refine ⟨f * fr.t, mul_mem (hFN f hf) (t_mem_normalizer_P₁ p7), ?_⟩
    have htp : fr.t * p * fr.t⁻¹ = p⁻¹ := conj_eq_inv_of_mem_P₁ fr.t_mul_s₁ hp
    calc f * fr.t * (p * a) * (f * fr.t)⁻¹ =
          f * (fr.t * p * fr.t⁻¹) * f⁻¹ * (f * (fr.t * a * fr.t⁻¹) * f⁻¹) := by group
      _ = p⁻¹ * b := by rw [htp, F_conj_P₁ hf (inv_mem hp), hfab]

theorem card_L₁ : Nat.card fr.L₁ = 8 := by rw [fr.L₁_eq, Nat.card_zpowers, fr.orderOf_ℓ]

theorem L₁_le_F : fr.L₁ ≤ fr.F := fr.L₁_eq ▸ zpowers_le.mpr fr.ℓ_mem_F

theorem L₁_le_L : fr.L₁ ≤ fr.L := by rw [← fr.L_inf_centralizer]; exact inf_le_left

theorem L₁_inf_centralizer_eq_bot [Finite G] (p7 : JankoProp7 fr) (p10 : JankoProp10 fr)
    (hz : orderOf z = 2) {s : G} (hs : s ∈ fr.S) (hs1 : s ≠ 1) :
    fr.L₁ ⊓ centralizer ({s} : Set G) = ⊥ := by
  by_contra hne
  have hdvd : Nat.card (fr.L₁ ⊓ centralizer ({s} : Set G) : Subgroup G) ∣ 2 ^ 3 := by
    rw [show (2 : ℕ) ^ 3 = 8 by norm_num, ← card_L₁ (fr := fr)]
    exact Subgroup.card_dvd_of_le inf_le_left
  obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  have hk0 : k ≠ 0 := fun h => hne (Subgroup.card_eq_one.mp (by rw [hk', h, pow_zero]))
  have heven : Even (Nat.card (fr.L₁ ⊓ centralizer ({s} : Set G) : Subgroup G)) := by
    rw [hk']
    exact Nat.even_pow.mpr ⟨even_two, hk0⟩
  have hzC := z_mem_of_even (inf_le_left.trans L₁_le_F) heven
  have hsM : s ∈ fr.Mbar := by rw [S_eq p7 p10 hz] at hs; exact hs.2
  have h1 : z * s * z⁻¹ = s := by
    rw [mem_centralizer_singleton_iff.mp hzC.2, mul_inv_cancel_right]
  exact hs1 (eq_one_of_conj_eq_self_of_conj_eq_inv (p10.M_pow_three s (Mbar_le_M hsM)) h1
    (inv_of_mem_Mbar p10 hz hsM))

theorem exists_L₁_conj_S [Finite G] (p7 : JankoProp7 fr) (p10 : JankoProp10 fr)
    (hz : orderOf z = 2) {s s' : G} (hs : s ∈ fr.S) (hs1 : s ≠ 1) (hs' : s' ∈ fr.S)
    (hs'1 : s' ≠ 1) : ∃ l ∈ fr.L₁, l * s * l⁻¹ = s' := by
  have hL₁S : fr.L₁ ≤ normalizer (fr.S : Set G) := by
    rw [fr.L₁_eq]; exact zpowers_le.mpr (ℓ_mem_normalizer_S p7 p10 hz)
  refine exists_conj_of_card_le (fun l hl w hw => conj_mem_of_mem_normalizer (hL₁S hl) hw)
    hs hs1 ?_ hs' hs'1
  rw [L₁_inf_centralizer_eq_bot p7 p10 hz hs hs1, Subgroup.card_bot, card_S_eq p7 p10 hz,
    card_L₁]

theorem t_mem_normalizer_S [Finite G] (p7 : JankoProp7 fr) (p10 : JankoProp10 fr)
    (hz : orderOf z = 2) : fr.t ∈ normalizer (fr.S : Set G) := by
  rw [S_eq p7 p10 hz]
  exact inf_mem_normalizer (t_mem_normalizer_ZN p7) (t_mem_normalizer_Mbar p7 p10 hz)

theorem exists_conj_ZN [Finite G] (p7 : JankoProp7 fr) (p10 : JankoProp10 fr)
    (hz : orderOf z = 2) :
    ∀ x ∈ fr.ZN, ∀ y ∈ fr.ZN, x ∉ fr.P₁ → x ∉ fr.S → y ∉ fr.P₁ → y ∉ fr.S →
      ∃ l ∈ fr.L, l * x * l⁻¹ = y := by
  intro x hx y hy hxP hxS hyP hyS
  have hle : fr.P₁ ≤ normalizer (fr.S : Set G) :=
    le_normalizer_of_comm p10.M_comm p10.P₁_le_M (S_le_M p10)
  rw [ZN_eq p7 p10 hz] at hx hy
  obtain ⟨p, hp, s, hs, rfl⟩ := exists_mul_of_mem_sup hle hx
  obtain ⟨q, hq, s', hs', rfl⟩ := exists_mul_of_mem_sup hle hy
  have hp1 : p ≠ 1 := fun h => hxS (by rw [h, one_mul]; exact hs)
  have hs1 : s ≠ 1 := fun h => hxP (by rw [h, mul_one]; exact hp)
  have hq1 : q ≠ 1 := fun h => hyS (by rw [h, one_mul]; exact hs')
  have hs'1 : s' ≠ 1 := fun h => hyP (by rw [h, mul_one]; exact hq)
  have hL₁P : ∀ l ∈ fr.L₁, ∀ p ∈ fr.P₁, l * p * l⁻¹ = p := fun l hl p hp =>
    F_conj_P₁ (L₁_le_F hl) hp
  rcases eq_or_eq_inv_of_mem_P₁ hp hp1 hq hq1 with rfl | rfl
  · obtain ⟨l, hl, hls⟩ := exists_L₁_conj_S p7 p10 hz hs hs1 hs' hs'1
    exact ⟨l, L₁_le_L hl, by rw [conj_mul_conj, hL₁P l hl _ hp, hls]⟩
  · have hts := conj_mem_of_mem_normalizer (t_mem_normalizer_S p7 p10 hz) hs
    obtain ⟨l, hl, hls⟩ := exists_L₁_conj_S p7 p10 hz hts (conj_ne_one hs1) hs' hs'1
    refine ⟨l * fr.t, mul_mem (L₁_le_L hl) t_mem_L, ?_⟩
    have htp : fr.t * p * fr.t⁻¹ = p⁻¹ := conj_eq_inv_of_mem_P₁ fr.t_mul_s₁ hp
    calc l * fr.t * (p * s) * (l * fr.t)⁻¹ =
          l * (fr.t * p * fr.t⁻¹) * l⁻¹ * (l * (fr.t * s * fr.t⁻¹) * l⁻¹) := by group
      _ = p⁻¹ * s' := by rw [htp, hL₁P l hl _ (inv_mem hp), hls]

end CFSG.ProperTwoGeneratedCore.Lemma37.TwoANine.JankoEleven
