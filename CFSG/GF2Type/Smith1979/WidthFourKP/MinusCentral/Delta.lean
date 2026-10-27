module

public import CFSG.GF2Type.Smith1979.WidthFourKP.MinusCentral.Types
public import CFSG.GF2Type.Smith1979.WidthFourKP.MinusCentral.CentLbar
public import CFSG.GF2Type.Smith1979.WidthFourKP.MinusCentral.TwoCubed

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1979.W4MinusC

open CFSG.LargeExtraspecial CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S7
  CFSG.LargeExtraspecial.S8 CFSG.Open Subgroup Module
open CFSG.RankThree.OrthogonalInvolutions

variable {G : Type} [Group G] [Finite G] {S : Setting G} {g : G}

section Norm

variable {X : Type*} [Group X] {A : Subgroup X} {θ : X}
  (hAc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) (hθ : θ ∈ normalizer (A : Set X)) (hθ3 : θ ^ 3 = 1)
include hAc hθ

theorem conj_mem_of_mem_normalizer {a : X} (ha : a ∈ A) :
    θ * a * θ⁻¹ ∈ A ∧ θ⁻¹ * a * θ ∈ A := by
  refine ⟨(mem_normalizer_iff.mp hθ a).mp ha, ?_⟩
  have h := (mem_normalizer_iff.mp (inv_mem hθ) a).mp ha
  rwa [inv_inv] at h

theorem norm_mul {a b : X} (ha : a ∈ A) (hb : b ∈ A) :
    a * b * (θ * (a * b) * θ⁻¹) * (θ⁻¹ * (a * b) * θ) =
      (a * (θ * a * θ⁻¹) * (θ⁻¹ * a * θ)) * (b * (θ * b * θ⁻¹) * (θ⁻¹ * b * θ)) := by
  obtain ⟨ha1, ha2⟩ := conj_mem_of_mem_normalizer hAc hθ ha
  obtain ⟨hb1, hb2⟩ := conj_mem_of_mem_normalizer hAc hθ hb
  have e1 : θ * (a * b) * θ⁻¹ = (θ * a * θ⁻¹) * (θ * b * θ⁻¹) := by group
  have e2 : θ⁻¹ * (a * b) * θ = (θ⁻¹ * a * θ) * (θ⁻¹ * b * θ) := by group
  rw [e1, e2]
  have key : ∀ x ∈ A, ∀ y ∈ A, Commute x y := fun x hx y hy => hAc x hx y hy
  calc a * b * ((θ * a * θ⁻¹) * (θ * b * θ⁻¹)) * ((θ⁻¹ * a * θ) * (θ⁻¹ * b * θ))
      = a * (b * (θ * a * θ⁻¹)) * (θ * b * θ⁻¹) * ((θ⁻¹ * a * θ) * (θ⁻¹ * b * θ)) := by group
    _ = a * ((θ * a * θ⁻¹) * b) * (θ * b * θ⁻¹) * ((θ⁻¹ * a * θ) * (θ⁻¹ * b * θ)) := by
        rw [(key b hb _ ha1).eq]
    _ = a * (θ * a * θ⁻¹) * (b * (θ * b * θ⁻¹) * (θ⁻¹ * a * θ)) * (θ⁻¹ * b * θ) := by group
    _ = a * (θ * a * θ⁻¹) * ((θ⁻¹ * a * θ) * (b * (θ * b * θ⁻¹))) * (θ⁻¹ * b * θ) := by
        rw [(key _ (mul_mem hb hb1) _ ha2).eq]
    _ = (a * (θ * a * θ⁻¹) * (θ⁻¹ * a * θ)) * (b * (θ * b * θ⁻¹) * (θ⁻¹ * b * θ)) := by group

include hθ3 in
theorem commute_norm {a : X} (ha : a ∈ A) :
    θ * (a * (θ * a * θ⁻¹) * (θ⁻¹ * a * θ)) = (a * (θ * a * θ⁻¹) * (θ⁻¹ * a * θ)) * θ := by
  obtain ⟨ha1, ha2⟩ := conj_mem_of_mem_normalizer hAc hθ ha
  have hθ2 : θ * θ = θ⁻¹ := by
    rw [eq_inv_iff_mul_eq_one, ← pow_two, ← pow_succ, hθ3]
  have e1 : θ * (θ * a * θ⁻¹) * θ⁻¹ = θ⁻¹ * a * θ := by
    calc θ * (θ * a * θ⁻¹) * θ⁻¹ = (θ * θ) * a * (θ * θ)⁻¹ := by group
      _ = θ⁻¹ * a * θ := by rw [hθ2, inv_inv]
  have e : θ * (a * (θ * a * θ⁻¹) * (θ⁻¹ * a * θ)) * θ⁻¹ =
      (θ * a * θ⁻¹) * (θ⁻¹ * a * θ) * a := by
    calc θ * (a * (θ * a * θ⁻¹) * (θ⁻¹ * a * θ)) * θ⁻¹
        = (θ * a * θ⁻¹) * (θ * (θ * a * θ⁻¹) * θ⁻¹) * (θ * (θ⁻¹ * a * θ) * θ⁻¹) := by group
      _ = (θ * a * θ⁻¹) * (θ⁻¹ * a * θ) * a := by rw [e1]; group
  have hc : (θ * a * θ⁻¹) * (θ⁻¹ * a * θ) * a = a * (θ * a * θ⁻¹) * (θ⁻¹ * a * θ) := by
    rw [hAc _ (mul_mem ha1 ha2) a ha, ← mul_assoc]
  rw [← mul_inv_eq_iff_eq_mul, e, hc]

end Norm

section Context

variable (hCE : CentralExtInput.{0}) (hw : S.width = 4) (H : Hyp4 S g) (hNo : NoA2 S g)
  (C : Cons311 S g) {t : S.O} (ht : t ∈ S.Lbar g) (ht1 : t ≠ 1) (hVQ : ¬ V S g t ≤ S.Qa g)
  (hΩ : OmegaCase H C ht ht1 hVQ) (h4 : finrank (ZMod 2) (Vt S g t) = 4) (hP : ¬ PlusAt H C)
include hCE hw H hNo C ht ht1 hVQ hΩ h4 hP

theorem exists_theta0 : ∃ θ ∈ ⁅Rbar S g t, Rbar S g t⁆, θ ^ 3 = 1 ∧ θ ∈ NLbar S g ∧
    ∀ l ∈ S.Lbar g, θ * l = l * θ ↔ l = 1 ∨ l = t := by
  obtain ⟨θ, hθR, hθ3, hθa, v, hv⟩ :=
    exists_theta_w4 hCE hw H hNo C ht ht1 hVQ hΩ h4 hP (aV_ne_zero H ht)
  have hθRbar : θ ∈ Rbar S g t := Subgroup.commutator_le_self _ hθR
  have hθM : θ ∈ S.Mbar := Rbar_le_Mbar hθRbar
  have hθt : θ * t = t * θ := commute_of_mem_Rbar H.conj_mem hθRbar
  have e : ((1 : S.M) : G) * g * S.z * (((1 : S.M) : G) * g)⁻¹ = g * S.z * g⁻¹ := by
    simp [mul_assoc]
  have hθN : θ ∈ normalizer (S.Lbar g : Set S.O) := by
    have h0 := mem_normalizer_of_fix H.conj_mem H.conj_ne (h := 1) hθM (by rw [e]; exact hθa)
    have e2 : ((1 : S.M) : G) * g = g := by simp
    rwa [e2] at h0
  have hL8 : Nat.card (S.Lbar g) = 8 := by rw [C.card_Lbar, hw]; norm_num
  have hθA : ¬ ∀ a ∈ S.Lbar g, θ * a = a * θ := by
    intro hc
    have hθL := mem_Lbar_of_centralizes_w4 hCE hw H hNo C ht ht1 hVQ hΩ h4 hP hθM hc
    have h2 : θ * θ = 1 := mul_self_of_mem_Lbar S H.conj_mem hθL
    have h1 : θ = 1 := by
      calc θ = θ ^ 3 * (θ * θ)⁻¹ := by group
        _ = 1 := by rw [hθ3, h2]; group
    apply hv
    rw [h1]
    rfl
  have h2 := card_inf_centralizer_eq_two (S.Lbar g) hL8 hθN hθ3 hθA
  have htt : t * t = 1 := mul_self_of_mem_Lbar S H.conj_mem ht
  have hle : zpowers t ≤ S.Lbar g ⊓ centralizer ({θ} : Set S.O) :=
    zpowers_le.mpr (Subgroup.mem_inf.mpr ⟨ht, mem_centralizer_singleton_iff.mpr hθt.symm⟩)
  have heq : zpowers t = S.Lbar g ⊓ centralizer ({θ} : Set S.O) :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [h2, S7.card_zpowers_eq_two H ht ht1])
  refine ⟨θ, hθR, hθ3, ⟨hθM, hθN⟩, fun l hl => ?_⟩
  constructor
  · intro hc
    have hmem : l ∈ S.Lbar g ⊓ centralizer ({θ} : Set S.O) :=
      Subgroup.mem_inf.mpr ⟨hl, mem_centralizer_singleton_iff.mpr hc.symm⟩
    rw [← heq] at hmem
    exact S8.eq_one_or_eq_of_mem_zpowers htt hmem
  · rintro (rfl | rfl)
    · group
    · exact hθt

theorem delta_dichotomy :
    (∀ n ∈ NLbar S g, n * t * n⁻¹ = t) ∨
    ((Delta S g t).ncard = 4 ∧ ∃ θ ∈ ⁅Rbar S g t, Rbar S g t⁆, θ ^ 3 = 1 ∧ θ ∈ NLbar S g ∧
      (∀ l ∈ S.Lbar g, θ * l = l * θ ↔ l = 1 ∨ l = t) ∧
      (∀ l₁ ∈ S.Lbar g, ∀ l₂ ∈ S.Lbar g, (l₁ * l₂ ∈ Delta S g t ↔
        ¬ (l₁ ∈ Delta S g t ↔ l₂ ∈ Delta S g t))) ∧
      ∀ l ∈ S.Lbar g, l ∉ Delta S g t → ∃ a ∈ S.Lbar g, l = a⁻¹ * (θ * a * θ⁻¹)) := by
  obtain ⟨θ, hθR, hθ3, hθN, hθC⟩ := exists_theta0 hCE hw H hNo C ht ht1 hVQ hΩ h4 hP
  have hL8 : Nat.card (S.Lbar g) = 8 := by rw [C.card_Lbar, hw]; norm_num
  have hA2 : ∀ a ∈ S.Lbar g, a * a = 1 := fun a ha => mul_self_of_mem_Lbar S H.conj_mem ha
  have hAc : ∀ a ∈ S.Lbar g, ∀ b ∈ S.Lbar g, a * b = b * a := fun a ha b hb =>
    Lbar_comm S H.conj_mem ha hb
  have h1Δ : (1 : S.O) ∉ Delta S g t := by
    rintro ⟨n, -, hn⟩
    apply ht1
    calc t = n⁻¹ * (n * t * n⁻¹) * n := by group
      _ = 1 := by rw [← hn]; group
  rcases eq_or_ncard_four_of_cap (S.Lbar g) hL8 hA2 hAc hθN.2 hθ3 hθC
      (fun x hx => Case25.delta_subset_Lbar ht hx) (mem_Delta_self S g t) h1Δ
      (fun d hd => Case25.conj_mem_Delta hθN hd)
      (fun d hd d' hd' hne => mul_not_mem_Delta hCE hw H hNo C ht ht1 hVQ hΩ h4 hP hd hd' hne)
    with hΔ | ⟨hΔ4, hΔν⟩
  · left
    intro n hn
    have : n * t * n⁻¹ ∈ Delta S g t := ⟨n, hn, rfl⟩
    rw [hΔ] at this
    exact this
  · right
    have htt : t * t = 1 := mul_self_of_mem_Lbar S H.conj_mem ht
    have hν : ∀ l ∈ S.Lbar g, l * (θ * l * θ⁻¹) * (θ⁻¹ * l * θ) = 1 ∨
        l * (θ * l * θ⁻¹) * (θ⁻¹ * l * θ) = t := by
      intro l hl
      obtain ⟨hl1, hl2⟩ := conj_mem_of_mem_normalizer hAc hθN.2 hl
      exact (hθC _ (mul_mem (mul_mem hl hl1) hl2)).mp (commute_norm hAc hθN.2 hθ3 hl)
    refine ⟨hΔ4, θ, hθR, hθ3, hθN, hθC, fun l₁ hl₁ l₂ hl₂ => ?_, fun l hl hlΔ => ?_⟩
    · rw [hΔν _ (mul_mem hl₁ hl₂), hΔν _ hl₁, hΔν _ hl₂, norm_mul hAc hθN.2 hl₁ hl₂]
      rcases hν l₁ hl₁ with h1 | h1 <;> rcases hν l₂ hl₂ with h2 | h2 <;>
        simp [h1, h2, htt, ht1, Ne.symm ht1]
    · have hn1 : l * (θ * l * θ⁻¹) * (θ⁻¹ * l * θ) = 1 :=
        (hν l hl).resolve_right fun h => hlΔ ((hΔν l hl).mpr h)
      exact exists_eq_comm_of_norm_eq_one (S.Lbar g) hL8 hA2 hAc hθN.2 hθ3 hθC hl hn1

end Context

end CFSG.GF2Type.Smith1979.W4MinusC
