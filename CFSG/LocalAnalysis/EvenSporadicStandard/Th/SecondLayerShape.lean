module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Th.SecondLayerA
public import CFSG.LocalAnalysis.EvenSporadicStandard.Th.SylowEndIdx

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.ThStd

open Subgroup SylowEnd

variable {G : Type} [Group G] [Finite G] {L R : Subgroup G} {t : G} {S A B Aa D : Subgroup G}
  {z b : G}

section

variable (H : ThCyc G L R t) (W : ThLocalIn L S A B z) (W2 : ThLocalIn2 B A Aa b)
  (hD : DHyp A Aa t D)

include H W W2 hD

theorem ThCyc.conj_t_data {y : G}
    (hyN : y ∈ normalizer ((S ⊔ Bp A t : Subgroup G) : Set G)) :
    y * t * y⁻¹ ∈ S ⊔ Bp A t ∧
      Nat.card ↥((S ⊔ Bp A t) ⊓ centralizer ({y * t * y⁻¹} : Set G)) = 2 * Nat.card S := by
  have htT : t ∈ S ⊔ Bp A t := mem_sup_right (H.t_mem_Bp W W2)
  refine ⟨(mem_normalizer_iff.1 hyN t).1 htT, ?_⟩
  rw [← map_conj_inf_centralizer hyN t,
    Subgroup.card_map_of_injective (MulAut.conj y).injective,
    H.sup_Bp_inf_centralizer_t W W2, H.card_sup_zpowers W]

theorem ThCyc.conj_t_type
    (hAb : ∀ g : G, ∀ Y : Subgroup G, Y ≤ L.map (MulAut.conj g).toMonoidHom → IsPGroup 2 Y →
      (∀ x ∈ Y, ∀ y ∈ Y, x * y = y * x) → Nat.card Y ≤ 2 ^ 8)
    (hEl : ∀ g : G, ∀ Y : Subgroup G, Y ≤ L.map (MulAut.conj g).toMonoidHom →
      (∀ x ∈ Y, ∀ y ∈ Y, x * y = y * x) → (∀ y ∈ Y, y ^ 2 = 1) → Nat.card Y ≤ 2 ^ 7)
    (hZ : ∀ s ∈ S, (∀ x ∈ S, s * x * s⁻¹ * x⁻¹ ∈ Aa) → s ∈ B) {y : G}
    (hyN : y ∈ normalizer ((S ⊔ Bp A t : Subgroup G) : Set G)) :
    (∃ d₁ ∈ D, y * t * y⁻¹ = d₁ * t ∧ d₁ ^ 2 = theta t d₁ ∧
        ∀ s ∈ S, d₁ * s * d₁⁻¹ * s⁻¹ ∈ A) ∨
      (∃ d₁ ∈ Aa, y * t * y⁻¹ = d₁ * (b * t) ∧
        ∀ s ∈ S, (d₁ * b) * s * (d₁ * b)⁻¹ * s⁻¹ ∈ A) := by
  obtain ⟨huT, hR⟩ := H.conj_t_data W W2 hD hyN
  have h := H.extremal_type W W2 hD hAb hEl hZ (g := y⁻¹) (by rw [inv_inv]; exact hR.ge)
    (by rw [inv_inv]; exact huT)
  simpa only [inv_inv] using h

theorem ThCyc.conj_t_card_D
    (hAb : ∀ g : G, ∀ Y : Subgroup G, Y ≤ L.map (MulAut.conj g).toMonoidHom → IsPGroup 2 Y →
      (∀ x ∈ Y, ∀ y ∈ Y, x * y = y * x) → Nat.card Y ≤ 2 ^ 8)
    (hZ : ∀ s ∈ S, (∀ x ∈ S, s * x * s⁻¹ * x⁻¹ ∈ Aa) → s ∈ B) {y : G}
    (hyN : y ∈ normalizer ((S ⊔ Bp A t : Subgroup G) : Set G)) :
    Nat.card ↥(D ⊓ centralizer ({y * t * y⁻¹} : Set G)) = 2 ^ 8 := by
  have htT : t ∈ S ⊔ Bp A t := mem_sup_right (H.t_mem_Bp W W2)
  obtain ⟨huT, hR⟩ := H.conj_t_data W W2 hD hyN
  have h := (H.ext_extremal_of_card W W2 hD hAb hZ (H.isPGroup_S_sup_Bp W)
    (sup_le le_sup_left (zpowers_le.2 htT)) le_sup_right (H.S_sup_Bp_le_normalizer W)
    (g := y⁻¹) (by rw [inv_inv]; exact hR.ge) (by rw [inv_inv]; exact huT)).2.1
  simpa only [inv_inv] using h

theorem ThCyc.mem_Bp_of_shape_a
    (hAb : ∀ g : G, ∀ Y : Subgroup G, Y ≤ L.map (MulAut.conj g).toMonoidHom → IsPGroup 2 Y →
      (∀ x ∈ Y, ∀ y ∈ Y, x * y = y * x) → Nat.card Y ≤ 2 ^ 8)
    (hEl : ∀ g : G, ∀ Y : Subgroup G, Y ≤ L.map (MulAut.conj g).toMonoidHom →
      (∀ x ∈ Y, ∀ y ∈ Y, x * y = y * x) → (∀ y ∈ Y, y ^ 2 = 1) → Nat.card Y ≤ 2 ^ 7)
    (hZ : ∀ s ∈ S, (∀ x ∈ S, s * x * s⁻¹ * x⁻¹ ∈ Aa) → s ∈ B)
    (h4 : ∀ d ∈ D, d ^ 4 = theta t d) {y : G}
    (hyN : y ∈ normalizer ((S ⊔ Bp A t : Subgroup G) : Set G))
    (hyA : ∀ a ∈ A, y * a * y⁻¹ = a) : y ∈ Bp A t := by
  have hAL : A ≤ L := le_trans (fun x hx => ((W.mem_A_iff x).1 hx).1) W.S_le
  rcases H.conj_t_type W W2 hD hAb hEl hZ hyN with ⟨d₁, hd₁, hu, hsq, -⟩ | ⟨d₁, hd₁, hu, -⟩
  · have hθA : theta t d₁ ∈ A := H.theta_mem_A W (H.D_le_Bp W W2 hD hd₁)
    have hθ1 : theta t d₁ = 1 := by
      rw [← h4 d₁ hd₁]
      calc d₁ ^ 4 = (d₁ ^ 2) ^ 2 := by rw [← pow_mul]
        _ = 1 := by rw [hsq]; exact W.A_sq _ hθA
    have hd₁Aa : d₁ ∈ Aa := (H.D_theta_eq_one_iff W W2 hD hd₁).1 hθ1
    have hd₁A : d₁ ∈ A := W2.mem_A_of_sq_eq_one W hd₁Aa (by rw [hsq, hθ1])
    obtain ⟨-, g, -, -, hgn, -, hgt⟩ := H.exists_fusing_z W
    obtain ⟨r, hrN, hrt, hrA⟩ := H.exists_translation W hgt (H.normalizes_S W hgn hgt) hd₁A
    have hrBp : r ∈ Bp A t := ⟨mem_centralizer_iff.2 fun x hx => by
      have := hrA x hx
      calc x * r = (r * x * r⁻¹) * r := by rw [this]
        _ = r * x := by group, hrN⟩
    have hq : r⁻¹ * y ∈ centralizer ((W5 A t : Subgroup G) : Set G) := by
      have hqA : ∀ a ∈ A, (r⁻¹ * y) * a = a * (r⁻¹ * y) := fun a ha => by
        have h1 := hrA a ha
        have h2 := hyA a ha
        calc (r⁻¹ * y) * a = r⁻¹ * (y * a * y⁻¹) * y := by group
          _ = r⁻¹ * a * y := by rw [h2]
          _ = r⁻¹ * (r * a * r⁻¹) * y := by rw [h1]
          _ = a * (r⁻¹ * y) := by group
      have hqt : (r⁻¹ * y) * t = t * (r⁻¹ * y) := by
        have h1 : r⁻¹ * (d₁ * t) * r = t := by
          rw [← hrt]; group
        calc (r⁻¹ * y) * t = r⁻¹ * (y * t * y⁻¹) * y := by group
          _ = r⁻¹ * (d₁ * t) * y := by rw [hu]
          _ = (r⁻¹ * (d₁ * t) * r) * (r⁻¹ * y) := by group
          _ = t * (r⁻¹ * y) := by rw [h1]
      refine mem_centralizer_iff.2 fun w hw => ?_
      rcases (H.mem_W5_iff hAL).1 hw with h | ⟨a, ha, rfl⟩
      · exact (hqA w h).symm
      · calc a * t * (r⁻¹ * y) = a * (t * (r⁻¹ * y)) := by group
          _ = a * ((r⁻¹ * y) * t) := by rw [hqt]
          _ = (a * (r⁻¹ * y)) * t := by group
          _ = ((r⁻¹ * y) * a) * t := by rw [hqA a ha]
          _ = (r⁻¹ * y) * (a * t) := by group
    have := (Bp A t).mul_mem hrBp (centralizer_W5_le_Bp A t hq)
    simpa using this
  · exfalso
    have hd₁D : d₁ ∈ D := hD.Aa_le hd₁
    have hcard := H.conj_t_card_D W W2 hD hAb hZ hyN
    rw [hu, inf_centralizer_mul_eq hD.comm hd₁D, H.inf_centralizer_bt_eq_A W W2 hD h4,
      W.A_card] at hcard
    norm_num at hcard

end

@[expose] def ThSecondLayerB : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L R : Subgroup G) (t : G) (S A B Aa D : Subgroup G)
    (z b : G), ThCyc G L R t → ThLocalIn L S A B z → ThLocalIn2 B A Aa b → SylowFacts L S B Aa →
    DHyp A Aa t D → (∀ d ∈ D, d ^ 4 = 1) → (∀ d ∈ D, b * d * b⁻¹ = d⁻¹) →
    ∀ P : Subgroup G, IsPGroup 2 P → S ⊔ Bp A t ≤ P →
      ∀ c ∈ P, (∀ a ∈ A, c * a * c⁻¹ = a) →
        c ∈ normalizer ((S ⊔ Bp A t : Subgroup G) : Set G) → c ∉ S ⊔ Bp A t → False

theorem thSecondLayerA_of_B (h : ThSecondLayerB) : ThSecondLayerA := by
  intro G _ _ L R t S A B Aa z b H W W2 F P hP hSP c hcP hcA hcN hcT
  obtain ⟨D, hDC, hDab, hAaD, hDsup, hDdisj, hDcard, hDnorm, hBpC⟩ := H.exists_D W W2
  have hD : SylowEnd.DHyp A Aa t D := ⟨hDC, hDab, hAaD, hDsup, hDdisj, hDcard, hDnorm, hBpC⟩
  rcases H.D_cases W W2 hD F.elementary_le with ⟨h4, -, -⟩ | ⟨h4, hb, -, -⟩
  · refine hcT (mem_sup_right ?_)
    refine H.mem_Bp_of_shape_a W W2 hD F.abelian_le F.elementary_le F.center_quotient h4 hcN
      (fun a ha => hcA a ha)
  · exact h G L R t S A B Aa D z b H W W2 F hD h4 hb P hP hSP c hcP hcA hcN hcT

end CFSG.EvenSporadicStandard.ThStd
