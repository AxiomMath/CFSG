module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34TwDefs
import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4Single
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrCriticalGrowth
import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5Lemma53

public section

namespace CFSG.ComponentClassification.GrSLit.L34Tw

open CFSG Subgroup CFSG.ComponentClassification.PSL3Four
  CFSG.ComponentClassification.UnbalancedLayer

variable {G : Type} [Group G] [Finite G] {a x : G} {J S' W K T : Subgroup G} {t : G}

theorem zStarIn_eq_oddIn_J (h : TwHyp G a x J S' W K T t) : zStarIn J = oddIn J := by
  obtain ⟨-, -, -, -, hSsyl, -, -⟩ := h.hset
  have hZ1 := h.hZ1
  have hchar : (Open.fusionZStar ↥J).Characteristic := inferInstance
  refine le_antisymm ?_ (GrS4.oddIn_le_zStarIn J)
  have hodd : Odd (Nat.card ↥(zStarIn J)) := by
    by_contra hodd
    have h2 : 2 ∣ Nat.card ↥(zStarIn J) := even_iff_two_dvd.mp (Nat.not_odd_iff_even.mp hodd)
    obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := ↥(zStarIn J)) 2 h2
    have hy2 : orderOf (y : G) = 2 := by rw [Subgroup.orderOf_coe, hy]
    have hyJ : (y : G) ∈ J := (map_subtype_le _ : zStarIn J ≤ J) y.2
    obtain ⟨c, hcN, hcS⟩ := hSsyl.exists_conj_le (zpowers_le.mpr (le_normalizer hyJ))
      (IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hy2, pow_one]))
    have hcy : c * (y : G) * c⁻¹ ∈ zStarIn J :=
      (mem_normalizer_iff.mp (UnbalancedGS.normalizer_le_normalizer_map_of_characteristic J
        (Open.fusionZStar ↥J) hcN) _).mp y.2
    have h1 : c * (y : G) * c⁻¹ ∈ S' ⊓ zStarIn J := mem_inf.mpr ⟨hcS _ (mem_zpowers _), hcy⟩
    rw [hZ1, mem_bot, mul_inv_eq_one, mul_eq_left] at h1
    rw [h1, orderOf_one] at hy2
    exact absurd hy2 (by norm_num)
  refine GrSLit.le_map_pPrimeCore (map_subtype_le _) (fun k hk z hz => ?_) hodd
  exact (mem_normalizer_iff.mp (UnbalancedGS.normalizer_le_normalizer_map_of_characteristic J
    (Open.fusionZStar ↥J) (le_normalizer hk)) z).mp hz

theorem perfect_J (h : TwHyp G a x J S' W K T t) : ⁅J, J⁆ = J := by
  obtain ⟨-, hU3, -, -, -, -, -⟩ := h.hset
  exact UnbalancedCorr.commutator_eq_of_isPComponent hU3.2.2.2.1 hU3.2.2.2.2.1

variable {ρ : ↥(normalizer (W : Set G)) →* WrE}

theorem isA_a (h : TwHyp G a x J S' W K T t) (hρ : TwModel (normalizer (W : Set G)) K t ρ) :
    ∃ ha : a ∈ normalizer (W : Set G), IsA (ρ ⟨a, ha⟩) := by
  obtain ⟨-, hU3, -, -, -, haS, -⟩ := h.hset
  have ha2 : orderOf a = 2 := hU3.1
  have haM : a ∈ normalizer (W : Set G) := h.hTsyl.1 (h.hST haS)
  refine ⟨haM, ?_⟩
  obtain ⟨he, ha1, hbS⟩ := hρ.Kt_img ⟨a, haM⟩ h.haKt
  have haa : a * a = 1 := by rw [← pow_two, ← ha2, pow_orderOf_eq_one]
  have hsq : ρ ⟨a, haM⟩ * ρ ⟨a, haM⟩ = 1 := by
    rw [← map_mul, show (⟨a, haM⟩ : ↥(normalizer (W : Set G))) * ⟨a, haM⟩ = 1 from
      Subtype.ext haa, map_one]
  have hb1 : (ρ ⟨a, haM⟩).b ≠ 1 := by
    intro hb
    have h1 : ρ ⟨a, haM⟩ = 1 := WrE.ext ha1 hb he
    have h2 := GrSLit.odd_orderOf_of_mem_map_pPrimeCore ((hρ.ker_iff ⟨a, haM⟩).mp h1)
    rw [ha2] at h2
    exact absurd h2 (by decide)
  exact ⟨he, hsq, Or.inl ⟨ha1, hb1, hbS⟩⟩

theorem isA_of_mem_J (h : TwHyp G a x J S' W K T t) (hρ : TwModel (normalizer (W : Set G)) K t ρ)
    {j : ↥(normalizer (W : Set G))} (hj : (j : G) ∈ J) (hj2 : j * j = 1) (hj1 : j ≠ 1) :
    IsA (ρ j) := by
  have hjs : (j : G) ∈ K ⊔ oddIn (normalizer (W : Set G)) := h.hsup ▸ mem_sup_left hj
  have hKo : K ≤ normalizer ((oddIn (normalizer (W : Set G)) : Subgroup G) : Set G) :=
    h.hKM.trans (GrS4.self_le_normalizer_oddIn _)
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right K _ hKo] at hjs
  obtain ⟨k, hk, o, ho, hko⟩ := hjs
  have hkM : k ∈ normalizer (W : Set G) := h.hKM hk
  have hoM : o ∈ normalizer (W : Set G) :=
    (map_subtype_le _ : oddIn (normalizer (W : Set G)) ≤ normalizer (W : Set G)) ho
  have hjko : j = ⟨k, hkM⟩ * ⟨o, hoM⟩ := Subtype.ext hko.symm
  have hρo : ρ ⟨o, hoM⟩ = 1 := (hρ.ker_iff ⟨o, hoM⟩).mpr ho
  have hρj : ρ j = ρ ⟨k, hkM⟩ := by rw [hjko, map_mul, hρo, mul_one]
  obtain ⟨he, hb, haS⟩ := hρ.K_img ⟨k, hkM⟩ hk
  rw [← hρj] at he hb haS
  have hsq : ρ j * ρ j = 1 := by rw [← map_mul, hj2, map_one]
  have ha1 : (ρ j).a ≠ 1 := by
    intro ha
    have h1 : ρ j = 1 := WrE.ext ha hb he
    have h2 := GrSLit.odd_orderOf_of_mem_map_pPrimeCore ((hρ.ker_iff j).mp h1)
    have h3 : orderOf j = 2 := orderOf_eq_prime (by rwa [pow_two]) hj1
    rw [Subgroup.orderOf_coe, h3] at h2
    exact absurd h2 (by decide)
  exact ⟨he, hsq, Or.inr ⟨hb, ha1, haS⟩⟩

end CFSG.ComponentClassification.GrSLit.L34Tw
