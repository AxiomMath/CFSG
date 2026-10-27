module

public import CFSG.GroupTheory.SylowIntersectionControl.GomiFact36ChiefInputs
import CFSG.GroupTheory.SylowIntersectionControl.GomiFact36Ident
import CFSG.GroupTheory.SylowIntersectionControl.GomiFact36HomogSL3
import CFSG.Quasithin.Background.B5Models
import CFSG.Quasithin.Background.GoldschmidtB69DeepSec
public import CFSG.Quasithin.Background.B1Restrict

public section

namespace CFSG.GroupTheory

open CFSG.Quasithin

private theorem gomi_section_card_data {W : Type} [CommGroup W] [Finite W]
    (A : Subgroup (MulAut W)) (I Z : Subgroup W) :
    0 < Nat.card (Sec I Z) ∧ 0 < Nat.card ↥(fixV (autSec A I Z)) ∧
      Nat.card ↥(fixV (autSec A I Z)) ≤ Nat.card (Sec I Z) := by
  refine ⟨Nat.card_pos, ?_, ?_⟩
  · exact Nat.card_pos_iff.2 ⟨⟨1, Subgroup.one_mem _⟩, inferInstance⟩
  · exact (fixV (autSec A I Z)).card_le_card_group

private theorem isElemAbelian2_autSec_of_inf_centSec_eq {W : Type} [CommGroup W]
    {A : Subgroup (MulAut W)} {I Z I' Z' : Subgroup W}
    (hAI : A ≤ stabSub I) (hAZ : A ≤ stabSub Z)
    (hAI' : A ≤ stabSub I') (hAZ' : A ≤ stabSub Z')
    (hker : A ⊓ centSec I Z = A ⊓ centSec I' Z')
    (hAel : IsElemAbelian2 (autSec A I Z)) :
    IsElemAbelian2 (autSec A I' Z') := by
  have hcent : ∀ a : ↥A, (a : MulAut W) ∈ centSec I Z ↔ (a : MulAut W) ∈ centSec I' Z' := by
    intro a
    constructor
    · intro ha
      have h : (a : MulAut W) ∈ A ⊓ centSec I Z := ⟨a.2, ha⟩
      rw [hker] at h
      exact h.2
    · intro ha
      have h : (a : MulAut W) ∈ A ⊓ centSec I' Z' := ⟨a.2, ha⟩
      rw [← hker] at h
      exact h.2
  rw [← B5.range_secHom A hAI' hAZ']
  constructor
  · rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
    have ha : B5.secHom A hAI hAZ a ∈ autSec A I Z := by
      rw [← B5.range_secHom A hAI hAZ]
      exact ⟨a, rfl⟩
    have hb : B5.secHom A hAI hAZ b ∈ autSec A I Z := by
      rw [← B5.range_secHom A hAI hAZ]
      exact ⟨b, rfl⟩
    have hcomm := hAel.1 _ ha _ hb
    have hc : ((a * b * (b * a)⁻¹ : ↥A) : MulAut W) ∈ centSec I Z := by
      rw [← B5.mem_ker_secHom A hAI hAZ]
      rw [MonoidHom.mem_ker, map_mul, map_mul, map_inv, map_mul, hcomm, mul_inv_cancel]
    have hc' : ((a * b * (b * a)⁻¹ : ↥A) : MulAut W) ∈ centSec I' Z' := (hcent _).1 hc
    have hk := (B5.mem_ker_secHom A hAI' hAZ' (a * b * (b * a)⁻¹)).2 hc'
    rw [MonoidHom.mem_ker, map_mul, map_mul, map_inv, map_mul] at hk
    exact mul_inv_eq_one.mp hk
  · rintro _ ⟨a, rfl⟩
    have ha : B5.secHom A hAI hAZ a ∈ autSec A I Z := by
      rw [← B5.range_secHom A hAI hAZ]
      exact ⟨a, rfl⟩
    have hsq := hAel.2 _ ha
    have hc : ((a ^ 2 : ↥A) : MulAut W) ∈ centSec I Z := by
      rw [← B5.mem_ker_secHom A hAI hAZ]
      rw [MonoidHom.mem_ker, map_pow]
      exact hsq
    have hc' : ((a ^ 2 : ↥A) : MulAut W) ∈ centSec I' Z' := (hcent _).1 hc
    have hk := (B5.mem_ker_secHom A hAI' hAZ' (a ^ 2)).2 hc'
    rw [MonoidHom.mem_ker, map_pow] at hk
    exact hk

private theorem not_le_centSec_of_inf_centSec_eq {W : Type} [CommGroup W]
    {A : Subgroup (MulAut W)} {I Z I' Z' : Subgroup W}
    (hker : A ⊓ centSec I Z = A ⊓ centSec I' Z')
    (h : ¬ A ≤ centSec I Z) : ¬ A ≤ centSec I' Z' := by
  intro hle
  apply h
  have hA : A ⊓ centSec I Z = A := by rw [hker, inf_eq_left.mpr hle]
  exact inf_eq_left.mp hA

private theorem card_autSec_eq_of_inf_centSec_eq {W : Type} [CommGroup W] [Finite W]
    {A : Subgroup (MulAut W)} {I Z I' Z' : Subgroup W}
    (hAI : A ≤ stabSub I) (hAZ : A ≤ stabSub Z)
    (hAI' : A ≤ stabSub I') (hAZ' : A ≤ stabSub Z')
    (hker : A ⊓ centSec I Z = A ⊓ centSec I' Z') :
    Nat.card ↥(autSec A I' Z') = Nat.card ↥(autSec A I Z) := by
  have h1 := card_autSec_mul (A := A) (W := I') (U := Z') hAI' hAZ'
  have h2 := card_autSec_mul (A := A) (W := I) (U := Z) hAI hAZ
  rw [hker] at h2
  have hk : 0 < Nat.card ↥(A ⊓ centSec I' Z') :=
    Nat.card_pos_iff.2 ⟨⟨1, (A ⊓ centSec I' Z').one_mem⟩, inferInstance⟩
  exact Nat.mul_right_cancel hk (h1.trans h2.symm)

private theorem false_of_gomi_cost_bounds {e f f' v v' : ℕ} (he : 2 ≤ e)
    (hf : 0 < f) (hf' : 0 < f') (hcost : v * v' ≤ e * f * f')
    (h1 : e ^ 2 * f ^ 3 ≤ v ^ 3) (h2 : e * f' ^ 2 ≤ v' ^ 2) : False := by
  have h1' : e ^ 4 * f ^ 6 ≤ v ^ 6 := by
    calc e ^ 4 * f ^ 6 = (e ^ 2 * f ^ 3) ^ 2 := by ring
      _ ≤ (v ^ 3) ^ 2 := Nat.pow_le_pow_left h1 2
      _ = v ^ 6 := by ring
  have h2' : e ^ 3 * f' ^ 6 ≤ v' ^ 6 := by
    calc e ^ 3 * f' ^ 6 = (e * f' ^ 2) ^ 3 := by ring
      _ ≤ (v' ^ 2) ^ 3 := Nat.pow_le_pow_left h2 3
      _ = v' ^ 6 := by ring
  have h3 : (v * v') ^ 6 ≤ (e * f * f') ^ 6 := Nat.pow_le_pow_left hcost 6
  have h4 : e ^ 7 * f ^ 6 * f' ^ 6 ≤ e ^ 6 * f ^ 6 * f' ^ 6 := by
    calc e ^ 7 * f ^ 6 * f' ^ 6 = (e ^ 4 * f ^ 6) * (e ^ 3 * f' ^ 6) := by ring
      _ ≤ v ^ 6 * v' ^ 6 := Nat.mul_le_mul h1' h2'
      _ = (v * v') ^ 6 := by ring
      _ ≤ (e * f * f') ^ 6 := h3
      _ = e ^ 6 * f ^ 6 * f' ^ 6 := by ring
  have hK : 0 < f ^ 6 * f' ^ 6 := Nat.mul_pos (pow_pos hf 6) (pow_pos hf' 6)
  have hcancel : e ^ 7 ≤ e ^ 6 := by
    refine Nat.le_of_mul_le_mul_right ?_ hK
    calc e ^ 7 * (f ^ 6 * f' ^ 6) = e ^ 7 * f ^ 6 * f' ^ 6 := by ring
      _ ≤ e ^ 6 * f ^ 6 * f' ^ 6 := h4
      _ = e ^ 6 * (f ^ 6 * f' ^ 6) := by ring
  have hepos : 0 < e ^ 6 := pow_pos (by omega) 6
  have hle : e ≤ 1 := by
    refine Nat.le_of_mul_le_mul_left ?_ hepos
    calc e ^ 6 * e = e ^ 7 := by ring
      _ ≤ e ^ 6 := hcancel
      _ = e ^ 6 * 1 := by ring
  omega

private theorem gomi_bound_sec {W : Type} [CommGroup W] [Finite W]
    (hW : ∀ w : W, w ^ 2 = 1) {L A : Subgroup (MulAut W)} {I Z : Subgroup W}
    (hChev : IsGomiChevTwo ↥L) (hAL : A ≤ Subgroup.normalizer (L : Set (MulAut W)))
    (hAI : A ≤ stabSub I) (hAZ : A ≤ stabSub Z)
    (hNF : IsGomiNoncentralFactor L I Z) (hnat : IsGomiNatural L I Z)
    (hAnc : ¬ A ≤ centSec I Z) (hAel : IsElemAbelian2 (autSec A I Z))
    {v₂ f₂ : ℕ}
    (hcost : Nat.card (Sec I Z) * v₂ ≤
      Nat.card ↥(autSec A I Z) * Nat.card ↥(fixV (autSec A I Z)) * f₂)
    (hf₂ : f₂ ≤ v₂) (hv₂ : 0 < v₂) :
    Nat.card (Sec I Z) ≤ Nat.card ↥(autSec A I Z) * Nat.card ↥(fixV (autSec A I Z)) ∧
      Nat.card ↥(autSec A I Z) * Nat.card ↥(fixV (autSec A I Z)) ^ 2 ≤ Nat.card (Sec I Z) ^ 2 ∧
        ((∃ a : ℕ, 1 ≤ a ∧ BinaryNaturalSL (autSec L I Z) ⊤ ⊥ 3 a) ∨
          Nat.card ↥(autSec A I Z) ^ 2 * Nat.card ↥(fixV (autSec A I Z)) ^ 3 ≤
            Nat.card (Sec I Z) ^ 3) := by
  have hff : Nat.card (Sec I Z) ≤
      Nat.card ↥(autSec A I Z) * Nat.card ↥(fixV (autSec A I Z)) := by
    refine Nat.le_of_mul_le_mul_right ?_ hv₂
    calc Nat.card (Sec I Z) * v₂
        ≤ Nat.card ↥(autSec A I Z) * Nat.card ↥(fixV (autSec A I Z)) * f₂ := hcost
      _ ≤ Nat.card ↥(autSec A I Z) * Nat.card ↥(fixV (autSec A I Z)) * v₂ :=
          Nat.mul_le_mul_left _ hf₂
  have hLI : L ≤ stabSub I := B1.le_stabSub_of_invariant fun l hl w hw => hNF.1 ⟨l, hl⟩ w hw
  have hLZ : L ≤ stabSub Z := B1.le_stabSub_of_invariant fun l hl w hw => hNF.2.1 ⟨l, hl⟩ w hw
  have hfaith : L ⊓ centSec I Z = ⊥ := IsGomiNatural.inf_centSec_eq_bot hnat
  have hQS : CFSG.IsQuasisimple ↥(autSec L I Z) :=
    B5.isQuasisimple_autSec hLI hLZ hfaith hChev.1
  have hIrr : XMod.IsIrrSec ↥(autSec L I Z) (⊥ : Subgroup (Sec I Z)) ⊤ := by
    refine B5.isIrrSec_autSec hNF.2.2.1.1 ?_ hLI hLZ
    intro J hJ hZJ hJI
    exact hNF.2.2.1.2 J (fun a x hx => hJ a a.2 x hx) hZJ hJI
  have hB4 : B4HypCore (autSec L I Z ⊔ autSec A I Z) (autSec L I Z) :=
    b4HypCore_autSec hW hLI hLZ hAI hAZ hAL hAel hQS hIrr
  have hnat' : IsGomiNatural (autSec L I Z) ⊤ ⊥ := IsGomiNatural.autSec hnat
  have hEN : autSec A I Z ≤ Subgroup.normalizer (autSec L I Z : Set (MulAut (Sec I Z))) :=
    autSec_le_normalizer hAL hLI hLZ hAI hAZ
  have hE1 : autSec A I Z ≠ ⊥ := B69.autSec_ne_bot hAI hAZ hAnc
  exact ⟨hff, gomiHomog_bound (V := Sec I Z) (sq_eq_one_sec hW I Z) hB4 hnat' hEN hAel hE1 hff⟩

private theorem secIsoL_of_both_binaryNaturalSL {W : Type} [CommGroup W] [Finite W]
    {L A : Subgroup (MulAut W)} {I Z I' Z' : Subgroup W} {a a' : ℕ}
    (hAL : A ≤ Subgroup.normalizer (L : Set (MulAut W)))
    (hAI : A ≤ stabSub I) (hAZ : A ≤ stabSub Z)
    (hAI' : A ≤ stabSub I') (hAZ' : A ≤ stabSub Z')
    (hNF : IsGomiNoncentralFactor L I Z) (hNF' : IsGomiNoncentralFactor L I' Z')
    (hnat : IsGomiNatural L I Z) (hnat' : IsGomiNatural L I' Z')
    (hAnc : ¬ A ≤ centSec I Z) (hker : A ⊓ centSec I Z = A ⊓ centSec I' Z')
    (hAel : IsElemAbelian2 (autSec A I Z)) (hAel' : IsElemAbelian2 (autSec A I' Z'))
    (hcost : Nat.card (Sec I Z) * Nat.card (Sec I' Z') ≤
      Nat.card ↥(autSec A I Z) * Nat.card ↥(fixV (autSec A I Z)) *
        Nat.card ↥(fixV (autSec A I' Z')))
    (hSL : BinaryNaturalSL (autSec L I Z) ⊤ ⊥ 3 a)
    (hSL' : BinaryNaturalSL (autSec L I' Z') ⊤ ⊥ 3 a')
    (hff : Nat.card (Sec I Z) ≤
      Nat.card ↥(autSec A I Z) * Nat.card ↥(fixV (autSec A I Z)))
    (hff' : Nat.card (Sec I' Z') ≤
      Nat.card ↥(autSec A I' Z') * Nat.card ↥(fixV (autSec A I' Z'))) :
    SecIsoL L I Z I' Z' := by
  have hLI : L ≤ stabSub I := B1.le_stabSub_of_invariant fun l hl w hw => hNF.1 ⟨l, hl⟩ w hw
  have hLZ : L ≤ stabSub Z := B1.le_stabSub_of_invariant fun l hl w hw => hNF.2.1 ⟨l, hl⟩ w hw
  have hLI' : L ≤ stabSub I' := B1.le_stabSub_of_invariant fun l hl w hw => hNF'.1 ⟨l, hl⟩ w hw
  have hLZ' : L ≤ stabSub Z' := B1.le_stabSub_of_invariant fun l hl w hw => hNF'.2.1 ⟨l, hl⟩ w hw
  have hfaith : L ⊓ centSec I Z = ⊥ := IsGomiNatural.inf_centSec_eq_bot hnat
  have hfaith' : L ⊓ centSec I' Z' = ⊥ := IsGomiNatural.inf_centSec_eq_bot hnat'
  have hEN : autSec A I Z ≤ Subgroup.normalizer (autSec L I Z : Set (MulAut (Sec I Z))) :=
    autSec_le_normalizer hAL hLI hLZ hAI hAZ
  have hEN' : autSec A I' Z' ≤
      Subgroup.normalizer (autSec L I' Z' : Set (MulAut (Sec I' Z'))) :=
    autSec_le_normalizer hAL hLI' hLZ' hAI' hAZ'
  have hA₁ := gomiHomog_le_of_binaryNaturalSL hSL hEN hAel hff
  have hA₂ := gomiHomog_le_of_binaryNaturalSL hSL' hEN' hAel' hff'
  exact gomiHomog_secIsoL_of_sl3 hAL hAI hAZ hAI' hAZ'
    (B5.binaryNaturalSL_of_autSec hNF.2.2.1.1.le hLI hLZ hfaith hSL)
    (B5.binaryNaturalSL_of_autSec hNF'.2.2.1.1.le hLI' hLZ' hfaith' hSL')
    hA₁ hA₂ hAnc hker hAel hcost

theorem gomiFact36Homogeneity_holds : GomiFact36Homogeneity := by
  intro W _ _ hW L A I Z I' Z' hChev hLie hAL hAI hAZ hAI' hAZ'
    hNF hNF' hnat hnat' hAnc hker hAel hAq hAq' hcost
  obtain ⟨hv, hfpos, hf_le⟩ := gomi_section_card_data A I Z
  obtain ⟨hv', hf'pos, hf'_le⟩ := gomi_section_card_data A I' Z'
  have hcard := card_autSec_eq_of_inf_centSec_eq hAI hAZ hAI' hAZ' hker
  have hAel' := isElemAbelian2_autSec_of_inf_centSec_eq hAI hAZ hAI' hAZ' hker hAel
  have hAnc' := not_le_centSec_of_inf_centSec_eq hker hAnc
  have hE1 : autSec A I Z ≠ ⊥ := B69.autSec_ne_bot hAI hAZ hAnc
  have hcost' : Nat.card (Sec I' Z') * Nat.card (Sec I Z) ≤
      Nat.card ↥(autSec A I' Z') * Nat.card ↥(fixV (autSec A I' Z')) *
        Nat.card ↥(fixV (autSec A I Z)) := by
    calc Nat.card (Sec I' Z') * Nat.card (Sec I Z)
        = Nat.card (Sec I Z) * Nat.card (Sec I' Z') := by ring
      _ ≤ Nat.card ↥(autSec A I Z) * Nat.card ↥(fixV (autSec A I Z)) *
            Nat.card ↥(fixV (autSec A I' Z')) := hcost
      _ = Nat.card ↥(autSec A I' Z') * Nat.card ↥(fixV (autSec A I' Z')) *
            Nat.card ↥(fixV (autSec A I Z)) := by
          rw [hcard]
          ring
  have hbound := gomi_bound_sec hW hChev hAL hAI hAZ hNF hnat hAnc hAel hcost hf'_le hv'
  have hbound' := gomi_bound_sec hW hChev hAL hAI' hAZ' hNF' hnat' hAnc' hAel' hcost' hf_le hv
  obtain ⟨hff, hb1, hd1⟩ := hbound
  obtain ⟨hff', hb1', hd2⟩ := hbound'
  rw [hcard] at hb1' hd2 hcost'
  have htwo : 2 ≤ Nat.card ↥(autSec A I Z) := by
    have := (Subgroup.one_lt_card_iff_ne_bot (H := autSec A I Z)).2 hE1
    omega
  rcases hd1 with ⟨a, ha, hSL⟩ | h1
  · rcases hd2 with ⟨a', ha', hSL'⟩ | h2
    · exact secIsoL_of_both_binaryNaturalSL hAL hAI hAZ hAI' hAZ' hNF hNF' hnat hnat'
        hAnc hker hAel hAel' hcost hSL hSL' hff hff'
    · exact (false_of_gomi_cost_bounds htwo hf'pos hfpos hcost' h2 hb1).elim
  · exact (false_of_gomi_cost_bounds htwo hfpos hf'pos hcost h1 hb1').elim

end CFSG.GroupTheory

end
