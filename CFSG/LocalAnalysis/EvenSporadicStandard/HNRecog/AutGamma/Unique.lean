module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.AutGamma.Comm
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.AutGamma.Rigid

public section

namespace CFSG.EvenSporadicStandard.HNRecog.AutGamma

open CFSG.EvenSporadicStandard.HNRecog CFSG.EvenSporadicStandard.HNRecog.Section3

variable {G : Type} [Group G] {a z : G}

theorem act_gammaConj_base (hF : IsF5Type a z) {x : G} (hx : IsConj a x) :
    act (gammaConj a a) x = a * x * a := by
  rw [act_gammaConj a hx, inv_eq_of_isConj hF (IsConj.refl a)]

theorem gammaConj_base_inv (hF : IsF5Type a z) : (gammaConj a a)⁻¹ = gammaConj a a := by
  rw [← map_inv, inv_eq_of_isConj hF (IsConj.refl a)]

theorem act_gammaConj_base_of_mem_orb2A (hF : IsF5Type a z) {b : G} (hb : b ∈ orb2A a a) :
    act (gammaConj a a) b = b := by
  rw [act_gammaConj_base hF hb.1, comm_of_adj hF (IsConj.refl a) hb.1 hb.2]
  have haa : a * a = 1 := mul_self_of_isConj hF (IsConj.refl a)
  rw [mul_assoc, haa, mul_one]

theorem eq_gammaConj_base (hF : IsF5Type a z) (hL : F5Local G a z) (hlines : LinesThrough a z)
    (hperp : PerpThreeA a) (τ : Gamma a ≃g Gamma a) (h2 : ∀ x ∈ orb2A a a, act τ x = x)
    (h3 : ∀ x ∈ orb3A a a, act τ x ≠ x) : τ = gammaConj a a := by
  have ha : act τ a = a := act_base_of_fix_two hF hL τ h2
  have haa : a * a = 1 := mul_self_of_isConj hF (IsConj.refl a)
  have h3' : ∀ x ∈ orb3A a a, act τ x = a * x * a := by
    intro x hx
    have hmem : act τ x ∈ gammaPerp a (orb2A a a ∩ orb2A a x) := by
      refine ⟨isConj_act τ hx.1, fun s hs => Or.inr ?_⟩
      have hxs : x ≠ s := by
        rintro rfl
        have h1 : IsConj a (x * x) := hs.2.2
        rw [mul_self_of_isConj hF hx.1] at h1
        exact ne_one_of_isConj hF h1 rfl
      have h := (adj_act_iff τ hx.1 hs.1.1).2 ⟨hxs, hs.2.2⟩
      rw [h2 s hs.1] at h
      refine ⟨fun hh => h.1 hh.symm, ?_⟩
      rw [← comm_of_adj hF (isConj_act τ hx.1) hs.1.1 h.2]
      exact h.2
    have hm := hperp x hx hmem
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hm
    rcases hm with h | h | h
    · exfalso
      have hxa : x = a := act_injOn τ hx.1 (IsConj.refl a) (h.trans ha.symm)
      have h1 := hx.2.1
      rw [hxa, haa, orderOf_one] at h1
      omega
    · exact absurd h (h3 x hx)
    · exact h
  have hone : (gammaConj a a)⁻¹ * τ = 1 := by
    refine eq_one_of_fix_two_three hF hL hlines _ (fun b hb => ?_) (fun x hx => ?_)
    · rw [act_mul _ _ hb.1, h2 b hb, gammaConj_base_inv hF, act_gammaConj_base_of_mem_orb2A hF hb]
    · have hc : IsConj a (a * x * a) := h3' x hx ▸ isConj_act τ hx.1
      rw [act_mul _ _ hx.1, h3' x hx, gammaConj_base_inv hF, act_gammaConj_base hF hc]
      calc a * (a * x * a) * a = (a * a) * x * (a * a) := by group
        _ = x := by rw [haa]; group
  calc τ = gammaConj a a * ((gammaConj a a)⁻¹ * τ) := by group
    _ = gammaConj a a := by rw [hone, mul_one]

theorem conj_gammaConj_base (hF : IsF5Type a z) (hL : F5Local G a z) (hlines : LinesThrough a z)
    (hperp : PerpThreeA a) (σ : Gamma a ≃g Gamma a) (hσ : act σ a = a) :
    σ * gammaConj a a * σ⁻¹ = gammaConj a a := by
  have haa : a * a = 1 := mul_self_of_isConj hF (IsConj.refl a)
  have hσ' : act σ⁻¹ a = a := by
    have h := act_inv_act σ (IsConj.refl a)
    rwa [hσ] at h
  have hform : ∀ {x : G}, IsConj a x → act (σ * gammaConj a a * σ⁻¹) x =
      act σ (act (gammaConj a a) (act σ⁻¹ x)) := by
    intro x hx
    rw [act_mul _ _ hx, act_mul _ _ (isConj_act σ⁻¹ hx)]
  refine eq_gammaConj_base hF hL hlines hperp _ (fun b hb => ?_) (fun x hx hfix => ?_)
  · have hb' : act σ⁻¹ b ∈ orb2A a a := act_mem_orb2A hF σ⁻¹ hσ' hb
    rw [hform hb.1, act_gammaConj_base_of_mem_orb2A hF hb', act_act_inv σ hb.1]
  · obtain ⟨w, hw⟩ : ∃ w, w = act σ⁻¹ x := ⟨_, rfl⟩
    have hwc : IsConj a w := hw ▸ isConj_act σ⁻¹ hx.1
    rw [hform hx.1, ← hw] at hfix
    have hfix' : act (gammaConj a a) w = w := by
      have h := congrArg (act σ⁻¹) hfix
      rwa [act_inv_act σ (isConj_act _ hwc), ← hw] at h
    rw [act_gammaConj_base hF hwc] at hfix'
    have hcomm : a * w = w * a := by
      calc a * w = a * w * (a * a) := by rw [haa, mul_one]
        _ = (a * w * a) * a := by group
        _ = w * a := by rw [hfix']
    have h := comm_act_of_comm hF hL hlines σ hσ hwc hcomm
    rw [hw, act_act_inv σ hx.1] at h
    exact not_comm_of_mem_orb3A hF hx h

end CFSG.EvenSporadicStandard.HNRecog.AutGamma
