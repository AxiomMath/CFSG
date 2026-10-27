module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1M24Tight

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch

open CFSG.Sporadic.Schreier CFSG.Sporadic.Mathieu CFSG.Blueprint CFSG.Quasithin
  CFSG.QuasithinUnique.Setup.Family CFSG.QuasithinUnique.Setup.X1

theorem m24TightNoQuad :
    ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w * w = 1) →
      ∀ L E : Subgroup (MulAut W), CFSG.IsQuasisimple ↥L → IsIrrOn L →
        Nonempty (CQ L ≃* NativeSporadic.Carrier .M24) →
        E ≤ Subgroup.normalizer (L : Set (MulAut W)) → E ≠ ⊥ → IsElemAbelian2 E →
        Nat.card E = 2 ^ 6 → (fixV E).index = 2 ^ 6 → False := by
  intro W _ _ hW L E hq hirr hiso hE hEne hEel hEcard hidx
  obtain ⟨e⟩ := hiso
  have e' : CQ L ≃* S24 := e
  have hperf : Group.IsPerfect ↥L := hq.1
  have hAut : ∀ φ : S24 ≃* S24, ∃ s : S24, ∀ x, φ x = s * x * s⁻¹ :=
    autInner_of_card_le m24_center_eq_bot' m24_mulAut_card
  have hEL : E ≤ L := le_of_autInner hW hperf hirr hE hEel e' hAut
  have hL : L ≠ ⊥ := by
    intro h
    have h1 : Nat.card ↥L = 1 := by rw [h]; simp
    have h2 : Nat.card (CQ L) ∣ Nat.card ↥L := Subgroup.card_quotient_dvd_card _
    rw [Nat.card_congr e'.toEquiv, m24_card_eq, h1] at h2
    have := Nat.le_of_dvd one_pos h2
    norm_num at this
  have hWge : 2 ^ orderOf (2 : ZMod 23) ≤ Nat.card W := by
    have : Fact (Nat.Prime 23) := ⟨by norm_num⟩
    exact two_pow_le_card_of_dvd hW e' (p := 23) (by norm_num)
      (by rw [m24_card_eq]; exact Dvd.dvd.mul_left (by norm_num) _)
  rw [orderOf_two_zmod_23] at hWge
  have hWbig : 256 < Nat.card W := by
    have : (2 : ℕ) ^ 11 = 2048 := by norm_num
    omega
  have hBcard : Nat.card (imgSub L E hEL e') = 64 := by
    rw [card_imgSub hW hirr hEL hEel e', hEcard]
    norm_num
  obtain ⟨s, hs⟩ := m24_unique64 (imgSub L E hEL e') (imgSub_comm (hEL := hEL) (e := e') hEel)
    (imgSub_sq (hEL := hEL) (e := e') hEel) hBcard
  obtain ⟨ŝ, hŝ⟩ := redHom_surjective L e' s
  set Ê : Subgroup (MulAut W) := conjSub (ŝ : MulAut W) E with hÊ
  have hÊL : Ê ≤ L := by
    intro x hx
    obtain ⟨b, hb, rfl⟩ := mem_conjSub.1 hx
    exact L.mul_mem (L.mul_mem ŝ.2 (hEL hb)) (L.inv_mem ŝ.2)
  have hÊel : IsElemAbelian2 Ê := by
    refine ⟨fun x hx y hy => ?_, fun x hx => ?_⟩
    · obtain ⟨b, hb, rfl⟩ := mem_conjSub.1 hx
      obtain ⟨b', hb', rfl⟩ := mem_conjSub.1 hy
      calc (ŝ : MulAut W) * b * (ŝ : MulAut W)⁻¹ * ((ŝ : MulAut W) * b' * (ŝ : MulAut W)⁻¹)
          = (ŝ : MulAut W) * (b * b') * (ŝ : MulAut W)⁻¹ := by group
        _ = (ŝ : MulAut W) * (b' * b) * (ŝ : MulAut W)⁻¹ := by rw [hEel.1 b hb b' hb']
        _ = _ := by group
    · obtain ⟨b, hb, rfl⟩ := mem_conjSub.1 hx
      have hb2 : b * b = 1 := by rw [← sq]; exact hEel.2 b hb
      calc ((ŝ : MulAut W) * b * (ŝ : MulAut W)⁻¹) ^ 2
          = (ŝ : MulAut W) * (b * b) * (ŝ : MulAut W)⁻¹ := by rw [sq]; group
        _ = 1 := by rw [hb2]; group
  have hÊidx : (fixV Ê).index = 64 := (index_fixV_conjSub _ _).trans (by rw [hidx]; norm_num)
  have hÊT : ∀ x, x ∈ imgSub L Ê hÊL e' ↔ s⁻¹ * x * s ∈ imgSub L E hEL e' := by
    intro x
    rw [mem_imgSub, mem_imgSub]
    constructor
    · rintro ⟨c, hc⟩
      obtain ⟨b, hb, hbc⟩ := mem_conjSub.1 c.2
      refine ⟨⟨b, hb⟩, ?_⟩
      have h1 : Subgroup.inclusion hÊL c = ŝ * Subgroup.inclusion hEL ⟨b, hb⟩ * ŝ⁻¹ :=
        Subtype.ext (by simp [← hbc])
      rw [h1, map_mul, map_mul, map_inv, hŝ] at hc
      rw [← hc]
      group
    · rintro ⟨b, hb⟩
      refine ⟨⟨(ŝ : MulAut W) * (b : MulAut W) * (ŝ : MulAut W)⁻¹,
        mem_conjSub.2 ⟨b, b.2, rfl⟩⟩, ?_⟩
      have h1 : Subgroup.inclusion hÊL ⟨(ŝ : MulAut W) * (b : MulAut W) * (ŝ : MulAut W)⁻¹,
          mem_conjSub.2 ⟨b, b.2, rfl⟩⟩ = ŝ * Subgroup.inclusion hEL b * ŝ⁻¹ :=
        Subtype.ext (by simp)
      rw [h1, map_mul, map_mul, map_inv, hŝ, hb]
      group
  have hflip : ∀ (El : List S24), (∀ x, x ∈ imgSub L E hEL e' ↔ s * x * s⁻¹ ∈ El) →
      ∀ x, x ∈ imgSub L Ê hÊL e' ↔ x ∈ El := by
    intro El hEl x
    rw [hÊT, hEl]
    have : s * (s⁻¹ * x * s) * s⁻¹ = x := by group
    rw [this]
  have hÊidx' : (fixV Ê).index = 64 := hÊidx
  rcases hs with h1 | h2
  · refine tight_chain_false hW hperf hirr hL e' m24_gen11 hÊL hÊel hÊidx' hWbig m24E1l
      (hflip _ h1) (m24Cj m24E1G2) (m24Cj m24E1G3) (adjCert_of_adjData m24_e1_adj.1)
      (adjCert_of_adjData m24_e1_adj.2) ?_
    exact m24_closure_top_of_slp m24E1B _ _ m24E1Slp m24E1Tg.1 m24E1Tg.2 m24_e1_check.2.2.2.2.2.2
      m24_e1_gen.1 m24_e1_gen.2
  · refine tight_chain_false hW hperf hirr hL e' m24_gen11 hÊL hÊel hÊidx' hWbig m24E2l
      (hflip _ h2) (m24Cj m24E2G2) (m24Cj m24E2G3) (adjCert_of_adjData m24_e2_adj.1)
      (adjCert_of_adjData m24_e2_adj.2) ?_
    exact m24_closure_top_of_slp m24E2B _ _ m24E2Slp m24E2Tg.1 m24E2Tg.2 m24_e2_check.2.2.2.2.2.2
      m24_e2_gen.1 m24_e2_gen.2

end CFSG.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch
