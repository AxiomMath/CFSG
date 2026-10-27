module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.AutExt.YCentK
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.AutExt.YThree
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.AutExt.EtaGz

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section4

open Section3

variable {G : Type} [Group G] {a z : G}

private theorem mul_self_of_comm {M : Type} [Semigroup M] {x y : M} (hxy : x * y = y * x) :
    (x * y) * (x * y) = (x * x) * (y * y) :=
  Commute.mul_mul_mul_comm hxy.symm x y

private theorem mul_self_of_class (h : F5Base a z) {x : G} (hx : IsConj a x ∨ IsConj z x) :
    x * x = 1 := by
  have h2 : x ^ 2 = 1 := by simpa [h.orderOf_eq_two hx] using pow_orderOf_eq_one x
  rwa [pow_two] at h2

theorem aut_Y_cent_of_base (h : F5Base a z) {b w t : G} (hb : IsConj a b) (hw : w ∈ orb2BB a z b)
    (ht : t ∈ Gxy b w ∧ t ∈ orb2A a b) {η : G → G}
    (hη : IsIsoOn (Gxy b w) (Gxy b w) η) (hfix : ∀ x ∈ Gxyz b w t, η x = x) :
    (∀ x ∈ Gxy b w, η x = x) ∨ ∀ x ∈ Gxy b w, η x = t * x * t⁻¹ := by
  classical
  have hFb : F5Base b z := h.of_isConj hb (IsConj.refl z)
  have hbw : b * w = w * b := h.mul_comm (Or.inl hb) (Or.inr hw.1) (Or.inr hw.2)
  have hwb' : IsConj z (w * b) := by rw [← hbw]; exact hw.2
  have hb2 : b * b = 1 := mul_self_of_class h (Or.inl hb)
  have hw2 : w * w = 1 := mul_self_of_class h (Or.inr hw.1)
  have ht2 : t * t = 1 := mul_self_of_class h (Or.inl ht.2.1)
  have htb : b * t = t * b := mem_Gx.mp (mem_Gxy.mp ht.1).1
  have htw : w * t = t * w := mem_Gx.mp (mem_Gxy.mp ht.1).2
  have hbY : b ∈ Gxy b w := mem_Gxy.mpr ⟨mem_Gx.mpr rfl, mem_Gx.mpr hbw.symm⟩
  have hwY : w ∈ Gxy b w := mem_Gxy.mpr ⟨mem_Gx.mpr hbw, mem_Gx.mpr rfl⟩
  have hwbY : w * b ∈ Gxy b w := (Gxy b w).mul_mem hwY hbY
  have hb_comm : ∀ y ∈ Gxy b w, b * y = y * b := fun y hy => mem_Gx.mp (mem_Gxy.mp hy).1
  have hw_comm : ∀ y ∈ Gxy b w, w * y = y * w := fun y hy => mem_Gx.mp (mem_Gxy.mp hy).2
  have hcent : ∀ v : G, (v = 1 ∨ v = w ∨ v = b ∨ v = w * b) → ∀ y ∈ Gxy b w, v * y = y * v := by
    intro v hv y hy
    rcases hv with hv | hv | hv | hv
    · rw [hv, one_mul, mul_one]
    · rw [hv]; exact hw_comm y hy
    · rw [hv]; exact hb_comm y hy
    · rw [hv, mul_assoc, hb_comm y hy, ← mul_assoc, hw_comm y hy, mul_assoc]
  have hsq : ∀ v : G, (v = 1 ∨ v = w ∨ v = b ∨ v = w * b) → v * v = 1 := by
    intro v hv
    rcases hv with hv | hv | hv | hv
    · rw [hv, one_mul]
    · rw [hv]; exact hw2
    · rw [hv]; exact hb2
    · rw [hv, mul_self_of_comm hbw.symm, hw2, hb2, mul_one]
  have hmemY : ∀ v : G, (v = 1 ∨ v = w ∨ v = b ∨ v = w * b) → v ∈ Gxy b w := by
    intro v hv
    rcases hv with hv | hv | hv | hv
    · rw [hv]; exact (Gxy b w).one_mem
    · rw [hv]; exact hwY
    · rw [hv]; exact hbY
    · rw [hv]; exact hwbY
  have hwT : w ∈ Gxyz b w t := mem_Gxyz.mpr ⟨mem_Gx.mpr hbw, mem_Gx.mpr rfl, mem_Gx.mpr htw.symm⟩
  have hbT : b ∈ Gxyz b w t :=
    mem_Gxyz.mpr ⟨mem_Gx.mpr rfl, mem_Gx.mpr hbw.symm, mem_Gx.mpr htb.symm⟩
  have hfixv : ∀ v : G, (v = 1 ∨ v = w ∨ v = b ∨ v = w * b) → η v = v := by
    intro v hv
    rcases hv with hv | hv | hv | hv
    · rw [hv]; exact hη.map_one
    · rw [hv]; exact hfix _ hwT
    · rw [hv]; exact hfix _ hbT
    · rw [hv, hη.map_mul w hwY b hbY, hfix _ hwT, hfix _ hbT]
  have hdec : ∀ x ∈ Gxy b w, ∃ v : G, (v = 1 ∨ v = w ∨ v = b ∨ v = w * b) ∧
      ∃ u ∈ derivedOf (Gxy b w), x = v * u := by
    intro x hx
    rw [Gxy_comm b w] at hx
    obtain ⟨u, hu, hxu⟩ := decomp_Y_of_base h hw.1 hb hwb' x hx
    rw [Gxy_comm w b] at hu
    rcases hxu with h' | h' | h' | h'
    · exact ⟨1, Or.inl rfl, u, hu, by rw [h', one_mul]⟩
    · exact ⟨w, Or.inr (Or.inl rfl), u, hu, h'⟩
    · exact ⟨b, Or.inr (Or.inr (Or.inl rfl)), u, hu, h'⟩
    · exact ⟨w * b, Or.inr (Or.inr (Or.inr rfl)), u, hu, h'⟩
  have hnotder : ∀ x : G, x ∈ Gxy b w → x * x = 1 → IsConj a x → IsConj a (b * x) →
      x ∉ derivedOf (Gxy b w) := by
    intro x hxY hx2 hxA hbxA hxK
    have hxGb : x ∈ Gx b := (mem_Gxy.mp hxY).1
    have hle : derivedOf (Gxy b w) ≤ derivedOf (Gx b) :=
      derivedOf_mono (by rw [Gxy_eq_inf]; exact inf_le_left)
    have hiff := hFb.loc.fusion2.self.mem_derived_iff x hxGb
      (by rw [pow_two]; exact hx2)
    have h1 : IsConj b x := hb.symm.trans hxA
    have h2 : IsConj b (b * x) := hb.symm.trans hbxA
    exact ((hiff.mp (hle hxK)).mp h1) h2
  obtain ⟨u₀, hu₀, y, hyK, hty⟩ : ∃ u₀ : G, (u₀ = w ∨ u₀ = w * b) ∧
      ∃ y ∈ derivedOf (Gxy b w), t = u₀ * y := by
    obtain ⟨v, hv, u, hu, htu⟩ := hdec t ht.1
    rcases hv with hv | hv | hv | hv
    · exfalso
      rw [hv, one_mul] at htu
      refine hnotder t ht.1 ht2 ht.2.1 ht.2.2 ?_
      rw [htu]
      exact hu
    · rw [hv] at htu
      exact ⟨w, Or.inl rfl, u, hu, htu⟩
    · exfalso
      rw [hv] at htu
      have hbtu : b * t = u := by rw [htu, ← mul_assoc, hb2, one_mul]
      refine hnotder (b * t) ((Gxy b w).mul_mem hbY ht.1) ?_ ht.2.2 ?_ ?_
      · rw [mul_self_of_comm htb, hb2, ht2, mul_one]
      · rw [← mul_assoc, hb2, one_mul]
        exact ht.2.1
      · rw [hbtu]
        exact hu
    · rw [hv] at htu
      exact ⟨w * b, Or.inr rfl, u, hu, htu⟩
  have hu₀v : u₀ = w ∨ u₀ = w * b := hu₀
  have hu₀c : ∀ x ∈ Gxy b w, u₀ * x = x * u₀ := by
    intro x hx
    rcases hu₀v with h' | h'
    · rw [h']; exact hcent w (Or.inr (Or.inl rfl)) x hx
    · rw [h']; exact hcent (w * b) (Or.inr (Or.inr (Or.inr rfl))) x hx
  have hu₀2 : u₀ * u₀ = 1 := by
    rcases hu₀v with h' | h'
    · rw [h']; exact hsq w (Or.inr (Or.inl rfl))
    · rw [h']; exact hsq (w * b) (Or.inr (Or.inr (Or.inr rfl)))
  have hyY : y ∈ Gxy b w := derivedOf_le _ hyK
  have hy2 : y * y = 1 := by
    have h' := ht2
    rw [hty, mul_self_of_comm (hu₀c y hyY), hu₀2, one_mul] at h'
    exact h'
  have hy1 : y ≠ 1 := by
    intro hy
    have htu : t = u₀ := by rw [hty, hy, mul_one]
    have hzt : IsConj z t := by
      rw [htu]
      rcases hu₀v with h' | h'
      · rw [h']; exact hw.1
      · rw [h']; exact hwb'
    exact not_isConj_of_isF5Type h.iface h.typ (ht.2.1.trans hzt.symm)
  have hconj_t : ∀ x ∈ Gxy b w, t * x * t⁻¹ = y * x * y⁻¹ := by
    intro x hx
    have hc : u₀ * (y * x * y⁻¹) = (y * x * y⁻¹) * u₀ :=
      hu₀c _ ((Gxy b w).mul_mem ((Gxy b w).mul_mem hyY hx) ((Gxy b w).inv_mem hyY))
    rw [hty, mul_inv_rev, inv_eq_of_mul_eq_one_right hu₀2]
    calc u₀ * y * x * (y⁻¹ * u₀) = u₀ * (y * x * y⁻¹) * u₀ := by simp only [mul_assoc]
      _ = (y * x * y⁻¹) * u₀ * u₀ := by rw [hc]
      _ = y * x * y⁻¹ := by rw [mul_assoc, hu₀2, mul_one]
  have hwbt : w ∈ Gxy b t := mem_Gxy.mpr ⟨mem_Gx.mpr hbw, mem_Gx.mpr htw.symm⟩
  obtain ⟨ε, hεT, hε⟩ := exists_order_three_Gxyz h hb ht.2 hwbt hw2
  have hε3 : ε ^ 3 = 1 := by rw [← hε]; exact pow_orderOf_eq_one ε
  have hε1 : ε ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hε
    exact absurd hε (by norm_num)
  obtain ⟨hεb, hεw, hεt⟩ := mem_Gxyz.mp hεT
  have hεY : ε ∈ Gxy b w := mem_Gxy.mpr ⟨hεb, hεw⟩
  have hεK : ε ∈ derivedOf (Gxy b w) := by
    obtain ⟨v, hv, u, hu, hεu⟩ := hdec ε hεY
    have hvu : v * u = u * v := hcent v hv u (derivedOf_le _ hu)
    have h4 : ε = u ^ 4 := by
      calc ε = ε ^ 3 * ε := by rw [hε3, one_mul]
        _ = ε ^ 4 := (pow_succ ε 3).symm
        _ = (v * u) ^ 4 := by rw [hεu]
        _ = v ^ 4 * u ^ 4 := (Commute.mul_pow hvu 4)
        _ = u ^ 4 := by
          have hv4 : v ^ 4 = 1 := by
            have h2 : v ^ 2 = 1 := by rw [pow_two]; exact hsq v hv
            calc v ^ 4 = (v ^ 2) ^ 2 := by rw [← pow_mul]
              _ = 1 := by rw [h2, one_pow]
          rw [hv4, one_mul]
    rw [h4]
    exact (derivedOf (Gxy b w)).pow_mem hu 4
  have hyε : y * ε = ε * y := by
    have h1 : t * ε = ε * t := mem_Gx.mp hεt
    rw [hty] at h1
    have h2 : u₀ * (y * ε) = u₀ * (ε * y) := by
      calc u₀ * (y * ε) = (u₀ * y) * ε := by rw [mul_assoc]
        _ = ε * (u₀ * y) := h1
        _ = (ε * u₀) * y := by rw [mul_assoc]
        _ = (u₀ * ε) * y := by rw [hu₀c ε hεY]
        _ = u₀ * (ε * y) := by rw [mul_assoc]
    exact mul_left_cancel h2
  obtain ⟨ρ, θ, hC⟩ := exists_orthCoord_Y h hw.1 hb hwb'
  have hyM : y ∈ CFSG.Open.pCoreOf 2 (derivedOf (Gxy b w)) :=
    hC.mem_of_comm_order_three hyK hεK hy2 hε3 hε1 hyε
  have hfixK : ∀ l ∈ derivedOf (Gxy b w), y * l = l * y → η l = l := by
    intro l hl hyl
    have hlY : l ∈ Gxy b w := derivedOf_le _ hl
    refine hfix l (mem_Gxyz.mpr ⟨(mem_Gxy.mp hlY).1, (mem_Gxy.mp hlY).2, mem_Gx.mpr ?_⟩)
    rw [hty]
    calc u₀ * y * l = u₀ * (y * l) := by rw [mul_assoc]
      _ = u₀ * (l * y) := by rw [hyl]
      _ = (u₀ * l) * y := by rw [mul_assoc]
      _ = (l * u₀) * y := by rw [hu₀c l hlY]
      _ = l * (u₀ * y) := by rw [mul_assoc]
  rcases hC.aut_cent hyM hy1 hη.derived hfixK with hid | hconj
  · left
    intro x hx
    obtain ⟨v, hv, u, hu, hxu⟩ := hdec x hx
    rw [hxu, hη.map_mul v (hmemY v hv) u (derivedOf_le _ hu), hfixv v hv, hid u hu]
  · right
    intro x hx
    obtain ⟨v, hv, u, hu, hxu⟩ := hdec x hx
    have hvy : v * y = y * v := hcent v hv y hyY
    rw [hconj_t x hx, hxu, hη.map_mul v (hmemY v hv) u (derivedOf_le _ hu), hfixv v hv,
      hconj u hu]
    calc v * (y * u * y⁻¹) = (v * y) * u * y⁻¹ := by simp only [mul_assoc]
      _ = (y * v) * u * y⁻¹ := by rw [hvy]
      _ = y * (v * u) * y⁻¹ := by simp only [mul_assoc]

end CFSG.EvenSporadicStandard.HNRecog.Section4
