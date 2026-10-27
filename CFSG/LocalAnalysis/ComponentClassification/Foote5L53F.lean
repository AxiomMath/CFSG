module

public import CFSG.LocalAnalysis.ComponentClassification.Foote5L53E
public import CFSG.LocalAnalysis.ComponentClassification.Foote5L53D
public import CFSG.LocalAnalysis.ComponentClassification.Foote5L51

public noncomputable section

namespace CFSG.ComponentClassification.Foote5

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ComponentClassification.FooteLit
  CFSG.ABGLocalTools

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem conj_mem_commutator_conjugate {P : Subgroup G} {a x : G} (hx : x ∈ ⁅P, P⁆) :
    a * x * a⁻¹ ∈ ⁅conjugate P a⁻¹, conjugate P a⁻¹⁆ := by
  have h1 : (MulAut.conj a).toMonoidHom x ∈ ⁅P, P⁆.map (MulAut.conj a).toMonoidHom :=
    mem_map_of_mem _ hx
  rw [map_commutator] at h1
  rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at h1
  have h2 : conjugate P a⁻¹ = P.map (MulAut.conj a).toMonoidHom := by
    rw [conjugate, inv_inv]
  rw [h2]
  exact h1

namespace Sec5

variable {L₀ L Q S T : Subgroup G} {z t : G} (h : Sec5 G L₀ L Q S T z t)
  {𝕊 : Type} [Group 𝕊] [Finite 𝕊] (ε : L ⧸ pPrimeCore 2 L ≃* 𝕊)
  {Lin : Subgroup (MulAut 𝕊)}
include h

theorem conj_t_inner (hD : Foote5AutData 𝕊 Lin) {w a U : G} (hwQ : w ∈ Q)
    (hw2 : orderOf w = 2) (hwz : w ≠ z) (hwa : a⁻¹ * w * a ∈ S) (hza : a⁻¹ * z * a ∈ S)
    (hU : U = a⁻¹ * w * a ∨ U = a⁻¹ * z * a ∨ U = a⁻¹ * w * a * (a⁻¹ * z * a))
    (hUc : ∀ x ∈ S ⊓ L ⊔ zpowers (a⁻¹ * w * a), x * U = U * x)
    (htc : t ∈ ⁅S ⊓ L ⊔ zpowers (a⁻¹ * w * a), S ⊓ L ⊔ zpowers (a⁻¹ * w * a)⁆) :
    actG L ε (a * t * a⁻¹) ∈ innAut5 𝕊 := by
  have hw22 : w * w = 1 := by rw [← sq, ← hw2, pow_orderOf_eq_one]
  have hz22 : z * z = 1 := by rw [← sq, ← h.z2, pow_orderOf_eq_one]
  have hw1 : w ≠ 1 := fun h1 => by rw [h1, orderOf_one] at hw2; omega
  have hcwz : w * z = z * w := h.zS w (h.QS hwQ)
  have hu : a * U * a⁻¹ = w ∨ a * U * a⁻¹ = z ∨ a * U * a⁻¹ = w * z := by
    rcases hU with rfl | rfl | rfl
    · left; group
    · right; left; group
    · right; right; group
  set u := a * U * a⁻¹ with hudef
  have huQ : u ∈ Q := by
    rcases hu with h1 | h1 | h1 <;> rw [h1]
    · exact hwQ
    · exact h.zQ
    · exact mul_mem hwQ h.zQ
  have hu2 : orderOf u = 2 := by
    rcases hu with h1 | h1 | h1 <;> rw [h1]
    · exact hw2
    · exact h.z2
    · refine orderOf_eq_prime ?_ fun h2 => hwz ?_
      · rw [sq, show w * z * (w * z) = w * (z * w) * z by group, ← hcwz,
          show w * (w * z) * z = (w * w) * (z * z) by group, hw22, hz22, one_mul]
      · calc w = w * z * z := by rw [mul_assoc, hz22, mul_one]
          _ = z := by rw [h2, one_mul]
  set P := S ⊓ L ⊔ zpowers (a⁻¹ * w * a) with hP
  have hPu : conjugate P a⁻¹ ≤ centralizer ({u} : Set G) := by
    refine conjugate_le_of_forall fun x hx => mem_centralizer_singleton_iff.mpr ?_
    rw [inv_inv, hudef]
    have h1 := hUc x hx
    calc a * x * a⁻¹ * (a * U * a⁻¹) = a * (x * U) * a⁻¹ := by group
      _ = a * (U * x) * a⁻¹ := by rw [h1]
      _ = a * U * a⁻¹ * (a * x * a⁻¹) := by group
  obtain ⟨-, hLu, hLuF, -, -, -⟩ := h.footeF_data huQ hu2
  have hPN : conjugate P a⁻¹ ≤ normalizer (footeF L₀ u : Set G) :=
    hPu.trans (le_normalizer_of_mem_footeFamilyOf h.sec4.huniq hLu hLuF)
  obtain ⟨εu, hεu⟩ := h.exists_actG_footeF_eq ε huQ hu2
  have h1 := mem_innAut_of_mem_commutator hD εu hPN (conj_mem_commutator_conjugate htc)
  have hta : ∀ y, a⁻¹ * y * a ∈ S → a * t * a⁻¹ * y = y * (a * t * a⁻¹) := by
    intro y hy
    have h2 := h.tZ _ hy
    calc a * t * a⁻¹ * y = a * (t * (a⁻¹ * y * a)) * a⁻¹ := by group
      _ = a * ((a⁻¹ * y * a) * t) * a⁻¹ := by rw [h2]
      _ = y * (a * t * a⁻¹) := by group
  have htz : a * t * a⁻¹ ∈ centralizer ({z} : Set G) :=
    mem_centralizer_singleton_iff.mpr (hta z hza)
  have htN := h.centralizer_le_normalizer htz
  have htu : a * t * a⁻¹ ∈ centralizer ({u} : Set G) := by
    rcases hu with h2 | h2 | h2 <;> rw [h2]
    · exact mem_centralizer_singleton_iff.mpr (hta w hwa)
    · exact htz
    · refine mem_centralizer_singleton_iff.mpr ?_
      have h3 := hta w hwa
      have h4 := hta z hza
      calc a * t * a⁻¹ * (w * z) = (a * t * a⁻¹ * w) * z := by group
        _ = w * (a * t * a⁻¹ * z) := by rw [h3, mul_assoc]
        _ = w * z * (a * t * a⁻¹) := by rw [h4]; group
  rw [← hεu _ htN htu]
  exact h1

theorem false_of_za_inner (hD : Foote5AutData 𝕊 Lin)
    (hz51 : ∀ y, (∀ s ∈ S, s * y = y * s) → IsConj z y → y ∈ Q)
    (ht51 : ∀ y, (∀ s ∈ S, s * y = y * s) → IsConj t y → y ∈ S ⊓ L) {w a n : G}
    (hwQ : w ∈ Q) (hw2 : orderOf w = 2) (hwz : w ≠ z)
    (hnw : ∀ y, (∀ s ∈ S, s * y = y * s) → ¬ IsConj w y)
    (hS₀ : IsSylowOf 2 (S ⊓ centralizer ({w} : Set G)) (centralizer ({w} : Set G)))
    (hnS : n ∈ S) (hn : n * w * n⁻¹ = w * z)
    (hwa : a⁻¹ * w * a ∈ S ⊓ centralizer ({w} : Set G))
    (hza : a⁻¹ * z * a ∈ S ⊓ centralizer ({w} : Set G)) (hwaQ : a⁻¹ * w * a ∉ Q)
    (hzaQ : a⁻¹ * z * a ∉ Q) (hinn : actG L ε (a⁻¹ * z * a) ∈ innAut5 𝕊) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hw22 : w * w = 1 := by rw [← sq, ← hw2, pow_orderOf_eq_one]
  have ht22 : t * t = 1 := by rw [← sq, ← h.t2, pow_orderOf_eq_one]
  have hcwz : w * z = z * w := h.zS w (h.QS hwQ)
  obtain ⟨q, ρ, hqW, hρ, hρρ, hA₂, hzwt, hzwzt⟩ :=
    h.za_inner_data ε hz51 hwQ hw2 hwz hnS hn hza hzaQ hinn
  have h11 : a⁻¹ * w * a * (a⁻¹ * w * a) = 1 := by
    rw [show a⁻¹ * w * a * (a⁻¹ * w * a) = a⁻¹ * (w * w) * a by group, hw22]; group
  have h1c : IsConj w (a⁻¹ * w * a) := isConj_iff.mpr ⟨a⁻¹, by rw [inv_inv]⟩
  have h1inn := h.wa_not_inner ε hwQ hw2 hwz hnw hzwt hzwzt hwa hwaQ h1c h11
  have h12 : a⁻¹ * w * a * (a⁻¹ * z * a) = a⁻¹ * z * a * (a⁻¹ * w * a) := by
    rw [show a⁻¹ * w * a * (a⁻¹ * z * a) = a⁻¹ * (w * z) * a by group, hcwz]; group
  have hqQ : q ∈ Q := by
    rcases hqW with hq | hq <;> rw [hq]
    · exact hwQ
    · exact mul_mem hwQ h.zQ
  have hA1w := mem_centralizer_singleton_iff.mp (mem_inf.mp hwa).2
  have hA1z := h.zS _ (mem_inf.mp hwa).1
  have hq1 : q * (a⁻¹ * w * a) = a⁻¹ * w * a * q := by
    rcases hqW with hq | hq <;> rw [hq]
    · exact hA1w.symm
    · rw [mul_assoc, ← hA1z, ← mul_assoc, ← hA1w, mul_assoc]
  obtain ⟨U, hU, hUc, htc⟩ := h.exists_U ε hD (mem_inf.mp hwa).1 h11 h1inn hqQ hρ hρρ hA₂ h12
    hq1
  have ht'inn := h.conj_t_inner ε hD hwQ hw2 hwz (mem_inf.mp hwa).1 (mem_inf.mp hza).1 hU hUc
    htc
  set t' := a * t * a⁻¹ with ht'
  have hta : ∀ y, a⁻¹ * y * a ∈ S → t' * y = y * t' := by
    intro y hy
    have h2 := h.tZ _ hy
    calc t' * y = a * (t * (a⁻¹ * y * a)) * a⁻¹ := by rw [ht']; group
      _ = a * ((a⁻¹ * y * a) * t) * a⁻¹ := by rw [h2]
      _ = y * t' := by rw [ht']; group
  have ht'K : t' ∈ centralizer ({w} : Set G) ⊓ centralizer ({z} : Set G) :=
    mem_inf.mpr ⟨mem_centralizer_singleton_iff.mpr (hta w (mem_inf.mp hwa).1),
      mem_centralizer_singleton_iff.mpr (hta z (mem_inf.mp hza).1)⟩
  have hS₀' : IsSylowOf 2 (S ⊓ centralizer ({w} : Set G))
      (centralizer ({w} : Set G) ⊓ centralizer ({z} : Set G)) :=
    hS₀.of_le (le_inf inf_le_right fun s hs => mem_centralizer_singleton_iff.mpr
      (h.zS s (mem_inf.mp hs).1)) inf_le_left
  have ht'2 : IsPGroup 2 (zpowers t') := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, pow_one, ht', orderOf_conj', h.t2]
  obtain ⟨b₁, hb₁K, hb₁⟩ := exists_conj_le_of_isSylowOf hS₀' (zpowers_le.mpr ht'K) ht'2
  set y₁ := b₁⁻¹ * t' * b₁ with hy₁
  have hy₁S₀ : y₁ ∈ S ⊓ centralizer ({w} : Set G) := hb₁ t' (mem_zpowers t')
  have hb₁N := h.centralizer_le_normalizer (mem_inf.mp hb₁K).2
  have ht'N := h.centralizer_le_normalizer (mem_inf.mp ht'K).2
  have hy₁inn : actG L ε y₁ ∈ innAut5 𝕊 := by
    obtain ⟨c, hc⟩ := ht'inn
    rw [hy₁, actG_mul ε (mul_mem (inv_mem hb₁N) ht'N) hb₁N, actG_mul ε (inv_mem hb₁N) ht'N,
      actG_inv ε hb₁N, ← hc]
    refine ⟨(actG L ε b₁)⁻¹ c, ?_⟩
    rw [← mulAut_mul_conj_mul_inv, inv_inv]
  have hy₁2 : y₁ * y₁ = 1 := by
    rw [hy₁, show b₁⁻¹ * t' * b₁ * (b₁⁻¹ * t' * b₁) = b₁⁻¹ * (a * (t * t) * a⁻¹) * b₁ by
      rw [ht']; group, ht22]; group
  obtain ⟨q₂, ρ₂, hq₂W, -, -, hy₁e, hk₂⟩ := h.exists_conj_qt ε hwQ hw2 hwz
    (mem_inf.mp hy₁S₀).1 (mem_centralizer_singleton_iff.mp (mem_inf.mp hy₁S₀).2) hy₁2 hy₁inn
  have hty₁ : IsConj t y₁ := (isConj_iff.mpr ⟨a, rfl⟩).trans (isConj_iff.mpr ⟨b₁⁻¹, by
    rw [inv_inv, hy₁]⟩)
  have hwzw : IsConj w (w * z) := isConj_iff.mpr ⟨n, hn⟩
  have hzt_not : ¬ IsConj t z := fun h2 => h.t_not_mem_Q (hz51 t h.tZ h2.symm)
  have hρ₂1 : ρ₂ ≠ 1 := by
    intro h2
    rw [h2, mul_one] at hy₁e
    rw [hy₁e] at hty₁
    rcases hq₂W with hq | hq | hq | hq <;> rw [hq] at hty₁
    · exact h.t_ne_one (isConj_one_left.mp hty₁)
    · exact hnw t h.tZ hty₁.symm
    · exact hzt_not hty₁
    · exact hnw t h.tZ (hwzw.trans hty₁.symm)
  obtain ⟨k₂, -, hk₂C, hk₂'⟩ := hk₂ hρ₂1
  have hq₂1 : q₂ = 1 := by
    have htq₂ : IsConj t (q₂ * t) := hty₁.trans (isConj_iff.mpr ⟨k₂⁻¹, by rw [inv_inv, hk₂']⟩)
    rcases hq₂W with hq | hq | hq | hq <;> rw [hq] at htq₂
    · exact hq
    · exact absurd (htq₂.trans hzwt.symm) hzt_not
    · exfalso
      have h3 := ht51 _ h.zt_center htq₂
      have h4 : z ∈ Q ⊓ L := mem_inf.mpr ⟨h.zQ, by
        rw [show z = z * t * t⁻¹ by group]; exact mul_mem (mem_inf.mp h3).2 (inv_mem h.tL)⟩
      rw [h.Q_inf_L, mem_bot] at h4
      have := h.z2
      rw [h4, orderOf_one] at this
      omega
    · exact absurd (htq₂.trans hzwzt.symm) hzt_not
  have hk₂z : k₂ * z = z * k₂ := (mem_centralizer_iff.mp hk₂C z (mem_inf.mpr ⟨h.zQ,
    mem_centralizer_singleton_iff.mpr hcwz.symm⟩)).symm
  have hbz : b₁ * k₂ * z = z * (b₁ * k₂) := by
    rw [mul_assoc, hk₂z, ← mul_assoc, mem_centralizer_singleton_iff.mp (mem_inf.mp hb₁K).2,
      mul_assoc]
  have hbt : (b₁ * k₂)⁻¹ * t' * (b₁ * k₂) = t := by
    rw [show (b₁ * k₂)⁻¹ * t' * (b₁ * k₂) = k₂⁻¹ * y₁ * k₂ by rw [hy₁]; group, hk₂', hq₂1,
      one_mul]
  have hzt : IsConj (z * t) (a⁻¹ * z * a * t) := by
    refine isConj_iff.mpr ⟨a⁻¹ * (b₁ * k₂), ?_⟩
    have h2 : b₁ * k₂ * t * (b₁ * k₂)⁻¹ = t' := by
      rw [← hbt]; group
    calc a⁻¹ * (b₁ * k₂) * (z * t) * (a⁻¹ * (b₁ * k₂))⁻¹ =
        a⁻¹ * (b₁ * k₂ * z) * t * (b₁ * k₂)⁻¹ * a := by group
      _ = a⁻¹ * z * (b₁ * k₂ * t * (b₁ * k₂)⁻¹) * a := by rw [hbz]; group
      _ = a⁻¹ * z * a * t := by rw [h2, ht']; group
  rw [hA₂] at hzt
  by_cases hρt : ρ = t
  · rw [hρt, mul_assoc, ht22, mul_one] at hzt
    rcases hqW with hq | hq <;> rw [hq] at hzt
    · exact hnw _ h.zt_center hzt.symm
    · exact hnw _ h.zt_center (hwzw.trans hzt.symm)
  · have hρtR : ρ * t ∈ S ⊓ L := mul_mem hρ h.tR
    have hρt2 : orderOf (ρ * t) = 2 := by
      refine orderOf_eq_prime ?_ fun h2 => hρt ?_
      · rw [sq, show ρ * t * (ρ * t) = ρ * (t * ρ) * t by group,
          ← h.tZ ρ (mem_inf.mp hρ).1, show ρ * (ρ * t) * t = ρ * ρ * (t * t) by group, hρρ,
          ht22, one_mul]
      · calc ρ = ρ * t * t := by rw [mul_assoc, ht22, mul_one]
          _ = t := by rw [h2, one_mul]
    obtain ⟨k₃, -, hk₃C, hk₃⟩ := h.exists_conj_t_footeF hwQ hw2 (h.isPGroup_Q.to_le inf_le_left)
      inf_le_left (fun x hx => (mem_inf.mp hx).2) hρtR hρt2
    have hqk : k₃⁻¹ * q * k₃ = q := by
      have h2 := mem_centralizer_iff.mp hk₃C q (mem_inf.mpr ⟨hqQ,
        mem_centralizer_singleton_iff.mpr (by
          rcases hqW with hq | hq <;> rw [hq]
          rw [mul_assoc, ← hcwz])⟩)
      rw [mul_assoc, h2]; group
    have h3 : IsConj (q * ρ * t) (q * t) := isConj_iff.mpr ⟨k₃⁻¹, by
      rw [inv_inv, show k₃⁻¹ * (q * ρ * t) * k₃ = k₃⁻¹ * q * k₃ * (k₃⁻¹ * (ρ * t) * k₃) by
        group, hqk, hk₃]⟩
    have hz' : IsConj z (z * t) := by
      rcases hqW with hq | hq <;> rw [hq] at h3 hzt
      · exact hzwt.trans (hzt.trans h3).symm
      · exact hzwzt.trans (hzt.trans h3).symm
    exact h.t_not_mem_Q (by
      rw [show t = z⁻¹ * (z * t) by group]
      exact mul_mem (inv_mem h.zQ) (hz51 _ h.zt_center hz'))

end Sec5

end CFSG.ComponentClassification.Foote5
