module

public import CFSG.LocalAnalysis.ComponentClassification.Foote5L53I
public import CFSG.LocalAnalysis.ComponentClassification.Foote5L53F
public import CFSG.LocalAnalysis.ComponentClassification.Foote5L53G

public noncomputable section

namespace CFSG.ComponentClassification.Foote5

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ComponentClassification.FooteLit
  CFSG.ABGLocalTools

variable {G : Type} [Group G] [Finite G]

structure BadData (L Q S : Subgroup G) (z t : G) {𝕊 : Type} [Group 𝕊]
    (ε : L ⧸ pPrimeCore 2 L ≃* 𝕊) (Lin : Subgroup (MulAut 𝕊)) (w n b : G) : Prop where
  wQ : w ∈ Q
  w2 : orderOf w = 2
  wz : w ≠ z
  sylow : IsSylowOf 2 (S ⊓ centralizer ({w} : Set G)) (centralizer ({w} : Set G))
  nS : n ∈ S
  n_conj : n * w * n⁻¹ = w * z
  not_central : ∀ y, (∀ s ∈ S, s * y = y * s) → ¬ IsConj w y
  b_mem : b ∈ normalizer ((S ⊓ centralizer ({w} : Set G) : Subgroup G) : Set G)
  b_conj : b⁻¹ * w * b = w * t
  b_t : b⁻¹ * t * b = t
  zb : actG L ε (b⁻¹ * z * b) ∉ Lin

namespace Sec5

variable {L₀ L Q S T : Subgroup G} {z t : G} (h : Sec5 G L₀ L Q S T z t)
  {𝕊 : Type} [Group 𝕊] [Finite 𝕊] (ε : L ⧸ pPrimeCore 2 L ≃* 𝕊)
  {Lin : Subgroup (MulAut 𝕊)}
include h

theorem conj_t_of_mem_normalizer_R (hna : ∃ a ∈ S ⊓ L, ∃ b ∈ S ⊓ L, a * b ≠ b * a) {x : G}
    (hx : x ∈ normalizer ((S ⊓ L : Subgroup G) : Set G)) : x * t * x⁻¹ = t := by
  have htR : x * t * x⁻¹ ∈ S ⊓ L := (mem_normalizer_iff.mp hx t).mp h.tR
  have hZ : ∀ r ∈ S ⊓ L, x * t * x⁻¹ * r = r * (x * t * x⁻¹) := by
    intro r hr
    have h1 := h.tZ _ (mem_inf.mp (conj_mem_of_mem_normalizer hx hr)).1
    calc x * t * x⁻¹ * r = x * (t * (x⁻¹ * r * x)) * x⁻¹ := by group
      _ = x * ((x⁻¹ * r * x) * t) * x⁻¹ := by rw [h1]
      _ = r * (x * t * x⁻¹) := by group
  rcases h.center_R hna htR hZ with h1 | h1
  · have h3 := orderOf_conj' x t
    rw [h1, orderOf_one, h.t2] at h3
    omega
  · exact h1

theorem exists_badData (hD : Foote5AutData 𝕊 Lin) (h𝕊 : FooteSimpleType 𝕊)
    (hz51 : ∀ y, (∀ s ∈ S, s * y = y * s) → IsConj z y → y ∈ Q)
    (ht51 : ∀ y, (∀ s ∈ S, s * y = y * s) → IsConj t y → y ∈ S ⊓ L) {w : G} (hwQ : w ∈ Q)
    (hw2 : orderOf w = 2) (hng : ¬ Good53 S L Q w) :
    ∃ x ∈ normalizer ((S ⊓ L : Subgroup G) : Set G), ∃ w' n b : G, x⁻¹ * w * x = w' ∧
      BadData L Q S z t ε Lin w' n b := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨x, -, hxR, hw'Q, hS₀⟩ := h.exists_conj_isSylowOf_centralizer hwQ
  obtain ⟨w', hw'⟩ : ∃ w', x⁻¹ * w * x = w' := ⟨_, rfl⟩
  rw [hw'] at hw'Q hS₀
  have hw'2 : orderOf w' = 2 := by
    rw [← hw', show x⁻¹ * w * x = x⁻¹ * w * x⁻¹⁻¹ by rw [inv_inv], orderOf_conj', hw2]
  have hng' : ¬ Good53 S L Q w' := fun hg => hng (good53_of_conj hxR (hw' ▸ hg))
  obtain ⟨hS₀', n, hnS, hn⟩ := h.isSylowOf_centralizer_of_not_good hw'Q hw'2 hng' hS₀
  have hwZ : ¬ ∀ s ∈ S, s * w' = w' * s := fun hZ =>
    hng' ⟨1, one_mem _, by simpa using hw'Q, by simpa using hZ⟩
  have hw'z : w' ≠ z := fun h1 => hwZ (h1 ▸ h.zS)
  have hlt : Nat.card ↥(S ⊓ centralizer ({w'} : Set G)) < Nat.card S := by
    refine card_lt_of_lt (lt_of_le_of_ne inf_le_left fun h1 => hwZ fun s hs => ?_)
    exact mem_centralizer_singleton_iff.mp (mem_inf.mp (h1.symm ▸ hs :
      s ∈ S ⊓ centralizer ({w'} : Set G))).2
  have hnw : ∀ y, (∀ s ∈ S, s * y = y * s) → ¬ IsConj w' y := fun y hy =>
    not_isConj_of_center h.isPGroup_S hS₀' hlt hy
  have hw22 : w' * w' = 1 := by rw [← sq, ← hw'2, pow_orderOf_eq_one]
  have hz22 : z * z = 1 := by rw [← sq, ← h.z2, pow_orderOf_eq_one]
  have hcwz : w' * z = z * w' := h.zS w' (h.QS hw'Q)
  obtain ⟨a, hwa, hza, hwaQ, hzaQ, hwzaQ⟩ := h.exists_a hw'Q hw'2 hng' hS₀'
  have hA : a⁻¹ * w' * a * (a⁻¹ * z * a) = a⁻¹ * (w' * z) * a := by group
  have h12 : a⁻¹ * w' * a * (a⁻¹ * z * a) = a⁻¹ * z * a * (a⁻¹ * w' * a) := by
    rw [hA, hcwz]; group
  have h11 : a⁻¹ * w' * a * (a⁻¹ * w' * a) = 1 := by
    rw [show a⁻¹ * w' * a * (a⁻¹ * w' * a) = a⁻¹ * (w' * w') * a by group, hw22]; group
  have h22 : a⁻¹ * z * a * (a⁻¹ * z * a) = 1 := by
    rw [show a⁻¹ * z * a * (a⁻¹ * z * a) = a⁻¹ * (z * z) * a by group, hz22]; group
  have hwzw : IsConj w' (w' * z) := isConj_iff.mpr ⟨n, hn⟩
  have hwt : IsConj w' (w' * t) := by
    rcases h.exists_inner_of_klein ε h𝕊 (mem_inf.mp hwa).1 (mem_inf.mp hza).1 h12 h11 h22
        hwaQ hzaQ (by rwa [hA]) with hinn | hinn | hinn
    · exact h.isConj_w_mul_t ε hw'Q hw'2 hw'z hnw hnS hn hwa hwaQ
        (isConj_iff.mpr ⟨a⁻¹, by rw [inv_inv]⟩) h11 hinn
    · exact (h.false_of_za_inner ε hD hz51 ht51 hw'Q hw'2 hw'z hnw hS₀' hnS hn hwa hza hwaQ
        hzaQ hinn).elim
    · refine h.isConj_w_mul_t ε hw'Q hw'2 hw'z hnw hnS hn (mul_mem hwa hza) (by rwa [hA])
        ?_ ?_ hinn
      · rw [hA]
        exact hwzw.trans (isConj_iff.mpr ⟨a⁻¹, by rw [inv_inv]⟩)
      · rw [show a⁻¹ * w' * a * (a⁻¹ * z * a) * (a⁻¹ * w' * a * (a⁻¹ * z * a)) =
          a⁻¹ * w' * a * (a⁻¹ * w' * a) * (a⁻¹ * z * a * (a⁻¹ * z * a)) by
            rw [mul_assoc (a⁻¹ * w' * a), ← mul_assoc (a⁻¹ * z * a), ← h12]; group,
          h11, h22, one_mul]
  obtain ⟨b, hb, hbw⟩ := h.exists_b hS₀' hwt
  have hzb := h.zb_not_mem_lin ε hD hz51 hw'Q hw'2 hw'z hnw hn hb hbw
  have hna := h.nonabelian_R_of_zb ε hD hw'Q hb hzb
  have hbt := h.conj_t_eq_of_b ε hD hna hz51 hw'Q hw'2 hw'z hnw hn hb
  exact ⟨x, hxR, w', n, b, hw', ⟨hw'Q, hw'2, hw'z, hS₀', hnS, hn, hnw, hb, hbw, hbt, hzb⟩⟩

include ε in
theorem star (hD : Foote5AutData 𝕊 Lin) (h𝕊 : FooteSimpleType 𝕊)
    (hz51 : ∀ y, (∀ s ∈ S, s * y = y * s) → IsConj z y → y ∈ Q)
    (ht51 : ∀ y, (∀ s ∈ S, s * y = y * s) → IsConj t y → y ∈ S ⊓ L) {u : G} (huQ : u ∈ Q)
    (hu2 : orderOf u = 2) :
    Good53 S L Q u ∨ ((∃ g ∈ centralizer ({t} : Set G), g⁻¹ * u * g = u * t) ∧
      ∀ y, (∀ s ∈ S, s * y = y * s) → ¬ IsConj u y) := by
  by_cases hg : Good53 S L Q u
  · exact Or.inl hg
  right
  obtain ⟨x, hxR, w', n, b, hxw, hB⟩ := h.exists_badData ε hD h𝕊 hz51 ht51 huQ hu2 hg
  have hna := h.nonabelian_R_of_zb ε hD hB.wQ hB.b_mem hB.zb
  have hxt : x * t * x⁻¹ = t := h.conj_t_of_mem_normalizer_R hna hxR
  have hbt : b * t = t * b := by
    calc b * t = b * (b⁻¹ * t * b) := by rw [hB.b_t]
      _ = t * b := by group
  have hxt' : x * t = t * x := by
    calc x * t = x * t * x⁻¹ * x := by group
      _ = t * x := by rw [hxt]
  have hxt'' : x⁻¹ * t = t * x⁻¹ := by
    calc x⁻¹ * t = x⁻¹ * (x * t * x⁻¹) := by rw [hxt]
      _ = t * x⁻¹ := by group
  have hu : u = x * w' * x⁻¹ := by rw [← hxw]; group
  refine ⟨⟨x * b * x⁻¹, mem_centralizer_singleton_iff.mpr ?_, ?_⟩,
    fun y hy hc => hB.not_central y hy ((isConj_iff.mpr ⟨x, hu.symm⟩).trans hc)⟩
  · calc x * b * x⁻¹ * t = x * b * (x⁻¹ * t) := by group
      _ = x * b * (t * x⁻¹) := by rw [hxt'']
      _ = x * (b * t) * x⁻¹ := by group
      _ = x * (t * b) * x⁻¹ := by rw [hbt]
      _ = (x * t) * b * x⁻¹ := by group
      _ = (t * x) * b * x⁻¹ := by rw [hxt']
      _ = t * (x * b * x⁻¹) := by group
  · calc (x * b * x⁻¹)⁻¹ * u * (x * b * x⁻¹) = x * (b⁻¹ * (x⁻¹ * u * x) * b) * x⁻¹ := by
          group
      _ = x * (b⁻¹ * w' * b) * x⁻¹ := by rw [hxw]
      _ = x * (w' * t) * x⁻¹ := by rw [hB.b_conj]
      _ = x * w' * x⁻¹ * (x * t * x⁻¹) := by group
      _ = u * t := by rw [hxt, ← hu]

theorem conj_t_mem_QR
    (hstar : ∀ u ∈ Q, orderOf u = 2 → Good53 S L Q u ∨
      ((∃ g ∈ centralizer ({t} : Set G), g⁻¹ * u * g = u * t) ∧
        ∀ y, (∀ s ∈ S, s * y = y * s) → ¬ IsConj u y))
    (hna : ∃ a ∈ S ⊓ L, ∃ b ∈ S ⊓ L, a * b ≠ b * a)
    (ht51 : ∀ y, (∀ s ∈ S, s * y = y * s) → IsConj t y → y ∈ S ⊓ L) {y q r : G}
    (hty : IsConj t y) (hq : q ∈ Q) (hr : r ∈ S ⊓ L) (hy : y = q * r) : q = 1 := by
  by_contra hq1
  have ht22 : t * t = 1 := by rw [← sq, ← h.t2, pow_orderOf_eq_one]
  have hyy : y * y = 1 := by
    obtain ⟨c, rfl⟩ := isConj_iff.mp hty
    rw [show c * t * c⁻¹ * (c * t * c⁻¹) = c * (t * t) * c⁻¹ by group, ht22]; group
  have hqr := h.commute_Q_R hq hr
  have hqq : q * q = 1 := by
    have h1 : q * q * (r * r) = 1 := by
      rw [← hyy, hy, show q * r * (q * r) = q * (r * q) * r by group, ← hqr]; group
    have h2 : q * q ∈ Q ⊓ L := by
      refine mem_inf.mpr ⟨mul_mem hq hq, ?_⟩
      rw [eq_inv_of_mul_eq_one_left h1]
      exact inv_mem (mul_mem (mem_inf.mp hr).2 (mem_inf.mp hr).2)
    rw [h.Q_inf_L, mem_bot] at h2
    exact h2
  have hrr : r * r = 1 := by
    rw [← hyy, hy, show q * r * (q * r) = q * (r * q) * r by group, ← hqr,
      show q * (q * r) * r = q * q * (r * r) by group, hqq, one_mul]
  have hq2 : orderOf q = 2 := orderOf_eq_prime (by rw [sq]; exact hqq) hq1
  have key : IsConj t q ∨ IsConj t (q * t) := by
    by_cases hr1 : r = 1
    · left
      rw [hy, hr1, mul_one] at hty
      exact hty
    · right
      have hr2 : orderOf r = 2 := orderOf_eq_prime (by rw [sq]; exact hrr) hr1
      obtain ⟨k, -, hkC, hk⟩ := h.exists_conj_t_footeF h.zQ h.z2 h.isPGroup_Q le_rfl
        (fun x hx => h.S_le_centralizer (h.QS hx)) hr hr2
      have hkq : k⁻¹ * q * k = q := by
        have h2 := mem_centralizer_iff.mp hkC q hq
        rw [mul_assoc, h2]; group
      refine hty.trans (isConj_iff.mpr ⟨k⁻¹, ?_⟩)
      rw [inv_inv, hy, show k⁻¹ * (q * r) * k = k⁻¹ * q * k * (k⁻¹ * r * k) by group, hkq, hk]
  rcases hstar q hq hq2 with ⟨g, hgR, hgQ, hgZ⟩ | ⟨⟨g, hgC, hg⟩, hnc⟩
  · have hgt : g⁻¹ * t * g = t := by
      have h1 := h.conj_t_of_mem_normalizer_R hna (inv_mem hgR)
      rwa [inv_inv] at h1
    have hq'1 : g⁻¹ * q * g ≠ 1 := fun h1 => hq1 (by
      calc q = g * (g⁻¹ * q * g) * g⁻¹ := by group
        _ = 1 := by rw [h1]; group)
    have hcq : IsConj q (g⁻¹ * q * g) := isConj_iff.mpr ⟨g⁻¹, by rw [inv_inv]⟩
    rcases key with h1 | h1
    · have h2 := ht51 _ hgZ (h1.trans hcq)
      have h3 : g⁻¹ * q * g ∈ Q ⊓ L := mem_inf.mpr ⟨hgQ, (mem_inf.mp h2).2⟩
      rw [h.Q_inf_L, mem_bot] at h3
      exact hq'1 h3
    · have hZ : ∀ s ∈ S, s * (g⁻¹ * q * g * t) = g⁻¹ * q * g * t * s := fun s hs => by
        calc s * (g⁻¹ * q * g * t) = (s * (g⁻¹ * q * g)) * t := by group
          _ = (g⁻¹ * q * g * s) * t := by rw [hgZ s hs]
          _ = g⁻¹ * q * g * (s * t) := by group
          _ = g⁻¹ * q * g * (t * s) := by rw [h.tZ s hs]
          _ = g⁻¹ * q * g * t * s := by group
      have hc : IsConj (q * t) (g⁻¹ * q * g * t) := isConj_iff.mpr ⟨g⁻¹, by
        rw [inv_inv, show g⁻¹ * (q * t) * g = g⁻¹ * q * g * (g⁻¹ * t * g) by group, hgt]⟩
      have h2 := ht51 _ hZ (h1.trans hc)
      have h3 : g⁻¹ * q * g ∈ Q ⊓ L := mem_inf.mpr ⟨hgQ, by
        rw [show g⁻¹ * q * g = g⁻¹ * q * g * t * t⁻¹ by group]
        exact mul_mem (mem_inf.mp h2).2 (inv_mem h.tL)⟩
      rw [h.Q_inf_L, mem_bot] at h3
      exact hq'1 h3
  · rcases key with h1 | h1
    · exact hnc t h.tZ h1.symm
    · have hgt : g⁻¹ * t * g = t := by
        have h2 := mem_centralizer_singleton_iff.mp hgC
        rw [mul_assoc, ← h2]; group
      have hc : IsConj (q * t) q := isConj_iff.mpr ⟨g⁻¹, by
        rw [inv_inv, show g⁻¹ * (q * t) * g = g⁻¹ * q * g * (g⁻¹ * t * g) by group, hg, hgt,
          mul_assoc, ht22, mul_one]⟩
      exact hnc t h.tZ (h1.trans hc).symm

end Sec5

end CFSG.ComponentClassification.Foote5
