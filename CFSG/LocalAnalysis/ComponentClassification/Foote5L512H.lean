module

public import CFSG.LocalAnalysis.ComponentClassification.Foote5L512G
public import CFSG.LocalAnalysis.ComponentClassification.Foote5L512E
public import CFSG.LocalAnalysis.ComponentClassification.Foote5L512F

public noncomputable section

namespace CFSG.ComponentClassification.Foote5

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ComponentClassification.FooteLit
  CFSG.ABGLocalTools GorensteinWalter CFSG.GH74.GLS.IVK.Lifted

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem conj_mem_centralizer_L512 {W₁ W₂ K : Subgroup G}
    (hK : ∀ k, k ∈ K ↔ (∀ w ∈ W₁, k * w = w * k) ∧ ∀ w ∈ W₂, k * w = w * k) {g : G}
    (hg : ∀ w, (w ∈ W₁ ∨ w ∈ W₂) → g⁻¹ * w * g ∈ W₁ ∨ g⁻¹ * w * g ∈ W₂) {k : G}
    (hk : k ∈ K) : g * k * g⁻¹ ∈ K := by
  have hkc : ∀ w, (w ∈ W₁ ∨ w ∈ W₂) → g * k * g⁻¹ * w = w * (g * k * g⁻¹) := by
    intro w hw
    have h1 : k * (g⁻¹ * w * g) = (g⁻¹ * w * g) * k := by
      rcases hg w hw with h2 | h2
      · exact ((hK k).mp hk).1 _ h2
      · exact ((hK k).mp hk).2 _ h2
    calc g * k * g⁻¹ * w = g * (k * (g⁻¹ * w * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * w * g) * k) * g⁻¹ := by rw [h1]
      _ = w * (g * k * g⁻¹) := by group
  exact (hK _).mpr ⟨fun w hw => hkc w (Or.inl hw), fun w hw => hkc w (Or.inr hw)⟩

theorem inv_conj_mem_L512 {V : Subgroup G} {g : G} (hg : ∀ w ∈ V, g * w * g⁻¹ ∈ V) {w : G}
    (hw : w ∈ V) : g⁻¹ * w * g ∈ V := by
  have h1 := (mem_normalizer_iff.mp (inv_mem (mem_normalizer_of_conj_mem_L512 hg)) w).mp hw
  rwa [inv_inv] at h1

namespace Sec5

variable {L₀ L Q S T : Subgroup G} {z t : G} (h : Sec5 G L₀ L Q S T z t)
  {𝕊 : Type} [Group 𝕊] [Finite 𝕊] (ε : L ⧸ pPrimeCore 2 L ≃* 𝕊)
include h

include ε in
theorem exists_y_L512 (hL24 : Foote5Lemma24iiV) (h𝕊 : FooteSimpleType 𝕊) (hQd : DSDData ↥Q)
    (hna : ∃ a ∈ S ⊓ L, ∃ b ∈ S ⊓ L, a * b ≠ b * a) {a x : G} (ha : a ∈ S ⊓ L)
    (ha2 : a * a = 1) (ha1 : a ≠ 1) (hat : a ≠ t) (hx2 : x * x = 1) (hxt : x * t * x⁻¹ = z)
    (hbQ : x * a * x⁻¹ ∈ Q) :
    ∃ y : G, x * y = y * x ∧ y * t * y⁻¹ = a ∧ y * a * y⁻¹ = a * t ∧
      y * z * y⁻¹ = x * a * x⁻¹ ∧ y * (x * a * x⁻¹) * y⁻¹ = x * a * x⁻¹ * z := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have ht2 := h.t_mul_self
  have hz2 := h.z_mul_self
  have hz1 : z ≠ 1 := fun h1 => by
    have h2 := h.z2
    rw [h1, orderOf_one] at h2
    omega
  have hatc : a * t = t * a := h.tZ a (mem_inf.mp ha).1
  have hata : a * t * a = t := by rw [hatc, mul_assoc, ha2, mul_one]
  have hxinv : x⁻¹ = x := inv_eq_of_mul_eq_one_left hx2
  have hcx : ∀ w : G, x⁻¹ * w * x = x * w * x⁻¹ := fun w => by rw [hxinv]
  set b := x * a * x⁻¹ with hb
  have hxz : x * z * x⁻¹ = t := by
    calc x * z * x⁻¹ = (x * x) * t * (x * x)⁻¹ := by rw [← hxt]; group
      _ = t := by rw [hx2]; group
  have hxb : x * b * x⁻¹ = a := by
    calc x * b * x⁻¹ = (x * x) * a * (x * x)⁻¹ := by rw [hb]; group
      _ = a := by rw [hx2]; group
  have hb2 : b * b = 1 := by
    rw [hb, show x * a * x⁻¹ * (x * a * x⁻¹) = x * (a * a) * x⁻¹ by group, ha2]
    group
  have hb1 : b ≠ 1 := fun h1 => ha1 (by rw [← hxb, h1]; group)
  have hbz : b ≠ z := fun h1 => hat (by rw [← hxb, h1, hxz])
  have hbzc : b * z = z * b := h.zS b (h.QS hbQ)
  have hbzb : b * z * b = z := by rw [hbzc, mul_assoc, hb2, mul_one]
  set W₁ := kleinFourOfCommutingInvolutions a t ha2 ht2 hatc with hW₁def
  set W₂ := kleinFourOfCommutingInvolutions b z hb2 hz2 hbzc with hW₂def
  have hW₁ : ∀ w, w ∈ W₁ ↔ w = a * t ∨ w = a ∨ w = t ∨ w = 1 := fun w =>
    mem_kleinFour_iff ha2 ht2 hatc
  have hW₂ : ∀ w, w ∈ W₂ ↔ w = b * z ∨ w = b ∨ w = z ∨ w = 1 := fun w =>
    mem_kleinFour_iff hb2 hz2 hbzc
  have hW₁4 : Nat.card W₁ = 4 :=
    (isKleinFour_kleinFourOfCommutingInvolutions a t ha2 ht2 ha1 h.t_ne_one hat hatc).card_four
  have hW₂4 : Nat.card W₂ = 4 :=
    (isKleinFour_kleinFourOfCommutingInvolutions b z hb2 hz2 hb1 hz1 hbz hbzc).card_four
  have hW₁sq : ∀ w ∈ W₁, w * w = 1 := fun w hw => by
    rcases (hW₁ w).mp hw with h1 | h1 | h1 | h1 <;> rw [h1]
    · rw [show a * t * (a * t) = a * t * a * t by group, hata, ht2]
    · exact ha2
    · exact ht2
    · exact one_mul 1
  have hW₂sq : ∀ w ∈ W₂, w * w = 1 := fun w hw => by
    rcases (hW₂ w).mp hw with h1 | h1 | h1 | h1 <;> rw [h1]
    · rw [show b * z * (b * z) = b * z * b * z by group, hbzb, hz2]
    · exact hb2
    · exact hz2
    · exact one_mul 1
  have hW₁R : W₁ ≤ S ⊓ L := fun w hw => by
    rcases (hW₁ w).mp hw with h1 | h1 | h1 | h1 <;> rw [h1]
    · exact mul_mem ha h.tR
    · exact ha
    · exact h.tR
    · exact one_mem _
  have hW₂Q : W₂ ≤ Q := fun w hw => by
    rcases (hW₂ w).mp hw with h1 | h1 | h1 | h1 <;> rw [h1]
    · exact mul_mem hbQ h.zQ
    · exact hbQ
    · exact h.zQ
    · exact one_mem _
  have hW₁₂ : ∀ u ∈ W₁, ∀ v ∈ W₂, u * v = v * u := fun u hu v hv =>
    (h.commute_Q_R (hW₂Q hv) (hW₁R hu)).symm
  have hxW₁ : ∀ w ∈ W₁, x * w * x⁻¹ ∈ W₂ := fun w hw => by
    rcases (hW₁ w).mp hw with h1 | h1 | h1 | h1 <;> rw [h1]
    · rw [show x * (a * t) * x⁻¹ = (x * a * x⁻¹) * (x * t * x⁻¹) by group, hxt]
      exact (hW₂ _).mpr (Or.inl rfl)
    · exact (hW₂ _).mpr (Or.inr (Or.inl rfl))
    · rw [hxt]; exact (hW₂ _).mpr (Or.inr (Or.inr (Or.inl rfl)))
    · rw [mul_one, mul_inv_cancel]; exact one_mem _
  have hxW₂ : ∀ w ∈ W₂, x * w * x⁻¹ ∈ W₁ := fun w hw => by
    rcases (hW₂ w).mp hw with h1 | h1 | h1 | h1 <;> rw [h1]
    · rw [show x * (b * z) * x⁻¹ = (x * b * x⁻¹) * (x * z * x⁻¹) by group, hxb, hxz]
      exact (hW₁ _).mpr (Or.inl rfl)
    · rw [hxb]; exact (hW₁ _).mpr (Or.inr (Or.inl rfl))
    · rw [hxz]; exact (hW₁ _).mpr (Or.inr (Or.inr (Or.inl rfl)))
    · rw [mul_one, mul_inv_cancel]; exact one_mem _
  set K := centralizer (W₁ : Set G) ⊓ centralizer (W₂ : Set G) with hKdef
  have hK : ∀ k, k ∈ K ↔ (∀ w ∈ W₁, k * w = w * k) ∧ ∀ w ∈ W₂, k * w = w * k := by
    intro k
    constructor
    · intro hk
      exact ⟨fun w hw => ((mem_centralizer_iff.mp (mem_inf.mp hk).1) w hw).symm,
        fun w hw => ((mem_centralizer_iff.mp (mem_inf.mp hk).2) w hw).symm⟩
    · rintro ⟨h1, h2⟩
      exact mem_inf.mpr ⟨mem_centralizer_iff.mpr fun w hw => (h1 w hw).symm,
        mem_centralizer_iff.mpr fun w hw => (h2 w hw).symm⟩
  have hW₁K : W₁ ≤ K := fun w hw => (hK w).mpr
    ⟨fun v hv => commute_of_mul_sq_L512 (hW₁sq w hw) (hW₁sq v hv) (hW₁sq _ (mul_mem hw hv)),
      fun v hv => hW₁₂ w hw v hv⟩
  have hW₂K : W₂ ≤ K := fun w hw => (hK w).mpr
    ⟨fun v hv => (hW₁₂ v hv w hw).symm,
      fun v hv => commute_of_mul_sq_L512 (hW₂sq w hw) (hW₂sq v hv) (hW₂sq _ (mul_mem hw hv))⟩
  obtain ⟨P, hP⟩ := exists_isSylowOf 2 K
  have hleP : ∀ V : Subgroup G, V ≤ K → IsPGroup 2 V → (∀ v ∈ V, ∀ k ∈ K, v * k = k * v) →
      V ≤ P := by
    intro V hVK hV2 hVc
    have hVN : V ≤ normalizer (P : Set G) := fun v hv => mem_normalizer_of_conj_mem_L512
      fun q hq => by rw [hVc v hv q (hP.le hq), mul_inv_cancel_right]; exact hq
    have heq := hP.eq_of_le le_sup_left (sup_le hP.le hVK)
      (IsPGroup.to_sup_of_normal_left' hP.isPGroup hV2 hVN)
    rw [← heq]
    exact le_sup_right
  have hW₁2 : IsPGroup 2 W₁ := IsPGroup.of_card (n := 2) (by rw [hW₁4]; norm_num)
  have hW₂2 : IsPGroup 2 W₂ := IsPGroup.of_card (n := 2) (by rw [hW₂4]; norm_num)
  have hW₁P := hleP W₁ hW₁K hW₁2 fun v hv k hk => (((hK k).mp hk).1 v hv).symm
  have hW₂P := hleP W₂ hW₂K hW₂2 fun v hv k hk => (((hK k).mp hk).2 v hv).symm
  have hPW₁ : ∀ p ∈ P, ∀ w ∈ W₁, p * w = w * p := fun p hp w hw =>
    ((hK p).mp (hP.le hp)).1 w hw
  have hPW₂ : ∀ p ∈ P, ∀ w ∈ W₂, p * w = w * p := fun p hp w hw =>
    ((hK p).mp (hP.le hp)).2 w hw
  have hKW : ∀ k ∈ K, ∀ w ∈ W₁ ⊔ W₂, k * w = w * k := by
    intro k hk w hw
    obtain ⟨u, hu, v, hv, rfl⟩ := exists_mul_of_mem_sup_commute hW₁₂ hw
    rw [← mul_assoc, ((hK k).mp hk).1 u hu, mul_assoc, ((hK k).mp hk).2 v hv, mul_assoc]
  obtain ⟨p₀, hp₀P, hcyc⟩ := h.exists_cyclic_mod_L512 ε hL24 h𝕊 hQd ha ha2 ha1 hat hbQ hb2
    hb1 hbz hbzc hW₁ hW₂ hP.isPGroup hW₁P hW₂P hPW₁ hPW₂
  obtain ⟨O, hOK, hOodd, hOchar, hdec⟩ := exists_normal_two_complement hP
    fun n hn hnP q hq => commute_of_normalizes_of_cyclic_mod hP (sup_le hW₁P hW₂P) hKW hp₀P
      hcyc hn hnP hq
  obtain ⟨e, he⟩ := hP.isPGroup ⟨p₀, hp₀P⟩
  have he' : p₀ ^ 2 ^ e = 1 := by simpa using congrArg Subtype.val he
  obtain ⟨h₁, -, h₁t, h₁a, h₁P, h₁odd⟩ := h.exists_odd_three_cycle_L512 hna ha ha2 ha1 hat
    hW₂2 hW₂Q (fun p hp => h.commute_Q_R (hW₂Q hp) ha) (fun p hp => h.commute_Q_R (hW₂Q hp) h.tR)
  have h₁at : h₁ * (a * t) * h₁⁻¹ = t := by
    rw [show h₁ * (a * t) * h₁⁻¹ = (h₁ * a * h₁⁻¹) * (h₁ * t * h₁⁻¹) by group, h₁a, h₁t, hata]
  have h₁W₁ : ∀ w ∈ W₁, h₁ * w * h₁⁻¹ ∈ W₁ := fun w hw => by
    rcases (hW₁ w).mp hw with h1 | h1 | h1 | h1 <;> rw [h1]
    · rw [h₁at]; exact (hW₁ _).mpr (Or.inr (Or.inr (Or.inl rfl)))
    · rw [h₁a]; exact (hW₁ _).mpr (Or.inl rfl)
    · rw [h₁t]; exact (hW₁ _).mpr (Or.inr (Or.inl rfl))
    · rw [mul_one, mul_inv_cancel]; exact one_mem _
  have h₁fix : ∀ w ∈ W₁, h₁ * w * h₁⁻¹ = w → w = 1 := fun w hw hfix => by
    rcases (hW₁ w).mp hw with h1 | h1 | h1 | h1 <;> rw [h1] at hfix ⊢
    · rw [h₁at] at hfix
      exact absurd (by simpa using hfix.symm) ha1
    · rw [h₁a] at hfix
      exact absurd (by simpa using hfix) h.t_ne_one
    · rw [h₁t] at hfix
      exact absurd hfix hat
  have h₁W₂ : ∀ w ∈ W₂, h₁ * w = w * h₁ := h₁P
  set h₂ := x * h₁ * x⁻¹ with hh₂
  have h₂W₁ : ∀ w ∈ W₁, h₂ * w = w * h₂ := fun w hw => by
    have h1 : x⁻¹ * w * x ∈ W₂ := by rw [hcx]; exact hxW₁ w hw
    calc x * h₁ * x⁻¹ * w = x * (h₁ * (x⁻¹ * w * x)) * x⁻¹ := by group
      _ = x * ((x⁻¹ * w * x) * h₁) * x⁻¹ := by rw [h₁W₂ _ h1]
      _ = w * (x * h₁ * x⁻¹) := by group
  have h₂W₂ : ∀ w ∈ W₂, h₂ * w * h₂⁻¹ ∈ W₂ := fun w hw => by
    have h1 : x⁻¹ * w * x ∈ W₁ := by rw [hcx]; exact hxW₂ w hw
    rw [show x * h₁ * x⁻¹ * w * (x * h₁ * x⁻¹)⁻¹ = x * (h₁ * (x⁻¹ * w * x) * h₁⁻¹) * x⁻¹ by
      group]
    exact hxW₁ _ (h₁W₁ _ h1)
  have h₂fix : ∀ w ∈ W₂, h₂ * w * h₂⁻¹ = w → w = 1 := fun w hw hfix => by
    have h1 : x⁻¹ * w * x ∈ W₁ := by rw [hcx]; exact hxW₂ w hw
    have h2 : h₁ * (x⁻¹ * w * x) * h₁⁻¹ = x⁻¹ * w * x := by
      calc h₁ * (x⁻¹ * w * x) * h₁⁻¹ = x⁻¹ * (x * h₁ * x⁻¹ * w * (x * h₁ * x⁻¹)⁻¹) * x := by
            group
        _ = x⁻¹ * w * x := by rw [hfix]
    have h3 := h₁fix _ h1 h2
    calc w = x * (x⁻¹ * w * x) * x⁻¹ := by group
      _ = 1 := by rw [h3]; group
  have h₂odd : Odd (orderOf h₂) := by
    rw [hh₂, ← MulAut.conj_apply, MulEquiv.orderOf_eq]
    exact h₁odd
  have hc := commutator_mem_of_fpf_L512 hW₁4 hW₂4 hW₁sq hW₂sq hW₁₂ hK hOK hOodd hOchar hdec
    (hP.le hp₀P) he' hcyc h₁W₁ h₁fix h₁W₂ h₁odd h₂W₂ h₂fix h₂W₁ h₂odd
  have hxK : ∀ k ∈ K, x * k * x⁻¹ ∈ K := fun k hk =>
    conj_mem_centralizer_L512 hK (fun w hw => by
      rw [hcx]
      rcases hw with hw | hw
      · exact Or.inr (hxW₁ w hw)
      · exact Or.inl (hxW₂ w hw)) hk
  have hh₁K : h₁ ∈ normalizer (K : Set G) := mem_normalizer_of_conj_mem_L512 fun k hk =>
    conj_mem_centralizer_L512 hK (fun w hw => by
      rcases hw with hw | hw
      · exact Or.inl (inv_conj_mem_L512 h₁W₁ hw)
      · rw [mul_assoc, ← h₁W₂ w hw, inv_mul_cancel_left]; exact Or.inr hw) hk
  have hh₂K : h₂ ∈ normalizer (K : Set G) := mem_normalizer_of_conj_mem_L512 fun k hk =>
    conj_mem_centralizer_L512 hK (fun w hw => by
      rcases hw with hw | hw
      · rw [mul_assoc, ← h₂W₁ w hw, inv_mul_cancel_left]; exact Or.inl hw
      · exact Or.inr (inv_conj_mem_L512 h₂W₂ hw)) hk
  have hgK : ∀ k ∈ K, (h₁ * h₂)⁻¹ * k * (h₁ * h₂)⁻¹⁻¹ ∈ K := fun k hk =>
    (mem_normalizer_iff.mp (inv_mem (mul_mem hh₁K hh₂K)) k).mp hk
  have hxg : IsPGroup 2 (zpowers x) := isPGroup_zpowers_of_pow_two (k := 1)
    (by rw [pow_one, sq]; exact hx2)
  have hOodd' : ¬ 2 ∣ Nat.card O := fun h2 => by
    have h3 := Nat.odd_iff.mp hOodd
    omega
  have hxh : x * (h₁ * h₂) * x⁻¹ = h₂ * h₁ := by
    calc x * (h₁ * h₂) * x⁻¹ = (x * h₁ * x⁻¹) * ((x * x) * h₁ * (x * x)⁻¹) := by rw [hh₂]; group
      _ = h₂ * h₁ := by rw [hx2, one_mul, inv_one, mul_one]
  obtain ⟨y, hyO, hyx⟩ := exists_commute_of_coprime hxg hOodd'
    (fun p hp o ho => by
      rcases eq_one_or_eq_of_mem_zpowers_sq hx2 hp with h1 | h1 <;> rw [h1]
      · simpa using ho
      · exact conj_mem_of_odd_char_L512 hOK hOodd hOchar hxK ho)
    (fun p hp => by
      rcases eq_one_or_eq_of_mem_zpowers_sq hx2 hp with h1 | h1 <;> rw [h1]
      · simp
      · rw [hxh]
        have h2 := conj_mem_of_odd_char_L512 hOK hOodd hOchar hgK (inv_mem hc)
        rw [show (h₁ * h₂)⁻¹ * (h₂ * h₁) =
          (h₁ * h₂)⁻¹ * (h₁ * h₂ * h₁⁻¹ * h₂⁻¹)⁻¹ * (h₁ * h₂)⁻¹⁻¹ by group]
        exact h2)
  set o := (h₁ * h₂)⁻¹ * y with ho
  have hoK := hOK hyO
  have hyeq : y = h₁ * h₂ * o := by rw [ho]; group
  have hact : ∀ u : G, (u ∈ W₁ ∨ u ∈ W₂) → y * u * y⁻¹ = h₁ * (h₂ * u * h₂⁻¹) * h₁⁻¹ := by
    intro u hu
    have h1 : o * u * o⁻¹ = u := by
      rcases hu with hu | hu
      · rw [((hK o).mp hoK).1 u hu, mul_inv_cancel_right]
      · rw [((hK o).mp hoK).2 u hu, mul_inv_cancel_right]
    rw [hyeq, show h₁ * h₂ * o * u * (h₁ * h₂ * o)⁻¹ = h₁ * (h₂ * (o * u * o⁻¹) * h₂⁻¹) * h₁⁻¹ by
      group, h1]
  have htW₁ : t ∈ W₁ := (hW₁ t).mpr (Or.inr (Or.inr (Or.inl rfl)))
  have haW₁ : a ∈ W₁ := (hW₁ a).mpr (Or.inr (Or.inl rfl))
  have hzW₂ : z ∈ W₂ := (hW₂ z).mpr (Or.inr (Or.inr (Or.inl rfl)))
  have hbW₂ : b ∈ W₂ := (hW₂ b).mpr (Or.inr (Or.inl rfl))
  have hc2 : ∀ u ∈ W₁, h₂ * u * h₂⁻¹ = u := fun u hu => by rw [h₂W₁ u hu, mul_inv_cancel_right]
  have hc1 : ∀ u ∈ W₂, h₁ * u * h₁⁻¹ = u := fun u hu => by rw [h₁W₂ u hu, mul_inv_cancel_right]
  have hh₂z : h₂ * z * h₂⁻¹ = b := by
    rw [hh₂, show x * h₁ * x⁻¹ * z * (x * h₁ * x⁻¹)⁻¹ = x * (h₁ * (x⁻¹ * z * x) * h₁⁻¹) * x⁻¹ by
      group, hcx, hxz, h₁t]
  have hh₂b : h₂ * b * h₂⁻¹ = b * z := by
    rw [hh₂, show x * h₁ * x⁻¹ * b * (x * h₁ * x⁻¹)⁻¹ = x * (h₁ * (x⁻¹ * b * x) * h₁⁻¹) * x⁻¹ by
      group, hcx, hxb, h₁a, show x * (a * t) * x⁻¹ = (x * a * x⁻¹) * (x * t * x⁻¹) by group, hxt]
  refine ⟨y, hyx x (mem_zpowers x), ?_, ?_, ?_, ?_⟩
  · rw [hact t (Or.inl htW₁), hc2 t htW₁, h₁t]
  · rw [hact a (Or.inl haW₁), hc2 a haW₁, h₁a]
  · rw [hact z (Or.inr hzW₂), hh₂z, hc1 b hbW₂]
  · rw [hact b (Or.inr hbW₂), hh₂b, hc1 _ (mul_mem hbW₂ hzW₂)]

end Sec5

end CFSG.ComponentClassification.Foote5
