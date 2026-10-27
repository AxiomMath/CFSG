module

public import CFSG.LocalAnalysis.EvenBN.Tits.N.StarBasic
public import CFSG.LocalAnalysis.EvenBN.Tits.N.P5Lin
public import CFSG.LocalAnalysis.EvenBN.Tits.N.P5Frob

public section

namespace CFSG.LocalAnalysis.EvenBN.Tits.N.P5

open Subgroup CFSG.Open CFSG.LocalAnalysis.EvenBN.Tits.N

variable {Γ : Type*} [Group Γ]

theorem k618_pow_eq_one_or_self {t : Γ} (ht2 : t * t = 1) (e : ℕ) : t ^ e = 1 ∨ t ^ e = t := by
  induction e with
  | zero => exact Or.inl (pow_zero t)
  | succ n ih =>
    rcases ih with h | h
    · exact Or.inr (by rw [pow_succ, h, one_mul])
    · exact Or.inl (by rw [pow_succ, h, ht2])

theorem k618_exists_mul_t {t : Γ} {W₀ W : Subgroup Γ} (ht2 : t * t = 1)
    (hW₀eq : ∀ w ∈ W₀, ∃ v ∈ W, ∃ e : ℕ, w = v * t ^ e) {a : Γ} (ha : a ∈ W₀) (haW : a ∉ W) :
    ∃ v ∈ W, a = v * t := by
  obtain ⟨v, hv, e, rfl⟩ := hW₀eq a ha
  rcases k618_pow_eq_one_or_self ht2 e with h | h
  · exact (haW (by rw [h, mul_one]; exact hv)).elim
  · exact ⟨v, hv, by rw [h]⟩

theorem k618_mul_inv_mem_W {t : Γ} {W₀ W : Subgroup Γ} (ht2 : t * t = 1)
    (hW₀eq : ∀ w ∈ W₀, ∃ v ∈ W, ∃ e : ℕ, w = v * t ^ e) {a b : Γ} (ha : a ∈ W₀) (hb : b ∈ W₀)
    (haW : a ∉ W) (hbW : b ∉ W) : a * b⁻¹ ∈ W := by
  obtain ⟨v₁, hv₁, rfl⟩ := k618_exists_mul_t ht2 hW₀eq ha haW
  obtain ⟨v₂, hv₂, rfl⟩ := k618_exists_mul_t ht2 hW₀eq hb hbW
  have e : v₁ * t * (v₂ * t)⁻¹ = v₁ * v₂⁻¹ := by group
  rw [e]
  exact mul_mem hv₁ (inv_mem hv₂)

theorem k618_part_involution {x y : Γ} {K W₀ : Subgroup Γ} (hW₀K : W₀ ≤ K)
    (hKW₀ : K ≤ normalizer (W₀ : Set Γ)) (hFW₀ : F20 x y ⊓ W₀ = ⊥) {d w f : Γ} (hdK : d ∈ K)
    (hd2 : d * d = 1) (hdW₀ : d ∉ W₀) (hw : w ∈ W₀) (hf : f ∈ F20 x y) (hdwf : d = w * f) :
    f * f = 1 ∧ f ≠ 1 := by
  subst hdwf
  have hfK : f ∈ K := by
    have e : f = w⁻¹ * (w * f) := by group
    rw [e]
    exact mul_mem (inv_mem (hW₀K hw)) hdK
  refine ⟨?_, ?_⟩
  · have hmem : f * f ∈ F20 x y ⊓ W₀ := by
      refine mem_inf.2 ⟨mul_mem hf hf, ?_⟩
      have e : f * f = (f * w * f⁻¹)⁻¹ * w⁻¹ * (w * f * (w * f)) := by group
      rw [e, hd2, mul_one]
      exact mul_mem (inv_mem ((mem_normalizer_iff.1 (hKW₀ hfK) w).1 hw)) (inv_mem hw)
    rw [hFW₀] at hmem
    exact mem_bot.1 hmem
  · rintro rfl
    exact hdW₀ (by rw [mul_one]; exact hw)

theorem k618_mul_inv_mem_W₀ {x y : Γ} (hF : IsF20 x y) {K W₀ D : Subgroup Γ} (hW₀K : W₀ ≤ K)
    (hKW₀ : K ≤ normalizer (W₀ : Set Γ))
    (hKdec : ∀ k ∈ K, ∃ w ∈ W₀, ∃ f ∈ F20 x y, k = w * f) (hFW₀ : F20 x y ⊓ W₀ = ⊥)
    (hDK : D ≤ K) (hD : IsElemAbelian 2 D) {a b : Γ} (ha : a ∈ D) (hb : b ∈ D)
    (haW₀ : a ∉ W₀) (hbW₀ : b ∉ W₀) : a * b⁻¹ ∈ W₀ := by
  have hab : a * b = b * a := congrArg Subtype.val (hD.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have ha2 : a * a = 1 := by rw [← pow_two]; exact hD.2 a ha
  have hb2 : b * b = 1 := by rw [← pow_two]; exact hD.2 b hb
  obtain ⟨w₁, hw₁, f₁, hf₁, hfa⟩ := hKdec a (hDK ha)
  obtain ⟨w₂, hw₂, f₂, hf₂, hfb⟩ := hKdec b (hDK hb)
  obtain ⟨hf₁2, hf₁1⟩ := k618_part_involution hW₀K hKW₀ hFW₀ (hDK ha) ha2 haW₀ hw₁ hf₁ hfa
  obtain ⟨hf₂2, hf₂1⟩ := k618_part_involution hW₀K hKW₀ hFW₀ (hDK hb) hb2 hbW₀ hw₂ hf₂ hfb
  have hc : f₁ * f₂ * f₁⁻¹ * f₂⁻¹ = 1 := by
    have hmem : f₁ * f₂ * f₁⁻¹ * f₂⁻¹ ∈ F20 x y ⊓ W₀ := by
      refine mem_inf.2 ⟨mul_mem (mul_mem (mul_mem hf₁ hf₂) (inv_mem hf₁)) (inv_mem hf₂), ?_⟩
      have e : f₁ * f₂ * f₁⁻¹ * f₂⁻¹ =
          w₁⁻¹ * (a * w₂⁻¹ * a⁻¹) * (a * b * a⁻¹ * b⁻¹) * (b * w₁ * b⁻¹) * w₂ := by
        rw [hfa, hfb]; group
      have e1 : a * b * a⁻¹ * b⁻¹ = 1 := by rw [hab]; group
      rw [e, e1, mul_one]
      exact mul_mem (mul_mem (mul_mem (inv_mem hw₁)
        ((mem_normalizer_iff.1 (hKW₀ (hDK ha)) _).1 (inv_mem hw₂)))
        ((mem_normalizer_iff.1 (hKW₀ (hDK hb)) _).1 hw₁)) hw₂
    rw [hFW₀] at hmem
    exact mem_bot.1 hmem
  have hc' : f₁ * f₂ = f₂ * f₁ := mul_inv_eq_iff_eq_mul.1 (mul_inv_eq_one.1 hc)
  have heq : f₁ = f₂ := hF.eq_of_involutions_comm hf₁ hf₂ hf₁2 hf₂2 hf₁1 hf₂1 hc'
  rw [hfa, hfb, heq]
  have e : w₁ * f₂ * (w₂ * f₂)⁻¹ = w₁ * w₂⁻¹ := by group
  rw [e]
  exact mul_mem hw₁ (inv_mem hw₂)

variable [Finite Γ]

theorem k618_card_le_two_mul {D H : Subgroup Γ}
    (h : ∀ a ∈ D, ∀ b ∈ D, a ∉ H → b ∉ H → a * b⁻¹ ∈ H) :
    Nat.card D ≤ 2 * Nat.card ↥(D ⊓ H) := by
  by_cases hDH : D ≤ H
  · rw [inf_eq_left.2 hDH]
    omega
  · obtain ⟨d₀, hd₀D, hd₀H⟩ := IsConcreteLE.not_le_iff_exists.1 hDH
    let ψ : ↥(D ⊓ H) ⊕ ↥(D ⊓ H) → D :=
      Sum.elim (fun s => ⟨s, (mem_inf.1 s.2).1⟩)
        (fun s => ⟨(s : Γ) * d₀, mul_mem (mem_inf.1 s.2).1 hd₀D⟩)
    have hψ : Function.Surjective ψ := by
      rintro ⟨d, hd⟩
      by_cases hdH : d ∈ H
      · exact ⟨Sum.inl ⟨d, mem_inf.2 ⟨hd, hdH⟩⟩, rfl⟩
      · exact ⟨Sum.inr ⟨d * d₀⁻¹, mem_inf.2 ⟨mul_mem hd (inv_mem hd₀D), h d hd d₀ hd₀D hdH hd₀H⟩⟩,
          Subtype.ext (inv_mul_cancel_right d d₀)⟩
    calc Nat.card D ≤ Nat.card (↥(D ⊓ H) ⊕ ↥(D ⊓ H)) := Nat.card_le_card_of_surjective ψ hψ
      _ = 2 * Nat.card ↥(D ⊓ H) := by rw [Nat.card_sum]; ring

theorem k618_card_fixSub {x y t : Γ} (hF : IsF20 x y) (htx : t * x = x * t)
    {K W₀ W : Subgroup Γ} (hW₀K : W₀ ≤ K) (hFK : F20 x y ≤ K)
    (hKW : K ≤ normalizer (W : Set Γ)) (hKW₀ : K ≤ normalizer (W₀ : Set Γ))
    (hWab : IsElemAbelian 2 W) (hWcard : Nat.card W = 256)
    (hW₀eq : ∀ w ∈ W₀, ∃ v ∈ W, ∃ e : ℕ, w = v * t ^ e)
    (hKdec : ∀ k ∈ K, ∃ w ∈ W₀, ∃ f ∈ F20 x y, k = w * f) (hFW₀ : F20 x y ⊓ W₀ = ⊥)
    (hfpf : ∀ w ∈ W, x * w * x⁻¹ = w → w = 1) {d : Γ} (hdK : d ∈ K) (hd2 : d * d = 1)
    (hdW₀ : d ∉ W₀) : Nat.card (fixSub (actFun W d)) = 16 := by
  obtain ⟨w, hw, f, hf, hdwf⟩ := hKdec d hdK
  obtain ⟨hf2, hf1⟩ := k618_part_involution hW₀K hKW₀ hFW₀ hdK hd2 hdW₀ hw hf hdwf
  have hfx : f * x * f⁻¹ = x⁻¹ := hF.inv_of_involution hf hf2 hf1
  obtain ⟨v, hv, n, hwv⟩ := hW₀eq w hw
  have hte : t ^ n * x⁻¹ = x⁻¹ * t ^ n :=
    ((Commute.pow_left (show Commute t x from htx) n).inv_right).eq
  have hdx : d * x * d⁻¹ = v * x⁻¹ * v⁻¹ := by
    calc d * x * d⁻¹ = v * t ^ n * (f * x * f⁻¹) * (t ^ n)⁻¹ * v⁻¹ := by rw [hdwf, hwv]; group
      _ = v * (t ^ n * x⁻¹) * (t ^ n)⁻¹ * v⁻¹ := by rw [hfx]; group
      _ = v * x⁻¹ * v⁻¹ := by rw [hte]; group
  have hxN : x ∈ normalizer (W : Set Γ) := hKW (hFK (mem_sup_left (mem_zpowers x)))
  have hdN : d ∈ normalizer (W : Set Γ) := hKW hdK
  have hc : ∀ a b : ↥W, a * b = b * a := fun a b => hWab.1.is_comm.comm a b
  have h2 : ∀ z : ↥W, z * z = 1 := fun z => Subtype.ext (by
    show (z : Γ) * z = 1
    rw [← pow_two]
    exact hWab.2 z z.2)
  have hα : actFun W d * actFun W d = 1 := by
    rw [← actFun_mul W hdN hdN, hd2, actFun_one]
  have hξ : actFun W x ^ 5 = 1 := by
    rw [← actFun_pow W hxN, hF.x5, actFun_one]
  have hfix : ∀ z : ↥W, actFun W x z = z → z = 1 := by
    intro z hz
    apply Subtype.ext
    have h1 := congrArg Subtype.val hz
    rw [actFun_apply_coe W hxN] at h1
    exact hfpf z z.2 h1
  have hinv : actFun W d * actFun W x * (actFun W d)⁻¹ = (actFun W x)⁻¹ := by
    rw [← actFun_conj W hdN hxN, ← actFun_inv W hxN,
      actFun_eq_iff W (mul_mem (mul_mem hdN hxN) (inv_mem hdN)) (inv_mem hxN), hdx]
    have hmem : (v * x⁻¹ * v⁻¹)⁻¹ * x⁻¹ ∈ W := by
      have e' : (v * x⁻¹ * v⁻¹)⁻¹ * x⁻¹ = v * (x * v⁻¹ * x⁻¹) := by group
      rw [e']
      exact mul_mem hv ((mem_normalizer_iff.1 hxN _).1 (inv_mem hv))
    rw [mem_centralizer_iff]
    intro u hu
    exact congrArg Subtype.val (hWab.1.is_comm.comm ⟨u, hu⟩ ⟨_, hmem⟩)
  have hsq := card_fixSub_sq_of_inverts hc h2 hα hξ hfix hinv
  rw [hWcard] at hsq
  have h0 := Nat.zero_le (Nat.card (fixSub (actFun W d)))
  have hle : Nat.card (fixSub (actFun W d)) ≤ 16 := by nlinarith
  have hge : 16 ≤ Nat.card (fixSub (actFun W d)) := by nlinarith
  omega

theorem k618_card_inf_le {x y t : Γ} (hF : IsF20 x y) (ht2 : t * t = 1) (htx : t * x = x * t)
    {K W₀ W U D : Subgroup Γ} (hW₀K : W₀ ≤ K) (hFK : F20 x y ≤ K)
    (hKW : K ≤ normalizer (W : Set Γ)) (hKW₀ : K ≤ normalizer (W₀ : Set Γ))
    (hWab : IsElemAbelian 2 W) (hWcard : Nat.card W = 256)
    (hW₀eq : ∀ w ∈ W₀, ∃ v ∈ W, ∃ e : ℕ, w = v * t ^ e)
    (hKdec : ∀ k ∈ K, ∃ w ∈ W₀, ∃ f ∈ F20 x y, k = w * f) (hFW₀ : F20 x y ⊓ W₀ = ⊥)
    (hfpf : ∀ w ∈ W, x * w * x⁻¹ = w → w = 1)
    (hU : ∀ w ∈ W, t * w * t⁻¹ = w ↔ w ∈ U) (hUcard : Nat.card U = 16)
    (hDK : D ≤ K) (hD : IsElemAbelian 2 D) {d : Γ} (hdD : d ∈ D) (hdW : d ∉ W) :
    Nat.card ↥(D ⊓ W) ≤ 16 := by
  have hcD : ∀ a ∈ D, ∀ b ∈ D, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hD.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  by_cases hdW₀ : d ∈ W₀
  · obtain ⟨v, hv, rfl⟩ := k618_exists_mul_t ht2 hW₀eq hdW₀ hdW
    have hle : D ⊓ W ≤ U := by
      intro u hu
      obtain ⟨huD, huW⟩ := mem_inf.1 hu
      refine (hU u huW).1 ?_
      have h1 : v * t * u = u * (v * t) := hcD _ hdD u huD
      have hvu : u * v = v * u := congrArg Subtype.val (hWab.1.is_comm.comm ⟨u, huW⟩ ⟨v, hv⟩)
      have htu : t * u = u * t := by
        refine mul_left_cancel (a := v) ?_
        calc v * (t * u) = v * t * u := (mul_assoc _ _ _).symm
          _ = u * (v * t) := h1
          _ = u * v * t := (mul_assoc _ _ _).symm
          _ = v * u * t := by rw [hvu]
          _ = v * (u * t) := mul_assoc _ _ _
      rw [htu, mul_inv_cancel_right]
    calc Nat.card ↥(D ⊓ W) ≤ Nat.card U := Subgroup.card_le_of_le hle
      _ = 16 := hUcard
  · have hd2 : d * d = 1 := by rw [← pow_two]; exact hD.2 d hdD
    have hcard := k618_card_fixSub hF htx hW₀K hFK hKW hKW₀ hWab hWcard hW₀eq hKdec hFW₀ hfpf
      (hDK hdD) hd2 hdW₀
    have hdN : d ∈ normalizer (W : Set Γ) := hKW (hDK hdD)
    let g : ↥(D ⊓ W) → ↥(fixSub (actFun W d)) := fun u =>
      ⟨⟨u, (mem_inf.1 u.2).2⟩,
        mem_fixSub.2 ((actFun_fixes_iff W hdN _).2 (hcD d hdD u (mem_inf.1 u.2).1))⟩
    have hg : Function.Injective g := fun a b hab =>
      Subtype.ext (congrArg (fun z : ↥(fixSub (actFun W d)) => ((z : ↥W) : Γ)) hab)
    calc Nat.card ↥(D ⊓ W) ≤ Nat.card ↥(fixSub (actFun W d)) := Nat.card_le_card_of_injective g hg
      _ = 16 := hcard

set_option linter.unusedVariables false

theorem maxElemAbelian2_eq_of_structure {x y t : Γ} (hF : IsF20 x y) (ht2 : t * t = 1)
    (htx : t * x = x * t) (hty : t * y = y * t) {K W₀ W U : Subgroup Γ}
    (hW₀K : W₀ ≤ K) (hFK : F20 x y ≤ K)
    (hKW : K ≤ normalizer (W : Set Γ)) (hKW₀ : K ≤ normalizer (W₀ : Set Γ))
    (hWab : IsElemAbelian 2 W) (hWcard : Nat.card W = 256) (hWW₀ : W ≤ W₀)
    (htW₀ : t ∈ W₀) (htW : t ∉ W) (hW₀eq : ∀ w ∈ W₀, ∃ v ∈ W, ∃ e : ℕ, w = v * t ^ e)
    (hKdec : ∀ k ∈ K, ∃ w ∈ W₀, ∃ f ∈ F20 x y, k = w * f)
    (hFW₀ : F20 x y ⊓ W₀ = ⊥)
    (hfpf : ∀ w ∈ W, x * w * x⁻¹ = w → w = 1)
    (hU : ∀ w ∈ W, t * w * t⁻¹ = w ↔ w ∈ U) (hUcard : Nat.card U = 16) :
    maxElemAbelian2 K = {W} := by
  have hWK : W ≤ K := hWW₀.trans hW₀K
  have hbound : ∀ D : Subgroup Γ, D ≤ K → IsElemAbelian 2 D → ¬ D ≤ W → Nat.card D ≤ 64 := by
    intro D hDK hD hDW
    obtain ⟨d, hdD, hdW⟩ := IsConcreteLE.not_le_iff_exists.1 hDW
    have h1 : Nat.card D ≤ 2 * Nat.card ↥(D ⊓ W₀) := k618_card_le_two_mul
      fun a ha b hb haW₀ hbW₀ => k618_mul_inv_mem_W₀ hF hW₀K hKW₀ hKdec hFW₀ hDK hD ha hb haW₀ hbW₀
    have h2 : Nat.card ↥(D ⊓ W₀) ≤ 2 * Nat.card ↥(D ⊓ W₀ ⊓ W) := k618_card_le_two_mul
      fun a ha b hb haW hbW => k618_mul_inv_mem_W ht2 hW₀eq (mem_inf.1 ha).2 (mem_inf.1 hb).2 haW hbW
    rw [inf_assoc, inf_eq_right.2 hWW₀] at h2
    have h3 := k618_card_inf_le hF ht2 htx hW₀K hFK hKW hKW₀ hWab hWcard hW₀eq hKdec hFW₀ hfpf hU
      hUcard hDK hD hdD hdW
    omega
  ext E
  show (E ≤ K ∧ IsElemAbelian 2 E ∧ ∀ D : Subgroup Γ, D ≤ K → IsElemAbelian 2 D →
    Nat.card D ≤ Nat.card E) ↔ E = W
  constructor
  · rintro ⟨hEK, hE, hmax⟩
    have h256 : 256 ≤ Nat.card E := by rw [← hWcard]; exact hmax W hWK hWab
    have hEW : E ≤ W := by
      by_contra hEW
      have := hbound E hEK hE hEW
      omega
    exact Subgroup.eq_of_le_of_card_ge hEW (by rw [hWcard]; exact h256)
  · intro hEW
    rw [hEW]
    refine ⟨hWK, hWab, fun D hDK hD => ?_⟩
    by_cases hDW : D ≤ W
    · exact Subgroup.card_le_of_le hDW
    · have := hbound D hDK hD hDW
      omega

end CFSG.LocalAnalysis.EvenBN.Tits.N.P5
