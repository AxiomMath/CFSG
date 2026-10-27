module

public import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec4ElemOut
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherGoldschmidtFour
public import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec4ElemFusion

public section

namespace CFSG.ComponentClassification.GMS78

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.RankTwoStandard
open scoped MatrixGroups

variable {G : Type} [Group G] [Finite G]

namespace Sec4Elem

variable {L T U₁ : Subgroup G} {f : ℕ}

omit [Finite G] in
theorem inf_W_le (hE : Sec4Elem L T U₁ (2 ^ f)) (h313 : Lemma313 L T (2 ^ f))
    (hT₀ : IsElemAbelian 2 (T ⊓ centralizer (L : Set G)))
    (hnf : ∀ t ∈ T ⊓ centralizer (L : Set G), t ≠ 1 → ∀ g : G, g * t * g⁻¹ ∉ U₁)
    {U : Subgroup G} (hU : U ≤ U₁) (g : G) :
    rightConjugate U g ⊓ (U₁ ⊔ (T ⊓ centralizer (L : Set G))) ≤ U₁ := by
  intro x hx
  obtain ⟨hxU, hxW⟩ := mem_inf.mp hx
  rw [mem_rightConjugate_iff] at hxU
  have h1 := hE.conj_mem_of_mem_W h313 hT₀ hnf (hU hxU) (g := g⁻¹)
    (by simpa [mul_assoc] using hxW)
  simpa [mul_assoc] using h1

theorem rightConjugate_eq
    (hE : Sec4Elem L T U₁ (2 ^ f))
    (h : Sec3 G L T) (hF : Foundation) (hf : 3 ≤ f) (e : rankTwoQuot L ≃* PSL(2, GaloisField 2 f))
    (hX : Sec3.Facts L T (2 ^ f)) (h313 : Lemma313 L T (2 ^ f))
    (hnf : ∀ t ∈ T ⊓ centralizer (L : Set G), t ≠ 1 → ∀ g : G, g * t * g⁻¹ ∉ U₁) {g : G}
    (hg : rightConjugate U₁ g ≤ U₁ ⊔ T) : rightConjugate U₁ g = U₁ := by
  have hT₀ := h.isElemAbelian_T₀ hF
  set E := rightConjugate U₁ g with hEdef
  have hEel : IsElemAbelian 2 E := isElemAbelian_map _ hE.elem
  have hE2 : ∀ x ∈ E, x * x = 1 := fun x hx => by rw [← sq]; exact hEel.2 x hx
  have hEW := hE.inf_W_le h313 hT₀ hnf le_rfl g
  by_cases hEWle : E ≤ U₁ ⊔ (T ⊓ centralizer (L : Set G))
  · have hEU : E ≤ U₁ := fun x hx => hEW (mem_inf.mpr ⟨hx, hEWle hx⟩)
    exact Subgroup.eq_of_le_of_card_ge hEU (by rw [hEdef, rightConjugate_card])
  · exfalso
    obtain ⟨x, hxE, hxW⟩ := IsConcreteLE.not_le_iff_exists.mp hEWle
    have hcard := hE.card_le_two_mul h hf e hg hE2
    have hDC : E ⊓ (U₁ ⊔ (T ⊓ centralizer (L : Set G))) ≤ centralizer ({x} : Set G) :=
      fun y hy => mem_centralizer_singleton_iff.mpr (congrArg Subtype.val
        (hEel.1.is_comm.comm ⟨y, (mem_inf.mp hy).1⟩ ⟨x, hxE⟩))
    have hlt := hE.two_mul_card_lt h hf e hX (hg hxE) (hE2 x hxE) hxW hEW hDC
    rw [hEdef, rightConjugate_card, hE.card] at hcard
    omega

theorem mem_normalizer_W (hE : Sec4Elem L T U₁ (2 ^ f))
    (h : Sec3 G L T) (hf : 3 ≤ f) (e : rankTwoQuot L ≃* PSL(2, GaloisField 2 f)) {a : G}
    (haS : a ∈ normalizer ((U₁ ⊔ T : Subgroup G) : Set G))
    (haA : ∀ b ∈ gmsA L T, a * b * a⁻¹ ∈ gmsA L T)
    (haA' : ∀ b ∈ gmsA L T, a⁻¹ * b * a ∈ gmsA L T) :
    a ∈ normalizer ((U₁ ⊔ (T ⊓ centralizer (L : Set G)) : Subgroup G) : Set G) := by
  have hWS : U₁ ⊔ (T ⊓ centralizer (L : Set G)) ≤ U₁ ⊔ T := sup_le_sup_left inf_le_left _
  have hWA : ∀ x ∈ U₁ ⊔ (T ⊓ centralizer (L : Set G)), ∀ b ∈ gmsA L T, x * b = b * x := by
    intro x hx b hb
    obtain ⟨u, hu, t, ht, rfl⟩ := hE.exists_mul_eq hx
    have h1 : u * b = b * u := hE.comm hu (hE.A_le hb)
    have h2 : t * b = b * t :=
      (mem_centralizer_iff.mp (mem_inf.mp ht).2 b (mem_inf.mp (mem_inf.mp hb).1).2).symm
    rw [mul_assoc, h2, ← mul_assoc, h1, mul_assoc]
  have key : ∀ c : G, c ∈ normalizer ((U₁ ⊔ T : Subgroup G) : Set G) →
      (∀ b ∈ gmsA L T, c⁻¹ * b * c ∈ gmsA L T) →
      ∀ x ∈ U₁ ⊔ (T ⊓ centralizer (L : Set G)),
        c * x * c⁻¹ ∈ U₁ ⊔ (T ⊓ centralizer (L : Set G)) := by
    intro c hc hcA x hx
    refine hE.mem_W_of_commute h hf e ((mem_normalizer_iff.mp hc x).mp (hWS hx)) fun b hb => ?_
    have h1 := hWA x hx _ (hcA b hb)
    calc c * x * c⁻¹ * b = c * (x * (c⁻¹ * b * c)) * c⁻¹ := by group
      _ = c * ((c⁻¹ * b * c) * x) * c⁻¹ := by rw [h1]
      _ = b * (c * x * c⁻¹) := by group
  exact mem_normalizer_of_conj_mem (key a haS haA')
    (fun x hx => by simpa using key a⁻¹ (inv_mem haS) (by simpa using haA) x hx)

theorem inf_normalizer_le
    (hE : Sec4Elem L T U₁ (2 ^ f)) (h : Sec3 G L T) (hF : Foundation) (hf : 3 ≤ f)
    (e : rankTwoQuot L ≃* PSL(2, GaloisField 2 f)) (h313 : Lemma313 L T (2 ^ f))
    (hnf : ∀ t ∈ T ⊓ centralizer (L : Set G), t ≠ 1 → ∀ g : G, g * t * g⁻¹ ∉ U₁)
    {S : Subgroup G} (hS : IsPGroup 2 S) (hS₀S : U₁ ⊔ T ≤ S) :
    S ⊓ normalizer (U₁ : Set G) ≤ U₁ ⊔ T := by
  have hT₀ := h.isElemAbelian_T₀ hF
  have hT₀1 := h.T₀_ne_bot
  by_contra hne
  obtain ⟨a, haS₁, haN, haS₀⟩ := exists_mem_normalizer_of_lt (hS.to_le inf_le_left)
    (le_inf hS₀S hE.S₀_le_normalizer) hne
  obtain ⟨haS, haU⟩ := mem_inf.mp haS₁
  set W := U₁ ⊔ (T ⊓ centralizer (L : Set G)) with hWdef
  have hT₀S : ∀ t ∈ T ⊓ centralizer (L : Set G), a * t * a⁻¹ ∈ U₁ ⊔ T := fun t ht =>
    (mem_normalizer_iff.mp haN t).mp (mem_sup_right (mem_inf.mp ht).1)
  by_cases hmeet : ∃ t ∈ T ⊓ centralizer (L : Set G), t ≠ 1 ∧ a * t * a⁻¹ ∈ W
  · obtain ⟨t, ht, ht1, htW⟩ := hmeet
    have htt : t * t = 1 := by rw [← sq]; exact hT₀.2 t ht
    have htU : a * t * a⁻¹ ∉ U₁ := by
      intro h1
      have h2 : t ∈ (T ⊓ centralizer (L : Set G)) ⊓ U₁ := by
        refine mem_inf.mpr ⟨ht, ?_⟩
        have := (mem_normalizer_iff.mp (inv_mem haU) _).mp h1
        simpa [mul_assoc] using this
      rw [hE.inf_eq_bot, mem_bot] at h2
      exact ht1 h2
    have hsq : a * t * a⁻¹ * (a * t * a⁻¹) = 1 := by
      calc a * t * a⁻¹ * (a * t * a⁻¹) = a * (t * t) * a⁻¹ := by group
        _ = 1 := by rw [htt]; group
    have htV := (hE.mem_or_mem hT₀ htW hsq).resolve_left htU
    have htA : a * t * a⁻¹ ∉ gmsA L T := fun h1 => htU (hE.A_le h1)
    have hC := hE.centralizer_eq_of_mem_V htV htA
    have hC0 := hE.centralizer_eq t ht ht1
    have haA : ∀ b ∈ gmsA L T, a * b * a⁻¹ ∈ gmsA L T := by
      intro b hb
      rw [← hC0] at hb
      obtain ⟨hbU, hbC⟩ := mem_inf.mp hb
      rw [← hC]
      refine mem_inf.mpr ⟨(mem_normalizer_iff.mp haU b).mp hbU,
        mem_centralizer_singleton_iff.mpr ?_⟩
      have h1 : b * t = t * b := mem_centralizer_singleton_iff.mp hbC
      calc a * b * a⁻¹ * (a * t * a⁻¹) = a * (b * t) * a⁻¹ := by group
        _ = a * (t * b) * a⁻¹ := by rw [h1]
        _ = a * t * a⁻¹ * (a * b * a⁻¹) := by group
    have haA' : ∀ b ∈ gmsA L T, a⁻¹ * b * a ∈ gmsA L T := by
      intro b hb
      rw [← hC] at hb
      obtain ⟨hbU, hbC⟩ := mem_inf.mp hb
      rw [← hC0]
      refine mem_inf.mpr ⟨by simpa using (mem_normalizer_iff.mp (inv_mem haU) b).mp hbU,
        mem_centralizer_singleton_iff.mpr ?_⟩
      have h1 : b * (a * t * a⁻¹) = a * t * a⁻¹ * b := mem_centralizer_singleton_iff.mp hbC
      calc a⁻¹ * b * a * t = a⁻¹ * (b * (a * t * a⁻¹)) * a := by group
        _ = a⁻¹ * (a * t * a⁻¹ * b) * a := by rw [h1]
        _ = t * (a⁻¹ * b * a) := by group
    have haW := hE.mem_normalizer_W h hf e haN haA haA'
    exact haS₀ (hE.mem_of_mem_normalizer_W h313 hT₀ hT₀1 hnf hS hS₀S haS haW)
  · push Not at hmeet
    set E := (T ⊓ centralizer (L : Set G)).map (MulAut.conj a).toMonoidHom with hEdef
    have hES : E ≤ U₁ ⊔ T := by
      rintro _ ⟨t, ht, rfl⟩
      exact hT₀S t ht
    have hE2 : ∀ x ∈ E, x * x = 1 := by
      rintro _ ⟨t, ht, rfl⟩
      have htt : t * t = 1 := by rw [← sq]; exact hT₀.2 t ht
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      calc a * t * a⁻¹ * (a * t * a⁻¹) = a * (t * t) * a⁻¹ := by group
        _ = 1 := by rw [htt]; group
    have hEW : E ⊓ W = ⊥ := by
      rw [eq_bot_iff]
      rintro _ hx
      obtain ⟨⟨t, ht, rfl⟩, hxW⟩ := mem_inf.mp hx
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hxW ⊢
      by_contra h1
      have ht1 : t ≠ 1 := by
        rintro rfl
        exact h1 (by simp)
      exact hmeet t ht ht1 hxW
    have hcard := hE.card_le_two_mul h hf e hES hE2
    rw [hEdef, card_map_of_injective (MulAut.conj a).injective] at hcard
    rw [← hEdef, hEW, card_bot] at hcard
    obtain ⟨F, hF4, -, hF4c⟩ := h.exists_four_le
    have := card_le_of_le hF4
    omega

theorem isSylowOf_top
    (hE : Sec4Elem L T U₁ (2 ^ f)) (h : Sec3 G L T) (hF : Foundation) (hf : 3 ≤ f)
    (e : rankTwoQuot L ≃* PSL(2, GaloisField 2 f)) (hX : Sec3.Facts L T (2 ^ f))
    (h313 : Lemma313 L T (2 ^ f))
    (hnf : ∀ t ∈ T ⊓ centralizer (L : Set G), t ≠ 1 → ∀ g : G, g * t * g⁻¹ ∉ U₁) :
    IsSylowOf 2 (U₁ ⊔ T) ⊤ := by
  by_contra hns
  obtain ⟨S, hS₀S, z, hzS, hzN, hzS₀⟩ :=
    exists_mem_normalizer_of_not_isSylowOf hE.sylow.isPGroup hns
  have hle : rightConjugate U₁ z⁻¹ ≤ U₁ ⊔ T := by
    intro x hx
    rw [mem_rightConjugate_iff] at hx
    have h1 := (mem_normalizer_iff.mp hzN _).mp (mem_sup_left hx)
    simpa [mul_assoc] using h1
  have hzU : z ∈ normalizer (U₁ : Set G) := by
    have h1 := (rightConjugate_eq_self_iff _ _).mp (hE.rightConjugate_eq h hF hf e hX h313 hnf hle)
    simpa using inv_mem h1
  exact hzS₀ (hE.inf_normalizer_le h hF hf e h313 hnf S.isPGroup' hS₀S (mem_inf.mpr ⟨hzS, hzU⟩))

theorem false_of_noFusion
    (hE : Sec4Elem L T U₁ (2 ^ f)) (h : Sec3 G L T) (hF : Foundation) (hf : 3 ≤ f)
    (e : rankTwoQuot L ≃* PSL(2, GaloisField 2 f)) (hX : Sec3.Facts L T (2 ^ f))
    (h313 : Lemma313 L T (2 ^ f))
    (hnf : ∀ t ∈ T ⊓ centralizer (L : Set G), t ≠ 1 → ∀ g : G, g * t * g⁻¹ ∉ U₁) : False := by
  have hT₀ := h.isElemAbelian_T₀ hF
  have hsyl := hE.isSylowOf_top h hF hf e hX h313 hnf
  obtain ⟨-, hS₀p, hS₀idx⟩ := isSylowOf_iff.mp hsyl
  rw [relIndex_top_right] at hS₀idx
  let S : Sylow 2 G := hS₀p.toSylow hS₀idx
  have hSc : (S : Subgroup G) = U₁ ⊔ T := IsPGroup.toSylow_coe hS₀p hS₀idx
  have hU₁S : U₁ ≤ S := hSc ▸ le_sup_left
  have hU₁ne : U₁ ≠ ⊥ := by
    intro hb
    have := hE.card
    rw [hb, card_bot] at this
    have : 1 < (2 ^ f) ^ 2 := Nat.one_lt_pow (by norm_num) (Nat.one_lt_two_pow (by omega))
    omega
  have hwc : ∀ g : G, rightConjugate U₁ g ≤ S → rightConjugate U₁ g = U₁ := fun g hg =>
    hE.rightConjugate_eq h hF hf e hX h313 hnf (hSc ▸ hg)
  by_cases hsc : ∃ v ∈ U₁, ∃ g : G, g⁻¹ * v * g ∈ (S : Subgroup G) ∧ g⁻¹ * v * g ∉ U₁
  · obtain ⟨U, hUU₁, g, hUg, hUgU₁, hbound⟩ :=
      GoldschmidtFour.goldschmidt_theorem_four_holds G S U₁ hU₁S hE.elem hwc hsc
    set U' := rightConjugate U g with hU'def
    have hU'S : U' ≤ U₁ ⊔ T := hSc ▸ hUg
    have hU'el : IsElemAbelian 2 U' := isElemAbelian_map _ (isElemAbelian_of_le hE.elem hUU₁)
    have hU'2 : ∀ x ∈ U', x * x = 1 := fun x hx => by rw [← sq]; exact hU'el.2 x hx
    have hU'W := hE.inf_W_le h313 hT₀ hnf hUU₁ g
    have hU'Wle : ¬ U' ≤ U₁ ⊔ (T ⊓ centralizer (L : Set G)) := fun h1 =>
      hUgU₁ fun x hx => hU'W (mem_inf.mpr ⟨hx, h1 hx⟩)
    obtain ⟨w, hwU', hwW⟩ := IsConcreteLE.not_le_iff_exists.mp hU'Wle
    have hcard := hE.card_le_two_mul h hf e hU'S hU'2
    have hinf : U₁ ⊓ U' = U' ⊓ (U₁ ⊔ (T ⊓ centralizer (L : Set G))) := by
      apply le_antisymm
      · exact le_inf inf_le_right (inf_le_left.trans le_sup_left)
      · exact le_inf (hU'W) inf_le_left
    have hidx := relIndex_mul_card U₁ U'
    rw [hinf] at hidx
    have hpos : 0 < Nat.card (U' ⊓ (U₁ ⊔ (T ⊓ centralizer (L : Set G))) : Subgroup G) :=
      Nat.card_pos
    have hidx2 : U₁.relIndex U' ≤ 2 := by nlinarith
    have hb := hbound w hwU'
    have hwN : w ∈ normalizer (U₁ : Set G) := hE.S₀_le_normalizer (hU'S hwU')
    have hc := card_le_card_inf_centralizer_mul hE.elem.1 hwN
    have hlt := hE.two_mul_card_lt h hf e hX (hU'S hwU') (hU'2 w hwU') hwW
      (inf_le_left : U₁ ⊓ centralizer ({w} : Set G) ≤ U₁) inf_le_right
    rw [hE.card] at hc
    have : (2 ^ f) ^ 2 ≤ Nat.card (U₁ ⊓ centralizer ({w} : Set G) : Subgroup G) * 2 :=
      hc.trans (Nat.mul_le_mul_left _ (hb.trans hidx2))
    omega
  · push Not at hsc
    exact h.hyp.lemma34 S hU₁S hE.elem.1 hU₁ne hsc

theorem false_of_lt
    (hE : Sec4Elem L T U₁ (2 ^ f)) (h : Sec3 G L T) (hF : Foundation) (hf : 3 ≤ f)
    (e : rankTwoQuot L ≃* PSL(2, GaloisField 2 f)) (hX : Sec3.Facts L T (2 ^ f))
    (h313 : Lemma313 L T (2 ^ f))
    (hlt : Nat.card (T ⊓ centralizer (L : Set G) : Subgroup G) < 2 ^ f) : False :=
  hE.false_of_noFusion h hF hf e hX h313 fun _ ht ht1 g => hE.conj_not_mem h hF hf e hX hlt ht ht1 g

end Sec4Elem

end CFSG.ComponentClassification.GMS78
