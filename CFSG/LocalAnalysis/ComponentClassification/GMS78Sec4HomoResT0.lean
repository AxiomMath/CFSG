module

public import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec4HomoResT0Basic

public section

namespace CFSG.ComponentClassification.GMS78

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.RankTwoStandard
open scoped MatrixGroups

variable {G : Type} [Group G] [Finite G] {L T : Subgroup G} {f : ℕ}

namespace Sec3

theorem false_of_mem_centralizer_rightConjugate
    (h : Sec3 G L T) (hf : 3 ≤ f)
    (e : rankTwoQuot L ≃* PSL(2, GaloisField 2 f)) {q : ℕ} (h313 : Lemma313 L T q) {x y : G}
    (hxT : x ∈ T) (hxV : x ∉ gmsV L T) (hxx : x * x = 1)
    (hxT₀ : T ⊓ centralizer (L : Set G) ≤ centralizer ({x} : Set G))
    (hy : y * x * y⁻¹ ∈ centralizer (L : Set G)) : False := by
  classical
  have hLp := h.hyp.standard.1.1
  have hZ := odd_card_center_of_psl2 hLp hf e
  have hel := isElemAbelian_of_psl2 hZ (by omega) e h.isSylowOf_T₁
  have hA : gmsA L T = T ⊓ L := h.gmsA_eq_of_psl2 hf e
  have hB := (rankTwoBenderType_iff.mp h.hyp.bender).fusionIsBenderGroup
  have hx1 : x ≠ 1 := fun h1 => hxV (h1 ▸ one_mem _)
  have h8 : 8 ≤ Nat.card (T ⊓ L : Subgroup G) := h.eight_le_card_T₁
  obtain ⟨-, -, htight, -, -⟩ := h.hyp.standard
  have hyN : y⁻¹ ∉ normalizer (centralizer (L : Set G) : Set G) := by
    intro hyK
    apply hxV
    have hxK : x ∈ centralizer (L : Set G) := by
      have := (mem_normalizer_iff.mp hyK (y * x * y⁻¹)).mp hy
      rwa [show y⁻¹ * (y * x * y⁻¹) * y⁻¹⁻¹ = x by group] at this
    exact (le_sup_right : T ⊓ centralizer (L : Set G) ≤ gmsV L T) (mem_inf.mpr ⟨hxT, hxK⟩)
  obtain ⟨F, hFT₀, hFel, hF4⟩ := h.exists_four_le
  have ht1 : y * x * y⁻¹ ≠ 1 := fun h1 => hx1 (conj_eq_one_iff.mp h1)
  have htt : y * x * y⁻¹ * (y * x * y⁻¹) = 1 := by
    calc y * x * y⁻¹ * (y * x * y⁻¹) = y * (x * x) * y⁻¹ := by group
      _ = 1 := by rw [hxx]; group
  have hF'N : F.map (MulAut.conj y).toMonoidHom ≤ normalizer (L : Set G) := by
    rintro _ ⟨a, ha, rfl⟩
    refine h.centralizer_le_normalizer_of_mem hy ht1 htt (mem_centralizer_singleton_iff.mpr ?_)
    have hax : a * x = x * a := mem_centralizer_singleton_iff.mp (hxT₀ (hFT₀ ha))
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    calc y * a * y⁻¹ * (y * x * y⁻¹) = y * (a * x) * y⁻¹ := by group
      _ = y * (x * a) * y⁻¹ := by rw [hax]
      _ = y * x * y⁻¹ * (y * a * y⁻¹) := by group
  have h1 := card_le_two_mul_inf hLp hB hF'N (isElemAbelian_map _ hFel)
  rw [card_map_of_injective (MulAut.conj y).injective, hF4] at h1
  obtain ⟨_, ht₁mem, ht₁1⟩ := exists_ne_one_of_two_le_card (H := F.map (MulAut.conj y).toMonoidHom ⊓
    (L ⊔ centralizer (L : Set G))) (by omega)
  obtain ⟨⟨t₁, ht₁F, rfl⟩, ht₁LK⟩ := mem_inf.mp ht₁mem
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at ht₁LK ht₁1
  have ht₁T₀ := hFT₀ ht₁F
  have ht₁K : y * t₁ * y⁻¹ ∉ centralizer (L : Set G) := by
    intro hk
    have hodd := htight y⁻¹ hyN
    set C := centralizer (L : Set G)
    have htC : t₁ ∈ C ⊓ C.map (MulAut.conj y⁻¹).toMonoidHom := by
      refine mem_inf.mpr ⟨(mem_inf.mp ht₁T₀).2, mem_map.mpr ⟨y * t₁ * y⁻¹, hk, ?_⟩⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    have ht₁1' : t₁ ≠ 1 := fun h0 => ht₁1 (by rw [h0]; group)
    have h2 : orderOf (⟨t₁, htC⟩ : (C ⊓ C.map (MulAut.conj y⁻¹).toMonoidHom : Subgroup G)) = 2 := by
      refine orderOf_eq_prime ?_ (fun h0 => ht₁1' (congrArg Subtype.val h0))
      apply Subtype.ext
      simp only [SubgroupClass.coe_pow, OneMemClass.coe_one]
      exact hFel.2 t₁ ht₁F
    have h3 := orderOf_dvd_natCard
      (⟨t₁, htC⟩ : (C ⊓ C.map (MulAut.conj y⁻¹).toMonoidHom : Subgroup G))
    rw [h2] at h3
    exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h3)
  obtain ⟨k, hk, l, hl, hkl⟩ := CFSG.Goldschmidt.G37.mem_sup_of_le_normalizer
    h.centralizer_le_normalizer (by rw [sup_comm]; exact ht₁LK)
  have hlK : l ∉ centralizer (L : Set G) := fun hlK => ht₁K (hkl ▸ mul_mem hk hlK)
  have hkl' : l * k = k * l := mem_centralizer_iff.mp hk l hl
  have hll : l * l ∈ centralizer (L : Set G) := by
    have hsq : y * t₁ * y⁻¹ * (y * t₁ * y⁻¹) = 1 := by
      have : t₁ * t₁ = 1 := by rw [← sq]; exact hFel.2 t₁ ht₁F
      calc y * t₁ * y⁻¹ * (y * t₁ * y⁻¹) = y * (t₁ * t₁) * y⁻¹ := by group
        _ = 1 := by rw [this]; group
    rw [← hkl] at hsq
    have h4 : l * l = (k * k)⁻¹ := by
      apply eq_inv_of_mul_eq_one_left
      calc l * l * (k * k) = l * (l * k) * k := by group
        _ = l * (k * l) * k := by rw [hkl']
        _ = (l * k) * (l * k) := by group
        _ = (k * l) * (k * l) := by rw [hkl']
        _ = 1 := hsq
    rw [h4]
    exact inv_mem (mul_mem hk hk)
  have hxA₁ : ∀ a ∈ T ⊓ L, x * a * x⁻¹ ∈ T ⊓ L := fun a ha =>
    (mem_normalizer_iff.mp (h.mem_normalizer_T₁ hxT) a).mp ha
  have hE := card_le_card_inf_centralizer_sq hel hxx hxA₁
  have hP3 := h.card_le_two_mul_inf_rightConjugate hf e h313 hy hx1 hxx
    (E := gmsA L T ⊓ centralizer ({x} : Set G)) inf_le_left inf_le_right
  rw [hA] at hP3
  have hE3 : 3 ≤ Nat.card (T ⊓ L ⊓ centralizer ({x} : Set G) : Subgroup G) := by
    by_contra hlt
    push Not at hlt
    have : Nat.card (T ⊓ L ⊓ centralizer ({x} : Set G) : Subgroup G) ^ 2 ≤ 4 := by
      have h5 : Nat.card (T ⊓ L ⊓ centralizer ({x} : Set G) : Subgroup G) ≤ 2 := by omega
      calc _ ≤ 2 ^ 2 := Nat.pow_le_pow_left h5 2
        _ = 4 := by norm_num
    omega
  obtain ⟨c₁, hc₁mem, hc₁1⟩ := exists_ne_one_of_two_le_card
    (H := T ⊓ L ⊓ centralizer ({x} : Set G) ⊓ rightConjugate L y) (by omega)
  obtain ⟨⟨hc₁A, -⟩, hc₁y⟩ := mem_inf.mp hc₁mem
  obtain ⟨l₁, hl₁, hxA', hnc⟩ := h.exists_second_sylow hf e hxT hxV hxx
  set A' := (T ⊓ L).map (MulAut.conj l₁).toMonoidHom with hA'
  have hA'el : IsElemAbelian 2 A' := isElemAbelian_map _ hel
  have hxA'' : ∀ b ∈ A', x * b * x⁻¹ ∈ A' := by
    rintro _ ⟨a, ha, rfl⟩
    simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using hxA' a ha
  have hE' := card_le_card_inf_centralizer_sq hA'el hxx hxA''
  have hA'card : Nat.card A' = Nat.card (T ⊓ L : Subgroup G) :=
    card_map_of_injective (MulAut.conj l₁).injective
  have hroot : ∀ b ∈ A' ⊓ centralizer ({x} : Set G), ∃ g : G, g * b * g⁻¹ ∈ gmsA L T := by
    rintro _ ⟨⟨a, ha, rfl⟩, -⟩
    refine ⟨l₁⁻¹, ?_⟩
    rw [hA]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [show l₁⁻¹ * (l₁ * a * l₁⁻¹) * l₁⁻¹⁻¹ = a by group]
    exact ha
  have hP3' := h.card_le_two_mul_inf_rightConjugate_of_conj hf e h313 hy hx1 hxx
    (isElemAbelian_of_le hA'el inf_le_left) hroot inf_le_right
  have hE'3 : 3 ≤ Nat.card (A' ⊓ centralizer ({x} : Set G) : Subgroup G) := by
    by_contra hlt
    push Not at hlt
    have : Nat.card (A' ⊓ centralizer ({x} : Set G) : Subgroup G) ^ 2 ≤ 4 := by
      have h5 : Nat.card (A' ⊓ centralizer ({x} : Set G) : Subgroup G) ≤ 2 := by omega
      calc _ ≤ 2 ^ 2 := Nat.pow_le_pow_left h5 2
        _ = 4 := by norm_num
    omega
  obtain ⟨c₂, hc₂mem, hc₂1⟩ := exists_ne_one_of_two_le_card (H := A' ⊓ centralizer ({x} : Set G) ⊓
    rightConjugate L y) (by omega)
  obtain ⟨⟨⟨b, hb, rfl⟩, -⟩, hc₂y⟩ := mem_inf.mp hc₂mem
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hc₂y hc₂1
  have hb1 : b ≠ 1 := fun h0 => hc₂1 (by rw [h0]; group)
  have hnc' := hnc c₁ hc₁A b hb hc₁1 hb1
  rw [mem_rightConjugate_iff] at hc₁y hc₂y
  have hc₁L : c₁ ∈ L := (mem_inf.mp hc₁A).2
  have hc₂L : l₁ * b * l₁⁻¹ ∈ L := mul_mem (mul_mem hl₁ (mem_inf.mp hb).2) (inv_mem hl₁)
  have hcomm_l : ∀ c ∈ L, y * c * y⁻¹ ∈ L → l * (y * c * y⁻¹) = (y * c * y⁻¹) * l := by
    intro c hc hcy
    have ht₁c : t₁ * c = c * t₁ := (mem_centralizer_iff.mp (mem_inf.mp ht₁T₀).2 c hc).symm
    have hkc : (y * c * y⁻¹) * k = k * (y * c * y⁻¹) := mem_centralizer_iff.mp hk _ hcy
    have h6 : (k * l) * (y * c * y⁻¹) = (y * c * y⁻¹) * (k * l) := by
      rw [hkl]
      calc y * t₁ * y⁻¹ * (y * c * y⁻¹) = y * (t₁ * c) * y⁻¹ := by group
        _ = y * (c * t₁) * y⁻¹ := by rw [ht₁c]
        _ = y * c * y⁻¹ * (y * t₁ * y⁻¹) := by group
    calc l * (y * c * y⁻¹) = k⁻¹ * ((k * l) * (y * c * y⁻¹)) := by group
      _ = k⁻¹ * ((y * c * y⁻¹) * (k * l)) := by rw [h6]
      _ = k⁻¹ * ((y * c * y⁻¹) * k) * l := by group
      _ = k⁻¹ * (k * (y * c * y⁻¹)) * l := by rw [hkc]
      _ = (y * c * y⁻¹) * l := by group
  have hinv : ∀ {c : G}, c * c = 1 → y * c * y⁻¹ * (y * c * y⁻¹) = 1 := fun {c} hc => by
    calc y * c * y⁻¹ * (y * c * y⁻¹) = y * (c * c) * y⁻¹ := by group
      _ = 1 := by rw [hc]; group
  have hc₁c₁ : c₁ * c₁ = 1 := by rw [← sq]; exact hel.2 c₁ hc₁A
  have hc₂c₂ : l₁ * b * l₁⁻¹ * (l₁ * b * l₁⁻¹) = 1 := by
    have : b * b = 1 := by rw [← sq]; exact hel.2 b hb
    calc l₁ * b * l₁⁻¹ * (l₁ * b * l₁⁻¹) = l₁ * (b * b) * l₁⁻¹ := by group
      _ = 1 := by rw [this]; group
  have hcomm := h.commute_of_commute hf e hl hlK hll hc₁y hc₂y (hinv hc₁c₁) (hinv hc₂c₂)
    (hcomm_l c₁ hc₁L hc₁y) (hcomm_l _ hc₂L hc₂y)
  apply hnc'
  calc c₁ * (l₁ * b * l₁⁻¹) =
        y⁻¹ * ((y * c₁ * y⁻¹) * (y * (l₁ * b * l₁⁻¹) * y⁻¹)) * y := by group
    _ = y⁻¹ * ((y * (l₁ * b * l₁⁻¹) * y⁻¹) * (y * c₁ * y⁻¹)) * y := by rw [hcomm]
    _ = l₁ * b * l₁⁻¹ * c₁ := by group

end Sec3

theorem gms42ResidualT0 :
    GMS42ResidualT0 := by
  intro G _ _ L T U₁ h _ he _ h313 _ _ _ U g _ _ _ _ u _ _ t₀ _ _ _ _ w _ _ _ _ hww _ _ c _ x hcx
    hxT hxV _ hxT₀ y hy _
  obtain ⟨e⟩ := he
  have hxx : x * x = 1 := by
    rw [← hcx]
    calc c * w * c⁻¹ * (c * w * c⁻¹) = c * (w * w) * c⁻¹ := by group
      _ = 1 := by rw [hww]; group
  exact h.false_of_mem_centralizer_rightConjugate (by norm_num) e h313 hxT hxV hxx hxT₀
    (mem_inf.mp hy).2

end CFSG.ComponentClassification.GMS78
