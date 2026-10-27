module

public import CFSG.LocalAnalysis.GH72.Sec4Basic

public section

namespace CFSG.GH72

open Subgroup CFSG.ABGLocalTools

namespace Sec7

variable {G : Type*} [Group G]

theorem IsDih.exists_mul {D : Subgroup G} (hD : IsDih D) {d : G} (hd : d ∈ D) :
    ∃ a ∈ D, ∃ b ∈ D, a * a = 1 ∧ b * b = 1 ∧ d = a * b := by
  obtain ⟨k, -, ⟨e⟩⟩ := hD
  have hsq : ∀ u : DihedralGroup (2 ^ k), u * u = 1 →
      ((e.symm u : D) : G) * (e.symm u : D) = 1 := by
    intro u hu
    rw [← Subgroup.coe_mul, ← map_mul, hu, map_one, Subgroup.coe_one]
  cases h : e ⟨d, hd⟩ with
  | r i =>
    refine ⟨(e.symm (DihedralGroup.sr 0) : D), (e.symm _).2, (e.symm (DihedralGroup.sr i) : D),
      (e.symm _).2, hsq _ (DihedralGroup.sr_mul_self 0), hsq _ (DihedralGroup.sr_mul_self i), ?_⟩
    rw [← Subgroup.coe_mul, ← map_mul, DihedralGroup.sr_mul_sr, sub_zero, ← h,
      MulEquiv.symm_apply_apply]
  | sr i =>
    refine ⟨d, hd, 1, one_mem _, ?_, mul_one 1, (mul_one d).symm⟩
    have h1 := hsq _ (DihedralGroup.sr_mul_self i)
    rwa [← h, MulEquiv.symm_apply_apply] at h1

theorem IsDih.exists_four_le [Finite G] {D T : Subgroup G} (hD : IsDih D) (hTD : T ≤ D)
    (hT : T ≠ ⊥) :
    ∃ T' V : Subgroup G, T' ≤ T ∧ T' ≠ ⊥ ∧ normalizer (T : Set G) ≤ normalizer (T' : Set G) ∧
      CFSG.CGT.Foote81L6.TStruct.IsFourIn D V ∧ T' ≤ V := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let T' : Subgroup G :=
    { carrier := {x | x ∈ T ∧ (∀ y ∈ T, x * y = y * x) ∧ x * x = 1}
      mul_mem' := by
        rintro a b ⟨haT, hac, ha2⟩ ⟨hbT, hbc, hb2⟩
        refine ⟨mul_mem haT hbT, fun y hy => ?_, ?_⟩
        · rw [mul_assoc, hbc y hy, ← mul_assoc, hac y hy, mul_assoc]
        · calc a * b * (a * b) = a * (b * a) * b := by group
            _ = a * (a * b) * b := by rw [(hac b hbT).symm]
            _ = (a * a) * (b * b) := by group
            _ = 1 := by rw [ha2, hb2, one_mul]
      one_mem' := ⟨one_mem T, fun y _ => by group, mul_one 1⟩
      inv_mem' := by
        rintro a ⟨haT, hac, ha2⟩
        rw [inv_eq_of_mul_eq_one_right ha2]
        exact ⟨haT, hac, ha2⟩ }
  have hT'T : T' ≤ T := fun x hx => hx.1
  have hT'2 : ∀ x ∈ T', x * x = 1 := fun x hx => hx.2.2
  have hT2 : IsPGroup 2 T := hD.isPGroup.to_le hTD
  have : Nontrivial T := (Subgroup.nontrivial_iff_ne_bot T).mpr hT
  have hZ : Nontrivial (center T) := hT2.center_nontrivial
  have h2Z : 2 ∣ Nat.card (center T) := by
    rcases (hT2.to_subgroup (center T)).card_eq_or_dvd with h | h
    · exact absurd (Subgroup.card_eq_one.1 h) ((Subgroup.nontrivial_iff_ne_bot _).mp hZ)
    · exact h
  obtain ⟨⟨z, hz⟩, hzo⟩ := exists_prime_orderOf_dvd_card' (G := center T) 2 h2Z
  have hzo' : orderOf (z : G) = 2 := by
    rw [Subgroup.orderOf_mk] at hzo
    rwa [Subgroup.orderOf_coe]
  have hzT' : (z : G) ∈ T' := by
    refine ⟨z.2, fun y hy => ?_, ?_⟩
    · exact congrArg Subtype.val ((mem_center_iff.mp hz ⟨y, hy⟩).symm)
    · rw [← pow_two, ← hzo', pow_orderOf_eq_one]
  have hz1 : (z : G) ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hzo'
    exact absurd hzo' (by norm_num)
  have hT'ne : T' ≠ ⊥ := fun h => hz1 ((Subgroup.eq_bot_iff_forall _).mp h _ hzT')
  have hN : normalizer (T : Set G) ≤ normalizer (T' : Set G) := by
    intro g hg
    refine Subgroup.mem_normalizer_fintype fun x hx => ⟨?_, fun y hy => ?_, ?_⟩
    · exact (mem_normalizer_iff.mp hg x).mp hx.1
    · have hy' : g⁻¹ * y * g ∈ T := (mem_normalizer_iff''.mp hg y).mp hy
      have hc := hx.2.1 _ hy'
      calc g * x * g⁻¹ * y = g * (x * (g⁻¹ * y * g)) * g⁻¹ := by group
        _ = g * ((g⁻¹ * y * g) * x) * g⁻¹ := by rw [hc]
        _ = y * (g * x * g⁻¹) := by group
    · calc g * x * g⁻¹ * (g * x * g⁻¹) = g * (x * x) * g⁻¹ := by group
        _ = 1 := by rw [hx.2.2, mul_one, mul_inv_cancel]
  have hT'D : T' ≤ D := hT'T.trans hTD
  have hcard4 : Nat.card T' ≤ 4 := hD.elemBound T' hT'D hT'2
  obtain ⟨n, hn⟩ := (hT2.to_le hT'T).exists_card_eq
  have hn1 : n ≠ 0 := by
    rintro rfl
    exact hT'ne (Subgroup.card_eq_one.1 (by rw [hn, pow_zero]))
  have hn2 : n ≤ 2 := by
    by_contra h
    have : 2 ^ 3 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  refine ⟨T', ?_⟩
  rcases (show n = 1 ∨ n = 2 by omega) with rfl | rfl
  · obtain ⟨V, hV, hzV⟩ := hD.exists_four_mem (hT'D hzT') (hT'2 _ hzT')
    refine ⟨V, hT'T, hT'ne, hN, hV, ?_⟩
    have hzp : zpowers (z : G) = T' := by
      refine Subgroup.eq_of_le_of_card_ge ((zpowers_le).mpr hzT') ?_
      rw [hn, Nat.card_zpowers, hzo', pow_one]
    rw [← hzp, zpowers_le]
    exact hzV
  · exact ⟨T', hT'T, hT'ne, hN, ⟨hT'D, hT'2, by rw [hn]; norm_num⟩, le_rfl⟩

end Sec7

namespace Sec4Setting

variable {G : Type} [Group G] [Finite G] (𝔖 : Sec4Setting G)

theorem isDih_factor {P : Subgroup G} (hP : P = 𝔖.S₁ ∨ P = 𝔖.S₂) : IsDih P := by
  rcases hP with rfl | rfl
  exacts [𝔖.decomp.dih₁, 𝔖.decomp.isDih₂]

theorem factor_le_S {P : Subgroup G} (hP : P = 𝔖.S₁ ∨ P = 𝔖.S₂) : P ≤ (𝔖.S : Subgroup G) := by
  rcases hP with rfl | rfl
  exacts [𝔖.decomp.le_left, 𝔖.decomp.le_right]

theorem conj_mem_factor_of_mul_self {P : Subgroup G} (hP : P = 𝔖.S₁ ∨ P = 𝔖.S₂) {a g : G}
    (ha : a ∈ P) (ha2 : a * a = 1) (hg : g * a * g⁻¹ ∈ (𝔖.S : Subgroup G)) : g * a * g⁻¹ ∈ P := by
  by_cases ha1 : a = 1
  · rw [ha1, mul_one, mul_inv_cancel]
    exact one_mem _
  · exact 𝔖.conj_mem_of_mem_factor hP ha (orderOf_eq_prime (by rw [pow_two]; exact ha2) ha1) hg

theorem normalizer_S_le {P : Subgroup G} (hP : P = 𝔖.S₁ ∨ P = 𝔖.S₂) :
    normalizer ((𝔖.S : Subgroup G) : Set G) ≤ normalizer (P : Set G) := by
  intro g hg
  refine Subgroup.mem_normalizer_fintype fun s hs => ?_
  obtain ⟨a, ha, b, hb, ha2, hb2, rfl⟩ := Sec7.IsDih.exists_mul (𝔖.isDih_factor hP) hs
  have hS : ∀ x ∈ P, g * x * g⁻¹ ∈ (𝔖.S : Subgroup G) := fun x hx =>
    (mem_normalizer_iff.mp hg x).mp (𝔖.factor_le_S hP hx)
  have h := mul_mem (𝔖.conj_mem_factor_of_mul_self hP ha ha2 (hS a ha))
    (𝔖.conj_mem_factor_of_mul_self hP hb hb2 (hS b hb))
  rwa [show g * a * g⁻¹ * (g * b * g⁻¹) = g * (a * b) * g⁻¹ by group] at h

theorem normalizer_A_le {P : Subgroup G} (hP : P = 𝔖.S₁ ∨ P = 𝔖.S₂) {A : Subgroup G}
    (hAS : A ≤ (𝔖.S : Subgroup G)) (hA : IsE16 A) :
    normalizer (A : Set G) ≤ normalizer ((A ⊓ P : Subgroup G) : Set G) := by
  intro g hg
  refine Subgroup.mem_normalizer_fintype fun a ha => ?_
  have hgA : g * a * g⁻¹ ∈ A := (mem_normalizer_iff.mp hg a).mp ha.1
  have ha2 : a * a = 1 := by
    have := hA.1.2 a ha.1
    rwa [pow_two] at this
  exact ⟨hgA, 𝔖.conj_mem_factor_of_mul_self hP ha.2 ha2 (hAS hgA)⟩

theorem normalizer_ne_top {P : Subgroup G} (hP : P = 𝔖.S₁ ∨ P = 𝔖.S₂)
    (h417 : ∀ (H : Subgroup G), H.Normal →
      ¬ IsSylowOf 2 𝔖.S₁ H ∧ ¬ IsSylowOf 2 𝔖.S₂ H)
    {T : Subgroup G} (hTP : T ≤ P) (hT : T ≠ ⊥) : normalizer (T : Set G) ≠ ⊤ := by
  intro htop
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTn : T.Normal := normalizer_eq_top_iff.mp htop
  have hD := 𝔖.isDih_factor hP
  have hT2 : IsPGroup 2 T := hD.isPGroup.to_le hTP
  have h2 : 2 ∣ Nat.card T := by
    rcases hT2.card_eq_or_dvd with h | h
    · exact absurd ((Subgroup.card_eq_one).1 h) hT
    · exact h
  obtain ⟨⟨t, htT⟩, ht⟩ := exists_prime_orderOf_dvd_card' (G := T) 2 h2
  have ht2 : orderOf t = 2 := by rwa [Subgroup.orderOf_mk] at ht
  have hinv : ∀ x ∈ P, x * x = 1 → x ∈ T := by
    intro x hx hx2
    by_cases hx1 : x = 1
    · rw [hx1]
      exact one_mem _
    have hxo : orderOf x = 2 := orderOf_eq_prime (by rw [pow_two]; exact hx2) hx1
    have hconj : IsConj t x := by
      rcases hP with rfl | rfl
      · exact 𝔖.fusion.conj₁ t (hTP htT) x hx ht2 hxo
      · exact 𝔖.fusion.conj₂ t (hTP htT) x hx ht2 hxo
    obtain ⟨c, hc⟩ := isConj_iff.mp hconj
    rw [← hc]
    exact hTn.conj_mem t htT c
  have hPT : P ≤ T := by
    intro s hs
    obtain ⟨a, ha, b, hb, ha2, hb2, rfl⟩ := Sec7.IsDih.exists_mul hD hs
    exact mul_mem (hinv a ha ha2) (hinv b hb hb2)
  have hTeq : T = P := le_antisymm hTP hPT
  have hsyl : IsSylowOf 2 P T := by
    rw [hTeq, isSylowOf_iff]
    exact ⟨le_rfl, hD.isPGroup, by rw [relIndex_self]; norm_num⟩
  obtain ⟨h₁, h₂⟩ := h417 T hTn
  rcases hP with rfl | rfl
  exacts [h₁ hsyl, h₂ hsyl]

end Sec4Setting

end CFSG.GH72
