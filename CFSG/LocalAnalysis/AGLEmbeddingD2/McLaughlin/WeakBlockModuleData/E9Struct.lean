module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.E9Group
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.E9Abs2
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.SixLieOneNode

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData

open scoped commutatorElement Pointwise

section Assembly

variable {Y : Type} [Group Y] [Finite Y]

theorem separated_pair_one {J R T E : Subgroup Y} {x y : Y} (hRJ : R ≤ J)
    (hJR : J ≤ Subgroup.normalizer (R : Set Y)) (hR2 : IsPGroup 2 R) (hTJ : T ≤ J) (hxJ : x ∈ J)
    (hyJ : y ∈ J) (hJle : J ≤ R ⊔ (T ⊔ Subgroup.closure {x, y}))
    (hTx : ∀ t ∈ T, t * x = x * t) (hTy : ∀ t ∈ T, t * y = y * t) (hT3 : ∀ t ∈ T, t ^ 3 = 1)
    (hx2 : x * x = 1) (hy2 : y * y = 1) (hxy3 : (x * y) ^ 3 = 1) (hxy1 : x * y ≠ 1)
    (ht : ∃ t ∈ T, t ≠ 1) (hEJ : E ≤ J) (hE9 : Nat.card E = 9)
    (hsyl : ¬ 3 ∣ (E.subgroupOf J).index) :
    ∃ e₁ e₂ : ↥J, (e₁ : Y) ∈ E ∧ (e₂ : Y) ∈ E ∧ e₁ ≠ 1 ∧ e₂ ≠ 1 ∧
      ∀ φ : ↥J ≃* ↥J, φ e₁ ≠ e₂ := by
  obtain ⟨t, htT, ht1⟩ := ht
  have hclJ : Subgroup.closure ({x, y} : Set Y) ≤ J := (Subgroup.closure_le _).2 (by
    intro z hz
    rcases hz with rfl | hz
    · exact hxJ
    · rw [Set.mem_singleton_iff] at hz; rw [hz]; exact hyJ)
  have htc : t * (x * y) = (x * y) * t := by
    calc t * (x * y) = (t * x) * y := by group
      _ = (x * t) * y := by rw [hTx t htT]
      _ = x * (t * y) := by group
      _ = x * (y * t) := by rw [hTy t htT]
      _ = (x * y) * t := by group
  obtain ⟨V, hV3, hV⟩ := exists_pGroup_card_9 (a := t) (b := x * y) (zb := x) htc (hT3 t htT) hxy3
    ht1 hxy1 (conj_c_eq_inv hx2 hy2) (hTx t htT).symm
  have hVJ : V ≤ J := by
    rw [hV]
    exact sup_le ((Subgroup.zpowers_le).2 (hTJ htT)) ((Subgroup.zpowers_le).2 (J.mul_mem hxJ hyJ))
  obtain ⟨g, hgJ, hg⟩ := exists_conj_into hEJ hE9 hsyl hVJ hV3
  have htV : t ∈ V := by rw [hV]; exact Subgroup.mem_sup_left (Subgroup.mem_zpowers t)
  have hcV : x * y ∈ V := by rw [hV]; exact Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
  set gJ : ↥J := ⟨g, hgJ⟩ with hgJdef
  set x' : ↥J := ⟨x, hxJ⟩ with hx'
  set y' : ↥J := ⟨y, hyJ⟩ with hy'
  set tJ : ↥J := ⟨t, hTJ htT⟩ with htJ
  set T' : Subgroup ↥J := T.subgroupOf J with hT'
  have hgen : (⊤ : Subgroup ↥J) ≤
      CFSG.pCore 2 ↥J ⊔ (T' ⊔ Subgroup.closure ({x', y'} : Set ↥J)) := by
    rw [subgroupOf_closure_pair hxJ hyJ]
    exact (top_le_subgroupOf_sup hJle hRJ hTJ hclJ).trans
      (sup_le_sup_right (subgroupOf_le_pCore hRJ hJR hR2) _)
  have hTx' : ∀ s ∈ T', s * x' = x' * s := fun s hs =>
    Subtype.ext (hTx s.1 (Subgroup.mem_subgroupOf.1 hs))
  have hTy' : ∀ s ∈ T', s * y' = y' * s := fun s hs =>
    Subtype.ext (hTy s.1 (Subgroup.mem_subgroupOf.1 hs))
  have hT3' : ∀ s ∈ T', s ^ 3 = 1 := fun s hs =>
    Subtype.ext (hT3 s.1 (Subgroup.mem_subgroupOf.1 hs))
  have hx2' : x' * x' = 1 := Subtype.ext hx2
  have hy2' : y' * y' = 1 := Subtype.ext hy2
  have hxy3' : (x' * y') ^ 3 = 1 := Subtype.ext hxy3
  have hxy1' : x' * y' ≠ 1 := fun h => hxy1 (congrArg Subtype.val h)
  have htx' : tJ * x' = x' * tJ := Subtype.ext (hTx t htT)
  have hinv₁ : HasInvolMod ↥J tJ := hasInvolMod_of_commute htx' hx2' hy2' hxy3' hxy1'
  have hinv₂ : ¬ HasInvolMod ↥J (x' * y') :=
    not_hasInvolMod_c_one hgen hTx' hTy' hT3' hx2' hy2' hxy3' hxy1'
  refine ⟨gJ⁻¹ * tJ * gJ, gJ⁻¹ * (x' * y') * gJ, ?_, ?_, ?_, ?_, ?_⟩
  · exact hg t htV
  · exact hg _ hcV
  · intro h
    apply ht1
    have := congrArg Subtype.val h
    have h' : g⁻¹ * t * g = 1 := this
    calc t = g * (g⁻¹ * t * g) * g⁻¹ := by group
      _ = 1 := by rw [h']; group
  · intro h
    apply hxy1
    have := congrArg Subtype.val h
    have h' : g⁻¹ * (x * y) * g = 1 := this
    calc x * y = g * (g⁻¹ * (x * y) * g) * g⁻¹ := by group
      _ = 1 := by rw [h']; group
  · intro φ hφ
    have h1 : HasInvolMod ↥J (gJ⁻¹ * tJ * gJ) := by
      have := hasInvolMod_map (MulAut.conj gJ⁻¹) hinv₁
      simpa [MulAut.conj_apply] using this
    have h2 : HasInvolMod ↥J (gJ⁻¹ * (x' * y') * gJ) := hφ ▸ hasInvolMod_map φ h1
    apply hinv₂
    have := hasInvolMod_map (MulAut.conj gJ) h2
    simpa [MulAut.conj_apply, mul_assoc] using this

theorem separated_pair_two {J R E : Subgroup Y} {x₁ y₁ x₂ y₂ : Y} (hRJ : R ≤ J)
    (hJR : J ≤ Subgroup.normalizer (R : Set Y)) (hR2 : IsPGroup 2 R) (hx₁J : x₁ ∈ J)
    (hy₁J : y₁ ∈ J) (hx₂J : x₂ ∈ J) (hy₂J : y₂ ∈ J)
    (hJle : J ≤ R ⊔ (Subgroup.closure {x₁, y₁} ⊔ Subgroup.closure {x₂, y₂}))
    (h11 : x₁ * x₂ = x₂ * x₁) (h12 : x₁ * y₂ = y₂ * x₁) (h21 : y₁ * x₂ = x₂ * y₁)
    (h22 : y₁ * y₂ = y₂ * y₁)
    (hx₁ : x₁ * x₁ = 1) (hy₁ : y₁ * y₁ = 1) (h₁3 : (x₁ * y₁) ^ 3 = 1) (h₁1 : x₁ * y₁ ≠ 1)
    (hx₂ : x₂ * x₂ = 1) (hy₂ : y₂ * y₂ = 1) (h₂3 : (x₂ * y₂) ^ 3 = 1) (h₂1 : x₂ * y₂ ≠ 1)
    (hEJ : E ≤ J) (hE9 : Nat.card E = 9) (hsyl : ¬ 3 ∣ (E.subgroupOf J).index) :
    ∃ e₁ e₂ : ↥J, (e₁ : Y) ∈ E ∧ (e₂ : Y) ∈ E ∧ e₁ ≠ 1 ∧ e₂ ≠ 1 ∧
      ∀ φ : ↥J ≃* ↥J, φ e₁ ≠ e₂ := by
  have hcl : ∀ {x y : Y}, x ∈ J → y ∈ J → Subgroup.closure ({x, y} : Set Y) ≤ J := fun {x y} hx hy =>
    (Subgroup.closure_le _).2 (by
      intro z hz
      rcases hz with rfl | hz
      · exact hx
      · rw [Set.mem_singleton_iff] at hz; rw [hz]; exact hy)
  have e1 : Commute x₂ (x₁ * y₁) :=
    (show Commute x₂ x₁ from h11.symm).mul_right (show Commute x₂ y₁ from h21.symm)
  have e1' : Commute x₁ (x₂ * y₂) :=
    (show Commute x₁ x₂ from h11).mul_right (show Commute x₁ y₂ from h12)
  have e2' : Commute y₁ (x₂ * y₂) :=
    (show Commute y₁ x₂ from h21).mul_right (show Commute y₁ y₂ from h22)
  have hcc : (x₁ * y₁) * (x₂ * y₂) = (x₂ * y₂) * (x₁ * y₁) := (e1'.mul_left e2').eq
  obtain ⟨V, hV3, hV⟩ := exists_pGroup_card_9 (a := x₁ * y₁) (b := x₂ * y₂) (zb := x₂) hcc h₁3 h₂3
    h₁1 h₂1 (conj_c_eq_inv hx₂ hy₂) e1.eq
  have hc₁J : x₁ * y₁ ∈ J := J.mul_mem hx₁J hy₁J
  have hc₂J : x₂ * y₂ ∈ J := J.mul_mem hx₂J hy₂J
  have hVJ : V ≤ J := by
    rw [hV]
    exact sup_le ((Subgroup.zpowers_le).2 hc₁J) ((Subgroup.zpowers_le).2 hc₂J)
  obtain ⟨g, hgJ, hg⟩ := exists_conj_into hEJ hE9 hsyl hVJ hV3
  have hc₁V : x₁ * y₁ ∈ V := by rw [hV]; exact Subgroup.mem_sup_left (Subgroup.mem_zpowers _)
  have hc₂V : x₂ * y₂ ∈ V := by rw [hV]; exact Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
  have hc₁₂V : (x₁ * y₁) * (x₂ * y₂) ∈ V := V.mul_mem hc₁V hc₂V
  have hne : (x₁ * y₁) * (x₂ * y₂) ≠ 1 := by
    intro h
    have hc2 : x₂ * y₂ = (x₁ * y₁)⁻¹ := eq_inv_of_mul_eq_one_right h
    have hcomm2 : x₂ * (x₂ * y₂) * x₂⁻¹ = x₂ * y₂ := by
      rw [hc2]
      have := e1.eq
      calc x₂ * (x₁ * y₁)⁻¹ * x₂⁻¹ = (x₂ * (x₁ * y₁) * x₂⁻¹)⁻¹ := by group
        _ = (x₁ * y₁)⁻¹ := by rw [this]; group
    rw [conj_c_eq_inv hx₂ hy₂] at hcomm2
    have hsq : (x₂ * y₂) * (x₂ * y₂) = 1 := by
      calc (x₂ * y₂) * (x₂ * y₂) = (x₂ * y₂)⁻¹ * (x₂ * y₂) := by rw [hcomm2]
        _ = 1 := inv_mul_cancel _
    exact h₂1 (eq_one_of_mul_self_of_pow_three hsq h₂3)
  set gJ : ↥J := ⟨g, hgJ⟩ with hgJdef
  set x₁' : ↥J := ⟨x₁, hx₁J⟩
  set y₁' : ↥J := ⟨y₁, hy₁J⟩
  set x₂' : ↥J := ⟨x₂, hx₂J⟩
  set y₂' : ↥J := ⟨y₂, hy₂J⟩
  have hgen : (⊤ : Subgroup ↥J) ≤ CFSG.pCore 2 ↥J ⊔
      (Subgroup.closure ({x₁', y₁'} : Set ↥J) ⊔ Subgroup.closure ({x₂', y₂'} : Set ↥J)) := by
    rw [subgroupOf_closure_pair hx₁J hy₁J, subgroupOf_closure_pair hx₂J hy₂J]
    exact (top_le_subgroupOf_sup hJle hRJ (hcl hx₁J hy₁J) (hcl hx₂J hy₂J)).trans
      (sup_le_sup_right (subgroupOf_le_pCore hRJ hJR hR2) _)
  have hh11 : x₁' * x₂' = x₂' * x₁' := Subtype.ext h11
  have hh12 : x₁' * y₂' = y₂' * x₁' := Subtype.ext h12
  have hh21 : y₁' * x₂' = x₂' * y₁' := Subtype.ext h21
  have hh22 : y₁' * y₂' = y₂' * y₁' := Subtype.ext h22
  have hhx₁ : x₁' * x₁' = 1 := Subtype.ext hx₁
  have hhy₁ : y₁' * y₁' = 1 := Subtype.ext hy₁
  have hh₁3 : (x₁' * y₁') ^ 3 = 1 := Subtype.ext h₁3
  have hh₁1 : x₁' * y₁' ≠ 1 := fun h => h₁1 (congrArg Subtype.val h)
  have hhx₂ : x₂' * x₂' = 1 := Subtype.ext hx₂
  have hhy₂ : y₂' * y₂' = 1 := Subtype.ext hy₂
  have hh₂3 : (x₂' * y₂') ^ 3 = 1 := Subtype.ext h₂3
  have hh₂1 : x₂' * y₂' ≠ 1 := fun h => h₂1 (congrArg Subtype.val h)
  have hinv₁ : HasInvolMod ↥J (x₁' * y₁') :=
    hasInvolMod_c_two_left hh11 hh21 hhx₂ hhy₂ hh₂3 hh₂1
  have hinv₂ : ¬ HasInvolMod ↥J ((x₁' * y₁') * (x₂' * y₂')) :=
    not_hasInvolMod_c_two hgen hh11 hh12 hh21 hh22 hhx₁ hhy₁ hh₁3 hh₁1 hhx₂ hhy₂ hh₂3 hh₂1
  refine ⟨gJ⁻¹ * (x₁' * y₁') * gJ, gJ⁻¹ * ((x₁' * y₁') * (x₂' * y₂')) * gJ, ?_, ?_, ?_, ?_, ?_⟩
  · exact hg _ hc₁V
  · exact hg _ hc₁₂V
  · intro h
    apply h₁1
    have h' : g⁻¹ * (x₁ * y₁) * g = 1 := congrArg Subtype.val h
    calc x₁ * y₁ = g * (g⁻¹ * (x₁ * y₁) * g) * g⁻¹ := by group
      _ = 1 := by rw [h']; group
  · intro h
    apply hne
    have h' : g⁻¹ * ((x₁ * y₁) * (x₂ * y₂)) * g = 1 := congrArg Subtype.val h
    calc (x₁ * y₁) * (x₂ * y₂) = g * (g⁻¹ * ((x₁ * y₁) * (x₂ * y₂)) * g) * g⁻¹ := by group
      _ = 1 := by rw [h']; group
  · intro φ hφ
    have h1 : HasInvolMod ↥J (gJ⁻¹ * (x₁' * y₁') * gJ) := by
      have := hasInvolMod_map (MulAut.conj gJ⁻¹) hinv₁
      simpa [MulAut.conj_apply] using this
    have h2 : HasInvolMod ↥J (gJ⁻¹ * ((x₁' * y₁') * (x₂' * y₂')) * gJ) :=
      hφ ▸ hasInvolMod_map φ h1
    apply hinv₂
    have := hasInvolMod_map (MulAut.conj gJ) h2
    simpa [MulAut.conj_apply, mul_assoc] using this

theorem not_nine_dvd_card_of_le_sup {J R : Subgroup Y} {x y : Y} (hRJ : R ≤ J)
    (hJR : J ≤ Subgroup.normalizer (R : Set Y)) (hR2 : IsPGroup 2 R) (hxJ : x ∈ J) (hyJ : y ∈ J)
    (hJle : J ≤ R ⊔ Subgroup.closure {x, y}) (hx2 : x * x = 1) (hy2 : y * y = 1)
    (hxy3 : (x * y) ^ 3 = 1) (hxy1 : x * y ≠ 1) : ¬ 9 ∣ Nat.card J := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hclJ : Subgroup.closure ({x, y} : Set Y) ≤ J := (Subgroup.closure_le _).2 (by
    intro z hz
    rcases hz with rfl | hz
    · exact hxJ
    · rw [Set.mem_singleton_iff] at hz; rw [hz]; exact hyJ)
  have hx2' : x ^ 2 = 1 := by rw [sq]; exact hx2
  have hy2' : y ^ 2 = 1 := by rw [sq]; exact hy2
  have hcl6 := card_closure_pair_dvd_six hx2' hy2' hxy3 hxy1
  obtain ⟨a, ha⟩ : ∃ a, Nat.card R = 2 ^ a := IsPGroup.iff_card.mp hR2
  have hN : Subgroup.closure ({x, y} : Set Y) ≤ Subgroup.normalizer (R : Set Y) := hclJ.trans hJR
  have h := CFSG.RankThree.PartOne.K1214.card_sup_mul_card_inf_of_le_normalizer hN
  have h1 : Nat.card (R ⊔ Subgroup.closure {x, y} : Subgroup Y) ∣
      Nat.card R * Nat.card (Subgroup.closure {x, y} : Subgroup Y) := by
    rw [sup_comm] at h ⊢
    exact Dvd.intro _ h
  rw [ha] at h1
  have h2 : Nat.card J ∣ 2 ^ a * 6 :=
    (Subgroup.card_dvd_of_le hJle).trans (h1.trans (Nat.mul_dvd_mul_left _ hcl6))
  intro h9
  have h96 : 9 ∣ 2 ^ a * 6 := h9.trans h2
  have hcop : Nat.Coprime 9 (2 ^ a) := Nat.Coprime.pow_right _ (by norm_num)
  have := hcop.dvd_of_dvd_mul_left h96
  omega

end Assembly

end CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData
