module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Harada.L27.A5Basic

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Harada.L27

open Subgroup

private lemma le_normalizer_right_of_comm {Y : Type*} [Group Y] {T₁ T₂ : Subgroup Y}
    (hcomm : ∀ a ∈ T₁, ∀ b ∈ T₂, a * b = b * a) : T₁ ≤ Subgroup.normalizer T₂ := by
  rw [Subgroup.le_normalizer_iff]
  intro a ha b hb
  rw [show a * b * a⁻¹ = b by rw [hcomm a ha b hb]; group]
  exact hb

private lemma le_normalizer_left_of_comm {Y : Type*} [Group Y] {T₁ T₂ : Subgroup Y}
    (hcomm : ∀ a ∈ T₁, ∀ b ∈ T₂, a * b = b * a) : T₂ ≤ Subgroup.normalizer T₁ := by
  rw [Subgroup.le_normalizer_iff]
  intro b hb a ha
  rw [show b * a * b⁻¹ = a by rw [← hcomm a ha b hb]; group]
  exact ha

theorem exists_conj_of_involution_mul {Y : Type*} [Group Y] {T₁ T₂ : Subgroup Y} {v : Y}
    (hv2 : v * v = 1) (hcomm : ∀ a ∈ T₁, ∀ b ∈ T₂, a * b = b * a) (hdisj : T₁ ⊓ T₂ = ⊥)
    (hswap : T₁.map (MulAut.conj v).toMonoidHom = T₂) {e : Y} (he : e ∈ T₁ ⊔ T₂)
    (hev : (e * v) * (e * v) = 1) : ∃ t ∈ T₂, e * v = t * v * t⁻¹ := by
  have hle : T₁ ≤ Subgroup.normalizer T₂ := le_normalizer_right_of_comm hcomm
  obtain ⟨a, ha, b, hb, hab⟩ : ∃ a ∈ T₁, ∃ b ∈ T₂, a * b = e := by
    have hx : e ∈ (↑(T₁ ⊔ T₂) : Set Y) := he
    rw [Subgroup.coe_mul_of_left_le_normalizer_right T₁ T₂ hle, Set.mem_mul] at hx
    exact hx
  have hmul_conj : MulAut.conj v * MulAut.conj v = 1 := by
    rw [← map_mul, hv2, map_one]
  have hcomp : (MulAut.conj v).toMonoidHom.comp (MulAut.conj v).toMonoidHom
      = MonoidHom.id Y := by
    ext x
    show (MulAut.conj v * MulAut.conj v) x = x
    rw [hmul_conj]
    rfl
  have hswap' : T₂.map (MulAut.conj v).toMonoidHom = T₁ := by
    rw [← hswap, Subgroup.map_map, hcomp, Subgroup.map_id]
  have hs₁ : v * b * v⁻¹ ∈ T₁ := by
    have h : (MulAut.conj v).toMonoidHom b ∈ T₂.map (MulAut.conj v).toMonoidHom :=
      Subgroup.mem_map_of_mem _ hb
    rw [hswap'] at h
    simpa [MulAut.conj_apply] using h
  have hs₂ : v * a * v⁻¹ ∈ T₂ := by
    have h : (MulAut.conj v).toMonoidHom a ∈ T₁.map (MulAut.conj v).toMonoidHom :=
      Subgroup.mem_map_of_mem _ ha
    rw [hswap] at h
    simpa [MulAut.conj_apply] using h
  have h1 : e * (v * e * v⁻¹) * (v * v) = 1 := by
    rw [← hev]
    group
  have h2 : e * (v * e * v⁻¹) = 1 := by simpa [hv2] using h1
  have hconj : v * e * v⁻¹ = (v * a * v⁻¹) * (v * b * v⁻¹) := by
    rw [← hab]
    group
  have hprod0 : a * b * (v * a * v⁻¹) * (v * b * v⁻¹) = 1 := by
    have h := h2
    rw [hconj, ← hab] at h
    simpa [mul_assoc] using h
  have hkey : (a * (v * b * v⁻¹)) * (b * (v * a * v⁻¹))
      = a * b * (v * a * v⁻¹) * (v * b * v⁻¹) := by
    calc (a * (v * b * v⁻¹)) * (b * (v * a * v⁻¹))
        = a * ((v * b * v⁻¹) * b) * (v * a * v⁻¹) := by group
      _ = a * (b * (v * b * v⁻¹)) * (v * a * v⁻¹) := by
            rw [hcomm (v * b * v⁻¹) hs₁ b hb]
      _ = a * b * ((v * b * v⁻¹) * (v * a * v⁻¹)) := by group
      _ = a * b * ((v * a * v⁻¹) * (v * b * v⁻¹)) := by
            rw [hcomm (v * b * v⁻¹) hs₁ (v * a * v⁻¹) hs₂]
      _ = a * b * (v * a * v⁻¹) * (v * b * v⁻¹) := by group
  have hprod : (a * (v * b * v⁻¹)) * (b * (v * a * v⁻¹)) = 1 := by rw [hkey, hprod0]
  have hmem₂ : a * (v * b * v⁻¹) ∈ T₂ := by
    rw [eq_inv_of_mul_eq_one_left hprod]
    exact T₂.inv_mem (T₂.mul_mem hb hs₂)
  have haeq : a * (v * b * v⁻¹) = 1 := by
    have hmem : a * (v * b * v⁻¹) ∈ T₁ ⊓ T₂ :=
      Subgroup.mem_inf.mpr ⟨T₁.mul_mem ha hs₁, hmem₂⟩
    rw [hdisj] at hmem
    exact Subgroup.mem_bot.mp hmem
  have hs1 : v * b * v⁻¹ = a⁻¹ := eq_inv_of_mul_eq_one_right haeq
  refine ⟨b, hb, ?_⟩
  have hbvb : b * v * b⁻¹ = b * a * v := by
    rw [show b * v * b⁻¹ = b * (v * b * v⁻¹)⁻¹ * v by group, hs1, inv_inv]
  calc e * v = a * b * v := by rw [hab]
    _ = b * a * v := by rw [hcomm a ha b hb]
    _ = b * v * b⁻¹ := by rw [hbvb]

theorem eq_or_inf_eq_bot_of_le_sup {Y : Type*} [Group Y] {T₁ T₂ F : Subgroup Y}
    (hcomm : ∀ a ∈ T₁, ∀ b ∈ T₂, a * b = b * a) (hF : F ≤ T₁ ⊔ T₂)
    (eF : F ≃* alternatingGroup (Fin 5)) (h₁ : Nat.card T₁ = 60) (h₂ : Nat.card T₂ = 60) :
    F = T₁ ∨ F = T₂ ∨ (F ⊓ T₁ = ⊥ ∧ F ⊓ T₂ = ⊥) := by
  have hsup_n₁ : T₁ ⊔ T₂ ≤ Subgroup.normalizer T₁ :=
    sup_le Subgroup.le_normalizer (le_normalizer_left_of_comm hcomm)
  have hsup_n₂ : T₁ ⊔ T₂ ≤ Subgroup.normalizer T₂ :=
    sup_le (le_normalizer_right_of_comm hcomm) Subgroup.le_normalizer
  have hFn₁ : F ≤ Subgroup.normalizer T₁ := hF.trans hsup_n₁
  have hFn₂ : F ≤ Subgroup.normalizer T₂ := hF.trans hsup_n₂
  have hnorm₁ : (T₁.subgroupOf F).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer hFn₁
  have hnorm₂ : (T₂.subgroupOf F).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer hFn₂
  haveI : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
  haveI : IsSimpleGroup F := eF.isSimpleGroup
  have hFcard : Nat.card F = 60 := by
    rw [Nat.card_congr eF.toEquiv, card_alternatingGroup_five]
  have hcase₁ : T₁.subgroupOf F = ⊥ ∨ F ≤ T₁ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (T₁.subgroupOf F) with h | h
    · exact Or.inl h
    · exact Or.inr (Subgroup.subgroupOf_eq_top.mp h)
  have hcase₂ : T₂.subgroupOf F = ⊥ ∨ F ≤ T₂ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (T₂.subgroupOf F) with h | h
    · exact Or.inl h
    · exact Or.inr (Subgroup.subgroupOf_eq_top.mp h)
  haveI : Finite T₁ := Nat.finite_of_card_ne_zero (by rw [h₁]; norm_num)
  haveI : Finite T₂ := Nat.finite_of_card_ne_zero (by rw [h₂]; norm_num)
  rcases hcase₁ with hbot₁ | hle₁
  · rcases hcase₂ with hbot₂ | hle₂
    · right; right
      refine ⟨?_, ?_⟩
      · rw [inf_comm]
        exact disjoint_iff.mp (Subgroup.subgroupOf_eq_bot.mp hbot₁)
      · rw [inf_comm]
        exact disjoint_iff.mp (Subgroup.subgroupOf_eq_bot.mp hbot₂)
    · right; left
      exact Subgroup.eq_of_le_of_card_ge hle₂ (by simp [h₂, hFcard])
  · left
    exact Subgroup.eq_of_le_of_card_ge hle₁ (by simp [h₁, hFcard])

private theorem centralizes_left_of_diagonal {Y : Type*} [Group Y] {T₁ T₂ F : Subgroup Y} {v : Y}
    (hcomm : ∀ a ∈ T₁, ∀ b ∈ T₂, a * b = b * a) (hdisj : T₁ ⊓ T₂ = ⊥)
    (hF : F ≤ T₁ ⊔ T₂) (hF₂ : F ⊓ T₂ = ⊥)
    (h₁ : Nat.card T₁ = 60) (hFc : Nat.card F = 60)
    (hv₁ : ∀ t ∈ T₁, v * t * v⁻¹ ∈ T₁) (hv₂ : ∀ t ∈ T₂, v * t * v⁻¹ ∈ T₂)
    (hFv : ∀ f ∈ F, f * v = v * f) :
    ∀ t ∈ T₁, t * v = v * t := by
  have hle : T₁ ≤ Subgroup.normalizer T₂ := le_normalizer_right_of_comm hcomm
  have hdecomp : ∀ x : Y, x ∈ T₁ ⊔ T₂ → ∃ a : T₁, ∃ b : T₂, (a : Y) * (b : Y) = x := by
    intro x hx
    have hx' : x ∈ (↑(T₁ ⊔ T₂) : Set Y) := hx
    rw [Subgroup.coe_mul_of_left_le_normalizer_right T₁ T₂ hle, Set.mem_mul] at hx'
    obtain ⟨a, ha, b, hb, hab⟩ := hx'
    exact ⟨⟨a, ha⟩, ⟨b, hb⟩, hab⟩
  let aOf : F → T₁ := fun f => Classical.choose (hdecomp (f : Y) (hF f.2))
  have haOf_spec : ∀ f : F, ∃ b : T₂, (aOf f : Y) * (b : Y) = (f : Y) :=
    fun f => Classical.choose_spec (hdecomp (f : Y) (hF f.2))
  have haOf_comm : ∀ f : F, (aOf f : Y) * v = v * (aOf f : Y) := by
    intro f
    obtain ⟨b, hb⟩ := haOf_spec f
    have hconj : v * (f : Y) * v⁻¹ = (f : Y) := by
      rw [← hFv f f.2]
      group
    have hva : v * (aOf f : Y) * v⁻¹ ∈ T₁ := hv₁ _ (aOf f).2
    have hvb : v * (b : Y) * v⁻¹ ∈ T₂ := hv₂ _ b.2
    have h1 : v * ((aOf f : Y) * (b : Y)) * v⁻¹ = (aOf f : Y) * (b : Y) := by
      rw [hb, hconj]
    have h2 : v * ((aOf f : Y) * (b : Y)) * v⁻¹
        = (v * (aOf f : Y) * v⁻¹) * (v * (b : Y) * v⁻¹) := by group
    rw [h2] at h1
    have heq : (v * (aOf f : Y) * v⁻¹)⁻¹ * (aOf f : Y)
        = (v * (b : Y) * v⁻¹) * (b : Y)⁻¹ := by
      calc (v * (aOf f : Y) * v⁻¹)⁻¹ * (aOf f : Y)
          = (v * (aOf f : Y) * v⁻¹)⁻¹ * ((aOf f : Y) * (b : Y)) * (b : Y)⁻¹ := by
              group
        _ = (v * (aOf f : Y) * v⁻¹)⁻¹
              * ((v * (aOf f : Y) * v⁻¹) * (v * (b : Y) * v⁻¹)) * (b : Y)⁻¹ := by
              rw [← h1]
        _ = (v * (b : Y) * v⁻¹) * (b : Y)⁻¹ := by group
    have hmem : (v * (aOf f : Y) * v⁻¹)⁻¹ * (aOf f : Y) ∈ T₁ ⊓ T₂ := by
      rw [Subgroup.mem_inf]
      exact ⟨T₁.mul_mem (T₁.inv_mem hva) (aOf f).2, by
        rw [heq]; exact T₂.mul_mem hvb (T₂.inv_mem b.2)⟩
    have hone : (v * (aOf f : Y) * v⁻¹)⁻¹ * (aOf f : Y) = 1 := by
      have := hmem
      rw [hdisj] at this
      exact Subgroup.mem_bot.mp this
    have hva_eq : v * (aOf f : Y) * v⁻¹ = (aOf f : Y) := inv_mul_eq_one.mp hone
    have haev : v * (aOf f : Y) = (aOf f : Y) * v := by
      calc v * (aOf f : Y) = v * (aOf f : Y) * v⁻¹ * v := by group
        _ = (aOf f : Y) * v := by rw [hva_eq]
    exact haev.symm
  have haOf_inj : Function.Injective aOf := by
    intro f₁ f₂ h
    obtain ⟨b₁, hb₁⟩ := haOf_spec f₁
    obtain ⟨b₂, hb₂⟩ := haOf_spec f₂
    have hval : (aOf f₁ : Y) = (aOf f₂ : Y) := congrArg Subtype.val h
    have hc₁ : Commute (aOf f₁ : Y) (b₁ : Y) :=
      (commute_iff_eq _ _).mpr (hcomm (aOf f₁) (aOf f₁).2 b₁ b₁.2)
    have hc₂ : Commute (aOf f₁ : Y) (b₂ : Y) :=
      (commute_iff_eq _ _).mpr (hcomm (aOf f₁) (aOf f₁).2 b₂ b₂.2)
    have hc : Commute (aOf f₁ : Y) ((b₁ : Y) * (b₂ : Y)⁻¹) := hc₁.mul_right hc₂.inv_right
    have hf : (f₁ : Y) * (f₂ : Y)⁻¹ = (b₁ : Y) * (b₂ : Y)⁻¹ := by
      rw [← hb₁, ← hb₂, ← hval]
      calc (aOf f₁ : Y) * (b₁ : Y) * ((aOf f₁ : Y) * (b₂ : Y))⁻¹
          = (aOf f₁ : Y) * ((b₁ : Y) * (b₂ : Y)⁻¹) * (aOf f₁ : Y)⁻¹ := by group
        _ = ((b₁ : Y) * (b₂ : Y)⁻¹) * (aOf f₁ : Y) * (aOf f₁ : Y)⁻¹ := by rw [hc.eq]
        _ = (b₁ : Y) * (b₂ : Y)⁻¹ := by group
    have hmemT₂ : (f₁ : Y) * (f₂ : Y)⁻¹ ∈ T₂ := by
      rw [hf]; exact T₂.mul_mem b₁.2 (T₂.inv_mem b₂.2)
    have hone : (f₁ : Y) * (f₂ : Y)⁻¹ = 1 := by
      have hmem : (f₁ : Y) * (f₂ : Y)⁻¹ ∈ F ⊓ T₂ :=
        Subgroup.mem_inf.mpr ⟨F.mul_mem f₁.2 (F.inv_mem f₂.2), hmemT₂⟩
      rw [hF₂] at hmem
      exact Subgroup.mem_bot.mp hmem
    exact Subtype.ext (mul_inv_eq_one.mp hone)
  have haOf_surj : Function.Surjective aOf := by
    haveI : Finite T₁ := Nat.finite_of_card_ne_zero (by rw [h₁]; norm_num)
    exact (haOf_inj.bijective_of_nat_card_le (by simp [h₁, hFc])).2
  intro t ht
  obtain ⟨f, hf⟩ := haOf_surj ⟨t, ht⟩
  have := haOf_comm f
  rwa [show (aOf f : Y) = t from congrArg Subtype.val hf] at this

theorem centralizes_of_diagonal {Y : Type*} [Group Y] {T₁ T₂ F : Subgroup Y} {v : Y}
    (hcomm : ∀ a ∈ T₁, ∀ b ∈ T₂, a * b = b * a) (hdisj : T₁ ⊓ T₂ = ⊥)
    (hF : F ≤ T₁ ⊔ T₂) (hF₁ : F ⊓ T₁ = ⊥) (hF₂ : F ⊓ T₂ = ⊥)
    (h₁ : Nat.card T₁ = 60) (h₂ : Nat.card T₂ = 60) (hFc : Nat.card F = 60)
    (hv₁ : ∀ t ∈ T₁, v * t * v⁻¹ ∈ T₁) (hv₂ : ∀ t ∈ T₂, v * t * v⁻¹ ∈ T₂)
    (hFv : ∀ f ∈ F, f * v = v * f) :
    (∀ t ∈ T₁, t * v = v * t) ∧ (∀ t ∈ T₂, t * v = v * t) := by
  refine ⟨centralizes_left_of_diagonal hcomm hdisj hF hF₂ h₁ hFc hv₁ hv₂ hFv, ?_⟩
  have hcomm' : ∀ a ∈ T₂, ∀ b ∈ T₁, a * b = b * a := fun a ha b hb => (hcomm b hb a ha).symm
  have hdisj' : T₂ ⊓ T₁ = ⊥ := by rw [inf_comm]; exact hdisj
  have hF' : F ≤ T₂ ⊔ T₁ := by rw [sup_comm]; exact hF
  exact centralizes_left_of_diagonal hcomm' hdisj' hF' hF₁ h₂ hFc hv₂ hv₁ hFv

end CFSG.EvenSporadicStandard.HNRecog.Harada.L27
