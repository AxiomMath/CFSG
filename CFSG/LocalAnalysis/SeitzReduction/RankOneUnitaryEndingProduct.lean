module

public import Mathlib.GroupTheory.Index
public import Mathlib.Tactic.Group

public section

namespace CFSG.SeitzReduction.RankOne

open Subgroup

variable {G : Type*} [Group G]

theorem eq_and_eq_of_mul_eq_mul_of_inf_eq_bot {Y₁ Y₂ : Subgroup G} (hinf : Y₁ ⊓ Y₂ = ⊥)
    {a a' b b' : G} (ha : a ∈ Y₁) (ha' : a' ∈ Y₁) (hb : b ∈ Y₂) (hb' : b' ∈ Y₂)
    (h : a * b = a' * b') : a = a' ∧ b = b' := by
  have h1 : a'⁻¹ * a = b' * b⁻¹ := by
    calc a'⁻¹ * a = a'⁻¹ * (a * b) * b⁻¹ := by group
      _ = a'⁻¹ * (a' * b') * b⁻¹ := by rw [h]
      _ = b' * b⁻¹ := by group
  have h2 : a'⁻¹ * a ∈ Y₁ ⊓ Y₂ := by
    refine mem_inf.mpr ⟨mul_mem (inv_mem ha') ha, ?_⟩
    rw [h1]
    exact mul_mem hb' (inv_mem hb)
  rw [hinf, mem_bot] at h2
  have e1 : a = a' := by
    calc a = a' * (a'⁻¹ * a) := by group
      _ = a' := by rw [h2, mul_one]
  refine ⟨e1, ?_⟩
  rw [e1] at h
  exact mul_left_cancel h

theorem exists_mul_eq_of_mem_sup_of_commute {Y₁ Y₂ : Subgroup G}
    (hcomm : ∀ a ∈ Y₁, ∀ b ∈ Y₂, a * b = b * a) {x : G} (hx : x ∈ Y₁ ⊔ Y₂) :
    ∃ a ∈ Y₁, ∃ b ∈ Y₂, a * b = x := by
  have hle : Y₂ ≤ normalizer (Y₁ : Set G) := by
    intro b hb
    refine mem_normalizer_iff.mpr fun a => ⟨fun ha => ?_, fun ha => ?_⟩
    · rw [← hcomm a ha b hb, mul_inv_cancel_right]
      exact ha
    · have e : a = b * a * b⁻¹ := by
        calc a = b⁻¹ * (b * a * b⁻¹) * b := by group
          _ = b⁻¹ * (b * (b * a * b⁻¹)) := by rw [mul_assoc, hcomm _ ha b hb]
          _ = b * a * b⁻¹ := by group
      rw [e]
      exact ha
  have hx' : x ∈ ((Y₁ ⊔ Y₂ : Subgroup G) : Set G) := hx
  rw [coe_mul_of_right_le_normalizer_left Y₁ Y₂ hle] at hx'
  obtain ⟨a, ha, b, hb, rfl⟩ := Set.mem_mul.mp hx'
  exact ⟨a, ha, b, hb, rfl⟩

theorem mem_centralizer_or_of_not_comm {Y₁ Y₂ : Subgroup G} (hinf : Y₁ ⊓ Y₂ = ⊥)
    (hcomm : ∀ a ∈ Y₁, ∀ b ∈ Y₂, a * b = b * a)
    (hCA₁ : ∀ y ∈ Y₁, (∃ z ∈ Y₁, y * z ≠ z * y) →
      ∀ c ∈ Y₁, ∀ c' ∈ Y₁, c * y = y * c → c' * y = y * c' → c * c' = c' * c)
    (hCA₂ : ∀ y ∈ Y₂, (∃ z ∈ Y₂, y * z ≠ z * y) →
      ∀ c ∈ Y₂, ∀ c' ∈ Y₂, c * y = y * c → c' * y = y * c' → c * c' = c' * c)
    {x c c' : G} (hx : x ∈ Y₁ ⊔ Y₂) (hc : c ∈ Y₁ ⊔ Y₂) (hc' : c' ∈ Y₁ ⊔ Y₂)
    (hcx : c * x = x * c) (hc'x : c' * x = x * c') (hcc' : c * c' ≠ c' * c) :
    x ∈ centralizer (Y₂ : Set G) ∨ x ∈ centralizer (Y₁ : Set G) := by
  by_contra hno
  rw [not_or] at hno
  obtain ⟨hx2, hx1⟩ := hno
  obtain ⟨a, ha, b, hb, rfl⟩ := exists_mul_eq_of_mem_sup_of_commute hcomm hx
  have hbnc : ∃ z ∈ Y₂, b * z ≠ z * b := by
    by_contra hall
    apply hx2
    refine mem_centralizer_iff.mpr fun z hz => ?_
    have hbz : b * z = z * b := by
      by_contra hne
      exact hall ⟨z, hz, hne⟩
    calc z * (a * b) = (z * a) * b := by group
      _ = (a * z) * b := by rw [← hcomm a ha z hz]
      _ = a * (z * b) := by group
      _ = a * (b * z) := by rw [← hbz]
      _ = a * b * z := by group
  have hanc : ∃ z ∈ Y₁, a * z ≠ z * a := by
    by_contra hall
    apply hx1
    refine mem_centralizer_iff.mpr fun z hz => ?_
    have haz : a * z = z * a := by
      by_contra hne
      exact hall ⟨z, hz, hne⟩
    calc z * (a * b) = (z * a) * b := by group
      _ = (a * z) * b := by rw [← haz]
      _ = a * (z * b) := by group
      _ = a * (b * z) := by rw [hcomm z hz b hb]
      _ = a * b * z := by group
  have hsplit : ∀ {d₁ d₂ : G}, d₁ ∈ Y₁ → d₂ ∈ Y₂ → d₁ * d₂ * (a * b) = a * b * (d₁ * d₂) →
      d₁ * a = a * d₁ ∧ d₂ * b = b * d₂ := by
    intro d₁ d₂ hd₁ hd₂ h
    apply eq_and_eq_of_mul_eq_mul_of_inf_eq_bot hinf (mul_mem hd₁ ha) (mul_mem ha hd₁)
      (mul_mem hd₂ hb) (mul_mem hb hd₂)
    calc d₁ * a * (d₂ * b) = d₁ * (a * d₂) * b := by group
      _ = d₁ * (d₂ * a) * b := by rw [hcomm a ha d₂ hd₂]
      _ = d₁ * d₂ * (a * b) := by group
      _ = a * b * (d₁ * d₂) := h
      _ = a * (b * d₁) * d₂ := by group
      _ = a * (d₁ * b) * d₂ := by rw [hcomm d₁ hd₁ b hb]
      _ = a * d₁ * (b * d₂) := by group
  obtain ⟨c₁, hc₁, c₂, hc₂, rfl⟩ := exists_mul_eq_of_mem_sup_of_commute hcomm hc
  obtain ⟨c₁', hc₁', c₂', hc₂', rfl⟩ := exists_mul_eq_of_mem_sup_of_commute hcomm hc'
  obtain ⟨h1, h2⟩ := hsplit hc₁ hc₂ hcx
  obtain ⟨h1', h2'⟩ := hsplit hc₁' hc₂' hc'x
  have e1 := hCA₁ a ha hanc c₁ hc₁ c₁' hc₁' h1 h1'
  have e2 := hCA₂ b hb hbnc c₂ hc₂ c₂' hc₂' h2 h2'
  apply hcc'
  calc c₁ * c₂ * (c₁' * c₂') = c₁ * (c₂ * c₁') * c₂' := by group
    _ = c₁ * (c₁' * c₂) * c₂' := by rw [hcomm c₁' hc₁' c₂ hc₂]
    _ = (c₁ * c₁') * (c₂ * c₂') := by group
    _ = (c₁' * c₁) * (c₂' * c₂) := by rw [e1, e2]
    _ = c₁' * (c₁ * c₂') * c₂ := by group
    _ = c₁' * (c₂' * c₁) * c₂ := by rw [hcomm c₁ hc₁ c₂' hc₂']
    _ = c₁' * c₂' * (c₁ * c₂) := by group

theorem map_conj_le_or_le {U Y₁ Y₂ : Subgroup G} (hU : Y₁ ⊔ Y₂ = U) (hinf : Y₁ ⊓ Y₂ = ⊥)
    (hcomm : ∀ a ∈ Y₁, ∀ b ∈ Y₂, a * b = b * a)
    (hCA₁ : ∀ y ∈ Y₁, (∃ z ∈ Y₁, y * z ≠ z * y) →
      ∀ c ∈ Y₁, ∀ c' ∈ Y₁, c * y = y * c → c' * y = y * c' → c * c' = c' * c)
    (hCA₂ : ∀ y ∈ Y₂, (∃ z ∈ Y₂, y * z ≠ z * y) →
      ∀ c ∈ Y₂, ∀ c' ∈ Y₂, c * y = y * c → c' * y = y * c' → c * c' = c' * c)
    (hna₂ : ∃ c ∈ Y₂, ∃ c' ∈ Y₂, c * c' ≠ c' * c) {h : G}
    (hh : h ∈ normalizer (U : Set G)) :
    (U ⊓ centralizer (Y₂ : Set G)).map (MulAut.conj h).toMonoidHom ≤
        U ⊓ centralizer (Y₂ : Set G) ∨
      (U ⊓ centralizer (Y₂ : Set G)).map (MulAut.conj h).toMonoidHom ≤
        U ⊓ centralizer (Y₁ : Set G) := by
  subst hU
  rw [← SubgroupClass.subset_union]
  rintro _ ⟨m, hm, rfl⟩
  obtain ⟨hmU, hmC⟩ := mem_inf.mp hm
  obtain ⟨c, hc, c', hc', hcc'⟩ := hna₂
  have hmU' : h * m * h⁻¹ ∈ Y₁ ⊔ Y₂ := (mem_normalizer_iff.mp hh m).mp hmU
  have hcU : h * c * h⁻¹ ∈ Y₁ ⊔ Y₂ := (mem_normalizer_iff.mp hh c).mp (mem_sup_right hc)
  have hc'U : h * c' * h⁻¹ ∈ Y₁ ⊔ Y₂ := (mem_normalizer_iff.mp hh c').mp (mem_sup_right hc')
  have hcm : c * m = m * c := mem_centralizer_iff.mp hmC c hc
  have hc'm : c' * m = m * c' := mem_centralizer_iff.mp hmC c' hc'
  have key := mem_centralizer_or_of_not_comm hinf hcomm hCA₁ hCA₂ hmU' hcU hc'U
    (by
      calc h * c * h⁻¹ * (h * m * h⁻¹) = h * (c * m) * h⁻¹ := by group
        _ = h * (m * c) * h⁻¹ := by rw [hcm]
        _ = h * m * h⁻¹ * (h * c * h⁻¹) := by group)
    (by
      calc h * c' * h⁻¹ * (h * m * h⁻¹) = h * (c' * m) * h⁻¹ := by group
        _ = h * (m * c') * h⁻¹ := by rw [hc'm]
        _ = h * m * h⁻¹ * (h * c' * h⁻¹) := by group)
    (by
      intro e
      apply hcc'
      have e' : h * (c * c') * h⁻¹ = h * (c' * c) * h⁻¹ := by
        calc h * (c * c') * h⁻¹ = h * c * h⁻¹ * (h * c' * h⁻¹) := by group
          _ = h * c' * h⁻¹ * (h * c * h⁻¹) := e
          _ = h * (c' * c) * h⁻¹ := by group
      exact mul_left_cancel (mul_right_cancel e'))
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, Set.mem_union, SetLike.mem_coe]
  rcases key with h1 | h1
  · exact Or.inl (mem_inf.mpr ⟨hmU', h1⟩)
  · exact Or.inr (mem_inf.mpr ⟨hmU', h1⟩)

theorem map_conj_mul_eq (K : Subgroup G) (a b : G) :
    K.map (MulAut.conj (a * b)).toMonoidHom =
      (K.map (MulAut.conj b).toMonoidHom).map (MulAut.conj a).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply, mul_assoc]

theorem mem_normalizer_iff_map_conj_eq' {K : Subgroup G} {h : G} :
    h ∈ normalizer (K : Set G) ↔ K.map (MulAut.conj h).toMonoidHom = K := by
  rw [MulEquiv.toMonoidHom_eq_coe]
  exact mem_normalizer_iff_map_conj_eq

theorem map_conj_eq_of_le_of_card_eq [Finite G] {K K' : Subgroup G}
    (hKK' : Nat.card K = Nat.card K') {h : G} (hle : K.map (MulAut.conj h).toMonoidHom ≤ K') :
    K.map (MulAut.conj h).toMonoidHom = K' := by
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  rw [Subgroup.card_map_of_injective (MulAut.conj h).injective, hKK']

theorem map_conj_eq_or_eq [Finite G] {U Y₁ Y₂ : Subgroup G} (hU : Y₁ ⊔ Y₂ = U)
    (hinf : Y₁ ⊓ Y₂ = ⊥) (hcomm : ∀ a ∈ Y₁, ∀ b ∈ Y₂, a * b = b * a)
    (hCA₁ : ∀ y ∈ Y₁, (∃ z ∈ Y₁, y * z ≠ z * y) →
      ∀ c ∈ Y₁, ∀ c' ∈ Y₁, c * y = y * c → c' * y = y * c' → c * c' = c' * c)
    (hCA₂ : ∀ y ∈ Y₂, (∃ z ∈ Y₂, y * z ≠ z * y) →
      ∀ c ∈ Y₂, ∀ c' ∈ Y₂, c * y = y * c → c' * y = y * c' → c * c' = c' * c)
    (hna₁ : ∃ c ∈ Y₁, ∃ c' ∈ Y₁, c * c' ≠ c' * c) (hna₂ : ∃ c ∈ Y₂, ∃ c' ∈ Y₂, c * c' ≠ c' * c)
    {t : G} (htt : t * t = 1) (htU : t ∈ normalizer (U : Set G))
    (ht₁ : ∀ a ∈ Y₁, t * a * t⁻¹ ∈ Y₂) (ht₂ : ∀ b ∈ Y₂, t * b * t⁻¹ ∈ Y₁) :
    U ⊓ centralizer (Y₂ : Set G) ≠ U ⊓ centralizer (Y₁ : Set G) ∧
      (U ⊓ centralizer (Y₂ : Set G)).map (MulAut.conj t).toMonoidHom =
        U ⊓ centralizer (Y₁ : Set G) ∧
      ∀ h ∈ normalizer (U : Set G),
        ((U ⊓ centralizer (Y₂ : Set G)).map (MulAut.conj h).toMonoidHom =
            U ⊓ centralizer (Y₂ : Set G) ∧
          (U ⊓ centralizer (Y₁ : Set G)).map (MulAut.conj h).toMonoidHom =
            U ⊓ centralizer (Y₁ : Set G)) ∨
        ((U ⊓ centralizer (Y₂ : Set G)).map (MulAut.conj h).toMonoidHom =
            U ⊓ centralizer (Y₁ : Set G) ∧
          (U ⊓ centralizer (Y₁ : Set G)).map (MulAut.conj h).toMonoidHom =
            U ⊓ centralizer (Y₂ : Set G)) := by
  set M₁ := U ⊓ centralizer (Y₂ : Set G) with hM₁
  set M₂ := U ⊓ centralizer (Y₁ : Set G) with hM₂
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
  have hne : M₁ ≠ M₂ := by
    obtain ⟨c, hc, c', hc', hcc'⟩ := hna₁
    intro e
    have hcM : c ∈ M₁ := mem_inf.mpr ⟨hU ▸ mem_sup_left hc,
      mem_centralizer_iff.mpr fun b hb => (hcomm c hc b hb).symm⟩
    rw [e] at hcM
    exact hcc' (mem_centralizer_iff.mp (mem_inf.mp hcM).2 c' hc').symm
  have hswap : ∀ {X₁ X₂ : Subgroup G}, (∀ a ∈ X₁, t * a * t⁻¹ ∈ X₂) →
      (U ⊓ centralizer (X₂ : Set G)).map (MulAut.conj t).toMonoidHom ≤
        U ⊓ centralizer (X₁ : Set G) := by
    intro X₁ X₂ hX
    rintro _ ⟨m, hm, rfl⟩
    obtain ⟨hmU, hmC⟩ := mem_inf.mp hm
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    refine mem_inf.mpr ⟨(mem_normalizer_iff.mp htU m).mp hmU,
      mem_centralizer_iff.mpr fun a ha => ?_⟩
    have hb : t * a * t⁻¹ ∈ X₂ := hX a ha
    have hbm : t * a * t⁻¹ * m = m * (t * a * t⁻¹) := mem_centralizer_iff.mp hmC _ hb
    calc a * (t * m * t⁻¹) = t * ((t⁻¹ * a * t) * m) * t⁻¹ := by group
      _ = t * ((t * a * t⁻¹) * m) * t⁻¹ := by rw [htinv]
      _ = t * (m * (t * a * t⁻¹)) * t⁻¹ := by rw [hbm]
      _ = t * (m * (t⁻¹ * a * t)) * t⁻¹ := by rw [htinv]
      _ = t * m * t⁻¹ * a := by group
  have h12 : M₁.map (MulAut.conj t).toMonoidHom ≤ M₂ := hswap ht₁
  have h21 : M₂.map (MulAut.conj t).toMonoidHom ≤ M₁ := hswap ht₂
  have hcard : Nat.card M₁ = Nat.card M₂ := by
    apply le_antisymm
    · have := Subgroup.card_le_of_le h12
      rwa [Subgroup.card_map_of_injective (MulAut.conj t).injective] at this
    · have := Subgroup.card_le_of_le h21
      rwa [Subgroup.card_map_of_injective (MulAut.conj t).injective] at this
  have htM : M₁.map (MulAut.conj t).toMonoidHom = M₂ := map_conj_eq_of_le_of_card_eq hcard h12
  refine ⟨hne, htM, fun h hh => ?_⟩
  have hinj : Function.Injective (Subgroup.map (MulAut.conj h).toMonoidHom) :=
    Subgroup.map_injective (MulAut.conj h).injective
  have hU' : Y₂ ⊔ Y₁ = U := by rw [sup_comm]; exact hU
  have hinf' : Y₂ ⊓ Y₁ = ⊥ := by rw [inf_comm]; exact hinf
  have hcomm' : ∀ a ∈ Y₂, ∀ b ∈ Y₁, a * b = b * a := fun a ha b hb => (hcomm b hb a ha).symm
  rcases map_conj_le_or_le hU hinf hcomm hCA₁ hCA₂ hna₂ hh with h1 | h1 <;>
    rcases map_conj_le_or_le hU' hinf' hcomm' hCA₂ hCA₁ hna₁ hh with h2 | h2
  · exact Or.inl ⟨map_conj_eq_of_le_of_card_eq rfl h1, map_conj_eq_of_le_of_card_eq rfl h2⟩
  · exact absurd (hinj ((map_conj_eq_of_le_of_card_eq rfl h1).trans
      (map_conj_eq_of_le_of_card_eq hcard.symm h2).symm)) hne
  · exact absurd (hinj ((map_conj_eq_of_le_of_card_eq hcard h1).trans
      (map_conj_eq_of_le_of_card_eq rfl h2).symm)) hne
  · exact Or.inr ⟨map_conj_eq_of_le_of_card_eq hcard h1,
      map_conj_eq_of_le_of_card_eq hcard.symm h2⟩

theorem relIndex_inf_normalizer_eq_two [Finite G] {U Y₁ Y₂ : Subgroup G} (hU : Y₁ ⊔ Y₂ = U)
    (hinf : Y₁ ⊓ Y₂ = ⊥) (hcomm : ∀ a ∈ Y₁, ∀ b ∈ Y₂, a * b = b * a)
    (hCA₁ : ∀ y ∈ Y₁, (∃ z ∈ Y₁, y * z ≠ z * y) →
      ∀ c ∈ Y₁, ∀ c' ∈ Y₁, c * y = y * c → c' * y = y * c' → c * c' = c' * c)
    (hCA₂ : ∀ y ∈ Y₂, (∃ z ∈ Y₂, y * z ≠ z * y) →
      ∀ c ∈ Y₂, ∀ c' ∈ Y₂, c * y = y * c → c' * y = y * c' → c * c' = c' * c)
    (hna₁ : ∃ c ∈ Y₁, ∃ c' ∈ Y₁, c * c' ≠ c' * c) (hna₂ : ∃ c ∈ Y₂, ∃ c' ∈ Y₂, c * c' ≠ c' * c)
    {t : G} (htt : t * t = 1) (htU : t ∈ normalizer (U : Set G))
    (ht₁ : ∀ a ∈ Y₁, t * a * t⁻¹ ∈ Y₂) (ht₂ : ∀ b ∈ Y₂, t * b * t⁻¹ ∈ Y₁) {P : Subgroup G}
    (hPU : P ≤ normalizer (U : Set G)) (htP : t ∈ P) :
    (P ⊓ normalizer ((U ⊓ centralizer (Y₂ : Set G) : Subgroup G) : Set G)).relIndex P = 2 ∧
      t ∉ P ⊓ normalizer ((U ⊓ centralizer (Y₂ : Set G) : Subgroup G) : Set G) := by
  obtain ⟨hne, htM, hdich⟩ :=
    map_conj_eq_or_eq hU hinf hcomm hCA₁ hCA₂ hna₁ hna₂ htt htU ht₁ ht₂
  refine ⟨?_, fun htQ => hne ?_⟩
  · rw [relIndex_eq_two_iff]
    refine ⟨t, htP, fun b hb => ?_⟩
    rcases hdich b (hPU hb) with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · refine Or.inr ⟨mem_inf.mpr ⟨hb, mem_normalizer_iff_map_conj_eq'.mpr h1⟩, fun hbt => hne ?_⟩
      have e := mem_normalizer_iff_map_conj_eq'.mp (mem_inf.mp hbt).2
      rw [map_conj_mul_eq, htM, h2] at e
      exact e.symm
    · refine Or.inl ⟨mem_inf.mpr ⟨mul_mem hb htP, mem_normalizer_iff_map_conj_eq'.mpr ?_⟩,
        fun hbQ => hne ?_⟩
      · rw [map_conj_mul_eq, htM, h2]
      · have e := mem_normalizer_iff_map_conj_eq'.mp (mem_inf.mp hbQ).2
        rw [h1] at e
        exact e.symm
  · have e := mem_normalizer_iff_map_conj_eq'.mp (mem_inf.mp htQ).2
    rw [htM] at e
    exact e.symm

end CFSG.SeitzReduction.RankOne
