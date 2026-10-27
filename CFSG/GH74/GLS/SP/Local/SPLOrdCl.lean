module

public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.Tactic.Group

public section

namespace CFSG.GH74.GLS.SP.Local

private theorem card_eq_two_mul_card_range {α β : Type*} [Finite α] (f : α → β)
    (hf : ∀ a, ∃ b, b ≠ a ∧ ∀ c, f c = f a ↔ c = a ∨ c = b) :
    Nat.card α = 2 * Nat.card (Set.range f) := by
  classical
  have _ : Fintype (Set.range f) := Fintype.ofFinite _
  let g : α → Set.range f := fun a => ⟨f a, a, rfl⟩
  have hfib : ∀ y : Set.range f, Nat.card {a : α // g a = y} = 2 := by
    rintro ⟨_, a, rfl⟩
    obtain ⟨b, hb, hab⟩ := hf a
    have h1 : Nat.card {a' : α // g a' = g a} = Nat.card ↥({a, b} : Set α) :=
      Nat.card_congr (Equiv.subtypeEquivRight fun a' => by
        rw [Subtype.ext_iff]
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
        exact hab a')
    rw [h1, Nat.card_coe_set_eq, Set.ncard_pair hb.symm]
  rw [← Nat.card_congr (Equiv.sigmaFiberEquiv g), Nat.card_sigma]
  simp only [hfib, Finset.sum_const, Finset.card_univ, smul_eq_mul]
  rw [mul_comm, Nat.card_eq_fintype_card]

section Setting

variable {X : Type} [Group X]

private lemma zmem_left {K₁ K₂ : Subgroup X} {z : X} (hinf : K₁ ⊓ K₂ = Subgroup.zpowers z) :
    z ∈ K₁ := by
  have h : z ∈ K₁ ⊓ K₂ := by rw [hinf]; exact Subgroup.mem_zpowers z
  exact h.1

private lemma zmem_right {K₁ K₂ : Subgroup X} {z : X} (hinf : K₁ ⊓ K₂ = Subgroup.zpowers z) :
    z ∈ K₂ := by
  have h : z ∈ K₁ ⊓ K₂ := by rw [hinf]; exact Subgroup.mem_zpowers z
  exact h.2

private lemma zsq {z : X} (hz2 : orderOf z = 2) : z * z = 1 := by
  rw [← sq, ← hz2]
  exact pow_orderOf_eq_one z

private lemma zne {z : X} (hz2 : orderOf z = 2) : z ≠ 1 := by
  rintro rfl
  rw [orderOf_one] at hz2
  exact absurd hz2 (by decide)

private lemma zinv {z : X} (hz2 : orderOf z = 2) : z⁻¹ = z :=
  inv_eq_of_mul_eq_one_right (zsq hz2)

private lemma mem_inf_cases {K₁ K₂ : Subgroup X} {z : X} (hinf : K₁ ⊓ K₂ = Subgroup.zpowers z)
    (hz2 : orderOf z = 2) {x : X} (h₁ : x ∈ K₁) (h₂ : x ∈ K₂) : x = 1 ∨ x = z := by
  have hx : x ∈ Subgroup.zpowers z := by rw [← hinf]; exact ⟨h₁, h₂⟩
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  have h2 := zpow_mod_orderOf z n
  rw [hz2] at h2
  rcases Int.emod_two_eq_zero_or_one n with h | h
  · left
    rw [← h2]
    simp [h]
  · right
    rw [← h2]
    simp [h]

private lemma mem_sup_iff {K₁ K₂ : Subgroup X} (hcomm : ∀ a ∈ K₁, ∀ b ∈ K₂, a * b = b * a)
    {x : X} : x ∈ K₁ ⊔ K₂ ↔ ∃ a ∈ K₁, ∃ b ∈ K₂, a * b = x := by
  have hLE : K₁ ≤ Subgroup.normalizer (K₂ : Set X) := by
    intro a ha
    rw [Subgroup.mem_normalizer_iff]
    intro b
    constructor
    · intro hb
      rw [hcomm a ha b hb, mul_inv_cancel_right]
      exact hb
    · intro hb
      have hc : a * (a * b * a⁻¹) = (a * b * a⁻¹) * a := hcomm a ha _ hb
      have h2 : a * (a * b * a⁻¹) = a * b := by rw [hc, inv_mul_cancel_right]
      have h3 : a * b * a⁻¹ = b := mul_left_cancel h2
      rwa [h3] at hb
  have h := Subgroup.coe_mul_of_left_le_normalizer_right K₁ K₂ hLE
  rw [← SetLike.mem_coe, h, Set.mem_mul]
  rfl

private lemma conjClass_card [Finite X] {K₁ K₂ : Subgroup X} {z s : X}
    (hinf : K₁ ⊓ K₂ = Subgroup.zpowers z) (hz2 : orderOf z = 2)
    (hzs : z * s = s * z) (hs₁ : ∀ a ∈ K₁, s * a * s⁻¹ ∈ K₂) :
    2 * Nat.card {a : X // ∃ g ∈ K₁, a = g * s * g⁻¹} = Nat.card K₁ := by
  classical
  have hz₁ : z ∈ K₁ := zmem_left hinf
  let z₁ : K₁ := ⟨z, hz₁⟩
  let f : K₁ → X := fun g => (g : X) * s * (g : X)⁻¹
  have hf : ∀ g : K₁, ∃ b, b ≠ g ∧ ∀ c, f c = f g ↔ c = g ∨ c = b := by
    intro g
    refine ⟨g * z₁, ?_, ?_⟩
    · intro h
      have h1 : (g : X) * z = g := congrArg Subtype.val h
      exact zne hz2 (mul_eq_left.mp h1)
    · intro g'
      constructor
      · intro e
        have e' : (g' : X) * s * (g' : X)⁻¹ = g * s * (g : X)⁻¹ := e
        have key : ((g : X)⁻¹ * g') * s = s * ((g : X)⁻¹ * g') := by
          calc ((g : X)⁻¹ * g') * s = (g : X)⁻¹ * ((g' : X) * s * (g' : X)⁻¹) * g' := by group
            _ = (g : X)⁻¹ * ((g : X) * s * (g : X)⁻¹) * g' := by rw [e']
            _ = s * ((g : X)⁻¹ * g') := by group
        have hh₁ : ((g : X)⁻¹ * g') ∈ K₁ := mul_mem (inv_mem g.2) g'.2
        have hh₂ : ((g : X)⁻¹ * g') ∈ K₂ := by
          have h1 : s * ((g : X)⁻¹ * g') * s⁻¹ = (g : X)⁻¹ * g' := by
            rw [← key, mul_inv_cancel_right]
          rw [← h1]
          exact hs₁ _ hh₁
        rcases mem_inf_cases hinf hz2 hh₁ hh₂ with h1 | h1
        · left
          exact Subtype.ext (inv_mul_eq_one.mp h1).symm
        · right
          exact Subtype.ext (inv_mul_eq_iff_eq_mul.mp h1)
      · rintro (rfl | rfl)
        · rfl
        · show ((g * z₁ : K₁) : X) * s * ((g * z₁ : K₁) : X)⁻¹ = g * s * (g : X)⁻¹
          calc (g : X) * z * s * ((g : X) * z)⁻¹
              = (g : X) * (z * s) * z⁻¹ * (g : X)⁻¹ := by group
            _ = (g : X) * (s * z) * z⁻¹ * (g : X)⁻¹ := by rw [hzs]
            _ = (g : X) * s * (g : X)⁻¹ := by group
  have h := card_eq_two_mul_card_range f hf
  have hr : Nat.card {a : X // ∃ g ∈ K₁, a = g * s * g⁻¹} = Nat.card (Set.range f) :=
    Nat.card_congr (Equiv.subtypeEquivRight fun a => by
      constructor
      · rintro ⟨g, hg, rfl⟩
        exact ⟨⟨g, hg⟩, rfl⟩
      · rintro ⟨g, rfl⟩
        exact ⟨g, g.2, rfl⟩)
  rw [hr, ← h]

private lemma card_sq_eq {K₁ K₂ : Subgroup X} {z t : X} (ht2 : t * t = 1) (htz : z * t = t * z)
    (ht₁ : ∀ a ∈ K₁, t * a * t⁻¹ ∈ K₂) (ht₂ : ∀ b ∈ K₂, t * b * t⁻¹ ∈ K₁) :
    Nat.card {v : K₂ // (v : X) * v = z} = Nat.card {u : K₁ // (u : X) * u = z} := by
  have htz' : t * z * t⁻¹ = z := by rw [← htz, mul_inv_cancel_right]
  have hsq : ∀ x : X, x * x = z → (t * x * t⁻¹) * (t * x * t⁻¹) = z := fun x hx => by
    calc (t * x * t⁻¹) * (t * x * t⁻¹) = t * (x * x) * t⁻¹ := by group
      _ = z := by rw [hx, htz']
  have hinv : ∀ x : X, t * (t * x * t⁻¹) * t⁻¹ = x := fun x => by
    calc t * (t * x * t⁻¹) * t⁻¹ = (t * t) * x * (t * t)⁻¹ := by group
      _ = x := by rw [ht2]; group
  exact Nat.card_congr
    { toFun := fun v => ⟨⟨t * (v : X) * t⁻¹, ht₂ _ v.1.2⟩, hsq _ v.2⟩
      invFun := fun u => ⟨⟨t * (u : X) * t⁻¹, ht₁ _ u.1.2⟩, hsq _ u.2⟩
      left_inv := fun v => Subtype.ext (Subtype.ext (hinv _))
      right_inv := fun u => Subtype.ext (Subtype.ext (hinv _)) }

private lemma sq_mul_z {u z : X} (hc : u * z = z * u) (hz : z * z = 1) :
    (u * z) * (u * z) = u * u := by
  calc (u * z) * (u * z) = u * (z * u) * z := by group
    _ = u * (u * z) * z := by rw [hc]
    _ = u * u * (z * z) := by group
    _ = u * u := by rw [hz, mul_one]

private lemma pair_eq {K₁ K₂ : Subgroup X} {z : X} (hinf : K₁ ⊓ K₂ = Subgroup.zpowers z)
    (hz2 : orderOf z = 2) (hzc : ∀ b ∈ K₂, z * b = b * z)
    {u u' v v' : X} (hu : u ∈ K₁) (hu' : u' ∈ K₁) (hv : v ∈ K₂) (hv' : v' ∈ K₂)
    (h : u' * v' = u * v) : (u' = u ∧ v' = v) ∨ (u' = u * z ∧ v' = v * z) := by
  have hm : u⁻¹ * u' = v * v'⁻¹ := by
    calc u⁻¹ * u' = u⁻¹ * (u' * v') * v'⁻¹ := by group
      _ = u⁻¹ * (u * v) * v'⁻¹ := by rw [h]
      _ = v * v'⁻¹ := by group
  have hm₁ : u⁻¹ * u' ∈ K₁ := mul_mem (inv_mem hu) hu'
  have hm₂ : u⁻¹ * u' ∈ K₂ := by rw [hm]; exact mul_mem hv (inv_mem hv')
  rcases mem_inf_cases hinf hz2 hm₁ hm₂ with h1 | h1
  · left
    have hu1 : u' = u := (inv_mul_eq_one.mp h1).symm
    refine ⟨hu1, ?_⟩
    rw [hu1] at h
    exact mul_left_cancel h
  · right
    refine ⟨inv_mul_eq_iff_eq_mul.mp h1, ?_⟩
    have e0 : v * v'⁻¹ = z := by rw [← hm]; exact h1
    have e : v = z * v' := mul_inv_eq_iff_eq_mul.mp e0
    have e1 : v' = z * v := by
      rw [e, ← mul_assoc, zsq hz2, one_mul]
    exact e1.trans (hzc v hv)

private lemma prod_mem {K₁ K₂ : Subgroup X} {z : X} (hcomm : ∀ a ∈ K₁, ∀ b ∈ K₂, a * b = b * a)
    (hinf : K₁ ⊓ K₂ = Subgroup.zpowers z) (hz2 : orderOf z = 2)
    {u v : X} (hu : u ∈ K₁) (hv : v ∈ K₂) (hu2 : u * u = z) (hv2 : v * v = z) :
    u * v ∈ K₁ ⊔ K₂ ∧ (u * v) * (u * v) = 1 ∧ u * v ≠ 1 ∧ u * v ≠ z := by
  have hz₂ : z ∈ K₂ := zmem_right hinf
  have hbad : u ∉ K₂ := by
    intro huK₂
    rcases mem_inf_cases hinf hz2 hu huK₂ with h | h
    · rw [h, mul_one] at hu2
      exact zne hz2 hu2.symm
    · rw [h, zsq hz2] at hu2
      exact zne hz2 hu2.symm
  refine ⟨mul_mem (Subgroup.mem_sup_left hu) (Subgroup.mem_sup_right hv), ?_, ?_, ?_⟩
  · calc u * v * (u * v) = u * (v * u) * v := by group
      _ = u * (u * v) * v := by rw [← hcomm u hu v hv]
      _ = (u * u) * (v * v) := by group
      _ = 1 := by rw [hu2, hv2, zsq hz2]
  · intro h
    apply hbad
    rw [eq_inv_of_mul_eq_one_left h]
    exact inv_mem hv
  · intro h
    apply hbad
    rw [eq_mul_inv_of_mul_eq h]
    exact mul_mem hz₂ (inv_mem hv)

private lemma prod_decomp {K₁ K₂ : Subgroup X} {z t : X}
    (hcomm : ∀ a ∈ K₁, ∀ b ∈ K₂, a * b = b * a)
    (hinf : K₁ ⊓ K₂ = Subgroup.zpowers z) (hz2 : orderOf z = 2)
    (htz : z * t = t * z) (ht₂ : ∀ b ∈ K₂, t * b * t⁻¹ ∈ K₁)
    (hK₁inv : ∀ a ∈ K₁, a * a = 1 → a = 1 ∨ a = z)
    {a : X} (ha : a ∈ K₁ ⊔ K₂) (ha2 : a * a = 1) (ha1 : a ≠ 1) (haz : a ≠ z) :
    ∃ u ∈ K₁, ∃ v ∈ K₂, u * u = z ∧ v * v = z ∧ u * v = a := by
  obtain ⟨a₁, h₁, a₂, h₂, rfl⟩ := (mem_sup_iff hcomm).mp ha
  have hsq : (a₁ * a₁) * (a₂ * a₂) = 1 := by
    calc (a₁ * a₁) * (a₂ * a₂) = a₁ * (a₁ * a₂) * a₂ := by group
      _ = a₁ * (a₂ * a₁) * a₂ := by rw [hcomm a₁ h₁ a₂ h₂]
      _ = a₁ * a₂ * (a₁ * a₂) := by group
      _ = 1 := ha2
  have hmem₂ : a₁ * a₁ ∈ K₂ := by
    rw [eq_inv_of_mul_eq_one_left hsq]
    exact inv_mem (mul_mem h₂ h₂)
  rcases mem_inf_cases hinf hz2 (mul_mem h₁ h₁) hmem₂ with hs | hs
  ·
    exfalso
    have hs2 : a₂ * a₂ = 1 := by
      rw [hs, one_mul] at hsq
      exact hsq
    have hta : (t * a₂ * t⁻¹) * (t * a₂ * t⁻¹) = 1 := by
      calc (t * a₂ * t⁻¹) * (t * a₂ * t⁻¹) = t * (a₂ * a₂) * t⁻¹ := by group
        _ = 1 := by rw [hs2]; group
    have hd : a₂ = 1 ∨ a₂ = z := by
      rcases hK₁inv _ (ht₂ a₂ h₂) hta with hc | hc
      · left
        calc a₂ = t⁻¹ * (t * a₂ * t⁻¹) * t := by group
          _ = t⁻¹ * 1 * t := by rw [hc]
          _ = 1 := by group
      · right
        calc a₂ = t⁻¹ * (t * a₂ * t⁻¹) * t := by group
          _ = t⁻¹ * z * t := by rw [hc]
          _ = t⁻¹ * (z * t) := by group
          _ = t⁻¹ * (t * z) := by rw [htz]
          _ = z := by group
    rcases hK₁inv a₁ h₁ hs with hc | hc <;> rcases hd with hd | hd
    · exact ha1 (by rw [hc, hd, one_mul])
    · exact haz (by rw [hc, hd, one_mul])
    · exact haz (by rw [hc, hd, mul_one])
    · exact ha1 (by rw [hc, hd, zsq hz2])
  · refine ⟨a₁, h₁, a₂, h₂, hs, ?_, rfl⟩
    rw [hs] at hsq
    calc a₂ * a₂ = z⁻¹ * (z * (a₂ * a₂)) := by group
      _ = z⁻¹ := by rw [hsq]; group
      _ = z := zinv hz2

end Setting

theorem tclass_card {X : Type} [Group X] [Finite X] (K₁ K₂ : Subgroup X) (z t : X)
    (hcomm : ∀ a ∈ K₁, ∀ b ∈ K₂, a * b = b * a)
    (hinf : K₁ ⊓ K₂ = Subgroup.zpowers z) (hz2 : orderOf z = 2)
    (ht2 : t * t = 1) (htz : z * t = t * z) (htK : t ∉ K₁ ⊔ K₂)
    (ht₁ : ∀ a ∈ K₁, t * a * t⁻¹ ∈ K₂) (ht₂ : ∀ b ∈ K₂, t * b * t⁻¹ ∈ K₁) :
    2 * Nat.card {a : X // ∃ g ∈ K₁, a = g * t * g⁻¹} = Nat.card K₁ := by
  have _ := hcomm
  have _ := ht2
  have _ := htK
  have _ := ht₂
  exact conjClass_card hinf hz2 htz ht₁

theorem Jone_card {X : Type} [Group X] [Finite X] (K₁ K₂ : Subgroup X) (z t : X)
    (hcomm : ∀ a ∈ K₁, ∀ b ∈ K₂, a * b = b * a)
    (hinf : K₁ ⊓ K₂ = Subgroup.zpowers z) (hz2 : orderOf z = 2)
    (ht2 : t * t = 1) (htz : z * t = t * z) (htK : t ∉ K₁ ⊔ K₂)
    (ht₁ : ∀ a ∈ K₁, t * a * t⁻¹ ∈ K₂) (ht₂ : ∀ b ∈ K₂, t * b * t⁻¹ ∈ K₁)
    (hK₁inv : ∀ a ∈ K₁, a * a = 1 → a = 1 ∨ a = z) :
    2 * Nat.card {a : X // a ∈ K₁ ⊔ K₂ ∧ a * a = 1 ∧ a ≠ 1 ∧ a ≠ z} =
      Nat.card {u : K₁ // (u : X) * u = z} ^ 2 := by
  have _ := htK
  classical
  have hz₁ : z ∈ K₁ := zmem_left hinf
  have hz₂ : z ∈ K₂ := zmem_right hinf
  have hzc : ∀ b ∈ K₂, z * b = b * z := fun b hb => hcomm z hz₁ b hb
  let μ : {u : K₁ // (u : X) * u = z} × {v : K₂ // (v : X) * v = z} → X :=
    fun w => ((w.1 : K₁) : X) * ((w.2 : K₂) : X)
  have hfib : ∀ w, ∃ w', w' ≠ w ∧ ∀ c, μ c = μ w ↔ c = w ∨ c = w' := by
    rintro ⟨⟨⟨u, hu⟩, hu2⟩, ⟨⟨v, hv⟩, hv2⟩⟩
    have hu2' : u * u = z := hu2
    have hv2' : v * v = z := hv2
    have huz : (u * z) * (u * z) = z := by
      rw [sq_mul_z (hcomm u hu z hz₂) (zsq hz2)]; exact hu2'
    have hvz : (v * z) * (v * z) = z := by
      rw [sq_mul_z (hzc v hv).symm (zsq hz2)]; exact hv2'
    refine ⟨(⟨⟨u * z, mul_mem hu hz₁⟩, huz⟩, ⟨⟨v * z, mul_mem hv hz₂⟩, hvz⟩), ?_, ?_⟩
    · intro h
      have h1 : u * z = u :=
        congrArg (fun w : {u : K₁ // (u : X) * u = z} × {v : K₂ // (v : X) * v = z} =>
          ((w.1 : K₁) : X)) h
      exact zne hz2 (mul_eq_left.mp h1)
    · intro c
      constructor
      · obtain ⟨⟨⟨u', hu'⟩, hu2''⟩, ⟨⟨v', hv'⟩, hv2''⟩⟩ := c
        intro h
        have h' : u' * v' = u * v := h
        rcases pair_eq hinf hz2 hzc hu hu' hv hv' h' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · left; rfl
        · right; rfl
      · rintro (rfl | rfl)
        · rfl
        · show u * z * (v * z) = u * v
          calc u * z * (v * z) = u * (z * v) * z := by group
            _ = u * (v * z) * z := by rw [hzc v hv]
            _ = u * v * (z * z) := by group
            _ = u * v := by rw [zsq hz2, mul_one]
  have hrange : ∀ a : X, (a ∈ K₁ ⊔ K₂ ∧ a * a = 1 ∧ a ≠ 1 ∧ a ≠ z) ↔ a ∈ Set.range μ := by
    intro a
    constructor
    · rintro ⟨ha, ha2, ha1, haz⟩
      obtain ⟨u, hu, v, hv, hu2, hv2, rfl⟩ :=
        prod_decomp hcomm hinf hz2 htz ht₂ hK₁inv ha ha2 ha1 haz
      exact ⟨(⟨⟨u, hu⟩, hu2⟩, ⟨⟨v, hv⟩, hv2⟩), rfl⟩
    · rintro ⟨⟨⟨⟨u, hu⟩, hu2⟩, ⟨⟨v, hv⟩, hv2⟩⟩, rfl⟩
      exact prod_mem hcomm hinf hz2 hu hv hu2 hv2
  have h1 := card_eq_two_mul_card_range μ hfib
  have h2 : Nat.card {a : X // a ∈ K₁ ⊔ K₂ ∧ a * a = 1 ∧ a ≠ 1 ∧ a ≠ z} =
      Nat.card (Set.range μ) := Nat.card_congr (Equiv.subtypeEquivRight hrange)
  have h3 := card_sq_eq ht2 htz ht₁ ht₂
  rw [h2, ← h1, Nat.card_prod, h3, sq]

end CFSG.GH74.GLS.SP.Local
