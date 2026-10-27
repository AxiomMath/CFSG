module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherKnownGroupLemma37Basic
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherKnownGroupLemma38

public section

namespace CFSG.ComponentClassification.AschbacherKnownGroup

open CFSG.Open Subgroup

namespace Lemma37

variable {G : Type*} [Group G]

theorem mul_inv_mem_of_relIndex_le_two [Finite G] {S M : Subgroup G}
    (hidx : M.relIndex S ≤ 2) {u v : G} (hu : u ∈ S) (hv : v ∈ S) (huM : u ∉ M)
    (hvM : v ∉ M) : u * v⁻¹ ∈ M := by
  have h0 : M.relIndex S ≠ 0 := by
    intro h
    have := Subgroup.relIndex_mul_card (H := M) (K := S)
    rw [h, zero_mul] at this
    exact Nat.card_pos.ne' this.symm
  rcases (by omega : M.relIndex S = 1 ∨ M.relIndex S = 2) with h1 | h2
  · exact absurd (relIndex_eq_one.1 h1 hu) huM
  · obtain ⟨a, haS, ha⟩ := relIndex_eq_two_iff.1 h2
    have hua : u * a ∈ M := by
      rcases ha u hu with h | h
      · exact h.1
      · exact absurd h.1 huM
    have hva : v * a ∈ M := by
      rcases ha v hv with h | h
      · exact h.1
      · exact absurd h.1 hvM
    have := M.mul_mem hua (M.inv_mem hva)
    simpa [mul_assoc] using this

theorem comm_of_not_le [Finite G] {S M Y U : Subgroup G}
    (hidx : M.relIndex S ≤ 2) (hMab : ∀ a ∈ M, ∀ b ∈ M, a * b = b * a) (hYS : Y ≤ S)
    (hUS : U ≤ S) (hYU : ∀ y ∈ Y, ∀ u ∈ U, y * u = u * y) (hY : ¬ Y ≤ M) (hU : ¬ U ≤ M) :
    ∀ a ∈ U, ∀ b ∈ U, a * b = b * a := by
  obtain ⟨y₀, hy₀Y, hy₀M⟩ := Set.not_subset.1 hY
  obtain ⟨u₀, hu₀U, hu₀M⟩ := Set.not_subset.1 hU
  have hu₀iM : u₀⁻¹ ∉ M := fun h => hu₀M (by simpa using M.inv_mem h)
  have hyu : y₀ * u₀ ∈ M := by
    have := mul_inv_mem_of_relIndex_le_two hidx (hYS hy₀Y) (S.inv_mem (hUS hu₀U))
      hy₀M hu₀iM
    simpa using this
  have hcen : ∀ b ∈ U, b ∈ M → b * u₀ = u₀ * b := by
    intro b hbU hbM
    have h1 := hMab b hbM _ hyu
    have h2 := hYU y₀ hy₀Y b hbU
    calc b * u₀ = y₀⁻¹ * (y₀ * b) * u₀ := by group
      _ = y₀⁻¹ * (b * y₀) * u₀ := by rw [h2]
      _ = y₀⁻¹ * (b * (y₀ * u₀)) := by group
      _ = y₀⁻¹ * ((y₀ * u₀) * b) := by rw [h1]
      _ = u₀ * b := by group
  have hform : ∀ a ∈ U, a ∈ M ∨ a * u₀⁻¹ ∈ M := by
    intro a haU
    by_cases haM : a ∈ M
    · exact Or.inl haM
    · exact Or.inr (mul_inv_mem_of_relIndex_le_two hidx (hUS haU) (hUS hu₀U) haM hu₀M)
  intro a haU b hbU
  rcases hform a haU with ha | ha <;> rcases hform b hbU with hb | hb
  · exact hMab a ha b hb
  ·
    have hbU' : b * u₀⁻¹ ∈ U := U.mul_mem hbU (U.inv_mem hu₀U)
    have e : b = (b * u₀⁻¹) * u₀ := by group
    rw [e]
    calc a * (b * u₀⁻¹ * u₀) = (a * (b * u₀⁻¹)) * u₀ := by group
      _ = ((b * u₀⁻¹) * a) * u₀ := by rw [hMab a ha _ hb]
      _ = (b * u₀⁻¹) * (a * u₀) := by group
      _ = (b * u₀⁻¹) * (u₀ * a) := by rw [hcen a haU ha]
      _ = b * u₀⁻¹ * u₀ * a := by group
  · have haU' : a * u₀⁻¹ ∈ U := U.mul_mem haU (U.inv_mem hu₀U)
    have e : a = (a * u₀⁻¹) * u₀ := by group
    rw [e]
    calc a * u₀⁻¹ * u₀ * b = (a * u₀⁻¹) * (u₀ * b) := by group
      _ = (a * u₀⁻¹) * (b * u₀) := by rw [hcen b hbU hb]
      _ = ((a * u₀⁻¹) * b) * u₀ := by group
      _ = (b * (a * u₀⁻¹)) * u₀ := by rw [hMab _ ha b hb]
      _ = b * (a * u₀⁻¹ * u₀) := by group
  · have haU' : a * u₀⁻¹ ∈ U := U.mul_mem haU (U.inv_mem hu₀U)
    have hbU' : b * u₀⁻¹ ∈ U := U.mul_mem hbU (U.inv_mem hu₀U)
    have ea : a = (a * u₀⁻¹) * u₀ := by group
    have eb : b = (b * u₀⁻¹) * u₀ := by group
    rw [ea, eb]
    set a' := a * u₀⁻¹
    set b' := b * u₀⁻¹
    calc a' * u₀ * (b' * u₀) = a' * (u₀ * b') * u₀ := by group
      _ = a' * (b' * u₀) * u₀ := by rw [hcen b' hbU' hb]
      _ = (a' * b') * (u₀ * u₀) := by group
      _ = (b' * a') * (u₀ * u₀) := by rw [hMab a' ha b' hb]
      _ = b' * (a' * u₀) * u₀ := by group
      _ = b' * (u₀ * a') * u₀ := by rw [hcen a' haU' ha]
      _ = b' * u₀ * (a' * u₀) := by group

theorem elem_sup {H : Subgroup G} {b : G} (hH : ∀ h ∈ H, h ^ 2 = 1)
    (hHab : ∀ h₁ ∈ H, ∀ h₂ ∈ H, h₁ * h₂ = h₂ * h₁) (hb : b ^ 2 = 1)
    (hbH : ∀ h ∈ H, b * h = h * b) :
    (∀ g ∈ H ⊔ zpowers b, g ^ 2 = 1) ∧
      (∀ g₁ ∈ H ⊔ zpowers b, ∀ g₂ ∈ H ⊔ zpowers b, g₁ * g₂ = g₂ * g₁) := by
  have hbN : b ∈ normalizer (H : Set G) := by
    refine Subgroup.centralizer_le_normalizer _ (mem_centralizer_iff.2 fun h hh => ?_)
    exact (hbH h hh).symm
  have hb2 : b ^ 2 ∈ H := by rw [hb]; exact one_mem H
  have hform : ∀ g ∈ H ⊔ zpowers b, ∃ h ∈ H, g = h ∨ g = b * h := by
    intro g hg
    rcases (mem_sup_zpowers_iff hbN hb2).1 hg with h | h
    · exact ⟨g, h, Or.inl rfl⟩
    · exact ⟨b⁻¹ * g, h, Or.inr (by group)⟩
  have hbb : b * b = 1 := by rw [← pow_two, hb]
  refine ⟨fun g hg => ?_, fun g₁ hg₁ g₂ hg₂ => ?_⟩
  · obtain ⟨h, hh, hgh | hgh⟩ := hform g hg <;> rw [hgh]
    · exact hH h hh
    · rw [pow_two]
      calc b * h * (b * h) = b * (h * b) * h := by group
        _ = b * (b * h) * h := by rw [hbH h hh]
        _ = (b * b) * (h * h) := by group
        _ = 1 := by rw [hbb, ← pow_two, hH h hh, one_mul]
  · obtain ⟨h₁, hh₁, hg₁h | hg₁h⟩ := hform g₁ hg₁ <;>
      obtain ⟨h₂, hh₂, hg₂h | hg₂h⟩ := hform g₂ hg₂ <;> rw [hg₁h, hg₂h]
    · exact hHab h₁ hh₁ h₂ hh₂
    · calc h₁ * (b * h₂) = b * (h₁ * h₂) := by rw [← mul_assoc, ← hbH h₁ hh₁, mul_assoc]
        _ = b * (h₂ * h₁) := by rw [hHab h₁ hh₁ h₂ hh₂]
        _ = b * h₂ * h₁ := by group
    · calc b * h₁ * h₂ = b * (h₁ * h₂) := by group
        _ = b * (h₂ * h₁) := by rw [hHab h₁ hh₁ h₂ hh₂]
        _ = h₂ * (b * h₁) := by rw [← mul_assoc, hbH h₂ hh₂, mul_assoc]
    · calc b * h₁ * (b * h₂) = b * (h₁ * b) * h₂ := by group
        _ = b * (b * h₁) * h₂ := by rw [hbH h₁ hh₁]
        _ = b * b * (h₁ * h₂) := by group
        _ = b * b * (h₂ * h₁) := by rw [hHab h₁ hh₁ h₂ hh₂]
        _ = b * (b * h₂) * h₁ := by group
        _ = b * (h₂ * b) * h₁ := by rw [hbH h₂ hh₂]
        _ = b * h₂ * (b * h₁) := by group

theorem elem_zpowers {b : G} (hb : b ^ 2 = 1) :
    (∀ g ∈ zpowers b, g ^ 2 = 1) ∧ (∀ g₁ ∈ zpowers b, ∀ g₂ ∈ zpowers b, g₁ * g₂ = g₂ * g₁) := by
  refine ⟨fun g hg => ?_, fun g₁ hg₁ g₂ hg₂ => ?_⟩
  · rcases RankOne.mem_zpowers_of_sq hb hg with rfl | rfl
    · exact one_pow 2
    · exact hb
  · obtain ⟨i, rfl⟩ := mem_zpowers_iff.1 hg₁
    obtain ⟨j, rfl⟩ := mem_zpowers_iff.1 hg₂
    exact (Commute.zpow_zpow_self b i j).eq

theorem card_zpowers_involution [Finite G] {b : G} (hb : b ^ 2 = 1) (hb1 : b ≠ 1) :
    Nat.card (zpowers b) = 2 := by
  rw [Nat.card_zpowers]
  exact orderOf_eq_prime hb hb1

theorem two_involutions_sub [Finite G] {S U : Subgroup G} (hSp : IsPGroup 2 S) (hUS : U ≤ S)
    (hUab : ∀ a ∈ U, ∀ b ∈ U, a * b = b * a) (hUc : ¬ IsCyclic U) :
    ∃ x y : G, x ∈ U ∧ y ∈ U ∧ x ^ 2 = 1 ∧ y ^ 2 = 1 ∧ x ≠ 1 ∧ y ≠ 1 ∧ x ≠ y := by
  have hab : IsMulCommutative (U.subgroupOf S) := by
    refine ⟨⟨fun a b => Subtype.ext (Subtype.ext ?_)⟩⟩
    exact hUab _ a.2 _ b.2
  have hc : ¬ IsCyclic (U.subgroupOf S) :=
    fun h => hUc ((Subgroup.subgroupOfEquivOfLe hUS).isCyclic.1 h)
  obtain ⟨x, y, hx, hy, hx2, hy2, hx1, hy1, hxy⟩ :=
    Lemma38.two_involutions_of_not_isCyclic hSp hab hc
  refine ⟨x, y, hx, hy, ?_, ?_, fun h => hx1 (Subtype.ext h), fun h => hy1 (Subtype.ext h),
    fun h => hxy (Subtype.ext h)⟩
  · exact congrArg Subtype.val hx2
  · exact congrArg Subtype.val hy2

theorem mem_normalizer_of_comm {H : Subgroup G} {b : G} (hb : ∀ h ∈ H, b * h = h * b) :
    b ∈ normalizer (H : Set G) :=
  Subgroup.centralizer_le_normalizer _ (mem_centralizer_iff.2 fun h hh => (hb h hh).symm)

theorem card_sup_involution [Finite G] {H : Subgroup G} {b : G} (hb2 : b ^ 2 = 1)
    (hbH : ∀ h ∈ H, b * h = h * b) (hbn : b ∉ H) :
    Nat.card (H ⊔ zpowers b : Subgroup G) = 2 * Nat.card H :=
  card_sup_zpowers (mem_normalizer_of_comm hbH) (by rw [hb2]; exact one_mem H) hbn

theorem exists_involution [Finite G] {H : Subgroup G} (hH : IsPGroup 2 H) (hne : H ≠ ⊥) :
    ∃ z ∈ H, z ^ 2 = 1 ∧ z ≠ 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hnt : Nontrivial H := (Subgroup.nontrivial_iff_ne_bot H).2 hne
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 hH
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hk
    exact (Finite.one_lt_card (α := H)).ne' hk
  have h2 : 2 ∣ Nat.card H := by rw [hk]; exact dvd_pow_self 2 hk0
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := H) 2 h2
  refine ⟨z, z.2, ?_, ?_⟩
  · have := pow_orderOf_eq_one z
    rw [hz] at this
    exact congrArg Subtype.val this
  · intro h
    have : z = 1 := Subtype.ext h
    rw [this, orderOf_one] at hz
    norm_num at hz

theorem card_inf_ge [Finite G] {S M V : Subgroup G} (hidx : M.relIndex S ≤ 2) (hVS : V ≤ S) :
    Nat.card V ≤ 2 * Nat.card (M ⊓ V : Subgroup G) := by
  have h0 : M.relIndex S ≠ 0 := by
    intro h
    have := Subgroup.relIndex_mul_card (H := M) (K := S)
    rw [h, zero_mul] at this
    exact Nat.card_pos.ne' this.symm
  have h1 := Subgroup.relIndex_le_of_le_right hVS h0
  have h2 := Subgroup.relIndex_mul_card (H := M) (K := V)
  calc Nat.card V = M.relIndex V * Nat.card (M ⊓ V : Subgroup G) := h2.symm
    _ ≤ 2 * Nat.card (M ⊓ V : Subgroup G) := Nat.mul_le_mul_right _ (h1.trans hidx)

theorem not_two_commuting [Finite G] {S M Ua Ub : Subgroup G} (hSp : IsPGroup 2 S)
    (hMab : ∀ a ∈ M, ∀ b ∈ M, a * b = b * a) (hidx : M.relIndex S ≤ 2)
    (hΩ : ∀ F : Subgroup G, F ≤ M → (∀ f ∈ F, f ^ 2 = 1) → Nat.card F ≤ 4)
    (haS : Ua ≤ S) (hbS : Ub ≤ S) (hac : ¬ IsCyclic Ua) (hbc : ¬ IsCyclic Ub)
    (hab : ∀ x ∈ Ua, ∀ y ∈ Ub, x * y = y * x) (hinf : ∀ x ∈ Ua, x ∈ Ub → x = 1)
    (haab : ∀ x ∈ Ua, ∀ y ∈ Ua, x * y = y * x) : False := by
  classical
  obtain ⟨x₂, y₂, hx₂, hy₂, hx₂2, hy₂2, hx₂1, hy₂1, hxy₂⟩ := two_involutions_sub hSp haS haab hac
  set W := zpowers x₂ ⊔ zpowers y₂ with hW
  have hWa : W ≤ Ua := sup_le (zpowers_le.2 hx₂) (zpowers_le.2 hy₂)
  have hW₁ := elem_zpowers hx₂2
  have hy₂W : y₂ ∉ zpowers x₂ := by
    intro h
    rcases RankOne.mem_zpowers_of_sq hx₂2 h with h | h
    · exact hy₂1 h
    · exact hxy₂ h.symm
  have hy₂c : ∀ h ∈ zpowers x₂, y₂ * h = h * y₂ := fun h hh =>
    haab y₂ hy₂ h (zpowers_le.2 hx₂ hh)
  have hW₂ := elem_sup hW₁.1 hW₁.2 hy₂2 hy₂c
  have hcW : Nat.card W = 4 := by
    rw [hW, card_sup_involution hy₂2 hy₂c hy₂W, card_zpowers_involution hx₂2 hx₂1]
  by_cases hbab : ∀ x ∈ Ub, ∀ y ∈ Ub, x * y = y * x
  ·
    obtain ⟨x₁, y₁, hx₁, hy₁, hx₁2, hy₁2, hx₁1, hy₁1, hxy₁⟩ :=
      two_involutions_sub hSp hbS hbab hbc
    set W' := zpowers x₁ ⊔ zpowers y₁ with hW'
    have hW'b : W' ≤ Ub := sup_le (zpowers_le.2 hx₁) (zpowers_le.2 hy₁)
    have hV₁ := elem_zpowers hx₁2
    have hy₁W : y₁ ∉ zpowers x₁ := by
      intro h
      rcases RankOne.mem_zpowers_of_sq hx₁2 h with h | h
      · exact hy₁1 h
      · exact hxy₁ h.symm
    have hy₁c : ∀ h ∈ zpowers x₁, y₁ * h = h * y₁ := fun h hh =>
      hbab y₁ hy₁ h (zpowers_le.2 hx₁ hh)
    have hV₂ := elem_sup hV₁.1 hV₁.2 hy₁2 hy₁c
    have hcW' : Nat.card W' = 4 := by
      rw [hW', card_sup_involution hy₁2 hy₁c hy₁W, card_zpowers_involution hx₁2 hx₁1]
    have hx₂c : ∀ h ∈ W', x₂ * h = h * x₂ := fun h hh => hab x₂ hx₂ h (hW'b hh)
    have hx₂W' : x₂ ∉ W' := fun h => hx₂1 (hinf x₂ hx₂ (hW'b h))
    have hV₃ := elem_sup hV₂.1 hV₂.2 hx₂2 hx₂c
    set V₃ := W' ⊔ zpowers x₂ with hV₃def
    have hcV₃ : Nat.card V₃ = 8 := by
      rw [hV₃def, card_sup_involution hx₂2 hx₂c hx₂W', hcW']
    have hy₂c' : ∀ h ∈ V₃, y₂ * h = h * y₂ := by
      intro h hh
      rcases (mem_sup_zpowers_iff (mem_normalizer_of_comm hx₂c)
        (by rw [hx₂2]; exact one_mem _)).1 hh with h' | h'
      · exact hab y₂ hy₂ h (hW'b h')
      · have e : h = x₂ * (x₂⁻¹ * h) := by group
        rw [e]
        calc y₂ * (x₂ * (x₂⁻¹ * h)) = (y₂ * x₂) * (x₂⁻¹ * h) := by group
          _ = (x₂ * y₂) * (x₂⁻¹ * h) := by rw [haab y₂ hy₂ x₂ hx₂]
          _ = x₂ * (y₂ * (x₂⁻¹ * h)) := by group
          _ = x₂ * ((x₂⁻¹ * h) * y₂) := by rw [hab y₂ hy₂ _ (hW'b h')]
          _ = x₂ * (x₂⁻¹ * h) * y₂ := by group
    have hy₂V₃ : y₂ ∉ V₃ := by
      intro hh
      rcases (mem_sup_zpowers_iff (mem_normalizer_of_comm hx₂c)
        (by rw [hx₂2]; exact one_mem _)).1 hh with h' | h'
      · exact hy₂1 (hinf y₂ hy₂ (hW'b h'))
      · have h1 := hinf _ (Ua.mul_mem (Ua.inv_mem hx₂) hy₂) (hW'b h')
        apply hxy₂
        calc x₂ = x₂ * (x₂⁻¹ * y₂) := by rw [h1, mul_one]
          _ = y₂ := by group
    have hV₄ := elem_sup hV₃.1 hV₃.2 hy₂2 hy₂c'
    set V₄ := V₃ ⊔ zpowers y₂ with hV₄def
    have hcV₄ : Nat.card V₄ = 16 := by
      rw [hV₄def, card_sup_involution hy₂2 hy₂c' hy₂V₃, hcV₃]
    have hV₄S : V₄ ≤ S :=
      sup_le (sup_le (hW'b.trans hbS) (zpowers_le.2 (haS hx₂))) (zpowers_le.2 (haS hy₂))
    have h1 := card_inf_ge hidx hV₄S
    have h2 := hΩ (M ⊓ V₄) inf_le_left (fun f hf => hV₄.1 f (mem_inf.1 hf).2)
    omega
  ·
    have hUbM : ¬ Ub ≤ M := fun h => hbab fun x hx y hy => hMab x (h hx) y (h hy)
    have hUaM : Ua ≤ M := by
      by_contra h
      exact hbab (comm_of_not_le hidx hMab haS hbS hab h hUbM)
    have hne : Ub ⊓ M ≠ ⊥ := by
      intro hbot
      apply hbc
      have hnb : Ub ≠ ⊥ := fun h => hbc (by rw [h]; infer_instance)
      obtain ⟨⟨u, huU⟩, hu1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hnb
      have hu1' : u ≠ 1 := fun h => hu1 (Subtype.ext h)
      have hnotM : ∀ w ∈ Ub, w ≠ 1 → w ∉ M := fun w hw hw1 hwM => by
        have : w ∈ Ub ⊓ M := mem_inf.2 ⟨hw, hwM⟩
        rw [hbot, mem_bot] at this
        exact hw1 this
      have hle : Ub ≤ zpowers u := by
        intro w hw
        by_cases hw1 : w = 1
        · rw [hw1]; exact one_mem _
        · have hm := mul_inv_mem_of_relIndex_le_two hidx (hbS hw) (hbS huU)
            (hnotM w hw hw1) (hnotM u huU hu1')
          have : w * u⁻¹ ∈ Ub ⊓ M := mem_inf.2 ⟨Ub.mul_mem hw (Ub.inv_mem huU), hm⟩
          rw [hbot, mem_bot] at this
          have : w = u := by
            calc w = w * u⁻¹ * u := by group
              _ = u := by rw [this, one_mul]
          rw [this]
          exact mem_zpowers u
      exact TwoGroup.isCyclic_of_le_isCyclic inferInstance hle
    obtain ⟨z, hz, hz2, hz1⟩ := exists_involution (hSp.to_le (inf_le_left.trans hbS)) hne
    obtain ⟨hzb, hzM⟩ := mem_inf.1 hz
    have hzc : ∀ h ∈ W, z * h = h * z := fun h hh => (hab h (hWa hh) z hzb).symm
    have hzW : z ∉ W := fun h => hz1 (hinf z (hWa h) hzb)
    have hV := elem_sup hW₂.1 hW₂.2 hz2 hzc
    have hcV : Nat.card (W ⊔ zpowers z : Subgroup G) = 8 := by
      rw [card_sup_involution hz2 hzc hzW, hcW]
    have hVM : W ⊔ zpowers z ≤ M := sup_le (hWa.trans hUaM) (zpowers_le.2 hzM)
    have := hΩ _ hVM hV.1
    omega

theorem quasisimple_of_abelian_index_two [Finite G] {A : Subgroup G}
    (hA : aschbacherThm5IsSemisimple A) (S₀ : Sylow 2 A) {M : Subgroup G}
    (hMab : ∀ a ∈ M, ∀ b ∈ M, a * b = b * a)
    (hidx : M.relIndex ((S₀ : Subgroup A).map A.subtype) ≤ 2)
    (hΩ : ∀ F : Subgroup G, F ≤ M → (∀ f ∈ F, f ^ 2 = 1) → Nat.card F ≤ 4) :
    Open.IsQuasisimple A := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set S := (S₀ : Subgroup A).map A.subtype with hS
  have hSp : IsPGroup 2 S := S₀.isPGroup'.map _
  obtain ⟨k, K, hk, hKq, hcomm, hsup⟩ := hA
  have hKA : ∀ i, K i ≤ A := fun i => (hKq i).1
  by_cases hk1 : k = 1
  · subst hk1
    have hA0 : K 0 = A := by
      rw [← hsup, iSup_unique]
      rfl
    rw [← hA0]
    exact (hKq 0).2
  exfalso
  set i₀ : Fin k := ⟨0, by omega⟩
  set i₁ : Fin k := ⟨1, by omega⟩
  have hi : i₀ ≠ i₁ := by simp [i₀, i₁, Fin.ext_iff]
  have hT : ∀ i, ∃ T : Sylow 2 (K i), ¬ IsCyclic ((T : Subgroup (K i)).map (K i).subtype) := by
    intro i
    have : Group.IsPerfect (K i) := ⟨(hKq i).2.1⟩
    let T : Sylow 2 (K i) := default
    refine ⟨T, fun hc => ?_⟩
    apply TwoRankLowerBound.Helpers.sylow_two_not_isCyclic_of_perfect (K i)
      (Lemma38.even_card_of_isQuasisimple (hKq i).2) T
    exact ((T : Subgroup (K i)).equivMapOfInjective _ (K i).subtype_injective).isCyclic.2 hc
  have hgasch : ∀ i i' : Fin k, i ≠ i' → ∀ T : Sylow 2 (K i),
      (∀ a ∈ (T : Subgroup (K i)).map (K i).subtype,
        ∀ b ∈ (T : Subgroup (K i)).map (K i).subtype, a * b = b * a) →
      ∀ r ∈ (T : Subgroup (K i)).map (K i).subtype, r ∈ K i' → r = 1 := by
    intro i i' hii' T hTab r hrT hrK'
    have : Group.IsPerfect (K i) := ⟨(hKq i).2.1⟩
    obtain ⟨r', hr'T, rfl⟩ := hrT
    have hab : IsMulCommutative (T : Subgroup (K i)) := by
      refine ⟨⟨fun a b => Subtype.ext (Subtype.ext ?_)⟩⟩
      exact hTab _ ⟨a, a.2, rfl⟩ _ ⟨b, b.2, rfl⟩
    have hcen : zpowers r' ≤ center (K i) := by
      rw [zpowers_le, mem_center_iff]
      intro y
      apply Subtype.ext
      exact (hcomm i' i hii'.symm _ hrK' y y.2).symm
    have hp : IsPGroup 2 (zpowers r') := T.isPGroup'.to_le (zpowers_le.2 hr'T)
    have hbot := Walter.W67.inf_commutator_eq_bot_of_isPGroup T hab hcen hp
    rw [Group.IsPerfect.commutator_eq_top, inf_top_eq] at hbot
    have : r' = 1 := by
      have := mem_zpowers r'
      rw [hbot, mem_bot] at this
      exact this
    rw [this]
    rfl
  obtain ⟨T₀, hT₀⟩ := hT i₀
  obtain ⟨T₁, hT₁⟩ := hT i₁
  set R₀ := (T₀ : Subgroup (K i₀)).map (K i₀).subtype with hR₀
  set R₁ := (T₁ : Subgroup (K i₁)).map (K i₁).subtype with hR₁
  have hR₀K : R₀ ≤ K i₀ := map_subtype_le _
  have hR₁K : R₁ ≤ K i₁ := map_subtype_le _
  have hRcomm : ∀ x ∈ R₀, ∀ y ∈ R₁, x * y = y * x :=
    fun x hx y hy => hcomm i₀ i₁ hi x (hR₀K hx) y (hR₁K hy)
  have hR₀p : IsPGroup 2 R₀ := T₀.isPGroup'.map _
  have hR₁p : IsPGroup 2 R₁ := T₁.isPGroup'.map _
  have hRp : IsPGroup 2 (R₀ ⊔ R₁ : Subgroup G) := by
    refine hR₀p.to_sup_of_normal_left' hR₁p ?_
    refine le_trans ?_ (Subgroup.centralizer_le_normalizer _)
    intro y hy
    rw [mem_centralizer_iff]
    intro x hx
    exact hRcomm x hx y hy
  have hRA : R₀ ⊔ R₁ ≤ A := sup_le (hR₀K.trans (hKA i₀)) (hR₁K.trans (hKA i₁))
  have hQp : IsPGroup 2 ((R₀ ⊔ R₁).subgroupOf A) :=
    hRp.of_equiv (Subgroup.subgroupOfEquivOfLe hRA).symm
  obtain ⟨S₁, hS₁⟩ := hQp.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq A S₁ S₀
  have hconjS : ∀ x ∈ R₀ ⊔ R₁, (g : G) * x * (g : G)⁻¹ ∈ S := by
    intro x hx
    have hxQ : (⟨x, hRA hx⟩ : A) ∈ (S₁ : Subgroup A) := hS₁ hx
    have hmem : g * ⟨x, hRA hx⟩ * g⁻¹ ∈ ((g • S₁ : Sylow 2 A) : Subgroup A) := by
      rw [Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]
      exact ⟨⟨x, hRA hx⟩, hxQ, by simp [MulAut.conj_apply]⟩
    rw [hg] at hmem
    exact ⟨_, hmem, rfl⟩
  let c := (MulAut.conj (g : G)).toMonoidHom
  set U₀ := R₀.map c with hU₀
  set U₁ := R₁.map c with hU₁
  have hcinj : Function.Injective c := (MulAut.conj (g : G)).injective
  have hU₀S : U₀ ≤ S := by
    rintro _ ⟨x, hx, rfl⟩
    exact hconjS x (mem_sup_left hx)
  have hU₁S : U₁ ≤ S := by
    rintro _ ⟨x, hx, rfl⟩
    exact hconjS x (mem_sup_right hx)
  have hU₀c : ¬ IsCyclic U₀ := fun h => hT₀ ((R₀.equivMapOfInjective c hcinj).isCyclic.2 h)
  have hU₁c : ¬ IsCyclic U₁ := fun h => hT₁ ((R₁.equivMapOfInjective c hcinj).isCyclic.2 h)
  have hcmul : ∀ a b : G, c a * c b = c (a * b) := fun a b => (map_mul c a b).symm
  have hUcomm : ∀ x ∈ U₀, ∀ y ∈ U₁, x * y = y * x := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [hcmul, hcmul, hRcomm x hx y hy]
  have hback : ∀ R : Subgroup G, (∀ a ∈ R.map c, ∀ b ∈ R.map c, a * b = b * a) →
      ∀ a ∈ R, ∀ b ∈ R, a * b = b * a := by
    intro R hR a ha b hb
    apply hcinj
    rw [← hcmul, ← hcmul]
    exact hR _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
  have hinf : (∀ a ∈ U₀, ∀ b ∈ U₀, a * b = b * a) ∨ (∀ a ∈ U₁, ∀ b ∈ U₁, a * b = b * a) →
      ∀ x ∈ U₀, x ∈ U₁ → x = 1 := by
    rintro hab _ ⟨x, hx, rfl⟩ hx1
    obtain ⟨y, hy, hyx⟩ := hx1
    have hxy : x = y := hcinj hyx.symm
    subst hxy
    have : x = 1 := by
      rcases hab with h | h
      · exact hgasch i₀ i₁ hi T₀ (hback R₀ h) x hx (hR₁K hy)
      · exact hgasch i₁ i₀ hi.symm T₁ (hback R₁ h) x hy (hR₀K hx)
    rw [this, map_one]
  have hone : (∀ a ∈ U₀, ∀ b ∈ U₀, a * b = b * a) ∨ (∀ a ∈ U₁, ∀ b ∈ U₁, a * b = b * a) := by
    by_cases h₀ : U₀ ≤ M
    · exact Or.inl fun a ha b hb => hMab a (h₀ ha) b (h₀ hb)
    by_cases h₁ : U₁ ≤ M
    · exact Or.inr fun a ha b hb => hMab a (h₁ ha) b (h₁ hb)
    exact Or.inl (comm_of_not_le hidx hMab hU₁S hU₀S (fun y hy x hx => (hUcomm x hx y hy).symm)
      h₁ h₀)
  have hI := hinf hone
  rcases hone with h₀ | h₁
  · exact not_two_commuting hSp hMab hidx hΩ hU₀S hU₁S hU₀c hU₁c hUcomm hI h₀
  · exact not_two_commuting hSp hMab hidx hΩ hU₁S hU₀S hU₁c hU₀c
      (fun y hy x hx => (hUcomm x hx y hy).symm) (fun x hx₁ hx₀ => hI x hx₀ hx₁) h₁

end Lemma37

end CFSG.ComponentClassification.AschbacherKnownGroup
