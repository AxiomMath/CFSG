module

public import CFSG.Goldschmidt.Steps.G2Tr

public section

namespace CFSG.Goldschmidt.G2

open Module CFSG.QuasithinUnique
open scoped Pointwise

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
  {X : Subgroup (V ≃ₗ[ZMod 2] V)} {η : V ≃ₗ[ZMod 2] V}

namespace LinHyp

variable (h : LinHyp X η)
include h

theorem eq_of_transitive
    (hidx : ∀ X₀ : Subgroup (V ≃ₗ[ZMod 2] V), X₀ ≤ X → (X₀.subgroupOf X).index ≠ 2)
    (hnorm : ∀ x ∈ X, x • fixSp η = fixSp η → x * η * x⁻¹ ∈ Subgroup.zpowers η)
    (htr : ∀ v w : V, v ≠ 0 → w ≠ 0 → ∃ x ∈ X, x v = w) :
    Nat.card V = 8 ∧ Nat.card (fixSp η) = 2 ∧ Nat.card X = 21 ∧
      ∃ x₁ ∈ X, ∃ x₂ ∈ X, x₁ * x₂ ≠ x₂ * x₁ := by
  classical
  have hk1 := h.finrank_fixSp_eq_one (irreducible_of_transitive htr)
    (h.semiregular_of_transitive hidx hnorm htr)
  have hW2 : Nat.card (fixSp η) = 2 := by
    rw [ONan.natCard_submodule, hk1]
    norm_num
  obtain ⟨w₀, hw₀, hw₀0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h.fixSp_ne_bot
  have hWw : ∀ w ∈ fixSp η, w = 0 ∨ w = w₀ := by
    intro w hw
    have hw₀' : (⟨w₀, hw₀⟩ : fixSp η) ≠ 0 := fun h0 => hw₀0 (congrArg Subtype.val h0)
    obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' _ hw₀').mp hk1 ⟨w, hw⟩
    have hc' : c • w₀ = w := congrArg Subtype.val hc
    rcases ONan.zmod_smul_eq c w₀ with h0 | h1
    · left
      rw [← hc', h0]
    · right
      rw [← hc', h1]
  have hw₀D : w₀ ∉ comSp η := fun hD => hw₀0 (by
    have := Submodule.mem_inf.mpr ⟨hD, hw₀⟩
    rwa [h.isCompl.inf_eq_bot, Submodule.mem_bot] at this)
  have hD2 : ∀ u, u ∉ comSp η → u + w₀ ∈ comSp η := by
    intro u hu
    obtain ⟨d, hd, w, hw, rfl⟩ := h.exists_add u
    rcases hWw w hw with rfl | rfl
    · exact absurd (by rwa [add_zero]) hu
    · rw [add_assoc, add_self, add_zero]
      exact hd
  have hDidx : ∀ u u' : V, (u + u' ∈ comSp η ↔ (u ∈ comSp η ↔ u' ∈ comSp η)) := by
    intro u u'
    by_cases hu : u ∈ comSp η <;> by_cases hu' : u' ∈ comSp η
    · exact iff_of_true ((comSp η).add_mem hu hu') (iff_of_true hu hu')
    · refine iff_of_false (fun h' => hu' ?_) (fun h' => hu' (h'.mp hu))
      have := (comSp η).sub_mem h' hu
      rwa [add_sub_cancel_left] at this
    · refine iff_of_false (fun h' => hu ?_) (fun h' => hu (h'.mpr hu'))
      have := (comSp η).sub_mem h' hu'
      rwa [add_sub_cancel_right] at this
    · refine iff_of_true ?_ (iff_of_false hu hu')
      have := (comSp η).add_mem (hD2 u hu) (hD2 u' hu')
      rwa [add_add_add_comm, add_self, add_zero] at this
  have hstabW : ∀ z ∈ X, z w₀ = w₀ → z • fixSp η = fixSp η := by
    intro z hz hzw
    have hne : z • fixSp η ⊓ (1 : V ≃ₗ[ZMod 2] V) • fixSp η ≠ ⊥ := by
      intro hbot
      have hmem : w₀ ∈ z • fixSp η ⊓ (1 : V ≃ₗ[ZMod 2] V) • fixSp η := by
        refine Submodule.mem_inf.mpr ⟨?_, by rw [one_smul]; exact hw₀⟩
        rw [← hzw]
        exact Submodule.smul_mem_pointwise_smul _ _ _ hw₀
      rw [hbot, Submodule.mem_bot] at hmem
      exact hw₀0 hmem
    have := h.smul_eq_of_inf_ne_bot hz X.one_mem hne
    rwa [one_smul] at this
  have hstabD : ∀ z ∈ X, z w₀ = w₀ → ∀ d ∈ comSp η, z d ∈ comSp η :=
    fun z hz hzw d hd => h.apply_mem_comSp_of_normalizes (hnorm z hz (hstabW z hz hzw)) hd
  have hcase : ∀ x ∈ X, x • fixSp η ⊓ comSp η ≠ ⊥ → x • fixSp η ≤ comSp η := by
    intro x hx hne
    obtain ⟨d, hd, hd0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
    obtain ⟨hdx, hdD⟩ := Submodule.mem_inf.mp hd
    obtain ⟨w, hw, hwd⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp hdx
    have hxw₀ : x w₀ ∈ comSp η := by
      rcases hWw w hw with rfl | rfl
      · exact absurd (by rw [← hwd, smul_zero]) hd0
      · rw [← LinearEquiv.smul_def, hwd]
        exact hdD
    rintro _ ⟨u, hu, rfl⟩
    rcases hWw u hu with rfl | rfl
    · rw [map_zero]
      exact (comSp η).zero_mem
    · exact hxw₀
  have hodd := h.odd_card hidx hnorm htr hcase
  set R : V → V → Prop := fun b a => ∃ x ∈ X, x a = w₀ ∧ x b ∈ comSp η with hRdef
  have hex : ∀ a, a ≠ 0 → ∃ x ∈ X, x a = w₀ := fun a ha => htr a w₀ ha hw₀0
  have hRiff : ∀ a b x, x ∈ X → x a = w₀ → (R b a ↔ x b ∈ comSp η) := by
    intro a b x hx hxa
    refine ⟨fun ⟨x₀, hx₀, hx₀a, hx₀b⟩ => ?_, fun hb => ⟨x, hx, hxa, hb⟩⟩
    have hz : (x * x₀⁻¹) w₀ = w₀ := by
      have h1 : x₀⁻¹ w₀ = a := by rw [← hx₀a]; simp
      rw [LinearEquiv.mul_apply, h1, hxa]
    have := hstabD _ (X.mul_mem hx (X.inv_mem hx₀)) hz _ hx₀b
    simpa [LinearEquiv.mul_apply] using this
  have hRadd : ∀ a, a ≠ 0 → ∀ b b', (R (b + b') a ↔ (R b a ↔ R b' a)) := by
    intro a ha b b'
    obtain ⟨x, hx, hxa⟩ := hex a ha
    rw [hRiff a _ x hx hxa, hRiff a _ x hx hxa, hRiff a _ x hx hxa, map_add]
    exact hDidx _ _
  have hRaa : ∀ a, a ≠ 0 → ¬ R a a := by
    intro a ha hR
    obtain ⟨x, hx, hxa⟩ := hex a ha
    rw [hRiff a a x hx hxa, hxa] at hR
    exact hw₀D hR
  have hR0 : ∀ a, a ≠ 0 → R 0 a := by
    intro a ha
    obtain ⟨x, hx, hxa⟩ := hex a ha
    rw [hRiff a 0 x hx hxa, map_zero]
    exact (comSp η).zero_mem
  have hnoswap : ∀ g ∈ X, ∀ a b : V, g a = b → g b = a → a = b := by
    intro g hg a b hab hba
    have := smul_eq_of_sq_smul_eq (Ω := V) hodd ⟨g, hg⟩ a (by
      show g (g a) = a
      rw [hab, hba])
    have h1 : g a = a := this
    rw [← hab, h1]
  have hηw₀ : ∀ i : ℕ, (η ^ i) w₀ = w₀ := fun i =>
    apply_eq_of_mem_zpowers (Subgroup.npow_mem_zpowers η i) hw₀
  have hanti : ∀ a b, a ≠ 0 → b ≠ 0 → a ≠ b → (R b a ↔ ¬ R a b) := by
    intro a b ha hb hab
    obtain ⟨x, hx, hxa⟩ := hex a ha
    obtain ⟨x', hx', hx'b⟩ := hex b hb
    have hxb0 : x b ≠ 0 := fun h0 => hb (by simpa using congrArg x.symm h0)
    have hx'a0 : x' a ≠ 0 := fun h0 => ha (by simpa using congrArg x'.symm h0)
    have hxbw : x b ≠ w₀ := fun h' => hab (x.injective (hxa.trans h'.symm))
    have hx'aw : x' a ≠ w₀ := fun h' => hab (x'.injective (h'.trans hx'b.symm))
    have hgX : ∀ i : ℕ, x'⁻¹ * η ^ i * x ∈ X :=
      fun i => X.mul_mem (X.mul_mem (X.inv_mem hx') (X.pow_mem h.mem i)) hx
    have hga : ∀ i : ℕ, (x'⁻¹ * η ^ i * x) a = b := by
      intro i
      rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, hxa, hηw₀, ← hx'b]
      simp
    rw [hRiff a b x hx hxa, hRiff b a x' hx' hx'b]
    constructor
    · intro hb' ha'
      obtain ⟨i, hi⟩ := h.trans (x b) hb' (x' a) ha' hxb0 hx'a0
      have hgb : (x'⁻¹ * η ^ i * x) b = a := by
        rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, hi]
        simp
      exact hab (hnoswap _ (hgX i) a b (hga i) hgb)
    · intro hna
      by_contra hnb
      have h1 := hD2 _ hnb
      have h2 := hD2 _ hna
      have h1' : x b + w₀ ≠ 0 := fun h0 => hxbw ((ONan.add_eq_zero_iff_eq _ _).mp h0)
      have h2' : x' a + w₀ ≠ 0 := fun h0 => hx'aw ((ONan.add_eq_zero_iff_eq _ _).mp h0)
      obtain ⟨i, hi⟩ := h.trans _ h1 _ h2 h1' h2'
      have hgb : (x'⁻¹ * η ^ i * x) b = a := by
        rw [map_add, hηw₀] at hi
        have : (η ^ i) (x b) = x' a := by
          have := congrArg (· + w₀) hi
          simpa [add_assoc, add_self] using this
        rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, this]
        simp
      exact hab (hnoswap _ (hgX i) a b (hga i) hgb)
  set χ : V → V → ZMod 2 := fun a z => if R z a then 0 else 1 with hχdef
  have hχadd : ∀ a, a ≠ 0 → ∀ z z', χ a (z + z') = χ a z + χ a z' := by
    intro a ha z z'
    have := hRadd a ha z z'
    by_cases h1 : R z a <;> by_cases h2 : R z' a
    · have h3 : R (z + z') a := this.mpr (iff_of_true h1 h2)
      simp [hχdef, h1, h2, h3]
    · have h3 : ¬ R (z + z') a := fun h3 => h2 ((this.mp h3).mp h1)
      simp [hχdef, h1, h2, h3]
    · have h3 : ¬ R (z + z') a := fun h3 => h1 ((this.mp h3).mpr h2)
      simp [hχdef, h1, h2, h3]
    · have h3 : R (z + z') a := this.mpr (iff_of_false h1 h2)
      simp only [hχdef, h1, h2, h3, ite_true, ite_false]
      decide
  have hχ0 : ∀ a, a ≠ 0 → χ a 0 = 0 := fun a ha => by simp [hχdef, hR0 a ha]
  have hχanti : ∀ a b, a ≠ 0 → b ≠ 0 → a ≠ b → χ a b = 1 + χ b a := by
    intro a b ha hb hab
    have := hanti a b ha hb hab
    by_cases h1 : R b a
    · have h2 : ¬ R a b := this.mp h1
      simp only [hχdef, h1, h2, ite_true, ite_false]
      decide
    · have h2 : R a b := by
        by_contra h2
        exact h1 (this.mpr h2)
      simp [hχdef, h1, h2]
  obtain ⟨d₁, hd₁, hd₁0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h.comSp_ne_bot
  have hw₀d₁ : w₀ ≠ d₁ := fun h' => hw₀D (h' ▸ hd₁)
  have hu₃0 : w₀ + d₁ ≠ 0 := fun h0 => hw₀d₁ ((ONan.add_eq_zero_iff_eq _ _).mp h0)
  have hsum : w₀ + d₁ + (w₀ + d₁) = 0 := add_self _
  let L : V →+ ZMod 2 :=
    { toFun := fun z => χ w₀ z + χ d₁ z + χ (w₀ + d₁) z
      map_zero' := by rw [hχ0 _ hw₀0, hχ0 _ hd₁0, hχ0 _ hu₃0]; rfl
      map_add' := fun z z' => by
        rw [hχadd _ hw₀0, hχadd _ hd₁0, hχadd _ hu₃0]
        ring }
  have hker : ∀ z, L z = 0 → z ∈ ({0, w₀, d₁, w₀ + d₁} : Set V) := by
    intro z hz
    by_contra hzP
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hzP
    obtain ⟨hz0, hz1, hz2, hz3⟩ := hzP
    have e1 := hχanti w₀ z hw₀0 hz0 (Ne.symm hz1)
    have e2 := hχanti d₁ z hd₁0 hz0 (Ne.symm hz2)
    have e3 := hχanti (w₀ + d₁) z hu₃0 hz0 (Ne.symm hz3)
    have e4 : χ z w₀ + χ z d₁ + χ z (w₀ + d₁) = 0 := by
      rw [← hχadd z hz0, ← hχadd z hz0, hsum, hχ0 z hz0]
    have hLz : L z = χ w₀ z + χ d₁ z + χ (w₀ + d₁) z := rfl
    rw [hLz, e1, e2, e3] at hz
    revert hz e4
    generalize χ z w₀ = p
    generalize χ z d₁ = q
    generalize χ z (w₀ + d₁) = r
    revert p q r
    decide
  have hcardV : Nat.card V = 8 := by
    have hle1 : Nat.card L.ker ≤ 4 := by
      have hsub : (L.ker : Set V) ⊆ ({0, w₀, d₁, w₀ + d₁} : Set V) := fun z hz => hker z hz
      have h1 := Set.ncard_le_ncard hsub (Set.toFinite _)
      have h2 : ({0, w₀, d₁, w₀ + d₁} : Set V).ncard ≤ 4 := by
        refine (Set.ncard_insert_le _ _).trans ?_
        refine (Nat.add_le_add_right (Set.ncard_insert_le _ _) 1).trans ?_
        refine (Nat.add_le_add_right (Nat.add_le_add_right (Set.ncard_insert_le _ _) 1) 1).trans ?_
        rw [Set.ncard_singleton]
      calc Nat.card L.ker = (L.ker : Set V).ncard := Nat.card_coe_set_eq _
        _ ≤ 4 := h1.trans h2
    have hle2 : Nat.card L.range ≤ 2 := by
      have := Nat.card_le_card_of_injective (fun x : L.range => (x : ZMod 2)) Subtype.val_injective
      rwa [Nat.card_zmod] at this
    have hVL := AddSubgroup.card_mul_index L.ker
    rw [AddSubgroup.index_ker] at hVL
    have hge : 8 ≤ Nat.card V := by
      rw [ONan.natCard_space, ← Submodule.finrank_add_eq_of_isCompl h.isCompl, hk1]
      calc 8 = 2 ^ (2 + 1) := by norm_num
        _ ≤ 2 ^ (finrank (ZMod 2) (comSp η) + 1) :=
            Nat.pow_le_pow_right (by norm_num) (by have := h.two_le_finrank_comSp; omega)
    have hmul : Nat.card L.ker * Nat.card L.range ≤ 4 * 2 := Nat.mul_le_mul hle1 hle2
    omega
  have hfrD : finrank (ZMod 2) (comSp η) = 2 := by
    have h1 := ONan.natCard_space (V := V)
    rw [hcardV, ← Submodule.finrank_add_eq_of_isCompl h.isCompl, hk1] at h1
    have h2 : 2 ^ 3 = 2 ^ (finrank (ZMod 2) (comSp η) + 1) := by rw [← h1]; norm_num
    have := Nat.pow_right_injective (le_refl 2) h2
    omega
  have hη3 : orderOf η = 3 := by
    have h1 := h.card_zpowers_add_one
    rw [ONan.natCard_submodule, hfrD, Nat.card_zpowers] at h1
    omega
  set K₀ := MulAction.stabilizer X w₀ with hK₀
  have hmemK₀ : ∀ k : X, k ∈ K₀ ↔ (k : V ≃ₗ[ZMod 2] V) w₀ = w₀ := fun k =>
    MulAction.mem_stabilizer_iff
  have horb : MulAction.orbit X w₀ = {v : V | v ≠ 0} := by
    ext v
    simp only [Set.mem_ofPred_eq]
    constructor
    · rintro ⟨x, rfl⟩ h0
      have h0' : (x : V ≃ₗ[ZMod 2] V) w₀ = 0 := h0
      exact hw₀0 (by simpa using congrArg (x : V ≃ₗ[ZMod 2] V).symm h0')
    · intro hv
      obtain ⟨x, hx, hxv⟩ := htr w₀ v hw₀0 hv
      exact ⟨⟨x, hx⟩, hxv⟩
  have hidxK : K₀.index = 7 := by
    rw [hK₀, MulAction.index_stabilizer, horb]
    have h1 := card_nonzero_add_one (⊤ : Submodule (ZMod 2) V)
    rw [ONan.natCard_submodule, finrank_top, ← ONan.natCard_space, hcardV] at h1
    have h2 : {v : V // v ∈ (⊤ : Submodule (ZMod 2) V) ∧ v ≠ 0} ≃ {v : V | v ≠ 0} :=
      { toFun := fun v => ⟨v.1, v.2.2⟩
        invFun := fun v => ⟨v.1, Submodule.mem_top, v.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    rw [← Nat.card_coe_set_eq, ← Nat.card_congr h2]
    omega
  have hcardX : Nat.card X = 7 * Nat.card K₀ := by
    rw [← hidxK, Subgroup.index_mul_card]
  let Dn := {v : V // v ∈ comSp η ∧ v ≠ 0}
  let _ : MulAction K₀ Dn :=
    { smul := fun k d => ⟨((k : X) : V ≃ₗ[ZMod 2] V) d.1,
        hstabD _ (k : X).2 ((hmemK₀ k).mp k.2) d.1 d.2.1,
        fun h0 => d.2.2 (by simpa using congrArg ((k : X) : V ≃ₗ[ZMod 2] V).symm h0)⟩
      one_smul := fun d => Subtype.ext rfl
      mul_smul := fun k k' d => Subtype.ext rfl }
  have hψinj : Function.Injective (MulAction.toPermHom K₀ Dn) := by
    rw [injective_iff_map_eq_one]
    intro k hk
    have hkD : ∀ d ∈ comSp η, ((k : X) : V ≃ₗ[ZMod 2] V) d = d := by
      intro d hd
      by_cases hd0 : d = 0
      · rw [hd0, map_zero]
      · have := congrArg (fun σ : Equiv.Perm Dn => (σ ⟨d, hd, hd0⟩ : V)) hk
        exact this
    apply Subtype.ext
    apply Subtype.ext
    ext v
    obtain ⟨d, hd, w, hw, rfl⟩ := h.exists_add v
    rw [map_add, hkD d hd]
    rcases hWw w hw with rfl | rfl
    · simp
    · rw [(hmemK₀ k).mp k.2]
      simp
  have hDn : Nat.card Dn = 3 := by
    have h1 := card_nonzero_add_one (comSp η)
    rw [ONan.natCard_submodule, hfrD] at h1
    show Nat.card {v : V // v ∈ comSp η ∧ v ≠ 0} = 3
    omega
  have hK6 : Nat.card K₀ ∣ 6 := by
    have := Subgroup.card_dvd_of_injective _ hψinj
    rwa [Nat.card_perm, hDn] at this
  have hK3 : 3 ∣ Nat.card K₀ := by
    have hle : Subgroup.zpowers (⟨η, h.mem⟩ : X) ≤ K₀ := by
      rw [Subgroup.zpowers_le, hmemK₀]
      exact mem_fixSp.mp hw₀
    have := Subgroup.card_dvd_of_le hle
    rwa [Nat.card_zpowers, Subgroup.orderOf_mk, hη3] at this
  have hKodd : Odd (Nat.card K₀) := Odd.of_dvd_nat hodd (Subgroup.card_subgroup_dvd_card K₀)
  have hK : Nat.card K₀ = 3 := by
    obtain ⟨c, hc⟩ := hK3
    have hc6 := Nat.le_of_dvd (by norm_num) hK6
    rcases hKodd with ⟨t, ht⟩
    omega
  refine ⟨hcardV, hW2, by rw [hcardX, hK], ?_⟩
  by_contra hcomm
  push Not at hcomm
  apply h.ne_one
  ext v
  by_cases hv : v = 0
  · rw [hv, map_zero, map_zero]
  obtain ⟨x, hx, rfl⟩ := htr w₀ v hw₀0 hv
  have := congrArg (fun f : V ≃ₗ[ZMod 2] V => f w₀) (hcomm η h.mem x hx)
  simp only [LinearEquiv.mul_apply] at this
  rw [this, mem_fixSp.mp hw₀, LinearEquiv.coe_one, id]

end LinHyp

end CFSG.Goldschmidt.G2
