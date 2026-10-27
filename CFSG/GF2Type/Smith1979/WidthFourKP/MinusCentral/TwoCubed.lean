module

public import CFSG.HardMathSupport.Lang.Proving.FixedOrderCongruence

public section

namespace CFSG.GF2Type.Smith1979.W4MinusC

namespace TwoCubed

theorem ncard_four {α : Type*} {a b c d : α} (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) : ({a, b, c, d} : Set α).ncard = 4 := by
  rw [Set.ncard_insert_of_notMem, Set.ncard_insert_of_notMem, Set.ncard_pair hcd]
  · simp [hbc, hbd]
  · simp [hab, hac, had]

section General

variable {V : Type*} [Group V]

@[expose] def fixSub (α : MulAut V) : Subgroup V := α.toMonoidHom.eqLocus (MonoidHom.id V)

theorem mem_fixSub {α : MulAut V} {v : V} : v ∈ fixSub α ↔ α v = v := Iff.rfl

theorem card_fixSub_eq_two [Finite V] (hcard : Nat.card V = 8) {α : MulAut V}
    (hα3 : α ^ 3 = 1) (hα1 : α ≠ 1) : Nat.card (fixSub α) = 2 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hmod := CFSG.HardMathSupport.Lang.Proving.card_modEq_card_fixedPoints_of_pow_prime α hα3
  have hfx : Nat.card {x : V // α x = x} = Nat.card (fixSub α) :=
    Nat.card_congr (Equiv.subtypeEquivRight fun x => mem_fixSub)
  rw [hfx, hcard] at hmod
  have hdvd : Nat.card (fixSub α) ∣ 8 := hcard ▸ Subgroup.card_subgroup_dvd_card _
  have hne : Nat.card (fixSub α) ≠ 8 := by
    intro h
    apply hα1
    have htop := Subgroup.eq_top_of_card_eq (fixSub α) (h.trans hcard.symm)
    ext v
    have hv : v ∈ fixSub α := htop ▸ Subgroup.mem_top v
    exact hv
  have hle : Nat.card (fixSub α) ≤ 8 := Nat.le_of_dvd (by norm_num) hdvd
  have hpos : 0 < Nat.card (fixSub α) := Nat.card_pos
  unfold Nat.ModEq at hmod
  generalize Nat.card (fixSub α) = m at *
  have hcases : m = 1 ∨ m = 2 ∨ m = 3 ∨ m = 4 ∨ m = 5 ∨ m = 6 ∨ m = 7 ∨ m = 8 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega

theorem exists_fix_pair [Finite V] (hcard : Nat.card V = 8) {α : MulAut V} (hα3 : α ^ 3 = 1)
    (hα1 : α ≠ 1) : ∃ t : V, t ≠ 1 ∧ ∀ a, α a = a ↔ a = 1 ∨ a = t := by
  have h2 := card_fixSub_eq_two hcard hα3 hα1
  obtain ⟨⟨t, ht⟩, ht1, hu⟩ := (Nat.card_eq_two_iff' (1 : fixSub α)).1 h2
  refine ⟨t, fun h => ht1 (Subtype.ext h), fun a => ⟨fun ha => ?_, ?_⟩⟩
  · by_cases ha1 : a = 1
    · exact Or.inl ha1
    · right
      have := hu ⟨a, ha⟩ (fun h => ha1 (congrArg Subtype.val h))
      exact congrArg Subtype.val this
  · rintro (rfl | rfl)
    · exact map_one α
    · exact ht

end General

section Comm

variable {V : Type*} [CommGroup V]

@[expose] def normHom (α : MulAut V) : V →* V :=
  MonoidHom.id V * α.toMonoidHom * α.toMonoidHom.comp α.toMonoidHom

theorem normHom_apply (α : MulAut V) (v : V) : normHom α v = v * α v * α (α v) := rfl

theorem cube_apply {α : MulAut V} (hα3 : α ^ 3 = 1) (v : V) : α (α (α v)) = v := by
  have h := congrArg (fun f : MulAut V => f v) hα3
  simpa [pow_succ, MulAut.mul_apply] using h

theorem apply_normHom {α : MulAut V} (hα3 : α ^ 3 = 1) (v : V) :
    α (normHom α v) = normHom α v := by
  simp only [normHom_apply, map_mul, cube_apply hα3]
  ac_rfl

theorem normHom_apply_apply {α : MulAut V} (hα3 : α ^ 3 = 1) (v : V) :
    normHom α (α v) = normHom α v := by
  simp only [normHom_apply, cube_apply hα3]
  ac_rfl

theorem normHom_of_fixed (hV2 : ∀ v : V, v * v = 1) {α : MulAut V} {w : V} (hw : α w = w) :
    normHom α w = w := by
  rw [normHom_apply, hw, hw, mul_assoc, hV2, mul_one]

theorem card_ker_normHom [Finite V] (hV2 : ∀ v : V, v * v = 1) (hcard : Nat.card V = 8)
    {α : MulAut V} (hα3 : α ^ 3 = 1) {t : V} (ht1 : t ≠ 1)
    (hfix : ∀ a, α a = a ↔ a = 1 ∨ a = t) : Nat.card (normHom α).ker = 4 := by
  have hrange : ((normHom α).range : Set V) = {1, t} := by
    ext x
    simp only [SetLike.mem_coe, MonoidHom.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨v, rfl⟩
      exact (hfix _).1 (apply_normHom hα3 v)
    · rintro (h | h)
      · rw [h]
        exact ⟨1, map_one _⟩
      · rw [h]
        exact ⟨t, normHom_of_fixed hV2 ((hfix t).2 (Or.inr rfl))⟩
  have hr : Nat.card (normHom α).range = 2 := by
    rw [← SetLike.coe_sort_coe, Nat.card_coe_set_eq, hrange, Set.ncard_pair ht1.symm]
  have := Subgroup.card_ker_mul_card_range (normHom α)
  rw [hr, hcard] at this
  omega

theorem ncard_fibre_normHom [Finite V] (hV2 : ∀ v : V, v * v = 1) (hcard : Nat.card V = 8)
    {α : MulAut V} (hα3 : α ^ 3 = 1) {t : V} (ht1 : t ≠ 1)
    (hfix : ∀ a, α a = a ↔ a = 1 ∨ a = t) : {a : V | normHom α a = t}.ncard = 4 := by
  have hker := card_ker_normHom hV2 hcard hα3 ht1 hfix
  have hνt : normHom α t = t := normHom_of_fixed hV2 ((hfix t).2 (Or.inr rfl))
  have himg : {a : V | normHom α a = t} = (fun k => t * k) '' ((normHom α).ker : Set V) := by
    ext a
    simp only [Set.mem_setOf_eq, Set.mem_image, SetLike.mem_coe, MonoidHom.mem_ker]
    constructor
    · intro h
      refine ⟨t * a, ?_, ?_⟩
      · rw [map_mul, h, hνt]
        exact hV2 t
      · rw [← mul_assoc, hV2, one_mul]
    · rintro ⟨k, hk, rfl⟩
      rw [map_mul, hk, mul_one]
      exact hνt
  rw [himg, Set.ncard_image_of_injective _ (mul_right_injective t), ← Nat.card_coe_set_eq,
    SetLike.coe_sort_coe, hker]

theorem cap_dichotomy_aux [Finite V] (hV2 : ∀ v : V, v * v = 1) (hcard : Nat.card V = 8)
    {α : MulAut V} (hα3 : α ^ 3 = 1) {t : V} (ht1 : t ≠ 1)
    (hfix : ∀ a, α a = a ↔ a = 1 ∨ a = t) {Δ : Set V} (htΔ : t ∈ Δ) (h1Δ : 1 ∉ Δ)
    (hinv : ∀ d ∈ Δ, α d ∈ Δ) (hcap : ∀ d ∈ Δ, ∀ d' ∈ Δ, d ≠ d' → d * d' ∉ Δ) :
    Δ = {t} ∨ (Δ.ncard = 4 ∧ ∀ a, a ∈ Δ ↔ normHom α a = t) := by
  have hαt : α t = t := (hfix t).2 (Or.inr rfl)
  have hF := ncard_fibre_normHom hV2 hcard hα3 ht1 hfix
  have hsub : Δ ⊆ {a : V | normHom α a = t} := by
    intro d hd
    by_cases hdt : d = t
    · rw [Set.mem_setOf_eq, hdt]
      exact normHom_of_fixed hV2 hαt
    · have hd1 : d ≠ 1 := fun h => h1Δ (h ▸ hd)
      have hnf : α d ≠ d := fun h => ((hfix d).1 h).elim hd1 hdt
      rcases (hfix _).1 (apply_normHom hα3 d) with hν | hν
      · exfalso
        have hprod : d * α d = α (α d) := by
          have h' : d * α d * α (α d) = 1 := hν
          exact (mul_eq_one_iff_eq_inv.1 h').trans (inv_eq_of_mul_eq_one_right (hV2 _))
        exact hcap d hd (α d) (hinv d hd) (Ne.symm hnf) (hprod ▸ hinv _ (hinv d hd))
      · exact hν
  by_cases hΔt : Δ = {t}
  · exact Or.inl hΔt
  · right
    obtain ⟨d, hd, hdt⟩ : ∃ d ∈ Δ, d ≠ t := by
      by_contra hcon
      exact hΔt (Set.eq_singleton_iff_unique_mem.2
        ⟨htΔ, fun x hx => by_contra fun hxt => hcon ⟨x, hx, hxt⟩⟩)
    have hd1 : d ≠ 1 := fun h => h1Δ (h ▸ hd)
    have hnf : α d ≠ d := fun h => ((hfix d).1 h).elim hd1 hdt
    have hdΔ : α d ∈ Δ := hinv d hd
    have hddΔ : α (α d) ∈ Δ := hinv _ hdΔ
    have hfour : ({t, d, α d, α (α d)} : Set V).ncard = 4 := by
      apply ncard_four
      · exact fun h => hdt h.symm
      · exact fun h => hdt (α.injective (h.symm.trans hαt.symm))
      · exact fun h => hdt (α.injective ((α.injective (h.symm.trans hαt.symm)).trans hαt.symm))
      · exact Ne.symm hnf
      · exact fun h => hnf ((congrArg α h).trans (cube_apply hα3 d))
      · exact fun h => hnf (α.injective h).symm
    have h4 : 4 ≤ Δ.ncard := by
      rw [← hfour]
      apply Set.ncard_le_ncard _ (Set.toFinite _)
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> assumption
    have hΔF : Δ = {a : V | normHom α a = t} :=
      Set.eq_of_subset_of_ncard_le hsub (by rw [hF]; exact h4) (Set.toFinite _)
    refine ⟨?_, fun a => ?_⟩
    · rw [hΔF]
      exact hF
    · rw [hΔF]
      rfl

theorem exists_eq_of_normHom_eq_one [Finite V] (hV2 : ∀ v : V, v * v = 1)
    (hcard : Nat.card V = 8) {α : MulAut V} (hα3 : α ^ 3 = 1) {t : V} (ht1 : t ≠ 1)
    (hfix : ∀ a, α a = a ↔ a = 1 ∨ a = t) {k : V} (hk : normHom α k = 1) :
    ∃ a : V, k = a⁻¹ * α a := by
  let φ : V →* V := (MonoidHom.id V)⁻¹ * α.toMonoidHom
  have hφ : ∀ a, φ a = a⁻¹ * α a := fun a => rfl
  have hker : (φ.ker : Set V) = {1, t} := by
    ext a
    simp only [SetLike.mem_coe, MonoidHom.mem_ker, hφ, inv_mul_eq_one, Set.mem_insert_iff,
      Set.mem_singleton_iff]
    rw [eq_comm]
    exact hfix a
  have hker2 : Nat.card φ.ker = 2 := by
    rw [← SetLike.coe_sort_coe, Nat.card_coe_set_eq, hker, Set.ncard_pair ht1.symm]
  have hrange4 : Nat.card φ.range = 4 := by
    have := Subgroup.card_ker_mul_card_range φ
    rw [hker2, hcard] at this
    omega
  have hle : φ.range ≤ (normHom α).ker := by
    rintro _ ⟨a, rfl⟩
    rw [MonoidHom.mem_ker, hφ, map_mul, map_inv, normHom_apply_apply hα3, inv_mul_cancel]
  have heq : φ.range = (normHom α).ker :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [card_ker_normHom hV2 hcard hα3 ht1 hfix, hrange4])
  have hkmem : k ∈ φ.range := by
    rw [heq]
    exact hk
  obtain ⟨a, ha⟩ := hkmem
  exact ⟨a, by rw [← ha, hφ]⟩

theorem eq_one_of_commute_aux [Finite V] (hV2 : ∀ v : V, v * v = 1) (hcard : Nat.card V = 8)
    {α : MulAut V} (hα3 : α ^ 3 = 1) (hα1 : α ≠ 1) {τ : MulAut V}
    (hτ2 : τ * τ = 1) (hτα : τ * α = α * τ) : τ = 1 := by
  obtain ⟨t, ht1, hfix⟩ := exists_fix_pair hcard hα3 hα1
  have hαt : α t = t := (hfix t).2 (Or.inr rfl)
  have hττ : ∀ v, τ (τ v) = v := fun v => by
    simpa using congrArg (fun f : MulAut V => f v) hτ2
  have hτα' : ∀ v, τ (α v) = α (τ v) := fun v => by
    simpa using congrArg (fun f : MulAut V => f v) hτα
  have hτt : τ t = t := by
    rcases (hfix _).1 (show α (τ t) = τ t by rw [← hτα', hαt]) with h | h
    · exact absurd (τ.injective (h.trans (map_one τ).symm)) ht1
    · exact h
  have hντ : ∀ v, normHom α (τ v) = τ (normHom α v) := fun v => by
    simp only [normHom_apply, map_mul, hτα']
  have hνt : normHom α t = t := normHom_of_fixed hV2 hαt
  have hτfix : ∀ w, α w = w → τ w = w := fun w hw => by
    rcases (hfix w).1 hw with h | h
    · rw [h, map_one]
    · rw [h, hτt]
  have hK : Nat.card (normHom α).ker = 4 := card_ker_normHom hV2 hcard hα3 ht1 hfix
  have hstep : ∀ w, normHom α w = 1 → w ≠ 1 → τ w = w →
      ∀ k, normHom α k = 1 → τ k = k := by
    intro w hw hw1 hτw k hk
    have hαw1 : α w ≠ 1 := fun h => hw1 (α.injective (h.trans (map_one α).symm))
    have hααw1 : α (α w) ≠ 1 := fun h => hαw1 (α.injective (h.trans (map_one α).symm))
    have hnf : α w ≠ w := fun h => by
      rcases (hfix w).1 h with h1 | h1
      · exact hw1 h1
      · rw [h1, hνt] at hw
        exact ht1 hw
    have hfour : ({1, w, α w, α (α w)} : Set V).ncard = 4 := by
      apply ncard_four
      · exact hw1.symm
      · exact hαw1.symm
      · exact hααw1.symm
      · exact Ne.symm hnf
      · exact fun h => hnf ((congrArg α h).trans (cube_apply hα3 w))
      · exact fun h => hnf (α.injective h).symm
    have hsub : ({1, w, α w, α (α w)} : Set V) ⊆ ((normHom α).ker : Set V) := by
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      simp only [SetLike.mem_coe, MonoidHom.mem_ker]
      rcases hx with rfl | rfl | rfl | rfl
      · exact map_one _
      · exact hw
      · rw [normHom_apply_apply hα3]
        exact hw
      · rw [normHom_apply_apply hα3, normHom_apply_apply hα3]
        exact hw
    have heq : ({1, w, α w, α (α w)} : Set V) = ((normHom α).ker : Set V) :=
      Set.eq_of_subset_of_ncard_le hsub
        (by rw [← Nat.card_coe_set_eq, SetLike.coe_sort_coe, hK, hfour]) (Set.toFinite _)
    have hkmem : k ∈ ({1, w, α w, α (α w)} : Set V) := by
      rw [heq]
      exact hk
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hkmem
    rcases hkmem with rfl | rfl | rfl | rfl
    · exact map_one τ
    · exact hτw
    · rw [hτα', hτw]
    · rw [hτα', hτα', hτw]
  have hKτ : ∀ k, normHom α k = 1 → τ k = k := by
    intro k hk
    by_cases hw1 : k * τ k = 1
    · rw [eq_inv_of_mul_eq_one_right hw1]
      exact inv_eq_of_mul_eq_one_right (hV2 k)
    · apply hstep (k * τ k)
      · rw [map_mul, hντ, hk, map_one, mul_one]
      · exact hw1
      · rw [map_mul, hττ, mul_comm]
      · exact hk
  have hall : ∀ v, τ v = v := fun v => by
    have hu : normHom α (v * normHom α v) = 1 := by
      rw [map_mul, normHom_of_fixed hV2 (apply_normHom hα3 v), hV2]
    have hdecomp : v = normHom α v * (v * normHom α v) := by
      rw [mul_comm v, ← mul_assoc, hV2, one_mul]
    calc τ v = τ (normHom α v * (v * normHom α v)) := by rw [← hdecomp]
      _ = τ (normHom α v) * τ (v * normHom α v) := map_mul _ _ _
      _ = normHom α v * (v * normHom α v) := by
          rw [hτfix _ (apply_normHom hα3 v), hKτ _ hu]
      _ = v := hdecomp.symm
  ext v
  exact hall v

end Comm

section Translation

variable {X : Type*} [Group X]

@[expose] def conjAut (A : Subgroup X) (θ : X) (hθ : θ ∈ Subgroup.normalizer (A : Set X)) :
    MulAut A :=
  A.normalizerMonoidHom ⟨θ, hθ⟩

theorem coe_conjAut (A : Subgroup X) {θ : X} (hθ : θ ∈ Subgroup.normalizer (A : Set X))
    (a : A) : ((conjAut A θ hθ a : A) : X) = θ * a * θ⁻¹ := rfl

theorem conjAut_apply_eq_iff {A : Subgroup X} {θ : X}
    (hθ : θ ∈ Subgroup.normalizer (A : Set X)) (a : A) :
    conjAut A θ hθ a = a ↔ θ * a = a * θ := by
  rw [Subtype.ext_iff, coe_conjAut, mul_inv_eq_iff_eq_mul]

theorem conjAut_pow_three (A : Subgroup X) {θ : X} (hθ : θ ∈ Subgroup.normalizer (A : Set X))
    (hθ3 : θ ^ 3 = 1) : conjAut A θ hθ ^ 3 = 1 := by
  have h : (⟨θ, hθ⟩ : Subgroup.normalizer (A : Set X)) ^ 3 = 1 := Subtype.ext hθ3
  rw [conjAut, ← map_pow, h, map_one]

theorem conj_conj_eq {θ : X} (hθ3 : θ ^ 3 = 1) (a : X) :
    θ * (θ * a * θ⁻¹) * θ⁻¹ = θ⁻¹ * a * θ := by
  have h3 : θ * θ * θ = 1 := by simpa [pow_succ] using hθ3
  have h2 : θ * θ = θ⁻¹ := eq_inv_of_mul_eq_one_left h3
  calc θ * (θ * a * θ⁻¹) * θ⁻¹ = (θ * θ) * a * (θ * θ)⁻¹ := by group
    _ = θ⁻¹ * a * θ := by rw [h2, inv_inv]

theorem conjAut_ne_one_of_not_forall {A : Subgroup X} {θ : X}
    (hθ : θ ∈ Subgroup.normalizer (A : Set X)) (hθA : ¬ ∀ a ∈ A, θ * a = a * θ) :
    conjAut A θ hθ ≠ 1 := fun h =>
  hθA fun a ha => (conjAut_apply_eq_iff hθ ⟨a, ha⟩).1 (by rw [h]; rfl)

theorem not_forall_commute_of_cases (A : Subgroup X) (hA : Nat.card A = 8) {θ t : X}
    (ht : ∀ a ∈ A, θ * a = a * θ ↔ a = 1 ∨ a = t) : ¬ ∀ a ∈ A, θ * a = a * θ := by
  intro hall
  have hsub : (A : Set X) ⊆ {1, t} := fun a ha => by
    simpa using (ht a ha).1 (hall a ha)
  have h1 : (A : Set X).ncard ≤ ({1, t} : Set X).ncard :=
    Set.ncard_le_ncard hsub (Set.toFinite _)
  have h2 : ({1, t} : Set X).ncard ≤ 2 := by
    refine (Set.ncard_insert_le _ _).trans ?_
    rw [Set.ncard_singleton]
  have h3 : Nat.card A = (A : Set X).ncard := by
    rw [← Nat.card_coe_set_eq, SetLike.coe_sort_coe]
  omega

end Translation

end TwoCubed

section Main

variable {X : Type*} [Group X]

open scoped IsMulCommutative
open TwoCubed

theorem card_inf_centralizer_eq_two (A : Subgroup X) (hA : Nat.card A = 8) {θ : X}
    (hθ : θ ∈ Subgroup.normalizer (A : Set X)) (hθ3 : θ ^ 3 = 1)
    (hθA : ¬ ∀ a ∈ A, θ * a = a * θ) :
    Nat.card ↥(A ⊓ Subgroup.centralizer {θ}) = 2 := by
  haveI : Finite A := Nat.finite_of_card_ne_zero (by omega)
  have h2 := card_fixSub_eq_two hA (conjAut_pow_three A hθ hθ3)
    (conjAut_ne_one_of_not_forall hθ hθA)
  have hiff : ∀ y : A,
      y ∈ fixSub (conjAut A θ hθ) ↔ (y : X) ∈ A ⊓ Subgroup.centralizer {θ} := by
    intro y
    rw [mem_fixSub, conjAut_apply_eq_iff hθ y, Subgroup.mem_inf, Subgroup.mem_centralizer_iff]
    constructor
    · intro h
      exact ⟨y.2, fun x hx => by rw [Set.mem_singleton_iff.1 hx]; exact h⟩
    · rintro ⟨-, h⟩
      exact h θ rfl
  rw [← h2]
  exact (Nat.card_congr ((Equiv.subtypeEquivRight hiff).trans
    (Equiv.subtypeSubtypeEquivSubtype fun h => (Subgroup.mem_inf.1 h).1))).symm

theorem centralizes_of_commute_three (A : Subgroup X) (hA : Nat.card A = 8)
    (hA2 : ∀ a ∈ A, a * a = 1) (hAc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) {θ : X}
    (hθ : θ ∈ Subgroup.normalizer (A : Set X)) (hθ3 : θ ^ 3 = 1)
    (hθA : ¬ ∀ a ∈ A, θ * a = a * θ) {s : X} (hs : s ∈ Subgroup.normalizer (A : Set X))
    (hss : s * s = 1) (hsθ : s * θ = θ * s) : ∀ a ∈ A, s * a = a * s := by
  haveI : Finite A := Nat.finite_of_card_ne_zero (by omega)
  haveI : IsMulCommutative A := IsMulCommutative.of_comm fun a b => Subtype.ext (hAc a a.2 b b.2)
  have hV2 : ∀ v : A, v * v = 1 := fun v => Subtype.ext (hA2 v v.2)
  have hτ2 : conjAut A s hs * conjAut A s hs = 1 := by
    have h : (⟨s, hs⟩ * ⟨s, hs⟩ : Subgroup.normalizer (A : Set X)) = 1 := Subtype.ext hss
    rw [conjAut, ← map_mul, h, map_one]
  have hτα : conjAut A s hs * conjAut A θ hθ = conjAut A θ hθ * conjAut A s hs := by
    have h : (⟨s, hs⟩ * ⟨θ, hθ⟩ : Subgroup.normalizer (A : Set X)) = ⟨θ, hθ⟩ * ⟨s, hs⟩ :=
      Subtype.ext hsθ
    rw [conjAut, conjAut, ← map_mul, ← map_mul, h]
  have h1 := eq_one_of_commute_aux hV2 hA (conjAut_pow_three A hθ hθ3)
    (conjAut_ne_one_of_not_forall hθ hθA) hτ2 hτα
  intro a ha
  exact (conjAut_apply_eq_iff hs ⟨a, ha⟩).1 (by rw [h1]; rfl)

theorem eq_or_ncard_four_of_cap (A : Subgroup X) (hA : Nat.card A = 8)
    (hA2 : ∀ a ∈ A, a * a = 1) (hAc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) {θ : X}
    (hθ : θ ∈ Subgroup.normalizer (A : Set X)) (hθ3 : θ ^ 3 = 1) {t : X}
    (ht : ∀ a ∈ A, θ * a = a * θ ↔ a = 1 ∨ a = t) {Δ : Set X} (hΔA : Δ ⊆ A)
    (htΔ : t ∈ Δ) (h1Δ : 1 ∉ Δ) (hinv : ∀ d ∈ Δ, θ * d * θ⁻¹ ∈ Δ)
    (hcap : ∀ d ∈ Δ, ∀ d' ∈ Δ, d ≠ d' → d * d' ∉ Δ) :
    Δ = {t} ∨ (Δ.ncard = 4 ∧ ∀ a ∈ A, a ∈ Δ ↔ a * (θ * a * θ⁻¹) * (θ⁻¹ * a * θ) = t) := by
  haveI : Finite A := Nat.finite_of_card_ne_zero (by omega)
  haveI : IsMulCommutative A := IsMulCommutative.of_comm fun a b => Subtype.ext (hAc a a.2 b b.2)
  have hV2 : ∀ v : A, v * v = 1 := fun v => Subtype.ext (hA2 v v.2)
  have hα3 := conjAut_pow_three A hθ hθ3
  have hα1 := conjAut_ne_one_of_not_forall hθ (not_forall_commute_of_cases A hA ht)
  have htA : t ∈ A := hΔA htΔ
  have hfix : ∀ a : A, conjAut A θ hθ a = a ↔ a = 1 ∨ a = ⟨t, htA⟩ := by
    intro a
    rw [conjAut_apply_eq_iff hθ a, ht a a.2]
    constructor
    · rintro (h | h)
      · exact Or.inl (Subtype.ext h)
      · exact Or.inr (Subtype.ext h)
    · rintro (h | h)
      · exact Or.inl (congrArg Subtype.val h)
      · exact Or.inr (congrArg Subtype.val h)
  obtain ⟨t'', ht''1, hfix''⟩ := exists_fix_pair hA hα3 hα1
  have ht1 : (⟨t, htA⟩ : A) ≠ 1 := by
    have : t'' = ⟨t, htA⟩ := ((hfix t'').1 ((hfix'' t'').2 (Or.inr rfl))).resolve_left ht''1
    exact this ▸ ht''1
  set Δ' : Set A := {a | (a : X) ∈ Δ}
  have hΔeq : Δ = Subtype.val '' Δ' := by
    ext x
    constructor
    · intro hx
      exact ⟨⟨x, hΔA hx⟩, hx, rfl⟩
    · rintro ⟨a, ha, rfl⟩
      exact ha
  have key := cap_dichotomy_aux hV2 hA hα3 ht1 hfix (Δ := Δ') htΔ h1Δ
    (fun d hd => hinv d hd)
    (fun d hd d' hd' hne => hcap d hd d' hd' (fun h => hne (Subtype.ext h)))
  rcases key with h | ⟨h4, hiff⟩
  · left
    rw [hΔeq, h, Set.image_singleton]
  · right
    refine ⟨?_, fun a ha => ?_⟩
    · rw [hΔeq, Set.ncard_image_of_injective _ Subtype.val_injective]
      exact h4
    · have h := hiff ⟨a, ha⟩
      have hn : ((normHom (conjAut A θ hθ) ⟨a, ha⟩ : A) : X) =
          a * (θ * a * θ⁻¹) * (θ⁻¹ * a * θ) := by
        rw [← conj_conj_eq hθ3 a]
        rfl
      rw [Subtype.ext_iff, hn] at h
      exact h

theorem exists_eq_comm_of_norm_eq_one (A : Subgroup X) (hA : Nat.card A = 8)
    (hA2 : ∀ a ∈ A, a * a = 1) (hAc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) {θ : X}
    (hθ : θ ∈ Subgroup.normalizer (A : Set X)) (hθ3 : θ ^ 3 = 1) {t : X}
    (ht : ∀ a ∈ A, θ * a = a * θ ↔ a = 1 ∨ a = t) {k : X} (hk : k ∈ A)
    (hnorm : k * (θ * k * θ⁻¹) * (θ⁻¹ * k * θ) = 1) :
    ∃ a ∈ A, k = a⁻¹ * (θ * a * θ⁻¹) := by
  haveI : Finite A := Nat.finite_of_card_ne_zero (by omega)
  haveI : IsMulCommutative A := IsMulCommutative.of_comm fun a b => Subtype.ext (hAc a a.2 b b.2)
  have hV2 : ∀ v : A, v * v = 1 := fun v => Subtype.ext (hA2 v v.2)
  have hα3 := conjAut_pow_three A hθ hθ3
  have hα1 := conjAut_ne_one_of_not_forall hθ (not_forall_commute_of_cases A hA ht)
  obtain ⟨t', ht'1, hfix'⟩ := exists_fix_pair hA hα3 hα1
  have hk' : normHom (conjAut A θ hθ) ⟨k, hk⟩ = 1 := by
    refine Subtype.ext ?_
    rw [← conj_conj_eq hθ3 k] at hnorm
    exact hnorm
  obtain ⟨a, ha⟩ := exists_eq_of_normHom_eq_one hV2 hA hα3 ht'1 hfix' hk'
  exact ⟨a, a.2, congrArg Subtype.val ha⟩

end Main

end CFSG.GF2Type.Smith1979.W4MinusC
