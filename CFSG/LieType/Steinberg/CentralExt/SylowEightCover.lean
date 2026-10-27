module

public import CFSG.LocalAnalysis.ComponentInitial.CoprimeSeriesCoverTrivial

public section

open Subgroup

namespace CFSG.LieType.Steinberg.CentralExt.SylowEight

theorem exists_notMem_finset {A : Type*} [Finite A] (s : Finset A) (h : s.card < Nat.card A) :
    ∃ a, a ∉ s := by
  obtain ⟨a, -, ha⟩ := Set.exists_mem_notMem_of_ncard_lt_ncard (s := (s : Set A))
    (t := Set.univ) (by rwa [Set.ncard_coe_finset, Set.ncard_univ])
  exact ⟨a, ha⟩

theorem form_eq_zero {A : Type*} [Group A] [Finite A] (hcomm : ∀ a b : A, a * b = b * a)
    (hsq : ∀ a : A, a * a = 1) (h8 : Nat.card A = 8) {T : Type*} (σ : T → A → A)
    (htr : ∀ u v : A, u ≠ 1 → v ≠ 1 → ∃ t, σ t u = v) (B : A → A → ZMod 2)
    (hB₁ : ∀ u u' v, B (u * u') v = B u v + B u' v)
    (hB₂ : ∀ u v v', B u (v * v') = B u v + B u v')
    (hBσ : ∀ t u v, B (σ t u) (σ t v) = B u v) (u v : A) : B u v = 0 := by
  classical
  have hl : ∀ v, B 1 v = 0 := fun v => by
    have h := hB₁ 1 1 v
    rw [mul_one] at h
    exact left_eq_add.1 h
  have hr : ∀ u, B u 1 = 0 := fun u => by
    have h := hB₂ u 1 1
    rw [mul_one] at h
    exact left_eq_add.1 h
  have hinv : ∀ a : A, a⁻¹ = a := fun a => inv_eq_of_mul_eq_one_right (hsq a)
  have hne : ∀ a b : A, a ≠ b → a * b ≠ 1 := fun a b hab h =>
    hab ((hinv a).symm.trans (inv_eq_of_mul_eq_one_right h))
  have hdiag : ∀ a b : A, a ≠ 1 → b ≠ 1 → B a a = B b b := fun a b ha hb => by
    obtain ⟨t, rfl⟩ := htr a b ha hb
    rw [hBσ]
  have hs : ∀ a b : A, a ≠ 1 → b ≠ 1 → a ≠ b → B a b + B b a = B a a := fun a b ha hb hab => by
    have e := hdiag (a * b) a (hne a b hab) ha
    rw [hB₁, hB₂, hB₂, hdiag b a hb ha] at e
    have key : ∀ p q r : ZMod 2, p + q + (r + p) = p → q + r = p := by decide
    exact key _ _ _ e
  obtain ⟨x, hx⟩ := exists_notMem_finset ({1} : Finset A)
    (by rw [Finset.card_singleton, h8]; norm_num)
  rw [Finset.mem_singleton] at hx
  obtain ⟨y, hy⟩ := exists_notMem_finset ({1, x} : Finset A)
    (lt_of_le_of_lt Finset.card_le_two (by rw [h8]; norm_num))
  obtain ⟨z, hz⟩ := exists_notMem_finset ({1, x, y, x * y} : Finset A)
    (lt_of_le_of_lt Finset.card_le_four (by rw [h8]; norm_num))
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hy hz
  obtain ⟨hy1, hyx⟩ := hy
  obtain ⟨hz1, hzx, hzy, hzxy⟩ := hz
  have hxy1 : x * y ≠ 1 := hne x y (Ne.symm hyx)
  have hyzx : y * z ≠ x := fun h => hzxy (by
    calc z = y * (y * z) := by rw [← mul_assoc, hsq, one_mul]
      _ = x * y := by rw [h, hcomm])
  have hc : B x x = 0 := by
    have h1 := hs x (y * z) hx (hne y z (Ne.symm hzy)) (Ne.symm hyzx)
    rw [hB₂, hB₁] at h1
    have key : ∀ p q r s e : ZMod 2, p + q + (r + s) = e → p + r = e → q + s = e → e = 0 := by
      decide
    exact key _ _ _ _ _ h1 (hs x y hx hy1 (Ne.symm hyx)) (hs x z hx hz1 (Ne.symm hzx))
  have halt : ∀ a, B a a = 0 := fun a => by
    by_cases ha : a = 1
    · rw [ha, hl]
    · rw [hdiag a x ha hx, hc]
  have hsym : ∀ a b, B a b = B b a := fun a b => by
    by_cases ha : a = 1
    · rw [ha, hl, hr]
    by_cases hb : b = 1
    · rw [hb, hl, hr]
    by_cases hab : a = b
    · rw [hab]
    have h := hs a b ha hb hab
    rw [halt] at h
    have key : ∀ p q : ZMod 2, p + q = 0 → p = q := by decide
    exact key _ _ h
  have hgen : ∀ W : Subgroup A, x ∈ W → y ∈ W → z ∈ W → ∀ w, w ∈ W := by
    intro W hxW hyW hzW
    have h5 : 5 ≤ Nat.card W := by
      have hsub : (({1, x, y, x * y, z} : Finset A) : Set A) ⊆ W := by
        intro w hw
        simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
          Set.mem_singleton_iff] at hw
        rcases hw with rfl | rfl | rfl | rfl | rfl
        exacts [W.one_mem, hxW, hyW, W.mul_mem hxW hyW, hzW]
      have hcard : ({1, x, y, x * y, z} : Finset A).card = 5 := by
        rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
          Finset.card_insert_of_notMem, Finset.card_pair (Ne.symm hzxy)]
        · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
          exact ⟨fun h => hx (mul_eq_right.1 h.symm), Ne.symm hzy⟩
        · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
          exact ⟨Ne.symm hyx, fun h => hy1 (mul_eq_left.1 h.symm), Ne.symm hzx⟩
        · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
          exact ⟨Ne.symm hx, Ne.symm hy1, Ne.symm hxy1, Ne.symm hz1⟩
      have := Set.ncard_le_ncard hsub
      rwa [Set.ncard_coe_finset, hcard] at this
    have hdvd : Nat.card W ∣ 8 := h8 ▸ Subgroup.card_subgroup_dvd_card W
    have hW8 : Nat.card W = 8 := by
      have hle : Nat.card W ≤ 8 := Nat.le_of_dvd (by norm_num) hdvd
      interval_cases h : Nat.card W <;> omega
    intro w
    rw [Subgroup.eq_top_of_card_eq W (hW8.trans h8.symm)]
    exact Subgroup.mem_top w
  have hyx' : B y x = B x y := hsym y x
  have hzx' : B z x = B x z := hsym z x
  have hzy' : B z y = B y z := hsym z y
  have h01 : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide
  obtain ⟨r, hr1, hrx, hry, hrz⟩ : ∃ r, r ≠ 1 ∧ B r x = 0 ∧ B r y = 0 ∧ B r z = 0 := by
    rcases h01 (B x y) with hα | hα <;> rcases h01 (B x z) with hβ | hβ <;>
      rcases h01 (B y z) with hγ | hγ
    · exact ⟨x, hx, halt x, hα, hβ⟩
    · exact ⟨x, hx, halt x, hα, hβ⟩
    · exact ⟨y, hy1, hyx'.trans hα, halt y, hγ⟩
    · refine ⟨x * y, hxy1, ?_, ?_, ?_⟩ <;> simp only [hB₁, halt, hyx', hα, hβ, hγ] <;> decide
    · exact ⟨z, hz1, hzx'.trans hβ, hzy'.trans hγ, halt z⟩
    · refine ⟨x * z, hne x z (Ne.symm hzx), ?_, ?_, ?_⟩ <;>
        simp only [hB₁, halt, hzx', hzy', hα, hβ, hγ] <;> decide
    · refine ⟨y * z, hne y z (Ne.symm hzy), ?_, ?_, ?_⟩ <;>
        simp only [hB₁, halt, hyx', hzx', hzy', hα, hβ, hγ] <;> decide
    · refine ⟨x * y * z, hne (x * y) z (Ne.symm hzxy), ?_, ?_, ?_⟩ <;>
        simp only [hB₁, halt, hyx', hzx', hzy', hα, hβ, hγ] <;> decide
  let W : Subgroup A :=
    { carrier := {w | B r w = 0}
      mul_mem' := fun {a b} (ha : B r a = 0) (hb : B r b = 0) =>
        show B r (a * b) = 0 by rw [hB₂, ha, hb, add_zero]
      one_mem' := hr r
      inv_mem' := fun {a} (ha : B r a = 0) => show B r a⁻¹ = 0 by rwa [hinv] }
  have hrw : ∀ w, B r w = 0 := fun w => hgen W hrx hry hrz w
  by_cases hu : u = 1
  · rw [hu, hl]
  obtain ⟨t, ht⟩ := htr u r hu hr1
  rw [← hBσ t u v, ht, hrw]

theorem ker_eq_bot_of_sylow_eight {G : Type*} [Group G] [Finite G] (P : Sylow 2 G)
    (hab : ∀ x ∈ (P : Subgroup G), ∀ y ∈ (P : Subgroup G), x * y = y * x)
    (hsq : ∀ x ∈ (P : Subgroup G), x * x = 1)
    (h8 : Nat.card (P : Subgroup G) = 8)
    (hconj : ∀ x ∈ (P : Subgroup G), ∀ y ∈ (P : Subgroup G), x ≠ 1 → y ≠ 1 →
      ∃ g : G, g * x * g⁻¹ = y)
    {E : Type*} [Group E] [Finite E] [Group.IsPerfect E] (η : E →* G)
    (hη : Function.Surjective η) (hC : η.ker ≤ Subgroup.center E) (h2 : IsPGroup 2 η.ker) :
    η.ker = ⊥ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : IsMulCommutative P := ⟨⟨fun a b => Subtype.ext (hab a a.2 b b.2)⟩⟩
  set N : Subgroup G := normalizer ((P : Subgroup G) : Set G)
  set P' : Subgroup N := (P : Subgroup G).subgroupOf N
  have hPi : ¬ 2 ∣ (P : Subgroup G).index := P.not_dvd_index
  have hP'i : ¬ 2 ∣ P'.index := fun h => hPi (h.trans (relIndex_dvd_index_of_le le_normalizer))
  have hP'c : Nat.card P' = 8 := by
    rw [← h8]
    exact Nat.card_congr (subgroupOfEquivOfLe le_normalizer).toEquiv
  obtain ⟨H, hH⟩ := exists_right_complement'_of_coprime (N := P') (by
    rw [hP'c, show (8 : ℕ) = 2 ^ 3 by norm_num]
    exact Nat.Coprime.pow_left 3 ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 hP'i))
  have hHodd : Odd (Nat.card H) := by
    rw [← hH.symm.index_eq_card]
    exact Nat.odd_iff.2 (Nat.two_dvd_ne_zero.1 hP'i)
  let τ : H →* G := N.subtype.comp H.subtype
  have hτP : ∀ t : H, ∀ x ∈ (P : Subgroup G), τ t * x * (τ t)⁻¹ ∈ (P : Subgroup G) :=
    fun t x hx => ((t : N).2 x).1 hx
  have htr : ∀ x ∈ (P : Subgroup G), ∀ y ∈ (P : Subgroup G), x ≠ 1 → y ≠ 1 →
      ∃ t : H, τ t * x * (τ t)⁻¹ = y := by
    intro x hx y hy hx1 hy1
    obtain ⟨g, hg⟩ := hconj x hx y hy hx1 hy1
    obtain ⟨n, hn, hnx⟩ := P.conj_eq_normalizer_conj_of_mem x g⁻¹ hx (by rwa [inv_inv, hg])
    rw [inv_inv, hg] at hnx
    obtain ⟨⟨⟨⟨p, hpN⟩, hpP⟩, ⟨⟨h, hhN⟩, hhH⟩⟩, hph⟩ := hH.2 ⟨n⁻¹, inv_mem hn⟩
    have hph' : p * h = n⁻¹ := congrArg Subtype.val hph
    have hp : p ∈ (P : Subgroup G) := hpP
    have hhx : h * x * h⁻¹ ∈ (P : Subgroup G) := (hhN x).1 hx
    refine ⟨⟨⟨h, hhN⟩, hhH⟩, ?_⟩
    change h * x * h⁻¹ = y
    rw [hnx, ← inv_inv n, ← hph', inv_inv]
    calc h * x * h⁻¹ = h * x * h⁻¹ * p * p⁻¹ := by group
      _ = p * (h * x * h⁻¹) * p⁻¹ := by rw [hab _ hhx _ hp]
      _ = p * h * x * (p * h)⁻¹ := by group
  let ηT : E →* (⊤ : Subgroup G) := η.codRestrict ⊤ fun x => mem_top (η x)
  have hker : ηT.ker = η.ker := MonoidHom.ker_codRestrict η ⊤ _
  have hηT : Function.Surjective ηT := fun g => by
    obtain ⟨e, he⟩ := hη g
    exact ⟨e, Subtype.ext he⟩
  let S : ℕ → Subgroup G := fun
    | 0 => ⊥
    | _ + 1 => (P : Subgroup G)
  rw [← hker]
  refine CFSG.LocalAnalysis.ComponentInitial.ker_eq_bot_of_coprime_central_series ηT hηT
    (hker ▸ hC) (hker ▸ h2) (U := (P : Subgroup G)) le_top
    (P.isPGroup'.of_equiv (subgroupOfEquivOfLe le_top).symm)
    (by
      change ¬ 2 ∣ (P : Subgroup G).relIndex ⊤
      rwa [relIndex_top_right])
    hHodd τ (fun t => mem_top _) hτP 1 S rfl rfl ?_ ?_ ?_ ?_ ?_ ?_
  ·
    intro i hi
    obtain rfl : i = 0 := by omega
    exact bot_le
  ·
    intro i hi t x hx
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hi with rfl | rfl
    · have hx1 : x = 1 := mem_bot.1 hx
      rw [hx1, mul_one, mul_inv_cancel]
      exact one_mem _
    · exact hτP t x hx
  ·
    intro i hi x hx g hg
    obtain rfl : i = 0 := by omega
    change _ ∈ (⊥ : Subgroup G)
    rw [mem_bot, mul_assoc _ x g, hab x hx g hg]
    group
  ·
    intro i hi x hx
    obtain rfl : i = 0 := by omega
    change _ ∈ (⊥ : Subgroup G)
    rw [mem_bot, pow_two]
    exact hsq x hx
  ·
    intro i hi x hx hfx
    obtain rfl : i = 0 := by omega
    change x ∈ (⊥ : Subgroup G)
    rw [mem_bot]
    by_contra hx1
    obtain ⟨y, hy⟩ := exists_notMem_finset ({1, ⟨x, hx⟩} : Finset (P : Subgroup G))
      (lt_of_le_of_lt Finset.card_le_two (by rw [h8]; norm_num))
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hy
    obtain ⟨t, ht⟩ := htr x hx y y.2 hx1 fun h => hy.1 (Subtype.ext h)
    have h := hfx t
    change _ ∈ (⊥ : Subgroup G) at h
    rw [mem_bot, ht, inv_mul_eq_one] at h
    exact hy.2 (Subtype.ext h)
  ·
    intro i hi j hj b hb₁ hb₂ _ _ hbτ x hx y hy
    obtain rfl : i = 0 := by omega
    obtain rfl : j = 0 := by omega
    refine form_eq_zero (A := (P : Subgroup G)) (fun a a' => Subtype.ext (hab a a.2 a' a'.2))
      (fun a => Subtype.ext (hsq a a.2)) h8
      (fun t a => (⟨τ t * a * (τ t)⁻¹, hτP t a a.2⟩ : (P : Subgroup G))) ?_
      (fun a a' => b a a') (fun a a' c => hb₁ a a.2 a' a'.2 c c.2)
      (fun a c c' => hb₂ a a.2 c c.2 c' c'.2) (fun t a a' => hbτ t a a.2 a' a'.2)
      ⟨x, hx⟩ ⟨y, hy⟩
    intro a a' ha ha'
    obtain ⟨t, ht⟩ := htr a a.2 a' a'.2 (fun h => ha (Subtype.ext h))
      (fun h => ha' (Subtype.ext h))
    exact ⟨t, Subtype.ext ht⟩

end CFSG.LieType.Steinberg.CentralExt.SylowEight
