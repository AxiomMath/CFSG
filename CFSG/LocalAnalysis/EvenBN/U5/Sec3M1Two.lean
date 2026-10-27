module

public import CFSG.LocalAnalysis.EvenBN.U5.Sec3M1One
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card

public noncomputable section

namespace CFSG.LocalAnalysis.EvenBN.U5

open Subgroup CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.RankThree.PartOne.U5K.Hyp
open CFSG.ABGLocalTools (IsSylowOf isSylowOf_of_card)

namespace Data

variable {G : Type} [Group G] [Finite G] {f : ℕ} {K : Type} [Field K]
  {h : UnitaryFieldData 2 f K} {d : Data G h}

@[expose] def U₁ (d : Data G h) : Subgroup G := d.pull (patSub h sI₁ isPattern_sI₁)

@[expose] def D₁ (d : Data G h) : Subgroup G := (d.η.comp (dHom h)).range

omit [Finite G] in
theorem U₁_le_N₁ (d : Data G h) : d.U₁ ≤ d.N₁ := d.pull_mono patSub_I₁_le_N₁sub

omit [Finite G] in
theorem U₁_le_P (d : Data G h) : d.U₁ ≤ d.P := d.pull_mono (patSub_le_U _ _)

omit [Finite G] in
theorem card_U₁ (d : Data G h) : Nat.card d.U₁ = (2 ^ f) ^ 2 := by
  rw [U₁, d.card_pull (patSub_le_U _ _), card_patSub_I₁]

omit [Finite G] in
theorem U₁_eq (d : Data G h) (hf : 2 ≤ f) : d.U₁ = d.P ⊓ centralizer (d.I₁ : Set G) :=
  (d.P_inf_centralizer_I₁ hf).symm

omit [Finite G] in
theorem exists_eq_η_uSU {u : G} (hu : u ∈ d.U₁) : ∃ c : K, u = d.η (uSU h c) := by
  obtain ⟨g, hg, rfl⟩ := hu
  exact ⟨mat g ιe₁ ιe₂, by rw [← eq_uSU_of_mem hg]⟩

omit [Finite G] in
theorem η_uSU_mem (d : Data G h) (c : K) : d.η (uSU h c) ∈ d.U₁ := ⟨_, uSU_mem_patSub c, rfl⟩

omit [Finite G] in
theorem η_uSU_injective (d : Data G h) : Function.Injective fun c : K => d.η (uSU h c) :=
  fun a b e => uSU_injective (d.η_injOn (patSub_le_U _ _ (uSU_mem_patSub a))
    (patSub_le_U _ _ (uSU_mem_patSub b)) e)

omit [Finite G] in
theorem mul_self_of_mem_U₁ {u : G} (hu : u ∈ d.U₁) : u * u = 1 := by
  obtain ⟨g, hg, rfl⟩ := hu
  rw [← map_mul, mul_self_of_mem_patSub_I₁ hg, map_one]

omit [Finite G] in
theorem η_injOn_N₁ (d : Data G h) {g g' : hypSU h 2 1} (hg : g ∈ N₁sub h) (hg' : g' ∈ N₁sub h)
    (e : d.η g = d.η g') : g = g' := by
  have hk : g⁻¹ * g' ∈ N₁sub h ⊓ hypScalars h 2 1 :=
    Subgroup.mem_inf.2 ⟨mul_mem (inv_mem hg) hg',
      (d.η_eq_one_iff _).1 (by rw [map_mul, map_inv, e, inv_mul_cancel])⟩
  rw [N₁sub_inf_hypScalars, mem_bot] at hk
  exact inv_mul_eq_one.1 hk

omit [Finite G] in
theorem card_N₁ (d : Data G h) : Nat.card d.N₁ = (2 ^ f) ^ 2 * ((2 ^ f) ^ 4 - 1) := by
  classical
  have := h.finite
  let := Fintype.ofFinite K
  have hq : 1 < Fintype.card K := Fintype.one_lt_card
  have hcard : Fintype.card K = (2 ^ f) ^ 2 := by rw [← Nat.card_eq_fintype_card, h.card_eq_sq]
  rw [← Nat.card_congr d.N₁equiv.toEquiv, Matrix.card_SL_field, Fin.prod_univ_two, Fin.val_zero,
    Fin.val_one, pow_zero, pow_one, show Fintype.card K ^ 2 - Fintype.card K =
      Fintype.card K * (Fintype.card K - 1) by rw [Nat.mul_sub_one, sq], ← mul_assoc,
    Nat.mul_div_cancel _ (by omega), mul_comm, hcard,
    show ((2 ^ f) ^ 2) ^ 2 = (2 ^ f) ^ 4 by ring]

theorem Hyp.isSylowOf_U₁_N₁ (hd : d.Hyp) : IsSylowOf 2 d.U₁ d.N₁ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine isSylowOf_of_card d.U₁_le_N₁ ?_
  have hodd : ¬ 2 ∣ (2 ^ f) ^ 4 - 1 := by
    have h1 : 1 ≤ (2 ^ f) ^ 4 := Nat.one_le_pow _ _ (by positivity)
    have h2 : Even ((2 ^ f) ^ 4) :=
      (Nat.even_pow.2 ⟨Nat.even_pow.2 ⟨even_two, by have := hd.two_le; omega⟩, by norm_num⟩)
    exact Nat.not_even_iff_odd.2 (Nat.Even.sub_odd h1 h2 odd_one) ∘ (even_iff_two_dvd.2)
  have hne : (2 ^ f) ^ 4 - 1 ≠ 0 := fun e => hodd (e ▸ dvd_zero 2)
  rw [d.card_U₁, d.card_N₁, Nat.factorization_mul (by positivity) hne,
    Finsupp.add_apply, Nat.factorization_eq_zero_of_not_dvd hodd, add_zero, ← pow_mul,
    Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same, pow_mul]

omit [Finite G] in
theorem η_dHom_mem (d : Data G h) (α : Kˣ) : d.η (dHom h α) ∈ d.D₁ := ⟨α, rfl⟩

omit [Finite G] in
theorem D₁_le_N₁ (d : Data G h) : d.D₁ ≤ d.N₁ := by
  rintro _ ⟨α, rfl⟩
  exact ⟨_, dHom_mem_N₁sub α, rfl⟩

omit [Finite G] in
theorem D₁_le_I (d : Data G h) : d.D₁ ≤ d.I := by
  rintro _ ⟨α, rfl⟩
  exact ⟨_, dHom_mem_Isub α, rfl⟩

omit [Finite G] in
theorem η_dHom_injective (d : Data G h) : Function.Injective (d.η.comp (dHom h)) :=
  fun α β e => dHom_injective (d.η_injOn_N₁ (dHom_mem_N₁sub α) (dHom_mem_N₁sub β) e)

omit [Finite G] in
theorem isCyclic_D₁ (d : Data G h) : IsCyclic d.D₁ := by
  have := h.finite
  exact isCyclic_of_surjective _ (d.η.comp (dHom h)).rangeRestrict_surjective

omit [Finite G] in
theorem card_D₁ (d : Data G h) : Nat.card d.D₁ = (2 ^ f) ^ 2 - 1 := by
  have := h.finite
  rw [D₁, Nat.card_congr (MonoidHom.ofInjective d.η_dHom_injective).toEquiv.symm, Nat.card_units,
    h.card_eq_sq]

omit [Finite G] in
theorem η_dHom_conj (d : Data G h) (α : Kˣ) (c : K) :
    d.η (dHom h α) * d.η (uSU h c) * (d.η (dHom h α))⁻¹ = d.η (uSU h ((α : K) ^ 2 * c)) := by
  rw [← map_inv, ← map_mul, ← map_mul, dHom_conj_uSU]

theorem D₁_le_normalizer_U₁ (d : Data G h) : d.D₁ ≤ normalizer (d.U₁ : Set G) := by
  rintro _ ⟨α, rfl⟩
  refine mem_normalizer_fintype fun u hu => ?_
  obtain ⟨c, rfl⟩ := exists_eq_η_uSU hu
  change d.η (dHom h α) * d.η (uSU h c) * (d.η (dHom h α))⁻¹ ∈ d.U₁
  rw [d.η_dHom_conj]
  exact d.η_uSU_mem _

theorem odd_card_D₁ (hd : d.Hyp) : Odd (Nat.card d.D₁) := by
  rw [d.card_D₁]
  have h1 : 1 ≤ (2 ^ f) ^ 2 := Nat.one_le_pow _ _ (by positivity)
  have h2 : Even ((2 ^ f) ^ 2) :=
    Nat.even_pow.2 ⟨Nat.even_pow.2 ⟨even_two, by have := hd.two_le; omega⟩, by norm_num⟩
  exact Nat.Even.sub_odd h1 h2 odd_one

theorem Hyp.D₁_inf_U₁ (hd : d.Hyp) : d.D₁ ⊓ d.U₁ = ⊥ := by
  refine eq_bot_iff.2 fun x hx => ?_
  obtain ⟨hxD, hxU⟩ := Subgroup.mem_inf.1 hx
  have h1 : orderOf x ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [sq, mul_self_of_mem_U₁ hxU])
  have h2 : orderOf x ∣ Nat.card d.D₁ := by
    rw [← Subgroup.orderOf_mk x hxD]
    exact orderOf_dvd_natCard _
  have hcop : Nat.Coprime 2 (Nat.card d.D₁) := Nat.coprime_two_left.2 (d.odd_card_D₁ hd)
  exact mem_bot.2 (orderOf_eq_one_iff.1 (Nat.Coprime.eq_one_of_dvd
    (Nat.Coprime.coprime_dvd_left h1 hcop) h2))

theorem Hyp.D₁_le_centralizer_t (hd : d.Hyp) : d.D₁ ≤ centralizer ({d.t} : Set G) :=
  (d.D₁_le_N₁.trans (d.pull_le_L _)).trans hd.L_le_centralizer

theorem U₁_sup_D₁ (d : Data G h) :
    d.U₁ ⊔ d.D₁ = d.N₁ ⊓ normalizer (d.U₁ : Set G) := by
  refine le_antisymm (sup_le (le_inf d.U₁_le_N₁ le_normalizer)
    (le_inf d.D₁_le_N₁ d.D₁_le_normalizer_U₁)) fun x hx => ?_
  obtain ⟨hxN, hxU⟩ := Subgroup.mem_inf.1 hx
  obtain ⟨g, hg, rfl⟩ := hxN
  have h1 : d.η g * d.η (uSU h 1) * (d.η g)⁻¹ ∈ d.U₁ :=
    (mem_normalizer_iff.1 hxU _).1 (d.η_uSU_mem 1)
  rw [← map_inv, ← map_mul, ← map_mul] at h1
  obtain ⟨w, hw, hwe⟩ := h1
  have hgN : g * uSU h 1 * g⁻¹ ∈ N₁sub h :=
    mul_mem (mul_mem hg (uSU_mem_N₁sub 1)) (inv_mem hg)
  have e := d.η_injOn_N₁ (patSub_I₁_le_N₁sub hw) hgN hwe
  obtain ⟨c, α, rfl⟩ := exists_eq_uSU_mul_dHom hg (e ▸ hw)
  rw [map_mul]
  exact mul_mem (mem_sup_left (d.η_uSU_mem c)) (mem_sup_right (d.η_dHom_mem α))

omit [Finite G] in
theorem D₁_regular_U₁ (d : Data G h) :
    ∀ u ∈ d.U₁, u ≠ 1 → ∀ w ∈ d.U₁, w ≠ 1 → ∃! x : d.D₁, (x : G) * u * (x : G)⁻¹ = w := by
  have := h.charP
  have := h.finite
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro u hu hu1 w hw hw1
  obtain ⟨a, rfl⟩ := exists_eq_η_uSU hu
  obtain ⟨b, rfl⟩ := exists_eq_η_uSU hw
  have ha : a ≠ 0 := fun e => hu1 (by rw [e, uSU_zero, map_one])
  have hb : b ≠ 0 := fun e => hw1 (by rw [e, uSU_zero, map_one])
  have key : ∀ α : Kˣ, d.η (dHom h α) * d.η (uSU h a) * (d.η (dHom h α))⁻¹ =
      d.η (uSU h b) ↔ (α : K) ^ 2 = b / a := by
    intro α
    rw [d.η_dHom_conj, (d.η_uSU_injective).eq_iff]
    constructor
    · intro e
      rw [← e]
      field_simp
    · intro e
      rw [e]
      field_simp
  obtain ⟨y, hy⟩ := (Finite.injective_iff_surjective.1 (frobenius_inj K 2)) (b / a)
  rw [frobenius_def] at hy
  have hy0 : y ≠ 0 := by
    rintro rfl
    rw [zero_pow two_ne_zero] at hy
    exact div_ne_zero hb ha hy.symm
  refine ⟨⟨_, d.η_dHom_mem (Units.mk0 y hy0)⟩, (key _).2 hy, fun x hx => ?_⟩
  obtain ⟨β, hβ⟩ := x.2
  have hβ' : d.η (dHom h β) = x := hβ
  have h1 := (key β).1 (by rw [hβ']; exact hx)
  apply Subtype.ext
  rw [← hβ']
  change d.η (dHom h β) = d.η (dHom h (Units.mk0 y hy0))
  congr 2
  exact Units.ext ((frobenius_inj K 2) (by
    rw [frobenius_def, frobenius_def, Units.val_mk0, h1, hy]))

end Data

end CFSG.LocalAnalysis.EvenBN.U5
