module

public import CFSG.Open.LocalVocabulary
import CFSG.LocalAnalysis.SectionRank.QTK.CoverBSigned
import CFSG.LocalAnalysis.SectionRank.QTK.Witness3

public section

namespace CFSG.SectionRank.QTK.CentreFact

open Subgroup
open scoped commutatorElement

section Lifts

variable {Y : Type*} [Group Y]

theorem conj_swap_of_conj_eq_mul {c x y : Y} (hxy : x * y * x⁻¹ = c * y) :
    y * x * y⁻¹ = c⁻¹ * x :=
  calc y * x * y⁻¹ = c⁻¹ * (c * y) * x * y⁻¹ := by group
    _ = c⁻¹ * (x * y * x⁻¹) * x * y⁻¹ := by rw [hxy]
    _ = c⁻¹ * x := by group

theorem commutator_inv_mul_pow {c x y : Y} (hc : c ∈ center Y) (hxy : x * y * x⁻¹ = c * y)
    (k l : ℕ) : ⁅x⁻¹, x ^ k * y ^ l⁆ = (c ^ l)⁻¹ := by
  have hxyl : x * y ^ l * x⁻¹ = c ^ l * y ^ l := by
    rw [← conj_pow, hxy, (Commute.mul_pow ((mem_center_iff.mp hc y).symm) l)]
  have hswap := conj_swap_of_conj_eq_mul hxyl
  have hz : (c ^ l)⁻¹ ∈ center Y := inv_mem (pow_mem hc l)
  calc ⁅x⁻¹, x ^ k * y ^ l⁆
      = x⁻¹ * x ^ k * (y ^ l * x * (y ^ l)⁻¹) * (x ^ k)⁻¹ := by
        rw [commutatorElement_def]; group
    _ = x⁻¹ * x ^ k * ((c ^ l)⁻¹ * x) * (x ^ k)⁻¹ := by rw [hswap]
    _ = (x⁻¹ * x ^ k * (c ^ l)⁻¹) * x * (x ^ k)⁻¹ := by group
    _ = ((c ^ l)⁻¹ * (x⁻¹ * x ^ k)) * x * (x ^ k)⁻¹ := by
        rw [mem_center_iff.mp hz (x⁻¹ * x ^ k)]
    _ = (c ^ l)⁻¹ := by group

theorem commute_of_pair {r : ℕ} (hr : r.Prime) {x y d : Y} {k l : ℕ} (hc : ⁅x, y⁆ ∈ center Y)
    (hxr : x ^ r ∈ center Y) (hdx : x * (d * x * d⁻¹) ∈ center Y)
    (hdy : (x ^ k * y ^ l)⁻¹ * (d * y * d⁻¹) ∈ center Y) (hl : ¬ r ∣ l + 1) :
    Commute x y := by
  set c := ⁅x, y⁆ with hcdef
  have hxy : x * y * x⁻¹ = c * y := by rw [hcdef, commutatorElement_def]; group
  have hcr : c ^ r = 1 := by
    have h1 := CFSG.SectionRank.QTK.conj_pow_eq_of_mem_center hc hxy r
    have h2 : x ^ r * y * (x ^ r)⁻¹ = y := by
      rw [← mem_center_iff.mp hxr y, mul_inv_cancel_right]
    rw [h2] at h1
    exact mul_right_cancel (h1.symm.trans (one_mul y).symm)
  have hconj : d * c * d⁻¹ = (c ^ l)⁻¹ := by
    have h5 : d * c * d⁻¹ = ⁅d * x * d⁻¹, d * y * d⁻¹⁆ := by
      rw [hcdef]; simp only [commutatorElement_def]; group
    have hdx' : d * x * d⁻¹ = x⁻¹ * (x * (d * x * d⁻¹)) := by group
    have hdy' : d * y * d⁻¹ = (x ^ k * y ^ l) * ((x ^ k * y ^ l)⁻¹ * (d * y * d⁻¹)) := by group
    rw [h5, hdx', hdy', CFSG.SectionRank.commutatorElement_mul_central_left hdx,
      CFSG.SectionRank.commutatorElement_mul_central_right hdy,
      commutator_inv_mul_pow hc hxy k l]
  have hfix : d * c * d⁻¹ = c := by rw [mem_center_iff.mp hc d, mul_inv_cancel_right]
  have hcl : c ^ (l + 1) = 1 := by
    have h : c = (c ^ l)⁻¹ := hfix.symm.trans hconj
    rw [pow_succ', ← eq_inv_iff_mul_eq_one]
    exact h
  have hcop : Nat.Coprime r (l + 1) := (Nat.Prime.coprime_iff_not_dvd hr).mpr hl
  have hc1 : c = 1 := (pow_eq_one_iff_of_coprime hcop).mp ⟨hcr, hcl⟩
  exact commutatorElement_eq_one_iff_mul_comm.mp hc1

end Lifts

variable {G : Type} [Group G] [Finite G]

theorem not_dvd_card_center_of_pair (he : CFSG.Open.evenRank G ≤ 2) {Y : Subgroup G}
    {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) {R : Subgroup (↥Y ⧸ center ↥Y)} (hR : R ≠ ⊥)
    (hR2 : IsPGroup 2 R) {a b d₁ d₂ : ↥Y ⧸ center ↥Y}
    (ha : a ∈ normalizer (R : Set (↥Y ⧸ center ↥Y)))
    (hb : b ∈ normalizer (R : Set (↥Y ⧸ center ↥Y))) (har : a ^ r = 1) (hbr : b ^ r = 1)
    (hab : a * b = b * a) (hind : ∀ i j : ℕ, i < r → j < r → a ^ i * b ^ j = 1 → i = 0 ∧ j = 0)
    (hd₁a : d₁ * a * d₁⁻¹ = a⁻¹) {k l : ℕ} (hd₁b : d₁ * b * d₁⁻¹ = a ^ k * b ^ l)
    (hl : ¬ r ∣ l + 1) (hd₂b : d₂ * b * d₂⁻¹ = b⁻¹) : ¬ r ∣ Nat.card (center ↥Y) := by
  intro hrZ
  have : Fact r.Prime := ⟨hr⟩
  have hodd : r % 2 = 1 := Nat.odd_iff.mp (hr.odd_of_ne_two hr2)
  obtain ⟨x₀, hx₀⟩ := QuotientGroup.mk'_surjective (center ↥Y) a
  obtain ⟨y₀, hy₀⟩ := QuotientGroup.mk'_surjective (center ↥Y) b
  obtain ⟨e₁, he₁⟩ := QuotientGroup.mk'_surjective (center ↥Y) d₁
  obtain ⟨e₂, he₂⟩ := QuotientGroup.mk'_surjective (center ↥Y) d₂
  set π := QuotientGroup.mk' (center ↥Y) with hπ
  have hmem : ∀ g : ↥Y, π g = 1 → g ∈ center ↥Y := fun g h => (QuotientGroup.eq_one_iff g).mp h
  have hπZ : ∀ g ∈ center ↥Y, π g = 1 := fun g h => (QuotientGroup.eq_one_iff g).mpr h
  obtain ⟨v₁, hv₁, hx⟩ := CoverB.exists_mem_center_pow_eq_one hodd (x := x₀) (d := e₁)
    (hmem _ (by rw [map_pow, hx₀, har]))
    (hmem _ (by rw [map_mul, map_mul, map_mul, map_inv, hx₀, he₁, hd₁a, mul_inv_cancel]))
  obtain ⟨v₂, hv₂, hy⟩ := CoverB.exists_mem_center_pow_eq_one hodd (x := y₀) (d := e₂)
    (hmem _ (by rw [map_pow, hy₀, hbr]))
    (hmem _ (by rw [map_mul, map_mul, map_mul, map_inv, hy₀, he₂, hd₂b, mul_inv_cancel]))
  have hπx : π (x₀ * v₁) = a := by rw [map_mul, hx₀, hπZ _ hv₁, mul_one]
  have hπy : π (y₀ * v₂) = b := by rw [map_mul, hy₀, hπZ _ hv₂, mul_one]
  generalize x₀ * v₁ = x at hx hπx
  generalize y₀ * v₂ = y at hy hπy
  have hc0 : ⁅x, y⁆ ∈ center ↥Y := hmem _ (by
    rw [map_commutatorElement, hπx, hπy, commutatorElement_eq_one_iff_mul_comm]; exact hab)
  have hdx : x * (e₁ * x * e₁⁻¹) ∈ center ↥Y := hmem _ (by
    simp only [map_mul, map_inv, hπx, he₁]; rw [hd₁a, mul_inv_cancel])
  have hdy : (x ^ k * y ^ l)⁻¹ * (e₁ * y * e₁⁻¹) ∈ center ↥Y := hmem _ (by
    simp only [map_mul, map_inv, map_pow, hπx, hπy, he₁]; rw [hd₁b, inv_mul_cancel])
  have hxy : Commute x y := commute_of_pair hr hc0 (by rw [hx]; exact one_mem _) hdx hdy hl
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := ↥(center ↥Y)) r hrZ
  have hzr : (z : ↥Y) ^ r = 1 := by
    rw [← orderOf_dvd_iff_pow_eq_one, Subgroup.orderOf_coe, hz]
  have hzo : orderOf (z : ↥Y) = r := by rw [Subgroup.orderOf_coe, hz]
  have : NeZero r := ⟨hr.ne_zero⟩
  set g' : Fin 3 → ↥Y := ![x, y, (z : ↥Y)] with hg'
  have hg'p : ∀ i, g' i ^ r = 1 := fun i => by
    fin_cases i
    · exact hx
    · exact hy
    · exact hzr
  have hzc : ∀ g : ↥Y, Commute (z : ↥Y) g := fun g => (mem_center_iff.mp z.2 g).symm
  have hcomm' : ∀ i j, Commute (g' i) (g' j) := by
    intro i j
    fin_cases i <;> fin_cases j
    all_goals first
      | exact Commute.refl _
      | exact hxy
      | exact hxy.symm
      | exact hzc _
      | exact (hzc _).symm
  let ψ : Fin 3 → Multiplicative (ZMod r) →* ↥Y :=
    fun i => CFSG.SectionRank.zmodPowHom (g' i) (hg'p i)
  have hψcomm : Pairwise fun i j => ∀ (u v : Multiplicative (ZMod r)),
      Commute (ψ i u) (ψ j v) := fun i j _ u v => (hcomm' i j).pow_pow _ _
  let Ψ : (Fin 3 → Multiplicative (ZMod r)) →* ↥Y := MonoidHom.noncommPiCoprod ψ hψcomm
  have hΨ : ∀ f, Ψ f = x ^ (Multiplicative.toAdd (f 0)).val *
      y ^ (Multiplicative.toAdd (f 1)).val *
      (z : ↥Y) ^ (Multiplicative.toAdd (f 2)).val := by
    intro f
    have hf : f = Pi.mulSingle 0 (f 0) * Pi.mulSingle 1 (f 1) * Pi.mulSingle 2 (f 2) := by
      funext i
      fin_cases i <;> simp
    conv_lhs => rw [hf]
    rw [map_mul, map_mul, MonoidHom.noncommPiCoprod_mulSingle,
      MonoidHom.noncommPiCoprod_mulSingle, MonoidHom.noncommPiCoprod_mulSingle]
    rfl
  have hπΨ : ∀ f, π (Ψ f) = a ^ (Multiplicative.toAdd (f 0)).val *
      b ^ (Multiplicative.toAdd (f 1)).val := fun f => by
    rw [hΨ, map_mul, map_mul, map_pow, map_pow, map_pow, hπx, hπy, hπZ _ z.2, one_pow, mul_one]
  have hΨinj : Function.Injective Ψ := by
    rw [injective_iff_map_eq_one]
    intro f hf
    obtain ⟨h0, h1⟩ := hind _ _ (ZMod.val_lt _) (ZMod.val_lt _)
      (by rw [← hπΨ, hf, map_one])
    rw [hΨ, h0, h1, pow_zero, pow_zero, one_mul, one_mul] at hf
    have h2 : (Multiplicative.toAdd (f 2)).val = 0 := by
      have hd := orderOf_dvd_of_pow_eq_one hf
      rw [hzo] at hd
      exact Nat.eq_zero_of_dvd_of_lt hd (ZMod.val_lt _)
    funext i
    apply Multiplicative.toAdd.injective
    fin_cases i
    · exact (ZMod.val_eq_zero _).mp h0
    · exact (ZMod.val_eq_zero _).mp h1
    · exact (ZMod.val_eq_zero _).mp h2
  have hEel : CFSG.Open.IsElemAbelian r Ψ.range := by
    refine ⟨⟨⟨fun u v => ?_⟩⟩, fun w hw => ?_⟩
    · obtain ⟨f, hf⟩ := MonoidHom.mem_range.1 u.2
      obtain ⟨f', hf'⟩ := MonoidHom.mem_range.1 v.2
      apply Subtype.ext
      change (u : ↥Y) * v = v * u
      rw [← hf, ← hf', ← map_mul, ← map_mul, mul_comm]
    · obtain ⟨f, rfl⟩ := MonoidHom.mem_range.1 hw
      have hfr : f ^ r = 1 := by
        funext i
        apply Multiplicative.toAdd.injective
        rw [Pi.pow_apply, toAdd_pow, Pi.one_apply, toAdd_one, nsmul_eq_mul, CharP.cast_eq_zero,
          zero_mul]
      rw [← map_pow, hfr, map_one]
  have hEcard : Nat.card Ψ.range = r ^ 3 := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hΨinj).toEquiv, Nat.card_pi, Finset.prod_const,
      Finset.card_univ, Fintype.card_fin, Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]
  obtain ⟨R₂, hR₂, hR₂2, hR₂N⟩ := exists_two_subgroup_normalized hR hR2
  have hEN : Ψ.range ≤ normalizer (R₂ : Set ↥Y) := by
    rintro _ ⟨f, rfl⟩
    refine hR₂N _ ?_
    change π (Ψ f) ∈ _
    rw [hπΨ]
    exact mul_mem (pow_mem ha _) (pow_mem hb _)
  have hE'N : Ψ.range.map Y.subtype ≤ normalizer ((R₂.map Y.subtype : Subgroup G) : Set G) :=
    (Subgroup.map_mono hEN).trans (Subgroup.le_normalizer_map _)
  have hE'card : Nat.card (Ψ.range.map Y.subtype) = r ^ 3 := by
    rw [Subgroup.card_map_of_injective Y.subtype_injective, hEcard]
  have hR₂' : R₂.map Y.subtype ≠ ⊥ := fun h =>
    hR₂ ((Subgroup.map_eq_bot_iff_of_injective _ Y.subtype_injective).mp h)
  have := le_two_of_evenRank_le_two he hR₂' (hR₂2.map _) hr hr2 (isElemAbelian_map _ hEel)
    hE'N hE'card
  omega

theorem not_dvd_card_center_of_pair_equiv (he : CFSG.Open.evenRank G ≤ 2) {Y : Subgroup G}
    {T : Type} [Group T] (e : ↥Y ⧸ center ↥Y ≃* T) {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    {R : Subgroup T} (hR : R ≠ ⊥) (hR2 : IsPGroup 2 R) {a b d₁ d₂ : T}
    (ha : a ∈ normalizer (R : Set T)) (hb : b ∈ normalizer (R : Set T)) (har : a ^ r = 1)
    (hbr : b ^ r = 1) (hab : a * b = b * a)
    (hind : ∀ i j : ℕ, i < r → j < r → a ^ i * b ^ j = 1 → i = 0 ∧ j = 0)
    (hd₁a : d₁ * a * d₁⁻¹ = a⁻¹) {k l : ℕ} (hd₁b : d₁ * b * d₁⁻¹ = a ^ k * b ^ l)
    (hl : ¬ r ∣ l + 1) (hd₂b : d₂ * b * d₂⁻¹ = b⁻¹) : ¬ r ∣ Nat.card (center ↥Y) := by
  have hmap : ∀ x : T, x ∈ normalizer (R : Set T) →
      e.symm x ∈ normalizer ((R.map e.symm.toMonoidHom : Subgroup _) : Set _) := fun x hx => by
    rw [← Subgroup.map_equiv_normalizer_eq]
    exact Subgroup.mem_map_of_mem _ hx
  refine not_dvd_card_center_of_pair he hr hr2 (R := R.map e.symm.toMonoidHom)
    (fun h => hR ((Subgroup.map_eq_bot_iff_of_injective _ e.symm.injective).mp h))
    (hR2.map _) (hmap a ha) (hmap b hb) (by rw [← map_pow, har, map_one])
    (by rw [← map_pow, hbr, map_one]) (by rw [← map_mul, hab, map_mul])
    (fun i j hi hj h => hind i j hi hj (e.symm.injective (by rw [map_mul, map_pow, map_pow, h,
      map_one]))) (d₁ := e.symm d₁) (d₂ := e.symm d₂) ?_ (k := k) (l := l) ?_ hl ?_
  · rw [← map_mul, ← map_inv, ← map_mul, hd₁a, map_inv]
  · rw [← map_mul, ← map_inv, ← map_mul, hd₁b, map_mul, map_pow, map_pow]
  · rw [← map_mul, ← map_inv, ← map_mul, hd₂b, map_inv]

theorem not_dvd_card_center_of_pair_inv (he : CFSG.Open.evenRank G ≤ 2) {Y : Subgroup G}
    {T : Type} [Group T] (e : ↥Y ⧸ center ↥Y ≃* T) {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    {t a b d₁ d₂ : T} (ht : t ^ 2 = 1) (ht1 : t ≠ 1) (hta : Commute a t) (htb : Commute b t)
    (har : a ^ r = 1) (hbr : b ^ r = 1) (hab : a * b = b * a)
    (hind : ∀ i j : ℕ, i < r → j < r → a ^ i * b ^ j = 1 → i = 0 ∧ j = 0)
    (hd₁a : d₁ * a * d₁⁻¹ = a⁻¹) {k l : ℕ} (hd₁b : d₁ * b * d₁⁻¹ = a ^ k * b ^ l)
    (hl : ¬ r ∣ l + 1) (hd₂b : d₂ * b * d₂⁻¹ = b⁻¹) : ¬ r ∣ Nat.card (center ↥Y) :=
  not_dvd_card_center_of_pair_equiv he e hr hr2 (R := zpowers t)
    (fun h => ht1 (Subgroup.zpowers_eq_bot.mp h)) (isPGroup_zpowers_of_sq ht)
    (mem_normalizer_zpowers hta) (mem_normalizer_zpowers htb) har hbr hab hind hd₁a hd₁b hl hd₂b

end CFSG.SectionRank.QTK.CentreFact
