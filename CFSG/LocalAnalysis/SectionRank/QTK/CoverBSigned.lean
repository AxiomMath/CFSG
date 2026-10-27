module

public import CFSG.LocalAnalysis.SectionRank.QTK.SectionLiftB
public import CFSG.LocalAnalysis.SectionRank.SignLines

public section

namespace CFSG.SectionRank.QTK.CoverB

open Subgroup
open scoped commutatorElement

section Lifts

variable {Y : Type*} [Group Y]

theorem exists_mem_center_pow_eq_one {r : ℕ} (hr : r % 2 = 1) {x d : Y}
    (hxr : x ^ r ∈ center Y) (hdx : x * (d * x * d⁻¹) ∈ center Y) :
    ∃ v ∈ center Y, (x * v) ^ r = 1 := by
  set w := x * (d * x * d⁻¹) with hw
  set c := x ^ r with hc
  have hcen : ∀ a ∈ center Y, ∀ g : Y, Commute a g := fun a ha g =>
    (mem_center_iff.mp ha g).symm
  have hdx' : d * x * d⁻¹ = x⁻¹ * w := by rw [hw]; group
  have hfix : d * c * d⁻¹ = c := by rw [(hcen c hxr d).symm.eq, mul_inv_cancel_right]
  have hpow : d * c * d⁻¹ = c⁻¹ * w ^ r := by
    rw [hc, ← conj_pow, hdx', (hcen w hdx x⁻¹).symm.mul_pow, inv_pow]
  have hcc : c * c = w ^ r := by
    calc c * c = c * (c⁻¹ * w ^ r) := by rw [← hpow, hfix]
      _ = w ^ r := mul_inv_cancel_left c _
  have hvZ : (w ^ ((r + 1) / 2) * c⁻¹)⁻¹ ∈ center Y :=
    inv_mem (mul_mem (pow_mem hdx _) (inv_mem hxr))
  refine ⟨(w ^ ((r + 1) / 2) * c⁻¹)⁻¹, hvZ, ?_⟩
  have hac : Commute (w ^ ((r + 1) / 2)) c⁻¹ := ((hcen w hdx c).pow_left _).inv_right
  have hdp : (w ^ ((r + 1) / 2) * c⁻¹) ^ r = c := by
    rw [hac.mul_pow, ← pow_mul, mul_comm, pow_mul, ← hcc, inv_pow]
    rw [(Commute.refl c).mul_pow, ← pow_add]
    have : (r + 1) / 2 + (r + 1) / 2 = r + 1 := by omega
    rw [this, pow_succ, ((Commute.refl c).pow_left r).eq, mul_inv_cancel_right]
  rw [(hcen _ hvZ x).symm.mul_pow, inv_pow, hdp, mul_inv_cancel]

theorem commute_of_sign {r : ℕ} (hr : r % 2 = 1) {x y d : Y} (hc : ⁅x, y⁆ ∈ center Y)
    (hxr : x ^ r ∈ center Y) (hdx : x * (d * x * d⁻¹) ∈ center Y)
    (hdy : y⁻¹ * (d * y * d⁻¹) ∈ center Y) : Commute x y := by
  set c := ⁅x, y⁆ with hcdef
  have hxy : x * y * x⁻¹ = c * y := by rw [hcdef, commutatorElement_def]; group
  have hcr : c ^ r = 1 := by
    have h1 := conj_pow_eq_of_mem_center hc hxy r
    have h2 : x ^ r * y * (x ^ r)⁻¹ = y := by
      rw [← mem_center_iff.mp hxr y, mul_inv_cancel_right]
    rw [h2] at h1
    exact mul_right_cancel (h1.symm.trans (one_mul y).symm)
  have hinv : ⁅x⁻¹, y⁆ = c⁻¹ := by
    have h4 : y * x⁻¹ * y⁻¹ * x = c := by
      calc y * x⁻¹ * y⁻¹ * x = x⁻¹ * (x * y * x⁻¹ * y⁻¹) * x := by group
        _ = x⁻¹ * c * x := by rw [hcdef, commutatorElement_def]
        _ = c := by rw [mul_assoc, ← mem_center_iff.mp hc x, inv_mul_cancel_left]
    rw [← h4, commutatorElement_def]
    group
  have hconj : d * c * d⁻¹ = c⁻¹ := by
    have h5 : d * c * d⁻¹ = ⁅d * x * d⁻¹, d * y * d⁻¹⁆ := by
      rw [hcdef]; simp only [commutatorElement_def]; group
    have hdx' : d * x * d⁻¹ = x⁻¹ * (x * (d * x * d⁻¹)) := by group
    have hdy' : d * y * d⁻¹ = y * (y⁻¹ * (d * y * d⁻¹)) := by group
    rw [h5, hdx', hdy', commutatorElement_mul_central_left hdx,
      commutatorElement_mul_central_right hdy, hinv]
  have hfix : d * c * d⁻¹ = c := by rw [mem_center_iff.mp hc d, mul_inv_cancel_right]
  have hc2 : c * c = 1 := by
    calc c * c = c * (d * c * d⁻¹)⁻¹ := by rw [hconj, inv_inv]
      _ = 1 := by rw [hfix, mul_inv_cancel]
  have hc1 : c = 1 := by
    obtain ⟨k, hk⟩ : ∃ k, r = 2 * k + 1 := ⟨r / 2, by omega⟩
    rw [hk, pow_succ, pow_mul, sq, hc2, one_pow, one_mul] at hcr
    exact hcr
  exact commutatorElement_eq_one_iff_mul_comm.mp hc1

end Lifts

variable {G : Type} [Group G] [Finite G]

theorem not_dvd_card_center_of_signed (he : CFSG.Open.evenRank G ≤ 2) {Y : Subgroup G}
    {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) {R : Subgroup (↥Y ⧸ center ↥Y)} (hR : R ≠ ⊥)
    (hR2 : IsPGroup 2 R) {a b d₁ d₂ : ↥Y ⧸ center ↥Y}
    (ha : a ∈ normalizer (R : Set (↥Y ⧸ center ↥Y)))
    (hb : b ∈ normalizer (R : Set (↥Y ⧸ center ↥Y))) (har : a ^ r = 1) (hbr : b ^ r = 1)
    (hab : a * b = b * a) (hind : ∀ i j : ℕ, i < r → j < r → a ^ i * b ^ j = 1 → i = 0 ∧ j = 0)
    (hd₁a : d₁ * a * d₁⁻¹ = a⁻¹) (hd₁b : d₁ * b * d₁⁻¹ = b) (hd₂b : d₂ * b * d₂⁻¹ = b⁻¹) :
    ¬ r ∣ Nat.card (center ↥Y) := by
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
  obtain ⟨v₁, hv₁, hx⟩ := exists_mem_center_pow_eq_one hodd (x := x₀) (d := e₁)
    (hmem _ (by rw [map_pow, hx₀, har]))
    (hmem _ (by rw [map_mul, map_mul, map_mul, map_inv, hx₀, he₁, hd₁a, mul_inv_cancel]))
  obtain ⟨v₂, hv₂, hy⟩ := exists_mem_center_pow_eq_one hodd (x := y₀) (d := e₂)
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
  have hdy : y⁻¹ * (e₁ * y * e₁⁻¹) ∈ center ↥Y := hmem _ (by
    simp only [map_mul, map_inv, hπy, he₁]; rw [hd₁b, inv_mul_cancel])
  have hxy : Commute x y := commute_of_sign hodd hc0 (by rw [hx]; exact one_mem _) hdx hdy
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
  let ψ : Fin 3 → Multiplicative (ZMod r) →* ↥Y := fun i => zmodPowHom (g' i) (hg'p i)
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

end CFSG.SectionRank.QTK.CoverB
