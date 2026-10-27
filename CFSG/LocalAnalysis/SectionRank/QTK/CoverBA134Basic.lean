module

public import CFSG.LocalAnalysis.SectionRank.QTK.CoverBSigned
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.SectionRank.QTK.CoverB

open Subgroup

section Group

variable {G : Type*} [Group G]

theorem isElemAbelian_zpowers_of_pow {x : G} {r : ℕ} (hx : x ^ r = 1) :
    CFSG.Open.IsElemAbelian r (zpowers x) := CFSG.Open.isElemAbelian_zpowers hx

theorem eq_zero_of_pow_mem {r : ℕ} (hr : r.Prime) {x : G} (hx : x ^ r = 1) {K : Subgroup G}
    (hxK : x ∉ K) {a : ℕ} (ha : a < r) (h : x ^ a ∈ K) : a = 0 := by
  by_contra h0
  have : Fact r.Prime := ⟨hr⟩
  have hx1 : x ≠ 1 := fun h1 => hxK (h1 ▸ K.one_mem)
  have hox : orderOf x = r := orderOf_eq_prime hx hx1
  have hcop : a.gcd (orderOf x) = 1 := by
    rw [hox]
    exact Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hr).mpr fun hd =>
      h0 (Nat.eq_zero_of_dvd_of_lt hd ha))
  exact hxK (zpowers_le.mpr h (mem_zpowers_pow_iff.mpr hcop))

theorem exists_elemAbelian_sup {r k : ℕ} (hr : r.Prime) {E : Subgroup G}
    (hE : CFSG.Open.IsElemAbelian r E) (hEc : Nat.card E = r ^ k) {x : G} (hx : x ^ r = 1)
    (hxE : ∀ e ∈ E, Commute x e) (hxnE : x ∉ E) {K : Subgroup G} (hxK : x ∈ K) (hEK : E ≤ K) :
    ∃ F : Subgroup G, CFSG.Open.IsElemAbelian r F ∧ Nat.card F = r ^ (k + 1) ∧ F ≤ K := by
  have : Fact r.Prime := ⟨hr⟩
  have : NeZero r := ⟨hr.ne_zero⟩
  let ψ : Multiplicative (ZMod r) →* G := CFSG.SectionRank.zmodPowHom x hx
  have hψ : ∀ u : Multiplicative (ZMod r), ψ u = x ^ (Multiplicative.toAdd u).val := fun _ => rfl
  let Φ : Multiplicative (ZMod r) × ↥E →* G :=
    MonoidHom.noncommCoprod ψ E.subtype fun u e => (hxE e e.2).pow_left _
  have hΦ : ∀ p : Multiplicative (ZMod r) × ↥E,
      Φ p = x ^ (Multiplicative.toAdd p.1).val * (p.2 : G) := fun _ => rfl
  have hΦinj : Function.Injective Φ := by
    rw [injective_iff_map_eq_one]
    rintro ⟨u, e⟩ h
    rw [hΦ] at h
    have hxa : x ^ (Multiplicative.toAdd u).val ∈ E := by
      rw [eq_inv_of_mul_eq_one_left h]
      exact E.inv_mem e.2
    have h0 := eq_zero_of_pow_mem hr hx hxnE (ZMod.val_lt _) hxa
    rw [h0, pow_zero, one_mul] at h
    refine Prod.ext (Multiplicative.toAdd.injective ((ZMod.val_eq_zero _).mp h0)) ?_
    exact Subtype.ext h
  have hcomm : ∀ a b : Multiplicative (ZMod r) × ↥E, a * b = b * a := by
    rintro ⟨u, e⟩ ⟨u', e'⟩
    refine Prod.ext (mul_comm u u') ?_
    exact (hE.1.is_comm).comm e e'
  have hpow : ∀ a : Multiplicative (ZMod r) × ↥E, a ^ r = 1 := by
    rintro ⟨u, e⟩
    refine Prod.ext ?_ (Subtype.ext ?_)
    · apply Multiplicative.toAdd.injective
      rw [Prod.pow_fst, toAdd_pow, nsmul_eq_mul, CharP.cast_eq_zero, zero_mul]
      rfl
    · rw [Prod.pow_snd, SubgroupClass.coe_pow]
      exact hE.2 _ e.2
  have hcard : Nat.card (Multiplicative (ZMod r) × ↥E) = r ^ (k + 1) := by
    rw [Nat.card_prod, hEc, Nat.card_congr Multiplicative.toAdd, Nat.card_zmod, pow_succ,
      mul_comm]
  refine ⟨Φ.range, ?_, ?_, ?_⟩
  · refine ⟨⟨⟨fun a b => ?_⟩⟩, fun y hy => ?_⟩
    · obtain ⟨p, hp⟩ := MonoidHom.mem_range.1 a.2
      obtain ⟨q, hq⟩ := MonoidHom.mem_range.1 b.2
      apply Subtype.ext
      change (a : G) * b = b * a
      rw [← hp, ← hq, ← map_mul, ← map_mul, hcomm]
    · obtain ⟨p, rfl⟩ := MonoidHom.mem_range.1 hy
      rw [← map_pow, hpow, map_one]
  · rw [← Nat.card_congr (MonoidHom.ofInjective hΦinj).toEquiv, hcard]
  · rintro _ ⟨p, rfl⟩
    rw [hΦ]
    exact K.mul_mem (K.pow_mem hxK _) (hEK p.2.2)

end Group

section Lift

variable {Y : Type*} [Group Y]

theorem exists_lift_pow_eq_one {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) {x : Y ⧸ center Y}
    (hx : x ^ r = 1)
    (h : (∃ d : Y ⧸ center Y, d * x * d⁻¹ = x⁻¹) ∨ ¬ r ∣ Nat.card (center Y)) :
    ∃ y : Y, y ^ r = 1 ∧ (y : Y ⧸ center Y) = x := by
  rcases h with ⟨d, hd⟩ | hrZ
  · have hodd : r % 2 = 1 := Nat.odd_iff.mp (hr.odd_of_ne_two hr2)
    obtain ⟨x₀, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨d₀, rfl⟩ := QuotientGroup.mk_surjective d
    obtain ⟨v, hv, hxv⟩ := exists_mem_center_pow_eq_one hodd (x := x₀) (d := d₀)
      ((QuotientGroup.eq_one_iff _).mp (by rw [QuotientGroup.mk_pow, hx]))
      ((QuotientGroup.eq_one_iff _).mp (by
        rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv,
          hd, mul_inv_cancel]))
    refine ⟨x₀ * v, hxv, ?_⟩
    rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff v).mpr hv, mul_one]
  · obtain ⟨P, hP, -, hPE⟩ := exists_lift hr hrZ (isElemAbelian_zpowers_of_pow hx)
    have hxm : x ∈ P.map (QuotientGroup.mk' (center Y)) := by
      rw [hPE]
      exact mem_zpowers x
    obtain ⟨y, hyP, hy⟩ := hxm
    exact ⟨y, hP.2 y hyP, hy⟩

theorem exists_elemAbelian_sq_of_lift [Finite Y] {r : ℕ} (hr : r.Prime) {y : Y} (hy : y ^ r = 1)
    (hyZ : y ∉ center Y)
    (hE : ¬ r ∣ Nat.card (center Y) → ∃ E : Subgroup (Y ⧸ center Y),
      CFSG.Open.IsElemAbelian r E ∧ Nat.card E = r ^ 2) :
    ∃ E : Subgroup Y, CFSG.Open.IsElemAbelian r E ∧ Nat.card E = r ^ 2 := by
  by_cases hrZ : r ∣ Nat.card (center Y)
  · have : Fact r.Prime := ⟨hr⟩
    obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := ↥(center Y)) r hrZ
    have hzr : (z : Y) ^ r = 1 := by
      rw [← orderOf_dvd_iff_pow_eq_one, Subgroup.orderOf_coe, hz]
    have hzE : CFSG.Open.IsElemAbelian r (zpowers (z : Y)) :=
      isElemAbelian_zpowers_of_pow hzr
    have hzc : Nat.card (zpowers (z : Y)) = r ^ 1 := by
      rw [Nat.card_zpowers, Subgroup.orderOf_coe, hz, pow_one]
    have hyz : y ∉ zpowers (z : Y) := fun h => hyZ
      ((zpowers_le.mpr z.2) h)
    obtain ⟨F, hF, hFc, -⟩ := exists_elemAbelian_sup hr hzE hzc hy
      (fun e he => by
        obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp he
        exact (show Commute y (z : Y) from mem_center_iff.mp z.2 y).zpow_right k)
      hyz (K := ⊤) (mem_top _) le_top
    exact ⟨F, hF, hFc⟩
  · obtain ⟨E, hE, hEc⟩ := hE hrZ
    obtain ⟨P, hP, hPc, -⟩ := exists_lift hr hrZ hE
    exact ⟨P, hP, by rw [hPc, hEc]⟩

end Lift

section Components

variable {H : Type} [Group H]

theorem mem_center_of_mem_commuting {L₁ L₂ : Subgroup H} (hc : ∀ a ∈ L₁, ∀ b ∈ L₂, Commute a b)
    {y : ↥L₁} (hy : (y : H) ∈ L₂) : y ∈ center ↥L₁ :=
  mem_center_iff.mpr fun g => Subtype.ext (hc g g.2 y hy)

theorem le_normalizer_of_commuting {L M R : Subgroup H} (hc : ∀ a ∈ L, ∀ b ∈ M, Commute a b)
    (hRL : R ≤ L) : M ≤ normalizer (R : Set H) := fun b hb =>
  centralizer_le_normalizer (R : Set H) (mem_centralizer_iff.mpr fun g hg => hc g (hRL hg) b hb)

theorem exists_lift_component [Finite H] {L : Subgroup H} {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    {R : Subgroup (↥L ⧸ center ↥L)} (hR : R ≠ ⊥) (hR2 : IsPGroup 2 R) {x : ↥L ⧸ center ↥L}
    (hxN : x ∈ normalizer (R : Set (↥L ⧸ center ↥L))) (hx : orderOf x = r)
    (hlift : (∃ d : ↥L ⧸ center ↥L, d * x * d⁻¹ = x⁻¹) ∨ ¬ r ∣ Nat.card (center ↥L)) :
    ∃ y : ↥L, y ^ r = 1 ∧ y ∉ center ↥L ∧ (y : ↥L ⧸ center ↥L) = x ∧
      ∃ R₂ : Subgroup ↥L, R₂ ≠ ⊥ ∧ IsPGroup 2 R₂ ∧ y ∈ normalizer (R₂ : Set ↥L) := by
  have hxr : x ^ r = 1 := by rw [← hx]; exact pow_orderOf_eq_one x
  obtain ⟨y, hyr, hyx⟩ := exists_lift_pow_eq_one hr hr2 hxr hlift
  have hyZ : y ∉ center ↥L := fun h => by
    have h1 : x = 1 := by rw [← hyx]; exact (QuotientGroup.eq_one_iff y).mpr h
    rw [h1, orderOf_one] at hx
    exact hr.one_lt.ne hx
  obtain ⟨R₂, hR₂, hR₂2, hR₂N⟩ := exists_two_subgroup_normalized hR hR2
  exact ⟨y, hyr, hyZ, hyx, R₂, hR₂, hR₂2, hR₂N y (by rw [hyx]; exact hxN)⟩

theorem map_two_subgroup {L : Subgroup H} {R₂ : Subgroup ↥L} (hR₂ : R₂ ≠ ⊥)
    (hR₂2 : IsPGroup 2 R₂) {y : ↥L} (hyN : y ∈ normalizer (R₂ : Set ↥L)) :
    R₂.map L.subtype ≠ ⊥ ∧ IsPGroup 2 (R₂.map L.subtype) ∧ R₂.map L.subtype ≤ L ∧
      (y : H) ∈ normalizer ((R₂.map L.subtype : Subgroup H) : Set H) :=
  ⟨fun h => hR₂ ((map_eq_bot_iff_of_injective _ L.subtype_injective).mp h), hR₂2.map _,
    map_subtype_le R₂, le_normalizer_map L.subtype (mem_map_of_mem _ hyN)⟩

theorem false_of_components [Finite H] (he : CFSG.Open.evenRank H ≤ 2) {L₁ L₂ : Subgroup H}
    (hc : ∀ a ∈ L₁, ∀ b ∈ L₂, Commute a b) (φ : ↥L₁ ≃* ↥L₂) {r : ℕ} (hr : r.Prime)
    (hr2 : r ≠ 2) {R : Subgroup (↥L₁ ⧸ center ↥L₁)} (hR : R ≠ ⊥) (hR2 : IsPGroup 2 R)
    {x : ↥L₁ ⧸ center ↥L₁} (hxN : x ∈ normalizer (R : Set (↥L₁ ⧸ center ↥L₁)))
    (hx : orderOf x = r)
    (hlift : (∃ d : ↥L₁ ⧸ center ↥L₁, d * x * d⁻¹ = x⁻¹) ∨ ¬ r ∣ Nat.card (center ↥L₁))
    (hE : ¬ r ∣ Nat.card (center ↥L₁) → ∃ E : Subgroup (↥L₁ ⧸ center ↥L₁),
      CFSG.Open.IsElemAbelian r E ∧ Nat.card E = r ^ 2) : False := by
  obtain ⟨y, hyr, hyZ, -, R₂, hR₂, hR₂2, hyN⟩ := exists_lift_component hr hr2 hR hR2 hxN hx hlift
  obtain ⟨hRh, hRh2, hRhL, hyhN⟩ := map_two_subgroup hR₂ hR₂2 hyN
  obtain ⟨E₁, hE₁, hE₁c⟩ := exists_elemAbelian_sq_of_lift hr hyr hyZ hE
  set f : ↥L₁ →* H := L₂.subtype.comp φ.toMonoidHom with hf
  have hfinj : Function.Injective f := L₂.subtype_injective.comp φ.injective
  have hE₂ : CFSG.Open.IsElemAbelian r (E₁.map f) := isElemAbelian_map f hE₁
  have hE₂c : Nat.card (E₁.map f) = r ^ 2 := by rw [card_map_of_injective hfinj, hE₁c]
  have hE₂L : E₁.map f ≤ L₂ := by
    rintro _ ⟨e, -, rfl⟩
    exact (φ e).2
  have hyh : ((y : H)) ^ r = 1 := by rw [← SubgroupClass.coe_pow, hyr, OneMemClass.coe_one]
  obtain ⟨F, hF, hFc, hFN⟩ := exists_elemAbelian_sup hr hE₂ hE₂c hyh
    (fun e he => hc _ y.2 e (hE₂L he))
    (fun h => hyZ (mem_center_of_mem_commuting hc (hE₂L h))) hyhN
    (hE₂L.trans (le_normalizer_of_commuting hc hRhL))
  have := le_two_of_evenRank_le_two he hRh hRh2 hr hr2 hF hFN hFc
  omega

end Components

end CFSG.SectionRank.QTK.CoverB
