module

public import CFSG.CharacterTheory.Semidihedral.Presentation
public import CFSG.CharacterTheory.Wreathed.BaseAndDerived

public section

namespace CFSG.RankTwoShapes

open CFSG.Wreathed CFSG.Semidihedral

theorem exists_eq_add_self_of_castHom_eq_zero {n : ℕ} (hn : n ≠ 0) (u : ZMod (2 ^ n))
    (hu : ZMod.castHom (dvd_pow_self 2 hn) (ZMod 2) u = 0) : ∃ v : ZMod (2 ^ n), u = v + v := by
  have h1 : ((u.val : ℕ) : ZMod 2) = 0 := by
    rw [← map_natCast (ZMod.castHom (dvd_pow_self 2 hn) (ZMod 2)), ZMod.natCast_zmod_val]
    exact hu
  rw [ZMod.natCast_eq_zero_iff] at h1
  obtain ⟨k, hk⟩ := h1
  refine ⟨(k : ZMod (2 ^ n)), ?_⟩
  rw [← two_mul, ← ZMod.natCast_zmod_val u, hk, Nat.cast_mul, Nat.cast_two]

theorem isUnit_of_castHom_ne_zero {n : ℕ} (hn : n ≠ 0) (u : ZMod (2 ^ n))
    (hu : ZMod.castHom (dvd_pow_self 2 hn) (ZMod 2) u ≠ 0) : IsUnit u := by
  have h1 : ((u.val : ℕ) : ZMod 2) ≠ 0 := by
    rw [← map_natCast (ZMod.castHom (dvd_pow_self 2 hn) (ZMod 2)), ZMod.natCast_zmod_val]
    exact hu
  rw [Ne, ZMod.natCast_eq_zero_iff, ← even_iff_two_dvd, Nat.not_even_iff_odd] at h1
  have hcop : Nat.Coprime u.val (2 ^ n) := Nat.Coprime.pow_right _ h1.coprime_two_right
  have h2 := ZMod.coe_unitOfCoprime u.val hcop
  rw [ZMod.natCast_zmod_val] at h2
  exact ⟨_, h2⟩

theorem zmod_two_det_ne_zero : ∀ p q r s : ZMod 2, ¬ (p = 0 ∧ q = 0) → ¬ (r = 0 ∧ s = 0) →
    ¬ (r - p = 0 ∧ s - q = 0) → p * s - q * r ≠ 0 := by
  decide

theorem homocyclic_swap_extension {R : Type*} [Group R] [Finite R] {n : ℕ} (hn : 1 ≤ n)
    (Q : Subgroup R) (hQnormal : Q.Normal) (hQindex : Q.index = 2)
    (hQ : Nonempty (Q ≃* (Multiplicative (ZMod (2 ^ n)) × Multiplicative (ZMod (2 ^ n)))))
    (t : R) (htQ : t ∉ Q) (hnontriv : ∃ q ∈ Q, ∀ r ∈ Q, t * q * t⁻¹ ≠ q * r ^ 2) :
    ∃ x y u : R, x ∈ Q ∧ y ∈ Q ∧ u ∉ Q ∧ u ^ 2 = 1 ∧
      orderOf x = 2 ^ n ∧ orderOf y = 2 ^ n ∧ Commute x y ∧
      Subgroup.zpowers x ⊓ Subgroup.zpowers y = ⊥ ∧
      Subgroup.zpowers x ⊔ Subgroup.zpowers y = Q ∧
      u * x * u⁻¹ = y ∧ u * y * u⁻¹ = x ∧
      Nat.card R = 2 ^ (2 * n + 1) ∧
      (∃ e : R ≃* CFSG.Open.WreathedTwoGroup n,
        Q.map e.toMonoidHom = (RegularWreathProduct.rightHom :
          CFSG.Open.WreathedTwoGroup n →* Multiplicative (ZMod 2)).ker) ∧
      (2 ≤ n →
        (∀ H : Subgroup R, IsMulCommutative H → ¬ H ≤ Q → Nat.card H ≤ 2 ^ (n + 1)) ∧
        (∀ H : Subgroup R, IsMulCommutative H → H.index = 2 → H = Q) ∧
        Q.Characteristic) := by
  classical
  obtain ⟨φ⟩ := hQ
  have hn0 : n ≠ 0 := by omega
  have hm2 : 2 ≤ 2 ^ n := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have : Fact (1 < 2 ^ n) := ⟨by omega⟩
  have hQcomm : ∀ a ∈ Q, ∀ b ∈ Q, a * b = b * a := by
    intro a ha b hb
    have h1 : φ (⟨a, ha⟩ * ⟨b, hb⟩) = φ (⟨b, hb⟩ * ⟨a, ha⟩) := by
      rw [map_mul, map_mul, mul_comm]
    exact congrArg Subtype.val (φ.injective h1)
  have hQab : IsMulCommutative Q := ⟨⟨fun a b => Subtype.ext (hQcomm a a.2 b b.2)⟩⟩
  have hCm : ∀ c : Multiplicative (ZMod (2 ^ n)), c ^ 2 ^ n = 1 := fun c => by
    apply Multiplicative.toAdd.injective
    rw [toAdd_pow, toAdd_one, nsmul_eq_mul, ZMod.natCast_self, zero_mul]
  have hQexp : ∀ a ∈ Q, a ^ 2 ^ n = 1 := by
    intro a ha
    have h1 : φ ⟨a, ha⟩ ^ 2 ^ n = 1 := Prod.ext (by simp [hCm]) (by simp [hCm])
    have h2 : (⟨a, ha⟩ : Q) ^ 2 ^ n = 1 := φ.injective (by rw [map_pow, h1, map_one])
    simpa using congrArg Subtype.val h2
  have hCcard : Nat.card (Multiplicative (ZMod (2 ^ n)) × Multiplicative (ZMod (2 ^ n))) =
      (2 ^ n) ^ 2 := by
    rw [Nat.card_prod, Nat.card_congr Multiplicative.toAdd, Nat.card_zmod, sq]
  have hQcard : Nat.card Q = (2 ^ n) ^ 2 := by
    rw [Nat.card_congr φ.toEquiv, hCcard]
  have hRcard : Nat.card R = 2 ^ (2 * n + 1) := by
    rw [← Subgroup.card_mul_index Q, hQcard, hQindex, ← pow_mul, mul_comm n 2, pow_succ]
  obtain ⟨x, hxQ, hx⟩ := hnontriv
  set y := t * x * t⁻¹ with hy
  have hyQ : y ∈ Q := hQnormal.conj_mem x hxQ t
  have ht2 : t ^ 2 ∈ Q := by
    rw [pow_two]
    exact Subgroup.mul_self_mem_of_index_two hQindex t
  have hconjQ : ∀ q ∈ Q, t * q * t⁻¹ ∈ Q := fun q hq => hQnormal.conj_mem q hq t
  have hyx : t * y * t⁻¹ = x := by
    have h1 := hQcomm _ ht2 x hxQ
    calc t * y * t⁻¹ = (t ^ 2 * x) * (t ^ 2)⁻¹ := by rw [hy, pow_two]; group
      _ = x := by rw [h1]; group
  have hsq_comm : ∀ a ∈ Q, ∀ b ∈ Q, (a * b) ^ 2 = a ^ 2 * b ^ 2 := fun a ha b hb =>
    Commute.mul_pow (hQcomm a ha b hb) 2
  have hN1 : ∀ s ∈ Q, x ≠ s ^ 2 := by
    intro s hs hxs
    have hts : t * s * t⁻¹ ∈ Q := hconjQ s hs
    apply hx (s⁻¹ * (t * s * t⁻¹)) (Q.mul_mem (Q.inv_mem hs) hts)
    rw [hsq_comm _ (Q.inv_mem hs) _ hts, hy, hxs, ← conj_pow, inv_pow, mul_inv_cancel_left]
  have hN2 : ∀ s ∈ Q, y ≠ s ^ 2 := by
    intro s hs hys
    have hts : t * s * t⁻¹ ∈ Q := hconjQ s hs
    apply hx ((t * s * t⁻¹)⁻¹ * s) (Q.mul_mem (Q.inv_mem hts) hs)
    have hx' : x = (t * s * t⁻¹) ^ 2 := by rw [← hyx, hys, conj_pow]
    rw [hsq_comm _ (Q.inv_mem hts) _ hs, hx', inv_pow, mul_inv_cancel_left, hys]
  let X : Q := ⟨x, hxQ⟩
  let Y : Q := ⟨y, hyQ⟩
  let κ := ZMod.castHom (dvd_pow_self 2 hn0) (ZMod 2)
  have hsqcrit : ∀ q (hq : q ∈ Q), κ (Multiplicative.toAdd (φ ⟨q, hq⟩).1) = 0 →
      κ (Multiplicative.toAdd (φ ⟨q, hq⟩).2) = 0 → ∃ s ∈ Q, q = s ^ 2 := by
    intro q hq h1 h2
    obtain ⟨v₁, hv₁⟩ := exists_eq_add_self_of_castHom_eq_zero hn0 _ h1
    obtain ⟨v₂, hv₂⟩ := exists_eq_add_self_of_castHom_eq_zero hn0 _ h2
    refine ⟨(φ.symm (Multiplicative.ofAdd v₁, Multiplicative.ofAdd v₂) : Q),
      Subtype.coe_prop _, ?_⟩
    have h3 : (⟨q, hq⟩ : Q) = φ.symm (Multiplicative.ofAdd v₁, Multiplicative.ofAdd v₂) ^ 2 := by
      apply φ.injective
      rw [map_pow, MulEquiv.apply_symm_apply]
      refine Prod.ext ?_ ?_
      · apply Multiplicative.toAdd.injective
        simp [hv₁, two_mul]
      · apply Multiplicative.toAdd.injective
        simp [hv₂, two_mul]
    simpa using congrArg Subtype.val h3
  set a₁ := Multiplicative.toAdd (φ X).1 with ha₁
  set a₂ := Multiplicative.toAdd (φ X).2 with ha₂
  set b₁ := Multiplicative.toAdd (φ Y).1 with hb₁
  set b₂ := Multiplicative.toAdd (φ Y).2 with hb₂
  have hNx : ¬ (κ a₁ = 0 ∧ κ a₂ = 0) := fun ⟨h1, h2⟩ => by
    obtain ⟨s, hs, hxs⟩ := hsqcrit x hxQ h1 h2
    exact hN1 s hs hxs
  have hNy : ¬ (κ b₁ = 0 ∧ κ b₂ = 0) := fun ⟨h1, h2⟩ => by
    obtain ⟨s, hs, hys⟩ := hsqcrit y hyQ h1 h2
    exact hN2 s hs hys
  have hNxy : ¬ (κ b₁ - κ a₁ = 0 ∧ κ b₂ - κ a₂ = 0) := fun ⟨h1, h2⟩ => by
    have hq : x⁻¹ * y ∈ Q := Q.mul_mem (Q.inv_mem hxQ) hyQ
    have e0 : φ ⟨x⁻¹ * y, hq⟩ = (φ X)⁻¹ * φ Y := by
      rw [← map_inv, ← map_mul]
      rfl
    have e1 : Multiplicative.toAdd (φ ⟨x⁻¹ * y, hq⟩).1 = b₁ - a₁ := by
      rw [e0, sub_eq_neg_add]
      rfl
    have e2 : Multiplicative.toAdd (φ ⟨x⁻¹ * y, hq⟩).2 = b₂ - a₂ := by
      rw [e0, sub_eq_neg_add]
      rfl
    obtain ⟨s, hs, hxys⟩ := hsqcrit _ hq (by rw [e1, map_sub]; exact h1)
      (by rw [e2, map_sub]; exact h2)
    apply hx s hs
    rw [← hxys, mul_inv_cancel_left]
  set D := a₁ * b₂ - a₂ * b₁ with hD
  have hDunit : IsUnit D := by
    apply isUnit_of_castHom_ne_zero hn0
    rw [hD, map_sub, map_mul, map_mul]
    exact zmod_two_det_ne_zero _ _ _ _ hNx hNy hNxy
  have hXm : X ^ 2 ^ n = 1 := Subtype.ext (by simpa using hQexp x hxQ)
  have hYm : Y ^ 2 ^ n = 1 := Subtype.ext (by simpa using hQexp y hyQ)
  let ψ : Cyclic (2 ^ n) × Cyclic (2 ^ n) →* Q :=
    (cyclicPowHom (2 ^ n) X hXm).noncommCoprod (cyclicPowHom (2 ^ n) Y hYm)
      (fun c d => Subtype.ext (hQcomm _ (Subtype.coe_prop _) _ (Subtype.coe_prop _)))
  have hval : ∀ c d : Cyclic (2 ^ n), ((ψ (c, d) : Q) : R) =
      x ^ (Multiplicative.toAdd c).val * y ^ (Multiplicative.toAdd d).val := fun c d => rfl
  have hφψ : ∀ c d : Cyclic (2 ^ n),
      Multiplicative.toAdd (φ (ψ (c, d))).1 =
        Multiplicative.toAdd c * a₁ + Multiplicative.toAdd d * b₁ ∧
      Multiplicative.toAdd (φ (ψ (c, d))).2 =
        Multiplicative.toAdd c * a₂ + Multiplicative.toAdd d * b₂ := by
    intro c d
    have e : ψ (c, d) = X ^ (Multiplicative.toAdd c).val * Y ^ (Multiplicative.toAdd d).val :=
      rfl
    rw [e, map_mul, map_pow, map_pow]
    constructor
    · simp only [Prod.fst_mul, Prod.pow_fst, toAdd_mul, toAdd_pow, nsmul_eq_mul,
        ZMod.natCast_zmod_val, ha₁, hb₁]
    · simp only [Prod.snd_mul, Prod.pow_snd, toAdd_mul, toAdd_pow, nsmul_eq_mul,
        ZMod.natCast_zmod_val, ha₂, hb₂]
  have hψinj : Function.Injective ψ := by
    rw [injective_iff_map_eq_one]
    rintro ⟨c, d⟩ hcd
    obtain ⟨e1, e2⟩ := hφψ c d
    rw [hcd, map_one] at e1 e2
    simp only [Prod.fst_one, Prod.snd_one, toAdd_one] at e1 e2
    have hc : Multiplicative.toAdd c * D = 0 := by
      rw [hD]
      linear_combination -(b₂ * e1) + b₁ * e2
    have hd : Multiplicative.toAdd d * D = 0 := by
      rw [hD]
      linear_combination -(a₁ * e2) + a₂ * e1
    have hc0 : c = 1 := Multiplicative.toAdd.injective ((hDunit.mul_left_eq_zero).mp hc)
    have hd0 : d = 1 := Multiplicative.toAdd.injective ((hDunit.mul_left_eq_zero).mp hd)
    rw [hc0, hd0]
    rfl
  have hψbij : Function.Bijective ψ :=
    hψinj.bijective_of_nat_card_le (by rw [hCcard, hQcard])
  have hrep : ∀ q ∈ Q, ∃ c d : Cyclic (2 ^ n),
      q = x ^ (Multiplicative.toAdd c).val * y ^ (Multiplicative.toAdd d).val := by
    intro q hq
    obtain ⟨⟨c, d⟩, hcd⟩ := hψbij.2 ⟨q, hq⟩
    exact ⟨c, d, by rw [← hval, hcd]⟩
  have hψeq : ∀ c d c' d' : Cyclic (2 ^ n),
      x ^ (Multiplicative.toAdd c).val * y ^ (Multiplicative.toAdd d).val =
        x ^ (Multiplicative.toAdd c').val * y ^ (Multiplicative.toAdd d').val → c = c' ∧ d = d' := by
    intro c d c' d' h
    have h1 : ψ (c, d) = ψ (c', d') := Subtype.ext (by rw [hval, hval, h])
    exact Prod.ext_iff.mp (hψinj h1)
  have hval1 : (Multiplicative.toAdd (Multiplicative.ofAdd (1 : ZMod (2 ^ n)))).val = 1 := by
    simp [ZMod.val_one]
  have hval0 : (Multiplicative.toAdd (1 : Cyclic (2 ^ n))).val = 0 := by simp
  have hordC : ∀ c d : Cyclic (2 ^ n), orderOf ((ψ (c, d) : Q) : R) = orderOf (c, d) := by
    intro c d
    rw [Subgroup.orderOf_coe, orderOf_injective ψ hψinj]
  have hord1 : orderOf (Multiplicative.ofAdd (1 : ZMod (2 ^ n))) = 2 ^ n := by
    rw [orderOf_ofAdd_eq_addOrderOf, ZMod.addOrderOf_one]
  have hordx : orderOf x = 2 ^ n := by
    have h1 := hordC (Multiplicative.ofAdd 1) 1
    rw [hval, hval1, hval0, pow_one, pow_zero, mul_one, Prod.orderOf, orderOf_one,
      Nat.lcm_one_right, hord1] at h1
    exact h1
  have hordy : orderOf y = 2 ^ n := by
    have h1 := hordC 1 (Multiplicative.ofAdd 1)
    rw [hval, hval1, hval0, pow_one, pow_zero, one_mul, Prod.orderOf, orderOf_one,
      Nat.lcm_one_left, hord1] at h1
    exact h1
  have hordxy : orderOf (x * y) = 2 ^ n := by
    have h1 := hordC (Multiplicative.ofAdd 1) (Multiplicative.ofAdd 1)
    rw [hval, hval1, pow_one, pow_one, Prod.orderOf, hord1, Nat.lcm_self] at h1
    exact h1
  have hinf : Subgroup.zpowers x ⊓ Subgroup.zpowers y = ⊥ := by
    have hfinx : IsOfFinOrder x := orderOf_pos_iff.mp (by rw [hordx]; positivity)
    have hfiny : IsOfFinOrder y := orderOf_pos_iff.mp (by rw [hordy]; positivity)
    rw [eq_bot_iff]
    intro g hg
    obtain ⟨i, rfl⟩ := (Submonoid.mem_powers_iff _ _).mp
      (hfinx.mem_powers_iff_mem_zpowers.mpr hg.1)
    obtain ⟨j, hj⟩ := (Submonoid.mem_powers_iff _ _).mp
      (hfiny.mem_powers_iff_mem_zpowers.mpr hg.2)
    have h1 := hψeq (Multiplicative.ofAdd (i : ZMod (2 ^ n))) 1 1
      (Multiplicative.ofAdd (j : ZMod (2 ^ n))) (by
        simp only [toAdd_ofAdd, toAdd_one, ZMod.val_zero, pow_zero, mul_one, one_mul,
          ZMod.val_natCast]
        have e1 : x ^ (i % 2 ^ n) = x ^ i := by rw [← hordx, pow_mod_orderOf]
        have e2 : y ^ (j % 2 ^ n) = y ^ j := by rw [← hordy, pow_mod_orderOf]
        rw [e1, e2]
        exact hj.symm)
    have h2 : (i : ZMod (2 ^ n)) = 0 := congrArg Multiplicative.toAdd h1.1
    rw [ZMod.natCast_eq_zero_iff, ← hordx, orderOf_dvd_iff_pow_eq_one] at h2
    rw [Subgroup.mem_bot]
    exact h2
  have hsup : Subgroup.zpowers x ⊔ Subgroup.zpowers y = Q := by
    apply le_antisymm
    · exact sup_le (Subgroup.zpowers_le.mpr hxQ) (Subgroup.zpowers_le.mpr hyQ)
    · intro q hq
      obtain ⟨c, d, rfl⟩ := hrep q hq
      exact Subgroup.mul_mem _
        (Subgroup.mem_sup_left (Subgroup.pow_mem _ (Subgroup.mem_zpowers x) _))
        (Subgroup.mem_sup_right (Subgroup.pow_mem _ (Subgroup.mem_zpowers y) _))
  have hconjpow : ∀ k : ℕ, t * x ^ k * t⁻¹ = y ^ k ∧ t * y ^ k * t⁻¹ = x ^ k := fun k =>
    ⟨by rw [← conj_pow], by rw [← conj_pow, hyx]⟩
  obtain ⟨c₀, d₀, ht2eq⟩ := hrep _ ht2
  have hcd₀ : c₀ = d₀ := by
    have e : t * t ^ 2 * t⁻¹ = t ^ 2 := by group
    rw [ht2eq] at e
    have e' : t * (x ^ (Multiplicative.toAdd c₀).val * y ^ (Multiplicative.toAdd d₀).val) * t⁻¹ =
        x ^ (Multiplicative.toAdd d₀).val * y ^ (Multiplicative.toAdd c₀).val := by
      rw [show t * (x ^ (Multiplicative.toAdd c₀).val * y ^ (Multiplicative.toAdd d₀).val) * t⁻¹ =
          (t * x ^ (Multiplicative.toAdd c₀).val * t⁻¹) *
            (t * y ^ (Multiplicative.toAdd d₀).val * t⁻¹) by group,
        (hconjpow _).1, (hconjpow _).2]
      exact hQcomm _ (Q.pow_mem hyQ _) _ (Q.pow_mem hxQ _)
    rw [e'] at e
    exact (hψeq _ _ _ _ e).2
  set i := (Multiplicative.toAdd c₀).val with hi
  have ht2' : t ^ 2 = x ^ i * y ^ i := by rw [ht2eq, ← hcd₀]
  set u := (x ^ i)⁻¹ * t with hu
  have huQ : u ∉ Q := fun h => htQ (by
    have e : t = x ^ i * u := by rw [hu, mul_inv_cancel_left]
    rw [e]
    exact Q.mul_mem (Q.pow_mem hxQ i) h)
  have hu2 : u ^ 2 = 1 := by
    calc u ^ 2 = (x ^ i)⁻¹ * (t * x ^ i * t⁻¹)⁻¹ * t ^ 2 := by rw [hu, pow_two, pow_two]; group
      _ = (x ^ i)⁻¹ * (y ^ i)⁻¹ * (y ^ i * x ^ i) := by
        rw [(hconjpow i).1, ht2', hQcomm _ (Q.pow_mem hxQ i) _ (Q.pow_mem hyQ i)]
      _ = 1 := by group
  have hux : u * x * u⁻¹ = y := by
    calc u * x * u⁻¹ = (x ^ i)⁻¹ * (t * x * t⁻¹) * x ^ i := by rw [hu]; group
      _ = y := by
        rw [← hy, mul_assoc, hQcomm y hyQ _ (Q.pow_mem hxQ i), inv_mul_cancel_left]
  have huy : u * y * u⁻¹ = x := by
    calc u * y * u⁻¹ = (x ^ i)⁻¹ * (t * y * t⁻¹) * x ^ i := by rw [hu]; group
      _ = x := by rw [hyx]; group
  have hxm : x ^ 2 ^ n = 1 := hQexp x hxQ
  have hym : y ^ 2 ^ n = 1 := hQexp y hyQ
  let fX := cyclicPowHom (2 ^ n) x hxm
  let fY := cyclicPowHom (2 ^ n) y hym
  let fU := cyclicPowHom 2 u hu2
  have hfX : ∀ a : ZMod (2 ^ n), fX (Multiplicative.ofAdd a) = x ^ a.val := fun a => rfl
  have hfY : ∀ a : ZMod (2 ^ n), fY (Multiplicative.ofAdd a) = y ^ a.val := fun a => rfl
  have hfXQ : ∀ a : ZMod (2 ^ n), fX (Multiplicative.ofAdd a) ∈ Q := fun a => Q.pow_mem hxQ _
  have hfYQ : ∀ a : ZMod (2 ^ n), fY (Multiplicative.ofAdd a) ∈ Q := fun a => Q.pow_mem hyQ _
  have hUX : ∀ a : ZMod (2 ^ n), u * fX (Multiplicative.ofAdd a) * u⁻¹ =
      fY (Multiplicative.ofAdd a) := fun a => by rw [hfX, hfY, ← conj_pow, hux]
  have hUY : ∀ a : ZMod (2 ^ n), u * fY (Multiplicative.ofAdd a) * u⁻¹ =
      fX (Multiplicative.ofAdd a) := fun a => by rw [hfX, hfY, ← conj_pow, huy]
  have hU1 : fU (Multiplicative.ofAdd 1) = u := cyclicPowHom_one 2 le_rfl u hu2
  have hU0 : fU (Multiplicative.ofAdd 0) = 1 := map_one fU
  let F : ZMod (2 ^ n) → ZMod (2 ^ n) → ZMod 2 → R := fun a b e =>
    fX (Multiplicative.ofAdd a) * fY (Multiplicative.ofAdd b) * fU (Multiplicative.ofAdd e)
  have hcoord : ∀ a b e, coordinateEquiv (2 ^ n) (element (2 ^ n) a b e) = (a, b, e) :=
    fun a b e => (coordinateEquiv (2 ^ n)).apply_symm_apply (a, b, e)
  let Φfun : Wreath (2 ^ n) → R := fun g =>
    F (coordinateEquiv (2 ^ n) g).1 (coordinateEquiv (2 ^ n) g).2.1 (coordinateEquiv (2 ^ n) g).2.2
  have hΦ : ∀ a b e, Φfun (element (2 ^ n) a b e) = F a b e := fun a b e => by
    simp only [Φfun, hcoord]
  have hsurjW : ∀ g : Wreath (2 ^ n), ∃ a b e, g = element (2 ^ n) a b e := fun g => by
    obtain ⟨⟨a, b, e⟩, rfl⟩ := (coordinateEquiv (2 ^ n)).symm.surjective g
    exact ⟨a, b, e, rfl⟩
  have hΦmul : ∀ g g' : Wreath (2 ^ n), Φfun (g * g') = Φfun g * Φfun g' := by
    intro g g'
    obtain ⟨a, b, e, rfl⟩ := hsurjW g
    obtain ⟨c, d, f, rfl⟩ := hsurjW g'
    have hcomXY : ∀ p q : ZMod (2 ^ n), fX (Multiplicative.ofAdd p) * fY (Multiplicative.ofAdd q) =
        fY (Multiplicative.ofAdd q) * fX (Multiplicative.ofAdd p) := fun p q =>
      hQcomm _ (hfXQ p) _ (hfYQ q)
    rcases swap_exponent_cases e with rfl | rfl
    · rw [element_base_mul, hΦ, hΦ, hΦ]
      simp only [F, ofAdd_add, map_mul, hU0, mul_one]
      calc fX (Multiplicative.ofAdd a) * fX (Multiplicative.ofAdd c) *
            (fY (Multiplicative.ofAdd b) * fY (Multiplicative.ofAdd d)) *
            fU (Multiplicative.ofAdd f)
          = fX (Multiplicative.ofAdd a) *
            (fX (Multiplicative.ofAdd c) * fY (Multiplicative.ofAdd b)) *
            fY (Multiplicative.ofAdd d) * fU (Multiplicative.ofAdd f) := by group
        _ = fX (Multiplicative.ofAdd a) *
            (fY (Multiplicative.ofAdd b) * fX (Multiplicative.ofAdd c)) *
            fY (Multiplicative.ofAdd d) * fU (Multiplicative.ofAdd f) := by rw [hcomXY]
        _ = fX (Multiplicative.ofAdd a) * fY (Multiplicative.ofAdd b) *
            (fX (Multiplicative.ofAdd c) * fY (Multiplicative.ofAdd d) *
              fU (Multiplicative.ofAdd f)) := by group
    · rw [element_swap_mul, hΦ, hΦ, hΦ]
      simp only [F, ofAdd_add, map_mul, hU1]
      have hcomXYY : fX (Multiplicative.ofAdd d) *
          (fY (Multiplicative.ofAdd b) * fY (Multiplicative.ofAdd c)) =
          fY (Multiplicative.ofAdd b) * fY (Multiplicative.ofAdd c) *
            fX (Multiplicative.ofAdd d) := by
        rw [← mul_assoc, hcomXY, mul_assoc, hcomXY, mul_assoc]
      calc fX (Multiplicative.ofAdd a) * fX (Multiplicative.ofAdd d) *
            (fY (Multiplicative.ofAdd b) * fY (Multiplicative.ofAdd c)) *
            (u * fU (Multiplicative.ofAdd f))
          = fX (Multiplicative.ofAdd a) * (fX (Multiplicative.ofAdd d) *
            (fY (Multiplicative.ofAdd b) * fY (Multiplicative.ofAdd c))) *
            (u * fU (Multiplicative.ofAdd f)) := by group
        _ = fX (Multiplicative.ofAdd a) * (fY (Multiplicative.ofAdd b) *
            fY (Multiplicative.ofAdd c) * fX (Multiplicative.ofAdd d)) *
            (u * fU (Multiplicative.ofAdd f)) := by rw [hcomXYY]
        _ = fX (Multiplicative.ofAdd a) * fY (Multiplicative.ofAdd b) *
            ((u * fX (Multiplicative.ofAdd c) * u⁻¹) * (u * fY (Multiplicative.ofAdd d) * u⁻¹)) *
            (u * fU (Multiplicative.ofAdd f)) := by rw [hUX, hUY]; group
        _ = fX (Multiplicative.ofAdd a) * fY (Multiplicative.ofAdd b) * u *
            (fX (Multiplicative.ofAdd c) * fY (Multiplicative.ofAdd d) *
              fU (Multiplicative.ofAdd f)) := by group
  have hΦone : Φfun 1 = 1 := by
    rw [← element_zero, hΦ]
    simp only [F, ofAdd_zero, map_one, mul_one]
  let Φ : Wreath (2 ^ n) →* R :=
    { toFun := Φfun
      map_one' := hΦone
      map_mul' := hΦmul }
  have hΦinj : Function.Injective Φ := by
    rw [injective_iff_map_eq_one]
    intro g hg
    obtain ⟨a, b, e, rfl⟩ := hsurjW g
    change Φfun (element (2 ^ n) a b e) = 1 at hg
    rw [hΦ] at hg
    rcases swap_exponent_cases e with rfl | rfl
    · simp only [F, hU0, mul_one, hfX, hfY] at hg
      have h1 := hψeq (Multiplicative.ofAdd a) (Multiplicative.ofAdd b) 1 1 (by
        simp only [toAdd_ofAdd, toAdd_one, ZMod.val_zero, pow_zero, mul_one]
        exact hg)
      have ha0 : a = 0 := congrArg Multiplicative.toAdd h1.1
      have hb0 : b = 0 := congrArg Multiplicative.toAdd h1.2
      rw [ha0, hb0, element_zero]
    · exfalso
      simp only [F, hU1] at hg
      apply huQ
      have e : u = (fX (Multiplicative.ofAdd a) * fY (Multiplicative.ofAdd b))⁻¹ :=
        eq_inv_of_mul_eq_one_right hg
      rw [e]
      exact Q.inv_mem (Q.mul_mem (hfXQ a) (hfYQ b))
  have hΦbij : Function.Bijective Φ :=
    hΦinj.bijective_of_nat_card_le (by rw [hRcard, card_wreath, ← pow_mul, mul_comm n 2,
      pow_succ, mul_comm])
  refine ⟨x, y, u, hxQ, hyQ, huQ, hu2, hordx, hordy, hQcomm x hxQ y hyQ, hinf, hsup, hux, huy,
    hRcard, ⟨(MulEquiv.ofBijective Φ hΦbij).symm, ?_⟩, ?_⟩
  · ext g
    rw [Subgroup.mem_map_equiv, MulEquiv.symm_symm, MulEquiv.ofBijective_apply]
    obtain ⟨a, b, f, rfl⟩ := hsurjW g
    change Φfun (element (2 ^ n) a b f) ∈ Q ↔ element (2 ^ n) a b f ∈ baseSubgroup (2 ^ n)
    rw [element_mem_base, hΦ]
    rcases swap_exponent_cases f with rfl | rfl
    · simp only [F, hU0, mul_one, iff_true]
      exact Q.mul_mem (hfXQ a) (hfYQ b)
    · simp only [F, hU1, one_ne_zero, iff_false]
      intro h
      apply huQ
      have e : u = (fX (Multiplicative.ofAdd a) * fY (Multiplicative.ofAdd b))⁻¹ *
          (fX (Multiplicative.ofAdd a) * fY (Multiplicative.ofAdd b) * u) := by group
      rw [e]
      exact Q.mul_mem (Q.inv_mem (Q.mul_mem (hfXQ a) (hfYQ b))) h
  · intro hn2
    have hcentu : ∀ q ∈ Q, u * q * u⁻¹ = q → q ∈ Subgroup.zpowers (x * y) := by
      intro q hq hfix
      obtain ⟨c, d, rfl⟩ := hrep q hq
      have e1 : u * (x ^ (Multiplicative.toAdd c).val * y ^ (Multiplicative.toAdd d).val) * u⁻¹ =
          x ^ (Multiplicative.toAdd d).val * y ^ (Multiplicative.toAdd c).val := by
        rw [show u * (x ^ (Multiplicative.toAdd c).val * y ^ (Multiplicative.toAdd d).val) * u⁻¹ =
            (u * x ^ (Multiplicative.toAdd c).val * u⁻¹) *
              (u * y ^ (Multiplicative.toAdd d).val * u⁻¹) by group,
          ← conj_pow, ← conj_pow, hux, huy]
        exact hQcomm _ (Q.pow_mem hyQ _) _ (Q.pow_mem hxQ _)
      rw [e1] at hfix
      have hcd : d = c := (hψeq _ _ _ _ hfix).1
      rw [hcd, ← (Commute.mul_pow (hQcomm x hxQ y hyQ))]
      exact Subgroup.pow_mem _ (Subgroup.mem_zpowers _) _
    have hbound : ∀ H : Subgroup R, IsMulCommutative H → ¬ H ≤ Q →
        Nat.card H ≤ 2 ^ (n + 1) := by
      intro H hHab hHQ
      obtain ⟨w, hwH, hwQ⟩ := Set.not_subset.mp hHQ
      have hq₁ : w * u⁻¹ ∈ Q := by
        rw [Subgroup.mul_mem_iff_of_index_two hQindex]
        exact iff_of_false hwQ (fun h => huQ (by simpa using Q.inv_mem h))
      have hwconj : ∀ q ∈ Q, w * q * w⁻¹ = u * q * u⁻¹ := by
        intro q hq
        have huq : u * q * u⁻¹ ∈ Q := hQnormal.conj_mem q hq u
        calc w * q * w⁻¹ = (w * u⁻¹) * (u * q * u⁻¹) * (w * u⁻¹)⁻¹ := by group
          _ = u * q * u⁻¹ := by rw [hQcomm _ hq₁ _ huq]; group
      have hle : Q ⊓ H ≤ Subgroup.zpowers (x * y) := by
        intro q hq
        apply hcentu q hq.1
        rw [← hwconj q hq.1, setLike_mul_comm (s := H) hwH hq.2, mul_inv_cancel_right]
      have hcardle : Nat.card (Q ⊓ H : Subgroup R) ≤ 2 ^ n := by
        calc Nat.card (Q ⊓ H : Subgroup R) ≤ Nat.card (Subgroup.zpowers (x * y)) :=
              Subgroup.card_le_of_le hle
          _ = 2 ^ n := by rw [Nat.card_zpowers, hordxy]
      have hrel : Q.relIndex H ≤ 2 := by
        have h1 := Subgroup.relIndex_dvd_index_of_normal Q H
        rw [hQindex] at h1
        exact Nat.le_of_dvd (by norm_num) h1
      rw [← Subgroup.relIndex_mul_card Q H, pow_succ, mul_comm (2 ^ n) 2]
      exact Nat.mul_le_mul hrel hcardle
    have huniq : ∀ H : Subgroup R, IsMulCommutative H → H.index = 2 → H = Q := by
      intro H hHab hHidx
      have hHcard : Nat.card H = 2 ^ (2 * n) := by
        have h1 := Subgroup.card_mul_index H
        rw [hHidx, hRcard, pow_succ] at h1
        exact Nat.eq_of_mul_eq_mul_right (by norm_num) h1
      by_cases hHQ : H ≤ Q
      · exact Subgroup.eq_of_le_of_card_ge hHQ (by rw [hQcard, hHcard, ← pow_mul, mul_comm])
      · exfalso
        have h1 := hbound H hHab hHQ
        rw [hHcard] at h1
        have h2 : 2 * n ≤ n + 1 := (Nat.pow_le_pow_iff_right (by norm_num)).mp h1
        omega
    refine ⟨hbound, huniq, ⟨fun σ => huniq _ ?_ ?_⟩⟩
    · exact Subgroup.comap_injective_isMulCommutative Q σ.injective
    · rw [Subgroup.index_comap_of_surjective Q σ.surjective, hQindex]

end CFSG.RankTwoShapes
