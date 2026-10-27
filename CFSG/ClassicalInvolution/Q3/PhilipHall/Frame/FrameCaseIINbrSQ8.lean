module

public import CFSG.ClassicalInvolution.Generic.Frame

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf.Q8

open CFSG.ClassicalInvolution.Generic

variable {G : Type*} [Group G]

private theorem q8_pow_four : ∀ x : QuaternionGroup 2, x ^ 4 = 1 := by decide

private theorem q8_unique : ∀ q : QuaternionGroup 2, q * q = 1 →
    q = 1 ∨ q = QuaternionGroup.a 2 := by decide

private theorem q8_a2_ne : (QuaternionGroup.a 2 : QuaternionGroup 2) ≠ 1 := by decide

private theorem q8_a2_sq : (QuaternionGroup.a 2 : QuaternionGroup 2) * QuaternionGroup.a 2 = 1 := by
  decide

private theorem q8_exists_other : ∀ p : QuaternionGroup 2, p * p ≠ 1 →
    ∃ q : QuaternionGroup 2, q * q ≠ 1 ∧ q ≠ p ∧ q ≠ p⁻¹ := by decide +kernel

private theorem q8_comm : ∀ p q : QuaternionGroup 2, p * p ≠ 1 → q * q ≠ 1 → p * q = q * p →
    q = p ∨ q = p⁻¹ := by decide +kernel

section Transport

variable {H : Type*} [Group H]

private theorem equiv_pow_four (e : H ≃* QuaternionGroup 2) (x : H) : x ^ 4 = 1 := by
  apply e.injective
  rw [map_pow, map_one]
  exact q8_pow_four _

private theorem equiv_unique (e : H ≃* QuaternionGroup 2) (y : H) (hy : y * y = 1) :
    y = 1 ∨ y = e.symm (QuaternionGroup.a 2) := by
  have := q8_unique (e y)
  simp only [← map_mul, ← map_one e, e.apply_eq_iff_eq] at this
  rcases this hy with h | h
  · exact Or.inl h
  · exact Or.inr (e.eq_symm_apply.2 h)

private theorem equiv_exists_other (e : H ≃* QuaternionGroup 2) {x : H} (hx : x * x ≠ 1) :
    ∃ y : H, y * y ≠ 1 ∧ y ≠ x ∧ y ≠ x⁻¹ := by
  obtain ⟨q, hq1, hq2, hq3⟩ := q8_exists_other (e x) (by
    simp only [← map_mul, ← map_one e, e.apply_eq_iff_eq, ne_eq]
    exact hx)
  refine ⟨e.symm q, fun h => hq1 ?_, fun h => hq2 ?_, fun h => hq3 ?_⟩
  · simpa using congrArg e h
  · simpa using congrArg e h
  · simpa [map_inv] using congrArg e h

private theorem equiv_comm (e : H ≃* QuaternionGroup 2) {x y : H} (hx : x * x ≠ 1) (hy : y * y ≠ 1)
    (h : x * y = y * x) : y = x ∨ y = x⁻¹ := by
  have := q8_comm (e x) (e y)
  simp only [← map_mul, ← map_inv, ← map_one e, e.apply_eq_iff_eq, ne_eq] at this
  exact this hx hy h

end Transport

section Basic

variable {R : Subgroup G}

private theorem mul_self_ne_one_of_orderOf_eq_four {x : G} (h : orderOf x = 4) : x * x ≠ 1 := by
  intro h1
  have h2 : orderOf x ∣ 2 := orderOf_dvd_of_pow_eq_one (by rwa [sq])
  rw [h] at h2
  omega

private theorem orderOf_eq_four_of {x : G} (h4 : x ^ 4 = 1) (h2 : x * x ≠ 1) : orderOf x = 4 := by
  have h2' : ¬ x ^ 2 ^ 1 = 1 := by
    rw [pow_one, sq]
    exact h2
  have := orderOf_eq_prime_pow (p := 2) (n := 1) h2' (by simpa using h4)
  simpa using this

private theorem mk_mul_self_ne_one {x : G} (hx : x ∈ R) (h4 : orderOf x = 4) :
    (⟨x, hx⟩ : ↥R) * ⟨x, hx⟩ ≠ 1 :=
  fun h => mul_self_ne_one_of_orderOf_eq_four h4 (congrArg Subtype.val h)

theorem exists_isUniqueInvolution_of_mulEquiv (hR : Nonempty (↥R ≃* QuaternionGroup 2)) :
    ∃ z, IsUniqueInvolution R z := by
  obtain ⟨e⟩ := hR
  refine ⟨(e.symm (QuaternionGroup.a 2) : G), (e.symm (QuaternionGroup.a 2)).2, ?_, ?_, ?_⟩
  · intro h
    have h1 : e.symm (QuaternionGroup.a 2) = 1 := Subtype.ext h
    apply q8_a2_ne
    simpa using congrArg e h1
  · have : e.symm (QuaternionGroup.a 2) * e.symm (QuaternionGroup.a 2) = 1 := by
      rw [← map_mul, q8_a2_sq, map_one]
    exact congrArg Subtype.val this
  · intro y hy hy2
    rcases equiv_unique e ⟨y, hy⟩ (Subtype.ext hy2) with h | h
    · exact Or.inl (congrArg Subtype.val h)
    · exact Or.inr (congrArg Subtype.val h)

theorem natCard_eq_eight_of_mulEquiv (hR : Nonempty (↥R ≃* QuaternionGroup 2)) :
    Nat.card ↥R = 8 := by
  obtain ⟨e⟩ := hR
  rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]

private theorem pow_four_of_mem (hR : Nonempty (↥R ≃* QuaternionGroup 2)) {x : G} (hx : x ∈ R) :
    x ^ 4 = 1 := by
  obtain ⟨e⟩ := hR
  exact congrArg Subtype.val (equiv_pow_four e ⟨x, hx⟩)

private theorem orderOf_eq_four_iff (hR : Nonempty (↥R ≃* QuaternionGroup 2)) {x : G}
    (hx : x ∈ R) : orderOf x = 4 ↔ x * x ≠ 1 :=
  ⟨mul_self_ne_one_of_orderOf_eq_four, fun h => orderOf_eq_four_of (pow_four_of_mem hR hx) h⟩

private theorem exists_other (hR : Nonempty (↥R ≃* QuaternionGroup 2)) {x : G} (hx : x ∈ R)
    (hx4 : orderOf x = 4) : ∃ y ∈ R, orderOf y = 4 ∧ y ≠ x ∧ y ≠ x⁻¹ := by
  obtain ⟨e⟩ := hR
  obtain ⟨y, hy, hyx, hyx'⟩ := equiv_exists_other e (mk_mul_self_ne_one hx hx4)
  exact ⟨y, y.2, (orderOf_eq_four_iff ⟨e⟩ y.2).2 fun h => hy (Subtype.ext h),
    fun h => hyx (Subtype.ext h), fun h => hyx' (Subtype.ext h)⟩

private theorem comm_cases (hR : Nonempty (↥R ≃* QuaternionGroup 2)) {x y : G} (hx : x ∈ R)
    (hy : y ∈ R) (hx4 : orderOf x = 4) (hy4 : orderOf y = 4) (h : x * y = y * x) :
    y = x ∨ y = x⁻¹ := by
  obtain ⟨e⟩ := hR
  rcases equiv_comm e (mk_mul_self_ne_one hx hx4) (mk_mul_self_ne_one hy hy4) (Subtype.ext h) with
    h' | h'
  · exact Or.inl (congrArg Subtype.val h')
  · exact Or.inr (congrArg Subtype.val h')

end Basic

section CentralProduct

variable {R R' : Subgroup G} {z : G}

theorem mem_sup_iff_exists_mul_of_forall_comm (hcomm : ∀ x ∈ R, ∀ y ∈ R', x * y = y * x) {u : G} :
    u ∈ R ⊔ R' ↔ ∃ x ∈ R, ∃ y ∈ R', u = x * y := by
  constructor
  · intro hu
    let P : Subgroup G :=
      { carrier := {u | ∃ x ∈ R, ∃ y ∈ R', u = x * y}
        one_mem' := ⟨1, R.one_mem, 1, R'.one_mem, by simp⟩
        mul_mem' := by
          rintro _ _ ⟨x, hx, y, hy, rfl⟩ ⟨x', hx', y', hy', rfl⟩
          refine ⟨x * x', R.mul_mem hx hx', y * y', R'.mul_mem hy hy', ?_⟩
          have h := hcomm x' hx' y hy
          calc x * y * (x' * y') = x * (y * x') * y' := by group
            _ = x * (x' * y) * y' := by rw [h]
            _ = x * x' * (y * y') := by group
        inv_mem' := by
          rintro _ ⟨x, hx, y, hy, rfl⟩
          refine ⟨x⁻¹, R.inv_mem hx, y⁻¹, R'.inv_mem hy, ?_⟩
          rw [mul_inv_rev]
          exact (hcomm x⁻¹ (R.inv_mem hx) y⁻¹ (R'.inv_mem hy)).symm }
    have hle : R ⊔ R' ≤ P :=
      sup_le (fun x hx => ⟨x, hx, 1, R'.one_mem, by simp⟩)
        (fun y hy => ⟨1, R.one_mem, y, hy, by simp⟩)
    exact hle hu
  · rintro ⟨x, hx, y, hy, rfl⟩
    exact Subgroup.mul_mem_sup hx hy

theorem eq_one_or_eq_unique_involution_of_forall_comm (hR : Nonempty (↥R ≃* QuaternionGroup 2))
    (hz : IsUniqueInvolution R z) {t : G} (ht : t ∈ R) (h : ∀ r ∈ R, t * r = r * t) :
    t = 1 ∨ t = z := by
  by_cases h2 : t * t = 1
  · exact hz.unique t ht h2
  · exfalso
    have ht4 : orderOf t = 4 := (orderOf_eq_four_iff hR ht).2 h2
    obtain ⟨y, hy, hy4, h1, h3⟩ := exists_other hR ht ht4
    rcases comm_cases hR ht hy ht4 hy4 (h y hy) with h4 | h4
    · exact h1 h4
    · exact h3 h4

theorem eq_one_or_eq_unique_involution_of_mem_inf (hR : Nonempty (↥R ≃* QuaternionGroup 2))
    (hz : IsUniqueInvolution R z) (hcomm : ∀ x ∈ R, ∀ y ∈ R', x * y = y * x) {t : G}
    (ht : t ∈ R ⊓ R') : t = 1 ∨ t = z :=
  eq_one_or_eq_unique_involution_of_forall_comm hR hz ht.1 fun r hr => (hcomm r hr t ht.2).symm

theorem natCard_sup_eq_32 (hR : Nonempty (↥R ≃* QuaternionGroup 2))
    (hR' : Nonempty (↥R' ≃* QuaternionGroup 2)) (hz : IsUniqueInvolution R z)
    (hz' : IsUniqueInvolution R' z) (hcomm : ∀ x ∈ R, ∀ y ∈ R', x * y = y * x) :
    Nat.card ↥(R ⊔ R') = 32 := by
  have hc : ∀ (a : ↥R) (b : ↥R'), Commute (R.subtype a) (R'.subtype b) :=
    fun a b => hcomm a a.2 b b.2
  let φ : ↥R × ↥R' →* G := MonoidHom.noncommCoprod R.subtype R'.subtype hc
  have hrange : φ.range = R ⊔ R' := by
    show (MonoidHom.noncommCoprod R.subtype R'.subtype hc).range = R ⊔ R'
    rw [MonoidHom.noncommCoprod_range, Subgroup.range_subtype, Subgroup.range_subtype]
  have hker : φ.ker = Subgroup.zpowers ((⟨z, hz.mem⟩, ⟨z, hz'.mem⟩) : ↥R × ↥R') := by
    ext ⟨a, b⟩
    rw [MonoidHom.mem_ker]
    constructor
    · intro h
      have h1 : (a : G) * b = 1 := h
      have hb : (a : G) = (b : G)⁻¹ := eq_inv_of_mul_eq_one_left h1
      have hab : (a : G) ∈ R ⊓ R' := ⟨a.2, by rw [hb]; exact R'.inv_mem b.2⟩
      rcases eq_one_or_eq_unique_involution_of_mem_inf hR hz hcomm hab with h2 | h2
      · have hb1 : (b : G) = 1 := by rw [h2, one_mul] at h1; exact h1
        have : (a, b) = 1 := Prod.ext (Subtype.ext h2) (Subtype.ext hb1)
        rw [this]
        exact one_mem _
      · have hb1 : (b : G) = z := by
          rw [h2] at h1
          rw [← inv_eq_of_mul_eq_one_right h1]
          exact inv_eq_of_mul_eq_one_right hz.sq
        have : (a, b) = (⟨z, hz.mem⟩, ⟨z, hz'.mem⟩) := Prod.ext (Subtype.ext h2) (Subtype.ext hb1)
        rw [this]
        exact Subgroup.mem_zpowers _
    · intro h
      have hle : Subgroup.zpowers ((⟨z, hz.mem⟩, ⟨z, hz'.mem⟩) : ↥R × ↥R') ≤ φ.ker :=
        Subgroup.zpowers_le.2 (MonoidHom.mem_ker.2 hz.sq)
      exact MonoidHom.mem_ker.1 (hle h)
  have hord : orderOf ((⟨z, hz.mem⟩, ⟨z, hz'.mem⟩) : ↥R × ↥R') = 2 := by
    have hz2 : orderOf z = 2 := orderOf_eq_prime (by rw [sq]; exact hz.sq) hz.ne_one
    rw [Prod.orderOf_mk, Subgroup.orderOf_mk, Subgroup.orderOf_mk, hz2]
    rfl
  have hkerCard : Nat.card φ.ker = 2 := by rw [hker, Nat.card_zpowers, hord]
  have h64 : Nat.card (↥R × ↥R') = 64 := by
    rw [Nat.card_prod, natCard_eq_eight_of_mulEquiv hR, natCard_eq_eight_of_mulEquiv hR']
  have h3 := Subgroup.card_eq_card_quotient_mul_card_subgroup φ.ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv, h64, hkerCard] at h3
  rw [← hrange]
  omega

end CentralProduct

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf.Q8
