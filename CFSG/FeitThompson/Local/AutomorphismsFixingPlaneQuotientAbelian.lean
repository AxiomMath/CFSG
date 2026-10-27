module

public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.Module.ZMod
public import Mathlib.FieldTheory.Finiteness

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

variable {B : Type*} [Group B]

def autFixingQuotient (T : Subgroup B) : Subgroup (MulAut B) where
  carrier := {a | (∀ t ∈ T, a t = t) ∧ ∀ b : B, (↑(a b) : B ⧸ T) = (↑b : B ⧸ T)}
  one_mem' := ⟨fun _ _ => rfl, fun _ => rfl⟩
  mul_mem' := by
    rintro a b ⟨ha1, ha2⟩ ⟨hb1, hb2⟩
    refine ⟨fun t ht => ?_, fun x => ?_⟩
    · rw [MulAut.mul_apply, hb1 t ht, ha1 t ht]
    · rw [MulAut.mul_apply, ha2, hb2]
  inv_mem' := by
    rintro a ⟨ha1, ha2⟩
    refine ⟨fun t ht => ?_, fun x => ?_⟩
    · rw [MulAut.inv_apply]
      exact a.symm_apply_eq.2 (ha1 t ht).symm
    · have := ha2 (a⁻¹ x)
      rw [MulAut.inv_apply, a.apply_symm_apply] at this
      exact this.symm

theorem mem_autFixingQuotient {T : Subgroup B} {a : MulAut B} :
    a ∈ autFixingQuotient T ↔
      (∀ t ∈ T, a t = t) ∧ ∀ b : B, (↑(a b) : B ⧸ T) = (↑b : B ⧸ T) := (Iff.rfl)

theorem autFixingQuotient_apply_mem {T : Subgroup B} {a : MulAut B}
    (ha : a ∈ autFixingQuotient T) {t : B} (ht : t ∈ T) : a t = t :=
  ha.1 t ht

theorem autFixingQuotient_coe_apply {T : Subgroup B} {a : MulAut B}
    (ha : a ∈ autFixingQuotient T) (b : B) : (↑(a b) : B ⧸ T) = (↑b : B ⧸ T) :=
  ha.2 b

theorem inv_mul_apply_mem_of_mem_autFixingQuotient {T : Subgroup B} {a : MulAut B}
    (ha : a ∈ autFixingQuotient T) (y : B) : y⁻¹ * a y ∈ T :=
  QuotientGroup.eq.1 (ha.2 y).symm

def autFixingQuotientEval (T : Subgroup B) (y : B) : autFixingQuotient T →* T where
  toFun a := ⟨y⁻¹ * (a : MulAut B) y, inv_mul_apply_mem_of_mem_autFixingQuotient a.2 y⟩
  map_one' := by ext; simp
  map_mul' a b := by
    have key : (a : MulAut B) (y⁻¹ * (b : MulAut B) y) = y⁻¹ * (b : MulAut B) y :=
      autFixingQuotient_apply_mem a.2 (inv_mul_apply_mem_of_mem_autFixingQuotient b.2 y)
    have h : (a : MulAut B) ((b : MulAut B) y)
        = (a : MulAut B) y * (y⁻¹ * (b : MulAut B) y) := by
      rw [← key, ← map_mul]; congr 1; group
    ext
    simp only [Subgroup.coe_mul, MulMemClass.mk_mul_mk]
    rw [MulAut.mul_apply, h]
    group

@[simp]
theorem autFixingQuotientEval_apply_coe {T : Subgroup B} (y : B)
    (a : autFixingQuotient T) : (autFixingQuotientEval T y a : B) = y⁻¹ * (a : MulAut B) y :=
  (rfl)

theorem autFixingQuotientEval_injective {T : Subgroup B} {y : B}
    (hy : T ⊔ Subgroup.zpowers y = ⊤) :
    Function.Injective (autFixingQuotientEval T y) := by
  rw [injective_iff_map_eq_one]
  intro a ha
  have h1 : y⁻¹ * (a : MulAut B) y = 1 := by
    have := Subtype.ext_iff.1 ha
    rwa [autFixingQuotientEval_apply_coe, OneMemClass.coe_one] at this
  have hay : (a : MulAut B) y = y := by rw [inv_mul_eq_one] at h1; exact h1.symm
  have key : (⊤ : Subgroup B) ≤
      ((a : MulAut B) : B ≃* B).toMonoidHom.eqLocus (MonoidHom.id B) := by
    rw [← hy]
    exact sup_le (fun t ht => autFixingQuotient_apply_mem a.2 ht) (Subgroup.zpowers_le.2 hay)
  ext x
  exact key (Subgroup.mem_top x)

theorem sup_zpowers_eq_top_of_index_prime {T : Subgroup B} {p : ℕ} (hp : p.Prime)
    (hT : T.index = p) {y : B} (hy : y ∉ T) : T ⊔ Subgroup.zpowers y = ⊤ := by
  have hfi : T.FiniteIndex := ⟨by rw [hT]; exact hp.pos.ne'⟩
  have hlt : T < T ⊔ Subgroup.zpowers y :=
    lt_of_le_of_ne le_sup_left fun h => hy (Subgroup.zpowers_le.1 (h ▸ le_sup_right))
  have h1 := Subgroup.index_strictAnti hlt
  have h2 := Subgroup.index_dvd_of_le (le_sup_left : T ≤ T ⊔ Subgroup.zpowers y)
  rw [hT] at h1 h2
  rcases hp.eq_one_or_self_of_dvd _ h2 with h | h
  · exact Subgroup.index_eq_one.1 h
  · omega

theorem exists_mulEquiv_pi_multiplicative_zmod {p : ℕ} (hp : p.Prime) (G : Type*) [CommGroup G]
    [Finite G] (h : ∀ g : G, g ^ p = 1) :
    ∃ d : ℕ, Nat.card G = p ^ d ∧ Nonempty (G ≃* (Fin d → Multiplicative (ZMod p))) := by
  have : Fact p.Prime := ⟨hp⟩
  let i : Module (ZMod p) (Additive G) :=
    AddCommGroup.zmodModule (n := p) fun x => by
      apply Additive.toMul.injective
      rw [toMul_nsmul, toMul_zero]
      exact h _
  have hfin : @Module.Finite (ZMod p) (Additive G) _ _ i := Module.Finite.of_finite
  have hfree : @Module.Free (ZMod p) (Additive G) _ _ i := Module.Free.of_divisionRing _ _
  refine ⟨@Module.finrank (ZMod p) (Additive G) _ _ i, ?_, ⟨?_⟩⟩
  · have h2 := @Module.natCard_eq_pow_finrank (ZMod p) (Additive G) _ _ i hfin
    rw [Nat.card_zmod] at h2
    rw [← h2]
    exact Nat.card_congr (Additive.ofMul (α := G))
  · exact (MulEquiv.multiplicativeAdditive G).symm.trans
      ((AddEquiv.toMultiplicative
        (@Module.finBasis (ZMod p) (Additive G) _ _ i hfree _ hfin).equivFun.toAddEquiv).trans
        (MulEquiv.piMultiplicative _))

variable {p : ℕ}

theorem exists_injective_autFixingQuotientEval {T : Subgroup B} (hp : p.Prime)
    (hB : Nat.card B = p ^ 3) (hT : Nat.card T = p ^ 2) :
    ∃ y : B, y ∉ T ∧ Function.Injective (autFixingQuotientEval T y) := by
  have hfinB : Finite B := Nat.finite_of_card_ne_zero (by rw [hB]; exact pow_ne_zero _ hp.pos.ne')
  have hidx : T.index = p := by
    have h := Subgroup.card_mul_index T
    rw [hT, hB, show p ^ 3 = p ^ 2 * p by ring] at h
    exact Nat.eq_of_mul_eq_mul_left (pow_pos hp.pos 2) h
  have hne : T ≠ ⊤ := by
    intro h
    rw [h, Subgroup.card_top, hB] at hT
    have := Nat.pow_right_injective hp.two_le hT
    omega
  obtain ⟨y, hy⟩ : ∃ y, y ∉ T := by
    by_contra hc
    simp only [not_exists, not_not] at hc
    exact hne (Subgroup.eq_top_iff' T |>.2 hc)
  exact ⟨y, hy, autFixingQuotientEval_injective (sup_zpowers_eq_top_of_index_prime hp hidx hy)⟩

theorem autFixingQuotient_elementaryAbelian {T : Subgroup B} (hp : p.Prime)
    (hB : Nat.card B = p ^ 3) (hexp : ∀ b : B, b ^ p = 1) (hT : Nat.card T = p ^ 2) :
    ∃ d ≤ 2, Nat.card (autFixingQuotient T) = p ^ d ∧
      Nonempty (autFixingQuotient T ≃* (Fin d → Multiplicative (ZMod p))) := by
  have : Fact p.Prime := ⟨hp⟩
  have hfinB : Finite B := Nat.finite_of_card_ne_zero (by rw [hB]; exact pow_ne_zero _ hp.pos.ne')
  obtain ⟨y, -, hinj⟩ := exists_injective_autFixingQuotientEval hp hB hT
  have hTcomm : ∀ x z : T, x * z = z * x := by
    let _ := IsPGroup.commGroupOfCardEqPrimeSq (p := p) hT
    exact fun x z => mul_comm x z
  have hKcomm : ∀ x z : autFixingQuotient T, x * z = z * x := fun x z =>
    hinj (by rw [map_mul, map_mul, hTcomm])
  let _ : CommGroup (autFixingQuotient T) :=
    { (inferInstance : Group (autFixingQuotient T)) with mul_comm := hKcomm }
  have hKexp : ∀ a : autFixingQuotient T, a ^ p = 1 := by
    intro a
    apply hinj
    rw [map_pow, map_one]
    ext
    push_cast
    exact hexp _
  obtain ⟨d, hd, hiso⟩ := exists_mulEquiv_pi_multiplicative_zmod hp _ hKexp
  refine ⟨d, ?_, hd, hiso⟩
  have hdvd : Nat.card (autFixingQuotient T) ∣ Nat.card T :=
    Subgroup.card_dvd_of_injective _ hinj
  rw [hd, hT] at hdvd
  exact (Nat.pow_dvd_pow_iff_le_right hp.one_lt).1 hdvd

theorem card_autFixingQuotient_le {T : Subgroup B} (hp : p.Prime)
    (hB : Nat.card B = p ^ 3) (hexp : ∀ b : B, b ^ p = 1) (hT : Nat.card T = p ^ 2) :
    Nat.card (autFixingQuotient T) ≤ p ^ 2 := by
  obtain ⟨d, hd2, hd, -⟩ := autFixingQuotient_elementaryAbelian hp hB hexp hT
  rw [hd]
  exact Nat.pow_le_pow_right hp.pos hd2

theorem isPGroup_autFixingQuotient {T : Subgroup B} (hp : p.Prime)
    (hB : Nat.card B = p ^ 3) (hexp : ∀ b : B, b ^ p = 1) (hT : Nat.card T = p ^ 2) :
    IsPGroup p (autFixingQuotient T) := by
  obtain ⟨d, -, hd, -⟩ := autFixingQuotient_elementaryAbelian hp hB hexp hT
  exact IsPGroup.of_card hd

end

end CFSG.FeitThompson
