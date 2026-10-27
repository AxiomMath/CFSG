module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk47abShape
public import Mathlib.FieldTheory.Finite.GaloisField

public section

namespace CFSG.GH74.GLS.IVK.Proofs2.Ivk47ab

open scoped MatrixGroups

theorem kl_pow_four {M : Type*} [Monoid M] (a : M) : a ^ 4 = (a * a) * (a * a) := by
  rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add, pow_two]

section Finite3

theorem kl_eq_neg_one_of_not_isSquare : ∀ x : ZMod 3, ¬IsSquare x → x = -1 := by decide

theorem kl_mul_adj : ∀ p q r s : ZMod 3, p * s - q * r = -1 →
    (!![p, q; r, s] : Matrix (Fin 2) (Fin 2) (ZMod 3)) * !![-s, q; r, -p] = 1 := by
  decide

theorem kl_sl3_sq_one : ∀ a : SL(2, ZMod 3), a * a = 1 → a = 1 ∨ a = -1 := by decide

theorem kl_sl3_noncentral : ∀ a : SL(2, ZMod 3), a ≠ 1 → a ≠ -1 →
    ∃ c : SL(2, ZMod 3), a * c ≠ c * a ∧ a * c ≠ -1 * (c * a) := by
  decide

theorem kl_outer_matrix : ∀ p q r s : ZMod 3, p * s - q * r = -1 →
    ∃ c : SL(2, ZMod 3),
      (!![p, q; r, s] * (c : Matrix (Fin 2) (Fin 2) (ZMod 3)) * !![-s, q; r, -p]) ≠
        (c : Matrix (Fin 2) (Fin 2) (ZMod 3)) ∧
      (!![p, q; r, s] * (c : Matrix (Fin 2) (Fin 2) (ZMod 3)) * !![-s, q; r, -p]) ≠
        ((-1 * c : SL(2, ZMod 3)) : Matrix (Fin 2) (Fin 2) (ZMod 3)) := by
  decide

theorem kl_two_comm : ∀ x : SL(2, ZMod 3), x ≠ 1 → x ≠ -1 →
    ∃ c₁ c₂ : SL(2, ZMod 3),
      (x * c₁ * x⁻¹ * c₁⁻¹) * (x * c₁ * x⁻¹ * c₁⁻¹) = -1 ∧
      (x * c₂ * x⁻¹ * c₂⁻¹) * (x * c₂ * x⁻¹ * c₂⁻¹) = -1 ∧
      (x * c₁ * x⁻¹ * c₁⁻¹) * (x * c₂ * x⁻¹ * c₂⁻¹) =
        -1 * ((x * c₂ * x⁻¹ * c₂⁻¹) * (x * c₁ * x⁻¹ * c₁⁻¹)) := by
  decide

theorem kl_q8_gen : ∀ p q : SL(2, ZMod 3), p * p = -1 → q * q = -1 → p * q = -1 * (q * p) →
    ∀ y : SL(2, ZMod 3), y ^ 4 = 1 → ∃ a : Fin 4, ∃ b : Fin 2, y = p ^ (a : ℕ) * q ^ (b : ℕ) := by
  decide

theorem kl_q8_mul : ∀ a b : SL(2, ZMod 3), a ^ 4 = 1 → b ^ 4 = 1 → (a * b) ^ 4 = 1 := by decide

theorem kl_noncomm_pair : ∃ i j : SL(2, ZMod 3), i ^ 4 = 1 ∧ j ^ 4 = 1 ∧ i * j ≠ j * i := by decide

theorem kl_sl3_normal {N : Subgroup SL(2, ZMod 3)} (hN : N.Normal) {x : SL(2, ZMod 3)} (hx : x ∈ N)
    (hx1 : x ≠ 1) (hx2 : x ≠ -1) {y : SL(2, ZMod 3)} (hy : y ^ 4 = 1) : y ∈ N := by
  obtain ⟨c₁, c₂, h₁, h₂, h₃⟩ := kl_two_comm x hx1 hx2
  have hmem : ∀ c : SL(2, ZMod 3), x * c * x⁻¹ * c⁻¹ ∈ N := by
    intro c
    have h1 : c * x⁻¹ * c⁻¹ ∈ N := hN.conj_mem _ (N.inv_mem hx) c
    have h2 : x * c * x⁻¹ * c⁻¹ = x * (c * x⁻¹ * c⁻¹) := by group
    rw [h2]
    exact N.mul_mem hx h1
  obtain ⟨a, b, hab⟩ := kl_q8_gen _ _ h₁ h₂ h₃ y hy
  rw [hab]
  exact N.mul_mem (N.pow_mem (hmem c₁) _) (N.pow_mem (hmem c₂) _)

theorem kl_move_toGL {A₀ : SL(2, ZMod 3)} (h1 : A₀ ≠ 1) (h2 : A₀ ≠ -1) :
    ∃ C : SL(2, ZMod 3), conjSLAut (Matrix.SpecialLinearGroup.toGL A₀) C ≠ C ∧
      conjSLAut (Matrix.SpecialLinearGroup.toGL A₀) C ≠ -1 * C := by
  obtain ⟨C, hC1, hC2⟩ := kl_sl3_noncentral A₀ h1 h2
  refine ⟨C, ?_, ?_⟩
  · rw [conjSLAut_toGL]
    intro h
    exact hC1 (mul_inv_eq_iff_eq_mul.1 h)
  · rw [conjSLAut_toGL]
    intro h
    apply hC2
    rw [mul_inv_eq_iff_eq_mul] at h
    rw [h, mul_assoc]

theorem kl_move_outer {G : GL (Fin 2) (ZMod 3)}
    (hG : ¬IsSquare ((Matrix.GeneralLinearGroup.det G : (ZMod 3)ˣ) : ZMod 3)) :
    ∃ C : SL(2, ZMod 3), conjSLAut G C ≠ C ∧ conjSLAut G C ≠ -1 * C := by
  have hdet : ((Matrix.GeneralLinearGroup.det G : (ZMod 3)ˣ) : ZMod 3) = -1 :=
    kl_eq_neg_one_of_not_isSquare _ hG
  rw [Matrix.GeneralLinearGroup.val_det_apply] at hdet
  obtain ⟨p, q, r, s, hM⟩ : ∃ p q r s : ZMod 3,
      (G : Matrix (Fin 2) (Fin 2) (ZMod 3)) = !![p, q; r, s] :=
    ⟨_, _, _, _, Matrix.eta_fin_two _⟩
  rw [hM, Matrix.det_fin_two_of] at hdet
  have hN : ((G⁻¹ : GL (Fin 2) (ZMod 3)) : Matrix (Fin 2) (Fin 2) (ZMod 3)) = !![-s, q; r, -p] := by
    rw [Matrix.coe_units_inv, hM]
    exact Matrix.inv_eq_right_inv (kl_mul_adj p q r s hdet)
  obtain ⟨C, hC1, hC2⟩ := kl_outer_matrix p q r s hdet
  refine ⟨C, fun h => hC1 ?_, fun h => hC2 ?_⟩
  · have := congrArg Subtype.val h
    rwa [conjSLAut_coe, hN, hM] at this
  · have := congrArg Subtype.val h
    rwa [conjSLAut_coe, hN, hM] at this

end Finite3

section Quat

variable {Y : Type} [Group Y]

@[expose] def klQ8 : Subgroup SL(2, ZMod 3) where
  carrier := {x | x ^ 4 = 1}
  one_mem' := one_pow 4
  mul_mem' {a b} ha hb := kl_q8_mul a b ha hb
  inv_mem' {x} hx := by
    show x⁻¹ ^ 4 = 1
    rw [inv_pow, show x ^ 4 = 1 from hx, inv_one]

theorem card_klQ8 : Nat.card klQ8 = 8 := by
  show Nat.card {x : SL(2, ZMod 3) // x ^ 4 = 1} = 8
  rw [Nat.card_eq_fintype_card]
  decide

@[expose] def klQuat (I : Subgroup Y) (e : ↥I ≃* SL(2, ZMod 3)) : Subgroup Y :=
  (klQ8.map e.symm.toMonoidHom).map I.subtype

theorem mem_klQuat {I : Subgroup Y} {e : ↥I ≃* SL(2, ZMod 3)} {a : Y} :
    a ∈ klQuat I e ↔ a ∈ I ∧ a ^ 4 = 1 := by
  constructor
  · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    refine ⟨(e.symm y).2, ?_⟩
    have h1 : (e.symm y) ^ 4 = 1 := by
      rw [← map_pow, show y ^ 4 = 1 from hy, map_one]
    show ((e.symm y : ↥I) : Y) ^ 4 = 1
    rw [← Subgroup.coe_pow, h1]
    rfl
  · rintro ⟨ha, ha4⟩
    have h1 : (⟨a, ha⟩ : ↥I) ^ 4 = 1 := Subtype.ext (by rw [Subgroup.coe_pow]; exact ha4)
    refine ⟨⟨a, ha⟩, ⟨e ⟨a, ha⟩, ?_, by simp⟩, rfl⟩
    show (e ⟨a, ha⟩) ^ 4 = 1
    rw [← map_pow, h1, map_one]

theorem card_klQuat (I : Subgroup Y) (e : ↥I ≃* SL(2, ZMod 3)) : Nat.card (klQuat I e) = 8 := by
  rw [klQuat, Subgroup.card_map_of_injective I.subtype_injective,
    Subgroup.card_map_of_injective (f := e.symm.toMonoidHom) e.symm.injective, card_klQ8]

theorem kl_exists_prod_range {K : Type} [Group K] {I₁ I₂ : Subgroup K}
    (hcomm : ∀ x ∈ I₁, ∀ y ∈ I₂, x * y = y * x) (hcard : Nat.card ↥(I₁ ⊓ I₂) = 2) :
    ∃ A : Subgroup K, (∀ x ∈ A, ∃ a ∈ I₁, ∃ b ∈ I₂, x = a * b) ∧
      Nat.card ↥A * 2 = Nat.card ↥I₁ * Nat.card ↥I₂ := by
  have hc : ∀ (a : I₁) (b : I₂), Commute (I₁.subtype a) (I₂.subtype b) :=
    fun a b => hcomm a a.2 b b.2
  set f : I₁ × I₂ →* K := I₁.subtype.noncommCoprod I₂.subtype hc with hf
  have hfapp : ∀ x : I₁ × I₂, f x = (x.1 : K) * (x.2 : K) := fun x => rfl
  refine ⟨f.range, ?_, ?_⟩
  · rintro _ ⟨x, rfl⟩
    exact ⟨x.1, x.1.2, x.2, x.2.2, rfl⟩
  · have hker : Nat.card f.ker = 2 := by
      rw [← hcard]
      refine Nat.card_congr
        { toFun := fun x => ⟨(x.1.1 : K), x.1.1.2, by
            have h := (MonoidHom.mem_ker.mp x.2)
            rw [hfapp] at h
            have h' : (x.1.2 : K) = (x.1.1 : K)⁻¹ := eq_inv_of_mul_eq_one_right h
            have h'' : (x.1.1 : K) = ((x.1.2 : K))⁻¹ := by rw [h', inv_inv]
            rw [h'']
            exact I₂.inv_mem (x.1.2).2⟩
          invFun := fun x => ⟨(⟨x.1, x.2.1⟩, ⟨x.1⁻¹, I₂.inv_mem x.2.2⟩), by
            rw [MonoidHom.mem_ker, hfapp]
            exact mul_inv_cancel _⟩
          left_inv := fun x => by
            apply Subtype.ext
            have h := (MonoidHom.mem_ker.mp x.2)
            rw [hfapp] at h
            have h' : (x.1.2 : K) = (x.1.1 : K)⁻¹ := eq_inv_of_mul_eq_one_right h
            refine Prod.ext rfl (Subtype.ext ?_)
            exact h'.symm
          right_inv := fun x => rfl }
    have := Subgroup.card_ker_mul_card_range f
    rw [hker, Nat.card_prod] at this
    rw [mul_comm]
    exact this

theorem kl_Q32 {I₁ I₂ : Subgroup Y} (e₁ : ↥I₁ ≃* SL(2, ZMod 3)) (e₂ : ↥I₂ ≃* SL(2, ZMod 3)) {z : Y}
    (hcomm : ∀ a ∈ I₁, ∀ b ∈ I₂, a * b = b * a) (hinter : I₁ ⊓ I₂ = Subgroup.zpowers z)
    (hz2 : z * z = 1) (hz1 : z ≠ 1) :
    ∃ R : Subgroup Y, Nat.card R = 32 ∧
      ∀ x ∈ R, ∃ a ∈ I₁, ∃ b ∈ I₂, a ^ 4 = 1 ∧ b ^ 4 = 1 ∧ x = a * b := by
  have hz4 : z ^ 4 = 1 := by
    rw [kl_pow_four, hz2, one_mul]
  have hzI₁ : z ∈ I₁ := by
    have : z ∈ I₁ ⊓ I₂ := by rw [hinter]; exact Subgroup.mem_zpowers z
    exact this.1
  have hzI₂ : z ∈ I₂ := by
    have : z ∈ I₁ ⊓ I₂ := by rw [hinter]; exact Subgroup.mem_zpowers z
    exact this.2
  have hq : klQuat I₁ e₁ ⊓ klQuat I₂ e₂ = Subgroup.zpowers z := by
    apply le_antisymm
    · intro a ha
      rw [← hinter]
      exact ⟨(mem_klQuat.1 ha.1).1, (mem_klQuat.1 ha.2).1⟩
    · rw [Subgroup.zpowers_le]
      exact ⟨mem_klQuat.2 ⟨hzI₁, hz4⟩, mem_klQuat.2 ⟨hzI₂, hz4⟩⟩
  have hcard2 : Nat.card ↥(klQuat I₁ e₁ ⊓ klQuat I₂ e₂) = 2 := by
    rw [hq, Nat.card_zpowers, orderOf_eq_prime (by rw [pow_two]; exact hz2) hz1]
  obtain ⟨A, hA, hAcard⟩ := kl_exists_prod_range
    (fun x hx y hy => hcomm x (mem_klQuat.1 hx).1 y (mem_klQuat.1 hy).1) hcard2
  rw [card_klQuat, card_klQuat] at hAcard
  refine ⟨A, by omega, ?_⟩
  intro x hx
  obtain ⟨a, ha, b, hb, rfl⟩ := hA x hx
  obtain ⟨ha₁, ha₄⟩ := mem_klQuat.1 ha
  obtain ⟨hb₂, hb₄⟩ := mem_klQuat.1 hb
  exact ⟨a, ha₁, b, hb₂, ha₄, hb₄, rfl⟩

theorem kl_exists_noncomm {I : Subgroup Y} (e : ↥I ≃* SL(2, ZMod 3)) :
    ∃ a ∈ I, ∃ b ∈ I, a ^ 4 = 1 ∧ b ^ 4 = 1 ∧ a * b ≠ b * a := by
  obtain ⟨i, j, hi, hj, hij⟩ := kl_noncomm_pair
  refine ⟨(e.symm i : Y), (e.symm i).2, (e.symm j : Y), (e.symm j).2, ?_, ?_, ?_⟩
  · rw [← Subgroup.coe_pow, ← map_pow, hi, map_one]
    rfl
  · rw [← Subgroup.coe_pow, ← map_pow, hj, map_one]
    rfl
  · intro h
    apply hij
    have h1 : e.symm i * e.symm j = e.symm j * e.symm i := Subtype.ext h
    have h2 := congrArg e h1
    simpa using h2

end Quat

section Core

variable {Y : Type} [Group Y]

theorem kl_core {I : Subgroup Y} (e : ↥I ≃* SL(2, ZMod 3)) {A : Subgroup Y}
    (hA : A.Normal) {u : Y} (hu : u ∈ A) {G : GL (Fin 2) (ZMod 3)}
    (hact : ∀ c : ↥I, ∃ c' : ↥I, (c' : Y) = u * (c : Y) * u⁻¹ ∧ e c' = conjSLAut G (e c))
    (hmove : ∃ C : SL(2, ZMod 3), conjSLAut G C ≠ C ∧ conjSLAut G C ≠ -1 * C) :
    ∀ a ∈ I, a ^ 4 = 1 → a ∈ A := by
  obtain ⟨C, hC1, hC2⟩ := hmove
  obtain ⟨c', hc'Y, hc'e⟩ := hact (e.symm C)
  rw [MulEquiv.apply_symm_apply] at hc'e
  have hNn : ((A.comap I.subtype).map e.toMonoidHom).Normal :=
    (hA.comap I.subtype).map e.toMonoidHom e.surjective
  have hxN : conjSLAut G C * C⁻¹ ∈ (A.comap I.subtype).map e.toMonoidHom := by
    refine ⟨c' * (e.symm C)⁻¹, ?_, ?_⟩
    · show ((c' * (e.symm C)⁻¹ : ↥I) : Y) ∈ A
      have h1 : ((c' * (e.symm C)⁻¹ : ↥I) : Y) =
          u * (((e.symm C : ↥I) : Y) * u⁻¹ * ((e.symm C : ↥I) : Y)⁻¹) := by
        rw [Subgroup.coe_mul, InvMemClass.coe_inv, hc'Y]
        group
      rw [h1]
      exact A.mul_mem hu (hA.conj_mem _ (A.inv_mem hu) _)
    · show e (c' * (e.symm C)⁻¹) = conjSLAut G C * C⁻¹
      rw [map_mul, map_inv, hc'e, MulEquiv.apply_symm_apply]
  have hx1 : conjSLAut G C * C⁻¹ ≠ 1 := fun h => hC1 (mul_inv_eq_one.1 h)
  have hx2 : conjSLAut G C * C⁻¹ ≠ -1 := fun h => hC2 (mul_inv_eq_iff_eq_mul.1 h)
  intro a ha ha4
  have hy : (e ⟨a, ha⟩) ^ 4 = 1 := by
    rw [← map_pow]
    have : (⟨a, ha⟩ : ↥I) ^ 4 = 1 := Subtype.ext (by rw [Subgroup.coe_pow]; exact ha4)
    rw [this, map_one]
  obtain ⟨w, hw, hwe⟩ := kl_sl3_normal hNn hxN hx1 hx2 hy
  have : w = ⟨a, ha⟩ := e.injective hwe
  rw [this] at hw
  exact hw

end Core

section Cases

variable {Y : Type} [Group Y]

theorem Shape.eq_one_or_z_of_sq {F₁ F₂ : Type} [Field F₁] [Field F₂] (S : Shape Y F₁ F₂)
    (hF : ∀ x : SL(2, F₁), x * x = 1 → x = 1 ∨ x = -1) {a : Y} (ha : a ∈ S.I₁) (h : a * a = 1) :
    a = 1 ∨ a = S.z := by
  have h1 : S.e₁ ⟨a, ha⟩ * S.e₁ ⟨a, ha⟩ = 1 := by
    rw [← map_mul, ← map_one S.e₁]
    exact congrArg S.e₁ (Subtype.ext h)
  rcases hF _ h1 with h2 | h2
  · left
    have : (⟨a, ha⟩ : ↥S.I₁) = 1 := S.e₁.injective (h2.trans (map_one _).symm)
    exact congrArg Subtype.val this
  · right
    have : (⟨a, ha⟩ : ↥S.I₁) = ⟨S.z, S.z_mem₁⟩ := S.e₁.injective (h2.trans S.e₁_z.symm)
    exact congrArg Subtype.val this

variable (S : Shape Y (ZMod 3) (ZMod 3))

theorem Shape.kl_case₁ {A : Subgroup Y} (hA : A.Normal) {a b : Y} (ha : a ∈ S.I₁) (hb : b ∈ S.I₂)
    (hu : a * b ∈ A) (hu2 : (a * b) * (a * b) = 1) (hu1 : a * b ≠ 1) (huz : a * b ≠ S.z) :
    ∀ x ∈ S.I₁, x ^ 4 = 1 → x ∈ A := by
  have hba : b * a = a * b := (S.comm a ha b hb).symm
  have haa : (a * a) * (b * b) = 1 := by
    calc a * a * (b * b) = a * (a * b) * b := by group
      _ = a * (b * a) * b := by rw [hba]
      _ = a * b * (a * b) := by group
      _ = 1 := hu2
  have key : a * a = 1 → False := by
    intro haa1
    have hbb : b * b = 1 := by rw [haa1, one_mul] at haa; exact haa
    rcases S.eq_one_or_z_of_sq kl_sl3_sq_one ha haa1 with rfl | rfl
    · rcases S.swap.eq_one_or_z_of_sq kl_sl3_sq_one hb hbb with rfl | rfl
      · exact hu1 (mul_one 1)
      · exact huz (one_mul _)
    · rcases S.swap.eq_one_or_z_of_sq kl_sl3_sq_one hb hbb with rfl | rfl
      · exact huz (mul_one _)
      · exact hu1 S.z_sq
  have hane : S.e₁ ⟨a, ha⟩ ≠ 1 ∧ S.e₁ ⟨a, ha⟩ ≠ -1 := by
    constructor
    · intro h
      apply key
      have : (⟨a, ha⟩ : ↥S.I₁) = 1 := S.e₁.injective (h.trans (map_one _).symm)
      have ha1 : a = 1 := congrArg Subtype.val this
      rw [ha1, one_mul]
    · intro h
      apply key
      have : (⟨a, ha⟩ : ↥S.I₁) = ⟨S.z, S.z_mem₁⟩ := S.e₁.injective (h.trans S.e₁_z.symm)
      have haz : a = S.z := congrArg Subtype.val this
      rw [haz]
      exact S.z_sq
  refine kl_core S.e₁ hA hu (G := Matrix.SpecialLinearGroup.toGL (S.e₁ ⟨a, ha⟩)) ?_
    (kl_move_toGL hane.1 hane.2)
  intro c
  refine ⟨⟨a, ha⟩ * c * ⟨a, ha⟩⁻¹, ?_, ?_⟩
  · have hbc : b * (c : Y) = (c : Y) * b := (S.comm c c.2 b hb).symm
    show a * (c : Y) * a⁻¹ = a * b * (c : Y) * (a * b)⁻¹
    calc a * (c : Y) * a⁻¹ = a * (c * b) * b⁻¹ * a⁻¹ := by group
      _ = a * (b * c) * b⁻¹ * a⁻¹ := by rw [hbc]
      _ = a * b * (c : Y) * (a * b)⁻¹ := by group
  · rw [map_mul, map_mul, map_inv, conjSLAut_toGL]

theorem Shape.kl_case₂ {A : Subgroup Y} (hA : A.Normal) {a b : Y} (ha : a ∈ S.I₁) (hb : b ∈ S.I₂)
    (hu : a * b * S.t ∈ A) : ∀ x ∈ S.I₁, x ^ 4 = 1 → x ∈ A := by
  refine kl_core S.e₁ hA hu (G := Matrix.SpecialLinearGroup.toGL (S.e₁ ⟨a, ha⟩) * S.g₁) ?_ ?_
  · intro c
    obtain ⟨y, hyY, hye⟩ := conjData_iff.mp S.act₁ c
    refine ⟨⟨a, ha⟩ * y * ⟨a, ha⟩⁻¹, ?_, ?_⟩
    · have hby : b * (y : Y) = (y : Y) * b := (S.comm y y.2 b hb).symm
      rw [hyY] at hby
      show a * (y : Y) * a⁻¹ = a * b * S.t * (c : Y) * (a * b * S.t)⁻¹
      rw [hyY]
      calc a * (S.t * (c : Y) * S.t⁻¹) * a⁻¹ = a * ((S.t * (c : Y) * S.t⁻¹) * b) * b⁻¹ * a⁻¹ := by group
        _ = a * (b * (S.t * (c : Y) * S.t⁻¹)) * b⁻¹ * a⁻¹ := by rw [hby]
        _ = a * b * S.t * (c : Y) * (a * b * S.t)⁻¹ := by group
    · rw [map_mul, map_mul, map_inv, hye, conjSLAut_mul, conjSLAut_toGL]
  · apply kl_move_outer
    have hdet : ((Matrix.GeneralLinearGroup.det
        (Matrix.SpecialLinearGroup.toGL (S.e₁ ⟨a, ha⟩) * S.g₁) : (ZMod 3)ˣ) : ZMod 3) =
        ((Matrix.GeneralLinearGroup.det S.g₁ : (ZMod 3)ˣ) : ZMod 3) := by
      rw [map_mul, Units.val_mul, det_toGL, one_mul]
    rw [hdet]
    exact S.ns₁

theorem Shape.kl₁ {A : Subgroup Y} (hA : A.Normal) {u : Y} (hu : u ∈ A) (hu2 : u * u = 1) (hu1 : u ≠ 1)
    (huz : u ≠ S.z) : ∀ x ∈ S.I₁, x ^ 4 = 1 → x ∈ A := by
  have := S.normal₁
  have := S.normal₂
  have hutop : u ∈ (S.I₁ ⊔ S.I₂) ⊔ Subgroup.zpowers S.t := by
    rw [S.gen]
    exact Subgroup.mem_top u
  obtain ⟨n, hn, k, hk, hnk⟩ := Subgroup.mem_sup_of_normal_left.1 hutop
  obtain ⟨a, ha, b, hb, rfl⟩ := mem_sup_of_commute S.comm hn
  rcases mem_zpowers_of_sq S.t_sq hk with rfl | rfl
  · rw [mul_one] at hnk
    subst hnk
    exact S.kl_case₁ hA ha hb hu hu2 hu1 huz
  · subst hnk
    exact S.kl_case₂ hA ha hb hu

end Cases

theorem kl_nonempty_ringEquiv {F : Type} [Field F] (h : Nat.card F = 3) : Nonempty (F ≃+* ZMod 3) := by
  have hfin : Finite F := Nat.finite_of_card_ne_zero (by rw [h]; decide)
  have : Fintype F := Fintype.ofFinite F
  have hc : Fintype.card F = Fintype.card (ZMod 3) := by
    rw [← Nat.card_eq_fintype_card, h, ZMod.card]
  exact ⟨FiniteField.ringEquivOfCardEq hc⟩

section Main

variable {Y : Type} [Group Y] {F₁ F₂ : Type} [Field F₁] [Field F₂]

theorem Shape.kl (S : Shape Y F₁ F₂) (h₁ : Nat.card F₁ = 3) (h₂ : Nat.card F₂ = 3)
    {A : Subgroup Y} (hA : A.Normal) {u : Y} (hu : u ∈ A) (hu2 : u * u = 1) (hu1 : u ≠ 1)
    (huz : u ≠ S.z) :
    (∀ a ∈ S.I₁, a ^ 4 = 1 → a ∈ A) ∧ (∀ b ∈ S.I₂, b ^ 4 = 1 → b ∈ A) := by
  obtain ⟨σ₁⟩ := kl_nonempty_ringEquiv h₁
  obtain ⟨σ₂⟩ := kl_nonempty_ringEquiv h₂
  let T : Shape Y (ZMod 3) (ZMod 3) := ((S.mapField₁ σ₁).swap.mapField₁ σ₂).swap
  exact ⟨T.kl₁ hA hu hu2 hu1 huz, T.swap.kl₁ hA hu hu2 hu1 huz⟩

theorem Shape.exists_noncomm₁ (S : Shape Y F₁ F₂) (h₁ : Nat.card F₁ = 3) :
    ∃ a ∈ S.I₁, ∃ b ∈ S.I₁, a ^ 4 = 1 ∧ b ^ 4 = 1 ∧ a * b ≠ b * a := by
  obtain ⟨σ₁⟩ := kl_nonempty_ringEquiv h₁
  exact kl_exists_noncomm (S.mapField₁ σ₁).e₁

theorem Shape.exists_Q32 (S : Shape Y F₁ F₂) (h₁ : Nat.card F₁ = 3) (h₂ : Nat.card F₂ = 3) :
    ∃ R : Subgroup Y, Nat.card R = 32 ∧
      ∀ x ∈ R, ∃ a ∈ S.I₁, ∃ b ∈ S.I₂, a ^ 4 = 1 ∧ b ^ 4 = 1 ∧ x = a * b := by
  obtain ⟨σ₁⟩ := kl_nonempty_ringEquiv h₁
  obtain ⟨σ₂⟩ := kl_nonempty_ringEquiv h₂
  exact kl_Q32 (S.mapField₁ σ₁).e₁ (S.swap.mapField₁ σ₂).e₁ S.comm S.inter S.z_sq S.z_ne

theorem Shape.sq_one_mem_sup (S : Shape Y F₁ F₂) {x : Y} (hx : x ∈ S.I₁ ⊔ S.I₂) (hx2 : x * x = 1) :
    ∃ a ∈ S.I₁, ∃ b ∈ S.I₂, a ^ 4 = 1 ∧ b ^ 4 = 1 ∧ x = a * b := by
  obtain ⟨a, ha, b, hb, rfl⟩ := mem_sup_of_commute S.comm hx
  have hba : b * a = a * b := (S.comm a ha b hb).symm
  have h1 : a * a * (b * b) = 1 := by
    calc a * a * (b * b) = a * (a * b) * b := by group
      _ = a * (b * a) * b := by rw [hba]
      _ = a * b * (a * b) := by group
      _ = 1 := hx2
  have h2 : a * a = (b * b)⁻¹ := eq_inv_of_mul_eq_one_left h1
  have h3 : b * b = (a * a)⁻¹ := eq_inv_of_mul_eq_one_right h1
  have hmem : a * a ∈ Subgroup.zpowers S.z := by
    rw [← S.inter]
    exact ⟨S.I₁.mul_mem ha ha, by rw [h2]; exact S.I₂.inv_mem (S.I₂.mul_mem hb hb)⟩
  have ha4 : a ^ 4 = 1 := by
    rw [kl_pow_four]
    rcases mem_zpowers_of_sq S.z_sq hmem with h | h
    · rw [h, one_mul]
    · rw [h]
      exact S.z_sq
  refine ⟨a, ha, b, hb, ha4, ?_, rfl⟩
  rw [kl_pow_four, h3, ← mul_inv_rev, ← kl_pow_four, ha4, inv_one]

end Main

end CFSG.GH74.GLS.IVK.Proofs2.Ivk47ab
