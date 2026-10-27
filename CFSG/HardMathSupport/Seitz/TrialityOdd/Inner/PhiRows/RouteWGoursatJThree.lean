module

public import CFSG.HardMathSupport.Seitz.TrialityOdd.Inner.PhiRows.RouteWGoursatJ
public import CFSG.HardMathSupport.Seitz.TrialityOdd.Proving.SubfieldMaximalThree

set_option linter.unusedSectionVars false

public section

open scoped MatrixGroups

namespace CFSG.HardMathSupport.Seitz.TrialityOdd.Inner.GoursatJ

section Three


def slMapEquiv {F L : Type} [Field F] [Field L] (e : F ≃+* L) : SL(2, F) ≃* SL(2, L) where
  toFun := Matrix.SpecialLinearGroup.map (n := Fin 2) (e : F →+* L)
  invFun := Matrix.SpecialLinearGroup.map (n := Fin 2) (e.symm : L →+* F)
  left_inv x := by
    apply Subtype.ext
    ext i j
    simp
  right_inv x := by
    apply Subtype.ext
    ext i j
    simp
  map_mul' := map_mul _

theorem slMapEquiv_neg_one {F L : Type} [Field F] [Field L] (e : F ≃+* L) :
    slMapEquiv e (-1) = -1 := by
  show Matrix.SpecialLinearGroup.map (n := Fin 2) (e : F →+* L) (-1) = -1
  apply Subtype.ext
  ext i j
  simp only [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, Matrix.map_apply,
    Matrix.SpecialLinearGroup.coe_neg, Matrix.SpecialLinearGroup.coe_one, Matrix.neg_apply]
  fin_cases i <;> fin_cases j <;> simp


theorem sl2_eq_one_or_neg_one_of_mul_self_three {F : Type} [Field F] (h2 : (2 : F) ≠ 0) {A : SL(2, F)} (hA : A * A = 1) :
    A = 1 ∨ A = -1 := by
  have hdet := A.2
  rw [Matrix.det_fin_two] at hdet
  have hA' := congrArg (fun X : SL(2, F) => (X : Matrix (Fin 2) (Fin 2) F)) hA
  simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one] at hA'
  have e00 : (A : Matrix (Fin 2) (Fin 2) F) 0 0 * (A : Matrix (Fin 2) (Fin 2) F) 0 0 +
      (A : Matrix (Fin 2) (Fin 2) F) 0 1 * (A : Matrix (Fin 2) (Fin 2) F) 1 0 = 1 := by
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using congrFun (congrFun hA' 0) 0
  have e01 : (A : Matrix (Fin 2) (Fin 2) F) 0 0 * (A : Matrix (Fin 2) (Fin 2) F) 0 1 +
      (A : Matrix (Fin 2) (Fin 2) F) 0 1 * (A : Matrix (Fin 2) (Fin 2) F) 1 1 = 0 := by
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using congrFun (congrFun hA' 0) 1
  have e10 : (A : Matrix (Fin 2) (Fin 2) F) 1 0 * (A : Matrix (Fin 2) (Fin 2) F) 0 0 +
      (A : Matrix (Fin 2) (Fin 2) F) 1 1 * (A : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := by
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using congrFun (congrFun hA' 1) 0
  have e11 : (A : Matrix (Fin 2) (Fin 2) F) 1 0 * (A : Matrix (Fin 2) (Fin 2) F) 0 1 +
      (A : Matrix (Fin 2) (Fin 2) F) 1 1 * (A : Matrix (Fin 2) (Fin 2) F) 1 1 = 1 := by
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using congrFun (congrFun hA' 1) 1
  set a := (A : Matrix (Fin 2) (Fin 2) F) 0 0
  set b := (A : Matrix (Fin 2) (Fin 2) F) 0 1
  set c := (A : Matrix (Fin 2) (Fin 2) F) 1 0
  set d := (A : Matrix (Fin 2) (Fin 2) F) 1 1
  by_cases hs : a + d = 0
  · exfalso
    have hd : d = -a := by linear_combination hs
    rw [hd] at e11 hdet
    apply h2
    linear_combination (-1 : F) * e00 - hdet
  · have hb : b = 0 := by
      have : b * (a + d) = 0 := by linear_combination e01
      exact (mul_eq_zero.1 this).resolve_right hs
    have hc : c = 0 := by
      have : c * (a + d) = 0 := by linear_combination e10
      exact (mul_eq_zero.1 this).resolve_right hs
    rw [hb, hc] at e00 e11 hdet
    have ha : a * a = 1 := by linear_combination e00
    have hd2 : d * d = 1 := by linear_combination e11
    rcases mul_self_eq_one_iff.1 ha with h | h
    · have hd1 : d = 1 := by
        rcases mul_self_eq_one_iff.1 hd2 with h' | h'
        · exact h'
        · exfalso; rw [h, h'] at hdet; apply h2; linear_combination -hdet
      left
      apply Subtype.ext
      ext i j
      fin_cases i <;> fin_cases j <;> simp [a, b, c, d, h, hd1, hb, hc]
    · have hd1 : d = -1 := by
        rcases mul_self_eq_one_iff.1 hd2 with h' | h'
        · exfalso; rw [h, h'] at hdet; apply h2; linear_combination -hdet
        · exact h'
      right
      apply Subtype.ext
      ext i j
      fin_cases i <;> fin_cases j <;> simp [a, b, c, d, h, hd1, hb, hc, Matrix.SpecialLinearGroup.coe_neg]

theorem slMapEquiv_neg {F L : Type} [Field F] [Field L] (e : F ≃+* L) (a : SL(2, F)) :
    slMapEquiv e (-a) = -slMapEquiv e a := by
  rw [neg_eq_neg_one_mul, map_mul, slMapEquiv_neg_one, ← neg_eq_neg_one_mul]

theorem sl2z3_comm : ∀ g : SL(2, ZMod 3), g ≠ 1 → g ≠ -1 →
    ∃ h : SL(2, ZMod 3), (g * h * g⁻¹ * h⁻¹) * (g * h * g⁻¹ * h⁻¹) = -1 := by
  decide +kernel

theorem sl2z3_conj : ∀ i : SL(2, ZMod 3), i * i = -1 →
    ∃ h : SL(2, ZMod 3), h * i * h⁻¹ ≠ i ∧ h * i * h⁻¹ ≠ -i := by
  decide +kernel

variable {F : Type} [Field F] [Finite F]

theorem sl2_three_comm (hF : Nat.card F = 3) : ∀ g : SL(2, F), g ≠ 1 → g ≠ -1 →
    ∃ h : SL(2, F), (g * h * g⁻¹ * h⁻¹) * (g * h * g⁻¹ * h⁻¹) = -1 := by
  classical
  have := Fintype.ofFinite F
  have hc : Fintype.card F = 3 := by rw [← Nat.card_eq_fintype_card]; exact hF
  let e : F ≃+* ZMod 3 := (ZMod.ringEquivOfPrime F Nat.prime_three hc).symm
  let E := slMapEquiv e
  intro g hg1 hg2
  have hE1 : E (-1) = -1 := slMapEquiv_neg_one e
  have h1 : E g ≠ 1 := fun h => hg1 (E.injective (by rw [h, map_one]))
  have h2 : E g ≠ -1 := fun h => hg2 (E.injective (by rw [h, hE1]))
  obtain ⟨h, hh⟩ := sl2z3_comm (E g) h1 h2
  refine ⟨E.symm h, E.injective ?_⟩
  simp only [map_mul, map_inv, MulEquiv.apply_symm_apply, hE1]
  exact hh

theorem sl2_three_conj (hF : Nat.card F = 3) : ∀ i : SL(2, F), i * i = -1 →
    ∃ h : SL(2, F), h * i * h⁻¹ ≠ i ∧ h * i * h⁻¹ ≠ -i := by
  classical
  have := Fintype.ofFinite F
  have hc : Fintype.card F = 3 := by rw [← Nat.card_eq_fintype_card]; exact hF
  let e : F ≃+* ZMod 3 := (ZMod.ringEquivOfPrime F Nat.prime_three hc).symm
  let E := slMapEquiv e
  intro i hi
  have hEi : E i * E i = -1 := by rw [← map_mul, hi]; exact slMapEquiv_neg_one e
  obtain ⟨h, hh1, hh2⟩ := sl2z3_conj (E i) hEi
  refine ⟨E.symm h, fun h1 => hh1 ?_, fun h2 => hh2 ?_⟩
  · have := congrArg E h1
    rwa [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply] at this
  · have := congrArg E h2
    rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply] at this
    exact this.trans (slMapEquiv_neg e i)

theorem neg_one_conj_three {R : Type} [Field R] (g : SL(2, R)) : g * (-1) * g⁻¹ = -1 := by
  have hz : (-1 : SL(2, R)) ∈ Subgroup.center SL(2, R) := by
    rw [Matrix.SpecialLinearGroup.mem_center_iff]
    refine ⟨-1, by simp, ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.SpecialLinearGroup.coe_neg, Matrix.scalar_apply]
  have := Subgroup.mem_center_iff.1 hz g
  rw [this]
  group

theorem psl2_three_vanish {G : Type*} [Group G] (hF : Nat.card F = 3) (h2 : ringChar F ≠ 2)
    (ψ : SL(2, F) →* G) (hψ : ∀ g, ψ g = 1 ↔ g = 1 ∨ g = -1) (Z : Subgroup G)
    (hnorm : ∀ x a, a ∈ Z → ψ x * a * (ψ x)⁻¹ ∈ Z) (z0 : G)
    (hinv : ∀ a ∈ Z, a * a = 1 → a = 1 ∨ a = z0) (x : SL(2, F)) (hx : ψ x ∈ Z) : ψ x = 1 := by
  by_contra hne
  have hn1 : (-1 : SL(2, F)) ≠ 1 := neg_one_ne_one' h2
  have hψneg : ψ (-1) = 1 := (hψ _).2 (Or.inr rfl)
  have hx1 : x ≠ 1 := fun h => hne (by rw [h, map_one])
  have hx2 : x ≠ -1 := fun h => hne (by rw [h, hψneg])
  obtain ⟨h, hh⟩ := sl2_three_comm hF x hx1 hx2
  set c := x * h * x⁻¹ * h⁻¹ with hc
  have hcZ : ψ c ∈ Z := by
    have e : ψ c = ψ x * (ψ h * (ψ x)⁻¹ * (ψ h)⁻¹) := by
      simp only [hc, map_mul, map_inv, mul_assoc]
    rw [e]
    exact Z.mul_mem hx (hnorm h _ (Z.inv_mem hx))
  have hcc : ψ c * ψ c = 1 := by rw [← map_mul, hh, hψneg]
  have hc1 : c ≠ 1 := fun h' => by
    rw [h', mul_one] at hh
    exact hn1 hh.symm
  have hc2 : c ≠ -1 := fun h' => by
    rw [h', ] at hh
    have : (-1 : SL(2, F)) * -1 = 1 := neg_one_mul_neg_one'
    rw [this] at hh
    exact hn1 hh.symm
  have hψc : ψ c = ψ c := rfl
  have hzc : ψ c = z0 := by
    rcases hinv _ hcZ hcc with h' | h'
    · exact absurd ((hψ c).1 h') (by tauto)
    · exact h'
  obtain ⟨h', hj1, hj2⟩ := sl2_three_conj hF c hh
  set j := h' * c * h'⁻¹ with hj
  have hjZ : ψ j ∈ Z := by
    have e : ψ j = ψ h' * ψ c * (ψ h')⁻¹ := by simp only [hj, map_mul, map_inv]
    rw [e]; exact hnorm h' _ hcZ
  have hjj : j * j = -1 := by
    have : j * j = h' * (c * c) * h'⁻¹ := by simp only [hj]; group
    rw [this, hh]
    exact neg_one_conj_three h'
  have hψjj : ψ j * ψ j = 1 := by rw [← map_mul, hjj, hψneg]
  have hjne1 : j ≠ 1 := fun h'' => by
    rw [h'', mul_one] at hjj
    exact hn1 hjj.symm
  have hjne2 : j ≠ -1 := fun h'' => by
    rw [h''] at hjj
    have : (-1 : SL(2, F)) * -1 = 1 := neg_one_mul_neg_one'
    rw [this] at hjj
    exact hn1 hjj.symm
  have hzj : ψ j = z0 := by
    rcases hinv _ hjZ hψjj with h'' | h''
    · exact absurd ((hψ j).1 h'') (by tauto)
    · exact h''
  have hker : ψ (j * c⁻¹) = 1 := by rw [map_mul, map_inv, hzj, hzc, mul_inv_cancel]
  rcases (hψ _).1 hker with h3 | h3
  · apply hj1
    have : j = c := by
      have := congrArg (· * c) h3
      simpa using this
    rw [hj] at this
    exact this
  · apply hj2
    have : j = -c := by
      rw [neg_eq_neg_one_mul, ← h3]
      group
    rw [hj] at this
    exact this

end Three

section Main

open Subgroup CFSG.HardMathSupport.Seitz.TrialityOdd.Proving

variable {G : Type*} [Group G] {F K : Type} [Field F] [Field K] [Algebra F K] [Finite F] [Finite K]

theorem goursatJThree
    (h3 : Module.finrank F K = 3) (hK : ringChar K ≠ 2) (hF : Nat.card F = 3)
    (ιA : SL(2, F) →* G) (ιB : SL(2, K) →* G)
    (hA : Function.Injective ιA) (hB : Function.Injective ιB)
    (hc : ∀ a b, ιA a * ιB b = ιB b * ιA a) (hz : ιA (-1) = ιB (-1))
    (J : Subgroup G) (hJA : ∀ a, ιA a ∈ J) (hJB : ∀ b, ιB b ∈ J ↔ b ∈ sl2Range F K)
    (ψ : SL(2, F) →* G) (hψ : ∀ g, ψ g = 1 ↔ g = 1 ∨ g = -1) (D : Subgroup G)
    (hDψ : ψ.range = D)
    (hDc : 2 * Nat.card D = Nat.card SL(2, F))
    (hDM : D ≤ ιA.range ⊔ ιB.range) (hDJ : D ≤ J)
    (ν : G) (hν : ν ∈ ιA.range ⊔ ιB.range) :
    ν ∈ J ∨ ιB.range ≤ (D ⊔ D.map (MulAut.conj ν).toMonoidHom) ⊔ ιA.range := by
  classical
  have hF2 : ringChar F ≠ 2 := ringChar_ne_two_of_algebra hK
  have hcomm : ∀ a ∈ ιA.range, ∀ b ∈ ιB.range, a * b = b * a := by
    rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
    exact hc a b
  let Φ : SL(2, F) × SL(2, K) →* G := ιA.noncommCoprod ιB (fun a b => hc a b)
  have hΦ : ∀ a b, Φ (a, b) = ιA a * ιB b := fun a b => rfl
  have hzz : ιA (-1) * ιA (-1) = 1 := by rw [← map_mul, neg_one_mul_neg_one', map_one]
  set Dt : Subgroup (SL(2, F) × SL(2, K)) := D.comap Φ with hDt
  have hDtJ : ∀ p ∈ Dt, p.2 ∈ sl2Range F K := by
    rintro ⟨a, b⟩ hp
    have h1 : ιA a * ιB b ∈ J := hDJ hp
    have h2 : ιB b ∈ J := by
      have := J.mul_mem (J.inv_mem (hJA a)) h1
      simpa [mul_assoc] using this
    exact (hJB b).1 h2
  have hψD : ∀ x, ψ x ∈ D := fun x => hDψ ▸ ⟨x, rfl⟩
  have hMn : ∀ m ∈ ιA.range ⊔ ιB.range, ∀ a ∈ ιA.range, m * a * m⁻¹ ∈ ιA.range := by
    intro m hm a ha
    obtain ⟨p, hp, q, hq, rfl⟩ := mem_sup_eq_mul_of_comm ιA.range ιB.range hcomm m hm
    have hqa : q * a = a * q := (hcomm a ha q hq).symm
    have : p * q * a * (p * q)⁻¹ = p * a * p⁻¹ := by
      calc p * q * a * (p * q)⁻¹ = p * (q * a) * q⁻¹ * p⁻¹ := by group
        _ = p * (a * q) * q⁻¹ * p⁻¹ := by rw [hqa]
        _ = p * a * p⁻¹ := by group
    rw [this]
    exact ιA.range.mul_mem (ιA.range.mul_mem hp ha) (ιA.range.inv_mem hp)
  have hMnB : ∀ m ∈ ιA.range ⊔ ιB.range, ∀ b ∈ ιB.range, m * b * m⁻¹ ∈ ιB.range := by
    intro m hm b hb
    obtain ⟨p, hp, q, hq, rfl⟩ := mem_sup_eq_mul_of_comm ιA.range ιB.range hcomm m hm
    have hqb : q * b * q⁻¹ ∈ ιB.range :=
      ιB.range.mul_mem (ιB.range.mul_mem hq hb) (ιB.range.inv_mem hq)
    have hpq : p * (q * b * q⁻¹) = (q * b * q⁻¹) * p := hcomm p hp _ hqb
    have : p * q * b * (p * q)⁻¹ = q * b * q⁻¹ := by
      calc p * q * b * (p * q)⁻¹ = p * (q * b * q⁻¹) * p⁻¹ := by group
        _ = (q * b * q⁻¹) * p * p⁻¹ := by rw [hpq]
        _ = q * b * q⁻¹ := by group
    rw [this]
    exact hqb
  have hDB : D ⊓ ιB.range = ⊥ := by
    rw [eq_bot_iff]
    rintro d ⟨hd, hdB⟩
    rw [← hDψ] at hd
    obtain ⟨x, rfl⟩ := hd
    have hinv : ∀ a ∈ ιB.range, a * a = 1 → a = 1 ∨ a = ιB (-1) := by
      rintro _ ⟨b, rfl⟩ h
      have : b * b = 1 := hB (by rw [map_mul, h, map_one])
      rcases sl2_eq_one_or_neg_one_of_mul_self_three (Ring.two_ne_zero hK) this with rfl | rfl
      · left; exact map_one _
      · right; rfl
    exact Subgroup.mem_bot.2 (psl2_three_vanish hF hF2 ψ hψ ιB.range
      (fun y a ha => hMnB _ (hDM (hψD y)) a ha) (ιB (-1)) hinv x hdB)
  have hDA : D ⊓ ιA.range = ⊥ := by
    rw [eq_bot_iff]
    rintro d ⟨hd, hdA⟩
    rw [← hDψ] at hd
    obtain ⟨x, rfl⟩ := hd
    have hinv : ∀ a ∈ ιA.range, a * a = 1 → a = 1 ∨ a = ιA (-1) := by
      rintro _ ⟨b, rfl⟩ h
      have : b * b = 1 := hA (by rw [map_mul, h, map_one])
      rcases sl2_eq_one_or_neg_one_of_mul_self_three (Ring.two_ne_zero hF2) this with rfl | rfl
      · left; exact map_one _
      · right; rfl
    exact Subgroup.mem_bot.2 (psl2_three_vanish hF hF2 ψ hψ ιA.range
      (fun y a ha => hMn _ (hDM (hψD y)) a ha) (ιA (-1)) hinv x hdA)
  have hε : ((-1 : SL(2, F)), (-1 : SL(2, K))) ∈ Dt := by
    show Φ _ ∈ D
    rw [hΦ, ← hz, hzz]
    exact D.one_mem
  have hdec := mem_sup_eq_mul_of_comm ιA.range ιB.range hcomm
  let f : Dt →* G := Φ.comp Dt.subtype
  have hfr : f.range = D := by
    refine le_antisymm ?_ ?_
    · rintro _ ⟨x, rfl⟩
      exact x.2
    · intro d hd
      obtain ⟨_, ⟨a, rfl⟩, _, ⟨b, rfl⟩, rfl⟩ := hdec d (hDM hd)
      exact ⟨⟨(a, b), hd⟩, rfl⟩
  have hker : 1 < Nat.card f.ker := by
    rw [Subgroup.one_lt_card_iff_ne_bot]
    intro hbot
    have hmem : (⟨_, hε⟩ : Dt) ∈ f.ker := by
      show Φ ((-1 : SL(2, F)), (-1 : SL(2, K))) = 1
      rw [hΦ, ← hz, hzz]
    rw [hbot, Subgroup.mem_bot] at hmem
    have := congrArg (fun x : Dt => (x : SL(2, F) × SL(2, K)).1) hmem
    exact neg_one_ne_one' (R := F) (ringChar_ne_two_of_algebra hK) this
  have hDtcard : Nat.card SL(2, F) ≤ Nat.card Dt := by
    have h := Subgroup.card_ker_mul_card_range f
    rw [hfr] at h
    have : 2 * Nat.card D ≤ Nat.card f.ker * Nat.card D :=
      Nat.mul_le_mul_right _ hker
    omega
  let pr1 : Dt →* SL(2, F) := (MonoidHom.fst _ _).comp Dt.subtype
  let pr2 : Dt →* SL(2, K) := (MonoidHom.snd _ _).comp Dt.subtype
  have hpr1 : Function.Injective pr1 := by
    rw [injective_iff_map_eq_one]
    rintro ⟨⟨a, b⟩, hx⟩ h
    have ha : a = 1 := h
    subst ha
    have hbD : ιB b ∈ D := by
      have : Φ (1, b) ∈ D := hx
      simpa [hΦ] using this
    have hmem : ιB b ∈ D ⊓ ιB.range := ⟨hbD, b, rfl⟩
    rw [hDB, Subgroup.mem_bot] at hmem
    have hb : b = 1 := hB (by rw [hmem, map_one])
    subst hb
    rfl
  have hpr2 : Function.Injective pr2 := by
    rw [injective_iff_map_eq_one]
    rintro ⟨⟨a, b⟩, hx⟩ h
    have hb : b = 1 := h
    subst hb
    have haD : ιA a ∈ D := by
      have : Φ (a, 1) ∈ D := hx
      simpa [hΦ] using this
    have hmem : ιA a ∈ D ⊓ ιA.range := ⟨haD, a, rfl⟩
    rw [hDA, Subgroup.mem_bot] at hmem
    have ha : a = 1 := hA (by rw [hmem, map_one])
    subst ha
    rfl
  have hcardr1 : Nat.card pr1.range = Nat.card Dt :=
    (Nat.card_congr (MonoidHom.ofInjective hpr1).toEquiv).symm
  have hcardr2 : Nat.card pr2.range = Nat.card Dt :=
    (Nat.card_congr (MonoidHom.ofInjective hpr2).toEquiv).symm
  have hr1 : pr1.range = ⊤ := by
    apply Subgroup.eq_top_of_card_eq
    have h1 : Nat.card pr1.range ≤ Nat.card SL(2, F) :=
      Nat.le_of_dvd Nat.card_pos (Subgroup.card_subgroup_dvd_card _)
    omega
  have hr2 : pr2.range = sl2Range F K := by
    refine Subgroup.eq_of_le_of_card_ge ?_ ?_
    · rintro _ ⟨x, rfl⟩
      exact hDtJ x.1 x.2
    · rw [sl2Range_card]
      omega
  have hsurjA : ∀ a : SL(2, F), ∃ b, ιA a * ιB b ∈ D := by
    intro a
    have : a ∈ pr1.range := by rw [hr1]; trivial
    obtain ⟨⟨⟨a', b⟩, hx⟩, h⟩ := this
    have ha : a' = a := h
    subst ha
    exact ⟨b, hx⟩
  have hsurjB : ∀ s ∈ sl2Range F K, ∃ a, ιA a * ιB s ∈ D := by
    intro s hs
    have : s ∈ pr2.range := by rw [hr2]; exact hs
    obtain ⟨⟨⟨a, b⟩, hx⟩, h⟩ := this
    have hb : b = s := h
    subst hb
    exact ⟨a, hx⟩
  obtain ⟨_, ⟨a₀, rfl⟩, _, ⟨b₀, rfl⟩, hνab⟩ := hdec ν hν
  by_cases hnorm : ∀ s ∈ sl2Range F K, b₀ * s * b₀⁻¹ ∈ sl2Range F K
  · left
    have hb₀ : b₀ ∈ sl2Range F K := by
      obtain ⟨y, hy, hyb⟩ := mem_SL2_of_normalizes_SL2 h3 (b₀ : Matrix (Fin 2) (Fin 2) K) b₀.2 (by
        intro x hx
        have hmem : Matrix.SpecialLinearGroup.map (n := Fin 2) (algebraMap F K)
            (⟨x, hx⟩ : SL(2, F)) ∈ sl2Range F K := ⟨_, rfl⟩
        obtain ⟨y, hy⟩ := hnorm _ hmem
        refine ⟨(y : Matrix (Fin 2) (Fin 2) F), y.2, ?_⟩
        have h1 : Matrix.SpecialLinearGroup.map (n := Fin 2) (algebraMap F K) y =
            b₀ * Matrix.SpecialLinearGroup.map (n := Fin 2) (algebraMap F K) ⟨x, hx⟩ * b₀⁻¹ := hy
        have h2 : Matrix.SpecialLinearGroup.map (n := Fin 2) (algebraMap F K) y * b₀ =
            b₀ * Matrix.SpecialLinearGroup.map (n := Fin 2) (algebraMap F K) ⟨x, hx⟩ := by
          rw [h1]; group
        have h3' := congrArg (fun z : SL(2, K) => (z : Matrix (Fin 2) (Fin 2) K)) h2
        simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.map_apply_coe]
          at h3'
        exact h3'.symm)
      refine ⟨(⟨y, hy⟩ : SL(2, F)), Subtype.ext ?_⟩
      exact hyb.symm
    rw [hνab]
    exact J.mul_mem (hJA a₀) ((hJB b₀).2 hb₀)
  · right
    push Not at hnorm
    obtain ⟨s, hs, hsn⟩ := hnorm
    set X : Subgroup G := D ⊔ D.map (MulAut.conj ν).toMonoidHom with hX
    have hνM : ν ∈ ιA.range ⊔ ιB.range := hν
    have hD''M : D.map (MulAut.conj ν).toMonoidHom ≤ ιA.range ⊔ ιB.range := by
      rintro _ ⟨d, hd, rfl⟩
      have := (ιA.range ⊔ ιB.range).mul_mem ((ιA.range ⊔ ιB.range).mul_mem hνM (hDM hd))
        ((ιA.range ⊔ ιB.range).inv_mem hνM)
      simpa [MulAut.conj_apply] using this
    have hXM : X ≤ ιA.range ⊔ ιB.range := sup_le hDM hD''M
    set Y : Subgroup SL(2, K) := (X.comap Φ).map (MonoidHom.snd _ _) with hY
    have hYmem : ∀ b : SL(2, K), b ∈ Y ↔ ∃ a, ιA a * ιB b ∈ X := by
      intro b
      constructor
      · rintro ⟨⟨a, b'⟩, hp, rfl⟩
        exact ⟨a, hp⟩
      · rintro ⟨a, ha⟩
        exact ⟨(a, b), ha, rfl⟩
    have hY0 : sl2Range F K ≤ Y := by
      intro b hb
      obtain ⟨a, ha⟩ := hsurjB b hb
      exact (hYmem b).2 ⟨a, (le_sup_left : D ≤ X) ha⟩
    have hj : b₀ * s * b₀⁻¹ ∈ Y := by
      obtain ⟨a, ha⟩ := hsurjB s hs
      refine (hYmem _).2 ⟨a₀ * a * a₀⁻¹, ?_⟩
      have hmem : ν * (ιA a * ιB s) * ν⁻¹ ∈ X :=
        (le_sup_right : D.map (MulAut.conj ν).toMonoidHom ≤ X) ⟨_, ha, by simp [MulAut.conj_apply]⟩
      have e : ν * (ιA a * ιB s) * ν⁻¹ = ιA (a₀ * a * a₀⁻¹) * ιB (b₀ * s * b₀⁻¹) := by
        have h1 : ν = Φ (a₀, b₀) := by rw [hνab]; rfl
        have h2 : ιA a * ιB s = Φ (a, s) := rfl
        rw [h1, h2, ← map_inv, ← map_mul, ← map_mul]
        show Φ _ = Φ (a₀ * a * a₀⁻¹, b₀ * s * b₀⁻¹)
        congr 1
      rwa [e] at hmem
    have hYtop : Y = ⊤ := Proving.sl2_range_maximal_three h3 hK hF Y hY0 hj hsn
    have hXA : X ⊔ ιA.range = ιA.range ⊔ ιB.range := by
      refine le_antisymm (sup_le hXM le_sup_left) (sup_le ?_ ?_)
      · exact le_sup_right
      · rintro _ ⟨b, rfl⟩
        have hb : b ∈ Y := by rw [hYtop]; trivial
        obtain ⟨a, ha⟩ := (hYmem b).1 hb
        have : ιB b = (ιA a)⁻¹ * (ιA a * ιB b) := by group
        rw [this]
        exact Subgroup.mul_mem _ (Subgroup.mem_sup_right ⟨a⁻¹, by simp⟩)
          (Subgroup.mem_sup_left ha)
    exact (le_sup_right : ιB.range ≤ ιA.range ⊔ ιB.range).trans hXA.ge

end Main

end CFSG.HardMathSupport.Seitz.TrialityOdd.Inner.GoursatJ
