module

public import CFSG.CGT.PushingUpLit.BHS.FourSymA
public import CFSG.CGT.PushingUpLit.BHS.LLemmaBasic
public import CFSG.Permutation.SymmetricCoxeter
public import CFSG.Timmesfeld.ARS.NaturalModule
public import Mathlib.FieldTheory.Finite.GaloisField
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card

public section

namespace CFSG.CGT.PushingUpLit.BHS

open CFSG.Quasithin CFSG.Quasithin.A1b CFSG.RankThree.PartOne

local macro "comm_group" : tactic =>
  `(tactic| (apply Additive.ofMul.injective
             simp only [ofMul_mul, ofMul_inv, ofMul_div, ofMul_one]
             abel))

variable {V : Type} [CommGroup V]

section Elements

variable {x y : MulAut V} {u w : V}

theorem pair_elements (hV : ∀ v : V, v ^ 2 = 1) (hx : IsTransv x u) (hy : IsTransv y w)
    (hxw : x w = w * u) (hyu : y u = u * w) :
    ∀ g ∈ Subgroup.zpowers x ⊔ Subgroup.zpowers y,
      g = 1 ∨ g = x ∨ g = y ∨ g = x * y ∨ g = y * x ∨ g = x * y * x := by
  have hb : x * y * x = y * x * y := hx.braid hV hy hxw hyu
  have hxx : x * x = 1 := hx.sq
  have hyy : y * y = 1 := hy.sq
  have hxinv : x⁻¹ = x := inv_eq_of_mul_eq_one_right hxx
  have hyinv : y⁻¹ = y := inv_eq_of_mul_eq_one_right hyy
  have hcl : Subgroup.zpowers x ⊔ Subgroup.zpowers y = Subgroup.closure {x, y} := by
    rw [Subgroup.zpowers_eq_closure, Subgroup.zpowers_eq_closure, ← Subgroup.closure_union,
      Set.singleton_union]
  intro g hg
  rw [hcl] at hg
  have hmulx : ∀ g : MulAut V, (g = 1 ∨ g = x ∨ g = y ∨ g = x * y ∨ g = y * x ∨ g = x * y * x) →
      (x * g = 1 ∨ x * g = x ∨ x * g = y ∨ x * g = x * y ∨ x * g = y * x ∨
        x * g = x * y * x) := by
    rintro g (rfl | rfl | rfl | rfl | rfl | rfl)
    · exact Or.inr (Or.inl (mul_one x))
    · exact Or.inl hxx
    · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
    · exact Or.inr (Or.inr (Or.inl (by rw [← mul_assoc, hxx, one_mul])))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (by rw [mul_assoc])))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by
        rw [← mul_assoc, ← mul_assoc, hxx, one_mul])))))
  have hmuly : ∀ g : MulAut V, (g = 1 ∨ g = x ∨ g = y ∨ g = x * y ∨ g = y * x ∨ g = x * y * x) →
      (y * g = 1 ∨ y * g = x ∨ y * g = y ∨ y * g = x * y ∨ y * g = y * x ∨
        y * g = x * y * x) := by
    rintro g (rfl | rfl | rfl | rfl | rfl | rfl)
    · exact Or.inr (Or.inr (Or.inl (mul_one y)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
    · exact Or.inl hyy
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (by rw [← mul_assoc, ← hb])))))
    · exact Or.inr (Or.inl (by rw [← mul_assoc, hyy, one_mul]))
    · exact Or.inr (Or.inr (Or.inr (Or.inl (by
        calc y * (x * y * x) = y * (y * x * y) := by rw [hb]
          _ = y * y * x * y := by simp only [mul_assoc]
          _ = x * y := by rw [hyy, one_mul]))))
  induction hg using Subgroup.closure_induction_left with
  | one => exact Or.inl rfl
  | mul_left a ha g _ ih =>
    rcases ha with rfl | ha
    · exact hmulx g ih
    · rw [Set.mem_singleton_iff.1 ha]
      exact hmuly g ih
  | inv_mul_cancel a ha g _ ih =>
    rcases ha with rfl | ha
    · rw [hxinv]
      exact hmulx g ih
    · rw [Set.mem_singleton_iff.1 ha, hyinv]
      exact hmuly g ih

end Elements

namespace LamPair

section Rigid

open Equiv CFSG.Permutation.SymmetricCoxeter

variable {G : Type*} [Group G]

theorem pow_three_of_braid {a b : G} (ha : a * a = 1) (hb : b * b = 1)
    (hab : a * b * a = b * a * b) : (a * b) ^ 3 = 1 := by
  calc (a * b) ^ 3 = (a * b * a) * (b * a * b) := by
        simp only [pow_succ, pow_zero, one_mul, mul_assoc]
    _ = (b * a * b) * (b * a * b) := by rw [hab]
    _ = b * (a * (b * b) * a) * b := by simp only [mul_assoc]
    _ = 1 := by rw [hb, mul_one, ha, mul_one, hb]

theorem six_dvd_card_of_coxeter {a b : G} (ha : a * a = 1) (hb : b * b = 1)
    (hab : a * b * a = b * a * b) (ha1 : a ≠ 1) (hba : a ≠ b) {R : Subgroup G} (haR : a ∈ R)
    (hbR : b ∈ R) : 6 ∣ Nat.card R := by
  have hpow3 : (a * b) ^ 3 = 1 := pow_three_of_braid ha hb hab
  have hab1 : a * b ≠ 1 := by
    intro h
    apply hba
    rw [eq_inv_of_mul_eq_one_left h]
    exact inv_eq_of_mul_eq_one_right hb
  have h2 : 2 ∣ Nat.card R := by
    have h := orderOf_dvd_natCard (⟨a, haR⟩ : R)
    rwa [Subgroup.orderOf_mk, orderOf_eq_prime (by rw [pow_two]; exact ha) ha1] at h
  have h3 : 3 ∣ Nat.card R := by
    have h := orderOf_dvd_natCard (⟨a * b, R.mul_mem haR hbR⟩ : R)
    rwa [Subgroup.orderOf_mk, orderOf_eq_prime hpow3 hab1] at h
  have := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num : Nat.Coprime 2 3) h2 h3
  simpa using this

theorem isCoxeterA_two {a b : G} (ha : a * a = 1) (hb : b * b = 1)
    (hab : a * b * a = b * a * b) :
    IsCoxeterA 2 (fun i => if i = 0 then a else b) := by
  refine ⟨fun i hi => ?_, fun i hi => ?_, fun i j hij hj => by omega⟩
  · interval_cases i <;> simpa
  · obtain rfl : i = 0 := by omega
    simpa using hab

theorem bijective_perm_of_coxeter [Finite G] (hG : Nat.card G = 6) {a b : G} (ha : a * a = 1)
    (hb : b * b = 1) (hab : a * b * a = b * a * b) (ha1 : a ≠ 1) (hba : a ≠ b)
    {ψ : Perm (Fin 3) →* G} (hψa : ψ (adjSwap 2 0) = a) (hψb : ψ (adjSwap 2 1) = b) :
    Function.Bijective ψ := by
  have h6 : 6 ∣ Nat.card ψ.range :=
    six_dvd_card_of_coxeter ha hb hab ha1 hba ⟨_, hψa⟩ ⟨_, hψb⟩
  have hle : Nat.card ψ.range ≤ 6 := by
    have := Subgroup.card_le_card_group ψ.range
    omega
  have hrange : ψ.range = ⊤ := Subgroup.eq_top_of_card_eq _ (by
    rw [hG]
    exact le_antisymm hle (Nat.le_of_dvd Nat.card_pos h6))
  have hsurj : Function.Surjective ψ := MonoidHom.range_eq_top.1 hrange
  refine hsurj.bijective_of_nat_card_le ?_
  rw [hG, Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
  decide

theorem exists_mulEquiv_of_coxeter {H : Type*} [Group H] [Finite G] [Finite H]
    (hG : Nat.card G = 6) (hH : Nat.card H = 6) {a b : G} {a' b' : H} (ha : a * a = 1)
    (hb : b * b = 1) (hab : a * b * a = b * a * b) (ha1 : a ≠ 1) (hba : a ≠ b)
    (ha' : a' * a' = 1) (hb' : b' * b' = 1) (hab' : a' * b' * a' = b' * a' * b')
    (ha1' : a' ≠ 1) (hba' : a' ≠ b') : ∃ θ : G ≃* H, θ a = a' ∧ θ b = b' := by
  obtain ⟨ψ, hψ⟩ := exists_hom_perm 2 _ (isCoxeterA_two ha hb hab)
  obtain ⟨ψ', hψ'⟩ := exists_hom_perm 2 _ (isCoxeterA_two ha' hb' hab')
  have h0 : ψ (adjSwap 2 0) = a := by simpa using hψ 0 (by norm_num)
  have h1 : ψ (adjSwap 2 1) = b := by simpa using hψ 1 (by norm_num)
  have h0' : ψ' (adjSwap 2 0) = a' := by simpa using hψ' 0 (by norm_num)
  have h1' : ψ' (adjSwap 2 1) = b' := by simpa using hψ' 1 (by norm_num)
  have hbij := bijective_perm_of_coxeter hG ha hb hab ha1 hba h0 h1
  have hbij' := bijective_perm_of_coxeter hH ha' hb' hab' ha1' hba' h0' h1'
  refine ⟨(MulEquiv.ofBijective ψ hbij).symm.trans (MulEquiv.ofBijective ψ' hbij'), ?_, ?_⟩
  · rw [MulEquiv.trans_apply]
    have : (MulEquiv.ofBijective ψ hbij).symm a = adjSwap 2 0 := by
      rw [MulEquiv.symm_apply_eq]
      exact h0.symm
    rw [this]
    exact h0'
  · rw [MulEquiv.trans_apply]
    have : (MulEquiv.ofBijective ψ hbij).symm b = adjSwap 2 1 := by
      rw [MulEquiv.symm_apply_eq]
      exact h1.symm
    rw [this]
    exact h1'

end Rigid

section Sylow

variable {G : Type*} [Group G]

theorem card_pgroup_of_card_six {L A : Subgroup G} (hL : Nat.card L = 6) (hAL : A ≤ L)
    (hA : IsPGroup 2 A) : Nat.card A = 1 ∨ Nat.card A = 2 := by
  have : Finite L := Nat.finite_of_card_ne_zero (by omega)
  have : Finite A := Finite.of_injective (Subgroup.inclusion hAL) (Subgroup.inclusion_injective hAL)
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 hA
  have hdvd : Nat.card A ∣ 6 := hL ▸ Subgroup.card_dvd_of_le hAL
  rcases k with _ | _ | k
  · left
    simpa using hk
  · right
    simpa using hk
  · exfalso
    rw [hk] at hdvd
    have h5 : (4 : ℕ) ∣ 6 := dvd_trans ⟨2 ^ k, by ring⟩ hdvd
    omega

theorem isSylowOf_two_iff_card {L A : Subgroup G} (hL : Nat.card L = 6) (hAL : A ≤ L)
    (hA : IsPGroup 2 A) : IsSylowOf 2 A L ↔ Nat.card A = 2 := by
  have h1 : A.relIndex L * Nat.card A = 6 := by
    have := Subgroup.relIndex_mul_card (H := A) (K := L)
    rwa [inf_eq_left.2 hAL, hL] at this
  constructor
  · rintro ⟨-, -, hidx⟩
    rcases card_pgroup_of_card_six hL hAL hA with h | h
    · exfalso
      apply hidx
      rw [h, mul_one] at h1
      rw [h1]
      norm_num
    · exact h
  · intro h2
    refine ⟨hAL, hA, ?_⟩
    rw [h2] at h1
    have : A.relIndex L = 3 := by omega
    rw [this]
    norm_num

end Sylow

section Words

variable {G : Type*} [Group G] {a b : G}

theorem eq_one_of_sq_cube {g : G} (h2 : g * g = 1) (h3 : g ^ 3 = 1) : g = 1 := by
  rw [pow_three', h2, one_mul] at h3
  exact h3

theorem aba_ne_one (ha : a * a = 1) (hb : b ≠ 1) : a * b * a ≠ 1 := by
  intro h
  apply hb
  calc b = (a * a) * b * (a * a) := by rw [ha, one_mul, mul_one]
    _ = a * (a * b * a) * a := by simp only [mul_assoc]
    _ = 1 := by rw [h, mul_one, ha]

theorem aba_ne_left (ha : a * a = 1) (hab : a ≠ b) : a * b * a ≠ a := by
  intro h
  apply hab
  calc a = a * a * a := by rw [ha, one_mul]
    _ = a * (a * b * a) * a := by rw [h]
    _ = (a * a) * b * (a * a) := by simp only [mul_assoc]
    _ = b := by rw [ha, one_mul, mul_one]

theorem aba_ne_right (hb : b * b = 1) (hbr : a * b * a = b * a * b) (hab : a ≠ b) :
    a * b * a ≠ b := by
  intro h
  have h1 : b * (a * b) = b * 1 := by
    calc b * (a * b) = b * a * b := by rw [mul_assoc]
      _ = a * b * a := hbr.symm
      _ = b := h
      _ = b * 1 := (mul_one b).symm
  have h2 : a * b = 1 := mul_left_cancel h1
  apply hab
  rw [eq_inv_of_mul_eq_one_left h2]
  exact inv_eq_of_mul_eq_one_right hb

end Words

section SLData

open CFSG.Timmesfeld.RankOne CFSG.Timmesfeld.ARS.NaturalModule Matrix

theorem gf2_eq_zero_or_one (c : GaloisField 2 1) : c = 0 ∨ c = 1 := by
  classical
  have : Fintype (GaloisField 2 1) := Fintype.ofFinite _
  have hKcard : Nat.card (GaloisField 2 1) = 2 := by simpa using GaloisField.card 2 1 one_ne_zero
  have hKcard' : Fintype.card (GaloisField 2 1) = 2 := by rwa [← Nat.card_eq_fintype_card]
  by_contra hc
  push Not at hc
  have h3 : ({0, 1, c} : Finset (GaloisField 2 1)).card = 3 :=
    Finset.card_eq_three.2 ⟨0, 1, c, zero_ne_one, hc.1.symm, hc.2.symm, rfl⟩
  have : ({0, 1, c} : Finset (GaloisField 2 1)).card ≤ Fintype.card (GaloisField 2 1) :=
    Finset.card_le_univ _
  omega

theorem card_sl2_gf2 : Nat.card (SpecialLinearGroup (Fin 2) (GaloisField 2 1)) = 6 := by
  classical
  have : Fintype (GaloisField 2 1) := Fintype.ofFinite _
  have hKcard : Nat.card (GaloisField 2 1) = 2 := by simpa using GaloisField.card 2 1 one_ne_zero
  have hKcard' : Fintype.card (GaloisField 2 1) = 2 := by rwa [← Nat.card_eq_fintype_card]
  rw [Matrix.card_SL_field (𝔽 := GaloisField 2 1) 2, hKcard']
  decide

theorem lowerElt_sq : lowerElt (GaloisField 2 1) 1 * lowerElt (GaloisField 2 1) 1 = 1 := by
  rw [lowerElt_mul, CharTwo.add_self_eq_zero, lowerElt_zero]

theorem upperElt_sq : upperElt (GaloisField 2 1) 1 * upperElt (GaloisField 2 1) 1 = 1 := by
  rw [upperElt_mul, CharTwo.add_self_eq_zero, upperElt_zero]

theorem lowerElt_upperElt_braid : lowerElt (GaloisField 2 1) 1 * upperElt (GaloisField 2 1) 1 *
    lowerElt (GaloisField 2 1) 1 = upperElt (GaloisField 2 1) 1 * lowerElt (GaloisField 2 1) 1 *
    upperElt (GaloisField 2 1) 1 := by
  have h2 : (1 : GaloisField 2 1) + 1 = 0 := CharTwo.add_self_eq_zero 1
  apply Subtype.ext
  ext i j
  simp only [Matrix.SpecialLinearGroup.coe_mul, coe_lowerElt, coe_upperElt]
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, h2]

theorem lowerElt_ne_one : lowerElt (GaloisField 2 1) 1 ≠ 1 := by
  intro h
  rw [← lowerElt_zero (K := GaloisField 2 1)] at h
  exact one_ne_zero (lowerElt_injective (GaloisField 2 1) h)

theorem lowerElt_ne_upperElt : lowerElt (GaloisField 2 1) 1 ≠ upperElt (GaloisField 2 1) 1 := by
  intro h
  have := congrArg (fun g : SpecialLinearGroup (Fin 2) (GaloisField 2 1) =>
    (g : Matrix (Fin 2) (Fin 2) (GaloisField 2 1)) 1 0) h
  simp [lowerElt, upperElt] at this

end SLData

section Coordinates

open CFSG.Timmesfeld.RankOne CFSG.Timmesfeld.ARS.NaturalModule Matrix

open Classical in
@[expose] noncomputable def eps (x : MulAut V) (v : V) : GaloisField 2 1 :=
  if x v = v then 0 else 1

theorem eps_eq_zero_iff (x : MulAut V) (v : V) : eps x v = 0 ↔ x v = v := by
  unfold eps
  split_ifs with h <;> simp [h]

theorem eps_eq_one_iff (x : MulAut V) (v : V) : eps x v = 1 ↔ x v ≠ v := by
  unfold eps
  split_ifs with h <;> simp [h]

variable {x y z : MulAut V} {u w c : V}

theorem eps_spec (hx : IsTransv x u) (v : V) :
    (eps x v = 0 ∧ x v = v) ∨ (eps x v = 1 ∧ x v = v * u) := by
  by_cases h : x v = v
  · exact Or.inl ⟨(eps_eq_zero_iff x v).2 h, h⟩
  · exact Or.inr ⟨(eps_eq_one_iff x v).2 h, (hx.step v).resolve_left h⟩

theorem eps_mul (hV : ∀ v : V, v ^ 2 = 1) (hx : IsTransv x u) (v v' : V) :
    eps x (v * v') = eps x v + eps x v' := by
  have hu2 : u * u = 1 := by rw [← pow_two]; exact hV u
  rcases eps_spec hx v with ⟨h1, h1'⟩ | ⟨h1, h1'⟩ <;>
    rcases eps_spec hx v' with ⟨h2, h2'⟩ | ⟨h2, h2'⟩
  · rw [(eps_eq_zero_iff x _).2 (by rw [map_mul, h1', h2']), h1, h2, add_zero]
  · have h3 : x (v * v') = v * v' * u := by rw [map_mul, h1', h2', mul_assoc]
    rw [(eps_eq_one_iff x _).2 (by rw [h3]; intro h; exact hx.ne (by simpa using h)), h1, h2,
      zero_add]
  · have h3 : x (v * v') = v * v' * u := by
      rw [map_mul, h1', h2']
      comm_group
    rw [(eps_eq_one_iff x _).2 (by rw [h3]; intro h; exact hx.ne (by simpa using h)), h1, h2,
      add_zero]
  · have h3 : x (v * v') = v * v' := by
      rw [map_mul, h1', h2']
      calc v * u * (v' * u) = v * v' * (u * u) := by comm_group
        _ = v * v' := by rw [hu2, mul_one]
    rw [(eps_eq_zero_iff x _).2 h3, h1, h2]
    exact (CharTwo.add_self_eq_zero (1 : GaloisField 2 1)).symm

theorem eps_one (x : MulAut V) : eps x 1 = 0 := (eps_eq_zero_iff x 1).2 (map_one x)

theorem eps_centre (hV : ∀ v : V, v ^ 2 = 1) (hx : IsTransv x u) : eps x u = 0 :=
  (eps_eq_zero_iff x u).2 (hx.apply_centre hV)

theorem eps_eq_one_of_apply {v d : V} (hd : d ≠ 1) (h : x v = v * d) : eps x v = 1 :=
  (eps_eq_one_iff x v).2 (by rw [h]; intro h'; exact hd (by simpa using h'))

theorem eps_apply (hV : ∀ v : V, v ^ 2 = 1) (hx : IsTransv x u) (hz : IsTransv z c) (v : V) :
    eps z (x v) = eps z v + eps x v * eps z u := by
  rcases eps_spec hx v with ⟨h1, h1'⟩ | ⟨h1, h1'⟩
  · rw [h1', h1, zero_mul, add_zero]
  · rw [h1', eps_mul hV hz, h1, one_mul]

theorem exists_coordHom (hV : ∀ v : V, v ^ 2 = 1) (hx : IsTransv x u) (hy : IsTransv y w) :
    ∃ β : V →* Multiplicative (Fin 2 → GaloisField 2 1),
      ∀ v, Multiplicative.toAdd (β v) = ![eps x v, eps y v] := by
  refine ⟨{ toFun := fun v => Multiplicative.ofAdd ![eps x v, eps y v]
            map_one' := ?_
            map_mul' := ?_ }, fun v => rfl⟩
  · show Multiplicative.ofAdd ![eps x 1, eps y 1] = 1
    rw [eps_one, eps_one]
    have h0 : (![0, 0] : Fin 2 → GaloisField 2 1) = 0 := by
      ext i
      fin_cases i <;> rfl
    rw [h0, ofAdd_zero]
  · intro v v'
    show Multiplicative.ofAdd ![eps x (v * v'), eps y (v * v')] =
      Multiplicative.ofAdd ![eps x v, eps y v] * Multiplicative.ofAdd ![eps x v', eps y v']
    rw [eps_mul hV hx, eps_mul hV hy, ← ofAdd_add]
    congr 1
    ext i
    fin_cases i <;> rfl

variable {β : V →* Multiplicative (Fin 2 → GaloisField 2 1)}

theorem coord_surjective (hV : ∀ v : V, v ^ 2 = 1) (hx : IsTransv x u) (hy : IsTransv y w)
    (hxw : x w = w * u) (hyu : y u = u * w)
    (hβ : ∀ v, Multiplicative.toAdd (β v) = ![eps x v, eps y v]) : Function.Surjective β := by
  have hxu : eps x u = 0 := eps_centre hV hx
  have hyw : eps y w = 0 := eps_centre hV hy
  have hxw1 : eps x w = 1 := eps_eq_one_of_apply hx.ne hxw
  have hyu1 : eps y u = 1 := eps_eq_one_of_apply hy.ne hyu
  intro t
  have ht : Multiplicative.toAdd t = ![Multiplicative.toAdd t 0, Multiplicative.toAdd t 1] := by
    ext i
    fin_cases i <;> rfl
  rcases gf2_eq_zero_or_one (Multiplicative.toAdd t 0) with ha | ha <;>
    rcases gf2_eq_zero_or_one (Multiplicative.toAdd t 1) with hb | hb
  · refine ⟨1, Multiplicative.toAdd.injective ?_⟩
    rw [hβ, ht, ha, hb, eps_one, eps_one]
  · refine ⟨u, Multiplicative.toAdd.injective ?_⟩
    rw [hβ, ht, ha, hb, hxu, hyu1]
  · refine ⟨w, Multiplicative.toAdd.injective ?_⟩
    rw [hβ, ht, ha, hb, hxw1, hyw]
  · refine ⟨w * u, Multiplicative.toAdd.injective ?_⟩
    rw [hβ, ht, ha, hb, eps_mul hV hx, eps_mul hV hy, hxu, hyu1, hxw1, hyw, zero_add, add_zero]

theorem coord_eq_one_iff
    (hβ : ∀ v, Multiplicative.toAdd (β v) = ![eps x v, eps y v]) (v : V) :
    β v = 1 ↔ v ∈ fixV (Subgroup.zpowers x ⊔ Subgroup.zpowers y) := by
  rw [fixV_sup, Subgroup.mem_inf, Glauberman.mem_fixV_zpowers, Glauberman.mem_fixV_zpowers,
    ← eps_eq_zero_iff, ← eps_eq_zero_iff]
  constructor
  · intro h
    have h1 := congrArg Multiplicative.toAdd h
    rw [hβ] at h1
    exact ⟨congrFun h1 0, congrFun h1 1⟩
  · rintro ⟨h1, h2⟩
    apply Multiplicative.toAdd.injective
    rw [hβ, h1, h2]
    ext i
    fin_cases i <;> rfl

theorem coord_apply_x (hV : ∀ v : V, v ^ 2 = 1) (hx : IsTransv x u) (hy : IsTransv y w)
    (hyu : y u = u * w) (hβ : ∀ v, Multiplicative.toAdd (β v) = ![eps x v, eps y v]) (v : V) :
    β (x v) = Multiplicative.ofAdd ((lowerElt (GaloisField 2 1) 1 :
      Matrix (Fin 2) (Fin 2) (GaloisField 2 1)) *ᵥ Multiplicative.toAdd (β v)) := by
  apply Multiplicative.toAdd.injective
  rw [toAdd_ofAdd, hβ, hβ, lowerElt_mulVec]
  have e1 : eps x (x v) = eps x v := by
    rw [eps_apply hV hx hx, eps_centre hV hx, mul_zero, add_zero]
  have e2 : eps y (x v) = eps x v + eps y v := by
    rw [eps_apply hV hx hy, eps_eq_one_of_apply hy.ne hyu, mul_one, add_comm]
  rw [e1, e2]
  ext i
  fin_cases i <;> simp

theorem coord_apply_y (hV : ∀ v : V, v ^ 2 = 1) (hx : IsTransv x u) (hy : IsTransv y w)
    (hxw : x w = w * u) (hβ : ∀ v, Multiplicative.toAdd (β v) = ![eps x v, eps y v]) (v : V) :
    β (y v) = Multiplicative.ofAdd ((upperElt (GaloisField 2 1) 1 :
      Matrix (Fin 2) (Fin 2) (GaloisField 2 1)) *ᵥ Multiplicative.toAdd (β v)) := by
  apply Multiplicative.toAdd.injective
  rw [toAdd_ofAdd, hβ, hβ, upperElt_mulVec]
  have e1 : eps y (y v) = eps y v := by
    rw [eps_apply hV hy hy, eps_centre hV hy, mul_zero, add_zero]
  have e2 : eps x (y v) = eps x v + eps y v := by
    rw [eps_apply hV hy hx, eps_eq_one_of_apply hx.ne hxw, mul_one]
  rw [e1, e2]
  ext i
  fin_cases i <;> simp

end Coordinates

end LamPair

section Pair

variable [Finite V] {x y : MulAut V} {u w : V}

omit [Finite V] in
theorem ne_of_ne_centre (hx : IsTransv x u) (hy : IsTransv y w) (huw : u ≠ w) : x ≠ y := by
  rintro rfl
  exact huw (hx.centre_unique hy)

theorem card_pair (hV : ∀ v : V, v ^ 2 = 1) (hx : IsTransv x u) (hy : IsTransv y w)
    (hxw : x w = w * u) (hyu : y u = u * w) (huw : u ≠ w) :
    Nat.card ↥(Subgroup.zpowers x ⊔ Subgroup.zpowers y) = 6 := by
  classical
  set L := Subgroup.zpowers x ⊔ Subgroup.zpowers y with hL
  have hxL : x ∈ L := Subgroup.mem_sup_left (Subgroup.mem_zpowers x)
  have hyL : y ∈ L := Subgroup.mem_sup_right (Subgroup.mem_zpowers y)
  have h6 : 6 ∣ Nat.card L :=
    LamPair.six_dvd_card_of_coxeter hx.sq hy.sq (hx.braid hV hy hxw hyu) hx.ne_one
      (ne_of_ne_centre hx hy huw) hxL hyL
  have hle : Nat.card L ≤ 6 := by
    have hsub : (L : Set (MulAut V)) ⊆
        ↑({1, x, y, x * y, y * x, x * y * x} : Finset (MulAut V)) := by
      intro g hg
      simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
        Set.mem_singleton_iff]
      exact pair_elements hV hx hy hxw hyu g hg
    calc Nat.card L = (L : Set (MulAut V)).ncard := Nat.card_coe_set_eq _
      _ ≤ (↑({1, x, y, x * y, y * x, x * y * x} : Finset (MulAut V)) : Set (MulAut V)).ncard :=
          Set.ncard_le_ncard hsub (Finset.finite_toSet _)
      _ = ({1, x, y, x * y, y * x, x * y * x} : Finset (MulAut V)).card :=
          Set.ncard_coe_finset _
      _ ≤ 6 := Finset.card_le_six
  exact le_antisymm hle (Nat.le_of_dvd Nat.card_pos h6)

theorem sylow_pair (hV : ∀ v : V, v ^ 2 = 1) (hx : IsTransv x u) (hy : IsTransv y w)
    (hxw : x w = w * u) (hyu : y u = u * w) (huw : u ≠ w) {S : Subgroup (MulAut V)}
    (hS : IsSylowOf 2 S (Subgroup.zpowers x ⊔ Subgroup.zpowers y)) :
    S = Subgroup.zpowers x ∨ S = Subgroup.zpowers y ∨ S = Subgroup.zpowers (x * y * x) := by
  set L := Subgroup.zpowers x ⊔ Subgroup.zpowers y with hL
  have hcard : Nat.card L = 6 := card_pair hV hx hy hxw hyu huw
  have hSL : S ≤ L := hS.1
  have hS2 : Nat.card S = 2 := (LamPair.isSylowOf_two_iff_card hcard hSL hS.2.1).1 hS
  have hne : S ≠ ⊥ := by
    intro hbot
    rw [hbot] at hS2
    simp at hS2
  obtain ⟨⟨a, ha⟩, ha1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hne
  have ha1' : a ≠ 1 := fun e => ha1 (Subtype.ext e)
  have hSa : S = Subgroup.zpowers a := eq_zpowers_of_card_two hS2 ha ha1'
  have ha2 : a * a = 1 := by
    have h := orderOf_dvd_natCard (⟨a, ha⟩ : S)
    rw [Subgroup.orderOf_mk, hS2] at h
    rw [← pow_two]
    exact orderOf_dvd_iff_pow_eq_one.1 h
  rcases pair_elements hV hx hy hxw hyu a (hSL ha) with h | h | h | h | h | h
  · exact absurd h ha1'
  · exact Or.inl (by rw [hSa, h])
  · exact Or.inr (Or.inl (by rw [hSa, h]))
  · exfalso
    apply ha1'
    rw [h] at ha2 ⊢
    exact LamPair.eq_one_of_sq_cube ha2 (hx.pow_three hV hy hxw hyu)
  · exfalso
    apply ha1'
    rw [h] at ha2 ⊢
    exact LamPair.eq_one_of_sq_cube ha2 (hy.pow_three hV hx hyu hxw)
  · exact Or.inr (Or.inr (by rw [hSa, h]))

theorem inf_pair (hV : ∀ v : V, v ^ 2 = 1) (hx : IsTransv x u) (hy : IsTransv y w)
    (hxw : x w = w * u) (hyu : y u = u * w) (huw : u ≠ w) {M : Subgroup (MulAut V)}
    (hxM : x ∈ M) (hyM : y ∉ M) :
    M ⊓ (Subgroup.zpowers x ⊔ Subgroup.zpowers y) = Subgroup.zpowers x := by
  set L := Subgroup.zpowers x ⊔ Subgroup.zpowers y with hL
  have hcard : Nat.card L = 6 := card_pair hV hx hy hxw hyu huw
  have hxL : x ∈ L := Subgroup.mem_sup_left (Subgroup.mem_zpowers x)
  have hyL : y ∈ L := Subgroup.mem_sup_right (Subgroup.mem_zpowers y)
  have hle : Subgroup.zpowers x ≤ M ⊓ L := Subgroup.zpowers_le.2 ⟨hxM, hxL⟩
  have hx2 : Nat.card (Subgroup.zpowers x) = 2 := by
    rw [Nat.card_zpowers, orderOf_eq_prime (by rw [pow_two]; exact hx.sq) hx.ne_one]
  have hd1 : Nat.card ↥(M ⊓ L) ∣ 6 := by
    have := Subgroup.card_dvd_of_le (inf_le_right : M ⊓ L ≤ L)
    rwa [hcard] at this
  have hd2 : 2 ∣ Nat.card ↥(M ⊓ L) := by
    have := Subgroup.card_dvd_of_le hle
    rwa [hx2] at this
  have hn : Nat.card ↥(M ⊓ L) = 2 ∨ Nat.card ↥(M ⊓ L) = 6 := by
    have hle6 : Nat.card ↥(M ⊓ L) ≤ 6 := Nat.le_of_dvd (by norm_num) hd1
    generalize Nat.card ↥(M ⊓ L) = n at hd1 hd2 hle6 ⊢
    interval_cases n <;> omega
  rcases hn with hn | hn
  · exact (Subgroup.eq_of_le_of_card_ge hle (by omega)).symm
  · exfalso
    have hML : M ⊓ L = L := Subgroup.eq_of_le_of_card_ge inf_le_right (by omega)
    have : y ∈ M ⊓ L := by
      rw [hML]
      exact hyL
    exact hyM this.1

theorem exists_mulEquiv_sl_pair (hV : ∀ v : V, v ^ 2 = 1) (hx : IsTransv x u)
    (hy : IsTransv y w) (hxw : x w = w * u) (hyu : y u = u * w) (huw : u ≠ w) :
    ∃ θ : ↥(Subgroup.zpowers x ⊔ Subgroup.zpowers y) ≃*
        Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 1),
      (∀ g : ↥(Subgroup.zpowers x ⊔ Subgroup.zpowers y), (g : MulAut V) = x →
          θ g = CFSG.Timmesfeld.RankOne.lowerElt (GaloisField 2 1) 1) ∧
        ∀ g : ↥(Subgroup.zpowers x ⊔ Subgroup.zpowers y), (g : MulAut V) = y →
          θ g = CFSG.Timmesfeld.RankOne.upperElt (GaloisField 2 1) 1 := by
  set L := Subgroup.zpowers x ⊔ Subgroup.zpowers y with hL
  have hcard : Nat.card L = 6 := card_pair hV hx hy hxw hyu huw
  have hxL : x ∈ L := Subgroup.mem_sup_left (Subgroup.mem_zpowers x)
  have hyL : y ∈ L := Subgroup.mem_sup_right (Subgroup.mem_zpowers y)
  have : Finite L := Nat.finite_of_card_ne_zero (by omega)
  have : Finite (Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 1)) :=
    Nat.finite_of_card_ne_zero (by rw [LamPair.card_sl2_gf2]; norm_num)
  obtain ⟨θ, h1, h2⟩ := LamPair.exists_mulEquiv_of_coxeter hcard LamPair.card_sl2_gf2
    (a := (⟨x, hxL⟩ : L)) (b := ⟨y, hyL⟩)
    (a' := CFSG.Timmesfeld.RankOne.lowerElt (GaloisField 2 1) 1)
    (b' := CFSG.Timmesfeld.RankOne.upperElt (GaloisField 2 1) 1)
    (Subtype.ext hx.sq) (Subtype.ext hy.sq) (Subtype.ext (hx.braid hV hy hxw hyu))
    (fun h => hx.ne_one (congrArg Subtype.val h))
    (fun h => ne_of_ne_centre hx hy huw (congrArg Subtype.val h))
    LamPair.lowerElt_sq LamPair.upperElt_sq LamPair.lowerElt_upperElt_braid
    LamPair.lowerElt_ne_one LamPair.lowerElt_ne_upperElt
  refine ⟨θ, fun g hg => ?_, fun g hg => ?_⟩
  · have : g = ⟨x, hxL⟩ := Subtype.ext hg
    rw [this]
    exact h1
  · have : g = ⟨y, hyL⟩ := Subtype.ext hg
    rw [this]
    exact h2

theorem isSLNatSection_pair (hV : ∀ v : V, v ^ 2 = 1) (hx : IsTransv x u) (hy : IsTransv y w)
    (hxw : x w = w * u) (hyu : y u = u * w) (huw : u ≠ w) :
    IsSLNatSection (Subgroup.zpowers x ⊔ Subgroup.zpowers y) ⊤
      (fixV (Subgroup.zpowers x ⊔ Subgroup.zpowers y)) 1 := by
  obtain ⟨θ, hθx, hθy⟩ := exists_mulEquiv_sl_pair hV hx hy hxw hyu huw
  obtain ⟨β, hβ⟩ := LamPair.exists_coordHom hV hx hy
  have hxL : x ∈ Subgroup.zpowers x ⊔ Subgroup.zpowers y :=
    Subgroup.mem_sup_left (Subgroup.mem_zpowers x)
  have hyL : y ∈ Subgroup.zpowers x ⊔ Subgroup.zpowers y :=
    Subgroup.mem_sup_right (Subgroup.mem_zpowers y)
  let T : Submonoid ↥(Subgroup.zpowers x ⊔ Subgroup.zpowers y) :=
    { carrier := {g | ∀ v : V, β ((g : MulAut V) v) = Multiplicative.ofAdd
        (Matrix.mulVec (θ g : Matrix (Fin 2) (Fin 2) (GaloisField 2 1))
          (Multiplicative.toAdd (β v)))}
      mul_mem' := by
        intro g h hg hh v
        rw [Subgroup.coe_mul, MulAut.mul_apply, hg, hh, toAdd_ofAdd, map_mul,
          Matrix.SpecialLinearGroup.coe_mul, Matrix.mulVec_mulVec]
      one_mem' := by
        intro v
        rw [Subgroup.coe_one, MulAut.one_apply, map_one, Matrix.SpecialLinearGroup.coe_one,
          Matrix.one_mulVec, ofAdd_toAdd] }
  have hxT : (⟨x, hxL⟩ : ↥(Subgroup.zpowers x ⊔ Subgroup.zpowers y)) ∈ T := fun v => by
    show β (x v) = _
    rw [hθx ⟨x, hxL⟩ rfl]
    exact LamPair.coord_apply_x hV hx hy hyu hβ v
  have hyT : (⟨y, hyL⟩ : ↥(Subgroup.zpowers x ⊔ Subgroup.zpowers y)) ∈ T := fun v => by
    show β (y v) = _
    rw [hθy ⟨y, hyL⟩ rfl]
    exact LamPair.coord_apply_y hV hx hy hxw hβ v
  have hall : ∀ g : ↥(Subgroup.zpowers x ⊔ Subgroup.zpowers y), g ∈ T := by
    rintro ⟨g, hg⟩
    rcases pair_elements hV hx hy hxw hyu g hg with h | h | h | h | h | h
    · have e : (⟨g, hg⟩ : ↥(Subgroup.zpowers x ⊔ Subgroup.zpowers y)) = 1 := Subtype.ext h
      rw [e]
      exact T.one_mem
    · have e : (⟨g, hg⟩ : ↥(Subgroup.zpowers x ⊔ Subgroup.zpowers y)) = ⟨x, hxL⟩ :=
        Subtype.ext h
      rw [e]
      exact hxT
    · have e : (⟨g, hg⟩ : ↥(Subgroup.zpowers x ⊔ Subgroup.zpowers y)) = ⟨y, hyL⟩ :=
        Subtype.ext h
      rw [e]
      exact hyT
    · have e : (⟨g, hg⟩ : ↥(Subgroup.zpowers x ⊔ Subgroup.zpowers y)) =
          ⟨x, hxL⟩ * ⟨y, hyL⟩ := Subtype.ext h
      rw [e]
      exact T.mul_mem hxT hyT
    · have e : (⟨g, hg⟩ : ↥(Subgroup.zpowers x ⊔ Subgroup.zpowers y)) =
          ⟨y, hyL⟩ * ⟨x, hxL⟩ := Subtype.ext h
      rw [e]
      exact T.mul_mem hyT hxT
    · have e : (⟨g, hg⟩ : ↥(Subgroup.zpowers x ⊔ Subgroup.zpowers y)) =
          ⟨x, hxL⟩ * ⟨y, hyL⟩ * ⟨x, hxL⟩ := Subtype.ext h
      rw [e]
      exact T.mul_mem (T.mul_mem hxT hyT) hxT
  refine ⟨fun _ _ _ _ => trivial, θ, β.comp (⊤ : Subgroup V).subtype, ?_, ?_, ?_⟩
  · intro t
    obtain ⟨v, hv⟩ := LamPair.coord_surjective hV hx hy hxw hyu hβ t
    exact ⟨⟨v, trivial⟩, hv⟩
  · ext p
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    exact LamPair.coord_eq_one_iff hβ p.1
  · intro g p hp
    exact hall g p.1

end Pair

section Lam

variable [Finite V] {x y : MulAut V} {u w : V} {P : Subgroup (MulAut V)}
  {D : Set (Subgroup (MulAut V))}

theorem lamSet_of_pair (h : Hyp41 P D) (hV : ∀ v : V, v ^ 2 = 1) (hx : IsTransv x u)
    (hy : IsTransv y w) (hxw : x w = w * u) (hyu : y u = u * w) (huw : u ≠ w) (hxP : x ∈ P)
    (hyP : y ∈ P) (hX : Subgroup.zpowers x ∈ D) (hY : Subgroup.zpowers y ∈ D)
    {M : Subgroup (MulAut V)} (hxM : x ∈ M) (hyM : y ∉ M) :
    Subgroup.zpowers x ⊔ Subgroup.zpowers y ∈ lamSet P D M := by
  set L := Subgroup.zpowers x ⊔ Subgroup.zpowers y with hL
  have hxx : x * x = 1 := hx.sq
  have hyy : y * y = 1 := hy.sq
  have hb : x * y * x = y * x * y := hx.braid hV hy hxw hyu
  have hcard : Nat.card L = 6 := card_pair hV hx hy hxw hyu huw
  have hxL : x ∈ L := Subgroup.mem_sup_left (Subgroup.mem_zpowers x)
  have hyL : y ∈ L := Subgroup.mem_sup_right (Subgroup.mem_zpowers y)
  have hxyL : x * y ∈ L := L.mul_mem hxL hyL
  have hxyxL : x * y * x ∈ L := L.mul_mem hxyL hxL
  have hxy : x ≠ y := ne_of_ne_centre hx hy huw
  have hLP : L ≤ P := sup_le (Subgroup.zpowers_le.2 hxP) (Subgroup.zpowers_le.2 hyP)
  have hX' : Subgroup.zpowers (x * y * x) ∈ D := by
    have := h.conj_mem _ hY x hxP
    rwa [conjSub_zpowers, inv_eq_of_mul_eq_one_right hxx] at this
  have hsyl : ∀ A : Subgroup (MulAut V), A ∈ dInter D L ↔ IsSylowOf 2 A L := by
    intro A
    constructor
    · rintro ⟨hAD, hAL⟩
      have hAp : IsPGroup 2 A := Glauberman.isPGroup_two_of_sq_eq_one (h.elemAb A hAD).2
      refine (LamPair.isSylowOf_two_iff_card hcard hAL hAp).2 ?_
      rcases LamPair.card_pgroup_of_card_six hcard hAL hAp with h1 | h1
      · exact absurd (Subgroup.eq_bot_of_card_eq A h1) (h.ne_bot A hAD)
      · exact h1
    · intro hA
      refine ⟨?_, hA.1⟩
      rcases sylow_pair hV hx hy hxw hyu huw hA with rfl | rfl | rfl
      · exact hX
      · exact hY
      · exact hX'
  have hmemX : M ∈ mSet P M (Subgroup.zpowers x) :=
    ⟨⟨1, P.one_mem, (conjSub_one M).symm⟩, Subgroup.zpowers_le.2 hxM⟩
  have hMne1 : mSet P M (Subgroup.zpowers x) ≠ mSet P M (Subgroup.zpowers y) := by
    intro heq
    rw [heq] at hmemX
    exact hyM (Subgroup.zpowers_le.1 hmemX.2)
  have hMne2 : mSet P M (Subgroup.zpowers x) ≠ mSet P M (Subgroup.zpowers (x * y * x)) := by
    intro heq
    rw [heq] at hmemX
    have hle : Subgroup.zpowers (x * y * x) ≤ M ⊓ L :=
      le_inf hmemX.2 (Subgroup.zpowers_le.2 hxyxL)
    rw [inf_pair hV hx hy hxw hyu huw hxM hyM] at hle
    rcases eq_one_or_of_mem_zpowers hxx (Subgroup.zpowers_le.1 hle) with h1 | h1
    · exact LamPair.aba_ne_one hxx hy.ne_one h1
    · exact LamPair.aba_ne_left hxx hxy h1
  have hconj : x * y * x * (x * y)⁻¹ = y := by
    rw [mul_inv_rev, inv_eq_of_mul_eq_one_right hxx, inv_eq_of_mul_eq_one_right hyy]
    calc x * y * x * (y * x) = (x * y * x) * y * x := by simp only [mul_assoc]
      _ = (y * x * y) * y * x := by rw [hb]
      _ = y * x * (y * y) * x := by simp only [mul_assoc]
      _ = y := by rw [hyy, mul_one, mul_assoc, hxx, mul_one]
  have hYeq : Subgroup.zpowers y = conjSub (x * y) (Subgroup.zpowers x) := by
    rw [conjSub_zpowers, hconj]
  have hMne3 : mSet P M (Subgroup.zpowers y) ≠ mSet P M (Subgroup.zpowers (x * y * x)) := by
    intro heq
    have hmem : conjSub (x * y) M ∈ mSet P M (Subgroup.zpowers y) :=
      ⟨⟨x * y, P.mul_mem hxP hyP, rfl⟩, by
        rw [hYeq]
        exact conjSub_mono _ (Subgroup.zpowers_le.2 hxM)⟩
    rw [heq] at hmem
    have h1 : Subgroup.zpowers (x * y * x) ≤ conjSub (x * y) M ⊓ conjSub (x * y) L :=
      le_inf hmem.2 (by
        rw [conjSub_self_of_mem hxyL]
        exact Subgroup.zpowers_le.2 hxyxL)
    rw [← conjSub_inf, inf_pair hV hx hy hxw hyu huw hxM hyM, ← hYeq] at h1
    rcases eq_one_or_of_mem_zpowers hyy (Subgroup.zpowers_le.1 h1) with h2 | h2
    · exact LamPair.aba_ne_one hxx hy.ne_one h2
    · exact LamPair.aba_ne_right hyy hb hxy h2
  refine ⟨hLP, ⟨1, le_rfl, isSLNatSection_pair hV hx hy hxw hyu huw⟩, hsyl, ?_⟩
  intro A hA B hB hAB
  have hA' := (hsyl A).1 hA
  have hB' := (hsyl B).1 hB
  rcases sylow_pair hV hx hy hxw hyu huw hA' with rfl | rfl | rfl <;>
    rcases sylow_pair hV hx hy hxw hyu huw hB' with rfl | rfl | rfl
  · exact absurd rfl hAB
  · exact hMne1
  · exact hMne2
  · exact hMne1.symm
  · exact absurd rfl hAB
  · exact hMne3
  · exact hMne2.symm
  · exact hMne3.symm
  · exact absurd rfl hAB

theorem lamSet_of_noncomm_pair (h : Hyp41 P D) (hV : ∀ v : V, v ^ 2 = 1)
    {M X Y : Subgroup (MulAut V)} (hX : X ∈ D) (hY : Y ∈ D) (hX2 : Nat.card X = 2)
    (hY2 : Nat.card Y = 2) (hnc : ∃ a ∈ X, ∃ b ∈ Y, a * b ≠ b * a) (hXM : X ≤ M)
    (hYM : ¬ Y ≤ M) : X ⊔ Y ∈ lamSet P D M := by
  obtain ⟨x, u, hx, hxP, hXx, -⟩ := exists_transv_of_card_two h hV hX hX2
  obtain ⟨y, w, hy, hyP, hYy, -⟩ := exists_transv_of_card_two h hV hY hY2
  subst hXx hYy
  have hnc' : x * y ≠ y * x := by
    intro hc
    obtain ⟨a, ha, b, hb, hab⟩ := hnc
    exact hab ((forall_comm_zpowers_iff x y).2 hc a ha b hb)
  obtain ⟨hxw, hyu, huw⟩ := Hyp41.rel_of_noncomm h hV hX hY hx hy rfl rfl hnc'
  exact lamSet_of_pair h hV hx hy hxw hyu huw hxP hyP hX hY (Subgroup.zpowers_le.1 hXM)
    (fun hyM => hYM (Subgroup.zpowers_le.2 hyM))

end Lam

end CFSG.CGT.PushingUpLit.BHS
