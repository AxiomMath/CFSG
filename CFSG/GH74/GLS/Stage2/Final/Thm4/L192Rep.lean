module

public import CFSG.LocalAnalysis.SectionRank.Ccomm.Supercritical
public import CFSG.LocalAnalysis.SectionRank.Ccomm.RankTwo
public import CFSG.LocalAnalysis.SectionRank.Ccomm.PrimeLinear
public import CFSG.GH74.GLS.Basic

public section

namespace CFSG.GH74.GLS.Stage2.Final.Thm4.L192

open Subgroup CFSG.SectionRank CFSG.SectionRank.Ccomm Matrix CFSG.GH74.GLS

theorem exists_rep {r : ℕ} [hr : Fact r.Prime] (hr2 : r ≠ 2) {Q : Type*} [Group Q] [Finite Q]
    (hQ : IsPGroup r Q) (hrk : CFSG.Open.pRank r (⊤ : Subgroup Q) ≤ 2)
    {X : Type*} [Group X] (α : X →* MulAut Q) :
    ∃ (n : ℕ) (ρ : X →* GL (Fin n) (ZMod r)), n ≤ 2 ∧ (∀ x : X, α x = 1 → ρ x = 1) ∧
      ∀ x : X, Nat.Coprime (orderOf x) r → ρ x = 1 → α x = 1 := by
  by_cases hQ1 : Nontrivial Q
  · obtain ⟨D, hDc, -, hDexp, -, -, hker⟩ := supercritical_witness hr2 hQ
    have hDp : IsPGroup r D := hQ.to_subgroup D
    have hDrank : CFSG.Open.pRank r (⊤ : Subgroup D) ≤ 2 :=
      (pRank_top_le_of_injective hr.out.one_lt D.subtype D.subtype_injective).trans hrk
    have hDexp' : ∀ x : D, x ^ r = 1 := fun x =>
      Subtype.ext (by rw [SubgroupClass.coe_pow, OneMemClass.coe_one]; exact hDexp _ x.2)
    obtain ⟨-, hW2⟩ := rank_two_exponent_prime_order_bound hDp hDexp' hDrank
    obtain ⟨k, hk⟩ := (hDp.to_quotient (frattini D)).exists_card_eq
    have hk2 : k ≤ 2 := (Nat.pow_le_pow_iff_right hr.out.one_lt).1 (hk ▸ hW2)
    obtain ⟨-, hWcomm, hWpow⟩ := frattini_quotient_elementary hDp
    obtain ⟨e⟩ := nonempty_mulEquiv_of_elementary hWcomm hWpow hk
    refine ⟨k, (elemAutEquivGL e).toMonoidHom.comp ((frattiniAction D).comp α), hk2,
      fun x hx => by simp [hx], ?_⟩
    intro x hx hρ
    have h1 : frattiniAction D (α x) = 1 := by
      apply (elemAutEquivGL e).injective
      simpa using hρ
    have h2 : α x ∈ (frattiniAction D).ker := h1
    obtain ⟨m, hm⟩ := (IsPGroup.iff_orderOf.mp hker) ⟨α x, h2⟩
    have h3 : orderOf (α x) ∣ orderOf x := orderOf_map_dvd α x
    rw [Subgroup.orderOf_mk] at hm
    have h4 : orderOf (α x) ∣ r ^ m := hm ▸ dvd_refl _
    have h5 : Nat.Coprime (orderOf (α x)) r := Nat.Coprime.coprime_dvd_left h3 hx
    have h6 : orderOf (α x) = 1 := by
      have := Nat.Coprime.pow_right m h5
      exact Nat.eq_one_of_dvd_coprimes this (dvd_refl _) h4
    exact orderOf_eq_one_iff.mp h6
  · rw [not_nontrivial_iff_subsingleton] at hQ1
    refine ⟨0, 1, by norm_num, fun x _ => Subsingleton.elim _ _, fun x _ _ => ?_⟩
    ext q
    exact Subsingleton.elim _ _

theorem GL_central_of_sq_det {r : ℕ} [hr : Fact r.Prime] (hr2 : r ≠ 2) {n : ℕ} (hn : n ≤ 2)
    (g h : GL (Fin n) (ZMod r)) (hsq : g * g = 1)
    (hdet : Matrix.GeneralLinearGroup.det g = 1) : g * h = h * g := by
  interval_cases n
  · exact Subsingleton.elim _ _
  · exact GL_one_comm g h
  · have h1 : (g : Matrix (Fin 2) (Fin 2) (ZMod r)) * (g : Matrix (Fin 2) (Fin 2) (ZMod r)) = 1 := by
      have := congrArg (fun u : GL (Fin 2) (ZMod r) => (u : Matrix (Fin 2) (Fin 2) (ZMod r))) hsq
      simpa using this
    have h2 : (g : Matrix (Fin 2) (Fin 2) (ZMod r)).det = 1 := by
      have := congrArg (fun u : (ZMod r)ˣ => (u : ZMod r)) hdet
      simpa [Matrix.GeneralLinearGroup.val_det_apply] using this
    rcases eq_one_or_neg_one_of_sq_eq_one (two_ne_zero_zmod hr2) h2 h1 with h3 | h3
    · have : g = 1 := Units.ext h3
      rw [this]
      simp
    · have : g = -1 := Units.ext (by rw [Units.val_neg, Units.val_one]; exact h3)
      rw [this]
      simp

@[expose] def oddTorsion (A : Type*) [CommGroup A] : Subgroup A where
  carrier := {y | ∃ m : ℕ, Nat.Coprime m 2 ∧ y ^ m = 1}
  one_mem' := ⟨1, by norm_num, one_pow _⟩
  mul_mem' := by
    rintro a b ⟨m₁, h₁, e₁⟩ ⟨m₂, h₂, e₂⟩
    refine ⟨m₁ * m₂, Nat.Coprime.mul_left h₁ h₂, ?_⟩
    rw [mul_pow, pow_mul, e₁, one_pow, mul_comm m₁ m₂, pow_mul, e₂, one_pow, one_mul]
  inv_mem' := by
    rintro a ⟨m, h, e⟩
    exact ⟨m, h, by rw [inv_pow, e, inv_one]⟩

theorem hom_eq_one_of_mem_oResidual {X A : Type*} [Group X] [CommGroup A] (δ : X →* A) {x : X}
    (hx : x ∈ oResidual 2 X) {a : ℕ} (ha : x ^ (2 ^ a) = 1) : δ x = 1 := by
  have hle : oResidual 2 X ≤ (oddTorsion A).comap δ := by
    refine (Subgroup.closure_le _).2 ?_
    intro y hy
    exact ⟨orderOf y, hy, by rw [← map_pow, pow_orderOf_eq_one, map_one]⟩
  obtain ⟨m, hm, hδ⟩ := hle hx
  have h1 : orderOf (δ x) ∣ m := orderOf_dvd_of_pow_eq_one hδ
  have h2 : orderOf (δ x) ∣ 2 ^ a := orderOf_dvd_of_pow_eq_one (by rw [← map_pow, ha, map_one])
  have h3 : Nat.Coprime m (2 ^ a) := Nat.Coprime.pow_right a hm
  have : orderOf (δ x) = 1 := Nat.eq_one_of_dvd_coprimes h3 h1 h2
  exact orderOf_eq_one_iff.mp this

end CFSG.GH74.GLS.Stage2.Final.Thm4.L192
