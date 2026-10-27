module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import CFSG.FeitThompson.Definitions.ElementaryAbelianPRank
import CFSG.FeitThompson.Foundations.FiniteHomImageOrder
import CFSG.FeitThompson.Local.GeneralLinearTwoPrimeFieldOrder
import CFSG.FeitThompson.Local.MaximalNormalAbelianSelfCentralizing

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Subgroup Matrix

variable {p d a : ℕ} {P : Type*} [Group P]

theorem isPGroup_of_forall_pow_eq_one (hexp : ∀ x : P, x ^ p = 1) : IsPGroup p P :=
  fun g => ⟨1, by simpa using hexp g⟩

theorem exists_card_eq_pow_of_forall_pow_eq_one [Finite P] (hp : p.Prime)
    (hexp : ∀ x : P, x ^ p = 1) : ∃ a, Nat.card P = p ^ a :=
  have := Fact.mk hp
  (isPGroup_of_forall_pow_eq_one hexp).exists_card_eq

private def addAutEquivLinearAut (m : ℕ) (M : Type*) [AddCommGroup M] [Module (ZMod m) M] :
    AddAut M ≃ (M ≃ₗ[ZMod m] M) where
  toFun e := { e.toAddMonoidHom.toZModLinearMap m with
    invFun := e.symm
    left_inv := e.left_inv
    right_inv := e.right_inv }
  invFun e := e.toAddEquiv
  left_inv _ := rfl
  right_inv _ := rfl

theorem card_mulAut_pi_multiplicative_zmod (p d : ℕ) :
    Nat.card (MulAut (Fin d → Multiplicative (ZMod p))) = Nat.card (GL (Fin d) (ZMod p)) := by
  calc Nat.card (MulAut (Fin d → Multiplicative (ZMod p)))
      = Nat.card (MulAut (Multiplicative (Fin d → ZMod p))) :=
        Nat.card_congr
          (MulAut.congr (MulEquiv.piMultiplicative fun _ : Fin d => ZMod p).symm).toEquiv
    _ = Nat.card (Multiplicative (AddAut (Fin d → ZMod p))) :=
        Nat.card_congr (MulAutMultiplicative _).toEquiv
    _ = Nat.card (AddAut (Fin d → ZMod p)) := Nat.card_congr Multiplicative.ofAdd.symm
    _ = Nat.card ((Fin d → ZMod p) ≃ₗ[ZMod p] (Fin d → ZMod p)) :=
        Nat.card_congr (addAutEquivLinearAut p _)
    _ = Nat.card (LinearMap.GeneralLinearGroup (ZMod p) (Fin d → ZMod p)) :=
        Nat.card_congr (LinearMap.GeneralLinearGroup.generalLinearEquiv _ _).toEquiv.symm
    _ = Nat.card (GL (Fin d) (ZMod p)) :=
        Nat.card_congr Matrix.GeneralLinearGroup.toLin.toEquiv.symm

theorem ker_conjNormal (A : Subgroup P) [A.Normal] :
    (MulAut.conjNormal (H := A)).ker = centralizer (A : Set P) := by
  ext g
  simp only [MonoidHom.mem_ker, mem_centralizer_iff]
  constructor
  · intro h b hb
    have hgb : g * b * g⁻¹ = b := by
      have := congrArg (fun e => ((e ⟨b, hb⟩ : A) : P)) h
      simpa [MulAut.conjNormal_apply] using this
    calc b * g = g * b * g⁻¹ * g := by rw [hgb]
      _ = g * b := by group
  · intro h
    refine MulEquiv.ext fun b => Subtype.ext ?_
    have hb := h b b.2
    simp only [MulAut.conjNormal_apply, MulAut.one_apply]
    rw [← hb]
    group

theorem add_le_three_of_pow_dvd_card_GL (hp : p.Prime) {k : ℕ} (hd : d ≤ 2)
    (h : p ^ k ∣ Nat.card (GL (Fin d) (ZMod p))) : k + d ≤ 3 := by
  have := Fact.mk hp
  have h2 := hp.two_le
  interval_cases d
  ·
    have h1 : p ^ k = 1 := Nat.eq_one_of_dvd_one (by simpa using h)
    rw [Nat.pow_eq_one] at h1
    omega
  ·
    rw [card_GL_one_zmod] at h
    have hk : k = 0 := by
      by_contra hk
      have hdvd : p ∣ p - 1 := dvd_trans (dvd_pow_self p hk) h
      have := Nat.le_of_dvd (by omega) hdvd
      omega
    omega
  ·
    have := (pow_dvd_card_GL_two_zmod_iff p (k := k)).1 h
    omega

theorem card_le_pow_three_of_elementaryAbelianPRank_le_two [Finite P] (hp : p.Prime)
    (hrank : elementaryAbelianPRank p P ≤ 2) (hexp : ∀ x : P, x ^ p = 1) :
    Nat.card P ≤ p ^ 3 := by
  have := Fact.mk hp
  have hP : IsPGroup p P := isPGroup_of_forall_pow_eq_one hexp
  obtain ⟨A, -, hA⟩ := Finite.exists_le_maximal
    (p := fun B : Subgroup P => B.Normal ∧ IsMulCommutative B) (a := ⊥)
    ⟨inferInstance, inferInstance⟩
  obtain ⟨hAn, hAc⟩ := hA.prop
  have := hAn
  have := hAc
  have hcent : centralizer (A : Set P) = A :=
    centralizer_eq_of_maximal_normal_isMulCommutative_of_isPGroup hp hP hA
  obtain ⟨d, hd⟩ := (hP.to_subgroup A).exists_card_eq
  have hdmem : d ∈ elementaryAbelianRanks p P :=
    (mem_elementaryAbelianRanks_iff_exists_subgroup hp).2 ⟨A, hAc, fun x _ => hexp x, hd⟩
  have hd2 : d ≤ 2 := (le_elementaryAbelianPRank hp.one_lt hdmem).trans hrank
  set f : P →* MulAut A := MulAut.conjNormal with hf
  have hker : f.ker = A := by rw [hf, ker_conjNormal, hcent]
  have hcard : Nat.card f.range * Nat.card A = Nat.card P := by
    rw [← natCard_range_mul_natCard_ker f, hker]
  obtain ⟨n, hn⟩ := hP.exists_card_eq
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow hp).1 (hn ▸ Subgroup.card_range_dvd f)
  have hAut : Nat.card (MulAut A) = Nat.card (GL (Fin d) (ZMod p)) := by
    let _ : CommGroup A := IsMulCommutative.instCommGroup
    obtain ⟨e⟩ := nonempty_mulEquiv_pi_of_exponent (G := A) hp
      (fun x => Subtype.ext (hexp x.1)) hd
    rw [Nat.card_congr (MulAut.congr e).toEquiv, card_mulAut_pi_multiplicative_zmod]
  have hdvd : p ^ k ∣ Nat.card (GL (Fin d) (ZMod p)) := by
    rw [← hAut, ← hk]
    exact Subgroup.card_subgroup_dvd_card f.range
  have hsum := add_le_three_of_pow_dvd_card_GL hp hd2 hdvd
  calc Nat.card P = p ^ k * p ^ d := by rw [← hcard, hk, hd]
    _ = p ^ (k + d) := (pow_add p k d).symm
    _ ≤ p ^ 3 := Nat.pow_le_pow_right hp.pos (by omega)

theorem card_le_pow_three_of_card_eq_pow_of_elementaryAbelianPRank_le_two (hp : p.Prime)
    (hcard : Nat.card P = p ^ a) (hrank : elementaryAbelianPRank p P ≤ 2)
    (hexp : ∀ x : P, x ^ p = 1) : Nat.card P ≤ p ^ 3 :=
  have : Finite P := Nat.finite_of_card_ne_zero (by rw [hcard]; exact pow_ne_zero _ hp.pos.ne')
  card_le_pow_three_of_elementaryAbelianPRank_le_two hp hrank hexp

theorem le_three_of_card_eq_pow_of_elementaryAbelianPRank_le_two (hp : p.Prime)
    (hcard : Nat.card P = p ^ a) (hrank : elementaryAbelianPRank p P ≤ 2)
    (hexp : ∀ x : P, x ^ p = 1) : a ≤ 3 := by
  have h := card_le_pow_three_of_card_eq_pow_of_elementaryAbelianPRank_le_two hp hcard hrank hexp
  rw [hcard] at h
  exact (Nat.pow_le_pow_iff_right hp.one_lt).1 h

end

end CFSG.FeitThompson
