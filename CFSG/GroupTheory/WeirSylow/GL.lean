module

public import CFSG.GroupTheory.WeirSylow.Arith
public import CFSG.GroupTheory.WeirSylow.SylowTransfer
public import CFSG.GroupTheory.WeirSylow.FormSpace
public import CFSG.GroupTheory.WeirSylow.FieldTorus
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
public import Mathlib.FieldTheory.Finite.Extension

public section

namespace CFSG.GroupTheory.WeirSylow

open Module Finset

theorem nonempty_sylow_mulEquiv_sigmaModel {p : ℕ} [Fact p.Prime] {G : Type*} [Group G]
    [Finite G] {e a N : ℕ} (φ : sigmaModel p e a N →* G) (hφ : Function.Injective φ)
    (hG : (Nat.card G).factorization p = a * (N / e) + padicValNat p (N / e).factorial)
    (P : Sylow p G) : Nonempty (P ≃* sigmaModel p e a N) :=
  nonempty_sylow_mulEquiv_of_injective φ hφ (by rw [card_sigmaModel, hG]) P

theorem prod_fin_pow_sub_one (c : ℤ) (n : ℕ) :
    ∏ i : Fin n, (c ^ (n - (i : ℕ)) - 1) = ∏ j ∈ Icc 1 n, (c ^ j - 1) := by
  rw [Fin.prod_univ_eq_prod_range (fun i => c ^ (n - i) - 1) n]
  refine Finset.prod_nbij' (fun i => n - i) (fun j => n - j) (fun i hi => ?_) (fun j hj => ?_)
    (fun i hi => ?_) (fun j hj => ?_) (fun i _ => rfl)
  all_goals simp only [Finset.mem_range, Finset.mem_Icc] at *
  all_goals omega

theorem natCard_GL_cast (K : Type*) [Field K] [Fintype K] (n : ℕ) :
    (Nat.card (GL (Fin n) K) : ℤ) = (∏ i : Fin n, (Fintype.card K : ℤ) ^ (i : ℕ)) *
      ∏ j ∈ Icc 1 n, ((Fintype.card K : ℤ) ^ j - 1) := by
  rw [Matrix.card_GL_field, Nat.cast_prod, ← prod_fin_pow_sub_one, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  have hq : 1 ≤ Fintype.card K := Fintype.card_pos
  rw [Nat.cast_sub (Nat.pow_le_pow_right hq i.2.le), Nat.cast_pow, Nat.cast_pow, mul_sub,
    mul_one, ← pow_add, Nat.add_sub_cancel' i.2.le]

theorem padicValInt_natCast_pow_sub_one (p : ℕ) {q : ℕ} (hq : 1 ≤ q) (k : ℕ) :
    padicValInt p ((q : ℤ) ^ k - 1) = padicValNat p (q ^ k - 1) := by
  rw [← padicValInt.of_nat, Nat.cast_sub (Nat.one_le_pow _ _ hq), Nat.cast_pow, Nat.cast_one]

theorem factorization_card_GL {p : ℕ} [hp : Fact p.Prime] (hp1 : Odd p) (K : Type*) [Field K]
    [Fintype K] (hpK : ¬ p ∣ Fintype.card K) (n : ℕ) :
    (Nat.card (GL (Fin n) K)).factorization p =
      padicValNat p (Fintype.card K ^ orderOf (Fintype.card K : ZMod p) - 1) *
          (n / orderOf (Fintype.card K : ZMod p)) +
        padicValNat p (n / orderOf (Fintype.card K : ZMod p)).factorial := by
  have hq : 1 < Fintype.card K := Fintype.one_lt_card
  have hc : ¬ (p : ℤ) ∣ (Fintype.card K : ℤ) := by exact_mod_cast hpK
  have hc2 : 2 ≤ |(Fintype.card K : ℤ)| := by
    rw [abs_of_nonneg (by positivity)]
    exact_mod_cast hq
  have hu : ¬ (p : ℤ) ∣ ∏ i : Fin n, (Fintype.card K : ℤ) ^ (i : ℕ) := by
    intro h
    obtain ⟨i, -, hi⟩ := ((Nat.prime_iff_prime_int.mp hp.out).dvd_finsetProd_iff _).1 h
    exact hc ((Nat.prime_iff_prime_int.mp hp.out).dvd_of_dvd_pow hi)
  rw [factorization_eq_of_cast_eq_mul_prod hp1 hc hc2 (natCard_GL_cast K n) hu, ordMod_natCast,
    padicValInt_natCast_pow_sub_one p hq.le]

section GeneralLinear

variable (K : Type) [Field K]

@[expose] noncomputable def isomToGL (S : FormSpace K PUnit) {n : ℕ}
    (hS : finrank K S.V = n) : S.isom →* GL (Fin n) K :=
  (Matrix.GeneralLinearGroup.toLin.symm.toMonoidHom).comp
    ((LinearMap.GeneralLinearGroup.generalLinearEquiv K (Fin n → K)).symm.toMonoidHom.comp
      ((formIsometryGroup K (fun (_ _ : Fin n → K) => PUnit.unit)).subtype.comp
        (formIsometryGroupCongr (F' := fun _ _ => PUnit.unit)
          (LinearEquiv.ofFinrankEq S.V (Fin n → K) (by rw [hS, Module.finrank_fin_fun]))
          (fun _ _ => Subsingleton.elim _ _)).toMonoidHom))

theorem isomToGL_injective (S : FormSpace K PUnit) {n : ℕ} (hS : finrank K S.V = n) :
    Function.Injective (isomToGL K S hS) :=
  Matrix.GeneralLinearGroup.toLin.symm.injective.comp
    ((LinearMap.GeneralLinearGroup.generalLinearEquiv K _).symm.injective.comp
      (Subtype.val_injective.comp (MulEquiv.injective _)))

theorem exists_injective_sigmaModel_GL {p : ℕ} [hp : Fact p.Prime] [Finite K] {e a : ℕ}
    (he : 0 < e) (ha : p ^ a ∣ Nat.card K ^ e - 1) (n : ℕ) :
    ∃ φ : sigmaModel p e a n →* GL (Fin n) K, Function.Injective φ := by
  have : NeZero e := ⟨he.ne'⟩
  have : NeZero p := ⟨hp.out.ne_zero⟩
  have : NeZero (p ^ a) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
  have : Fact (ringChar K).Prime := ⟨CharP.char_is_prime K _⟩
  let L := FiniteField.Extension K (ringChar K) e
  obtain ⟨ζ, hζ⟩ := exists_units_orderOf_eq (L := L) (d := p ^ a)
    (by rwa [FiniteField.natCard_extension])
  let S₀ : FormSpace K PUnit := ⟨L, fun _ _ => PUnit.unit⟩
  have hmem : DistribMulAction.toModuleAut K L ζ ∈ S₀.isom := fun _ _ => rfl
  obtain ⟨ρ, hρ⟩ := exists_injective_hom_of_orderOf_eq hmem
    (by rw [orderOf_toModuleAut, hζ])
  obtain ⟨S, -, hSdim, φ, hφ⟩ := exists_sigmaModel_rep p (fun _ => True)
    (fun _ _ _ _ => trivial) S₀ trivial (inferInstanceAs (Nontrivial L)) ρ hρ e n
  let T : FormSpace K PUnit := ⟨Fin (n - e * (n / e)) → K, fun _ _ => PUnit.unit⟩
  obtain ⟨ψ, hψ⟩ := exists_rep_prod S T φ hφ
  have hdim : finrank K (S.prod T).V = n := by
    rw [FormSpace.finrank_prod, hSdim]
    change finrank K L * (n / e) + finrank K (Fin (n - e * (n / e)) → K) = n
    rw [Module.finrank_fin_fun, FiniteField.finrank_extension]
    have := Nat.mul_div_le n e
    omega
  exact ⟨(isomToGL K _ hdim).comp ψ, (isomToGL_injective K _ hdim).comp hψ⟩

end GeneralLinear

theorem sylow_GL {p : ℕ} [hp : Fact p.Prime] (hp1 : Odd p) (K : Type) [Field K] [Fintype K]
    (hpK : ¬ p ∣ Fintype.card K) (n : ℕ) (P : Sylow p (GL (Fin n) K)) :
    Nonempty (P ≃* sigmaModel p (orderOf (Fintype.card K : ZMod p))
      (padicValNat p (Fintype.card K ^ orderOf (Fintype.card K : ZMod p) - 1)) n) := by
  have he : 0 < orderOf (Fintype.card K : ZMod p) := by
    rw [← ordMod_natCast]
    exact ordMod_pos (c := (Fintype.card K : ℤ)) (by exact_mod_cast hpK)
  obtain ⟨φ, hφ⟩ := exists_injective_sigmaModel_GL K (p := p) he
    (a := padicValNat p (Fintype.card K ^ orderOf (Fintype.card K : ZMod p) - 1))
    (by rw [Nat.card_eq_fintype_card]; exact pow_padicValNat_dvd) n
  exact nonempty_sylow_mulEquiv_sigmaModel φ hφ (factorization_card_GL hp1 K hpK n) P

end CFSG.GroupTheory.WeirSylow
