module

public import CFSG.CGT.PushingUpLit.CGT6.SixFourIdent
public import CFSG.LocalAnalysis.ComponentClassification.SymmetricLocalLinearFourTwo

public section

namespace CFSG.CGT.PushingUpLit.CGT6

open CFSG CFSG.RankThree.PartOne CFSG.CGT.PushingUp CFSG.CGT.PushingUpLit
open CFSG.Assembly.LowTwoRank (StatedClassicalModel StatedLieTag)
open Matrix Equiv
open scoped MatrixGroups

theorem sign_eq_neg_one_of_inv_seven {g t : Perm (Fin 8)} (hg : orderOf g = 7) (ht : t * t = 1)
    (hconj : t * g * t = g⁻¹) : Perm.sign t = -1 := by
  classical
  have hg7 : Nat.Prime (orderOf g) := by rw [hg]; norm_num
  have hcyc : g.IsCycle := Perm.isCycle_of_prime_order' hg7 (by rw [hg]; simp)
  have hsupp : g.support.card = 7 := by rw [← hcyc.orderOf]; exact hg
  have hcompl : g.supportᶜ.card = 1 := by
    rw [Finset.card_compl, hsupp]; simp
  obtain ⟨p, hp⟩ := Finset.card_eq_one.mp hcompl
  have hgfix : ∀ x, g x = x ↔ x = p := by
    intro x
    have : x ∈ g.supportᶜ ↔ x = p := by rw [hp]; simp
    rw [Finset.mem_compl, Perm.mem_support, not_not] at this
    exact this
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  have hconj_pow : ∀ i : ℕ, t * g ^ i * t = (g ^ i)⁻¹ := by
    intro i
    have := conj_pow (a := t) (b := g) (i := i)
    rw [htinv, hconj, inv_pow] at this
    exact this.symm
  have htt : ∀ x, t (t x) = x := fun x => by
    have := congrArg (fun f : Perm (Fin 8) => f x) ht
    simpa using this
  have hτx : ∀ (i : ℕ) (x : Fin 8), t ((g ^ i) x) = ((g ^ i)⁻¹) (t x) := by
    intro i x
    have := congrArg (fun f : Perm (Fin 8) => f (t x)) (hconj_pow i)
    simp only [Perm.mul_apply, htt] at this
    exact this
  have htp : t p = p := by
    have h1 := hτx 1 p
    rw [pow_one, (hgfix p).mpr rfl] at h1
    have h2 : g (t p) = t p := by
      conv_lhs => rw [h1]
      simp
    exact (hgfix _).mp h2
  have huniq : ∀ x y, x ≠ p → y ≠ p → t x = x → t y = y → y = x := by
    intro x y hx hy htx hty
    have hgx : g x ≠ x := fun h => hx ((hgfix x).mp h)
    have hgy : g y ≠ y := fun h => hy ((hgfix y).mp h)
    obtain ⟨i, hi⟩ := hcyc.exists_pow_eq hgx hgy
    have h1 : y = ((g ^ i)⁻¹) x := by
      have := hτx i x
      rw [hi, hty, htx] at this
      exact this
    have h2 : (g ^ (i + i)) x = x := by
      rw [pow_add, Perm.mul_apply, hi]
      conv_lhs => rw [h1]
      simp
    have h3 : g ^ (i + i) = 1 := hcyc.pow_eq_one_iff.mpr ⟨x, hgx, h2⟩
    have h4 : 7 ∣ i + i := hg ▸ orderOf_dvd_of_pow_eq_one h3
    have h5 : g ^ i = 1 := by
      apply orderOf_dvd_iff_pow_eq_one.mp
      rw [hg]; omega
    rw [← hi, h5]; rfl
  have ht2 : t ^ 2 = 1 := by rw [sq]; exact ht
  have hmod : t.supportᶜ.card ≡ Fintype.card (Fin 8) [MOD 2] := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact Perm.card_compl_support_modEq (p := 2) (n := 1) (by simpa using ht2)
  have hpF : p ∈ t.supportᶜ := by
    rw [Finset.mem_compl, Perm.mem_support, not_not]; exact htp
  have hcard1 : 1 ≤ t.supportᶜ.card := Finset.card_pos.mpr ⟨p, hpF⟩
  have heven : t.supportᶜ.card % 2 = 0 := by
    have := hmod; simp [Nat.ModEq] at this; omega
  obtain ⟨q, hqF, hqp⟩ := Finset.exists_mem_ne (s := t.supportᶜ) (by omega) p
  have hsub : t.supportᶜ ⊆ {p, q} := by
    intro y hy
    rw [Finset.mem_insert, Finset.mem_singleton]
    by_cases hyp : y = p
    · exact Or.inl hyp
    · refine Or.inr (huniq q y hqp hyp ?_ ?_)
      · rwa [Finset.mem_compl, Perm.mem_support, not_not] at hqF
      · rwa [Finset.mem_compl, Perm.mem_support, not_not] at hy
  have hle : t.supportᶜ.card ≤ 2 := (Finset.card_le_card hsub).trans Finset.card_le_two
  have hF2 : t.supportᶜ.card = 2 := by omega
  have hfp : Fintype.card (Function.fixedPoints t) = t.supportᶜ.card := by
    rw [Perm.card_fixedPoints, Perm.sum_cycleType, Finset.card_compl]
  rw [Perm.sign_of_pow_two_eq_one ht2, hfp, hF2]
  norm_num

@[expose] def eightTorus (K : Type*) [Field K] : Kˣ →* SL(2, K) where
  toFun a := ⟨!![(a : K), 0; 0, ((a⁻¹ : Kˣ) : K)], by
    rw [Matrix.det_fin_two_of]; simp⟩
  map_one' := by
    apply Subtype.ext
    change !![((1 : Kˣ) : K), 0; 0, (((1 : Kˣ)⁻¹ : Kˣ) : K)] = 1
    ext i j; fin_cases i <;> fin_cases j <;> simp
  map_mul' a b := by
    apply Subtype.ext
    change !![((a * b : Kˣ) : K), 0; 0, (((a * b)⁻¹ : Kˣ) : K)] =
      !![(a : K), 0; 0, ((a⁻¹ : Kˣ) : K)] * !![(b : K), 0; 0, ((b⁻¹ : Kˣ) : K)]
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, mul_comm]

theorem coe_eightTorus {K : Type*} [Field K] (a : Kˣ) :
    ((eightTorus K a : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) =
      !![(a : K), 0; 0, ((a⁻¹ : Kˣ) : K)] := rfl

theorem eightTorus_injective (K : Type*) [Field K] : Function.Injective (eightTorus K) := by
  rw [injective_iff_map_eq_one]
  intro a ha
  have := congrArg (fun M : SL(2, K) => (M : Matrix (Fin 2) (Fin 2) K) 0 0) ha
  simp only [coe_eightTorus, Matrix.of_apply] at this
  exact Units.ext (by simpa using this)

@[expose] def eightWeyl (K : Type*) [Field K] [CharP K 2] : SL(2, K) :=
  ⟨!![0, 1; 1, 0], by
    rw [Matrix.det_fin_two_of]
    simp [CharTwo.neg_eq]⟩

theorem eightWeyl_mul_self (K : Type*) [Field K] [CharP K 2] : eightWeyl K * eightWeyl K = 1 := by
  apply Subtype.ext
  change !![(0 : K), 1; 1, 0] * !![(0 : K), 1; 1, 0] = 1
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem eightWeyl_conj_eightTorus (K : Type*) [Field K] [CharP K 2] (a : Kˣ) :
    eightWeyl K * eightTorus K a * eightWeyl K = (eightTorus K a)⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  apply Subtype.ext
  change !![(0 : K), 1; 1, 0] * !![(a : K), 0; 0, ((a⁻¹ : Kˣ) : K)] * !![(0 : K), 1; 1, 0] *
    !![(a : K), 0; 0, ((a⁻¹ : Kˣ) : K)] = 1
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, mul_comm]

theorem exists_torus_inv (K : Type*) [Field K] [Finite K] [CharP K 2] :
    ∃ g w : SL(2, K), orderOf g = Nat.card K - 1 ∧ w * w = 1 ∧ w * g * w = g⁻¹ := by
  obtain ⟨a, ha⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := Kˣ)
  refine ⟨eightTorus K a, eightWeyl K, ?_, eightWeyl_mul_self K, eightWeyl_conj_eightTorus K a⟩
  rw [orderOf_injective (eightTorus K) (eightTorus_injective K) a, ha, Nat.card_units]

theorem not_injective_sl2_eight_alt (F : SL(2, GaloisField 2 3) →* alternatingGroup (Fin 8)) :
    ¬ Function.Injective F := by
  intro hF
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcard : Nat.card (GaloisField 2 3) = 8 := by
    rw [GaloisField.card 2 3 (by norm_num)]; norm_num
  obtain ⟨g, w, hg, hw, hgw⟩ := exists_torus_inv (GaloisField 2 3)
  rw [hcard] at hg
  have hg7 : orderOf (F g : Perm (Fin 8)) = 7 := by
    rw [Subgroup.orderOf_coe, orderOf_injective F hF g, hg]
  have hww : (F w : Perm (Fin 8)) * (F w : Perm (Fin 8)) = 1 := by
    rw [← Subgroup.coe_mul, ← map_mul, hw, map_one]; rfl
  have hconj : (F w : Perm (Fin 8)) * (F g : Perm (Fin 8)) * (F w : Perm (Fin 8)) =
      (F g : Perm (Fin 8))⁻¹ := by
    rw [← Subgroup.coe_mul, ← Subgroup.coe_mul, ← map_mul, ← map_mul, hgw, map_inv]; rfl
  have hsign := sign_eq_neg_one_of_inv_seven hg7 hww hconj
  have hmem : (F w : Perm (Fin 8)) ∈ alternatingGroup (Fin 8) := (F w).2
  rw [Perm.mem_alternatingGroup] at hmem
  rw [hmem] at hsign
  exact absurd hsign (by decide)

variable {G : Type} [Group G] [Finite G]

theorem eight_sl_not_alt8 {Y R : Subgroup G} {T : Sylow 2 G} [R.Normal] (h : EightCtx Y T R) {n : ℕ}
    (hn : 1 ≤ n) (hnat : IsNaturalSLTwoModule ↥Y n)
    (hS : CFSG.CGT.Timmesfeld75.SimpleCaseListStmt) (h215 : CFSG.CGT.Timmesfeld75.Lemma215Stmt)
    (hL : CFSG.CGT.Timmesfeld75.ListWCIdentification)
    (hA : Nonempty (↥(jBarClosure R T) ⧸ Subgroup.center ↥(jBarClosure R T) ≃*
      alternatingGroup (Fin 8))) : False := by
  obtain ⟨hn2, -, -, hstd, hcardTh, -, ρ, ι', -, -, hinj, -⟩ := eight_sl_ident h hn hnat hS h215 hL
  have h8 := hstd.card_alternating (k := 8) (by norm_num) (by norm_num) hA
  have hn3 : n = 3 := by
    have h2n : 2 ^ n = 2 ^ 3 := by
      rw [← hcardTh, h8]; norm_num
    exact Nat.pow_right_injective (le_refl 2) h2n
  subst hn3
  obtain ⟨φ, -⟩ := hnat
  obtain ⟨e⟩ := hA
  refine not_injective_sl2_eight_alt (e.toMonoidHom.comp (ι'.comp φ.symm.toMonoidHom)) ?_
  exact e.injective.comp (hinj.comp φ.symm.injective)

theorem nonempty_mulEquiv_alt_eight_of_psl_four_two {Q : Type} [Group Q]
    (h : StatedClassicalModel Q StatedLieTag.PSL 4 2 1) :
    Nonempty (Q ≃* alternatingGroup (Fin 8)) :=
  (CFSG.ComponentClassification.SymmetricLocal.lie_model_linear_four_two_iff Q).mp (Or.inl ⟨by decide, h⟩)

theorem eight_sl_not_psl_four_two {Y R : Subgroup G} {T : Sylow 2 G} [R.Normal] (h : EightCtx Y T R)
    {n : ℕ} (hn : 1 ≤ n) (hnat : IsNaturalSLTwoModule ↥Y n)
    (hS : CFSG.CGT.Timmesfeld75.SimpleCaseListStmt) (h215 : CFSG.CGT.Timmesfeld75.Lemma215Stmt)
    (hL : CFSG.CGT.Timmesfeld75.ListWCIdentification)
    (hf : StatedClassicalModel (↥(jBarClosure R T) ⧸ Subgroup.center ↥(jBarClosure R T))
      StatedLieTag.PSL 4 2 1) : False :=
  eight_sl_not_alt8 h hn hnat hS h215 hL (nonempty_mulEquiv_alt_eight_of_psl_four_two hf)

end CFSG.CGT.PushingUpLit.CGT6
