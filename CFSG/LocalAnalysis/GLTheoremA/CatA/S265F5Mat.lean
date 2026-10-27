module

public import CFSG.RankThree.PartOne.CTP.SeitzDiag
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.RingTheory.Etale.Weakly
public import Mathlib.RingTheory.TotallySplit
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S265F5

open Matrix

section Diag

variable {F : Type*} [Field F] {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem apply_eq_zero_of_diagonal_mul_comm {d : ι → F} {N : Matrix ι ι F}
    (h : diagonal d * N = N * diagonal d) {i j : ι} (hij : d i ≠ d j) : N i j = 0 := by
  have h1 := congrFun (congrFun h i) j
  rw [diagonal_mul, mul_diagonal] at h1
  have h0 : (d i - d j) * N i j = 0 := by linear_combination h1
  exact (mul_eq_zero.1 h0).resolve_left (sub_ne_zero.2 hij)

theorem eq_zero_of_diagonal_comm_of_mul_self_eq_zero {d : ι → F} (hd : Function.Injective d)
    {N : Matrix ι ι F} (hc : diagonal d * N = N * diagonal d) (hN : N * N = 0) : N = 0 := by
  have hoff : ∀ i j, i ≠ j → N i j = 0 := fun i j hij =>
    apply_eq_zero_of_diagonal_mul_comm hc (hd.ne hij)
  ext i j
  by_cases hij : i = j
  · subst hij
    have h1 : (N * N) i i = 0 := by rw [hN, Matrix.zero_apply]
    rw [mul_apply, Finset.sum_eq_single i (fun l _ hl => by rw [hoff i l (Ne.symm hl), zero_mul])
      (fun h => absurd (Finset.mem_univ i) h)] at h1
    rw [Matrix.zero_apply]
    exact mul_self_eq_zero.1 h1
  · rw [hoff i j hij, Matrix.zero_apply]

theorem injective_of_mul_diagonal_eq_smul {p : ℕ} (hp : p.Prime) (hcard : Fintype.card ι < 2 * p)
    {d : ι → F} (hd0 : ∀ i, d i ≠ 0) {lam : F} (hlamp : lam ^ p = 1) (hlam1 : lam ≠ 1)
    {X : Matrix ι ι F} (hX : IsUnit X.det) (hXD : X * diagonal d = lam • (diagonal d * X)) :
    Function.Injective d := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  have hlam0 : lam ≠ 0 := by
    rintro rfl
    rw [zero_pow hp.ne_zero] at hlamp
    exact zero_ne_one hlamp
  have hstep : ∀ c : F, (Finset.univ.filter fun i => d i = c).card =
      (Finset.univ.filter fun i => d i = lam⁻¹ * c).card := by
    intro c
    have hE : X * diagonal (fun i => d i - c) = diagonal (fun i => lam * d i - c) * X := by
      ext i j
      have h1 := congrFun (congrFun hXD i) j
      rw [mul_diagonal, Matrix.smul_apply, diagonal_mul, smul_eq_mul] at h1
      rw [mul_diagonal, diagonal_mul]
      linear_combination h1
    have hr : (diagonal (fun i => d i - c)).rank = (diagonal (fun i => lam * d i - c)).rank := by
      rw [← rank_mul_eq_right_of_isUnit_det X _ hX, hE, rank_mul_eq_left_of_isUnit_det X _ hX]
    rw [rank_diagonal, rank_diagonal, Fintype.card_subtype, Fintype.card_subtype] at hr
    have h1 := Finset.card_filter_add_card_filter_not (s := Finset.univ) (fun i => d i - c ≠ 0)
    have h2 := Finset.card_filter_add_card_filter_not (s := Finset.univ)
      (fun i => lam * d i - c ≠ 0)
    have e1 : (Finset.univ.filter fun i => ¬ (d i - c ≠ 0)) =
        Finset.univ.filter fun i => d i = c := by
      ext i
      simp [sub_eq_zero]
    have e2 : (Finset.univ.filter fun i => ¬ (lam * d i - c ≠ 0)) =
        Finset.univ.filter fun i => d i = lam⁻¹ * c := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_not, sub_eq_zero]
      constructor
      · intro h
        rw [← h, inv_mul_cancel_left₀ hlam0]
      · intro h
        rw [h, mul_inv_cancel_left₀ hlam0]
    rw [e1] at h1
    rw [e2] at h2
    omega
  have hord : orderOf lam = p := orderOf_eq_prime hlamp hlam1
  intro a a' haa'
  by_contra hne
  have hpow : ∀ j : ℕ, (Finset.univ.filter fun i => d i = lam ^ j * d a).card =
      (Finset.univ.filter fun i => d i = d a).card := by
    intro j
    induction j with
    | zero => rw [pow_zero, one_mul]
    | succ j ih =>
      rw [hstep (lam ^ (j + 1) * d a), ← ih, pow_succ', mul_assoc, inv_mul_cancel_left₀ hlam0]
  have hdisj : ((Finset.range p : Finset ℕ) : Set ℕ).PairwiseDisjoint
      (fun j => Finset.univ.filter fun i => d i = lam ^ j * d a) := by
    intro j hj j' hj' hjj'
    simp only [Function.onFun]
    rw [Finset.disjoint_filter]
    intro i _ h1 h2
    apply hjj'
    have h3 : lam ^ j = lam ^ j' := mul_right_cancel₀ (hd0 a) (h1.symm.trans h2)
    have hj1 : j ∈ Set.Iio (orderOf lam) := by
      rw [Set.mem_Iio, hord]
      exact Finset.mem_range.1 (Finset.mem_coe.1 hj)
    have hj2 : j' ∈ Set.Iio (orderOf lam) := by
      rw [Set.mem_Iio, hord]
      exact Finset.mem_range.1 (Finset.mem_coe.1 hj')
    exact pow_injOn_Iio_orderOf hj1 hj2 h3
  have hsum : p * (Finset.univ.filter fun i => d i = d a).card ≤ Fintype.card ι := by
    have h1 := Finset.card_le_univ
      ((Finset.range p).biUnion fun j => Finset.univ.filter fun i => d i = lam ^ j * d a)
    rw [Finset.card_biUnion hdisj, Finset.sum_congr rfl (fun j _ => hpow j), Finset.sum_const,
      Finset.card_range, smul_eq_mul] at h1
    exact h1
  have h2 : 2 ≤ (Finset.univ.filter fun i => d i = d a).card := by
    have hsub : ({a, a'} : Finset ι) ⊆ Finset.univ.filter fun i => d i = d a := by
      intro i hi
      simp only [Finset.mem_insert, Finset.mem_singleton] at hi
      rcases hi with rfl | rfl
      · simp
      · simp [haa']
    calc 2 = ({a, a'} : Finset ι).card := (Finset.card_pair hne).symm
      _ ≤ _ := Finset.card_le_card hsub
  have h3 : p * 2 ≤ p * (Finset.univ.filter fun i => d i = d a).card := Nat.mul_le_mul_left p h2
  omega

end Diag

section Root

variable {F : Type*} [Field F] {n : ℕ}

theorem exists_pow_eq_of_comm_of_mul_self_eq_zero {p : ℕ} (hp : p.Prime) (hn : n < 2 * p)
    {M N : Matrix (Fin n) (Fin n) F} {a : F} (hM : M ^ p = scalar (Fin n) a) (hMN : M * N = N * M)
    (hN0 : N ≠ 0) (hN : N * N = 0) : ∃ θ : F, θ ^ p = a := by
  classical
  by_cases ha : a = 0
  · exact ⟨0, by rw [ha, zero_pow hp.ne_zero]⟩
  set W : Submodule F (Fin n → F) := LinearMap.range N.mulVecLin with hW
  have hMW : ∀ x ∈ W, M.mulVecLin x ∈ W := by
    intro x hx
    obtain ⟨y, rfl⟩ := LinearMap.mem_range.1 hx
    refine LinearMap.mem_range.2 ⟨M.mulVecLin y, ?_⟩
    simp only [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, hMN]
  set f : W →ₗ[F] W := M.mulVecLin.restrict hMW with hf
  have hw0 : Module.finrank F W ≠ 0 := by
    intro h0
    apply hN0
    have hbot : W = ⊥ := Submodule.finrank_eq_zero.1 h0
    ext i j
    have hv : N *ᵥ Pi.single j 1 ∈ W := LinearMap.mem_range.2 ⟨Pi.single j 1, rfl⟩
    rw [hbot, Submodule.mem_bot] at hv
    have := congrFun hv i
    simpa [Matrix.mulVec_single_one] using this
  have hle : W ≤ LinearMap.ker N.mulVecLin := by
    intro x hx
    obtain ⟨y, rfl⟩ := LinearMap.mem_range.1 hx
    rw [LinearMap.mem_ker, Matrix.mulVecLin_apply, Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, hN,
      Matrix.zero_mulVec]
  have hrk := LinearMap.finrank_range_add_finrank_ker N.mulVecLin
  rw [Module.finrank_fin_fun] at hrk
  have hmono := Submodule.finrank_mono hle
  have hwp : Module.finrank F W < p := by
    have : Module.finrank F W + Module.finrank F W ≤ n := by
      calc Module.finrank F W + Module.finrank F W
          ≤ Module.finrank F W + Module.finrank F (LinearMap.ker N.mulVecLin) :=
            Nat.add_le_add_left hmono _
        _ = n := hrk
    omega
  have hpowv : ∀ (k : ℕ) (x : Fin n → F), (M.mulVecLin ^ k) x = (M ^ k) *ᵥ x := by
    intro k
    induction k with
    | zero =>
      intro x
      rw [pow_zero, pow_zero, Module.End.one_apply, Matrix.one_mulVec]
    | succ k ih =>
      intro x
      rw [pow_succ, Module.End.mul_apply, ih, Matrix.mulVecLin_apply, pow_succ,
        Matrix.mulVec_mulVec]
  have hfp : f ^ p = a • (1 : Module.End F W) := by
    rw [hf, Module.End.pow_restrict]
    refine LinearMap.ext fun x => Subtype.ext ?_
    rw [LinearMap.coe_restrict_apply, hpowv, hM, LinearMap.smul_apply, Module.End.one_apply,
      Submodule.coe_smul, Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal, Matrix.smul_mulVec,
      Matrix.one_mulVec]
  have hdet : LinearMap.det f ^ p = a ^ Module.finrank F W := by
    rw [← map_pow, hfp, LinearMap.det_smul, map_one, mul_one]
  set w := Module.finrank F W with hwdef
  have hcop : Nat.Coprime w p :=
    Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hp).2
      (Nat.not_dvd_of_pos_of_lt (Nat.pos_of_ne_zero hw0) hwp))
  obtain ⟨u, -, hu⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop hp.one_lt
  have hwu : w * u = p * (w * u / p) + 1 := by
    have := Nat.div_add_mod (w * u) p
    omega
  set v := w * u / p with hv
  have h1 : (LinearMap.det f ^ u) ^ p = a ^ (w * u) := by
    rw [← pow_mul, mul_comm u p, pow_mul, hdet, ← pow_mul]
  refine ⟨LinearMap.det f ^ u / a ^ v, ?_⟩
  rw [div_pow, h1, hwu, pow_succ, ← pow_mul, mul_comm v p]
  exact mul_div_cancel_left₀ a (pow_ne_zero _ ha)

end Root

section GLLemmas

variable {F : Type*} [Field F] {n : ℕ}

theorem sub_one_mul_self_eq_zero [CharP F 2] {u : GL (Fin n) F} (hu2 : u * u = 1) :
    ((u : Matrix (Fin n) (Fin n) F) - 1) * ((u : Matrix (Fin n) (Fin n) F) - 1) = 0 := by
  have h2 : (2 : F) = 0 := CharP.cast_eq_zero F 2
  have hu : (u : Matrix (Fin n) (Fin n) F) * u = 1 := by rw [← Units.val_mul, hu2, Units.val_one]
  have e : ((u : Matrix (Fin n) (Fin n) F) - 1) * ((u : Matrix (Fin n) (Fin n) F) - 1) =
      (2 : F) • (1 - (u : Matrix (Fin n) (Fin n) F)) := by
    rw [sub_mul, mul_sub, mul_sub, hu, mul_one, one_mul, one_mul, two_smul]
    abel
  rw [e, h2, zero_smul]

theorem not_injective_of_conj_eq_diagonal [CharP F 2] {M u R : GL (Fin n) F} (hu1 : u ≠ 1)
    (hu2 : u * u = 1) (hMu : M * u = u * M) {d : Fin n → F}
    (hR : ((R * M * R⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = diagonal d) :
    ¬ Function.Injective d := by
  intro hd
  set W := R * u * R⁻¹ with hW
  have hWd : diagonal d * (W : Matrix (Fin n) (Fin n) F) =
      (W : Matrix (Fin n) (Fin n) F) * diagonal d := by
    rw [← hR, ← Units.val_mul, ← Units.val_mul]
    congr 1
    rw [hW]
    calc R * M * R⁻¹ * (R * u * R⁻¹) = R * (M * u) * R⁻¹ := by group
      _ = R * (u * M) * R⁻¹ := by rw [hMu]
      _ = R * u * R⁻¹ * (R * M * R⁻¹) := by group
  have hW2 : W * W = 1 := by
    rw [hW]
    calc R * u * R⁻¹ * (R * u * R⁻¹) = R * (u * u) * R⁻¹ := by group
      _ = 1 := by rw [hu2]; group
  have h0 := eq_zero_of_diagonal_comm_of_mul_self_eq_zero hd
    (N := (W : Matrix (Fin n) (Fin n) F) - 1) (by rw [mul_sub, sub_mul, hWd, mul_one, one_mul])
    (sub_one_mul_self_eq_zero hW2)
  apply hu1
  have hW1 : W = 1 := Units.ext (sub_eq_zero.1 h0)
  calc u = R⁻¹ * W * R := by rw [hW]; group
    _ = 1 := by rw [hW1]; group

theorem exists_pow_eq_of_comm_involution [CharP F 2] {p : ℕ} (hp : p.Prime) (hn : n < 2 * p)
    {M u : GL (Fin n) F} (hu1 : u ≠ 1) (hu2 : u * u = 1) (hMu : M * u = u * M) {a : Fˣ}
    (ha : M ^ p = GeneralLinearGroup.scalar (Fin n) a) : ∃ θ : Fˣ, θ ^ p = a := by
  have hMm : (M : Matrix (Fin n) (Fin n) F) ^ p = scalar (Fin n) (a : F) := by
    rw [← Units.val_pow_eq_pow_val, ha, GeneralLinearGroup.coe_scalar]
  have hMN : (M : Matrix (Fin n) (Fin n) F) * ((u : Matrix (Fin n) (Fin n) F) - 1) =
      ((u : Matrix (Fin n) (Fin n) F) - 1) * M := by
    rw [mul_sub, sub_mul, ← Units.val_mul, ← Units.val_mul, hMu, mul_one, one_mul]
  have hN0 : (u : Matrix (Fin n) (Fin n) F) - 1 ≠ 0 := fun h =>
    hu1 (Units.ext (by rw [Units.val_one]; exact sub_eq_zero.1 h))
  obtain ⟨θ, hθ⟩ := exists_pow_eq_of_comm_of_mul_self_eq_zero hp hn hMm hMN hN0
    (sub_one_mul_self_eq_zero hu2)
  have hθ0 : θ ≠ 0 := by
    rintro rfl
    rw [zero_pow hp.ne_zero] at hθ
    exact a.ne_zero hθ.symm
  exact ⟨Units.mk0 θ hθ0, Units.ext (by rw [Units.val_pow_eq_pow_val, Units.val_mk0, hθ])⟩

theorem exists_conj_eq_diagonal_of_pow_eq_one {p : ℕ} (hp : p.Prime) {ζ : F}
    (hζ : IsPrimitiveRoot ζ p) {M : GL (Fin n) F} (hMp : M ^ p = 1) :
    ∃ (A : GL (Fin n) F) (d : Fin n → F),
      ((A * M * A⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = diagonal d := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨A, hA⟩ := CFSG.RankThree.PartOne.CTP.exists_conj_diagonal_of_exponent_prime ⟨ζ, hζ⟩
    (Subgroup.zpowers M)
    (fun x hx y hy => by
      obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
      obtain ⟨m', rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
      exact (Commute.zpow_zpow_self M m m').eq)
    (fun x hx => orderOf_dvd_iff_pow_eq_one.1
      ((orderOf_dvd_of_mem_zpowers hx).trans (orderOf_dvd_of_pow_eq_one hMp)))
  refine ⟨A, fun l => ((A * M * A⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) l l, ?_⟩
  ext i j
  by_cases hij : i = j
  · subst hij
    rw [diagonal_apply_eq]
  · rw [diagonal_apply_ne _ hij]
    exact hA M (Subgroup.mem_zpowers M) i j hij

theorem diagonal_pow_eq_one {p : ℕ} {A M : GL (Fin n) F} {d : Fin n → F} (hMp : M ^ p = 1)
    (hd : ((A * M * A⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = diagonal d) (l : Fin n) :
    d l ^ p = 1 := by
  have h1 : (A * M * A⁻¹ : GL (Fin n) F) ^ p = 1 := by rw [conj_pow, hMp]; group
  have h2 := congrArg (fun g : GL (Fin n) F => (g : Matrix (Fin n) (Fin n) F) l l) h1
  simp only [Units.val_pow_eq_pow_val, hd, diagonal_pow, diagonal_apply_eq, Units.val_one,
    one_apply_eq] at h2
  exact h2

theorem eq_one_of_map_eq_mul_scalar [CharP F 2] {p : ℕ} (hp : p.Prime) (hn : n < 2 * p)
    {ζ : F} (hζ : IsPrimitiveRoot ζ p) {σ : F ≃+* F} (hσ : ∀ x : F, x ^ p = 1 → σ x = x)
    {M u : GL (Fin n) F} (hu1 : u ≠ 1) (hu2 : u * u = 1) (hMu : M * u = u * M) (hMp : M ^ p = 1)
    {lam : Fˣ}
    (hσM : GeneralLinearGroup.map (σ : F →+* F) M = M * GeneralLinearGroup.scalar (Fin n) lam) :
    lam = 1 := by
  classical
  have hn0 : 0 < n := by
    rcases Nat.eq_zero_or_pos n with rfl | h
    · exact absurd (Units.ext (Subsingleton.elim _ _)) hu1
    · exact h
  have hlamp : lam ^ p = 1 := by
    have hc : Commute M (GeneralLinearGroup.scalar (Fin n) lam) :=
      (GeneralLinearGroup.scalar_commute lam M).symm
    have h1 : (M * GeneralLinearGroup.scalar (Fin n) lam) ^ p = 1 := by
      rw [← hσM, ← map_pow, hMp, map_one]
    rw [hc.mul_pow, hMp, one_mul, ← map_pow] at h1
    have h2 := congrArg (fun g : GL (Fin n) F => (g : Matrix (Fin n) (Fin n) F) ⟨0, hn0⟩ ⟨0, hn0⟩) h1
    simp only [GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, diagonal_apply_eq,
      Units.val_one, one_apply_eq] at h2
    exact Units.ext (h2.trans Units.val_one.symm)
  by_contra hlam1
  obtain ⟨A, d, hd⟩ := exists_conj_eq_diagonal_of_pow_eq_one hp hζ hMp
  have hdp := diagonal_pow_eq_one hMp hd
  have hd0 : ∀ l, d l ≠ 0 := by
    intro l h0
    have := hdp l
    rw [h0, zero_pow hp.ne_zero] at this
    exact zero_ne_one this
  set B := GeneralLinearGroup.map (σ : F →+* F) A with hB
  set D := A * M * A⁻¹ with hD
  have hσD : GeneralLinearGroup.map (σ : F →+* F) D = D := by
    ext i j
    rw [Matrix.GeneralLinearGroup.map_apply, RingEquiv.coe_toRingHom, hd]
    by_cases hij : i = j
    · subst hij
      rw [diagonal_apply_eq]
      exact hσ _ (hdp i)
    · rw [diagonal_apply_ne _ hij, map_zero]
  have hrel : B * M * B⁻¹ * GeneralLinearGroup.scalar (Fin n) lam = D := by
    rw [← hσD, hD, map_mul, map_mul, map_inv, hσM, ← hB]
    calc B * M * B⁻¹ * GeneralLinearGroup.scalar (Fin n) lam
        = B * M * (GeneralLinearGroup.scalar (Fin n) lam * B⁻¹) := by
          rw [GeneralLinearGroup.scalar_commute lam B⁻¹]; group
      _ = B * (M * GeneralLinearGroup.scalar (Fin n) lam) * B⁻¹ := by group
  have hXD : (B * A⁻¹) * D = GeneralLinearGroup.scalar (Fin n) lam⁻¹ * D * (B * A⁻¹) := by
    have e1 : B * M * B⁻¹ = D * GeneralLinearGroup.scalar (Fin n) lam⁻¹ := by
      rw [← hrel, map_inv]
      group
    calc (B * A⁻¹) * D = (B * M * B⁻¹) * (B * A⁻¹) := by rw [hD]; group
      _ = D * GeneralLinearGroup.scalar (Fin n) lam⁻¹ * (B * A⁻¹) := by rw [e1]
      _ = GeneralLinearGroup.scalar (Fin n) lam⁻¹ * D * (B * A⁻¹) := by
          rw [GeneralLinearGroup.scalar_commute lam⁻¹ D]
  have hXDm : ((B * A⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) * diagonal d =
      ((lam⁻¹ : Fˣ) : F) • (diagonal d * ((B * A⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)) := by
    have h1 : ((B * A⁻¹ * D : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) =
        ((GeneralLinearGroup.scalar (Fin n) lam⁻¹ * D * (B * A⁻¹) : GL (Fin n) F) :
          Matrix (Fin n) (Fin n) F) := by rw [hXD]
    have e1 : ((B * A⁻¹ * D : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) =
        ((B * A⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) * diagonal d := by
      rw [Units.val_mul (B * A⁻¹) D, hd]
    have e2 : ((GeneralLinearGroup.scalar (Fin n) lam⁻¹ * D * (B * A⁻¹) : GL (Fin n) F) :
        Matrix (Fin n) (Fin n) F) = ((lam⁻¹ : Fˣ) : F) •
          (diagonal d * ((B * A⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)) := by
      rw [Units.val_mul _ (B * A⁻¹), Units.val_mul _ D, hd, GeneralLinearGroup.coe_scalar,
        Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal, Matrix.smul_mul, Matrix.one_mul,
        Matrix.smul_mul]
    rw [← e1, ← e2, h1]
  have hinj := injective_of_mul_diagonal_eq_smul hp (by rw [Fintype.card_fin]; exact hn) hd0
    (lam := ((lam⁻¹ : Fˣ) : F))
    (by rw [← Units.val_pow_eq_pow_val, inv_pow, hlamp, inv_one, Units.val_one])
    (fun h => hlam1 (inv_eq_one.1 (Units.ext (h.trans Units.val_one.symm))))
    ((Matrix.isUnit_iff_isUnit_det _).1 (B * A⁻¹).isUnit) hXDm
  exact not_injective_of_conj_eq_diagonal hu1 hu2 hMu hd hinj

theorem exists_gl_subfield_eq {F₀ : Subfield F} {M : GL (Fin n) F}
    (hM : ∀ i j, (M : Matrix (Fin n) (Fin n) F) i j ∈ F₀) :
    ∃ M₀ : GL (Fin n) F₀, GeneralLinearGroup.map F₀.subtype M₀ = M := by
  let A : Matrix (Fin n) (Fin n) F₀ := fun i j => ⟨(M : Matrix (Fin n) (Fin n) F) i j, hM i j⟩
  have hA : F₀.subtype.mapMatrix A = (M : Matrix (Fin n) (Fin n) F) := rfl
  have hdet : A.det ≠ 0 := by
    intro h
    have h' := congrArg F₀.subtype h
    rw [RingHom.map_det, hA, map_zero] at h'
    exact ((Matrix.isUnit_iff_isUnit_det _).1 M.isUnit).ne_zero h'
  refine ⟨GeneralLinearGroup.mkOfDetNeZero A hdet, ?_⟩
  ext i j
  rfl

theorem map_subtype_injective (F₀ : Subfield F) :
    Function.Injective (GeneralLinearGroup.map (n := Fin n) F₀.subtype) := by
  intro x y hxy
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  have := congrArg (fun g : GL (Fin n) F => (g : Matrix (Fin n) (Fin n) F) i j) hxy
  exact Subtype.ext this

end GLLemmas

end CFSG.LocalAnalysis.GLTheoremA.S265F5

end
