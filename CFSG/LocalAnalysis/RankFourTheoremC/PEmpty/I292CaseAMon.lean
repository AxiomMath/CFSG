module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.I292CaseAMat
public import Mathlib.GroupTheory.Sylow
public import Mathlib.LinearAlgebra.Matrix.Permutation
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
public import Mathlib.NumberTheory.Multiplicity
public import Mathlib.Algebra.Group.Pi.Units

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.I292CaseA

open Matrix Subgroup

variable (p : ℕ) (K : Type) [Field K]

@[expose] noncomputable def diagGL : (Fin p → Kˣ) →* GL (Fin p) K :=
  (Units.map (Matrix.diagonalRingHom (Fin p) K).toMonoidHom).comp
    (MulEquiv.piUnits.symm : (Fin p → Kˣ) ≃* (Fin p → K)ˣ).toMonoidHom

theorem diagGL_val (d : Fin p → Kˣ) :
    ((diagGL p K d : GL (Fin p) K) : Matrix (Fin p) (Fin p) K) =
      Matrix.diagonal (fun i => (d i : K)) := rfl

@[expose] noncomputable def rotGL : GL (Fin p) K :=
  (Matrix.permMatrixHom (n := Fin p) (R := K)).toHomUnits (finRotate p)

theorem rotGL_val :
    ((rotGL p K : GL (Fin p) K) : Matrix (Fin p) (Fin p) K) =
      ((finRotate p)⁻¹).permMatrix K := rfl


theorem diagGL_injective : Function.Injective (diagGL p K) := by
  intro d e h
  have h1 := congrArg (fun g : GL (Fin p) K => (g : Matrix (Fin p) (Fin p) K)) h
  simp only [diagGL_val] at h1
  funext i
  have h2 := congrFun (congrFun h1 i) i
  simp only [Matrix.diagonal_apply_eq] at h2
  exact Units.ext h2

theorem rotGL_mul_diagGL (d : Fin p → Kˣ) :
    rotGL p K * diagGL p K d = diagGL p K (fun i => d ((finRotate p).symm i)) * rotGL p K := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, rotGL_val, diagGL_val, diagGL_val]
  apply Matrix.ext_of_mulVec_single
  intro j
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  ext i
  simp only [Matrix.permMatrix_mulVec, Matrix.mulVec_diagonal, Pi.single_apply,
    Equiv.Perm.inv_def, Function.comp_apply, mul_ite, mul_one, mul_zero]


variable {p K}

@[expose] noncomputable def diagQ (Q : Subgroup Kˣ) : (Fin p → Q) →* GL (Fin p) K :=
  (diagGL p K).comp (MonoidHom.compLeft Q.subtype (Fin p))

theorem diagQ_injective (Q : Subgroup Kˣ) : Function.Injective (diagQ (p := p) (K := K) Q) := by
  intro c c' h
  have h1 := diagGL_injective p K h
  funext i
  exact Subtype.ext (congrFun h1 i)

@[expose] noncomputable def torusQ (Q : Subgroup Kˣ) : Subgroup (GL (Fin p) K) :=
  (diagQ Q).range

theorem card_torusQ (Q : Subgroup Kˣ) : Nat.card (torusQ (p := p) (K := K) Q) = Nat.card Q ^ p := by
  rw [torusQ, Nat.card_congr (MonoidHom.ofInjective (diagQ_injective Q)).toEquiv.symm,
    Nat.card_fun, Nat.card_eq_fintype_card (α := Fin p), Fintype.card_fin]

theorem rotGL_conj_diagQ (Q : Subgroup Kˣ) (c : Fin p → Q) :
    rotGL p K * diagQ Q c * (rotGL p K)⁻¹ = diagQ Q (fun i => c ((finRotate p).symm i)) := by
  rw [mul_inv_eq_iff_eq_mul]
  exact rotGL_mul_diagGL p K (fun i => (c i : Kˣ))

theorem rotGL_mem_normalizer_torusQ (Q : Subgroup Kˣ) :
    rotGL p K ∈ normalizer (torusQ (p := p) (K := K) Q : Set (GL (Fin p) K)) := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · rintro ⟨c, rfl⟩
    exact ⟨_, (rotGL_conj_diagQ Q c).symm⟩
  · rintro ⟨c', hc'⟩
    refine ⟨fun i => c' ((finRotate p) i), ?_⟩
    have h2 := rotGL_conj_diagQ Q (fun i => c' ((finRotate p) i))
    have h3 : (fun i => (fun i => c' ((finRotate p) i)) ((finRotate p).symm i)) = c' := by
      funext i
      simp only [Equiv.apply_symm_apply]
    rw [h3] at h2
    exact mul_left_cancel (mul_right_cancel (h2.trans hc'))

theorem rotGL_pow_p (hp : 2 ≤ p) : rotGL p K ^ p = 1 := by
  have h1 : orderOf (finRotate p) = p := by
    rw [(isCycle_finRotate_of_le hp).orderOf, support_finRotate_of_le hp, Finset.card_univ,
      Fintype.card_fin]
  have h2 : (finRotate p) ^ p = 1 := by
    have := pow_orderOf_eq_one (finRotate p)
    rwa [h1] at this
  rw [rotGL, ← map_pow, h2, map_one]

theorem rotGL_not_mem_torusQ (Q : Subgroup Kˣ) (hp : 2 ≤ p) :
    rotGL p K ∉ torusQ (p := p) (K := K) Q := by
  haveI : NeZero p := ⟨by omega⟩
  rintro ⟨c, hc⟩
  have h1 := congrArg (fun g : GL (Fin p) K => (g : Matrix (Fin p) (Fin p) K)) hc
  simp only [diagQ, MonoidHom.comp_apply, diagGL_val, rotGL_val] at h1
  have hne : (finRotate p) 0 ≠ (0 : Fin p) := by
    obtain ⟨n, rfl⟩ : ∃ n, p = n + 2 := ⟨p - 2, by omega⟩
    simp [finRotate_succ_apply, Fin.ext_iff]
  have h2 := congrFun (congrFun h1 ((finRotate p) 0)) 0
  rw [Matrix.diagonal_apply_ne _ hne] at h2
  simp [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply] at h2


theorem factorization_card_GL {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {K : Type} [Field K]
    [Finite K] (hpK : p ∣ Nat.card K - 1) :
    (Nat.card (GL (Fin p) K)).factorization p = p * (Nat.card K - 1).factorization p + 1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI := Fintype.ofFinite K
  have hodd : Odd p := hp.odd_of_ne_two hp2
  set Q := Nat.card K with hQ
  have hQcard : Fintype.card K = Q := Nat.card_eq_fintype_card.symm
  have hQ1 : 1 < Q := Finite.one_lt_card
  have hpQ : ¬ p ∣ Q := by
    intro h
    have h1 : p ∣ Q - (Q - 1) := Nat.dvd_sub h hpK
    have h2 : Q - (Q - 1) = 1 := by omega
    rw [h2] at h1
    exact hp.one_lt.ne' (Nat.dvd_one.1 h1)
  have hcard : Nat.card (GL (Fin p) K) = ∏ i : Fin p, (Q ^ p - Q ^ (i : ℕ)) := by
    rw [Matrix.card_GL_field, hQcard]
  have hne : ∀ i ∈ (Finset.univ : Finset (Fin p)), Q ^ p - Q ^ (i : ℕ) ≠ 0 := by
    intro i _
    have : Q ^ (i : ℕ) < Q ^ p := Nat.pow_lt_pow_right hQ1 i.2
    omega
  have hterm : ∀ i : Fin p, (Q ^ p - Q ^ (i : ℕ)).factorization p =
      (Q - 1).factorization p + (if (i : ℕ) = 0 then 1 else 0) := by
    intro i
    have hpi : (i : ℕ) < p := i.2
    have hfac : Q ^ p - Q ^ (i : ℕ) = Q ^ (i : ℕ) * (Q ^ (p - i) - 1) := by
      have h1 : Q ^ p = Q ^ (i : ℕ) * Q ^ (p - i) := by rw [← pow_add]; congr 1; omega
      rw [h1, Nat.mul_sub, mul_one]
    have hQi : Q ^ (i : ℕ) ≠ 0 := pow_ne_zero _ (by omega)
    have hQj : Q ^ (p - i) - 1 ≠ 0 := by
      have : 1 < Q ^ (p - i) := Nat.one_lt_pow (by omega) hQ1
      omega
    rw [hfac, Nat.factorization_mul hQi hQj]
    simp only [Finsupp.coe_add, Pi.add_apply]
    have h0 : (Q ^ (i : ℕ)).factorization p = 0 :=
      Nat.factorization_eq_zero_of_not_dvd (fun h => hpQ (hp.dvd_of_dvd_pow h))
    have hn0 : p - (i : ℕ) ≠ 0 := by omega
    have h1 : (Q ^ (p - i) - 1).factorization p =
        (Q - 1).factorization p + padicValNat p (p - i) := by
      rw [Nat.factorization_def _ hp, Nat.factorization_def _ hp]
      have := padicValNat.pow_sub_pow hodd (x := Q) (y := 1) hQ1 hpK hpQ hn0
      rwa [one_pow] at this
    have h2 : padicValNat p (p - (i : ℕ)) = if (i : ℕ) = 0 then 1 else 0 := by
      by_cases hi : (i : ℕ) = 0
      · rw [if_pos hi, hi, Nat.sub_zero]
        exact padicValNat_self
      · rw [if_neg hi]
        apply padicValNat.eq_zero_of_not_dvd
        exact Nat.not_dvd_of_pos_of_lt (by omega) (by omega)
    rw [h0, h1, h2, zero_add]
  rw [hcard, Nat.factorization_prod hne, Finsupp.coe_finset_sum, Finset.sum_apply]
  simp only [hterm]
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul,
    Fin.sum_univ_eq_sum_range (fun j => if j = 0 then 1 else 0) p]
  simp [Finset.sum_ite_eq', hp.pos]


@[expose] noncomputable def monoQ (Q : Subgroup Kˣ) : Subgroup (GL (Fin p) K) :=
  torusQ Q ⊔ Subgroup.zpowers (rotGL p K)

theorem isPGroup_zpowers_rotGL (hp : p.Prime) (hp2 : 2 ≤ p) :
    IsPGroup p (Subgroup.zpowers (rotGL p K)) := by
  have h1 : rotGL p K ^ p = 1 := rotGL_pow_p hp2
  have h2 : orderOf (rotGL p K) ∣ p := orderOf_dvd_of_pow_eq_one h1
  rcases (Nat.dvd_prime hp).1 h2 with h3 | h3
  · exact IsPGroup.of_card (n := 0) (by rw [Nat.card_zpowers, h3, pow_zero])
  · exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, h3, pow_one])

variable [Finite K]

theorem isPGroup_torusQ [Fact p.Prime] {Q : Subgroup Kˣ} (hQ : IsPGroup p Q) :
    IsPGroup p (torusQ (p := p) (K := K) Q) := by
  obtain ⟨n, hn⟩ := hQ.exists_card_eq
  exact IsPGroup.of_card (n := n * p) (by rw [card_torusQ, hn, ← pow_mul])

theorem isPGroup_monoQ [Fact p.Prime] (hp2 : 2 ≤ p) {Q : Subgroup Kˣ} (hQ : IsPGroup p Q) :
    IsPGroup p (monoQ (p := p) (K := K) Q) := by
  rw [monoQ, sup_comm]
  exact (isPGroup_zpowers_rotGL (Fact.out : p.Prime) hp2).to_sup_of_normal_right'
    (isPGroup_torusQ hQ) (Subgroup.zpowers_le.2 (rotGL_mem_normalizer_torusQ Q))

theorem card_monoQ_ge [Fact p.Prime] (hp2 : 2 ≤ p) {Q : Subgroup Kˣ} (hQ : IsPGroup p Q) :
    Nat.card Q ^ p * p ≤ Nat.card (monoQ (p := p) (K := K) Q) := by
  set M := monoQ (p := p) (K := K) Q with hMdef
  have hM : IsPGroup p M := isPGroup_monoQ hp2 hQ
  set H : Subgroup M := (torusQ (p := p) (K := K) Q).subgroupOf M with hHdef
  have hle : torusQ (p := p) (K := K) Q ≤ M := le_sup_left
  have hH : Nat.card H = Nat.card (torusQ (p := p) (K := K) Q) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv
  have hcm := Subgroup.card_mul_index H
  obtain ⟨m, hm⟩ := hM.index H
  have hm0 : m ≠ 0 := by
    intro h0
    rw [h0, pow_zero] at hm
    have htop := Subgroup.index_eq_one.1 hm
    have hmem : (⟨rotGL p K, Subgroup.mem_sup_right (Subgroup.mem_zpowers _)⟩ : M) ∈ H := by
      rw [htop]
      exact Subgroup.mem_top _
    exact rotGL_not_mem_torusQ Q hp2 (Subgroup.mem_subgroupOf.1 hmem)
  have hpidx : p ≤ H.index := by
    rw [hm]
    exact Nat.le_self_pow hm0 p
  calc Nat.card Q ^ p * p ≤ Nat.card (torusQ (p := p) (K := K) Q) * H.index := by
        rw [card_torusQ]
        exact Nat.mul_le_mul_left _ hpidx
    _ = Nat.card M := by rw [← hH, hcm]

theorem not_dvd_index_monoQ [Fact p.Prime] (hp2 : p ≠ 2) (Q : Sylow p Kˣ)
    (hpK : p ∣ Nat.card K - 1) :
    ¬ p ∣ (monoQ (p := p) (K := K) (Q : Subgroup Kˣ)).index := by
  intro hdvd
  have hp : p.Prime := Fact.out
  have hp2' : 2 ≤ p := hp.two_le
  set M := monoQ (p := p) (K := K) (Q : Subgroup Kˣ) with hMdef
  have hM : IsPGroup p M := isPGroup_monoQ hp2' Q.isPGroup'
  obtain ⟨m, hm⟩ := hM.exists_card_eq
  have hQcard : Nat.card (Q : Subgroup Kˣ) = p ^ (Nat.card K - 1).factorization p := by
    rw [Sylow.card_eq_multiplicity, Nat.card_units]
  have hge := card_monoQ_ge (K := K) hp2' Q.isPGroup'
  rw [hQcard, hm, ← pow_mul, ← pow_succ] at hge
  have hmge : (Nat.card K - 1).factorization p * p + 1 ≤ m :=
    (Nat.pow_le_pow_iff_right hp.one_lt).1 hge
  have hcard := Subgroup.card_mul_index M
  have hfac := factorization_card_GL (K := K) hp hp2 hpK
  have hidx0 : M.index ≠ 0 := Subgroup.FiniteIndex.index_ne_zero
  have hpos : 0 < M.index.factorization p := Nat.Prime.factorization_pos_of_dvd hp hidx0 hdvd
  rw [← hcard, hm, Nat.factorization_mul (pow_ne_zero _ hp.ne_zero) hidx0, Finsupp.add_apply,
    Nat.Prime.factorization_pow hp, Finsupp.single_eq_same] at hfac
  nlinarith

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.I292CaseA


