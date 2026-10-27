module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk41RStd
public import CFSG.GH74.GLS.IVK.Proofs2.Lemma41aL3

public section

namespace CFSG.GH74.GLS.IVK.Proofs2.Ivk41R

open Subgroup Matrix CFSG.GH74.GLS.IVK.Proofs2.Lemma41dL3 CFSG.GH74.GLS.IVK.Proofs2
open CFSG.RankThree.SubgroupLists CFSG.Assembly.LowTwoRank
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open scoped commutatorElement

section Conj

variable {F : Type} [Field F]

@[expose] def swapMat (F : Type) [Field F] : Matrix (Fin 3) (Fin 3) F := !![1, 0, 0; 0, 0, 1; 0, 1, 0]

theorem det_swapMat : (swapMat F).det = -1 := by
  simp [swapMat, Matrix.det_fin_three]

theorem negDiag_mul_swap :
    (diagonal ![-1, -1, 1] : Matrix (Fin 3) (Fin 3) F) * swapMat F =
      swapMat F * !![-1, 0, 0; 0, 1, 0; 0, 0, -1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [swapMat, Matrix.mul_apply, Fin.sum_univ_three]

theorem exists_conj_tz (h2 : (2 : F) ≠ 0) {z : SpecialLinearGroup (Fin 3) F} (hz : z * z = 1)
    (hz1 : z ≠ 1) : ∃ g : SpecialLinearGroup (Fin 3) F, g * tz F * g⁻¹ = z := by
  have ha2 : (Matrix.SpecialLinearGroup.toGL z : GL (Fin 3) F) *
      Matrix.SpecialLinearGroup.toGL z = 1 := by
    rw [← map_mul, hz, map_one]
  have ha1 : (Matrix.SpecialLinearGroup.toGL z : GL (Fin 3) F) ≠ 1 := by
    intro h
    apply hz1
    apply Subtype.ext
    have := congrArg (fun g : GL (Fin 3) F => (g : Matrix (Fin 3) (Fin 3) F)) h
    simpa using this
  have hdet : ((Matrix.SpecialLinearGroup.toGL z : GL (Fin 3) F) :
      Matrix (Fin 3) (Fin 3) F).det = 1 := by
    simp
  obtain ⟨P, hP⟩ := exists_conj_negDiag3 h2 ha2 ha1 hdet
  have hP' : Matrix.SpecialLinearGroup.toGL z * P = P * negDiag3 F := by
    rw [← hP]
    group
  have hPm : (z : Matrix (Fin 3) (Fin 3) F) * (P : Matrix (Fin 3) (Fin 3) F) =
      (P : Matrix (Fin 3) (Fin 3) F) * diagonal ![-1, -1, 1] := by
    have := congrArg (fun g : GL (Fin 3) F => (g : Matrix (Fin 3) (Fin 3) F)) hP'
    simpa [coe_negDiag3] using this
  have hPdet : (P : Matrix (Fin 3) (Fin 3) F).det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det _).mp P.isUnit).ne_zero
  set d : F := ((P : Matrix (Fin 3) (Fin 3) F) * swapMat F).det with hd
  have hd0 : d ≠ 0 := by
    rw [hd, Matrix.det_mul, det_swapMat]
    simpa using hPdet
  set Q : Matrix (Fin 3) (Fin 3) F :=
    (P : Matrix (Fin 3) (Fin 3) F) * swapMat F * diagonal ![d⁻¹, 1, 1] with hQ
  have hQdet : Q.det = 1 := by
    rw [hQ, Matrix.det_mul, ← hd, Matrix.det_diagonal, Fin.prod_univ_three]
    simp [hd0]
  have hDT : (diagonal ![d⁻¹, 1, 1] : Matrix (Fin 3) (Fin 3) F) *
      !![-1, 0, 0; 0, 1, 0; 0, 0, -1] =
      !![-1, 0, 0; 0, 1, 0; 0, 0, -1] * diagonal ![d⁻¹, 1, 1] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]
  have hzQ : (z : Matrix (Fin 3) (Fin 3) F) * Q = Q * !![-1, 0, 0; 0, 1, 0; 0, 0, -1] := by
    calc (z : Matrix (Fin 3) (Fin 3) F) * Q
        = ((z : Matrix (Fin 3) (Fin 3) F) * (P : Matrix (Fin 3) (Fin 3) F)) * swapMat F *
            diagonal ![d⁻¹, 1, 1] := by
          rw [hQ]; simp only [Matrix.mul_assoc]
      _ = (P : Matrix (Fin 3) (Fin 3) F) * (diagonal ![-1, -1, 1] * swapMat F) *
            diagonal ![d⁻¹, 1, 1] := by
          rw [hPm]; simp only [Matrix.mul_assoc]
      _ = (P : Matrix (Fin 3) (Fin 3) F) * (swapMat F * !![-1, 0, 0; 0, 1, 0; 0, 0, -1]) *
            diagonal ![d⁻¹, 1, 1] := by rw [negDiag_mul_swap]
      _ = (P : Matrix (Fin 3) (Fin 3) F) * swapMat F *
            (!![-1, 0, 0; 0, 1, 0; 0, 0, -1] * diagonal ![d⁻¹, 1, 1]) := by
          simp only [Matrix.mul_assoc]
      _ = (P : Matrix (Fin 3) (Fin 3) F) * swapMat F *
            (diagonal ![d⁻¹, 1, 1] * !![-1, 0, 0; 0, 1, 0; 0, 0, -1]) := by rw [hDT]
      _ = Q * !![-1, 0, 0; 0, 1, 0; 0, 0, -1] := by
          rw [hQ]; simp only [Matrix.mul_assoc]
  let g : SpecialLinearGroup (Fin 3) F := ⟨Q, hQdet⟩
  refine ⟨g, ?_⟩
  rw [mul_inv_eq_iff_eq_mul]
  apply Subtype.ext
  exact hzQ.symm

end Conj

section Card

variable {F : Type} [Field F]

theorem card_centralizer_tz (h2 : (2 : F) ≠ 0) :
    Nat.card (centralizer ({tz F} : Set (Matrix.SpecialLinearGroup (Fin 3) F))) =
      Nat.card (GL (Fin 2) F) := by
  let e₀ := CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 3 F
  have ha : e₀ (tz F) * e₀ (tz F) = 1 := by rw [← map_mul, tz_mul_tz, map_one]
  have ha1 : e₀ (tz F) ≠ 1 := fun h => tz_ne_one h2 (e₀.injective (by rw [map_one]; exact h))
  obtain ⟨φ, hφ, hrange⟩ := Lemma41aL3.exists_phi h2 (StatedSL 3 F)
    (fun A => linConj_mem_statedSL A) ha ha1
  calc Nat.card (centralizer ({tz F} : Set (Matrix.SpecialLinearGroup (Fin 3) F)))
      = Nat.card (centralizer ({e₀ (tz F)} : Set (StatedSL 3 F))) :=
        Nat.card_congr (centralizerEquiv e₀ (tz F)).toEquiv
    _ = Nat.card φ.range := by rw [hrange]
    _ = Nat.card (GL (Fin 2) F) := Nat.card_range_of_injective hφ

theorem not_dvd_pow_sub_one {p q : ℕ} (hp : p.Prime) (hpq : p ∣ q) (hq : 1 ≤ q) {j : ℕ}
    (hj : j ≠ 0) : ¬ p ∣ q ^ j - 1 := by
  intro hdvd
  have hqj : p ∣ q ^ j := hpq.trans (dvd_pow_self q hj)
  have h1 : 1 ≤ q ^ j := Nat.one_le_pow _ _ hq
  have : p ∣ q ^ j - (q ^ j - 1) := Nat.dvd_sub hqj hdvd
  rw [Nat.sub_sub_self h1] at this
  exact hp.one_lt.ne' (Nat.dvd_one.mp this)

theorem card_GL2_factor [Finite F] {p n : ℕ} (hp : p.Prime) [CharP F p] (hF : Nat.card F = p ^ n) :
    ∃ m : ℕ, Nat.card (GL (Fin 2) F) = p ^ n * m ∧ ¬ p ∣ m := by
  have hpq : p ∣ Nat.card F := CFSG.GH74.GLS.IVK.Proofs2.Lemma41dL3.p_dvd_card
  have hq : 1 ≤ Nat.card F := Nat.card_pos
  refine ⟨(Nat.card F - 1) * (Nat.card F ^ 2 - 1), ?_, ?_⟩
  · rw [card_GL_eq 2, hF]
    have : Finset.Icc 1 2 = {1, 2} := by decide
    rw [this, Finset.prod_pair (by norm_num)]
    norm_num
  · intro hdvd
    rcases (Nat.Prime.dvd_mul hp).1 hdvd with h | h
    · exact not_dvd_pow_sub_one hp hpq hq (j := 1) (by norm_num) (by simpa using h)
    · exact not_dvd_pow_sub_one hp hpq hq (j := 2) (by norm_num) h

end Card

section Sylow

theorem exists_conj_of_card_eq {G : Type*} [Group G] [Finite G] {p k m : ℕ} [Fact p.Prime]
    (hG : Nat.card G = p ^ k * m) (hm : ¬ p ∣ m) {A B : Subgroup G}
    (hA : Nat.card A = p ^ k) (hB : Nat.card B = p ^ k) :
    ∃ g : G, A.map (MulAut.conj g).toMonoidHom = B := by
  have hm0 : m ≠ 0 := by
    rintro rfl
    have : 0 < Nat.card G := Nat.card_pos
    rw [hG, mul_zero] at this
    exact lt_irrefl _ this
  have hfac : (Nat.card G).factorization p = k := by
    rw [hG, Nat.factorization_mul (pow_ne_zero _ (Fact.out : p.Prime).ne_zero) hm0,
      Finsupp.add_apply, (Fact.out : p.Prime).factorization_pow, Finsupp.single_eq_same,
      Nat.factorization_eq_zero_of_not_dvd hm, add_zero]
  let SA : Sylow p G := Sylow.ofCard A (by rw [hA, hfac])
  let SB : Sylow p G := Sylow.ofCard B (by rw [hB, hfac])
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G SA SB
  refine ⟨g, ?_⟩
  have h1 : (SB : Subgroup G) = B := Sylow.coe_ofCard B _
  have h2 : (SA : Subgroup G) = A := Sylow.coe_ofCard A _
  rw [← h1, ← hg, ← h2]
  rfl

theorem exists_conj_subgroup_of_le {G : Type*} [Group G] [Finite G] {p k m : ℕ} [Fact p.Prime]
    (C : Subgroup G) (hC : Nat.card C = p ^ k * m) (hm : ¬ p ∣ m) {A B : Subgroup G}
    (hAC : A ≤ C) (hBC : B ≤ C) (hA : Nat.card A = p ^ k) (hB : Nat.card B = p ^ k) :
    ∃ g ∈ C, A.map (MulAut.conj g).toMonoidHom = B := by
  have hA' : Nat.card (A.subgroupOf C) = p ^ k := by
    rw [← hA]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAC).toEquiv
  have hB' : Nat.card (B.subgroupOf C) = p ^ k := by
    rw [← hB]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBC).toEquiv
  obtain ⟨g, hg⟩ := exists_conj_of_card_eq (G := C) hC hm hA' hB'
  refine ⟨g, g.2, ?_⟩
  have e1 : ((A.subgroupOf C).map (MulAut.conj g).toMonoidHom).map C.subtype =
      A.map (MulAut.conj (g : G)).toMonoidHom := by
    rw [Subgroup.map_map]
    conv_rhs => rw [← Subgroup.map_subgroupOf_eq_of_le hAC, Subgroup.map_map]
    congr 1
  rw [← Subgroup.map_subgroupOf_eq_of_le hBC, ← hg, e1]

end Sylow

section Main

variable {F : Type} [Field F] [Finite F]

omit [Finite F] in
theorem card_X₀ : Nat.card (X₀ F) = Nat.card F := by
  rw [X₀, Subgroup.card_map_of_injective heisSL_injective, Heis.card_center]

theorem rgood_sl3 {p n : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) [CharP F p] (hF : Nat.card F = p ^ n)
    {z : Matrix.SpecialLinearGroup (Fin 3) F} (hz : orderOf z = 2)
    {X : Subgroup (Matrix.SpecialLinearGroup (Fin 3) F)} (hXz : X ≤ centralizer ({z} : Set _))
    (hXc : Nat.card X = p ^ n) : RGood p n z X := by
  have : Fact p.Prime := ⟨hp⟩
  have h2 : (2 : F) ≠ 0 := by
    intro h
    have h' : ((2 : ℕ) : F) = 0 := by exact_mod_cast h
    rw [CharP.cast_eq_zero_iff F p] at h'
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h')
  have hzz : z * z = 1 := by
    have := pow_orderOf_eq_one z
    rwa [hz, sq] at this
  have hz1 : z ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hz
    omega
  obtain ⟨g, hg⟩ := exists_conj_tz h2 hzz hz1
  have htz : tz F = g⁻¹ * z * g := by rw [← hg]; group
  let ε₁ : Matrix.SpecialLinearGroup (Fin 3) F ≃* Matrix.SpecialLinearGroup (Fin 3) F :=
    MulAut.conj g⁻¹
  have hε₁z : ε₁ z = tz F := by
    rw [htz]
    simp [ε₁]
  have hX₁C : X.map ε₁.toMonoidHom ≤
      centralizer ({tz F} : Set (Matrix.SpecialLinearGroup (Fin 3) F)) := by
    rintro _ ⟨x, hx, rfl⟩
    rw [mem_centralizer_singleton_iff]
    have hxz := mem_centralizer_singleton_iff.mp (hXz hx)
    rw [htz]
    show g⁻¹ * x * g⁻¹⁻¹ * (g⁻¹ * z * g) = g⁻¹ * z * g * (g⁻¹ * x * g⁻¹⁻¹)
    calc g⁻¹ * x * g⁻¹⁻¹ * (g⁻¹ * z * g) = g⁻¹ * (x * z) * g := by group
      _ = g⁻¹ * (z * x) * g := by rw [hxz]
      _ = g⁻¹ * z * g * (g⁻¹ * x * g⁻¹⁻¹) := by group
  have hX₁c : Nat.card (X.map ε₁.toMonoidHom) = p ^ n := by
    rw [Subgroup.card_map_of_injective ε₁.injective]
    exact hXc
  obtain ⟨m, hm, hpm⟩ := card_GL2_factor hp hF
  have hC : Nat.card (centralizer ({tz F} : Set (Matrix.SpecialLinearGroup (Fin 3) F))) =
      p ^ n * m := (card_centralizer_tz h2).trans hm
  obtain ⟨h, hhC, hh⟩ := exists_conj_subgroup_of_le (centralizer ({tz F} : Set _)) hC hpm hX₁C
    X₀_le_centralizer_tz hX₁c (card_X₀.trans hF)
  let ε : Matrix.SpecialLinearGroup (Fin 3) F ≃* Matrix.SpecialLinearGroup (Fin 3) F :=
    ε₁.trans (MulAut.conj h)
  have hεz : ε z = tz F := by
    have hcomm := mem_centralizer_singleton_iff.mp hhC
    show (MulAut.conj h) (ε₁ z) = tz F
    rw [hε₁z, MulAut.conj_apply, hcomm]
    group
  have hεX : X.map ε.toMonoidHom = X₀ F := by
    rw [← hh, Subgroup.map_map]
    rfl
  exact RGood.congr ε.symm ((MulEquiv.symm_apply_eq _).2 hεz.symm)
    (by rw [← hεX]; exact map_map_symm_mulEquiv ε X) (rgood_std hp hF)

end Main

end CFSG.GH74.GLS.IVK.Proofs2.Ivk41R
