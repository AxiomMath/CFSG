module

public import CFSG.ClassicalInvolution.Asc77.AscSCH25
public import CFSG.ClassicalInvolution.Asc77.AscSCH12

public section

namespace CFSG.ClassicalInvolution.Asc77.SCH

open Matrix CFSG.RankThree.Classical
open scoped MatrixGroups

variable {K : Type} [Field K]

@[expose] def lineA : K →+ K × K × K × K :=
  AddMonoidHom.mk' (fun s => (s, 0, 0, 0)) (fun a b => by ext <;> simp)

@[expose] def lineB : K →+ K × K × K × K :=
  AddMonoidHom.mk' (fun s => (0, s, 0, 0)) (fun a b => by ext <;> simp)

@[expose] def lineC : K →+ K × K × K × K :=
  AddMonoidHom.mk' (fun s => (0, 0, s, 0)) (fun a b => by ext <;> simp)

@[expose] def lineD : K →+ K × K × K × K :=
  AddMonoidHom.mk' (fun s => (0, 0, 0, s)) (fun a b => by ext <;> simp)

@[expose] def lineF : Fin 4 → (K →+ K × K × K × K) := ![lineA, lineB, lineC, lineD]

theorem lineF_decomp (x : K × K × K × K) :
    x = ∑ i, lineF i (![x.1, x.2.1, x.2.2.1, x.2.2.2] i) := by
  rw [Fin.sum_univ_four]
  ext <;> simp [lineF, lineA, lineB, lineC, lineD]

@[expose] def wtR (t : Fin 4 → Kˣ) (i : Fin 4) : K :=
  (t (![0, 0, 1, 1] i) : K) / (t (![2, 3, 2, 3] i) : K)

theorem conj_lineF (t : Fin 4 → Kˣ) (ht : ∏ i, (t i : K) = 1) (i : Fin 4) (s : K) :
    diagSL t ht * rhoR (Multiplicative.ofAdd (lineF i s)) * (diagSL t ht)⁻¹ =
      rhoR (Multiplicative.ofAdd (lineF i (wtR t i * s))) := by
  fin_cases i <;>
    simp only [lineF, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three] <;>
    rw [diagSL_conj_rhoR] <;> congr 3 <;> simp [lineA, lineB, lineC, lineD, wtR]

section Pairing

variable {E : Type*} [Group E] {π : E →* SL(4, K)} (hπ : Function.Surjective π)
  (hZ : π.ker ≤ Subgroup.center E)

include hZ in
theorem cross_of_torus (i j : Fin 4) (t : Fin 4 → Kˣ) (ht : ∏ i, (t i : K) = 1)
    (hi : wtR t i = 1) (hj : wtR t j ≠ 1) (s u : K) :
    liftPair hπ rhoR (lineF i s) (lineF j u) = 1 ∧
      liftPair hπ rhoR (lineF j u) (lineF i s) = 1 :=
  ⟨liftPair_eq_one_of_scale_right hπ rhoR hZ (lineF i) (lineF j) (diagSL t ht) (wtR t j) hj
    (fun s => by rw [conj_lineF, hi, one_mul]) (fun u => conj_lineF t ht j u) s u,
   liftPair_eq_one_of_scale_left hπ rhoR hZ (lineF j) (lineF i) (diagSL t ht) (wtR t j) hj
    (fun u => conj_lineF t ht j u) (fun s => by rw [conj_lineF, hi, one_mul]) u s⟩

include hZ in
theorem self_of_torus (hCp : IsPGroup 3 π.ker) (i : Fin 4)
    (T : ∀ x : K, x ≠ 0 → ∃ (t : Fin 4 → Kˣ) (_ : ∏ i, (t i : K) = 1), wtR t i = x) (s u : K) :
    liftPair hπ rhoR (lineF i s) (lineF i u) = 1 :=
  liftPair_self_eq_one_of_full hπ rhoR hZ (p := 3) (by norm_num) hCp (lineF i) (fun x hx => by
    obtain ⟨t, ht, hw⟩ := T x hx
    exact ⟨diagSL t ht, fun s => by rw [conj_lineF, hw]⟩) s u

variable (c : Kˣ)

@[expose] def tor1 : Fin 4 → Kˣ := ![1, c⁻¹, 1, c]

@[expose] def tor2 : Fin 4 → Kˣ := ![c, 1, 1, c⁻¹]

@[expose] def tor3 : Fin 4 → Kˣ := ![1, c, 1, c⁻¹]

@[expose] def tor4 : Fin 4 → Kˣ := ![c, 1, c⁻¹, 1]

theorem prod_tor1 : ∏ i, ((tor1 c i : Kˣ) : K) = 1 := by
  simp [Fin.prod_univ_four, tor1]

theorem prod_tor2 : ∏ i, ((tor2 c i : Kˣ) : K) = 1 := by
  simp [Fin.prod_univ_four, tor2]

theorem prod_tor3 : ∏ i, ((tor3 c i : Kˣ) : K) = 1 := by
  simp [Fin.prod_univ_four, tor3]

theorem prod_tor4 : ∏ i, ((tor4 c i : Kˣ) : K) = 1 := by
  simp [Fin.prod_univ_four, tor4]

theorem wt_tor1_0 : wtR (tor1 c) 0 = (1 : K) := by simp [wtR, tor1]

theorem wt_tor1_1 : wtR (tor1 c) 1 = (((c⁻¹ : Kˣ)) : K) := by simp [wtR, tor1]

theorem wt_tor2_0 : wtR (tor2 c) 0 = (c : K) := by simp [wtR, tor2]

theorem wt_tor2_1 : wtR (tor2 c) 1 = (c : K) ^ 2 := by
  simp [wtR, tor2]
  ring

theorem wt_tor2_2 : wtR (tor2 c) 2 = (1 : K) := by simp [wtR, tor2]

theorem wt_tor2_3 : wtR (tor2 c) 3 = (c : K) := by simp [wtR, tor2]

theorem wt_tor3_0 : wtR (tor3 c) 0 = (1 : K) := by simp [wtR, tor3]

theorem wt_tor3_3 : wtR (tor3 c) 3 = (c : K) ^ 2 := by
  simp [wtR, tor3]
  ring

theorem wt_tor4_1 : wtR (tor4 c) 1 = (c : K) := by simp [wtR, tor4]

theorem wt_tor4_3 : wtR (tor4 c) 3 = (1 : K) := by simp [wtR, tor4]

include hZ in
theorem pair_vanish (hc : c ^ 2 ≠ 1) (i j : Fin 4) (hij : i ≠ j) (s u : K) :
    liftPair hπ rhoR (lineF i s) (lineF j u) = 1 := by
  have hc1 : (c : K) ≠ 1 := fun h1 => hc (by
    have : c = 1 := Units.ext h1
    rw [this, one_pow])
  have hc2 : (c : K) ^ 2 ≠ 1 := fun h1 => hc (Units.ext (by simpa using h1))
  have hc3 : (((c⁻¹ : Kˣ)) : K) ≠ 1 := fun h1 => hc1 (by
    have : c⁻¹ = 1 := Units.ext h1
    rw [inv_eq_one.1 this] ; simp)
  have p01 := fun s u => cross_of_torus hπ hZ 0 1 (tor1 c) (prod_tor1 c) (by rw [wt_tor1_0])
    (by rw [wt_tor1_1]; exact hc3) s u
  have p20 := fun s u => cross_of_torus hπ hZ 2 0 (tor2 c) (prod_tor2 c) (by rw [wt_tor2_2])
    (by rw [wt_tor2_0]; exact hc1) s u
  have p03 := fun s u => cross_of_torus hπ hZ 0 3 (tor3 c) (prod_tor3 c) (by rw [wt_tor3_0])
    (by rw [wt_tor3_3]; exact hc2) s u
  have p21 := fun s u => cross_of_torus hπ hZ 2 1 (tor2 c) (prod_tor2 c) (by rw [wt_tor2_2])
    (by rw [wt_tor2_1]; exact hc2) s u
  have p31 := fun s u => cross_of_torus hπ hZ 3 1 (tor4 c) (prod_tor4 c) (by rw [wt_tor4_3])
    (by rw [wt_tor4_1]; exact hc1) s u
  have p23 := fun s u => cross_of_torus hπ hZ 2 3 (tor2 c) (prod_tor2 c) (by rw [wt_tor2_2])
    (by rw [wt_tor2_3]; exact hc1) s u
  fin_cases i <;> fin_cases j <;> first
    | exact absurd rfl hij
    | exact (p01 s u).1 | exact (p01 u s).2
    | exact (p20 s u).1 | exact (p20 u s).2
    | exact (p03 s u).1 | exact (p03 u s).2
    | exact (p21 s u).1 | exact (p21 u s).2
    | exact (p31 s u).1 | exact (p31 u s).2
    | exact (p23 s u).1 | exact (p23 u s).2

include hZ in
theorem self_vanish (hCp : IsPGroup 3 π.ker) (i : Fin 4) (s u : K) :
    liftPair hπ rhoR (lineF i s) (lineF i u) = 1 := by
  refine self_of_torus hπ hZ hCp i ?_ s u
  intro x hx
  let w : Kˣ := Units.mk0 x hx
  have hw : (w : K) = x := rfl
  fin_cases i
  · refine ⟨![w, 1, 1, w⁻¹], by simp [Fin.prod_univ_four], ?_⟩
    simpa [wtR] using hw
  · refine ⟨![w, w⁻¹, 1, 1], by simp [Fin.prod_univ_four], ?_⟩
    simpa [wtR] using hw
  · refine ⟨![1, w, 1, w⁻¹], by simp [Fin.prod_univ_four], ?_⟩
    simpa [wtR] using hw
  · refine ⟨![1, w, w⁻¹, 1], by simp [Fin.prod_univ_four], ?_⟩
    simpa [wtR] using hw

include hZ in
theorem rhoR_liftPair_eq_one (hCp : IsPGroup 3 π.ker) (hc : c ^ 2 ≠ 1)
    (x y : K × K × K × K) : liftPair hπ rhoR x y = 1 := by
  rw [lineF_decomp x, lineF_decomp y]
  refine liftPair_eq_one_of_sum hπ rhoR hZ Finset.univ Finset.univ _ _ (fun i _ j _ => ?_)
  by_cases hij : i = j
  · subst hij
    exact self_vanish hπ hZ hCp i _ _
  · exact pair_vanish hπ hZ c hc i j hij _ _

end Pairing

@[expose] def lineV0 : K →+ K × K := AddMonoidHom.inl K K

@[expose] def lineV1 : K →+ K × K := AddMonoidHom.inr K K

@[expose] def lineVF : Fin 2 → (K →+ K × K) := ![lineV0, lineV1]

theorem lineVF_decomp (y : K × K) : y = ∑ i, lineVF i (![y.1, y.2] i) := by
  rw [Fin.sum_univ_two]
  ext <;> simp [lineVF, lineV0, lineV1]

@[expose] def wtV (t : Fin 4 → Kˣ) (i : Fin 2) : K :=
  (t (![0, 2] i) : K) / (t (![1, 3] i) : K)

theorem conj_lineVF (t : Fin 4 → Kˣ) (ht : ∏ i, (t i : K) = 1) (i : Fin 2) (s : K) :
    diagSL t ht * rhoV (Multiplicative.ofAdd (lineVF i s)) * (diagSL t ht)⁻¹ =
      rhoV (Multiplicative.ofAdd (lineVF i (wtV t i * s))) := by
  fin_cases i <;>
    simp only [lineVF, Fin.zero_eta, Fin.mk_one, Matrix.cons_val_zero, Matrix.cons_val_one] <;>
    rw [diagSL_conj_rhoV] <;> congr 3 <;> simp [lineV0, lineV1]

section PairingV

variable {E : Type*} [Group E] {π : E →* SL(4, K)} (hπ : Function.Surjective π)
  (hZ : π.ker ≤ Subgroup.center E)

include hZ in
theorem V_cross_of_torus (t : Fin 4 → Kˣ) (ht : ∏ i, (t i : K) = 1) (hi : wtV t 0 = 1)
    (hj : wtV t 1 ≠ 1) (s u : K) :
    liftPair hπ rhoV (lineVF 0 s) (lineVF 1 u) = 1 ∧
      liftPair hπ rhoV (lineVF 1 u) (lineVF 0 s) = 1 :=
  ⟨liftPair_eq_one_of_scale_right hπ rhoV hZ (lineVF 0) (lineVF 1) (diagSL t ht) (wtV t 1) hj
    (fun s => by rw [conj_lineVF, hi, one_mul]) (fun u => conj_lineVF t ht 1 u) s u,
   liftPair_eq_one_of_scale_left hπ rhoV hZ (lineVF 1) (lineVF 0) (diagSL t ht) (wtV t 1) hj
    (fun u => conj_lineVF t ht 1 u) (fun s => by rw [conj_lineVF, hi, one_mul]) u s⟩

include hZ in
theorem V_self_vanish (hCp : IsPGroup 3 π.ker) (i : Fin 2) (s u : K) :
    liftPair hπ rhoV (lineVF i s) (lineVF i u) = 1 := by
  refine liftPair_self_eq_one_of_full hπ rhoV hZ (p := 3) (by norm_num) hCp (lineVF i)
    (fun x hx => ?_) s u
  let w : Kˣ := Units.mk0 x hx
  have hw : (w : K) = x := rfl
  fin_cases i
  · refine ⟨diagSL ![w, 1, 1, w⁻¹] (by simp [Fin.prod_univ_four]), fun s => ?_⟩
    rw [conj_lineVF]
    simp [wtV, hw]
  · refine ⟨diagSL ![1, w⁻¹, w, 1] (by simp [Fin.prod_univ_four]), fun s => ?_⟩
    rw [conj_lineVF]
    simp [wtV, hw]

include hZ in
theorem rhoV_liftPair_eq_one (hCp : IsPGroup 3 π.ker) (c : Kˣ) (hc : c ^ 2 ≠ 1)
    (x y : K × K) : liftPair hπ rhoV x y = 1 := by
  have hc2 : (c : K) ^ 2 ≠ 1 := fun h1 => hc (Units.ext (by simpa using h1))
  have p01 := fun s u => V_cross_of_torus hπ hZ ![1, 1, c, c⁻¹] (by simp [Fin.prod_univ_four])
    (by simp [wtV]) (by simp [wtV]; rw [← sq]; exact hc2) s u
  rw [lineVF_decomp x, lineVF_decomp y]
  refine liftPair_eq_one_of_sum hπ rhoV hZ Finset.univ Finset.univ _ _ (fun i _ j _ => ?_)
  fin_cases i <;> fin_cases j
  · exact V_self_vanish hπ hZ hCp 0 _ _
  · exact (p01 _ _).1
  · exact (p01 _ _).2
  · exact V_self_vanish hπ hZ hCp 1 _ _

end PairingV

end CFSG.ClassicalInvolution.Asc77.SCH
