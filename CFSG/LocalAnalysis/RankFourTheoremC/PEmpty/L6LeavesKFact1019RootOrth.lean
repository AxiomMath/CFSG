module

public import CFSG.GH74.Filter.Orthogonal.OddReflections
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFact1019Reduce
public import CFSG.RankThree.PartTwo.Census.Carrier.SpinBOdd
public import CFSG.RankThree.PartTwo.Census.Carrier.SpinTDOdd
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFact1019Hom

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.Fact1019

open CFSG.Open CFSG.ClassicalGroups.Orthogonal CFSG.GH74.Filter QuadraticMap

section RefFrame

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

abbrev FIdx : Type := Fin 3 ⊕ Unit ⊕ Fin 3

@[expose] def fnorm (K : Type*) [Field K] : FIdx → K
  | .inl _ => 1
  | .inr (.inl _) => 1
  | .inr (.inr _) => -1

@[expose] def yIdx : Fin 4 → FIdx := ![.inl 1, .inr (.inr 1), .inl 2, .inr (.inl ())]

theorem yIdx_injective : Function.Injective yIdx := by decide

theorem yIdx_ne_a0 (i : Fin 4) : yIdx i ≠ .inl 0 := by revert i; decide

theorem yIdx_ne_b0 (i : Fin 4) : yIdx i ≠ .inr (.inr 0) := by revert i; decide

theorem yIdx_ne_b2 (i : Fin 4) : yIdx i ≠ .inr (.inr 2) := by revert i; decide

structure RefData (Q : QuadraticForm K V) where
  P : Fin 3 → HypPair Q
  orth : ∀ i j, i ≠ j → (P i).Orth (P j)
  w : V
  Q_w : Q w = 1
  polar_we : ∀ i, polar Q w (P i).e = 0
  polar_wf : ∀ i, polar Q w (P i).f = 0

namespace RefData

variable (D : RefData Q)

@[expose] def v : FIdx → V
  | .inl i => (D.P i).e + (D.P i).f
  | .inr (.inl _) => D.w
  | .inr (.inr i) => (D.P i).e - (D.P i).f

theorem Q_v (i : FIdx) : Q (D.v i) = fnorm K i := by
  rcases i with i | ⟨⟩ | i
  · simp only [v, fnorm]
    rw [QuadraticMap.map_add Q, (D.P i).Q_e, (D.P i).Q_f, (D.P i).polar_ef]
    ring
  · exact D.Q_w
  · simp only [v, fnorm]
    rw [sub_eq_add_neg, QuadraticMap.map_add Q, QuadraticMap.map_neg, polar_neg_right,
      (D.P i).Q_e, (D.P i).Q_f, (D.P i).polar_ef]
    ring

theorem polar_a_a {i j : Fin 3} (h : i ≠ j) :
    polar Q ((D.P i).e + (D.P i).f) ((D.P j).e + (D.P j).f) = 0 := by
  have := D.orth i j h
  rw [polar_add_left, polar_add_right, polar_add_right, this.ee, this.ef, this.fe, this.ff]
  ring

theorem polar_b_b {i j : Fin 3} (h : i ≠ j) :
    polar Q ((D.P i).e - (D.P i).f) ((D.P j).e - (D.P j).f) = 0 := by
  have := D.orth i j h
  rw [polar_sub_left, polar_sub_right, polar_sub_right, this.ee, this.ef, this.fe, this.ff]
  ring

theorem polar_a_b (i j : Fin 3) :
    polar Q ((D.P i).e + (D.P i).f) ((D.P j).e - (D.P j).f) = 0 := by
  by_cases hij : i = j
  · subst hij
    rw [polar_add_left, polar_sub_right, polar_sub_right, (D.P i).polar_ee, (D.P i).polar_ef,
      (D.P i).polar_fe, (D.P i).polar_ff]
    ring
  · have := D.orth i j hij
    rw [polar_add_left, polar_sub_right, polar_sub_right, this.ee, this.ef, this.fe, this.ff]
    ring

theorem polar_a_w (i : Fin 3) : polar Q ((D.P i).e + (D.P i).f) D.w = 0 := by
  rw [polar_add_left, polar_comm Q (D.P i).e, polar_comm Q (D.P i).f, D.polar_we, D.polar_wf]
  ring

theorem polar_b_w (i : Fin 3) : polar Q ((D.P i).e - (D.P i).f) D.w = 0 := by
  rw [polar_sub_left, polar_comm Q (D.P i).e, polar_comm Q (D.P i).f, D.polar_we, D.polar_wf]
  ring

theorem polar_v (i j : FIdx) (h : i ≠ j) : polar Q (D.v i) (D.v j) = 0 := by
  rcases i with i | ⟨⟩ | i <;> rcases j with j | ⟨⟩ | j
  · exact D.polar_a_a (fun e => h (by rw [e]))
  · exact D.polar_a_w i
  · exact D.polar_a_b i j
  · rw [v, v, polar_comm Q]; exact D.polar_a_w j
  · exact absurd rfl h
  · rw [v, v, polar_comm Q]; exact D.polar_b_w j
  · rw [v, v, polar_comm Q]; exact D.polar_a_b j i
  · exact D.polar_b_w i
  · exact D.polar_b_b (fun e => h (by rw [e]))

theorem Q_ne_zero (i : FIdx) : Q (D.v i) ≠ 0 := by
  rw [D.Q_v]
  rcases i with i | ⟨⟩ | i <;> simp [fnorm]

theorem v_ne_zero (i : FIdx) : D.v i ≠ 0 := fun h =>
  D.Q_ne_zero i (by rw [h, QuadraticMap.map_zero])

noncomputable def R (i : FIdx) : V ≃ₗ[K] V := reflect Q (D.v i)

theorem R_mem (i : FIdx) : D.R i ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
  reflect_mem_orthogonalGroup Q _

theorem R_mul_self (i : FIdx) : D.R i * D.R i = 1 := reflect_mul_self Q _

theorem R_comm (i j : FIdx) : Commute (D.R i) (D.R j) := by
  by_cases h : i = j
  · rw [h]
  · exact reflect_comm (D.polar_v i j h)

@[expose] def sgn (K : Type*) [Field K] (i j : FIdx) : K := if i = j then -1 else 1

theorem R_apply_v (i j : FIdx) : D.R i (D.v j) = sgn K i j • D.v j := by
  rcases eq_or_ne i j with rfl | h
  · simp [R, sgn, reflect_apply_self (D.Q_ne_zero i)]
  · simp [R, sgn, h, reflect_apply_of_polar_eq_zero (D.polar_v i j h)]

theorem R_mul_R_mem (h2 : (2 : K) ≠ 0) {i i' : FIdx} (hne : i ≠ i')
    (hν : fnorm K i = fnorm K i') :
    D.R i * D.R i' ∈
      ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ :=
  reflect_mul_reflect_mem_commutator h2 (D.polar_v i i' hne) (by rw [D.Q_v, D.Q_v, hν])
    (D.Q_ne_zero i')

noncomputable def t : V ≃ₗ[K] V :=
  (D.R (.inl 0) * D.R (.inl 1)) * (D.R (.inr (.inr 0)) * D.R (.inr (.inr 1))) *
    (D.R (.inl 2) * D.R (.inr (.inl ())))

theorem t_mem_orthogonalGroup : D.t ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
  mul_mem (mul_mem (mul_mem (D.R_mem _) (D.R_mem _)) (mul_mem (D.R_mem _) (D.R_mem _)))
    (mul_mem (D.R_mem _) (D.R_mem _))

theorem t_mem_commutator (h2 : (2 : K) ≠ 0) :
    D.t ∈ ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ :=
  mul_mem (mul_mem (D.R_mul_R_mem h2 (by decide) rfl) (D.R_mul_R_mem h2 (by decide) rfl))
    (D.R_mul_R_mem h2 (by decide) rfl)

theorem commute_pair (i j k l : FIdx) : Commute (D.R i * D.R j) (D.R k * D.R l) :=
  (((D.R_comm i k).mul_right (D.R_comm i l)).mul_left
    ((D.R_comm j k).mul_right (D.R_comm j l)))

theorem pair_mul_self (i j : FIdx) : (D.R i * D.R j) * (D.R i * D.R j) = 1 := by
  calc D.R i * D.R j * (D.R i * D.R j) = D.R i * D.R i * (D.R j * D.R j) :=
        (D.R_comm j i).mul_mul_mul_comm _ _
    _ = 1 := by rw [D.R_mul_self, D.R_mul_self, one_mul]

theorem t_mul_self : D.t * D.t = 1 := by
  have h12 := D.commute_pair (.inl 0) (.inl 1) (.inr (.inr 0)) (.inr (.inr 1))
  have h13 := D.commute_pair (.inl 0) (.inl 1) (.inl 2) (.inr (.inl ()))
  have h23 := D.commute_pair (.inr (.inr 0)) (.inr (.inr 1)) (.inl 2) (.inr (.inl ()))
  have h12' : Commute (D.R (.inl 0) * D.R (.inl 1) * (D.R (.inr (.inr 0)) * D.R (.inr (.inr 1))))
      (D.R (.inl 2) * D.R (.inr (.inl ()))) := h13.mul_left h23
  have h1 : D.R (.inl 0) * D.R (.inl 1) * (D.R (.inr (.inr 0)) * D.R (.inr (.inr 1))) *
      (D.R (.inl 0) * D.R (.inl 1) * (D.R (.inr (.inr 0)) * D.R (.inr (.inr 1)))) = 1 := by
    calc _ = (D.R (.inl 0) * D.R (.inl 1)) * (D.R (.inl 0) * D.R (.inl 1)) *
          ((D.R (.inr (.inr 0)) * D.R (.inr (.inr 1))) *
            (D.R (.inr (.inr 0)) * D.R (.inr (.inr 1)))) :=
          h12.symm.mul_mul_mul_comm _ _
      _ = 1 := by rw [D.pair_mul_self, D.pair_mul_self, one_mul]
  unfold t
  calc _ = (D.R (.inl 0) * D.R (.inl 1) * (D.R (.inr (.inr 0)) * D.R (.inr (.inr 1)))) *
        (D.R (.inl 0) * D.R (.inl 1) * (D.R (.inr (.inr 0)) * D.R (.inr (.inr 1)))) *
        ((D.R (.inl 2) * D.R (.inr (.inl ()))) * (D.R (.inl 2) * D.R (.inr (.inl ())))) :=
        h12'.symm.mul_mul_mul_comm _ _
    _ = 1 := by rw [h1, D.pair_mul_self, one_mul]

theorem t_apply_v_ne (j : FIdx) (hj : j ≠ .inr (.inr 2)) : D.t (D.v j) = -D.v j := by
  rcases j with i | ⟨⟩ | i
  · fin_cases i <;> simp [t, LinearEquiv.mul_apply, R_apply_v, sgn]
  · simp [t, LinearEquiv.mul_apply, R_apply_v, sgn]
  · fin_cases i
    · simp [t, LinearEquiv.mul_apply, R_apply_v, sgn]
    · simp [t, LinearEquiv.mul_apply, R_apply_v, sgn]
    · exact absurd rfl hj

theorem t_apply_v_b2 : D.t (D.v (.inr (.inr 2))) = D.v (.inr (.inr 2)) := by
  simp [t, LinearEquiv.mul_apply, R_apply_v, sgn]

theorem t_not_mem_scalars (h2 : (2 : K) ≠ 0) : D.t ∉ scalars K V := by
  intro hmem
  obtain ⟨c, hc⟩ := mem_scalars.1 hmem
  have h1 := hc (D.v (.inl 0))
  rw [D.t_apply_v_ne _ (by decide)] at h1
  have h3 := hc (D.v (.inr (.inr 2)))
  rw [D.t_apply_v_b2] at h3
  have hc1 : c = -1 := by
    have : c • D.v (.inl 0) = (-1 : K) • D.v (.inl 0) := by rw [← h1, neg_one_smul]
    exact smul_left_injective K (D.v_ne_zero _) this
  have hc2 : c = 1 := by
    have : c • D.v (.inr (.inr 2)) = (1 : K) • D.v (.inr (.inr 2)) := by rw [← h3, one_smul]
    exact smul_left_injective K (D.v_ne_zero _) this
  apply h2
  linear_combination hc1 - hc2

@[expose] def e : V := D.v (.inl 0) + D.v (.inr (.inr 0))

@[expose] def y (i : Fin 4) : V := D.v (yIdx i)

theorem Q_e : Q D.e = 0 := by
  rw [e, QuadraticMap.map_add Q, D.Q_v, D.Q_v, D.polar_v _ _ (by decide)]
  simp [fnorm]

theorem polar_e_y (i : Fin 4) : polar Q D.e (D.y i) = 0 := by
  rw [e, polar_add_left, y, D.polar_v _ _ (yIdx_ne_a0 i).symm,
    D.polar_v _ _ (yIdx_ne_b0 i).symm, add_zero]

theorem polar_y_y {i j : Fin 4} (h : i ≠ j) : polar Q (D.y i) (D.y j) = 0 :=
  D.polar_v _ _ (fun h' => h (yIdx_injective h'))

theorem polar_a0_y (i : Fin 4) : polar Q (D.v (.inl 0)) (D.y i) = 0 :=
  D.polar_v _ _ (yIdx_ne_a0 i).symm

theorem polar_a0_e : polar Q (D.v (.inl 0)) D.e = 2 := by
  rw [e, polar_add_right, polar_self_eq_two_mul, D.polar_v _ _ (by decide), D.Q_v]
  simp [fnorm]

theorem t_apply_e : D.t D.e = -D.e := by
  rw [e, map_add, D.t_apply_v_ne _ (by decide), D.t_apply_v_ne _ (by decide)]
  abel

theorem t_apply_y (i : Fin 4) : D.t (D.y i) = -D.y i :=
  D.t_apply_v_ne _ (yIdx_ne_b2 i)

theorem polar_sum_y (x : V) (cf : Fin 4 → K) :
    polar Q x (∑ i, cf i • D.y i) = ∑ i, cf i * polar Q x (D.y i) := by
  have := map_sum (polarBilin Q x) (fun i => cf i • D.y i) Finset.univ
  simp only [polarBilin_apply_apply, map_smul, smul_eq_mul] at this
  exact this

@[expose] noncomputable def yvec {p : ℕ} [CharP K p] (c : Multiplicative (Fin 4 → ZMod p)) : V :=
  ∑ i, (ZMod.castHom (dvd_refl p) K (Multiplicative.toAdd c i)) • D.y i

theorem yvec_mul {p : ℕ} [CharP K p] (c c' : Multiplicative (Fin 4 → ZMod p)) :
    D.yvec (c * c') = D.yvec c + D.yvec c' := by
  simp only [yvec, toAdd_mul, Pi.add_apply, map_add, add_smul, Finset.sum_add_distrib]

theorem polar_e_yvec {p : ℕ} [CharP K p] (c : Multiplicative (Fin 4 → ZMod p)) :
    polar Q D.e (D.yvec c) = 0 := by
  rw [yvec, D.polar_sum_y]
  exact Finset.sum_eq_zero fun i _ => by rw [D.polar_e_y, mul_zero]

theorem polar_a0_yvec {p : ℕ} [CharP K p] (c : Multiplicative (Fin 4 → ZMod p)) :
    polar Q (D.v (.inl 0)) (D.yvec c) = 0 := by
  rw [yvec, D.polar_sum_y]
  exact Finset.sum_eq_zero fun i _ => by rw [D.polar_a0_y, mul_zero]

theorem yvec_eq_zero {p : ℕ} [Fact p.Prime] [CharP K p] (h2 : (2 : K) ≠ 0)
    (c : Multiplicative (Fin 4 → ZMod p)) (h : D.yvec c = 0) : c = 1 := by
  apply Multiplicative.toAdd.injective
  funext j
  have h1 := D.polar_sum_y (D.y j) (fun i => ZMod.castHom (dvd_refl p) K (Multiplicative.toAdd c i))
  rw [← yvec, h, polar_zero_right,
    Finset.sum_eq_single j (fun i _ hij => by rw [D.polar_y_y hij.symm, mul_zero]) (by simp),
    polar_self_eq_two_mul] at h1
  have h3 : ZMod.castHom (dvd_refl p) K (Multiplicative.toAdd c j) = 0 := by
    rcases mul_eq_zero.1 h1.symm with h' | h'
    · exact h'
    · exact absurd h' (mul_ne_zero h2 (D.Q_ne_zero _))
  rw [toAdd_one, Pi.zero_apply]
  exact (map_eq_zero_iff _ (ZMod.castHom (dvd_refl p) K).injective).1 h3

@[expose] noncomputable def eichHom {p : ℕ} [CharP K p] :
    Multiplicative (Fin 4 → ZMod p) →* (V ≃ₗ[K] V) :=
  MonoidHom.mk' (fun c => ClassicalGroups.Orthogonal.eichler Q D.e (D.yvec c)) fun c c' => by
    rw [D.yvec_mul, eichler_mul (D.polar_e_yvec c) (D.polar_e_yvec c')]

theorem eichHom_apply {p : ℕ} [CharP K p] (c : Multiplicative (Fin 4 → ZMod p)) :
    D.eichHom c = eichler Q D.e (D.yvec c) := rfl

theorem eichHom_injective {p : ℕ} [Fact p.Prime] [CharP K p] (h2 : (2 : K) ≠ 0) :
    Function.Injective (D.eichHom (p := p)) := by
  rw [injective_iff_map_eq_one]
  intro c hc
  apply D.yvec_eq_zero h2
  have h := congrArg (fun g : V ≃ₗ[K] V => g (D.v (.inl 0))) hc
  simp only [eichHom_apply, LinearEquiv.coe_one, id_eq] at h
  rw [eichler_apply D.Q_e (D.polar_e_yvec c), D.polar_a0_e, D.polar_a0_yvec] at h
  have h0 : (2 : K) • D.yvec c - (0 + Q (D.yvec c) * 2) • D.e = 0 := by
    rw [add_sub_assoc] at h
    exact add_eq_left.mp h
  have hQ : Q (D.yvec c) = 0 := by
    have h4 := congrArg (polar Q (D.v (.inl 0))) h0
    rw [polar_sub_right, polar_smul_right_eq, polar_smul_right_eq, D.polar_a0_yvec,
      D.polar_a0_e, polar_zero_right] at h4
    have h5 : (0 + Q (D.yvec c) * 2) * 2 = 0 := by linear_combination -h4
    rw [zero_add] at h5
    rcases mul_eq_zero.1 h5 with h' | h'
    · rcases mul_eq_zero.1 h' with h'' | h''
      · exact h''
      · exact absurd h'' h2
    · exact absurd h' h2
  rw [hQ, zero_mul, add_zero, zero_smul, sub_zero] at h0
  exact (smul_eq_zero.1 h0).resolve_left h2

theorem eichHom_mem_commutator {p : ℕ} [CharP K p]
    (hE : ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ =
      elementaryGroup Q) (c : Multiplicative (Fin 4 → ZMod p)) :
    D.eichHom c ∈ ⁅TauCeti.QuadraticMap.orthogonalGroup Q,
      TauCeti.QuadraticMap.orthogonalGroup Q⁆ := by
  rw [hE]
  exact eichler_mem_elementaryGroup Q _ _

theorem t_comm {p : ℕ} [CharP K p] (c : Multiplicative (Fin 4 → ZMod p)) :
    D.t * D.eichHom c = D.eichHom c * D.t := by
  have h1 := eichler_conj D.t_mem_orthogonalGroup D.e (D.yvec c)
  have hty : D.t (D.yvec c) = -D.yvec c := by
    simp only [yvec, map_sum, map_smul, D.t_apply_y, smul_neg, Finset.sum_neg_distrib]
  rw [D.t_apply_e, hty] at h1
  have h2 : eichler Q (-D.e) (-D.yvec c) = eichler Q D.e (D.yvec c) := by
    have := eichler_smul_left (Q := Q) (-1 : K) D.e (-D.yvec c)
    simpa using this
  rw [h2] at h1
  exact mul_inv_eq_iff_eq_mul.1 h1

end RefData

end RefFrame

section Transfer

open CFSG.Assembly.LowTwoRank

variable {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K] {p : ℕ} [Fact p.Prime]
  [CharP K p]

theorem RefData.eichHom_eq_one_of_mem_scalars {V : Type*} [AddCommGroup V] [Module K V]
    {Q : QuadraticForm K V} (D : RefData Q) (c : Multiplicative (Fin 4 → ZMod p))
    (hs : D.eichHom c ∈ scalars K V) : D.eichHom c = 1 := by
  obtain ⟨l, hl⟩ := mem_scalars.1 hs
  have hcp : c ^ p = 1 := by
    apply Multiplicative.toAdd.injective
    rw [toAdd_pow, toAdd_one]
    funext k
    simp [ZMod.natCast_self]
  have h1 : (D.eichHom c ^ p) (D.v (.inl 0)) = l ^ p • D.v (.inl 0) :=
    pow_apply_of_eigen (hl _) p
  rw [← map_pow, hcp, map_one] at h1
  have h2 : l ^ p = 1 := by
    have : l ^ p • D.v (.inl 0) = (1 : K) • D.v (.inl 0) := by rw [← h1]; simp
    exact smul_left_injective K (D.v_ne_zero _) this
  have hl1 : l = 1 := by
    have h3 : (l - 1) ^ p = 0 := by rw [sub_pow_char, h2, one_pow, sub_self]
    exact sub_eq_zero.1 ((pow_eq_zero_iff (Fact.out : p.Prime).ne_zero).1 h3)
  exact LinearEquiv.ext fun v => by rw [hl, hl1, one_smul]; rfl

theorem exists_involution_of_refData (hp2 : p ≠ 2) {Q : QuadraticForm K (ι → K)}
    {Q₀ : (ι → K) → K} (hQ : ⇑Q = Q₀)
    (hE : ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ =
      elementaryGroup Q) (D : RefData Q) :
    ∃ t : StatedProj (StatedOmega Q₀), orderOf t = 2 ∧
      ∃ E : Subgroup (StatedProj (StatedOmega Q₀)), E ≤ Subgroup.centralizer {t} ∧
        IsElemAbelian p E ∧ Nat.card E = p ^ 4 := by
  have h2 : (2 : K) ≠ 0 := two_ne_zero_of_charP p hp2
  have hΩ := statedOmega_eq_comap hQ
  let ψ : ((ι → K) ≃ₗ[K] (ι → K)) →* GL ι K := (toLinEquiv ι K).symm.toMonoidHom
  have hψ : ∀ g, toLinEquiv ι K (ψ g) = g := fun g => (toLinEquiv ι K).apply_symm_apply g
  have hmemΩ : ∀ g ∈ ⁅TauCeti.QuadraticMap.orthogonalGroup Q,
      TauCeti.QuadraticMap.orthogonalGroup Q⁆, ψ g ∈ StatedOmega Q₀ := by
    intro g hg
    rw [hΩ, Subgroup.mem_comap]
    change toLinEquiv ι K (ψ g) ∈ _
    rw [hψ]
    exact hg
  let f₀ : Multiplicative (Fin 4 → ZMod p) →* StatedOmega Q₀ :=
    (ψ.comp D.eichHom).codRestrict (StatedOmega Q₀)
      (fun c => hmemΩ _ (D.eichHom_mem_commutator hE c))
  let π := QuotientGroup.mk' ((StatedScalars ι K).subgroupOf (StatedOmega Q₀))
  let xt : StatedOmega Q₀ := ⟨ψ D.t, hmemΩ _ (D.t_mem_commutator h2)⟩
  have hker : ∀ x : StatedOmega Q₀, π x = 1 ↔ toLinEquiv ι K (x : GL ι K) ∈ scalars K (ι → K) := by
    intro x
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf,
      mem_statedScalars_iff]
  have hf₀ : ∀ c, toLinEquiv ι K ((f₀ c : StatedOmega Q₀) : GL ι K) = D.eichHom c :=
    fun c => hψ _
  have hxt : toLinEquiv ι K (xt : GL ι K) = D.t := hψ _
  have hinj : Function.Injective (π.comp f₀) := by
    rw [injective_iff_map_eq_one]
    intro c hc
    have hc' : π (f₀ c) = 1 := hc
    rw [hker, hf₀] at hc'
    exact D.eichHom_injective h2 (by rw [D.eichHom_eq_one_of_mem_scalars c hc', map_one])
  have ht_sq : π xt ^ 2 = 1 := by
    rw [← map_pow]
    have : xt ^ 2 = 1 := Subtype.ext (by
      change ψ D.t ^ 2 = 1
      rw [← map_pow, pow_two, D.t_mul_self, map_one])
    rw [this, map_one]
  have ht_ne : π xt ≠ 1 := by
    rw [Ne, hker, hxt]
    exact D.t_not_mem_scalars h2
  have hcomm : ∀ c, π xt * (π.comp f₀) c = (π.comp f₀) c * π xt := by
    intro c
    show π xt * π (f₀ c) = π (f₀ c) * π xt
    rw [← map_mul, ← map_mul]
    congr 1
    refine Subtype.ext ?_
    change ψ D.t * ψ (D.eichHom c) = ψ (D.eichHom c) * ψ D.t
    rw [← map_mul, ← map_mul, D.t_comm c]
  obtain ⟨E, hEc, hEab, hEcard⟩ := exists_subgroup_of_hom (π.comp f₀) hinj (π xt) hcomm
  exact ⟨π xt, orderOf_eq_prime ht_sq ht_ne, E, hEc, hEab, hEcard⟩

end Transfer

section Models

open CFSG.LieType.Universal.Spin

variable (K : Type) [Field K]

noncomputable def oddRefData {n : ℕ} (hn : 3 ≤ n) : RefData (quadOdd n K) where
  P i := oddPair K (Fin.castLE hn i)
  orth i j hij := oddPair_orth (fun h => hij (Fin.castLE_injective hn h))
  w := Pi.single (Sum.inr (Sum.inr ())) 1
  Q_w := by rw [quadOdd_apply]; simp
  polar_we i := by simp [oddPair_e, polar_quadOdd_single_inl]
  polar_wf i := by simp [oddPair_f, polar_quadOdd_single_inr_inl]

theorem Q_hyp_add {V : Type*} [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}
    (P : HypPair Q) : Q (P.e + P.f) = 1 := by
  rw [QuadraticMap.map_add Q, P.Q_e, P.Q_f, P.polar_ef]
  ring

noncomputable def plusRefData {n : ℕ} (hn : 4 ≤ n) : RefData (quadPlus n K) where
  P i := plusPair K (⟨i.val, by have := i.isLt; omega⟩ : Fin n)
  orth i j hij := plusPair_orth (fun h => hij (Fin.ext (Fin.mk.inj h)))
  w := (plusPair K (⟨3, by omega⟩ : Fin n)).e + (plusPair K (⟨3, by omega⟩ : Fin n)).f
  Q_w := Q_hyp_add K _
  polar_we i := by
    have h := plusPair_orth_three K hn i
    rw [polar_add_left, h.ee, h.fe, add_zero]
  polar_wf i := by
    have h := plusPair_orth_three K hn i
    rw [polar_add_left, h.ef, h.ff, add_zero]

noncomputable def minusRefData {n : ℕ} (b c : K) (hn : 4 ≤ n) :
    RefData (quadMinus n K b c) where
  P i := minusPair K b c (⟨i.val, by have := i.isLt; omega⟩ : Fin (n - 1))
  orth i j hij := minusPair_orth (fun h => hij (Fin.ext (Fin.mk.inj h)))
  w := Pi.single (Sum.inr (Sum.inr (0 : Fin 2))) 1
  Q_w := by rw [quadMinus_apply]; simp
  polar_we i := by simp [minusPair_e, polar_quadMinus_single_inl]
  polar_wf i := by simp [minusPair_f, polar_quadMinus_single_inr_inl]

end Models

section Families

open CFSG.LieType.Universal.Spin

theorem involution_typeB3 : InvolutionAt FamB3 := by
  intro K _ _ d hd ⟨e⟩ p hp hp2 hchar
  obtain ⟨r, q, hr, hdq⟩ := hd
  obtain ⟨dd, hv⟩ := d
  have hdq' : dd = TauCeti.LieTypeIndex.B r q := hdq
  subst hdq'
  have hchar' : p = q.p := by simpa using hchar
  subst hchar'
  haveI : Fact q.p.Prime := ⟨hp⟩
  obtain ⟨-, F, hF, hFfin, hcard, ⟨e'⟩⟩ :=
    CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeB_odd r q hv hp2 hr e
  haveI : Fintype F := Fintype.ofFinite F
  haveI : CharP F q.p :=
    charP_of_card_eq_prime_pow (f := q.exponent)
      (by rw [← Nat.card_eq_fintype_card]; exact hcard)
  obtain ⟨t, ht, E, hEc, hE, hcard'⟩ := exists_involution_of_refData (K := F) (p := q.p) hp2
    (coe_quadOdd r F) (commutator_orthogonalGroup_quadOdd (two_ne_zero_of_charP q.p hp2) hr)
    (oddRefData F hr)
  obtain ⟨t', ht', E', hEc', hE', hcard''⟩ := exists_involution_transport e' hEc hE hcard'
  exact ⟨t', ht'.trans ht, E', hEc', hE', hcard''⟩

theorem involution_typeD4 : InvolutionAt FamD4 := by
  intro K _ _ d hd ⟨e⟩ p hp hp2 hchar
  obtain ⟨r, q, hr, hdq⟩ := hd
  obtain ⟨dd, hv⟩ := d
  have hdq' : dd = TauCeti.LieTypeIndex.D r q := hdq
  subst hdq'
  have hchar' : p = q.p := by simpa using hchar
  subst hchar'
  haveI : Fact q.p.Prime := ⟨hp⟩
  obtain ⟨-, F, hF, hFfin, hcard, ⟨e'⟩⟩ :=
    CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeD r q hv e
  haveI : Fintype F := Fintype.ofFinite F
  haveI : CharP F q.p :=
    charP_of_card_eq_prime_pow (f := q.exponent)
      (by rw [← Nat.card_eq_fintype_card]; exact hcard)
  obtain ⟨t, ht, E, hEc, hE, hcard'⟩ := exists_involution_of_refData (K := F) (p := q.p) hp2
    (coe_quadPlus r F) (commutator_orthogonalGroup_quadPlus (by omega)) (plusRefData F hr)
  obtain ⟨t', ht', E', hEc', hE', hcard''⟩ := exists_involution_transport e' hEc hE hcard'
  exact ⟨t', ht'.trans ht, E', hEc', hE', hcard''⟩

theorem involution_typeTwistedD4 : InvolutionAt FamTwistedD4 := by
  intro K _ _ d hd ⟨e⟩ p hp hp2 hchar
  obtain ⟨r, q, hr, hdq⟩ := hd
  obtain ⟨dd, hv⟩ := d
  have hdq' : dd = TauCeti.LieTypeIndex.twistedD r q := hdq
  subst hdq'
  have hchar' : p = q.p := by simpa using hchar
  subst hchar'
  haveI : Fact q.p.Prime := ⟨hp⟩
  obtain ⟨-, F, hF, hFfin, hcard, b, c, hirr, ⟨e'⟩⟩ :=
    CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeTwistedD r q hv e
  haveI : Fintype F := Fintype.ofFinite F
  haveI : CharP F q.p :=
    charP_of_card_eq_prime_pow (f := q.exponent)
      (by rw [← Nat.card_eq_fintype_card]; exact hcard)
  obtain ⟨t, ht, E, hEc, hE, hcard'⟩ := exists_involution_of_refData (K := F) (p := q.p) hp2
    (coe_quadMinus r F b c) (commutator_orthogonalGroup_quadMinus hr hirr)
    (minusRefData F b c hr)
  obtain ⟨t', ht', E', hEc', hE', hcard''⟩ := exists_involution_transport e' hEc hE hcard'
  exact ⟨t', ht'.trans ht, E', hEc', hE', hcard''⟩

end Families

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.Fact1019
