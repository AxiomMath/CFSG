module

public import CFSG.LieType.Universal.SymplecticExtras.Matrices

public section

namespace CFSG.LieType.Universal.Symplectic.SpExtras

open Matrix CFSG.LieType.RootSystem CFSG.LieType.Steinberg CFSG.Assembly.LowTwoRank
  TauCeti.GLSymplecticFin
open scoped commutatorElement

variable {n : ℕ} {F : Type} [Field F]

def IsSp (N : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) : Prop :=
  Nᵀ * J (Fin n) F = -(J (Fin n) F * N)

section Sp

variable {N M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F}

theorem J_mul_apply_inl (N : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) (k : Fin n)
    (b : Fin n ⊕ Fin n) : (J (Fin n) F * N) (.inl k) b = -N (.inr k) b := by
  simp [Matrix.mul_apply, Matrix.J, Fintype.sum_sum_type, Matrix.one_apply]

theorem J_mul_apply_inr (N : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) (k : Fin n)
    (b : Fin n ⊕ Fin n) : (J (Fin n) F * N) (.inr k) b = N (.inl k) b := by
  simp [Matrix.mul_apply, Matrix.J, Fintype.sum_sum_type, Matrix.one_apply]

theorem transpose_mul_J_apply_inl (N : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F)
    (a : Fin n ⊕ Fin n) (l : Fin n) : (Nᵀ * J (Fin n) F) a (.inl l) = N (.inr l) a := by
  simp [Matrix.mul_apply, Matrix.J, Fintype.sum_sum_type, Matrix.one_apply]

theorem transpose_mul_J_apply_inr (N : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F)
    (a : Fin n ⊕ Fin n) (l : Fin n) : (Nᵀ * J (Fin n) F) a (.inr l) = -N (.inl l) a := by
  simp [Matrix.mul_apply, Matrix.J, Fintype.sum_sum_type, Matrix.one_apply]

theorem isSp_iff : IsSp N ↔ (∀ k l, N (.inr l) (.inl k) = N (.inr k) (.inl l)) ∧
    (∀ k l, N (.inl l) (.inl k) + N (.inr k) (.inr l) = 0) ∧
    (∀ k l, N (.inl k) (.inr l) = N (.inl l) (.inr k)) := by
  constructor
  · intro h
    refine ⟨fun k l => ?_, fun k l => ?_, fun k l => ?_⟩
    · have := congrFun (congrFun h (.inl k)) (.inl l)
      rw [transpose_mul_J_apply_inl, Matrix.neg_apply, J_mul_apply_inl, neg_neg] at this
      exact this
    · have := congrFun (congrFun h (.inl k)) (.inr l)
      rw [transpose_mul_J_apply_inr, Matrix.neg_apply, J_mul_apply_inl, neg_neg] at this
      linear_combination -this
    · have := congrFun (congrFun h (.inr k)) (.inr l)
      rw [transpose_mul_J_apply_inr, Matrix.neg_apply, J_mul_apply_inr] at this
      linear_combination this
  · rintro ⟨hA, hB, hC⟩
    ext a b
    rcases a with k | k <;> rcases b with l | l
    · rw [transpose_mul_J_apply_inl, Matrix.neg_apply, J_mul_apply_inl, neg_neg]
      exact hA k l
    · rw [transpose_mul_J_apply_inr, Matrix.neg_apply, J_mul_apply_inl, neg_neg]
      linear_combination -hB k l
    · rw [transpose_mul_J_apply_inl, Matrix.neg_apply, J_mul_apply_inr]
      linear_combination hB l k
    · rw [transpose_mul_J_apply_inr, Matrix.neg_apply, J_mul_apply_inr]
      rw [hC l k]

theorem IsSp.zero : IsSp (0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) := by
  simp [IsSp]

theorem IsSp.add (hN : IsSp N) (hM : IsSp M) : IsSp (N + M) := by
  unfold IsSp at *
  rw [Matrix.transpose_add, Matrix.add_mul, hN, hM, Matrix.mul_add, neg_add]

theorem IsSp.smul (c : F) (hN : IsSp N) : IsSp (c • N) := by
  unfold IsSp at *
  rw [Matrix.transpose_smul, Matrix.smul_mul, hN, Matrix.mul_smul, smul_neg]

theorem IsSp.neg (hN : IsSp N) : IsSp (-N) := by
  have := hN.smul (-1)
  rwa [neg_one_smul] at this

theorem IsSp.sub (hN : IsSp N) (hM : IsSp M) : IsSp (N - M) := by
  rw [sub_eq_add_neg]
  exact hN.add hM.neg

theorem IsSp.lie (hN : IsSp N) (hM : IsSp M) : IsSp (N * M - M * N) := by
  unfold IsSp at *
  rw [Matrix.transpose_sub, Matrix.transpose_mul, Matrix.transpose_mul]
  have e1 : (Mᵀ * Nᵀ - Nᵀ * Mᵀ) * J (Fin n) F =
      Mᵀ * (Nᵀ * J (Fin n) F) - Nᵀ * (Mᵀ * J (Fin n) F) := by noncomm_ring
  rw [e1, hN, hM]
  have e2 : Mᵀ * -(J (Fin n) F * N) - Nᵀ * -(J (Fin n) F * M) =
      -(Mᵀ * J (Fin n) F * N) + Nᵀ * J (Fin n) F * M := by noncomm_ring
  rw [e2, hN, hM]
  noncomm_ring

theorem IsSp.triple (hN : IsSp N) (hM : IsSp M) : IsSp (N * M * N) := by
  unfold IsSp at *
  rw [Matrix.transpose_mul, Matrix.transpose_mul]
  have e1 : Nᵀ * (Mᵀ * Nᵀ) * J (Fin n) F = Nᵀ * Mᵀ * (Nᵀ * J (Fin n) F) := by noncomm_ring
  rw [e1, hN]
  have e2 : Nᵀ * Mᵀ * -(J (Fin n) F * N) = -(Nᵀ * (Mᵀ * J (Fin n) F) * N) := by noncomm_ring
  rw [e2, hM]
  have e3 : -(Nᵀ * -(J (Fin n) F * M) * N) = Nᵀ * J (Fin n) F * M * N := by noncomm_ring
  rw [e3, hN]
  noncomm_ring

end Sp

theorem isSp_E (r : RootSubgroupIndex n) : IsSp (E F r) := by
  rw [isSp_iff]
  refine ⟨fun k l => ?_, fun k l => ?_, fun k l => ?_⟩ <;>
    cases r <;> simp only [E, Matrix.sub_apply, Matrix.add_apply, Matrix.single_apply,
      Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq, false_and, and_false, ite_false] <;>
    (try split_ifs) <;> first | (simp; done) | (exfalso; tauto)

theorem eq_smul_E (r : RootSubgroupIndex n) {N : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F}
    (hN : IsSp N) (hdeg : HasDeg (stdVec r) N) : N = N (pos1 r).1 (pos1 r).2 • E F r := by
  have h2 : N (pos2 r).1 (pos2 r).2 = (sgn2 r : F) * N (pos1 r).1 (pos1 r).2 := by
    obtain ⟨hA, hB, hC⟩ := isSp_iff.1 hN
    cases r with
    | positiveLong i => simp [pos1, pos2, sgn2]
    | negativeLong i => simp [pos1, pos2, sgn2]
    | difference i j hij =>
      have := hB j i
      simp only [pos1, pos2, sgn2, Int.reduceNeg, Int.cast_neg, Int.cast_one]
      linear_combination this
    | positiveSum i j hij =>
      have := hC j i
      simpa [pos1, pos2, sgn2] using this
    | negativeSum i j hij =>
      have := hA i j
      simpa [pos1, pos2, sgn2] using this
  ext a b
  rw [Matrix.smul_apply, smul_eq_mul]
  by_cases h1 : (a, b) = pos1 r
  · rw [show a = (pos1 r).1 from congrArg Prod.fst h1,
      show b = (pos1 r).2 from congrArg Prod.snd h1, E_pos1, mul_one]
  by_cases h2' : (a, b) = pos2 r
  · rw [show a = (pos2 r).1 from congrArg Prod.fst h2', show b = (pos2 r).2 from
      congrArg Prod.snd h2', E_pos2, h2, mul_comm]
  · rw [E_eq_zero r h1 h2', mul_zero]
    by_contra hne
    rcases eq_pos_of_wt_sub r a b (hdeg a b hne) with h | h
    exacts [h1 h, h2' h]

theorem dot_wt_sub {a b : Fin n ⊕ Fin n} (hab : a ≠ b) :
    (wt a - wt b) ⬝ᵥ (wt a - wt b) = 2 ∨ (wt a - wt b) ⬝ᵥ (wt a - wt b) = 4 := by
  rcases a with i | i <;> rcases b with j | j <;>
    simp only [wt, dotProduct_sub, dotProduct_neg, dotProduct_single, Pi.single_apply,
      Pi.neg_apply, Pi.sub_apply, mul_one, ne_eq, Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq,
      not_false_eq_true] at hab ⊢ <;>
    split_ifs <;> omega

theorem dot_of_isPosWt {v : Fin n → ℤ} (hv : IsPosWt v) (h0 : v ≠ 0) :
    v ⬝ᵥ v = 2 ∨ v ⬝ᵥ v = 4 := by
  obtain ⟨a, b, rfl⟩ := hv
  have hab : a ≠ b := by
    rintro rfl
    exact h0 (sub_self _)
  exact dot_wt_sub hab

theorem dot_stdVec (r : RootSubgroupIndex n) :
    stdVec r ⬝ᵥ stdVec r = 2 ∨ stdVec r ⬝ᵥ stdVec r = 4 := by
  rw [← wt_pos1 r]
  exact dot_wt_sub (pos1_ne r)

theorem dot_comb (e f : Fin n → ℤ) (i j : ℕ) :
    (i • e + j • f) ⬝ᵥ (i • e + j • f) =
      (i : ℤ) * i * (e ⬝ᵥ e) + 2 * i * j * (e ⬝ᵥ f) + (j : ℤ) * j * (f ⬝ᵥ f) := by
  simp only [add_dotProduct, dotProduct_add, smul_dotProduct, dotProduct_smul]
  simp only [nsmul_eq_mul, dotProduct_comm f e]
  ring

theorem smul_E_mul_self (r : RootSubgroupIndex n) (c : F) : (c • E F r) * (c • E F r) = 0 := by
  have h := congrArg (mat n F) (elt_add r (-c) c)
  rw [neg_add_cancel, elt_zero, map_one, map_mul, mat_elt, mat_elt, neg_smul] at h
  generalize c • E F r = X at h ⊢
  have e : (1 + -X) * (1 + X) = 1 - X * X := by noncomm_ring
  rw [e, eq_comm, sub_eq_self] at h
  exact h

theorem mat_elt_inv (r : RootSubgroupIndex n) (c : F) :
    mat n F (elt r c)⁻¹ = 1 - c • E F r := by
  rw [← elt_neg, mat_elt, neg_smul, sub_eq_add_neg]

theorem exists_mem_cone_of_isSp {γ δ : Fin n → ℤ} {r r' : RootSubgroupIndex n}
    (hr : stdVec r = toStd n γ) (hr' : stdVec r' = toStd n δ)
    (hne : ∀ i j : ℕ, 0 < i → 0 < j → i • stdVec r + j • stdVec r' ≠ 0)
    (i j : ℕ) (hi : 0 < i) (hj : 0 < j) {N : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F}
    (hN : IsSp N) (hdeg : HasDeg (i • stdVec r + j • stdVec r') N) :
    ∃ g ∈ ⨆ ε ∈ openCone (roots (isFiniteType_cartanC n) ∅) γ δ, rootGroup n F ε,
      mat n F g = 1 + N := by
  by_cases hpw : IsPosWt (i • stdVec r + j • stdVec r')
  · obtain ⟨r'', hr''⟩ := exists_stdVec_of_isPosWt hpw (hne i j hi hj)
    have hε : stdVec r'' = toStd n (i • γ + j • δ) := by
      rw [toStd_add', toStd_nsmul', toStd_nsmul', ← hr, ← hr', hr'']
    refine ⟨elt r'' (N (pos1 r'').1 (pos1 r'').2), ?_, ?_⟩
    · exact le_iSup₂_of_le (f := fun ε (_ : ε ∈ openCone (roots (isFiniteType_cartanC n) ∅) γ δ) =>
        rootGroup n F ε) (i • γ + j • δ) ⟨mem_roots_of_stdVec hε, i, j, hi, hj, rfl⟩ le_rfl
        (elt_mem_rootGroup hε _)
    · rw [mat_elt, ← eq_smul_E r'' hN (hdeg.congr hr''.symm)]
  · exact ⟨1, one_mem _, by rw [map_one, hdeg.eq_zero hpw, add_zero]⟩

theorem commutator_mem {γ δ : Fin n → ℤ} (hγ : γ ∈ roots (isFiniteType_cartanC n) ∅)
    (hδ : δ ∈ roots (isFiniteType_cartanC n) ∅) (hind : LinIndepPair γ δ)
    {x y : StatedSp n F} (hx : x ∈ rootGroup n F γ) (hy : y ∈ rootGroup n F δ) :
    ⁅x, y⁆ ∈ ⨆ ε ∈ openCone (roots (isFiniteType_cartanC n) ∅) γ δ, rootGroup n F ε := by
  obtain ⟨r, hr⟩ := exists_stdVec_of_mem_roots hγ
  obtain ⟨r', hr'⟩ := exists_stdVec_of_mem_roots hδ
  obtain ⟨a, rfl⟩ := (mem_rootGroup_iff hr).1 hx
  obtain ⟨b, rfl⟩ := (mem_rootGroup_iff hr').1 hy
  set e := stdVec r with he
  set f := stdVec r' with hf
  have hne : ∀ i j : ℕ, 0 < i → 0 < j → i • e + j • f ≠ 0 := by
    intro i j hi hj h0
    have h1 : toStd n (i • γ + j • δ) = toStd n 0 := by
      rw [toStd_add', toStd_nsmul', toStd_nsmul', ← hr, ← hr', toStd_zero', h0]
    have h2 := toStd_inj h1
    have h3 := hind i j (by rw [natCast_zsmul, natCast_zsmul]; exact h2)
    omega
  have hdot : ∀ i j : ℕ, 0 < i → 0 < j → IsPosWt (i • e + j • f) →
      (i : ℤ) * i * (e ⬝ᵥ e) + 2 * i * j * (e ⬝ᵥ f) + (j : ℤ) * j * (f ⬝ᵥ f) = 2 ∨
      (i : ℤ) * i * (e ⬝ᵥ e) + 2 * i * j * (e ⬝ᵥ f) + (j : ℤ) * j * (f ⬝ᵥ f) = 4 := by
    intro i j hi hj h
    rw [← dot_comb]
    exact dot_of_isPosWt h (hne i j hi hj)
  have hdA := dot_stdVec r
  have hdB := dot_stdVec r'
  rw [← he] at hdA
  rw [← hf] at hdB
  set A := a • E F r with hAdef
  set B := b • E F r' with hBdef
  have hA : IsSp A := (isSp_E r).smul a
  have hB : IsSp B := (isSp_E r').smul b
  have hAd : HasDeg e A := (hasDeg_E r).smul a
  have hBd : HasDeg f B := (hasDeg_E r').smul b
  have hAA : A * A = 0 := smul_E_mul_self r a
  have hBB : B * B = 0 := smul_E_mul_self r' b
  have dAB : HasDeg (1 • e + 1 • f) (A * B) := (hAd.mul hBd).congr (by abel)
  have dBA : HasDeg (1 • e + 1 • f) (B * A) := (hBd.mul hAd).congr (by abel)
  have d1 : HasDeg (1 • e + 1 • f) (A * B - B * A) := dAB.sub dBA
  have d2 : HasDeg (2 • e + 1 • f) (-(A * B * A)) := ((hAd.mul hBd).mul hAd).neg.congr (by abel)
  have d3 : HasDeg (1 • e + 2 • f) (B * A * B) := ((hBd.mul hAd).mul hBd).congr (by abel)
  have d4 : HasDeg (2 • e + 2 • f) (A * B * A * B) :=
    (((hAd.mul hBd).mul hAd).mul hBd).congr (by abel)
  have hAB0 : ¬IsPosWt (1 • e + 1 • f) → A * B = 0 := fun h => dAB.eq_zero h
  have hBA0 : ¬IsPosWt (1 • e + 1 • f) → B * A = 0 := fun h => dBA.eq_zero h
  have hN4 : A * B * A * B = 0 := by
    by_cases h11 : IsPosWt (1 • e + 1 • f)
    · refine d4.eq_zero fun h22 => ?_
      have := hdot 1 1 one_pos one_pos h11
      have := hdot 2 2 two_pos two_pos h22
      push_cast at *
      omega
    · rw [hAB0 h11]
      simp
  have hN2 : ¬IsPosWt (1 • e + 1 • f) → -(A * B * A) = 0 := fun h => by
    rw [hAB0 h, zero_mul, neg_zero]
  have hN3 : ¬IsPosWt (1 • e + 1 • f) → B * A * B = 0 := fun h => by
    rw [hBA0 h, zero_mul]
  have hN12 : (A * B - B * A) * -(A * B * A) = 0 := by
    by_cases h11 : IsPosWt (1 • e + 1 • f)
    · by_cases h21 : IsPosWt (2 • e + 1 • f)
      · have e32 : (1 • e + 1 • f) + (2 • e + 1 • f) = 3 • e + 2 • f := by abel
        refine ((d1.mul d2).congr e32).eq_zero fun h32 => ?_
        have := hdot 1 1 one_pos one_pos h11
        have := hdot 2 1 two_pos one_pos h21
        have := hdot 3 2 (by norm_num) two_pos h32
        push_cast at *
        omega
      · rw [d2.eq_zero h21, mul_zero]
    · rw [hN2 h11, mul_zero]
  have hN13 : (A * B - B * A) * (B * A * B) = 0 := by
    by_cases h11 : IsPosWt (1 • e + 1 • f)
    · by_cases h12 : IsPosWt (1 • e + 2 • f)
      · have e23 : (1 • e + 1 • f) + (1 • e + 2 • f) = 2 • e + 3 • f := by abel
        refine ((d1.mul d3).congr e23).eq_zero fun h23 => ?_
        have := hdot 1 1 one_pos one_pos h11
        have := hdot 1 2 one_pos two_pos h12
        have := hdot 2 3 two_pos (by norm_num) h23
        push_cast at *
        omega
      · rw [d3.eq_zero h12, mul_zero]
    · rw [hN3 h11, mul_zero]
  have hN23 : -(A * B * A) * (B * A * B) = 0 := by
    by_cases h11 : IsPosWt (1 • e + 1 • f)
    · by_cases h21 : IsPosWt (2 • e + 1 • f)
      · have h12 : ¬IsPosWt (1 • e + 2 • f) := fun h12 => by
          have := hdot 1 1 one_pos one_pos h11
          have := hdot 2 1 two_pos one_pos h21
          have := hdot 1 2 one_pos two_pos h12
          push_cast at *
          omega
        rw [d3.eq_zero h12, mul_zero]
      · rw [d2.eq_zero h21, zero_mul]
    · rw [hN2 h11, zero_mul]
  have hmat : mat n F ⁅elt r a, elt r' b⁆ =
      (1 + (A * B - B * A)) * (1 + -(A * B * A)) * (1 + B * A * B) := by
    rw [commutatorElement_def, map_mul, map_mul, map_mul, mat_elt, mat_elt, mat_elt_inv,
      mat_elt_inv]
    have hexp : (1 + A) * (1 + B) * (1 - A) * (1 - B) =
        1 + (A * B - B * A) + -(A * B * A) + B * A * B + A * B * A * B - A * A - B * B -
          A * (B * B) + A * A * B := by noncomm_ring
    have hprod : (1 + (A * B - B * A)) * (1 + -(A * B * A)) * (1 + B * A * B) =
        1 + (A * B - B * A) + -(A * B * A) + B * A * B + (A * B - B * A) * -(A * B * A) +
          (A * B - B * A) * (B * A * B) + -(A * B * A) * (B * A * B) +
          (A * B - B * A) * -(A * B * A) * (B * A * B) := by noncomm_ring
    rw [hexp, hprod, hN12, hN13, hN23, hN4, hAA, hBB]
    simp
  obtain ⟨g1, hg1, h1⟩ := exists_mem_cone_of_isSp hr hr' hne 1 1 one_pos one_pos (hA.lie hB) d1
  obtain ⟨g2, hg2, h2⟩ := exists_mem_cone_of_isSp hr hr' hne 2 1 two_pos one_pos
    (hA.triple hB).neg d2
  obtain ⟨g3, hg3, h3⟩ := exists_mem_cone_of_isSp hr hr' hne 1 2 one_pos two_pos (hB.triple hA) d3
  have hg : ⁅elt r a, elt r' b⁆ = g1 * g2 * g3 := by
    apply mat_injective
    rw [hmat, map_mul, map_mul, h1, h2, h3]
  rw [hg]
  exact mul_mem (mul_mem hg1 hg2) hg3

end CFSG.LieType.Universal.Symplectic.SpExtras
