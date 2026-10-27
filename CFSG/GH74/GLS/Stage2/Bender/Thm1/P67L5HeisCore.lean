module

public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67LnToralDeriv
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67L3Glue
public import CFSG.GH74.GLS.Stage2.OddAut.HeisField
public import CFSG.RankThree.SteinbergR3ELinearRegularUnipotent
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67CoreTools
public import CFSG.GH74.GLS.Stage2.OddAut.Lin3Aut

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1.Ln

open Subgroup Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.GH74.GLS.Stage2.Signalizer.Odd87 CFSG.GH74.GLS.Stage2.OddAut
open scoped commutatorElement

section Elements5

variable {K : Type} [Field K]

@[expose] def cyc5 : Matrix (Fin 5) (Fin 5) K := Matrix.of fun i j => if i = j + 1 then 1 else 0

theorem det_cyc5 : (cyc5 : Matrix (Fin 5) (Fin 5) K).det = 1 := by
  have h : (cyc5 : Matrix (Fin 5) (Fin 5) K) = Equiv.Perm.permMatrix K ((finRotate 5)⁻¹) := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [cyc5, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply] <;> decide
  rw [h, Matrix.det_permutation]
  simp

@[expose] noncomputable def torusSL5 (s : K) (hs : s ≠ 0) : Matrix.SpecialLinearGroup (Fin 5) K :=
  ⟨diagonal ![s ^ 4, s⁻¹, s⁻¹, s⁻¹, s⁻¹], by
    rw [det_diagonal, Fin.prod_univ_five]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons, Matrix.cons_val_three, Matrix.cons_val_four]
    field_simp⟩

@[expose] def cycSL5 : Matrix.SpecialLinearGroup (Fin 5) K := ⟨cyc5, det_cyc5⟩

@[expose] noncomputable def commSL5 (s : K) (hs : s ≠ 0) : Matrix.SpecialLinearGroup (Fin 5) K :=
  ⟨diagonal ![s ^ 5, (s ^ 5)⁻¹, 1, 1, 1], by
    rw [det_diagonal, Fin.prod_univ_five]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons, Matrix.cons_val_three, Matrix.cons_val_four]
    field_simp⟩

theorem commutator_torusSL5_cycSL5 (s : K) (hs : s ≠ 0) :
    ⁅torusSL5 s hs, cycSL5⁆ = commSL5 s hs := by
  have h : torusSL5 s hs * cycSL5 = commSL5 s hs * (cycSL5 * torusSL5 s hs) := by
    have hm : ((torusSL5 s hs * cycSL5 : Matrix.SpecialLinearGroup (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) =
        ((commSL5 s hs * (cycSL5 * torusSL5 s hs) : Matrix.SpecialLinearGroup (Fin 5) K) :
          Matrix (Fin 5) (Fin 5) K) := by
      rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
        Matrix.SpecialLinearGroup.coe_mul]
      show diagonal ![s ^ 4, s⁻¹, s⁻¹, s⁻¹, s⁻¹] * (cyc5 : Matrix (Fin 5) (Fin 5) K) =
        diagonal ![s ^ 5, (s ^ 5)⁻¹, 1, 1, 1] * ((cyc5 : Matrix (Fin 5) (Fin 5) K) *
          diagonal ![s ^ 4, s⁻¹, s⁻¹, s⁻¹, s⁻¹])
      ext i j
      rw [Matrix.diagonal_mul, Matrix.diagonal_mul, Matrix.mul_diagonal]
      fin_cases i <;> fin_cases j <;> simp [cyc5] <;> field_simp
    exact Subtype.ext hm
  rw [commutatorElement_def, h]
  group

theorem conjAut_proj_eq_of_smul_n {n : ℕ} {A : GL (Fin n) K} {g : Matrix.SpecialLinearGroup (Fin n) K} {c : Kˣ}
    (hc : c ^ n = 1)
    (h : (A : Matrix (Fin n) (Fin n) K) * (g : Matrix (Fin n) (Fin n) K) =
      (c : K) • ((g : Matrix (Fin n) (Fin n) K) * (A : Matrix (Fin n) (Fin n) K))) :
    conjAut n K A (proj n K g) = proj n K g := by
  rw [conjAut_proj]
  have hs : CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation n K A g =
      g * scalarElement c hc := by
    apply Subtype.ext
    rw [CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation_matrix,
      Units.mul_inv_eq_iff_eq_mul]
    have e1 : ((g * scalarElement c hc : Matrix.SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) =
        (c : K) • (g : Matrix (Fin n) (Fin n) K) := by
      rw [Matrix.SpecialLinearGroup.coe_mul, coe_scalarElement, Matrix.scalar_apply,
        ← Matrix.smul_one_eq_diagonal, Matrix.mul_smul, Matrix.mul_one]
    rw [e1, Matrix.smul_mul, h]
  rw [hs, map_mul, proj_eq_one_iff.mpr (scalarElement_mem_scalars c hc), mul_one]

end Elements5

section Algebra5

variable {K : Type} [Field K]

theorem eq_one_of_conj_diag_five [DecidableEq K] (X : GL (Fin 5) K) (a₁ a₂ b₁ b₂ lam : K)
    (h : (X : Matrix (Fin 5) (Fin 5) K) * diagonal ![a₁, a₂, 1, 1, 1] *
        ((X⁻¹ : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) = lam • diagonal ![b₁, b₂, 1, 1, 1]) :
    lam = 1 := by
  by_contra hlam
  have hXi : (X : Matrix (Fin 5) (Fin 5) K) * ((X⁻¹ : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hD1 : diagonal ![a₁, a₂, 1, 1, 1] - (1 : Matrix (Fin 5) (Fin 5) K) =
      diagonal ![a₁ - 1, a₂ - 1, 0, 0, 0] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  have hD2 : lam • diagonal ![b₁, b₂, 1, 1, 1] - (1 : Matrix (Fin 5) (Fin 5) K) =
      diagonal ![lam * b₁ - 1, lam * b₂ - 1, lam - 1, lam - 1, lam - 1] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  have hconj : (X : Matrix (Fin 5) (Fin 5) K) * diagonal ![a₁ - 1, a₂ - 1, 0, 0, 0] *
      ((X⁻¹ : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) =
      diagonal ![lam * b₁ - 1, lam * b₂ - 1, lam - 1, lam - 1, lam - 1] := by
    rw [← hD1, ← hD2, ← h, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hXi]
  have hXdet : IsUnit (X : Matrix (Fin 5) (Fin 5) K).det := by
    rw [← Matrix.isUnit_iff_isUnit_det]; exact X.isUnit
  have hXidet : IsUnit ((X⁻¹ : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K).det := by
    rw [← Matrix.isUnit_iff_isUnit_det]; exact (X⁻¹).isUnit
  have hrank : (diagonal ![lam * b₁ - 1, lam * b₂ - 1, lam - 1, lam - 1, lam - 1]).rank =
      (diagonal ![a₁ - 1, a₂ - 1, 0, 0, 0] : Matrix (Fin 5) (Fin 5) K).rank := by
    rw [← hconj, Matrix.rank_mul_eq_left_of_isUnit_det _ _ hXidet,
      Matrix.rank_mul_eq_right_of_isUnit_det _ _ hXdet]
  have hlam1 : lam - 1 ≠ 0 := sub_ne_zero.mpr hlam
  have h3 : 3 ≤ (diagonal ![lam * b₁ - 1, lam * b₂ - 1, lam - 1, lam - 1, lam - 1] :
      Matrix (Fin 5) (Fin 5) K).rank := by
    rw [Matrix.rank_diagonal, Fintype.card_subtype]
    have hsub : ({2, 3, 4} : Finset (Fin 5)) ⊆ Finset.univ.filter (fun i : Fin 5 =>
        (![lam * b₁ - 1, lam * b₂ - 1, lam - 1, lam - 1, lam - 1] : Fin 5 → K) i ≠ 0) := by
      intro i hi
      simp only [Finset.mem_insert, Finset.mem_singleton] at hi
      rcases hi with rfl | rfl | rfl <;> simp [hlam1]
    have := Finset.card_le_card hsub
    simpa using this
  have h2 : (diagonal ![a₁ - 1, a₂ - 1, 0, 0, 0] : Matrix (Fin 5) (Fin 5) K).rank ≤ 2 := by
    rw [Matrix.rank_diagonal, Fintype.card_subtype]
    have hsub : Finset.univ.filter (fun i : Fin 5 => (![a₁ - 1, a₂ - 1, 0, 0, 0] : Fin 5 → K) i ≠ 0) ⊆
        ({0, 1} : Finset (Fin 5)) := by
      intro i hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
      fin_cases i <;> simp_all
    exact (Finset.card_le_card hsub).trans (by simp)
  omega

theorem trace_argument_five (X : GL (Fin 5) K) {a u : K} (ha : a ≠ 0) (hu : u ≠ 0)
    (h : (X : Matrix (Fin 5) (Fin 5) K) * diagonal ![a, a⁻¹, 1, 1, 1] *
        ((X⁻¹ : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) = diagonal ![u, u⁻¹, 1, 1, 1]) :
    a = u ∨ a * u = 1 := by
  have h1 := congrArg Matrix.trace h
  rw [Matrix.trace_units_conj] at h1
  simp only [Matrix.trace_diagonal, Fin.sum_univ_five, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Matrix.cons_val_three,
    Matrix.cons_val_four] at h1
  have h2 : a + a⁻¹ = u + u⁻¹ := by linear_combination h1
  have haa : a * a⁻¹ = 1 := mul_inv_cancel₀ ha
  have huu : u * u⁻¹ = 1 := mul_inv_cancel₀ hu
  have h4 : (a - u) * (a * u - 1) = a * u * ((a + a⁻¹) - (u + u⁻¹)) := by
    linear_combination (-u) * haa + a * huu
  rw [h2, sub_self, mul_zero] at h4
  rcases mul_eq_zero.mp h4 with h | h
  · left; exact sub_eq_zero.mp h
  · right; exact sub_eq_zero.mp h

theorem generator_contradiction_five {p f : ℕ} (hp : p.Prime) (hp7 : 7 ≤ p) (hf : 1 ≤ f)
    (hK : Nat.card K = p ^ f) (τ : K ≃+* K) (hτ : τ ≠ 1) {g : K} (hg0 : g ≠ 0)
    (hgord : ∀ n : ℕ, g ^ n = 1 → p ^ f - 1 ∣ n) :
    ¬ (τ (g ^ 5) = g ^ 5 ∨ τ (g ^ 5) * g ^ 5 = 1) := by
  obtain ⟨k, hkf, hτk⟩ := exists_frobenius_pow hp hf hK τ
  have hk0 : k ≠ 0 := by
    rintro rfl
    apply hτ
    ext a
    rw [hτk, pow_zero, pow_one]
    rfl
  have hP7 : 7 ≤ p ^ k := calc 7 ≤ p := hp7
    _ = p ^ 1 := (pow_one p).symm
    _ ≤ p ^ k := Nat.pow_le_pow_right hp.pos (Nat.one_le_iff_ne_zero.mpr hk0)
  have hpf : 7 * p ^ k ≤ p ^ f := calc 7 * p ^ k ≤ p * p ^ k := Nat.mul_le_mul_right _ hp7
    _ = p ^ (k + 1) := by rw [pow_succ, mul_comm]
    _ ≤ p ^ f := Nat.pow_le_pow_right hp.pos hkf
  have hτg : τ (g ^ 5) = g ^ (5 * p ^ k) := by
    rw [hτk, ← pow_mul]
  rintro (h | h)
  · have h1 : g ^ (5 * p ^ k) = g ^ 5 := by rw [← hτg]; exact h
    have h2 : g ^ (5 * p ^ k - 5) = 1 := by
      rw [pow_sub₀ _ hg0 (by omega), h1, mul_inv_cancel₀ (pow_ne_zero 5 hg0)]
    have := Nat.le_of_dvd (by omega) (hgord _ h2)
    omega
  · have h1 : g ^ (5 * p ^ k + 5) = 1 := by
      rw [pow_add, ← hτg]; exact h
    have := Nat.le_of_dvd (by omega) (hgord _ h1)
    omega

end Algebra5

end CFSG.GH74.GLS.Stage2.Bender.Thm1.Ln

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1.Ln

open Subgroup Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.GH74.GLS.Stage2.Signalizer.Odd87 CFSG.GH74.GLS.Stage2.OddAut
open scoped commutatorElement

section Core5

variable {K : Type} [Field K] [Finite K]

theorem false_of_heis5_frame {p f : ℕ} (hp : p.Prime) (hp7 : 7 ≤ p) (hf : 1 ≤ f)
    (hK : Nat.card K = p ^ f) {ξ : K} (hξ1 : ξ ≠ 1) (hξ5 : ξ ^ 5 = 1)
    (hdiag : ∀ k : Fin 5, (fun i : Fin 5 => ξ ^ (i : ℕ)) k ≠ 0)
    {V Z : Subgroup (MulAut (projectiveSL 5 K))} (h2 : N2Cfg (projectiveSL 5 K) 5 V Z)
    (h3 : N3Deriv (projectiveSL 5 K) V Z)
    (hΔV : conjAut 5 K (diagGLK (fun i : Fin 5 => ξ ^ (i : ℕ)) hdiag) ∈ V)
    (hZD : ∀ z ∈ Z, z ∈ linearAutGroup 5 K → z = 1) : False := by
  classical
  obtain ⟨hr, hr2, -, -, -, hZodd, -, hZbot, -⟩ := id h2
  have hcen : Subgroup.center (projectiveSL 5 K) = ⊥ :=
    CFSG.RankThree.RegularUnipotent.center_projectiveSL_eq_bot (by norm_num)
  have hinj := mulAut_conj_injective_of_center_bot hcen
  have hξ0 : ξ ≠ 0 := by rintro rfl; simp at hξ5
  set Δ : GL (Fin 5) K := diagGLK (fun i : Fin 5 => ξ ^ (i : ℕ)) hdiag with hΔdef
  obtain ⟨z, hz1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hZbot
  have hzE : (z : MulAut (projectiveSL 5 K)) ∈ semilinearAutGroup 5 K := by
    refine mem_semilinearAutGroup_of_pow_eq_one (m := Nat.card ↥Z) (by norm_num) hZodd ?_
    have h' : z ^ Nat.card ↥Z = 1 := pow_card_eq_one'
    simpa only [Subgroup.coe_pow, Subgroup.coe_one] using congrArg Subtype.val h'
  obtain ⟨X, τ, hzXτ⟩ := mem_semilinearAutGroup_iff.mp hzE
  have hτ1 : τ ≠ 1 := by
    rintro rfl
    have hzD : (z : MulAut (projectiveSL 5 K)) ∈ linearAutGroup 5 K := by
      rw [hzXτ, map_one, mul_one]; exact conjAut_mem_linearAutGroup X
    exact hz1 (Subtype.ext (hZD _ z.2 hzD))
  have hv0 : conjAut 5 K Δ ≠ 1 := by
    intro h
    obtain ⟨u, hu⟩ := (conjAut_eq_one_iff_of_three_le (by norm_num : 3 ≤ 5) Δ).mp h
    have e0 := congrArg (fun A : GL (Fin 5) K => (A : Matrix (Fin 5) (Fin 5) K) 0 0) hu
    have e1 := congrArg (fun A : GL (Fin 5) K => (A : Matrix (Fin 5) (Fin 5) K) 1 1) hu
    simp [hΔdef, coe_diagGLK] at e0 e1
    exact hξ1 (e1.trans e0.symm)
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Kˣ)
  have hgord : ∀ n : ℕ, (g : K) ^ n = 1 → p ^ f - 1 ∣ n := by
    intro n hn
    have h1 : g ^ n = 1 := Units.ext (by simpa using hn)
    have hord := orderOf_eq_card_of_forall_mem_zpowers hg
    rw [Nat.card_units, hK] at hord
    rw [← hord]
    exact orderOf_dvd_of_pow_eq_one h1
  set s : K := (g : K) with hsdef
  have hs : s ≠ 0 := g.ne_zero
  have htfix : conjAut 5 K Δ (proj 5 K (torusSL5 s hs)) = proj 5 K (torusSL5 s hs) :=
    conjAut_diagGLK_proj_diag (fun i : Fin 5 => ξ ^ (i : ℕ)) hdiag (torusSL5 s hs)
      ![s ^ 4, s⁻¹, s⁻¹, s⁻¹, s⁻¹] rfl
  have hPfix : conjAut 5 K Δ (proj 5 K (cycSL5 : Matrix.SpecialLinearGroup (Fin 5) K)) =
      proj 5 K cycSL5 := by
    refine conjAut_proj_eq_of_smul_n (c := Units.mk0 ξ hξ0) ?_ ?_
    · exact Units.ext (by simpa using hξ5)
    · show ((diagGLK (fun i : Fin 5 => ξ ^ (i : ℕ)) hdiag : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) *
        (cyc5 : Matrix (Fin 5) (Fin 5) K) =
        ξ • ((cyc5 : Matrix (Fin 5) (Fin 5) K) *
          ((diagGLK (fun i : Fin 5 => ξ ^ (i : ℕ)) hdiag : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K))
      rw [coe_diagGLK]
      ext i j
      rw [diagonal_mul, Matrix.smul_apply, mul_diagonal]
      fin_cases i <;> fin_cases j <;> simp [cyc5]
      all_goals first | ring1 | linear_combination -hξ5
  have hcconj : ∀ u : projectiveSL 5 K, MulAut.conj u ∈ linearAutGroup 5 K := by
    intro u
    obtain ⟨g', rfl⟩ := proj_surjective 5 K u
    rw [← conjAut_toGL]
    exact conjAut_mem_linearAutGroup _
  set c : projectiveSL 5 K := proj 5 K (commSL5 s hs) with hcdef
  have hcmem : c ∈ ⁅fixSub (conjAut 5 K Δ), fixSub (conjAut 5 K Δ)⁆ := by
    have : c = ⁅proj 5 K (torusSL5 s hs), proj 5 K cycSL5⁆ := by
      rw [hcdef, ← map_commutatorElement, commutator_torusSL5_cycSL5]
    rw [this]
    exact Subgroup.commutator_mem_commutator (mem_fixSub.2 htfix) (mem_fixSub.2 hPfix)
  have hnorm := h3 _ hΔV hv0 c hcmem
  have hzc : (z : MulAut (projectiveSL 5 K)) c = c := by
    have hzZ : (z : MulAut (projectiveSL 5 K)) ∈ Z := z.2
    have h1 := (Subgroup.mem_normalizer_iff.mp hnorm _).mp hzZ
    have h4 : MulAut.conj c * (z : MulAut (projectiveSL 5 K)) * (MulAut.conj c)⁻¹ *
        (z : MulAut (projectiveSL 5 K))⁻¹ ∈ Z := Z.mul_mem h1 (Z.inv_mem hzZ)
    have h5 : MulAut.conj c * (z : MulAut (projectiveSL 5 K)) * (MulAut.conj c)⁻¹ *
        (z : MulAut (projectiveSL 5 K))⁻¹ =
        MulAut.conj (c * (z : MulAut (projectiveSL 5 K)) c⁻¹) := by
      have : (z : MulAut (projectiveSL 5 K)) * (MulAut.conj c)⁻¹ * (z : MulAut (projectiveSL 5 K))⁻¹ =
          MulAut.conj ((z : MulAut (projectiveSL 5 K)) c⁻¹) := by
        have := mulAut_conj_conj (z : MulAut (projectiveSL 5 K)) c⁻¹
        simpa [map_inv] using this
      calc MulAut.conj c * (z : MulAut (projectiveSL 5 K)) * (MulAut.conj c)⁻¹ *
            (z : MulAut (projectiveSL 5 K))⁻¹
          = MulAut.conj c * ((z : MulAut (projectiveSL 5 K)) * (MulAut.conj c)⁻¹ *
              (z : MulAut (projectiveSL 5 K))⁻¹) := by group
        _ = MulAut.conj (c * (z : MulAut (projectiveSL 5 K)) c⁻¹) := by rw [this, map_mul]
    rw [h5] at h4
    have h6 := hZD _ h4 (hcconj _)
    have h7 : c * (z : MulAut (projectiveSL 5 K)) c⁻¹ = 1 := hinj (by rw [h6, map_one])
    have h8 : (z : MulAut (projectiveSL 5 K)) c⁻¹ = c⁻¹ := by
      have := congrArg (fun t => c⁻¹ * t) h7
      simpa using this
    have := congrArg (fun t => t⁻¹) h8
    simpa using this
  have hzc' : conjAut 5 K X (fieldAut 5 K τ c) = c := by
    have := hzc
    rw [hzXτ, MulAut.mul_apply] at this
    exact this
  rw [hcdef, fieldAut_proj, conjAut_proj] at hzc'
  obtain ⟨c0, -, hmat⟩ := mem_scalars.mp (proj_eq_proj_iff.mp hzc')
  set A : Matrix.SpecialLinearGroup (Fin 5) K :=
    CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation 5 K X
      (Matrix.SpecialLinearGroup.map τ.toRingHom (commSL5 s hs)) with hAdef
  have hDA : ((commSL5 s hs : Matrix.SpecialLinearGroup (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) =
      (c0 : K) • (A : Matrix (Fin 5) (Fin 5) K) := by
    calc ((commSL5 s hs : Matrix.SpecialLinearGroup (Fin 5) K) : Matrix (Fin 5) (Fin 5) K)
        = ((A * (A⁻¹ * commSL5 s hs) : Matrix.SpecialLinearGroup (Fin 5) K) :
            Matrix (Fin 5) (Fin 5) K) := by rw [mul_inv_cancel_left]
      _ = (A : Matrix (Fin 5) (Fin 5) K) * Matrix.scalar (Fin 5) (c0 : K) := by
          rw [Matrix.SpecialLinearGroup.coe_mul, hmat]
      _ = (c0 : K) • (A : Matrix (Fin 5) (Fin 5) K) := by
          rw [Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal, Matrix.mul_smul, Matrix.mul_one]
  have hAmat : (A : Matrix (Fin 5) (Fin 5) K) = (X : Matrix (Fin 5) (Fin 5) K) *
      diagonal ![τ (s ^ 5), (τ (s ^ 5))⁻¹, 1, 1, 1] *
        ((X⁻¹ : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) := by
    rw [hAdef, CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation_matrix]
    congr 2
    show ((commSL5 s hs : Matrix.SpecialLinearGroup (Fin 5) K) : Matrix (Fin 5) (Fin 5) K).map τ = _
    show (diagonal ![s ^ 5, (s ^ 5)⁻¹, 1, 1, 1]).map τ = _
    rw [diagonal_map (map_zero τ)]
    congr 1
    funext i
    fin_cases i <;> simp [map_inv₀]
  have hc0 : (c0 : K) ≠ 0 := c0.ne_zero
  have hfinal : (X : Matrix (Fin 5) (Fin 5) K) * diagonal ![τ (s ^ 5), (τ (s ^ 5))⁻¹, 1, 1, 1] *
      ((X⁻¹ : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) =
      ((c0 : K)⁻¹) • diagonal ![s ^ 5, (s ^ 5)⁻¹, 1, 1, 1] := by
    rw [← hAmat]
    have : (A : Matrix (Fin 5) (Fin 5) K) = ((c0 : K)⁻¹) • ((c0 : K) • (A : Matrix (Fin 5) (Fin 5) K)) := by
      rw [inv_smul_smul₀ hc0]
    rw [this, ← hDA]
    rfl
  have hlam : ((c0 : K)⁻¹) = 1 := eq_one_of_conj_diag_five X _ _ _ _ _ hfinal
  rw [hlam, one_smul] at hfinal
  have hu0 : s ^ 5 ≠ 0 := pow_ne_zero 5 hs
  have hτu0 : τ (s ^ 5) ≠ 0 := (map_ne_zero τ).mpr hu0
  exact generator_contradiction_five hp hp7 hf hK τ hτ1 hs hgord
    (trace_argument_five X hτu0 hu0 hfinal)

end Core5

end CFSG.GH74.GLS.Stage2.Bender.Thm1.Ln
