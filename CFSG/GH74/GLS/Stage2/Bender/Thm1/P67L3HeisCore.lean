module

public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67L3GenDeriv
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67L3Glue
public import CFSG.GH74.GLS.Stage2.OddAut.HeisField
public import CFSG.GH74.GLS.Stage2.OddAut.Lin3Aut
public import CFSG.RankThree.SteinbergR3ELinearRegularUnipotent
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67CoreTools

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1

open Subgroup Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.GH74.GLS.Stage2.Signalizer.Odd87
open scoped commutatorElement

section Elements

variable {K : Type} [Field K]

@[expose] noncomputable def torusSL (s : K) (hs : s ≠ 0) : SpecialLinearGroup (Fin 3) K :=
  ⟨diagonal ![s ^ 2, s⁻¹, s⁻¹], by
    rw [det_diagonal, Fin.prod_univ_three]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons]
    field_simp⟩

@[expose] def cycSL : SpecialLinearGroup (Fin 3) K :=
  ⟨Matrix.of ![![0, 0, 1], ![1, 0, 0], ![0, 1, 0]], by
    rw [det_fin_three]; simp⟩

@[expose] noncomputable def commSL (s : K) (hs : s ≠ 0) : SpecialLinearGroup (Fin 3) K :=
  ⟨diagonal ![s ^ 3, (s ^ 3)⁻¹, 1], by
    rw [det_diagonal, Fin.prod_univ_three]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons]
    field_simp⟩

theorem commutator_torusSL_cycSL (s : K) (hs : s ≠ 0) :
    ⁅torusSL s hs, cycSL⁆ = commSL s hs := by
  have h : torusSL s hs * cycSL = commSL s hs * (cycSL * torusSL s hs) := by
    have hm : ((torusSL s hs * cycSL : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
        ((commSL s hs * (cycSL * torusSL s hs) : SpecialLinearGroup (Fin 3) K) :
          Matrix (Fin 3) (Fin 3) K) := by
      rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
      show diagonal ![s ^ 2, s⁻¹, s⁻¹] * Matrix.of ![![0, 0, 1], ![1, 0, 0], ![0, 1, 0]] =
        diagonal ![s ^ 3, (s ^ 3)⁻¹, 1] * (Matrix.of ![![0, 0, 1], ![1, 0, 0], ![0, 1, 0]] *
          diagonal ![s ^ 2, s⁻¹, s⁻¹])
      ext i j
      rw [Matrix.diagonal_mul, Matrix.diagonal_mul, Matrix.mul_diagonal]
      fin_cases i <;> fin_cases j <;> simp <;> field_simp
    exact Subtype.ext hm
  rw [commutatorElement_def, h]
  group

theorem conjAut_proj_eq_of_smul {A : GL (Fin 3) K} {g : Matrix.SpecialLinearGroup (Fin 3) K} {c : Kˣ}
    (hc : c ^ 3 = 1)
    (h : (A : Matrix (Fin 3) (Fin 3) K) * (g : Matrix (Fin 3) (Fin 3) K) =
      (c : K) • ((g : Matrix (Fin 3) (Fin 3) K) * (A : Matrix (Fin 3) (Fin 3) K))) :
    conjAut 3 K A (proj 3 K g) = proj 3 K g := by
  rw [conjAut_proj]
  have hs : CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation 3 K A g =
      g * scalarElement c hc := by
    apply Subtype.ext
    rw [CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation_matrix,
      Units.mul_inv_eq_iff_eq_mul]
    have e1 : ((g * scalarElement c hc : Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
        (c : K) • (g : Matrix (Fin 3) (Fin 3) K) := by
      rw [Matrix.SpecialLinearGroup.coe_mul, coe_scalarElement, Matrix.scalar_apply,
        ← Matrix.smul_one_eq_diagonal, Matrix.mul_smul, Matrix.mul_one]
    rw [e1, Matrix.smul_mul, h]
  rw [hs, map_mul, proj_eq_one_iff.mpr (scalarElement_mem_scalars c hc), mul_one]

end Elements

section Core

variable {K : Type} [Field K] [Finite K]

theorem false_of_heis_frame {p f : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hf : 1 ≤ f)
    (hK : Nat.card K = p ^ f) (h2K : (2 : K) ≠ 0) {ξ : K} (hξ1 : ξ ≠ 1) (hξ3 : ξ ^ 3 = 1)
    (hdiag : ∀ k : Fin 3, (![1, ξ, ξ ^ 2] : Fin 3 → K) k ≠ 0)
    {V Z : Subgroup (MulAut (projectiveSL 3 K))} (h2 : N2Cfg (projectiveSL 3 K) 3 V Z)
    (h3 : N3Deriv (projectiveSL 3 K) V Z)
    (hΔV : conjAut 3 K (diagGLK ![1, ξ, ξ ^ 2] hdiag) ∈ V)
    (hZD : ∀ z ∈ Z, z ∈ linearAutGroup 3 K → z = 1) : False := by
  classical
  obtain ⟨hr, hr2, -, -, -, hZodd, -, hZbot, -⟩ := id h2
  have hcen : Subgroup.center (projectiveSL 3 K) = ⊥ :=
    CFSG.RankThree.RegularUnipotent.center_projectiveSL_eq_bot (by norm_num)
  have hinj := mulAut_conj_injective_of_center_bot hcen
  have hξ0 : ξ ≠ 0 := by rintro rfl; simp at hξ3
  set Δ : GL (Fin 3) K := diagGLK ![1, ξ, ξ ^ 2] hdiag with hΔdef
  obtain ⟨z, hz1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hZbot
  have hzE : (z : MulAut (projectiveSL 3 K)) ∈ semilinearAutGroup 3 K := by
    refine mem_semilinearAutGroup_of_pow_eq_one (m := Nat.card ↥Z) (le_refl 3) hZodd ?_
    have h' : z ^ Nat.card ↥Z = 1 := pow_card_eq_one'
    simpa only [Subgroup.coe_pow, Subgroup.coe_one] using congrArg Subtype.val h'
  obtain ⟨X, τ, hzXτ⟩ := mem_semilinearAutGroup_iff.mp hzE
  have hτ1 : τ ≠ 1 := by
    rintro rfl
    have hzD : (z : MulAut (projectiveSL 3 K)) ∈ linearAutGroup 3 K := by
      rw [hzXτ, map_one, mul_one]; exact conjAut_mem_linearAutGroup X
    exact hz1 (Subtype.ext (hZD _ z.2 hzD))
  have hv0 : conjAut 3 K Δ ≠ 1 := by
    intro h
    obtain ⟨u, hu⟩ := (CFSG.GH74.GLS.Stage2.OddAut.conjAut_eq_one_iff_of_three_le (le_refl 3) Δ).mp h
    have e0 := congrArg (fun A : GL (Fin 3) K => (A : Matrix (Fin 3) (Fin 3) K) 0 0) hu
    have e1 := congrArg (fun A : GL (Fin 3) K => (A : Matrix (Fin 3) (Fin 3) K) 1 1) hu
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
  have htfix : conjAut 3 K Δ (proj 3 K (torusSL s hs)) = proj 3 K (torusSL s hs) :=
    conjAut_diagGLK_proj_diag ![1, ξ, ξ ^ 2] hdiag (torusSL s hs) ![s ^ 2, s⁻¹, s⁻¹] rfl
  have hPfix : conjAut 3 K Δ (proj 3 K (cycSL : Matrix.SpecialLinearGroup (Fin 3) K)) =
      proj 3 K cycSL := by
    refine conjAut_proj_eq_of_smul (c := Units.mk0 ξ hξ0) ?_ ?_
    · exact Units.ext (by simpa using hξ3)
    · show ((diagGLK ![1, ξ, ξ ^ 2] hdiag : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
        Matrix.of ![![0, 0, 1], ![1, 0, 0], ![0, 1, 0]] =
        ξ • (Matrix.of ![![0, 0, 1], ![1, 0, 0], ![0, 1, 0]] *
          ((diagGLK ![1, ξ, ξ ^ 2] hdiag : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K))
      rw [coe_diagGLK]
      ext i j
      rw [diagonal_mul, Matrix.smul_apply, mul_diagonal]
      fin_cases i <;> fin_cases j <;> simp
      all_goals first | ring1 | linear_combination -hξ3
  have hcconj : ∀ u : projectiveSL 3 K, MulAut.conj u ∈ linearAutGroup 3 K := by
    intro u
    obtain ⟨g', rfl⟩ := proj_surjective 3 K u
    rw [← conjAut_toGL]
    exact conjAut_mem_linearAutGroup _
  set c : projectiveSL 3 K := proj 3 K (commSL s hs) with hcdef
  have hcmem : c ∈ ⁅fixSub (conjAut 3 K Δ), fixSub (conjAut 3 K Δ)⁆ := by
    have : c = ⁅proj 3 K (torusSL s hs), proj 3 K cycSL⁆ := by
      rw [hcdef, ← map_commutatorElement, commutator_torusSL_cycSL]
    rw [this]
    exact Subgroup.commutator_mem_commutator (mem_fixSub.2 htfix) (mem_fixSub.2 hPfix)
  have hnorm := h3 _ hΔV hv0 c hcmem
  have hzc : (z : MulAut (projectiveSL 3 K)) c = c := by
    have hzZ : (z : MulAut (projectiveSL 3 K)) ∈ Z := z.2
    have h1 := (Subgroup.mem_normalizer_iff.mp hnorm _).mp hzZ
    have h4 : MulAut.conj c * (z : MulAut (projectiveSL 3 K)) * (MulAut.conj c)⁻¹ *
        (z : MulAut (projectiveSL 3 K))⁻¹ ∈ Z := Z.mul_mem h1 (Z.inv_mem hzZ)
    have h5 : MulAut.conj c * (z : MulAut (projectiveSL 3 K)) * (MulAut.conj c)⁻¹ *
        (z : MulAut (projectiveSL 3 K))⁻¹ =
        MulAut.conj (c * (z : MulAut (projectiveSL 3 K)) c⁻¹) := by
      have : (z : MulAut (projectiveSL 3 K)) * (MulAut.conj c)⁻¹ * (z : MulAut (projectiveSL 3 K))⁻¹ =
          MulAut.conj ((z : MulAut (projectiveSL 3 K)) c⁻¹) := by
        have := mulAut_conj_conj (z : MulAut (projectiveSL 3 K)) c⁻¹
        simpa [map_inv] using this
      calc MulAut.conj c * (z : MulAut (projectiveSL 3 K)) * (MulAut.conj c)⁻¹ *
            (z : MulAut (projectiveSL 3 K))⁻¹
          = MulAut.conj c * ((z : MulAut (projectiveSL 3 K)) * (MulAut.conj c)⁻¹ *
              (z : MulAut (projectiveSL 3 K))⁻¹) := by group
        _ = MulAut.conj (c * (z : MulAut (projectiveSL 3 K)) c⁻¹) := by rw [this, map_mul]
    rw [h5] at h4
    have h6 := hZD _ h4 (hcconj _)
    have h7 : c * (z : MulAut (projectiveSL 3 K)) c⁻¹ = 1 := hinj (by rw [h6, map_one])
    have h8 : (z : MulAut (projectiveSL 3 K)) c⁻¹ = c⁻¹ := by
      have := congrArg (fun t => c⁻¹ * t) h7
      simpa using this
    have := congrArg (fun t => t⁻¹) h8
    simpa using this
  have hzc' : conjAut 3 K X (fieldAut 3 K τ c) = c := by
    have := hzc
    rw [hzXτ, MulAut.mul_apply] at this
    exact this
  rw [hcdef, fieldAut_proj, conjAut_proj] at hzc'
  obtain ⟨c0, -, hmat⟩ := mem_scalars.mp (proj_eq_proj_iff.mp hzc')
  set A : Matrix.SpecialLinearGroup (Fin 3) K :=
    CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation 3 K X
      (Matrix.SpecialLinearGroup.map τ.toRingHom (commSL s hs)) with hAdef
  have hDA : ((commSL s hs : Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      (c0 : K) • (A : Matrix (Fin 3) (Fin 3) K) := by
    calc ((commSL s hs : Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)
        = ((A * (A⁻¹ * commSL s hs) : Matrix.SpecialLinearGroup (Fin 3) K) :
            Matrix (Fin 3) (Fin 3) K) := by rw [mul_inv_cancel_left]
      _ = (A : Matrix (Fin 3) (Fin 3) K) * Matrix.scalar (Fin 3) (c0 : K) := by
          rw [Matrix.SpecialLinearGroup.coe_mul, hmat]
      _ = (c0 : K) • (A : Matrix (Fin 3) (Fin 3) K) := by
          rw [Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal, Matrix.mul_smul, Matrix.mul_one]
  have hAmat : (A : Matrix (Fin 3) (Fin 3) K) = (X : Matrix (Fin 3) (Fin 3) K) *
      diagonal ![τ s ^ 3, (τ s ^ 3)⁻¹, 1] * ((X⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
    rw [hAdef, CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation_matrix]
    congr 2
    show ((commSL s hs : Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).map τ = _
    show (diagonal ![s ^ 3, (s ^ 3)⁻¹, 1]).map τ = _
    rw [diagonal_map (map_zero τ)]
    congr 1
    funext i
    fin_cases i <;> simp [map_pow, map_inv₀]
  have hc0 : (c0 : K) ≠ 0 := c0.ne_zero
  have hfinal : (X : Matrix (Fin 3) (Fin 3) K) * diagonal ![τ s ^ 3, (τ s ^ 3)⁻¹, 1] *
      ((X⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      ((c0 : K)⁻¹) • diagonal ![s ^ 3, (s ^ 3)⁻¹, 1] := by
    rw [← hAmat]
    have : (A : Matrix (Fin 3) (Fin 3) K) = ((c0 : K)⁻¹) • ((c0 : K) • (A : Matrix (Fin 3) (Fin 3) K)) := by
      rw [inv_smul_smul₀ hc0]
    rw [this, ← hDA]
    rfl
  exact CFSG.GH74.GLS.Stage2.OddAut.generator_contradiction hp hp5 hf hK τ hτ1 hs hgord
    (CFSG.GH74.GLS.Stage2.OddAut.trace_argument h2K τ hs X _ hfinal)

end Core

end CFSG.GH74.GLS.Stage2.Bender.Thm1
