module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitFieldLocalPSLProof
public import CFSG.ClassicalGroups.SpecialLinear.TransvectionConjugacy
public import CFSG.LieType.SteinbergBRTriangularSolvable
public import CFSG.RankThree.PartOne.CTP.ExtA
public import CFSG.ClassicalGroups.SpecialLinear.InvolutionTransvectionClass

public section

namespace CFSG.ComponentClassification.GrSLit.L34Sec5S

open CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.LieType.SteinbergBR
open CFSG.ClassicalGroups.SpecialLinear
open CFSG.RankThree.PartOne.CTP
open CFSG.CGT.Timmesfeld75
open Matrix
open scoped MatrixGroups

theorem stdTransvection_dot (K : Type) [Field K] :
    (Pi.single 1 (1 : K) : Fin 3 → K) ⬝ᵥ
      (Pi.single 0 (1 : K) : Fin 3 → K) = 0 := by
  rw [dotProduct]
  refine Finset.sum_eq_zero ?_
  intro i _
  by_cases hi : i = 1
  · subst hi
    simp
  · rw [Pi.single_eq_of_ne hi]
    simp

def stdTransvection (K : Type) [Field K] : SpecialLinearGroup (Fin 3) K :=
  tvSL (c := Pi.single 0 1) (a := Pi.single 1 1) (stdTransvection_dot K)

theorem centralizer_std_transvection_solvable (K : Type) [Field K] [Finite K] [CharP K 2] :
    Group.IsSolvable ↥(Subgroup.centralizer
      ({stdTransvection K} : Set (SpecialLinearGroup (Fin 3) K))) := by
  let u : SpecialLinearGroup (Fin 3) K := stdTransvection K
  have hstd : (Pi.single 1 (1 : K) : Fin 3 → K) ⬝ᵥ
      (Pi.single 0 (1 : K) : Fin 3 → K) = 0 := stdTransvection_dot K
  have hv : (Pi.single 0 (1 : K) : Fin 3 → K) ≠ 0 := by simp
  have hw : (Pi.single 1 (1 : K) : Fin 3 → K) ≠ 0 := by simp
  have hu : (u : Matrix (Fin 3) (Fin 3) K) =
      1 + Matrix.vecMulVec (Pi.single 0 (1 : K) : Fin 3 → K)
        (Pi.single 1 (1 : K) : Fin 3 → K) := rfl
  let J : Submodule K (Fin 3 → K) :=
    Submodule.span K ({(Pi.single 0 (1 : K) : Fin 3 → K)} : Set (Fin 3 → K))
  let J₂ : Submodule K (Fin 3 → K) := LinearMap.ker (LinearMap.proj (1 : Fin 3))
  have data : ∀ {g : SpecialLinearGroup (Fin 3) K}, g * u = u * g →
      ∃ a : K, a ≠ 0 ∧
        (g : Matrix (Fin 3) (Fin 3) K) *ᵥ (Pi.single 0 (1 : K) : Fin 3 → K) =
          a • (Pi.single 0 (1 : K) : Fin 3 → K) ∧
        ∀ j, (g : Matrix (Fin 3) (Fin 3) K) 1 j =
          a * (Pi.single 1 (1 : K) : Fin 3 → K) j := by
    intro g hg
    have hmat : (g : Matrix (Fin 3) (Fin 3) K) *
        (1 + Matrix.vecMulVec (Pi.single 0 (1 : K) : Fin 3 → K)
          (Pi.single 1 (1 : K) : Fin 3 → K)) =
        (1 + Matrix.vecMulVec (Pi.single 0 (1 : K) : Fin 3 → K)
          (Pi.single 1 (1 : K) : Fin 3 → K)) * (g : Matrix (Fin 3) (Fin 3) K) := by
      have h := congrArg (fun x : SpecialLinearGroup (Fin 3) K =>
        (x : Matrix (Fin 3) (Fin 3) K)) hg
      simpa [SpecialLinearGroup.coe_mul, hu] using h
    obtain ⟨a, ha, hgv, hgw⟩ :=
      (mul_comm_one_add_vecMulVec_iff hstd hv hw (g : GL (Fin 3) K)).mp hmat
    refine ⟨a, ha, ?_, ?_⟩
    · simpa using hgv
    · intro j
      have h := congrFun hgw j
      simpa [Matrix.mulVec_apply_eq_sum, Matrix.transpose_apply, Pi.smul_apply,
        smul_eq_mul, Pi.single_apply] using h
  have hle : Subgroup.centralizer ({u} : Set (SpecialLinearGroup (Fin 3) K)) ≤
      stabilizer J ⊓ stabilizer J₂ := by
    intro g hg
    have hg_comm : g * u = u * g :=
      Subgroup.mem_centralizer_singleton_iff.mp hg
    obtain ⟨a, ha, hgv, hrow⟩ := data hg_comm
    have hline : g ∈ stabilizer J := by
      rw [mem_stabilizer]
      dsimp [J]
      rw [Submodule.map_span, Set.image_singleton, Matrix.mulVecLin_apply, hgv]
      rw [Submodule.span_singleton_smul_eq (x := (Pi.single 0 (1 : K) : Fin 3 → K))
        (isUnit_iff_ne_zero.mpr ha)]
    have hplane_mem : ∀ x ∈ J₂, (g : Matrix (Fin 3) (Fin 3) K) *ᵥ x ∈ J₂ := by
      intro x hx
      have hx1 : x 1 = 0 := by
        simpa [J₂, LinearMap.proj_apply] using hx
      dsimp only [J₂]
      rw [LinearMap.mem_ker]
      have hsum : ((g : Matrix (Fin 3) (Fin 3) K) *ᵥ x) 1 = 0 := by
        rw [Matrix.mulVec_apply_eq_sum]
        calc (∑ j : Fin 3, (g : Matrix (Fin 3) (Fin 3) K) 1 j * x j)
            = ∑ j : Fin 3,
                (a * (Pi.single 1 (1 : K) : Fin 3 → K) j) * x j := by
              refine Finset.sum_congr rfl ?_
              intro j _
              rw [hrow j]
          _ = a * x 1 := by
            rw [Finset.sum_eq_single (1 : Fin 3)]
            · simp
            · intro j _ hj
              simp [Pi.single_eq_of_ne hj]
            · intro h
              exact absurd (Finset.mem_univ (1 : Fin 3)) h
          _ = 0 := by rw [hx1, mul_zero]
      simpa [LinearMap.proj_apply] using hsum
    have hplane_le : J₂.map (Matrix.mulVecLin (g : Matrix (Fin 3) (Fin 3) K)) ≤ J₂ := by
      rw [Submodule.map_le_iff_le_comap]
      intro x hx
      rw [Submodule.mem_comap]
      exact hplane_mem x hx
    let f : (Fin 3 → K) →ₗ[K] (Fin 3 → K) :=
      Matrix.mulVecLin (g : Matrix (Fin 3) (Fin 3) K)
    have hg_unit : IsUnit (g : Matrix (Fin 3) (Fin 3) K) :=
      (Matrix.isUnit_iff_isUnit_det _).mpr (by rw [g.prop]; exact isUnit_one)
    have hinj : Function.Injective f := by
      simpa [f, Matrix.coe_mulVecLin] using Matrix.mulVec_injective_of_isUnit hg_unit
    let e : (Fin 3 → K) ≃ₗ[K] (Fin 3 → K) := LinearEquiv.ofInjectiveEndo f hinj
    have hfin : Module.finrank K (J₂.map f) = Module.finrank K J₂ :=
      LinearEquiv.finrank_map_eq e J₂
    have hplane_le' : J₂.map f ≤ J₂ := by
      simpa [f] using hplane_le
    have hplane : g ∈ stabilizer J₂ := by
      rw [mem_stabilizer]
      have hmap_eq : J₂.map f = J₂ :=
        Submodule.eq_of_le_of_finrank_eq hplane_le' hfin
      simpa [f] using hmap_eq
    exact ⟨hline, hplane⟩
  have hJJ : J ≤ J₂ := by
    dsimp only [J, J₂]
    rw [Submodule.span_le]
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    change (LinearMap.proj (1 : Fin 3)) (Pi.single 0 (1 : K) : Fin 3 → K) = 0
    simp [LinearMap.proj_apply]
  have hJ : Module.finrank K J = 1 := by
    dsimp [J]
    exact finrank_span_singleton (by simp)
  have hJ₂ : Module.finrank K J₂ = 2 := by
    have hφ_ne : (LinearMap.proj (1 : Fin 3) : (Fin 3 → K) →ₗ[K] K) ≠ 0 := by
      intro h
      have h1 : (Pi.single 1 (1 : K) : Fin 3 → K) 1 = 0 := by
        simpa [LinearMap.proj_apply] using
          congrArg (fun f : (Fin 3 → K) →ₗ[K] K => f (Pi.single 1 1)) h
      simpa using h1
    have h := Module.Dual.finrank_ker_add_one_of_ne_zero
      (f := (LinearMap.proj (1 : Fin 3) : (Fin 3 → K) →ₗ[K] K)) hφ_ne
    have h3 : Module.finrank K (Fin 3 → K) = 3 := by
      rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fin]
    dsimp [J₂]
    omega
  have hcard_exists : ∃ n : ℕ+, Nat.card K = 2 ^ (n : ℕ) := by
    letI : Fintype K := Fintype.ofFinite K
    obtain ⟨n, -, hcard⟩ := FiniteField.card (K := K) 2
    exact ⟨n, by rw [Nat.card_eq_fintype_card, hcard]⟩
  obtain ⟨n, hcard⟩ := hcard_exists
  haveI : Group.IsSolvable ↥(stabilizer J ⊓ stabilizer J₂) :=
    isSolvable_stabilizer_inf_stabilizer (K := K) (p := 2) (k := (n : ℕ))
      Nat.prime_two hcard hJJ hJ hJ₂
  exact Group.isSolvable_of_isSolvable_injective
    (f := Subgroup.inclusion hle) (Subgroup.inclusion_injective hle)

theorem centralizer_transvection_solvable (K : Type) [Field K] [Finite K] [CharP K 2]
    {t : SpecialLinearGroup (Fin 3) K} (ht2 : t * t = 1) (ht1 : t ≠ 1) :
    Group.IsSolvable ↥(Subgroup.centralizer
      ({t} : Set (SpecialLinearGroup (Fin 3) K))) := by
  have htmat2 : (t : Matrix (Fin 3) (Fin 3) K) * (t : Matrix (Fin 3) (Fin 3) K) = 1 := by
    have h := congrArg (fun x : SpecialLinearGroup (Fin 3) K =>
      (x : Matrix (Fin 3) (Fin 3) K)) ht2
    simpa [SpecialLinearGroup.coe_mul, SpecialLinearGroup.coe_one] using h
  have htmat1 : (t : Matrix (Fin 3) (Fin 3) K) ≠ 1 := by
    intro h
    exact ht1 (Subtype.ext h)
  obtain ⟨v, w, hvw, hv, hw, htvvw⟩ := exists_vecMulVec_of_involution htmat2 htmat1
  have ht_eq : t = tvSL (c := v) (a := w) hvw := by
    apply Subtype.ext
    rw [coe_tvSL]
    exact htvvw
  obtain ⟨W, hW⟩ := exists_conj_transvSL_eq hvw hv hw
  let u : SpecialLinearGroup (Fin 3) K := stdTransvection K
  have hW' : W * t * W⁻¹ = u := by
    rw [ht_eq]
    simpa [u, stdTransvection]
  let c : SpecialLinearGroup (Fin 3) K ≃* SpecialLinearGroup (Fin 3) K := MulAut.conj W
  have hct : c t = u := by
    change W * t * W⁻¹ = u
    exact hW'
  have hmap : (Subgroup.centralizer ({t} : Set (SpecialLinearGroup (Fin 3) K))).map
        c.toMonoidHom =
      Subgroup.centralizer ({u} : Set (SpecialLinearGroup (Fin 3) K)) := by
    apply le_antisymm
    · have h := Subgroup.map_centralizer_le_centralizer_image
        ({t} : Set (SpecialLinearGroup (Fin 3) K)) c.toMonoidHom
      simpa [c, hct] using h
    · have hle2 : (Subgroup.centralizer ({u} : Set (SpecialLinearGroup (Fin 3) K))).map
          c.symm.toMonoidHom ≤
          Subgroup.centralizer ({t} : Set (SpecialLinearGroup (Fin 3) K)) := by
        have h := Subgroup.map_centralizer_le_centralizer_image
          ({u} : Set (SpecialLinearGroup (Fin 3) K)) c.symm.toMonoidHom
        have hsymm : c.symm u = t := by
          rw [← hct]
          simp
        simpa [hsymm] using h
      intro x hx
      have hx' : c.symm x ∈
          Subgroup.centralizer ({t} : Set (SpecialLinearGroup (Fin 3) K)) :=
        hle2 (Subgroup.mem_map.mpr ⟨x, hx, rfl⟩)
      exact Subgroup.mem_map.mpr ⟨c.symm x, hx', by simp⟩
  have hsol_std : Group.IsSolvable ↥(Subgroup.centralizer
      ({u} : Set (SpecialLinearGroup (Fin 3) K))) := by
    simpa [u] using centralizer_std_transvection_solvable K
  have e : ↥(Subgroup.centralizer ({t} : Set (SpecialLinearGroup (Fin 3) K))) ≃*
      ↥(Subgroup.centralizer ({u} : Set (SpecialLinearGroup (Fin 3) K))) :=
    hmap ▸ Subgroup.equivMapOfInjective
      (Subgroup.centralizer ({t} : Set (SpecialLinearGroup (Fin 3) K)))
      c.toMonoidHom c.injective
  exact Group.isSolvable_of_surjective (f := e.symm.toMonoidHom) e.symm.surjective

theorem centralizer_proj_involution_solvable (K : Type) [Field K] [Finite K] [CharP K 2]
    {b : projectiveSL 3 K} (hb : orderOf b = 2) :
    Group.IsSolvable ↥(Subgroup.centralizer
      ({b} : Set (projectiveSL 3 K))) := by
  let P := projectiveSL 3 K
  obtain ⟨g, hg⟩ := proj_surjective 3 K b
  have hb2 : b ^ 2 = 1 := by simpa [hb] using pow_orderOf_eq_one b
  have hb_ne_one : b ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hb
    omega
  have hproj_g2 : proj 3 K (g ^ 2) = 1 := by
    rw [map_pow, hg, hb2]
  have hg2_mem : g ^ 2 ∈ scalars 3 K := proj_eq_one_iff.mp hproj_g2
  obtain ⟨c, hc3, hg2mat⟩ := mem_scalars.mp hg2_mem
  have hg2_eq : g ^ 2 = scalarElement c hc3 := Subtype.ext hg2mat
  have hg6 : (g ^ 2) ^ 3 = 1 := by
    rw [hg2_eq]
    apply Subtype.ext
    show (((scalarElement c hc3 : SpecialLinearGroup (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K) ^ 3) = 1
    rw [coe_scalarElement, ← map_pow, ← Units.val_pow_eq_pow_val, hc3, Units.val_one,
      map_one]
  let t : SpecialLinearGroup (Fin 3) K := g ^ 3
  have ht2 : t * t = 1 := by
    dsimp [t]
    calc g ^ 3 * g ^ 3 = g ^ (3 + 3) := by rw [← pow_add]
      _ = g ^ (2 * 3) := by norm_num
      _ = (g ^ 2) ^ 3 := by rw [pow_mul]
      _ = 1 := hg6
  have hproj_t : proj 3 K t = b := by
    dsimp [t]
    rw [map_pow, hg]
    calc b ^ 3 = b ^ 2 * b := by rw [pow_succ]
      _ = 1 * b := by rw [hb2]
      _ = b := one_mul b
  have ht_ne_one : t ≠ 1 := by
    intro ht1
    apply hb_ne_one
    rw [← hproj_t, ht1, map_one]
  have hCsol_t : Group.IsSolvable ↥(Subgroup.centralizer
      ({t} : Set (SpecialLinearGroup (Fin 3) K))) :=
    centralizer_transvection_solvable K ht2 ht_ne_one
  have hle : (Subgroup.centralizer ({t} : Set (SpecialLinearGroup (Fin 3) K))).map
        (proj 3 K) ≤
      Subgroup.centralizer ({b} : Set P) := by
    have h := Subgroup.map_centralizer_le_centralizer_image
      ({t} : Set (SpecialLinearGroup (Fin 3) K)) (proj 3 K)
    simpa [P, hproj_t] using h
  have hge : Subgroup.centralizer ({b} : Set P) ≤
      (Subgroup.centralizer ({t} : Set (SpecialLinearGroup (Fin 3) K))).map
        (proj 3 K) := by
    intro x hx
    obtain ⟨h, hh⟩ := proj_surjective 3 K x
    rw [← hh] at hx ⊢
    have hx_comm : proj 3 K h * b = b * proj 3 K h :=
      Subgroup.mem_centralizer_singleton_iff.mp hx
    let A : SpecialLinearGroup (Fin 3) K := h * t * h⁻¹
    have hconj : proj 3 K A = proj 3 K t := by
      dsimp [A]
      rw [map_mul, map_mul, map_inv, hproj_t]
      rw [hx_comm, mul_assoc, mul_inv_cancel, mul_one]
    have hAz : A⁻¹ * t ∈ scalars 3 K := proj_eq_proj_iff.mp hconj
    let z : SpecialLinearGroup (Fin 3) K := (A⁻¹ * t)⁻¹
    have hz_mem : z ∈ scalars 3 K := by
      dsimp [z]
      exact (scalars 3 K).inv_mem hAz
    obtain ⟨c', -, hzmat⟩ := mem_scalars.mp hz_mem
    have hA_eq : A = t * z := by
      have hAz_inv : A⁻¹ * t = z⁻¹ := by
        dsimp [z]
        rw [inv_inv]
      have h1 : A * z⁻¹ = t := by
        calc A * z⁻¹ = A * (A⁻¹ * t) := by rw [hAz_inv]
          _ = t := by group
      calc A = A * z⁻¹ * z := by group
        _ = t * z := by rw [h1]
    have htmat2 : (t : Matrix (Fin 3) (Fin 3) K) * (t : Matrix (Fin 3) (Fin 3) K) = 1 := by
      have h := congrArg (fun x : SpecialLinearGroup (Fin 3) K =>
        (x : Matrix (Fin 3) (Fin 3) K)) ht2
      simpa [SpecialLinearGroup.coe_mul, SpecialLinearGroup.coe_one] using h
    have htmat1 : (t : Matrix (Fin 3) (Fin 3) K) ≠ 1 := by
      intro h
      exact ht_ne_one (Subtype.ext h)
    have htr_t : Matrix.trace (t : Matrix (Fin 3) (Fin 3) K) = 3 := by
      obtain ⟨v, w, hvw, -, -, htvvw⟩ :=
        exists_vecMulVec_of_involution htmat2 htmat1
      rw [htvvw]
      have htrN : Matrix.trace (Matrix.vecMulVec v w) = 0 := by
        have hsum : Matrix.trace (Matrix.vecMulVec v w) =
            ∑ i : Fin 3, v i * w i := by
          simp [Matrix.trace, Matrix.vecMulVec_apply]
        rw [hsum, ← hvw, dotProduct]
        exact Finset.sum_congr rfl fun i _ => mul_comm (v i) (w i)
      rw [Matrix.trace_add, Matrix.trace_one, htrN, add_zero]
      simp
    have h3_ne_zero : (3 : K) ≠ 0 := by
      intro h
      have hdvd : 2 ∣ 3 := (CharP.cast_eq_zero_iff K 2 3).mp h
      omega
    have htrA : Matrix.trace (A : Matrix (Fin 3) (Fin 3) K) =
        Matrix.trace (t : Matrix (Fin 3) (Fin 3) K) := by
      dsimp [A]
      change Matrix.trace ((h : Matrix (Fin 3) (Fin 3) K) *
        (t : Matrix (Fin 3) (Fin 3) K) * (h : Matrix (Fin 3) (Fin 3) K).adjugate) =
        Matrix.trace (t : Matrix (Fin 3) (Fin 3) K)
      rw [Matrix.trace_mul_comm ((h : Matrix (Fin 3) (Fin 3) K) *
        (t : Matrix (Fin 3) (Fin 3) K)) ((h : Matrix (Fin 3) (Fin 3) K).adjugate)]
      rw [← Matrix.mul_assoc]
      have hadj : (h : Matrix (Fin 3) (Fin 3) K).adjugate *
          (h : Matrix (Fin 3) (Fin 3) K) = 1 := by
        rw [Matrix.adjugate_mul, h.prop, one_smul]
      rw [hadj, Matrix.one_mul]
    have htr_tz : Matrix.trace ((t * z : SpecialLinearGroup (Fin 3) K) :
        Matrix (Fin 3) (Fin 3) K) =
        (c' : K) * Matrix.trace (t : Matrix (Fin 3) (Fin 3) K) := by
      change Matrix.trace (((t : SpecialLinearGroup (Fin 3) K) :
        Matrix (Fin 3) (Fin 3) K) * ((z : SpecialLinearGroup (Fin 3) K) :
        Matrix (Fin 3) (Fin 3) K)) =
        (c' : K) * Matrix.trace (t : Matrix (Fin 3) (Fin 3) K)
      rw [hzmat, Matrix.scalar_apply, ← Matrix.smul_eq_mul_diagonal,
        Matrix.trace_smul, smul_eq_mul]
    have htrace_eq : Matrix.trace (t : Matrix (Fin 3) (Fin 3) K) =
        (c' : K) * Matrix.trace (t : Matrix (Fin 3) (Fin 3) K) := by
      calc Matrix.trace (t : Matrix (Fin 3) (Fin 3) K) =
          Matrix.trace (A : Matrix (Fin 3) (Fin 3) K) := htrA.symm
        _ = Matrix.trace ((t * z : SpecialLinearGroup (Fin 3) K) :
              Matrix (Fin 3) (Fin 3) K) := by rw [hA_eq]
        _ = (c' : K) * Matrix.trace (t : Matrix (Fin 3) (Fin 3) K) := htr_tz
    have hc1_val : (c' : K) = 1 := by
      refine mul_right_cancel₀ (b := Matrix.trace (t : Matrix (Fin 3) (Fin 3) K)) ?_ ?_
      · rw [htr_t]
        exact h3_ne_zero
      · rw [one_mul]
        exact htrace_eq.symm
    have hc1 : c' = 1 := Units.ext hc1_val
    have hz_one : z = 1 := by
      apply Subtype.ext
      rw [hzmat, hc1, Units.val_one, map_one]
      rfl
    have hA_eq_t : A = t := by
      rw [hA_eq, hz_one, mul_one]
    have hcomm : h * t = t * h := by
      have h := congrArg (fun x : SpecialLinearGroup (Fin 3) K => x * h) hA_eq_t
      simpa [A, mul_assoc] using h
    exact Subgroup.mem_map.mpr
      ⟨h, Subgroup.mem_centralizer_singleton_iff.mpr hcomm, rfl⟩
  have hC_eq : Subgroup.centralizer ({b} : Set P) =
      (Subgroup.centralizer ({t} : Set (SpecialLinearGroup (Fin 3) K))).map
        (proj 3 K) := le_antisymm hge hle
  have hmap_sol : Group.IsSolvable ↥((Subgroup.centralizer
      ({t} : Set (SpecialLinearGroup (Fin 3) K))).map (proj 3 K)) := by
    haveI : Group.IsSolvable ↥(Subgroup.centralizer
        ({t} : Set (SpecialLinearGroup (Fin 3) K))) := hCsol_t
    let f : ↥(Subgroup.centralizer ({t} : Set (SpecialLinearGroup (Fin 3) K))) →* P :=
      (proj 3 K).comp (Subgroup.subtype _)
    have hf_mem : ∀ x : ↥(Subgroup.centralizer
        ({t} : Set (SpecialLinearGroup (Fin 3) K))),
        f x ∈ (Subgroup.centralizer ({t} : Set (SpecialLinearGroup (Fin 3) K))).map
          (proj 3 K) :=
      fun x => Subgroup.mem_map.mpr ⟨x.1, x.2, rfl⟩
    let F : ↥(Subgroup.centralizer ({t} : Set (SpecialLinearGroup (Fin 3) K))) →*
        ↥((Subgroup.centralizer ({t} : Set (SpecialLinearGroup (Fin 3) K))).map
          (proj 3 K)) :=
      MonoidHom.codRestrict f _ hf_mem
    have hF : Function.Surjective F := by
      intro y
      obtain ⟨x, hx, hxy⟩ := Subgroup.mem_map.mp y.2
      refine ⟨⟨x, hx⟩, ?_⟩
      apply Subtype.ext
      simpa [F, f] using hxy
    exact Group.isSolvable_of_surjective (f := F) hF
  have hCsol_b : Group.IsSolvable ↥(Subgroup.centralizer ({b} : Set P)) := by
    rw [hC_eq]
    exact hmap_sol
  simpa [P] using hCsol_b

theorem involutionCentralizerSolvable : InvolutionCentralizerSolvable := by
  intro K _ _ _ b hb
  let P := projectiveSL 3 K
  let Q := CFSG.Open.StatedProj (CFSG.Open.StatedSL 3 K)
  let e : P ≃* Q := projectiveSLEquivStated 3 K
  let b' : P := e.symm b
  have hb' : orderOf b' = 2 := by
    dsimp [b']
    rw [MulEquiv.orderOf_eq e.symm b, hb]
  have hsol' : Group.IsSolvable ↥(Subgroup.centralizer ({b'} : Set P)) :=
    centralizer_proj_involution_solvable K hb'
  have hmap : (Subgroup.centralizer ({b'} : Set P)).map e.toMonoidHom =
      Subgroup.centralizer ({b} : Set Q) := by
    apply le_antisymm
    · have h := Subgroup.map_centralizer_le_centralizer_image
        ({b'} : Set P) e.toMonoidHom
      have heb : e b' = b := by simp [b']
      simpa [heb] using h
    · have hle2 : (Subgroup.centralizer ({b} : Set Q)).map e.symm.toMonoidHom ≤
          Subgroup.centralizer ({b'} : Set P) := by
        have h := Subgroup.map_centralizer_le_centralizer_image
          ({b} : Set Q) e.symm.toMonoidHom
        have hes : e.symm b = b' := rfl
        simpa [hes] using h
      intro x hx
      have hx' : e.symm x ∈ Subgroup.centralizer ({b'} : Set P) :=
        hle2 (Subgroup.mem_map.mpr ⟨x, hx, rfl⟩)
      exact Subgroup.mem_map.mpr ⟨e.symm x, hx', by simp⟩
  have eC : ↥(Subgroup.centralizer ({b'} : Set P)) ≃*
      ↥(Subgroup.centralizer ({b} : Set Q)) :=
    hmap ▸ Subgroup.equivMapOfInjective
      (Subgroup.centralizer ({b'} : Set P)) e.toMonoidHom e.injective
  exact Group.isSolvable_of_surjective (f := eC.toMonoidHom) eC.surjective

end CFSG.ComponentClassification.GrSLit.L34Sec5S
