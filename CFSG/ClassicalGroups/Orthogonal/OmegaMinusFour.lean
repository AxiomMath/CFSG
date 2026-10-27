module

public import CFSG.ClassicalGroups.Orthogonal.SL2Embedding
public import CFSG.ClassicalGroups.Orthogonal.RingEquivTransport
public import CFSG.RankThree.PartOne.KC.OrthogonalEvenMinusFourExtract
public import CFSG.ClassicalGroups.Orthogonal.RootGroupCard
public import CFSG.ClassicalGroups.Orthogonal.RootGroupChar
public import CFSG.ClassicalGroups.Orthogonal.RootGroupNormalizer

public section

namespace CFSG.ClassicalGroups.Orthogonal

open CFSG.ClassicalGroups.F2Fixed CFSG.LocalAnalysis.ComponentInitial QuadraticMap
open scoped MatrixGroups

section Swap

variable (E : Type*) [Field E] [CharP E 2]

@[expose] def sl2Antidiag : SL(2, E) :=
  ⟨!![0, 1; 1, 0], by
    rw [Matrix.det_fin_two_of]
    simp [CharTwo.neg_eq]⟩

variable {E}

theorem coe_sl2Antidiag : (sl2Antidiag E : Matrix (Fin 2) (Fin 2) E) = !![0, 1; 1, 0] := rfl

theorem sl2Antidiag_mul_self : sl2Antidiag E * sl2Antidiag E = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [coe_sl2Antidiag, Matrix.mul_apply, Fin.sum_univ_two]

theorem sl2Lower_eq_antidiag_mul (t : E) :
    sl2Lower E t = sl2Antidiag E * sl2Upper E t * sl2Antidiag E := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [coe_sl2Antidiag, Matrix.mul_apply, Fin.sum_univ_two]

end Swap

section Hermitian

open CFSG.RankThree.PartOne.KCOrthogonal Matrix

variable {K E : Type} [Field K] [Finite K] [CharP K 2] [Field E] [Algebra K E]
  (D : EvenNormPlane K E)

theorem coe_hermFourRho_sl2Upper (s : E) (X : hermFourSpace D.σ) :
    ((hermFourRho D (sl2Upper E s) X : hermFourSpace D.σ) : Matrix (Fin 2) (Fin 2) E) =
      !![(X : Matrix (Fin 2) (Fin 2) E) 0 0 + s * (X : Matrix (Fin 2) (Fin 2) E) 1 0 +
          D.σ s * (X : Matrix (Fin 2) (Fin 2) E) 0 1 +
          s * D.σ s * (X : Matrix (Fin 2) (Fin 2) E) 1 1,
        (X : Matrix (Fin 2) (Fin 2) E) 0 1 + s * (X : Matrix (Fin 2) (Fin 2) E) 1 1;
        (X : Matrix (Fin 2) (Fin 2) E) 1 0 + D.σ s * (X : Matrix (Fin 2) (Fin 2) E) 1 1,
        (X : Matrix (Fin 2) (Fin 2) E) 1 1] := by
  rw [coe_hermFourRho]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.map_apply, Matrix.transpose_apply,
      Matrix.vecMul, dotProduct] <;> ring

@[expose] noncomputable def hermFourE11 : hermFourSpace D.σ :=
  ⟨hermFourMat D.σ 1 0 0, hermFourMat_mem D 1 0 0⟩

theorem coe_hermFourE11 : (hermFourE11 D : Matrix (Fin 2) (Fin 2) E) = !![1, 0; 0, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hermFourE11, hermFourMat]

theorem hermFourRho_sl2Upper_hermFourE11 (s : E) :
    hermFourRho D (sl2Upper E s) (hermFourE11 D) = hermFourE11 D := by
  apply Subtype.ext
  rw [coe_hermFourRho_sl2Upper, coe_hermFourE11]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem hermFourRho_sl2Upper_sub (s : E) (X : hermFourSpace D.σ)
    (hX : (X : Matrix (Fin 2) (Fin 2) E) 1 1 = 0) :
    ∃ c : K, hermFourRho D (sl2Upper E s) X - X = c • hermFourE11 D := by
  have hX10 : D.σ ((X : Matrix (Fin 2) (Fin 2) E) 1 0) = (X : Matrix (Fin 2) (Fin 2) E) 0 1 :=
    mem_hermFourSpace.mp X.2 0 1
  have hX01 : D.σ ((X : Matrix (Fin 2) (Fin 2) E) 0 1) = (X : Matrix (Fin 2) (Fin 2) E) 1 0 :=
    mem_hermFourSpace.mp X.2 1 0
  have hσt : D.σ (s * (X : Matrix (Fin 2) (Fin 2) E) 1 0 +
      D.σ s * (X : Matrix (Fin 2) (Fin 2) E) 0 1) =
      s * (X : Matrix (Fin 2) (Fin 2) E) 1 0 + D.σ s * (X : Matrix (Fin 2) (Fin 2) E) 0 1 := by
    rw [map_add, map_mul, map_mul, hX10, D.sigma_sigma, hX01, add_comm]
  obtain ⟨c, hc⟩ := (D.sigma_eq_self_iff _).mp hσt
  refine ⟨c, ?_⟩
  apply Subtype.ext
  rw [Submodule.coe_sub, Submodule.coe_smul, coe_hermFourRho_sl2Upper, coe_hermFourE11]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Algebra.smul_def, hX, hc] <;> ring

variable {W : Type*} [AddCommGroup W] [Module K W] {Q : QuadraticForm K W}

theorem algebraMap_form_hermFour (ψ : W ≃ₗ[K] hermFourSpace D.σ)
    (hψ : ∀ w, hermFourForm D (ψ w) = Q w) (w : W) :
    algebraMap K E (Q w) = ((ψ w : hermFourSpace D.σ) : Matrix (Fin 2) (Fin 2) E).det := by
  rw [← hψ w, algebraMap_hermFourForm]

theorem algebraMap_polar_hermFour (ψ : W ≃ₗ[K] hermFourSpace D.σ)
    (hψ : ∀ w, hermFourForm D (ψ w) = Q w) (x y : W) :
    algebraMap K E (polar Q x y) =
      (ψ x : Matrix (Fin 2) (Fin 2) E) 0 0 * (ψ y : Matrix (Fin 2) (Fin 2) E) 1 1 +
        (ψ y : Matrix (Fin 2) (Fin 2) E) 0 0 * (ψ x : Matrix (Fin 2) (Fin 2) E) 1 1 -
        (ψ x : Matrix (Fin 2) (Fin 2) E) 0 1 * (ψ y : Matrix (Fin 2) (Fin 2) E) 1 0 -
        (ψ y : Matrix (Fin 2) (Fin 2) E) 0 1 * (ψ x : Matrix (Fin 2) (Fin 2) E) 1 0 := by
  rw [QuadraticMap.polar, map_sub, map_sub, algebraMap_form_hermFour D ψ hψ,
    algebraMap_form_hermFour D ψ hψ, algebraMap_form_hermFour D ψ hψ, map_add]
  simp only [Submodule.coe_add, Matrix.det_fin_two, Matrix.add_apply]
  ring

theorem exists_hypPair_sl2_rootGroups (hQ : (polarBilin Q).Nondegenerate)
    (ψ : W ≃ₗ[K] hermFourSpace D.σ) (hψ : ∀ w, hermFourForm D (ψ w) = Q w)
    (ρ : SL(2, E) →* (W ≃ₗ[K] W)) (hρ : ∀ g w, ψ (ρ g w) = hermFourRho D g (ψ w))
    (hρO : ∀ g, ρ g ∈ TauCeti.QuadraticMap.orthogonalGroup Q) :
    ∃ P : HypPair Q, (∀ s, ρ (sl2Upper E s) ∈ rootGroup Q P.e) ∧
      (∀ t, ρ (sl2Lower E t) ∈ rootGroup Q P.f) := by
  have : CharP E 2 := charP_two_of_algebra (K := K)
  set e : W := ψ.symm (hermFourE11 D) with he
  have hψe : ψ e = hermFourE11 D := ψ.apply_symm_apply _
  have hQe : Q e = 0 := by
    apply (algebraMap K E).injective
    rw [algebraMap_form_hermFour D ψ hψ, hψe, coe_hermFourE11, map_zero]
    simp [Matrix.det_fin_two_of]
  set f : W := ρ (sl2Antidiag E) e with hf
  have hQf : Q f = 0 := by rw [hf, map_of_mem (hρO _), hQe]
  have hψf : ((ψ f : hermFourSpace D.σ) : Matrix (Fin 2) (Fin 2) E) = !![0, 0; 0, 1] := by
    rw [hf, hρ, coe_hermFourRho, hψe, coe_hermFourE11, coe_sl2Antidiag]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.map_apply, Matrix.transpose_apply,
        Matrix.vecMul, dotProduct]
  have hpolef : polar Q e f = 1 := by
    apply (algebraMap K E).injective
    rw [algebraMap_polar_hermFour D ψ hψ, hψe, hψf, coe_hermFourE11, map_one]
    simp
  have he0 : e ≠ 0 := by
    intro h
    rw [h, polar_zero_left] at hpolef
    exact zero_ne_one hpolef
  have hupper : ∀ s, ρ (sl2Upper E s) ∈ rootGroup Q e := by
    intro s
    refine (mem_rootGroup_iff hQ hQe he0).mpr ⟨hρO _, ?_, ?_⟩
    · apply ψ.injective
      rw [hρ, hψe, hermFourRho_sl2Upper_hermFourE11]
    · intro x hx
      have h1 : ((ψ x : hermFourSpace D.σ) : Matrix (Fin 2) (Fin 2) E) 1 1 = 0 := by
        have := algebraMap_polar_hermFour D ψ hψ x e
        rw [hx, map_zero, hψe, coe_hermFourE11] at this
        simpa using this.symm
      obtain ⟨c, hc⟩ := hermFourRho_sl2Upper_sub D s (ψ x) h1
      refine ⟨c, ψ.injective ?_⟩
      rw [map_sub, hρ, map_smul, hψe, hc]
  have hlower : ∀ t, ρ (sl2Lower E t) ∈ rootGroup Q f := by
    intro t
    have hinv : (sl2Antidiag E)⁻¹ = sl2Antidiag E :=
      inv_eq_of_mul_eq_one_right sl2Antidiag_mul_self
    have h := conj_mem_rootGroup (hρO (sl2Antidiag E)) (hupper t)
    rwa [← map_inv, ← map_mul, ← map_mul, hinv, ← sl2Lower_eq_antidiag_mul] at h
  exact ⟨⟨e, f, hQe, hQf, hpolef⟩, hupper, hlower⟩

end Hermitian

section Main

open CFSG.RankThree.PartOne.KCOrthogonal

theorem card_eq_pow_of_sl2_model {K V : Type*} [Field K] [Finite K] [CharP K 2]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    {Q : QuadraticForm K V} (hQ : (polarBilin Q).Nondegenerate) (hdim : Module.finrank K V = 4)
    {E : Type*} [Field E] [Finite E] [CharP E 2] (hE : Nat.card E = Nat.card K ^ 2)
    (ρ : SL(2, E) →* (V ≃ₗ[K] V)) (hinj : Function.Injective ρ)
    (hρO : ∀ g, ρ g ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (P₀ : HypPair Q)
    (hPU : ∀ s, ρ (sl2Upper E s) ∈ rootGroup Q P₀.e)
    (hPL : ∀ t, ρ (sl2Lower E t) ∈ rootGroup Q P₀.f)
    {M : Type*} [AddCommGroup M] [Finite M] (h2 : ∀ m : M, m + m = 0)
    [DistribMulAction (Gom Q) M] {u u' : V} (hu : Q u = 0) (hu' : Q u' = 0)
    (huu' : polar Q u u' ≠ 0)
    (hdec : IsCompl (fixedSub M (Lom Q u : Set (Gom Q))) (fixedSub M (Lom Q u' : Set (Gom Q)))) :
    ∃ n : ℕ, Nat.card M = Nat.card K ^ (4 * n) := by
  have hρE : ∀ g, ρ g ∈ elementaryGroup Q := by
    intro g
    have hg : g ∈ Subgroup.closure (Set.range (sl2Upper E) ∪ Set.range (sl2Lower E)) := by
      rw [sl2_closure_upper_lower]
      trivial
    refine (Subgroup.closure_le ((elementaryGroup Q).comap ρ)).mpr ?_ hg
    rintro _ (⟨s, rfl⟩ | ⟨t, rfl⟩)
    · exact rootGroup_le_elementaryGroup Q _ (hPU s)
    · exact rootGroup_le_elementaryGroup Q _ (hPL t)
  have hu0 : u ≠ 0 := by
    rintro rfl
    exact huu' (polar_zero_left Q u')
  have hu'0 : u' ≠ 0 := by
    rintro rfl
    exact huu' (polar_zero_right Q u)
  have hc0 : (polar Q u u')⁻¹ ≠ 0 := inv_ne_zero huu'
  have hQ' : Q ((polar Q u u')⁻¹ • u') = 0 := by rw [map_smul_eq_sq, hu', mul_zero]
  have hpol : polar Q u ((polar Q u u')⁻¹ • u') = 1 := by
    rw [polar_smul_right_eq, inv_mul_cancel₀ huu']
  obtain ⟨h, hh, hhe, hhf⟩ := CFSG.Timmesfeld.ClassicalOrders.exists_mem_orthogonalGroup_apply_pair
    hQ CharTwo.two_eq_zero P₀ (⟨u, (polar Q u u')⁻¹ • u', hu, hQ', hpol⟩ : HypPair Q)
  let φ : SL(2, E) →* (V ≃ₗ[K] V) := (MulAut.conj h).toMonoidHom.comp ρ
  have hφ : ∀ g, φ g = h * ρ g * h⁻¹ := fun g => rfl
  have hφinj : Function.Injective φ := fun a b hab => hinj ((MulAut.conj h).injective hab)
  have hφE : ∀ g, φ g ∈ elementaryGroup Q := fun g => by
    rw [hφ]
    exact conj_mem_elementaryGroup hh (hρE g)
  have hU : ∀ s, φ (sl2Upper E s) ∈ rootGroup Q u := by
    intro s
    rw [hφ]
    have := conj_mem_rootGroup hh (hPU s)
    rwa [hhe] at this
  have hL : ∀ t, φ (sl2Lower E t) ∈ rootGroup Q u' := by
    intro t
    rw [hφ]
    have := conj_mem_rootGroup hh (hPL t)
    rw [hhf, rootGroup_smul hc0] at this
    exact this
  have hcU : Nat.card (rootGroup Q u) = Nat.card E := by
    rw [card_rootGroup hQ hu hu0, hdim, hE]
  have hcL : Nat.card (rootGroup Q u') = Nat.card E := by
    rw [card_rootGroup hQ hu' hu'0, hdim, hE]
  obtain ⟨n, hn⟩ := card_eq_pow_of_sl2_embedding φ hφinj hφE hU hL hcU hcL h2 hdec
  exact ⟨n, by rw [hn, hE, ← pow_mul]; ring_nf⟩

theorem omegaMinus4_card_eq_pow {K V : Type*} [Field K] [Finite K] [CharP K 2]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (Q : QuadraticForm K V) (hQ : (polarBilin Q).Nondegenerate) (hdim : Module.finrank K V = 4)
    (hts : ∀ U : Submodule K V, Module.finrank K U = 2 → ∃ u ∈ U, Q u ≠ 0)
    {M : Type*} [AddCommGroup M] [Finite M] (h2 : ∀ m : M, m + m = 0)
    [DistribMulAction (Gom Q) M] {u u' : V} (hu : Q u = 0) (hu' : Q u' = 0)
    (huu' : polar Q u u' ≠ 0)
    (hdec : IsCompl (fixedSub M (Lom Q u : Set (Gom Q))) (fixedSub M (Lom Q u' : Set (Gom Q)))) :
    ∃ n : ℕ, Nat.card M = Nat.card K ^ (4 * n) := by
  obtain ⟨K₀, _, ⟨e⟩⟩ := exists_field_equiv_type K
  letI : Module K₀ V := Module.compHom V (e : K₀ →+* K)
  have hsmul : ∀ (c : K₀) (v : V), c • v = e c • v := fun _ _ => rfl
  haveI : Finite K₀ := Finite.of_equiv K e.symm.toEquiv
  haveI : CharP K₀ 2 := charP_of_injective_ringHom (f := (e.symm : K →+* K₀)) e.symm.injective 2
  haveI : Finite V := Module.finite_of_finite K
  haveI : FiniteDimensional K₀ V := Module.Finite.of_finite
  have hcard : Nat.card K₀ = Nat.card K := Nat.card_congr e.toEquiv
  have hK₀ : 2 ≤ Nat.card K₀ := Finite.one_lt_card
  have hQ₀ : (polarBilin (formOfRingEquiv e hsmul Q)).Nondegenerate :=
    nondegenerate_formOfRingEquiv hQ
  have hdim₀ : Module.finrank K₀ V = 4 := by
    have h1 : Nat.card V = Nat.card K ^ Module.finrank K V := Module.natCard_eq_pow_finrank
    have h2 : Nat.card V = Nat.card K₀ ^ Module.finrank K₀ V := Module.natCard_eq_pow_finrank
    rw [hdim, ← hcard] at h1
    exact Nat.pow_right_injective hK₀ (h2.symm.trans h1)
  have hts₀ : ∀ U : Submodule K₀ V, Module.finrank K₀ U = 2 →
      ∃ u ∈ U, formOfRingEquiv e hsmul Q u ≠ 0 := by
    intro U hU
    let U' : Submodule K V :=
      { carrier := U
        add_mem' := U.add_mem
        zero_mem' := U.zero_mem
        smul_mem' := fun c v hv => by
          have := U.smul_mem (e.symm c) hv
          rwa [hsmul, RingEquiv.apply_symm_apply] at this }
    have hU' : Module.finrank K U' = 2 := by
      have h1 : Nat.card U' = Nat.card K ^ Module.finrank K U' := Module.natCard_eq_pow_finrank
      have h2 : Nat.card U = Nat.card K₀ ^ Module.finrank K₀ U := Module.natCard_eq_pow_finrank
      have h3 : Nat.card U' = Nat.card U :=
        Nat.card_congr (Equiv.subtypeEquivRight fun x => Iff.rfl)
      rw [hU, hcard] at h2
      rw [h3, h2, ← hcard] at h1
      exact (Nat.pow_right_injective hK₀ h1).symm
    obtain ⟨u, hu, hQu⟩ := hts U' hU'
    exact ⟨u, hu, by rwa [formOfRingEquiv_apply, Ne, map_eq_zero_iff _ e.symm.injective]⟩
  obtain ⟨E, _, _, D, ψ, ρ₀, hψ, hρ, hinj, hρO, -⟩ :=
    CFSG.RankThree.PartOne.even_minus_four_actual_derived_extraction (formOfRingEquiv e hsmul Q)
      hQ₀ hdim₀ hts₀
  haveI : Finite E := D.finite_E
  haveI : CharP E 2 := charP_two_of_algebra (K := K₀)
  obtain ⟨P₀', hPU, hPL⟩ := exists_hypPair_sl2_rootGroups D hQ₀ ψ hψ ρ₀ hρ hρO
  have hP₀e : Q P₀'.e = 0 := by
    have := P₀'.Q_e
    rwa [formOfRingEquiv_apply, map_eq_zero_iff _ e.symm.injective] at this
  have hP₀f : Q P₀'.f = 0 := by
    have := P₀'.Q_f
    rwa [formOfRingEquiv_apply, map_eq_zero_iff _ e.symm.injective] at this
  have hP₀ef : polar Q P₀'.e P₀'.f = 1 := by
    have := P₀'.polar_ef
    rw [polar_formOfRingEquiv] at this
    exact e.symm.injective (this.trans (map_one e.symm).symm)
  exact card_eq_pow_of_sl2_model hQ hdim (E := E) (by rw [D.card_E, hcard])
    ((restrictScalarsHom e hsmul).comp ρ₀)
    ((restrictScalarsHom_injective (e := e) (hsmul := hsmul)).comp hinj)
    (fun g => mem_orthogonalGroup_restrictScalarsHom (hρO g)) ⟨P₀'.e, P₀'.f, hP₀e, hP₀f, hP₀ef⟩
    (fun s => mem_rootGroup_restrictScalarsHom (hPU s))
    (fun t => mem_rootGroup_restrictScalarsHom (hPL t))
    h2 hu hu' huu' hdec

end Main

end CFSG.ClassicalGroups.Orthogonal
