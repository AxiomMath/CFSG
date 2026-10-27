module

public import CFSG.GH74.GLS.Stage1.Main.BrFusedH4
public import CFSG.GH74.GLS.Stage2.Final.ModelPGLUni

public section

namespace CFSG.GH74.GLS.Stage2.Final.ModelBlock

open CFSG.Assembly.LowTwoRank CFSG.GH74.L5U5 Matrix Subgroup CFSG.GH74.GLS
  CFSG.GH74.GLS.Stage1.Thm3.Sec7 CFSG.GorensteinWalter
  CFSG.ComponentClassification.CatalogueBUnitaryTwo
  CFSG.ComponentClassification.CatalogueBUnitaryIsometry CFSG.LieType.Universal.Unitary
  CFSG.LieType.BorelTits CFSG.LieType.Steinberg

theorem exists_norm_one_sq_mul_pow_four_uni {F : Type} [Field F] {n : ℕ} (hn : n % 8 = 3) {δ : Fˣ}
    (hδ : δ ^ (n + 1) = 1) : ∃ c : Fˣ, c ^ (n + 1) = 1 ∧ (c * c * δ) ^ 4 = 1 := by
  obtain ⟨k, hk⟩ : ∃ k, n = 8 * k + 3 := ⟨n / 8, by omega⟩
  refine ⟨(δ ^ (k + 1))⁻¹, ?_, ?_⟩
  · rw [inv_pow, ← pow_mul, mul_comm, pow_mul, hδ, one_pow, inv_one]
  · have h8 : (δ ^ (k + 1)) ^ 8 = δ ^ 4 := by
      rw [← pow_mul, show (k + 1) * 8 = (n + 1) + 4 by omega, pow_add, hδ, one_mul]
    rw [mul_pow, mul_pow, ← pow_add, inv_pow, show 4 + 4 = 8 from rfl, h8]
    exact inv_mul_cancel _

theorem uni_psi4 {F : Type} [Field F] [Finite F] {p f : ℕ} [Fact p.Prime] [CharP F p]
    (hF : Nat.card F = (p ^ f) ^ 2) (hp2 : p ≠ 2) (hq8 : p ^ f % 8 = 3) :
    ∃ (F₀ : Type) (_ : Field F₀) (_ : Finite F₀) (Ψ : ↥(H4 (ModelData.uni hF)) →* PGL2 F₀),
      Nat.card F₀ = p ^ f ∧ Function.Surjective Ψ ∧
        ∀ g : ↥(H4 (ModelData.uni hF)), Ψ g = 1 ↔ ∃ c : Fˣ, (g : GL (Fin 2) F) = sc2 c := by
  have _ := hp2
  set σ' := unitaryFieldConjugation p f hF with hσ'
  have hσeq : σ' = unitaryInvolution F p f :=
    RingEquiv.ext fun x => by rw [hσ', unitaryFieldConjugation_apply, unitaryInvolution_apply]
  obtain ⟨-, -, hcard⟩ := unitaryFieldConjugation_data p f hF
  have hinv : ∀ x, σ' (σ' x) = x := fun x => by
    rw [hσeq]
    exact unitaryInvolution_involutive hF x
  let h := CFSG.LocalAnalysis.ComponentInitial.LinearFlag.stdHermitian (n := 2) σ'.toRingHom
  have hsym : h.IsSymm :=
    CFSG.LocalAnalysis.ComponentInitial.LinearFlag.stdHermitian_isSymm (τ := σ'.toRingHom) hinv
  have hnd : h.Nondegenerate :=
    ⟨CFSG.LocalAnalysis.ComponentInitial.LinearFlag.stdHermitian_separatingLeft _,
      stdH_separatingRight _⟩
  have hdim : Module.finrank F (Fin 2 → F) = 2 := by simp
  obtain ⟨θ, hsurj, hker, -⟩ :=
    CFSG.LieType.odd_unitary_plane_full_projective_linear_quotient p f hF h hsym hnd hdim
  have hb : ∀ i j, h (Pi.basisFun F (Fin 2) i) (Pi.basisFun F (Fin 2) j) =
      if i = j then 1 else 0 := stdH_basis _
  let iso := isometryMatrixEquiv h (Pi.basisFun F (Fin 2)) hb
  have hle : H4 (ModelData.uni hF) ≤ Uid σ' 2 := fun g hg =>
    (mem_Uid_iff σ' 2 g).2 (by rw [hσeq]; exact (mem_uniGL _).1 (mem_H4.1 hg).1)
  have hU0 : ∀ X : GL (Fin 2) F, conjTr σ' (X : Matrix (Fin 2) (Fin 2) F) *
      (X : Matrix (Fin 2) (Fin 2) F) = 1 → X ∈ (ModelData.uni hF).U2 := fun X hX => by
    rw [hσeq] at hX
    exact (mem_uniGL _).2 hX
  have hU : ∀ A : ↥(Uid σ' 2), (A.val : GL (Fin 2) F) ∈ (ModelData.uni hF).U2 := fun A =>
    hU0 A.val ((mem_Uid_iff σ' 2 A.val).1 A.2)
  have hcn : ∀ c : Fˣ, c ^ (p ^ f + 1) = 1 → (c : F) * σ' c = 1 := fun c hc => by
    rw [hσeq, unitaryInvolution_apply, ← pow_succ']
    have := congrArg (fun v : Fˣ => (v : F)) hc
    simpa using this
  let Ψ₀ : ↥(Uid σ' 2) →* PGL2 ↥(CFSG.ComponentClassification.CatalogueBLinearTwoDescent.fixedSubfield F σ') :=
    θ.comp iso.symm.toMonoidHom
  let Ψ : ↥(H4 (ModelData.uni hF)) →*
      PGL2 ↥(CFSG.ComponentClassification.CatalogueBLinearTwoDescent.fixedSubfield F σ') :=
    Ψ₀.comp (Subgroup.inclusion hle)
  have hsymm_apply : ∀ (A : ↥(Uid σ' 2)) (v : Fin 2 → F),
      ((iso.symm A : ↥(CFSG.ComponentClassification.CatalogueBUnitaryIsometry.isometryGroup h)) :
        (Fin 2 → F) ≃ₗ[F] (Fin 2 → F)) v = (A.val : Matrix (Fin 2) (Fin 2) F) *ᵥ v := by
    intro A v
    have h1 := CFSG.ComponentClassification.CatalogueBAlternatingIsometry.basisMatrixEquiv_mulVec
      (Pi.basisFun F (Fin 2)) ((iso.symm A).val) v
    have h2 : CFSG.ComponentClassification.CatalogueBAlternatingIsometry.basisMatrixEquiv
        (Pi.basisFun F (Fin 2)) ((iso.symm A).val) = A.val := by
      have := isometryMatrixEquiv_val h (Pi.basisFun F (Fin 2)) hb (iso.symm A)
      rw [MulEquiv.apply_symm_apply] at this
      exact this.symm
    rw [h2] at h1
    simpa using h1.symm
  have hK : ∀ A : ↥(Uid σ' 2), Ψ₀ A = 1 ↔
      ∃ c : Fˣ, (c : F) * σ' c = 1 ∧ (A.val : GL (Fin 2) F) = sc2 c := by
    intro A
    show θ (iso.symm A) = 1 ↔ _
    rw [hker]
    constructor
    · rintro ⟨c, hc, hv⟩
      refine ⟨c, hc, eq_sc2_of_mulVec _ c fun v => ?_⟩
      rw [← hsymm_apply]
      exact hv v
    · rintro ⟨c, hc, hA⟩
      refine ⟨c, hc, fun v => ?_⟩
      rw [hsymm_apply, hA, sc2_mulVec]
  refine ⟨_, inferInstance, inferInstance, Ψ, hcard, ?_, ?_⟩
  · intro x
    obtain ⟨g', rfl⟩ := hsurj x
    set A : ↥(Uid σ' 2) := iso g' with hAdef
    have hA : (A.val : GL (Fin 2) F) ∈ (ModelData.uni hF).U2 := hU A
    have hnorm := norm_det_uni (σ := unitaryInvolution F p f) hA
    set δ : Fˣ := Matrix.GeneralLinearGroup.det A.val with hδdef
    have hδF : (δ : F) = ((A.val : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).det :=
      Matrix.GeneralLinearGroup.val_det_apply _
    have hδ : δ ^ (p ^ f + 1) = 1 := by
      apply Units.ext
      rw [Units.val_pow_eq_pow_val, pow_succ, Units.val_one, hδF]
      rw [unitaryInvolution_apply] at hnorm
      exact hnorm
    obtain ⟨c, hc, hcδ⟩ := exists_norm_one_sq_mul_pow_four_uni hq8 hδ
    have hcU : sc2 c ∈ (ModelData.uni hF).U2 := (sc2_mem_uni_iff hF c).2 hc
    have hscUid : (sc2 c : GL (Fin 2) F) ∈ Uid σ' 2 :=
      (mem_Uid_iff σ' 2 _).2 (by rw [hσeq]; exact (mem_uniGL _).1 hcU)
    have hdsc : Matrix.GeneralLinearGroup.det (sc2 c : GL (Fin 2) F) = c * c := by
      apply Units.ext
      rw [Matrix.GeneralLinearGroup.val_det_apply, det_sc2, Units.val_mul, sq]
    have hdetg : (Matrix.GeneralLinearGroup.det (sc2 c * A.val : GL (Fin 2) F)) ^ 4 = 1 := by
      rw [map_mul, hdsc, ← hδdef]
      exact hcδ
    refine ⟨⟨sc2 c * A.val, (ModelData.uni hF).U2.mul_mem hcU hA, hdetg⟩, ?_⟩
    have hprod : Subgroup.inclusion hle ⟨sc2 c * A.val, (ModelData.uni hF).U2.mul_mem hcU hA, hdetg⟩ =
        (⟨sc2 c, hscUid⟩ : ↥(Uid σ' 2)) * A := rfl
    show Ψ₀ (Subgroup.inclusion hle _) = θ g'
    rw [hprod, map_mul, (hK ⟨sc2 c, hscUid⟩).2 ⟨c, hcn c hc, rfl⟩, one_mul]
    show θ (iso.symm A) = θ g'
    rw [hAdef, MulEquiv.symm_apply_apply]
  · intro g
    show Ψ₀ (Subgroup.inclusion hle g) = 1 ↔ _
    rw [hK]
    constructor
    · rintro ⟨c, -, hgc⟩
      exact ⟨c, hgc⟩
    · rintro ⟨c, hgc⟩
      have hgc' : (g : GL (Fin 2) F) = sc2 c := hgc
      have hU2 : sc2 c ∈ (ModelData.uni hF).U2 := hgc' ▸ (mem_H4.1 g.2).1
      exact ⟨c, hcn c ((sc2_mem_uni_iff hF c).1 hU2), hgc'⟩

end CFSG.GH74.GLS.Stage2.Final.ModelBlock
