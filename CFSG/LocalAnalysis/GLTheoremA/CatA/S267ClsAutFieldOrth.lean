module

public import CFSG.RankThree.PartOne.S11d.OutOrthogonal
public import CFSG.RankThree.PartOne.KC.OrthogonalFieldDescentDefs
import CFSG.HardMathSupport.Lang.Proving.OrthogonalFieldDescentOdd
import CFSG.HardMathSupport.Timmesfeld.Tables.T1b.OrthOdd
import CFSG.RankThree.PartOne.MB3.OddOutOrthogonal
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267ClsAutField

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S267.ModelGen

open CFSG.Open Matrix QuadraticMap CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.OrthogonalOuter
open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.ComponentClassification.CatalogueBHigherLinearField (glFieldAut)
open CFSG.GroupTheory.SteinbergBK (semilinearFixedSubfield)
open CFSG.RankThree.PartOne.OutStructure (Inn OutPChain OutPNice.toChain OutPChain.of_mulEquiv
  orthD linearConjugationHom_range_eq_orthD)

section Model

variable {K : Type} [Field K] {d : ℕ}

@[expose] noncomputable def statedProjMatrixDerivedEquiv (Q : QuadraticForm K (Fin d → K)) :
    StatedProj (matrixDerived Q) ≃* matrixProjectiveDerived Q :=
  QuotientGroup.quotientMulEquivOfEq rfl

theorem not_dvd_card_orthScalars [Finite K] (Q : QuadraticForm K (Fin d → K))
    (hQ : ∃ v, Q v ≠ 0) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    ¬ p ∣ Nat.card ↥((StatedScalars (Fin d) K).subgroupOf (matrixDerived Q)) := by
  refine not_dvd_card_of_sq_eq_one hp hp2 fun z => ?_
  obtain ⟨⟨z, hzD⟩, hzZ⟩ := z
  obtain ⟨c, hc⟩ := Subgroup.mem_subgroupOf.1 hzZ
  have hc' : Matrix.GeneralLinearGroup.scalar (Fin d) c = z := hc
  subst hc'
  obtain ⟨v, hv⟩ := hQ
  have hiso := (mem_matrixIsometries_iff Q _).1 (matrixDerived_le_isometries Q hzD) v
  rw [matrixLinearEquiv_apply, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
    ← Matrix.smul_one_eq_diagonal, Matrix.smul_mulVec, Matrix.one_mulVec, QuadraticMap.map_smul,
    smul_eq_mul] at hiso
  have hc2 : (c : K) * (c : K) = 1 := by
    have h1 : ((c : K) * (c : K) - 1) * Q v = 0 := by rw [sub_mul, hiso, one_mul, sub_self]
    exact sub_eq_zero.1 ((mul_eq_zero.1 h1).resolve_right hv)
  have hcu : c ^ 2 = 1 := Units.ext (by rw [Units.val_pow_eq_pow_val, pow_two, hc2, Units.val_one])
  apply Subtype.ext
  apply Subtype.ext
  change (Matrix.GeneralLinearGroup.scalar (Fin d) c) ^ 2 = 1
  rw [← map_pow, hcu, map_one]

end Model

section Transport

variable {p : ℕ} {Ω : Type} [Group Ω] [Finite Ω] {S : Subgroup Ω} [S.Normal]
variable {K : Type} [Field K] {d : ℕ}

theorem fieldAct_of_transport {Q Q' : QuadraticForm K (Fin d → K)} {σ : K ≃+* K}
    (hQ'σ : ∀ v, Q' (fun i => σ (v i)) = σ (Q' v)) (U : similarityPairs Q)
    (hUσ : U.val.right = σ) (T : GL (Fin d) K) (ν : Kˣ)
    (hT : ∀ v, Q' ((T : Matrix (Fin d) (Fin d) K) *ᵥ v) = ν * Q v)
    (hTU : T * U.val.left = glFieldAut (Fin d) K U.val.right T) (φ : ↥(matrixDerived Q) →* Ω)
    (hφS : φ.range = S) (hφk : φ.ker = (StatedScalars (Fin d) K).subgroupOf (matrixDerived Q))
    {b : Ω}
    (hγ : transAut ((statedProjMatrixDerivedEquiv Q).symm.trans (coverProjEquiv φ hφS hφk)) b =
      matrixProjectiveConjugationHom Q U)
    (hσo : orderOf σ = p) (hcard : Nat.card K = Nat.card (semilinearFixedSubfield σ) ^ p) :
    FieldAct p φ b T⁻¹ σ ∧ FormRel (polarBilin Q) T⁻¹ σ := by
  subst hUσ
  have hUl : U.val.left = T⁻¹ * glFieldAut (Fin d) K U.val.right T := by
    rw [← hTU, inv_mul_cancel_left]
  refine ⟨⟨hσo, hcard, fun k => ⟨matrixDerivedConjugation Q U k, ?_, ?_⟩⟩, ⟨ν, fun u v => ?_⟩⟩
  · rw [matrixDerivedConjugation_val, semiConj_apply, inv_inv, hUl, map_mul, map_mul, map_inv]
    group
  · have h2 := transAut_spec ((statedProjMatrixDerivedEquiv Q).symm.trans
      (coverProjEquiv φ hφS hφk)) b (matrixProjectiveProjection Q k)
    rw [hγ] at h2
    change ((coverProjEquiv φ hφS hφk (QuotientGroup.mk (matrixDerivedConjugation Q U k)) :
      ↥S) : Ω) = b * ((coverProjEquiv φ hφS hφk (QuotientGroup.mk k) : ↥S) : Ω) * b⁻¹ at h2
    exact h2
  ·
    have key : ∀ w, (ν : K) * Q (semiMap T⁻¹ U.val.right w) = U.val.right ((ν : K) * Q w) := by
      intro w
      have h1 := hT ((((T⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K)) *ᵥ
        fun i => U.val.right (((T : Matrix (Fin d) (Fin d) K) *ᵥ w) i))
      rw [mulVec_mulVec_gl, mul_inv_cancel, Units.val_one, Matrix.one_mulVec, hQ'σ, hT] at h1
      rw [semiMap_apply, inv_inv, ← h1]
    have hadd : ∀ x y, semiMap T⁻¹ U.val.right (x + y) =
        semiMap T⁻¹ U.val.right x + semiMap T⁻¹ U.val.right y := fun x y => map_add _ x y
    rw [polarBilin_apply_apply, polarBilin_apply_apply, polar, polar]
    have e1 := key (u + v)
    have e2 := key u
    have e3 := key v
    rw [hadd] at e1
    calc (ν : K) * (Q (semiMap T⁻¹ U.val.right u + semiMap T⁻¹ U.val.right v) -
          Q (semiMap T⁻¹ U.val.right u) - Q (semiMap T⁻¹ U.val.right v))
        = (ν : K) * Q (semiMap T⁻¹ U.val.right u + semiMap T⁻¹ U.val.right v) -
          (ν : K) * Q (semiMap T⁻¹ U.val.right u) -
          (ν : K) * Q (semiMap T⁻¹ U.val.right v) := by ring
      _ = U.val.right ((ν : K) * Q (u + v)) - U.val.right ((ν : K) * Q u) -
          U.val.right ((ν : K) * Q v) := by rw [e1, e2, e3]
      _ = U.val.right ((ν : K) * (Q (u + v) - Q u - Q v)) := by
          rw [mul_sub, mul_sub, map_sub, map_sub]

theorem exists_clsData_orth_of [Finite K] (hp : p.Prime) (hp2 : p ≠ 2)
    (hcore : GLAPPrimeCore p ↥S = ⊥) (hZ : Subgroup.center ↥S = ⊥)
    (Q : QuadraticForm K (Fin d → K)) (hQ0 : ∃ v, Q v ≠ 0)
    (hab : ∃ m : ℕ, Nat.card (Abelianization (matrixIsometries Q)) = 2 ^ m)
    (hOut : OutPChain p (matrixProjectiveDerived Q))
    (himg : ∀ γ : MulAut (matrixProjectiveDerived Q), γ ^ p = 1 → γ ∈ matrixProjectiveImage Q)
    (hdesc : ∀ γ ∈ matrixProjectiveImage Q, γ ∉ (linearConjugationHom Q).range →
      orderOf γ = p → ∃ (σ : K ≃+* K) (U : similarityPairs Q) (Q' : QuadraticForm K (Fin d → K))
        (T : GL (Fin d) K) (ν : Kˣ), orderOf σ = p ∧
        Nat.card K = Nat.card (semilinearFixedSubfield σ) ^ p ∧
        matrixProjectiveConjugationHom Q U = γ ∧ U.val.right = σ ∧
        (∀ v, Q' (fun i => σ (v i)) = σ (Q' v)) ∧
        (∀ v, Q' ((T : Matrix (Fin d) (Fin d) K) *ᵥ v) = ν * Q v) ∧
        T * U.val.left = glFieldAut (Fin d) K U.val.right T)
    (e : PSimple p S ≃* matrixProjectiveDerived Q) {B : Subgroup Ω} (hB : IsElemAbelian p B) :
    ∃ φ : ↥(matrixDerived Q) →* Ω, φ.range = S ∧
      φ.ker = (StatedScalars (Fin d) K).subgroupOf (matrixDerived Q) ∧
      ¬ p ∣ Nat.card φ.ker ∧
      ∃ θ : ↥(B ⊓ (S ⊔ Subgroup.centralizer (S : Set Ω))) →* ↥(matrixDerived Q),
        (∀ x, (φ (θ x))⁻¹ * (x : Ω) ∈ Subgroup.centralizer (S : Set Ω)) ∧
        IsElemAbelian p θ.range ∧ θ.range ⊓ φ.ker = ⊥ ∧
        (∀ x, θ x = 1 ↔ (x : Ω) ∈ Subgroup.centralizer (S : Set Ω)) ∧
        (B ⊓ (S ⊔ Subgroup.centralizer (S : Set Ω)) = B ∨
          ∃ b ∈ B, b ∉ S ⊔ Subgroup.centralizer (S : Set Ω) ∧
            B = B ⊓ (S ⊔ Subgroup.centralizer (S : Set Ω)) ⊔ Subgroup.zpowers b ∧
            Subgroup.zpowers b ⊓ (S ⊔ Subgroup.centralizer (S : Set Ω)) = ⊥ ∧
            ∃ (A : GL (Fin d) K) (σ : K ≃+* K), FieldAct p φ b A σ ∧
              FormRel (polarBilin Q) A σ ∧
              ∀ x, semiConj A σ ((θ x : ↥(matrixDerived Q)) : GL (Fin d) K) = θ x) := by
  obtain ⟨φ, hφS, hφk⟩ :=
    exists_cover_of_center_eq_bot hcore hZ (e.trans (statedProjMatrixDerivedEquiv Q).symm)
  have hker : φ.ker ≤ Subgroup.center ↥(matrixDerived Q) :=
    hφk ▸ CFSG.Open.StatedAPI.statedScalars_subgroupOf_le_center _
  have hC : ¬ p ∣ Nat.card φ.ker := hφk ▸ not_dvd_card_orthScalars Q hQ0 hp hp2
  obtain ⟨θ, hθ, hθel, hθk, hθ1⟩ := exists_inner_lift hp hB hZ φ hφS hker hC
  set e₃ : matrixProjectiveDerived Q ≃* ↥S :=
    (statedProjMatrixDerivedEquiv Q).symm.trans (coverProjEquiv φ hφS hφk) with he₃
  refine ⟨φ, hφS, hφk, hC, θ, hθ, hθel, hθk, hθ1, ?_⟩
  rcases inner_split' hp hB (hOut.of_mulEquiv e₃.symm) with h | ⟨b, hb, hbN, hBb, hbinf⟩
  · exact Or.inl h
  · right
    set γ := transAut e₃ b with hγ
    have hγo : orderOf γ = p := orderOf_transAut_eq e₃ hp (hB.2 b hb) hbN
    have hγp : γ ^ p = 1 := by rw [← hγo]; exact pow_orderOf_eq_one γ
    have hγD : γ ∉ (linearConjugationHom Q).range := by
      intro hD
      rw [linearConjugationHom_range_eq_orthD] at hD
      have hnd := CFSG.HardMathSupport.Timmesfeld.Tables.T1b.orthD_relIndex_inner_not_dvd' Q hQ0
        hab hp hp2
      exact hbN ((transAut_mem_inner_iff e₃ b).1 (mem_of_pow_mem_of_coprime _ hD
        (by rw [hγp]; exact one_mem _) ((Nat.Prime.coprime_iff_not_dvd hp).2 hnd).symm))
    obtain ⟨σ, U, Q', T, ν, hσo, hcard, hUγ, hUσ, hQ'σ, hT, hTU⟩ :=
      hdesc γ (himg γ hγp) hγD hγo
    obtain ⟨hact, hform⟩ := fieldAct_of_transport hQ'σ U hUσ T ν hT hTU φ hφS hφk hUγ.symm hσo
      hcard
    exact ⟨b, hb, hbN, hBb, hbinf, T⁻¹, σ, hact, hform, semiConj_eq_of_fieldAct hp hZ φ hφS
      hker hC hB inf_le_left θ hθ (fun x => hθel.2 _ ⟨x, rfl⟩) hb hact⟩

theorem orthDesc_of {ℓ f : ℕ} {Q : QuadraticForm K (Fin d → K)}
    {Disp : ∀ U : similarityPairs Q,
      QuadraticForm (CFSG.RankThree.PartOne.KCOrthogonalDescent.fixedField U.val)
        (CFSG.RankThree.PartOne.KCOrthogonalDescent.fixedSpace U.val) → Prop}
    {γ : MulAut (matrixProjectiveDerived Q)} (hγE : γ ∈ matrixProjectiveImage Q)
    (hOFD : CFSG.RankThree.PartOne.KCOrthogonalDescent.OrthogonalFieldDescent ℓ f p Q Disp γ)
    (hK : Nat.card K = ℓ ^ f)
    (hDisp : ∀ (U : similarityPairs Q) Q₀, Disp U Q₀ → ∃ (Q' : QuadraticForm K (Fin d → K))
      (T : GL (Fin d) K) (ν : Kˣ), (∀ v, Q' (fun i => U.val.right (v i)) = U.val.right (Q' v)) ∧
        (∀ v, Q' ((T : Matrix (Fin d) (Fin d) K) *ᵥ v) = ν * Q v) ∧
        T * U.val.left = glFieldAut (Fin d) K U.val.right T) :
    ∃ (σ : K ≃+* K) (U : similarityPairs Q) (Q' : QuadraticForm K (Fin d → K))
      (T : GL (Fin d) K) (ν : Kˣ), orderOf σ = p ∧
      Nat.card K = Nat.card (semilinearFixedSubfield σ) ^ p ∧
      matrixProjectiveConjugationHom Q U = γ ∧ U.val.right = σ ∧
      (∀ v, Q' (fun i => σ (v i)) = σ (Q' v)) ∧
      (∀ v, Q' ((T : Matrix (Fin d) (Fin d) K) *ᵥ v) = ν * Q v) ∧
      T * U.val.left = glFieldAut (Fin d) K U.val.right T := by
  obtain ⟨g, hg⟩ := hγE
  obtain ⟨hpf, hall⟩ := hOFD
  obtain ⟨hσo, hσcard, U, -, Q₀, hUκ, hUr, -, hD⟩ := hall g.val.right ⟨g, hg, rfl⟩
  obtain ⟨Q', T, ν, h1, h2, h3⟩ := hDisp U Q₀ hD
  refine ⟨g.val.right, U, Q', T, ν, hσo, ?_, hUκ, hUr, hUr ▸ h1, h2, h3⟩
  rw [hσcard, hK, ← pow_mul, Nat.div_mul_cancel hpf]

end Transport

section Tags

variable {p : ℕ} {Ω : Type} [Group Ω] [Finite Ω] {S : Subgroup Ω} [S.Normal]

open CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.Spin CFSG.ClassicalGroups.Orthogonal
  CFSG.RankThree.PartOne.KCOrthogonalDescent

theorem exists_clsData_orthOdd (hp : p.Prime) (hp2 : p ≠ 2) (hcore : GLAPPrimeCore p ↥S = ⊥)
    (hZ : Subgroup.center ↥S = ⊥) {n ℓ f : ℕ}
    (hmodel : StatedClassicalModel (PSimple p S) .POmegaOdd n ℓ f) {K : Type} [Field K]
    [Finite K] (hK : Nat.card K = ℓ ^ f)
    (e : PSimple p S ≃* StatedProj (StatedOmega (StatedQuadOdd n K))) {B : Subgroup Ω}
    (hB : IsElemAbelian p B) :
    ∃ φ : ↥(matrixDerived (coordinateQuadOdd n K)) →* Ω, φ.range = S ∧
      φ.ker = (StatedScalars (Fin (2 * n + 1)) K).subgroupOf
        (matrixDerived (coordinateQuadOdd n K)) ∧
      ¬ p ∣ Nat.card φ.ker ∧
      ∃ θ : ↥(B ⊓ (S ⊔ Subgroup.centralizer (S : Set Ω))) →*
          ↥(matrixDerived (coordinateQuadOdd n K)),
        (∀ x, (φ (θ x))⁻¹ * (x : Ω) ∈ Subgroup.centralizer (S : Set Ω)) ∧
        IsElemAbelian p θ.range ∧ θ.range ⊓ φ.ker = ⊥ ∧
        (∀ x, θ x = 1 ↔ (x : Ω) ∈ Subgroup.centralizer (S : Set Ω)) ∧
        (B ⊓ (S ⊔ Subgroup.centralizer (S : Set Ω)) = B ∨
          ∃ b ∈ B, b ∉ S ⊔ Subgroup.centralizer (S : Set Ω) ∧
            B = B ⊓ (S ⊔ Subgroup.centralizer (S : Set Ω)) ⊔ Subgroup.zpowers b ∧
            Subgroup.zpowers b ⊓ (S ⊔ Subgroup.centralizer (S : Set Ω)) = ⊥ ∧
            ∃ (A : GL (Fin (2 * n + 1)) K) (σ : K ≃+* K), FieldAct p φ b A σ ∧
              FormRel (polarBilin (coordinateQuadOdd n K)) A σ ∧
              ∀ x, semiConj A σ ((θ x : ↥(matrixDerived (coordinateQuadOdd n K))) :
                GL (Fin (2 * n + 1)) K) = θ x) := by
  obtain ⟨⟨hℓ, hf, hn, hℓ2⟩, -⟩ := id hmodel
  obtain ⟨hchar, hnd, hT3, -⟩ := coordinate_model_witness_odd hmodel K hK e
  have hQ0 : ∃ v, coordinateQuadOdd n K v ≠ 0 :=
    CFSG.RankThree.PartOne.KCOrthComm.exists_ne_zero_of_nondegenerate hnd hT3
  have hab := orthogonal_model_isometry_abelianization_order_bound _ .POmegaOdd (.inl rfl) n ℓ f
    hmodel K hK (quadOdd n K) (coe_quadOdd n K) e
  have hab' := CFSG.HardMathSupport.Timmesfeld.Tables.T1b.card_abelianization_two_pow_of_bound
    (oddIndexEquiv n) (quadOdd n K) hab
  have htop := CFSG.RankThree.PartOne.KCOrthogonalAut.matrixProjectiveImage_eq_top_odd K n hn
    (by rw [hchar]; exact hℓ2)
  refine exists_clsData_orth_of hp hp2 hcore hZ _ hQ0 hab'
    (CFSG.HardMathSupport.Timmesfeld.Tables.T1b.outPNice_of_image_top_odd _ hQ0 hab' hp hp2
      htop).toChain (fun γ _ => htop ▸ Subgroup.mem_top γ) (fun γ hγE hγD hγo => ?_)
    (coordinateOddWitnessEquiv K e) hB
  refine orthDesc_of hγE
    (CFSG.HardMathSupport.Lang.Proving.orthogonal_prime_semilinear_actual_fixed_form_descent'
      (PSimple p S) .POmegaOdd (.inl rfl) n ℓ f p hmodel hp hp2 K hK e γ hγE hγD hγo) hK ?_
  rintro U Q₀ ⟨-, -, -, -, T, ν, hT, -, hTU, -⟩
  exact ⟨coordinateQuadOdd n K, T, ν, coordinateQuadOdd_field n U.val.right, hT, hTU⟩

theorem exists_clsData_orthPlus (hp : p.Prime) (hp2 : p ≠ 2) (hcore : GLAPPrimeCore p ↥S = ⊥)
    (hZ : Subgroup.center ↥S = ⊥) {n ℓ f : ℕ} (hn : 5 ≤ n)
    (hmodel : StatedClassicalModel (PSimple p S) .POmegaPlus n ℓ f) {K : Type} [Field K]
    [Finite K] (hK : Nat.card K = ℓ ^ f)
    (e : PSimple p S ≃* StatedProj (StatedOmega (StatedQuadPlus n K))) {B : Subgroup Ω}
    (hB : IsElemAbelian p B) :
    ∃ φ : ↥(matrixDerived (coordinateQuadPlus n K)) →* Ω, φ.range = S ∧
      φ.ker = (StatedScalars (Fin (2 * n)) K).subgroupOf (matrixDerived (coordinateQuadPlus n K)) ∧
      ¬ p ∣ Nat.card φ.ker ∧
      ∃ θ : ↥(B ⊓ (S ⊔ Subgroup.centralizer (S : Set Ω))) →*
          ↥(matrixDerived (coordinateQuadPlus n K)),
        (∀ x, (φ (θ x))⁻¹ * (x : Ω) ∈ Subgroup.centralizer (S : Set Ω)) ∧
        IsElemAbelian p θ.range ∧ θ.range ⊓ φ.ker = ⊥ ∧
        (∀ x, θ x = 1 ↔ (x : Ω) ∈ Subgroup.centralizer (S : Set Ω)) ∧
        (B ⊓ (S ⊔ Subgroup.centralizer (S : Set Ω)) = B ∨
          ∃ b ∈ B, b ∉ S ⊔ Subgroup.centralizer (S : Set Ω) ∧
            B = B ⊓ (S ⊔ Subgroup.centralizer (S : Set Ω)) ⊔ Subgroup.zpowers b ∧
            Subgroup.zpowers b ⊓ (S ⊔ Subgroup.centralizer (S : Set Ω)) = ⊥ ∧
            ∃ (A : GL (Fin (2 * n)) K) (σ : K ≃+* K), FieldAct p φ b A σ ∧
              FormRel (polarBilin (coordinateQuadPlus n K)) A σ ∧
              ∀ x, semiConj A σ ((θ x : ↥(matrixDerived (coordinateQuadPlus n K))) :
                GL (Fin (2 * n)) K) = θ x) := by
  obtain ⟨-, hnd, hT3, -⟩ := coordinate_model_witness_plus hmodel K hK e
  have hQ0 : ∃ v, coordinateQuadPlus n K v ≠ 0 :=
    CFSG.RankThree.PartOne.KCOrthComm.exists_ne_zero_of_nondegenerate hnd hT3
  have hab := orthogonal_model_isometry_abelianization_order_bound _ .POmegaPlus
    (.inr (.inl rfl)) n ℓ f hmodel K hK (quadPlus n K) (coe_quadPlus n K) e
  have hab' := CFSG.HardMathSupport.Timmesfeld.Tables.T1b.card_abelianization_two_pow_of_bound
    (plusIndexEquiv n) (quadPlus n K) hab
  have htop := CFSG.RankThree.PartOne.KCOrthogonalAut.matrixProjectiveImage_eq_top_plus K n hn
  refine exists_clsData_orth_of hp hp2 hcore hZ _ hQ0 hab'
    (CFSG.HardMathSupport.Timmesfeld.Tables.T1b.outPNice_of_image_top_odd _ hQ0 hab' hp hp2
      htop).toChain (fun γ _ => htop ▸ Subgroup.mem_top γ) (fun γ hγE hγD hγo => ?_)
    (coordinatePlusWitnessEquiv K e) hB
  refine orthDesc_of hγE
    (CFSG.HardMathSupport.Lang.Proving.orthogonal_prime_semilinear_actual_fixed_form_descent'
      (PSimple p S) .POmegaPlus (.inr (.inl rfl)) n ℓ f p hmodel hp hp2 K hK e γ hγE hγD hγo)
    hK ?_
  rintro U Q₀ ⟨-, -, -, -, T, ν, hT, -, hTU, -⟩
  exact ⟨coordinateQuadPlus n K, T, ν, coordinateQuadPlus_field n U.val.right, hT, hTU⟩

theorem exists_clsData_orthMinus (hp : p.Prime) (hp2 : p ≠ 2) (hcore : GLAPPrimeCore p ↥S = ⊥)
    (hZ : Subgroup.center ↥S = ⊥) {n ℓ f : ℕ} (hn1 : 1 ≤ n)
    (hmodel : StatedClassicalModel (PSimple p S) .POmegaMinus n ℓ f) {K : Type} [Field K]
    [Finite K] (hK : Nat.card K = ℓ ^ f) (b₀ c₀ : K) (hirr : ∀ s : K, s ^ 2 + b₀ * s + c₀ ≠ 0)
    (e : PSimple p S ≃* StatedProj (StatedOmega (StatedQuadMinus n K b₀ c₀))) {B : Subgroup Ω}
    (hB : IsElemAbelian p B) :
    ∃ φ : ↥(matrixDerived (coordinateQuadMinus n K hn1 b₀ c₀)) →* Ω, φ.range = S ∧
      φ.ker = (StatedScalars (Fin (2 * n)) K).subgroupOf
        (matrixDerived (coordinateQuadMinus n K hn1 b₀ c₀)) ∧
      ¬ p ∣ Nat.card φ.ker ∧
      ∃ θ : ↥(B ⊓ (S ⊔ Subgroup.centralizer (S : Set Ω))) →*
          ↥(matrixDerived (coordinateQuadMinus n K hn1 b₀ c₀)),
        (∀ x, (φ (θ x))⁻¹ * (x : Ω) ∈ Subgroup.centralizer (S : Set Ω)) ∧
        IsElemAbelian p θ.range ∧ θ.range ⊓ φ.ker = ⊥ ∧
        (∀ x, θ x = 1 ↔ (x : Ω) ∈ Subgroup.centralizer (S : Set Ω)) ∧
        (B ⊓ (S ⊔ Subgroup.centralizer (S : Set Ω)) = B ∨
          ∃ b ∈ B, b ∉ S ⊔ Subgroup.centralizer (S : Set Ω) ∧
            B = B ⊓ (S ⊔ Subgroup.centralizer (S : Set Ω)) ⊔ Subgroup.zpowers b ∧
            Subgroup.zpowers b ⊓ (S ⊔ Subgroup.centralizer (S : Set Ω)) = ⊥ ∧
            ∃ (A : GL (Fin (2 * n)) K) (σ : K ≃+* K), FieldAct p φ b A σ ∧
              FormRel (polarBilin (coordinateQuadMinus n K hn1 b₀ c₀)) A σ ∧
              ∀ x, semiConj A σ ((θ x : ↥(matrixDerived (coordinateQuadMinus n K hn1 b₀ c₀))) :
                GL (Fin (2 * n)) K) = θ x) := by
  obtain ⟨⟨-, -, hn⟩, -⟩ := id hmodel
  obtain ⟨-, hnd, hT3, -⟩ := coordinate_model_witness_minus hmodel K hK b₀ c₀ hirr e
  have hQ0 : ∃ v, coordinateQuadMinus n K hn1 b₀ c₀ v ≠ 0 :=
    CFSG.RankThree.PartOne.KCOrthComm.exists_ne_zero_of_nondegenerate hnd hT3
  have hab := orthogonal_model_isometry_abelianization_order_bound _ .POmegaMinus
    (.inr (.inr rfl)) n ℓ f hmodel K hK b₀ c₀ hirr (quadMinus n K b₀ c₀)
    (coe_quadMinus n K b₀ c₀) e
  have hab' := CFSG.HardMathSupport.Timmesfeld.Tables.T1b.card_abelianization_two_pow_of_bound
    (minusIndexEquiv n hn1) (quadMinus n K b₀ c₀) hab
  have htop := CFSG.RankThree.PartOne.KCOrthogonalAut.matrixProjectiveImage_eq_top_minus K n hn
    b₀ c₀ hirr
  refine exists_clsData_orth_of hp hp2 hcore hZ _ hQ0 hab'
    (CFSG.HardMathSupport.Timmesfeld.Tables.T1b.outPNice_of_image_top_odd _ hQ0 hab' hp hp2
      htop).toChain (fun γ _ => htop ▸ Subgroup.mem_top γ) (fun γ hγE hγD hγo => ?_)
    (coordinateMinusWitnessEquiv K hn1 b₀ c₀ e) hB
  refine orthDesc_of hγE
    (CFSG.HardMathSupport.Lang.Proving.orthogonal_prime_semilinear_actual_fixed_form_descent'
      (PSimple p S) .POmegaMinus (.inr (.inr rfl)) n ℓ f p hmodel hp hp2 hn1 K hK b₀ c₀ hirr e γ
      hγE hγD hγo) hK ?_
  rintro U Q₀ ⟨b', c', -, -, -, -, -, T, ν, hT, -, hTU, -⟩
  refine ⟨coordinateQuadMinus n K hn1 (b' : K) (c' : K), T, ν, coordinateQuadMinus_field n hn1
    (b' : K) (c' : K) U.val.right (RingHom.mem_eqLocusField.1 b'.2)
    (RingHom.mem_eqLocusField.1 c'.2), hT, hTU⟩

open CFSG.ComponentClassification.CatalogueBOrthogonalPointPlusFamilyOrbit in
open scoped Pointwise in
theorem exists_clsData_orthPlusFour (hp : p.Prime) (hp5 : 5 ≤ p)
    (hcore : GLAPPrimeCore p ↥S = ⊥) (hZ : Subgroup.center ↥S = ⊥) {ℓ f : ℕ}
    (hmodel : StatedClassicalModel (PSimple p S) .POmegaPlus 4 ℓ f) {K : Type} [Field K]
    [Finite K] (hK : Nat.card K = ℓ ^ f)
    (e : PSimple p S ≃* StatedProj (StatedOmega (StatedQuadPlus 4 K))) {B : Subgroup Ω}
    (hB : IsElemAbelian p B) :
    ∃ φ : ↥(matrixDerived (coordinateQuadPlus 4 K)) →* Ω, φ.range = S ∧
      φ.ker = (StatedScalars (Fin (2 * 4)) K).subgroupOf (matrixDerived (coordinateQuadPlus 4 K)) ∧
      ¬ p ∣ Nat.card φ.ker ∧
      ∃ θ : ↥(B ⊓ (S ⊔ Subgroup.centralizer (S : Set Ω))) →*
          ↥(matrixDerived (coordinateQuadPlus 4 K)),
        (∀ x, (φ (θ x))⁻¹ * (x : Ω) ∈ Subgroup.centralizer (S : Set Ω)) ∧
        IsElemAbelian p θ.range ∧ θ.range ⊓ φ.ker = ⊥ ∧
        (∀ x, θ x = 1 ↔ (x : Ω) ∈ Subgroup.centralizer (S : Set Ω)) ∧
        (B ⊓ (S ⊔ Subgroup.centralizer (S : Set Ω)) = B ∨
          ∃ b ∈ B, b ∉ S ⊔ Subgroup.centralizer (S : Set Ω) ∧
            B = B ⊓ (S ⊔ Subgroup.centralizer (S : Set Ω)) ⊔ Subgroup.zpowers b ∧
            Subgroup.zpowers b ⊓ (S ⊔ Subgroup.centralizer (S : Set Ω)) = ⊥ ∧
            ∃ (A : GL (Fin (2 * 4)) K) (σ : K ≃+* K), FieldAct p φ b A σ ∧
              FormRel (polarBilin (coordinateQuadPlus 4 K)) A σ ∧
              ∀ x, semiConj A σ ((θ x : ↥(matrixDerived (coordinateQuadPlus 4 K))) :
                GL (Fin (2 * 4)) K) = θ x) := by
  have hp2 : p ≠ 2 := by omega
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨-, hnd, hT3, -⟩ := coordinate_model_witness_plus hmodel K hK e
  have hQ0 : ∃ v, coordinateQuadPlus 4 K v ≠ 0 :=
    CFSG.RankThree.PartOne.KCOrthComm.exists_ne_zero_of_nondegenerate hnd hT3
  have hab := orthogonal_model_isometry_abelianization_order_bound _ .POmegaPlus
    (.inr (.inl rfl)) 4 ℓ f hmodel K hK (quadPlus 4 K) (coe_quadPlus 4 K) e
  have hab' := CFSG.HardMathSupport.Timmesfeld.Tables.T1b.card_abelianization_two_pow_of_bound
    (plusIndexEquiv 4) (quadPlus 4 K) hab
  have hEA := (orthogonal_geometry_plus_model_stabilizer_preserving_image hmodel K hK e).1
  have horbit := orthogonal_geometry_plus_point_family_orbit hmodel hK e
  have hidx : (matrixProjectiveImage (coordinateQuadPlus 4 K)).index ≤ 3 := by
    have hst : (projectivePointFamilyAut (coordinateQuadPlus 4 K)).index =
        (MulAction.orbit (MulAut (matrixProjectiveDerived (coordinateQuadPlus 4 K)))
          (projectivePointFamily (coordinateQuadPlus 4 K))).ncard :=
      MulAction.index_stabilizer _ _
    rw [← hEA, hst]
    exact (horbit.2.2.2.2.2 rfl).2
  have : Finite (MulAut (matrixProjectiveDerived (coordinateQuadPlus 4 K))) := inferInstance
  have himg : ∀ γ : MulAut (matrixProjectiveDerived (coordinateQuadPlus 4 K)), γ ^ p = 1 →
      γ ∈ matrixProjectiveImage (coordinateQuadPlus 4 K) := fun γ hγ =>
    CFSG.RankThree.PartOne.OutStructure.mem_of_pow_mem_of_index_le_three _ hidx hp
      (by omega : 3 < p) (k := 1) (by rw [pow_one, hγ]; exact one_mem _)
  have hOut := (CFSG.RankThree.PartOne.OutStructure.outPChain_POmegaPlus_four_gen hp hp5
    hmodel).of_mulEquiv (coordinatePlusWitnessEquiv K e).symm
  refine exists_clsData_orth_of hp hp2 hcore hZ _ hQ0 hab' hOut himg
    (fun γ hγE hγD hγo => ?_) (coordinatePlusWitnessEquiv K e) hB
  refine orthDesc_of hγE
    (CFSG.HardMathSupport.Lang.Proving.orthogonal_prime_semilinear_actual_fixed_form_descent'
      (PSimple p S) .POmegaPlus (.inr (.inl rfl)) 4 ℓ f p hmodel hp hp2 K hK e γ hγE hγD hγo)
    hK ?_
  rintro U Q₀ ⟨-, -, -, -, T, ν, hT, -, hTU, -⟩
  exact ⟨coordinateQuadPlus 4 K, T, ν, coordinateQuadPlus_field 4 U.val.right, hT, hTU⟩

end Tags

end CFSG.LocalAnalysis.GLTheoremA.S267.ModelGen

end
