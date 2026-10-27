module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotThreeOmegaUniqueCore
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14BlParamMain

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup QuadraticMap Module CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.ClassicalGroups.Orthogonal Module
open scoped Matrix
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.RankThree.OrthogonalInvolutions (commSpace two_mul_finrank_commSpace_le)
open CFSG.RankThree.PartOne.AUTSL (reflMat reflMat_mem_isometries reflMat_mul_self comm_reflMat_iff
  mul_reflMat_mem_iff finrank_commSpace_reflMat reflMat_congr mem_matrixDerived_iff_even)

section StepOne

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] [Finite K]
  [CharP K 2]

theorem not_mem_range_conj_of_mod_four (hset : SeitzSetting G L) {n f : ℕ} (hn : 3 ≤ n)
    (hn4 : (n + 1) % 4 ≠ 2) (hKc : Nat.card K = 2 ^ f) (hf : 2 ≤ f) (e : L ≃* StatedSp n K)
    {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t) {κ : Sp2mKind}
    (hκ : κ = .omegaPlus ∨ κ = .omegaMinus) (hglob : SpOmegaRowGlobal e t f κ) {g : G}
    (hg : g⁻¹ * t * g ∈ normalizer (spGlobal e : Set G)) :
    (spGlobal e).normalizerMonoidHom ⟨g⁻¹ * t * g, hg⟩ ∉
      (MulAut.conj : spGlobal e →* MulAut (spGlobal e)).range := by
  intro hin
  have hwG := conj_mem_spGlobal_of_mem_range hn hKc hf e ht hKt hκ hglob hg hin
  obtain ⟨τ, hτ, hτm⟩ : ∃ τ : StatedLieTag, (τ = .POmegaPlus ∨ τ = .POmegaMinus) ∧
      CFSG.Blueprint.LieModel (spGlobal e) τ (n + 1) 2 f := by
    have hty := hglob.1
    rcases hκ with rfl | rfl
    · simp only [Sp2mKindType] at hty
      exact ⟨_, Or.inl rfl, hty⟩
    · simp only [Sp2mKindType] at hty
      exact ⟨_, Or.inr rfl, hty⟩
  obtain ⟨F, _, _, _, V, _, _, _, Q, -, hF4, hnd, hdim, ⟨φ⟩⟩ :=
    exists_mulEquiv_omega_of_lieModel hτ hf hτm
  set s := φ ⟨_, hwG⟩ with hs
  have htt : t * t = 1 := by rw [← _root_.sq, ← ht, pow_orderOf_eq_one]
  have hss : s * s = 1 := by
    rw [hs, ← map_mul, ← map_one φ]
    congr 1
    apply Subtype.ext
    show (g⁻¹ * t * g) * (g⁻¹ * t * g) = 1
    calc (g⁻¹ * t * g) * (g⁻¹ * t * g) = g⁻¹ * (t * t) * g := by group
      _ = 1 := by rw [htt]; group
  refine false_of_mem_omegaO2Cent hset hn e ht hKt φ hwG
    (mem_omegaO2Cent_of_mem_omega_of_not_aTwo hF4 hnd (by omega) s.2
      (congrArg Subtype.val hss) ?_)
  rintro ⟨h1, -, h3⟩
  apply hn4
  rw [hdim] at h1
  have h4 : finrank F (omegaInvSpace (s : V ≃ₗ[F] V)) = n + 1 := by omega
  rw [h4] at h3
  exact h3

theorem false_of_linear_of_even (hset : SeitzSetting G L) {n f : ℕ} (hn : 3 ≤ n)
    (hn4 : (n + 1) % 4 ≠ 2) (hKc : Nat.card K = 2 ^ f) (hf : 2 ≤ f) (e : L ≃* StatedSp n K)
    {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t) {κ : Sp2mKind}
    (hκ : κ = .omegaPlus ∨ κ = .omegaMinus) (hglob : SpOmegaRowGlobal e t f κ) {g : G}
    (hg : g⁻¹ * t * g ∈ normalizer (spGlobal e : Set G))
    {K' : Type} [Field K'] [Finite K'] [CharP K' 2] {d : ℕ} {Q : QuadraticForm K' (Fin d → K')}
    (hQ : Q.polarBilin.Nondegenerate)
    (hT : ∃ T : Submodule K' (Fin d → K'), Module.finrank K' T = 3 ∧ ∀ x ∈ T, Q x = 0)
    (ε : spGlobal e ≃* matrixProjectiveDerived Q) (β : MulAut (matrixProjectiveDerived Q))
    (s : matrixIsometries Q) (hrank : Even (finrank K' (commSpace (matrixLinearIso s.val))))
    (hβ : β⁻¹ * MulAut.congr ε ((spGlobal e).normalizerMonoidHom ⟨g⁻¹ * t * g, hg⟩) * β =
      matrixProjectiveConjugationHom Q (matrixIsometryInclusion Q s)) : False := by
  have hsΩ : (s : GL (Fin d) K') ∈ matrixDerived Q :=
    (mem_matrixDerived_iff_even hQ hT s.2).2 hrank
  rw [matrixProjectiveConjugationHom_eq_conj Q s hsΩ] at hβ
  have hc : MulAut.congr ε ((spGlobal e).normalizerMonoidHom ⟨g⁻¹ * t * g, hg⟩) =
      MulAut.conj (β (matrixProjectiveProjection Q ⟨s, hsΩ⟩)) := by
    rw [← lagMulAut_mul_conj_mul_inv, ← hβ]
    group
  exact not_mem_range_conj_of_mod_four hset hn hn4 hKc hf e ht hKt hκ hglob hg
    (lagMem_range_conj_of_congr ε _ hc)

end StepOne

section Partner

variable {X : Type*} [Group X] {K : Type} [Field K] {K' : Type} [Field K'] [Finite K']
  [CharP K' 2] {n : ℕ} {Q : QuadraticForm K' (Fin (2 * (n + 1)) → K')}

theorem exists_bPartner_of_linear (σ : K ≃+* K') (hQ : Q.polarBilin.Nondegenerate)
    (hT : ∃ T : Submodule K' (Fin (2 * (n + 1)) → K'), Module.finrank K' T = 3 ∧
      ∀ x ∈ T, Q x = 0)
    (hE : ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ =
      elementaryGroup Q)
    (ε : X ≃* matrixProjectiveDerived Q) {α : MulAut X} {s : matrixIsometries Q}
    (hs : s * s = 1) {j : ℕ} (hj : 1 ≤ j)
    (hrank : finrank K' (commSpace (matrixLinearIso s.val)) = 2 * j + 1)
    (hθs : MulAut.congr ε α = matrixProjectiveConjugationHom Q (matrixIsometryInclusion Q s)) :
    2 * j ≤ n ∧ ∃ (ψ : StatedSp n K →* X) (η : MulAut X) (ρ : matrixIsometries Q),
      Function.Injective ψ ∧ α = MulAut.conj (ψ (spARep n j)) * η ∧
      fixedSubgroup η = ψ.range ∧
      fixedSubgroup α = (centralizer ({spARep n j} : Set (StatedSp n K))).map ψ ∧
      ρ * ρ = 1 ∧ finrank K' (commSpace (matrixLinearIso ρ.val)) = 1 ∧
      MulAut.congr ε η = matrixProjectiveConjugationHom Q (matrixIsometryInclusion Q ρ) ∧
      ∀ (θ : MulAut X) (s₀ : matrixIsometries Q), s₀ * s₀ = 1 →
        finrank K' (commSpace (matrixLinearIso s₀.val)) = 1 →
        MulAut.congr ε θ = matrixProjectiveConjugationHom Q (matrixIsometryInclusion Q s₀) →
        θ * α = α * θ → fixedSubgroup α ≤ fixedSubgroup θ → θ = η := by
  have hd : 1 ≤ 2 * (n + 1) := by omega
  have h2j : 2 * j ≤ n := by
    have h1 := bCoord_two_mul_finrank_le hQ hs
    rw [hrank] at h1
    omega
  obtain ⟨w, hw, -, hfixw⟩ := bCoord_canonical hQ hs ⟨j, hrank⟩
  have hw0 : Q w ≠ 0 := by rw [hw]; exact one_ne_zero
  have hQ0 : ∃ v, Q v ≠ 0 := ⟨w, hw0⟩
  obtain ⟨φ, hφinj, hφmem, hφsurj, hφa⟩ :=
    omegaBSpParamInput_holds n K' Q hQ hT hE s hs j hj hrank w hw0 hw hfixw
  obtain ⟨ρ, hρ⟩ : ∃ ρ, ρ = reflMat Q w hw0 := ⟨_, rfl⟩
  have hρO : ρ ∈ matrixIsometries Q := hρ ▸ reflMat_mem_isometries w hw0
  have hρρ : ρ * ρ = 1 := hρ ▸ reflMat_mul_self w hw0
  have hcomm : ∀ γ : GL (Fin (2 * (n + 1))) K', γ ∈ matrixIsometries Q →
      (γ * ρ = ρ * γ ↔
        (γ : Matrix (Fin (2 * (n + 1))) (Fin (2 * (n + 1))) K') *ᵥ w = w) :=
    fun γ hγ => hρ ▸ comm_reflMat_iff hQ hγ hw hw0
  rw [← hρ] at hφmem hφsurj hφa
  set ρI : matrixIsometries Q := ⟨ρ, hρO⟩ with hρI
  set φ' : StatedSp n K →* GL (Fin (2 * (n + 1))) K' :=
    φ.comp (F4Pilot.statedSpCongr σ n).toMonoidHom with hφ'
  have hφ'mem : ∀ x, φ' x ∈ matrixDerived Q ∧ φ' x * ρ = ρ * φ' x := fun x => hφmem _
  have hφ'a : φ' (spARep n j) = s.val * ρ := by
    rw [hφ', MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, bCoord_statedSpCongr_spARep, hφa]
  set φc : StatedSp n K →* matrixDerived Q :=
    φ'.codRestrict (matrixDerived Q) (fun x => (hφ'mem x).1) with hφc
  have hφcval : ∀ x, ((φc x : matrixDerived Q) : GL (Fin (2 * (n + 1))) K') = φ' x :=
    fun x => rfl
  have hφcinj : Function.Injective φc := fun x y h =>
    (F4Pilot.statedSpCongr σ n).injective (hφinj (congrArg Subtype.val h))
  have hφcsurj : ∀ A : matrixDerived Q, A.val * ρ = ρ * A.val → ∃ x, φc x = A := by
    intro A hA
    obtain ⟨x, hx⟩ := hφsurj A.val A.2 hA
    refine ⟨(F4Pilot.statedSpCongr σ n).symm x, Subtype.ext ?_⟩
    rw [hφcval, hφ', MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply,
      hx]
  set ψ : StatedSp n K →* X :=
    ε.symm.toMonoidHom.comp ((matrixProjectiveProjection Q).comp φc) with hψ
  have hψinj : Function.Injective ψ :=
    ε.symm.injective.comp ((bCoord_proj_injective hQ0).comp hφcinj)
  have hψx : ∀ x, ε (ψ x) = matrixProjectiveProjection Q (φc x) := fun x => by
    simp [hψ]
  have hψx' : ∀ x, ψ x = ε.symm (matrixProjectiveProjection Q (φc x)) := fun x => by
    simp [hψ]
  set η : MulAut X := (MulAut.congr ε).symm
    (matrixProjectiveConjugationHom Q (matrixIsometryInclusion Q ρI)) with hηdef
  have hηε : MulAut.congr ε η =
      matrixProjectiveConjugationHom Q (matrixIsometryInclusion Q ρI) := by
    rw [hηdef, MulEquiv.apply_symm_apply]
  have hα : α = MulAut.conj (ψ (spARep n j)) * η := by
    apply (MulAut.congr ε).injective
    rw [hθs, map_mul, bCoord_congr_conj, hηε, hψx, bCoord_conj_proj_eq, ← map_mul, ← map_mul]
    congr 2
    apply Subtype.ext
    change s.val = (φc (spARep n j) : GL (Fin (2 * (n + 1))) K') * ρ
    rw [hφcval, hφ'a, mul_assoc, hρρ, mul_one]
  have hη : fixedSubgroup η = ψ.range := by
    ext y
    obtain ⟨A, hA⟩ := matrixProjectiveProjection_surjective Q (ε y)
    have hy : y = ε.symm (matrixProjectiveProjection Q A) := by
      rw [hA, MulEquiv.symm_apply_apply]
    rw [hy, bCoord_mem_fixedSubgroup_iff hQ0 ε hηε A]
    constructor
    · intro h
      obtain ⟨x, hx⟩ := hφcsurj A h.symm
      exact ⟨x, by rw [hψx', hx]⟩
    · rintro ⟨x, hx⟩
      have h1 : matrixProjectiveProjection Q (φc x) = matrixProjectiveProjection Q A := by
        rw [← hψx, hx, MulEquiv.apply_symm_apply]
      rw [← bCoord_proj_injective hQ0 h1]
      exact (hφ'mem x).2.symm
  have hfix : fixedSubgroup α =
      (centralizer ({spARep n j} : Set (StatedSp n K))).map ψ := by
    ext y
    obtain ⟨A, hA⟩ := matrixProjectiveProjection_surjective Q (ε y)
    have hy : y = ε.symm (matrixProjectiveProjection Q A) := by
      rw [hA, MulEquiv.symm_apply_apply]
    rw [hy, bCoord_mem_fixedSubgroup_iff hQ0 ε hθs A]
    constructor
    · intro h
      have hAO : A.val ∈ matrixIsometries Q := matrixDerived_le_isometries Q A.2
      have hAρ := (hcomm A.val hAO).2 (hfixw A.val hAO h.symm)
      obtain ⟨x, hx⟩ := hφcsurj A hAρ
      refine ⟨x, mem_centralizer_singleton_iff.2 ?_, by rw [hψx', hx]⟩
      apply hφcinj
      apply Subtype.ext
      rw [map_mul, map_mul, Subgroup.coe_mul, Subgroup.coe_mul, hφcval (spARep n j), hφ'a, hx]
      have hAsρ : A.val * (s.val * ρ) = s.val * ρ * A.val := by
        calc A.val * (s.val * ρ) = A.val * s.val * ρ := (mul_assoc _ _ _).symm
          _ = s.val * A.val * ρ := by rw [h]
          _ = s.val * (A.val * ρ) := mul_assoc _ _ _
          _ = s.val * (ρ * A.val) := by rw [hAρ]
          _ = s.val * ρ * A.val := (mul_assoc _ _ _).symm
      exact hAsρ
    · rintro ⟨x, hx, hxy⟩
      have h1 : matrixProjectiveProjection Q (φc x) = matrixProjectiveProjection Q A := by
        rw [← hψx, hxy, MulEquiv.apply_symm_apply]
      rw [← bCoord_proj_injective hQ0 h1, hφcval]
      have hxa := mem_centralizer_singleton_iff.1 hx
      have h3 : Commute (φ' x) (s.val * ρ) := by
        have h4 := congrArg (fun z => ((φc z : matrixDerived Q) : GL (Fin (2 * (n + 1))) K')) hxa
        simp only [map_mul, Subgroup.coe_mul, hφcval, hφ'a] at h4
        exact h4
      have h5 : Commute (φ' x) ρ := (hφ'mem x).2
      have h6 := h3.mul_right h5
      rw [mul_assoc, hρρ, mul_one] at h6
      exact h6.eq.symm
  have hρI1 : finrank K' (commSpace (matrixLinearIso ρI.val)) = 1 := by
    change finrank K' (commSpace (matrixLinearIso ρ)) = 1
    rw [hρ]
    exact finrank_commSpace_reflMat hQ w hw0
  have hρIρI : ρI * ρI = 1 := Subtype.ext hρρ
  refine ⟨h2j, ψ, η, ρI, hψinj, hα, hη, hfix, hρIρI, hρI1, hηε, ?_⟩
  intro θ s₀ hs₀ hr₀ hθ hc hle
  obtain ⟨v, hv, hs₀v⟩ := exists_eq_reflMat_of_rank_eq_one hQ s₀ hs₀
    (by rw [lagRank_sub_one_eq_finrank_commSpace]; exact hr₀)
  have hc' : s₀ * s = s * s₀ := by
    apply CFSG.ComponentClassification.UnbalancedCatalog.kappa_inclusion_injective hQ hT hE hd
    have h1 := congrArg (MulAut.congr ε) hc
    rw [map_mul, map_mul, hθ, hθs] at h1
    simpa only [MonoidHom.coe_comp, Function.comp_apply, map_mul] using h1
  obtain ⟨c, hc2⟩ := FiniteField.isSquare_of_char_two (ringChar.eq K' 2) (1 / Q v)
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [mul_zero, one_div, inv_eq_zero] at hc2
    exact hv hc2
  have hv'1 : Q (c • v) = 1 := by
    rw [CFSG.ClassicalGroups.Orthogonal.map_smul_eq_sq, _root_.sq, ← hc2, one_div,
      inv_mul_cancel₀ hv]
  have hv'0 : Q (c • v) ≠ 0 := by rw [hv'1]; exact one_ne_zero
  have hs₀v' : s₀.val = reflMat Q (c • v) hv'0 := by rw [hs₀v, reflMat_smul v hv hc0 hv'0]
  have hsv' : (s.val : Matrix (Fin (2 * (n + 1))) (Fin (2 * (n + 1))) K') *ᵥ (c • v) =
      c • v :=
    (comm_reflMat_iff hQ s.2 hv'1 hv'0).1 (by
      rw [← hs₀v']
      exact (congrArg Subtype.val hc').symm)
  have hfixv : ∀ A ∈ matrixDerived Q, A * s.val = s.val * A →
      (A : Matrix (Fin (2 * (n + 1))) (Fin (2 * (n + 1))) K') *ᵥ (c • v) = c • v := by
    intro A hA hAs
    have hmem : ε.symm (matrixProjectiveProjection Q ⟨A, hA⟩) ∈ fixedSubgroup α :=
      (bCoord_mem_fixedSubgroup_iff hQ0 ε hθs ⟨A, hA⟩).2 hAs.symm
    have hAs₀ := (bCoord_mem_fixedSubgroup_iff hQ0 ε hθ ⟨A, hA⟩).1 (hle hmem)
    have h2 : A * reflMat Q (c • v) hv'0 = reflMat Q (c • v) hv'0 * A := by
      rw [← hs₀v']
      exact hAs₀.symm
    exact (comm_reflMat_iff hQ (matrixDerived_le_isometries Q hA) hv'1 hv'0).1 h2
  obtain ⟨c', hc'⟩ := Submodule.mem_span_singleton.1
    (omegaBFixedVectorInput_holds n K' Q hQ hT hE s hs j hj hrank w hw hfixw (c • v) hsv' hfixv)
  have hc'1 : c' = 1 := by
    have h3 := congrArg Q hc'
    rw [CFSG.ClassicalGroups.Orthogonal.map_smul_eq_sq, hw, mul_one, hv'1, _root_.sq] at h3
    exact CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.eq_one_of_mul_self_eq_one_of_charTwo h3
  have hvw : c • v = w := by rw [← hc', hc'1, one_smul]
  have hs₀ρ : s₀ = ρI := by
    apply Subtype.ext
    change s₀.val = ρ
    rw [hs₀v', hρ]
    exact reflMat_congr hvw hv'0 hw0
  apply (MulAut.congr ε).injective
  refine hθ.trans ?_
  rw [hs₀ρ]
  exact hηε.symm

theorem exists_inn_conj_of_reflections (hQ : Q.polarBilin.Nondegenerate)
    (hT : ∃ T : Submodule K' (Fin (2 * (n + 1)) → K'), Module.finrank K' T = 3 ∧
      ∀ x ∈ T, Q x = 0)
    (ε : X ≃* matrixProjectiveDerived Q) {θ θ' : MulAut X} {s₀ u : matrixIsometries Q}
    (hs₀ : s₀ * s₀ = 1) (hu : u * u = 1)
    (hr₀ : finrank K' (commSpace (matrixLinearIso s₀.val)) = 1)
    (hru : finrank K' (commSpace (matrixLinearIso u.val)) = 1)
    (hθ : MulAut.congr ε θ = matrixProjectiveConjugationHom Q (matrixIsometryInclusion Q s₀))
    (hθ' : MulAut.congr ε θ' = matrixProjectiveConjugationHom Q (matrixIsometryInclusion Q u)) :
    ∃ z : X, θ' = MulAut.conj z * θ * (MulAut.conj z)⁻¹ := by
  obtain ⟨v, hv, hs₀v⟩ := exists_eq_reflMat_of_rank_eq_one hQ s₀ hs₀
    (by rw [lagRank_sub_one_eq_finrank_commSpace]; exact hr₀)
  obtain ⟨γ, hγ⟩ := exists_conj_of_rank_eq_one hQ hT hu hs₀
    (by rw [lagRank_sub_one_eq_finrank_commSpace]; exact hru)
    (by rw [lagRank_sub_one_eq_finrank_commSpace]; exact hr₀)
  obtain ⟨γ', hγ'Ω, hγ'⟩ : ∃ γ' : matrixIsometries Q, γ'.val ∈ matrixDerived Q ∧
      γ' * s₀ * γ'⁻¹ = u := by
    by_cases hγΩ : γ.val ∈ matrixDerived Q
    · exact ⟨γ, hγΩ, hγ⟩
    · refine ⟨γ * s₀, ?_, ?_⟩
      · change γ.val * s₀.val ∈ matrixDerived Q
        rw [hs₀v]
        exact (mul_reflMat_mem_iff hQ hT γ.2 v hv).2 hγΩ
      · rw [← hγ]
        calc γ * s₀ * s₀ * (γ * s₀)⁻¹ = γ * (s₀ * s₀) * s₀⁻¹ * γ⁻¹ := by group
          _ = γ * s₀ * γ⁻¹ := by
            rw [hs₀, mul_one, show s₀⁻¹ = s₀ from inv_eq_of_mul_eq_one_right hs₀]
  refine ⟨ε.symm (matrixProjectiveProjection Q ⟨γ'.val, hγ'Ω⟩), (MulAut.congr ε).injective ?_⟩
  rw [hθ', map_mul, map_mul, map_inv, bCoord_congr_conj, MulEquiv.apply_symm_apply, hθ,
    ← bCoord_kappa_of_mem γ' hγ'Ω, ← hγ']
  simp only [map_mul, map_inv]

end Partner

section Shapes

variable {G : Type} [Group G] {L : Subgroup G} {K : Type} [Field K] {K' : Type} [Field K']
  [Finite K'] [CharP K' 2] {n : ℕ} {Q : QuadraticForm K' (Fin (2 * (n + 1)) → K')}

theorem spOmegaBShape_of_linear (e : L ≃* StatedSp n K) (σ : K ≃+* K')
    (hQ : Q.polarBilin.Nondegenerate)
    (hT : ∃ T : Submodule K' (Fin (2 * (n + 1)) → K'), Module.finrank K' T = 3 ∧
      ∀ x ∈ T, Q x = 0)
    (hE : ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ =
      elementaryGroup Q)
    (ε : spGlobal e ≃* matrixProjectiveDerived Q) {θ α : MulAut (spGlobal e)}
    {s₀ s : matrixIsometries Q} (hs₀ : s₀ * s₀ = 1)
    (hr₀ : finrank K' (commSpace (matrixLinearIso s₀.val)) = 1)
    (hθ : MulAut.congr ε θ = matrixProjectiveConjugationHom Q (matrixIsometryInclusion Q s₀))
    (hs : s * s = 1) {j : ℕ} (hj : 1 ≤ j)
    (hrank : finrank K' (commSpace (matrixLinearIso s.val)) = 2 * j + 1)
    (hθs : MulAut.congr ε α = matrixProjectiveConjugationHom Q (matrixIsometryInclusion Q s)) :
    SpOmegaBShape e θ α j := by
  obtain ⟨h2j, ψ, η, ρ, hψinj, hα, hη, hfix, hρρ, hρ1, hηε, huniq⟩ :=
    exists_bPartner_of_linear σ hQ hT hE ε hs hj hrank hθs
  obtain ⟨z, hz⟩ := exists_inn_conj_of_reflections hQ hT ε hs₀ hρρ hr₀ hρ1 hθ hηε
  exact ⟨hj, h2j, ψ, η, hψinj, hα, hη, hfix, ⟨z, hz⟩, huniq θ s₀ hs₀ hr₀ hθ⟩

theorem mulAutCongr_trans_inv {X Y : Type*} [Group X] [Group Y] (ε : X ≃* Y) (β : MulAut Y)
    (α : MulAut X) : MulAut.congr (ε.trans β⁻¹) α = β⁻¹ * MulAut.congr ε α * β := by
  refine MulEquiv.ext fun y => ?_
  rfl

theorem spOmegaBShapeAut_of_conj (e : L ≃* StatedSp n K) (σ : K ≃+* K')
    (hQ : Q.polarBilin.Nondegenerate)
    (hT : ∃ T : Submodule K' (Fin (2 * (n + 1)) → K'), Module.finrank K' T = 3 ∧
      ∀ x ∈ T, Q x = 0)
    (hE : ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ =
      elementaryGroup Q)
    (ε : spGlobal e ≃* matrixProjectiveDerived Q) {θ α : MulAut (spGlobal e)}
    {β₀ β : MulAut (matrixProjectiveDerived Q)} {s₀ s : matrixIsometries Q} (hs₀ : s₀ * s₀ = 1)
    (hr₀ : finrank K' (commSpace (matrixLinearIso s₀.val)) = 1)
    (hθ : β₀⁻¹ * MulAut.congr ε θ * β₀ =
      matrixProjectiveConjugationHom Q (matrixIsometryInclusion Q s₀))
    (hs : s * s = 1) {j : ℕ} (hj : 1 ≤ j)
    (hrank : finrank K' (commSpace (matrixLinearIso s.val)) = 2 * j + 1)
    (hθs : β⁻¹ * MulAut.congr ε α * β =
      matrixProjectiveConjugationHom Q (matrixIsometryInclusion Q s)) :
    SpOmegaBShapeAut e θ α j := by
  have hθs' : MulAut.congr (ε.trans β⁻¹) α =
      matrixProjectiveConjugationHom Q (matrixIsometryInclusion Q s) := by
    rw [mulAutCongr_trans_inv]
    exact hθs
  obtain ⟨h2j, ψ, η, ρ, hψinj, hα, hη, hfix, hρρ, hρ1, hηε, -⟩ :=
    exists_bPartner_of_linear σ hQ hT hE (ε.trans β⁻¹) hs hj hrank hθs'
  rw [mulAutCongr_trans_inv] at hηε
  obtain ⟨γ, hγ⟩ := exists_conj_of_rank_eq_one hQ hT hρρ hs₀
    (by rw [lagRank_sub_one_eq_finrank_commSpace]; exact hρ1)
    (by rw [lagRank_sub_one_eq_finrank_commSpace]; exact hr₀)
  obtain ⟨β', hβ'⟩ := exists_conj_of_linearClass_conj ε hηε hθ hγ
  exact ⟨hj, h2j, ψ, η, hψinj, hα, hη, hfix, β', hβ'⟩

theorem coset_dichotomy_of_linear (e : L ≃* StatedSp n K) (σ : K ≃+* K')
    (hQ : Q.polarBilin.Nondegenerate)
    (hT : ∃ T : Submodule K' (Fin (2 * (n + 1)) → K'), Module.finrank K' T = 3 ∧
      ∀ x ∈ T, Q x = 0)
    (hE : ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ =
      elementaryGroup Q)
    (ε : spGlobal e ≃* matrixProjectiveDerived Q) {θ : MulAut (spGlobal e)}
    {s₀ : matrixIsometries Q} (hs₀ : s₀ * s₀ = 1)
    (hr₀ : finrank K' (commSpace (matrixLinearIso s₀.val)) = 1)
    (hθ : MulAut.congr ε θ = matrixProjectiveConjugationHom Q (matrixIsometryInclusion Q s₀))
    (y : spGlobal e) (hy : (MulAut.conj y * θ) * (MulAut.conj y * θ) = 1) :
    (∃ z : spGlobal e, MulAut.conj y * θ = MulAut.conj z * θ * (MulAut.conj z)⁻¹) ∨
      ∃ j, 1 ≤ j ∧ 2 * j ≤ n ∧ SpOmegaBShape e θ (MulAut.conj y * θ) j := by
  have hd : 1 ≤ 2 * (n + 1) := by omega
  obtain ⟨Y, hY⟩ := matrixProjectiveProjection_surjective Q (ε y)
  set u : matrixIsometries Q := ⟨Y.val, matrixDerived_le_isometries Q Y.2⟩ * s₀ with hu
  have hθu : MulAut.congr ε (MulAut.conj y * θ) =
      matrixProjectiveConjugationHom Q (matrixIsometryInclusion Q u) := by
    rw [map_mul, bCoord_congr_conj, hθ, ← hY, bCoord_conj_proj_eq, ← map_mul, ← map_mul]
  have huu : u * u = 1 := by
    apply CFSG.ComponentClassification.UnbalancedCatalog.kappa_inclusion_injective hQ hT hE hd
    simp only [MonoidHom.coe_comp, Function.comp_apply, map_mul, map_one]
    rw [← hθu, ← map_mul, hy, map_one]
  have hs₀not : s₀.val ∉ matrixDerived Q := by
    rw [mem_matrixDerived_iff_even hQ hT s₀.2, hr₀]
    decide
  have hunot : u.val ∉ matrixDerived Q := by
    intro hu'
    apply hs₀not
    have h1 : s₀.val = Y.val⁻¹ * u.val := by
      rw [hu, Subgroup.coe_mul, ← mul_assoc]
      simp
    rw [h1]
    exact mul_mem (inv_mem Y.2) hu'
  have hodd : Odd (finrank K' (commSpace (matrixLinearIso u.val))) := by
    rw [← Nat.not_even_iff_odd]
    exact fun hev => hunot ((mem_matrixDerived_iff_even hQ hT u.2).2 hev)
  obtain ⟨m, hm⟩ := hodd
  rcases Nat.eq_zero_or_pos m with hm0 | hmpos
  · left
    exact exists_inn_conj_of_reflections hQ hT ε hs₀ huu hr₀ (by omega) hθ hθu
  · right
    have hsh := spOmegaBShape_of_linear e σ hQ hT hE ε hs₀ hr₀ hθ huu hmpos hm hθu
    exact ⟨m, hmpos, hsh.2.1, hsh⟩

end Shapes

end CFSG.SeitzReduction.SymplecticPilot
