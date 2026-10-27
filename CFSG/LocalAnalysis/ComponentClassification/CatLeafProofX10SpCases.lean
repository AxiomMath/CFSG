module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofX10SpModel
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBUnitaryBCentralizer

public noncomputable section

namespace CFSG.ComponentClassification.CatLeafProof.X10Sp

open CFSG Subgroup Module CFSG.Assembly.LowTwoRank
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ComponentClassification.CatalogueBSymplecticB
open LinearMap (BilinForm)

theorem similitudeCentralizer_component_cases {ℓ f : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2)
    (hf : 1 ≤ f) {K : Type} [Field K] [Finite K] (hK : Nat.card K = ℓ ^ f) {V : Type}
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] {r : ℕ} (hr : 3 ≤ r)
    (hdim : finrank K V = 2 * r) {B : BilinForm K V} (hB : B.IsAlt) (hBnd : B.Nondegenerate)
    {A : LinearMap.GeneralLinearGroup K V} (hAns : ∀ c : K, (A : Module.End K V) ≠ c • 1)
    {d : K} (hd0 : d ≠ 0) (hAA : (A : Module.End K V) * (A : Module.End K V) = d • 1) {μ : K}
    (hAμ : ∀ v w, B ((A : Module.End K V) v) ((A : Module.End K V) w) = μ * B v w)
    {M : Subgroup (similitudeCentralizer B A)} (hM : IsComponent M) :
    (∃ z ∈ M, (∀ y ∈ M, z * y = y * z) ∧ z * z = 1 ∧
      ∀ c : K, ((z : LinearMap.GeneralLinearGroup K V) : Module.End K V) ≠ c • 1) ∨
    CentralModel ℓ .PSL r f M ∨ (Even r ∧ CentralModel ℓ .PSp (r / 2) (2 * f) M) ∨
    CentralModel ℓ .PSU r f M := by
  have hodd : Odd (Nat.card K) := by
    rw [hK]
    exact (hℓ.odd_of_ne_two hℓ2).pow
  have h2 : (2 : K) ≠ 0 := CatalogueBOddQuadratic.two_ne_zero_of_odd_card hodd
  obtain ⟨hε, hsplit, hnonsplit⟩ := odd_symplectic_scalar_square_centralizer_structure hℓ hℓ2
    hf hK (by omega) hdim hB hBnd hAns hd0 hAA hAμ
  by_cases hsq : ∃ l : K, l ^ 2 = d
  · obtain ⟨l, hl⟩ := hsq
    obtain ⟨hP, hMm, hpos, hneg⟩ := hsplit l hl
    rcases hε with h1 | h1
    ·
      left
      obtain ⟨-, haltP, haltM, hndP, hndM, e, hres⟩ := hpos h1
      have hP' := Submodule.one_le_finrank_iff.mpr hP
      have hM' := Submodule.one_le_finrank_iff.mpr hMm
      obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hP
      obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hMm
      have hns : ∀ (x : similitudeCentralizer B A),
          ((((e x).1 : LinearMap.GeneralLinearGroup K (eigenPlus l (A : Module.End K V))) :
              Module.End K (eigenPlus l (A : Module.End K V))) = -1 ∧
            (((e x).2 : LinearMap.GeneralLinearGroup K (eigenMinus l (A : Module.End K V))) :
              Module.End K (eigenMinus l (A : Module.End K V))) = 1) ∨
          ((((e x).1 : LinearMap.GeneralLinearGroup K (eigenPlus l (A : Module.End K V))) :
              Module.End K (eigenPlus l (A : Module.End K V))) = 1 ∧
            (((e x).2 : LinearMap.GeneralLinearGroup K (eigenMinus l (A : Module.End K V))) :
              Module.End K (eigenMinus l (A : Module.End K V))) = -1) →
          ∀ c : K, ((x : LinearMap.GeneralLinearGroup K V) : Module.End K V) ≠ c • 1 := by
        intro x hx c hc
        obtain ⟨hx₁, hx₂⟩ := hres x
        have e₁ := LinearMap.congr_fun hx₁ ⟨v, hv⟩
        have e₂ := LinearMap.congr_fun hx₂ ⟨w, hw⟩
        simp only [LinearMap.comp_apply, Submodule.subtype_apply, hc, LinearMap.smul_apply,
          Module.End.one_apply] at e₁ e₂
        rcases hx with ⟨ha, hb⟩ | ⟨ha, hb⟩
        · rw [ha] at e₁
          rw [hb] at e₂
          simp only [LinearMap.neg_apply, Module.End.one_apply, Submodule.coe_neg] at e₁ e₂
          have hc1 : c = -1 := by
            have h3 : (c + 1) • v = 0 := by rw [add_smul, one_smul, ← e₁, neg_add_cancel]
            have := (smul_eq_zero.1 h3).resolve_right hv0
            linear_combination this
          have hc2 : c = 1 := by
            have h3 : (c - 1) • w = 0 := by rw [sub_smul, one_smul, ← e₂, sub_self]
            have := (smul_eq_zero.1 h3).resolve_right hw0
            linear_combination this
          exact h2 (by linear_combination hc1 - hc2)
        · rw [ha] at e₁
          rw [hb] at e₂
          simp only [LinearMap.neg_apply, Module.End.one_apply, Submodule.coe_neg] at e₁ e₂
          have hc1 : c = 1 := by
            have h3 : (c - 1) • v = 0 := by rw [sub_smul, one_smul, ← e₁, sub_self]
            have := (smul_eq_zero.1 h3).resolve_right hv0
            linear_combination this
          have hc2 : c = -1 := by
            have h3 : (c + 1) • w = 0 := by rw [add_smul, one_smul, ← e₂, neg_add_cancel]
            have := (smul_eq_zero.1 h3).resolve_right hw0
            linear_combination this
          exact h2 (by linear_combination hc2 - hc1)
      let m₁ : LocalAnalysis.ComponentInitial.sesqUnitaryGroup
          (B.domRestrict₁₂ (eigenPlus l (A : Module.End K V)) (eigenPlus l (A : Module.End K V))) :=
        ⟨-1, fun x y => by simp⟩
      let m₂ : LocalAnalysis.ComponentInitial.sesqUnitaryGroup
          (B.domRestrict₁₂ (eigenMinus l (A : Module.End K V))
            (eigenMinus l (A : Module.End K V))) :=
        ⟨-1, fun x y => by simp⟩
      have hm₁ : ∀ g, m₁ * g = g * m₁ := fun g => Subtype.ext (Units.ext (by
        change (-1 : Module.End K _) * _ = _ * (-1 : Module.End K _)
        rw [neg_one_mul, mul_neg_one]))
      have hm₂ : ∀ g, m₂ * g = g * m₂ := fun g => Subtype.ext (Units.ext (by
        change (-1 : Module.End K _) * _ = _ * (-1 : Module.End K _)
        rw [neg_one_mul, mul_neg_one]))
      have hm₁₁ : m₁ * m₁ = 1 := Subtype.ext (Units.ext (by
        change (-1 : Module.End K _) * (-1 : Module.End K _) = 1
        rw [neg_one_mul, neg_neg]))
      have hm₂₂ : m₂ * m₂ = 1 := Subtype.ext (Units.ext (by
        change (-1 : Module.End K _) * (-1 : Module.End K _) = 1
        rw [neg_one_mul, neg_neg]))
      have hMe := LocalCores.isComponent_map_mulEquiv e hM
      rcases LocalAnalysis.ComponentInitial.CentralQuotientLift.fst_eq_or_snd_eq_of_isComponent_prod
          hMe with h2' | h1'
      ·
        have h2'' : ∀ x ∈ M, (e x).2 = 1 := fun x hx => h2' _ ⟨x, hx, rfl⟩
        obtain ⟨ρ, -, hρc, hρ⟩ := OddClassSelector.restrict_component e hM h2''
        have htop := eq_top_of_isComponent_sesqUnitaryGroup hℓ hℓ2 hf hK _ haltP hndP
          (by omega) hρc
        obtain ⟨x, hx⟩ : m₁ ∈ ρ.range := htop ▸ mem_top m₁
        have hex : e x = (m₁, 1) := Prod.ext ((hρ x).symm.trans hx) (h2'' x x.2)
        refine ⟨x, x.2, fun y _ => ?_, ?_, hns x (Or.inl ⟨?_, ?_⟩)⟩
        · apply e.injective
          rw [map_mul, map_mul, hex]
          exact Prod.ext (hm₁ _) (by simp)
        · apply e.injective
          rw [map_mul, hex, map_one]
          exact Prod.ext hm₁₁ (mul_one 1)
        · rw [hex]
          rfl
        · rw [hex]
          rfl
      ·
        let e' := e.trans MulEquiv.prodComm
        have h2'' : ∀ x ∈ M, (e' x).2 = 1 := fun x hx => h1' _ ⟨x, hx, rfl⟩
        obtain ⟨ρ, -, hρc, hρ⟩ := OddClassSelector.restrict_component e' hM h2''
        have htop := eq_top_of_isComponent_sesqUnitaryGroup hℓ hℓ2 hf hK _ haltM hndM
          (by omega) hρc
        obtain ⟨x, hx⟩ : m₂ ∈ ρ.range := htop ▸ mem_top m₂
        have hex : e x = (1, m₂) := Prod.ext (h2'' x x.2) ((hρ x).symm.trans hx)
        refine ⟨x, x.2, fun y _ => ?_, ?_, hns x (Or.inr ⟨?_, ?_⟩)⟩
        · apply e.injective
          rw [map_mul, map_mul, hex]
          exact Prod.ext (by simp) (hm₂ _)
        · apply e.injective
          rw [map_mul, hex, map_one]
          exact Prod.ext (mul_one 1) hm₂₂
        · rw [hex]
          rfl
        · rw [hex]
          rfl
    ·
      right; left
      obtain ⟨-, -, hdP, -, -, -, e, -⟩ := hneg h1
      let bP : Basis (Fin r) K (eigenPlus l (A : Module.End K V)) :=
        Module.finBasisOfFinrankEq K _ hdP
      exact centralModel_of_component_equiv
        (e.trans (Units.mapEquiv (LinearMap.toMatrixAlgEquiv bP).toMulEquiv))
        (fun N hN => centralModel_GL_component hℓ hf hK hr hN) hM
  · push Not at hsq
    obtain ⟨-, hF, hcard, hfinrank, bar, hbar, hpow, hbarbar, hpos, hneg⟩ := hnonsplit hsq
    let : Field (scalarSquareField (A : Module.End K V)) := hF.toField
    have hEodd : Odd (Nat.card (scalarSquareField (A : Module.End K V))) := by
      rw [hcard]
      exact ((hℓ.odd_of_ne_two hℓ2).pow).pow
    have := finite_of_odd_card hEodd
    have : Module.Finite (scalarSquareField (A : Module.End K V)) V :=
      CatalogueBOrthogonalScalarSquareField.evaluationModule_finite (A : Module.End K V)
    rcases hε with h1 | h1
    ·
      right; right; left
      obtain ⟨BE, -, hBEalt, hBEnd, -, hiff⟩ := hpos h1
      obtain ⟨m, hdm, -⟩ :=
        CatalogueBAlternatingIsometry.exists_isometryEquiv_symplectic BE hBEalt hBEnd
      rw [hfinrank] at hdm
      have hm2 : 2 ≤ m := by omega
      refine ⟨⟨m, by omega⟩, ?_⟩
      rw [show r / 2 = m by omega]
      exact centralModel_of_component_equiv
        ((centralizerSimilitudeEquiv B A).symm.trans
          (evaluationIsometryEquiv B A (CatalogueBAlternatingIsometry.isometryGroup BE)
            (fun φ => ∀ v w, BE (φ v) (φ w) = BE v w)
            (CatalogueBAlternatingIsometry.mem_isometryGroup_iff BE) hiff))
        (fun N hN => centralModel_isometryGroup_component (j := 2 * f) hℓ hℓ2 (by omega)
          (by rw [hcard, ← pow_mul, mul_comm]) BE hBEalt hBEnd (hfinrank.trans hdm) hm2 hN) hM
    ·
      right; right; right
      obtain ⟨h, -, hsymm, hsep, hiff⟩ := hneg h1
      let sigma := RingEquiv.ofBijective bar (Function.Involutive.bijective hbarbar)
      let h' : V →ₛₗ[sigma.toRingHom] V →ₗ[scalarSquareField (A : Module.End K V)]
        scalarSquareField (A : Module.End K V) := h
      have hnd' : h'.Nondegenerate :=
        ⟨hsep, fun y hy => hsep y fun x => by
          rw [← hsymm.eq x y]
          exact (congrArg bar (hy x)).trans (map_zero bar)⟩
      have hsigma : sigma ^ 2 = 1 := RingEquiv.ext hbarbar
      have hne : sigma ≠ 1 := by
        intro heq
        let x : scalarSquareField (A : Module.End K V) :=
          ⟨A, Algebra.self_mem_adjoin_singleton K _⟩
        have hx := hbar x 0 1 (by simp only [zero_smul, zero_add, one_smul, x])
        have hfix : bar x = x := DFunLike.congr_fun heq x
        rw [hfix] at hx
        simp only [zero_smul, zero_sub, one_smul, x] at hx
        have hA2 : (2 : K) • (A : Module.End K V) = 0 := by
          rw [two_smul]
          nth_rewrite 2 [hx]
          exact add_neg_cancel _
        apply hAns 0
        rw [zero_smul]
        calc (A : Module.End K V) = (2 : K)⁻¹ • ((2 : K) • (A : Module.End K V)) := by
              rw [smul_smul, inv_mul_cancel₀ h2, one_smul]
          _ = 0 := by rw [hA2, smul_zero]
      have := centralModel_of_component_equiv
        ((centralizerSimilitudeEquiv B A).symm.trans
          (evaluationIsometryEquiv B A (CatalogueBUnitaryIsometry.isometryGroup h')
            (fun φ => ∀ v w, h (φ v) (φ w) = h v w)
            (CatalogueBUnitaryIsometry.mem_isometryGroup_iff h') hiff))
        (fun N hN => centralModel_unitary_component hℓ hℓ2 hf hcard (by omega) h' hsymm hnd'
          hsigma hne hpow hN) hM
      rwa [hfinrank] at this

end CFSG.ComponentClassification.CatLeafProof.X10Sp
