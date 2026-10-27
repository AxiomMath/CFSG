module

public import CFSG.RankThree.PartOne.KE6.Tw6D4Case

public noncomputable section

namespace CFSG.HardMathSupport.Lang.SeitzPlane

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.E6 CFSG.RankThree.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.RankThree.Classical2
  CFSG.RankThree.PartOne.KE6
open CFSG.RankThree.Lattice (e6T3W toMat lget)
open CFSG.RankThree.PartOne.KE (twistedTorusOf mem_twistedTorusOf twistedFixedPoints
  mem_twistedFixedPoints)
open scoped Matrix MatrixGroups Pointwise

variable {Ω : Type} [Field Ω] {Fr : Ω →+* Ω}

theorem tw6_D4_layer_data' {K : Type} [Field K] [Finite K] [Algebra K Ω]
    [IsAlgClosure K Ω] {ℓ f : ℕ} [Fact ℓ.Prime] [CharP Ω ℓ] (hf : 1 ≤ f)
    (hK : Nat.card K = ℓ ^ f) (hFr : ∀ c, Fr c = c ^ (ℓ ^ f)) {x : ModGL Tag.E6 Ω}
    (hx : x ∈ twistedTorusOf (tw6N Ω) (twistE6 Ω Fr)) {w : WeylGroup Tag.E6}
    (hw : (w • ·) '' torusRootKernel x = parabolicRoots Tag.E6 d4Support) :
    (rootSpan Tag.E6 Ω (torusRootKernel x)).map
        (MulAut.conj (canonicalRep (coxeterSystem Tag.E6) Ω w)).toMonoidHom =
      subsystemGroup Tag.E6 Ω d4Support ∧
    Finite ↥(rootSpan Tag.E6 Ω (torusRootKernel x) ⊓
      twistedFixedPoints (tw6N Ω) (twistE6 Ω Fr)) ∧
    CFSG.IsQuasisimple ↥(rootSpan Tag.E6 Ω (torusRootKernel x) ⊓
      twistedFixedPoints (tw6N Ω) (twistE6 Ω Fr)) ∧
    e6Commutant (((rootSpan Tag.E6 Ω (torusRootKernel x) ⊓
        twistedFixedPoints (tw6N Ω) (twistE6 Ω Fr)).map
        (MulAut.conj (canonicalRep (coxeterSystem Tag.E6) Ω w)).toMonoidHom :
          Subgroup (ModGL Tag.E6 Ω)) : Set (ModGL Tag.E6 Ω)) =
      e6Commutant (subsystemGroup Tag.E6 Ω d4Support : Set (ModGL Tag.E6 Ω)) ∧
    (∃ h₀ : ModGL Tag.E6 Ω, ∀ B : SL(2, K),
      h₀ * simpleRootSL2 Tag.E6 Ω (d4Idx 2) (Matrix.SpecialLinearGroup.map (algebraMap K Ω) B) *
        h₀⁻¹ ∈ rootSpan Tag.E6 Ω (torusRootKernel x) ⊓
          twistedFixedPoints (tw6N Ω) (twistE6 Ω Fr)) ∧
    ∃ (e : ℕ) (g : ModGL Tag.E6 Ω), (e = 1 ∨ e = 2) ∧
      (rootSpan Tag.E6 Ω (torusRootKernel x) ⊓
          twistedFixedPoints (tw6N Ω) (twistE6 Ω Fr)).map
          (MulAut.conj (canonicalRep (coxeterSystem Tag.E6) Ω w)).toMonoidHom =
        (d4Layer Fr e).map (MulAut.conj g⁻¹).toMonoidHom ∧
      Nonempty (↥(rootSpan Tag.E6 Ω (torusRootKernel x) ⊓
          twistedFixedPoints (tw6N Ω) (twistE6 Ω Fr)) ≃* ↥(d4ThetaFixed Ω Fr e)) := by
  classical
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed K
  have hℓ : ℓ.Prime := Fact.out
  have : Fintype K := Fintype.ofFinite K
  set S := torusRootKernel x with hSdef
  set n := canonicalRep (coxeterSystem Tag.E6) Ω w with hn
  have hFrs : Function.Surjective Fr := fun y => by
    obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq y (pow_pos hℓ.pos f)
    exact ⟨z, by rw [hFr, hz]⟩
  have hFrb : Function.Bijective Fr := ⟨Fr.injective, hFrs⟩
  have hSroots : ∀ α ∈ S, IsRoot Tag.E6 α := fun α hα => hα.1
  have hQ : (rootSpan Tag.E6 Ω S).map (MulAut.conj n).toMonoidHom =
      subsystemGroup Tag.E6 Ω d4Support := by
    rw [(canonical_weyl_root_transport Tag.E6 Ω).1 w S hSroots, hw, subsystemGroup_eq_rootSpan]
  have hvS := tw6_torusRootKernel_smul_stable hFr hx
  have hT : ∀ β ∈ parabolicRoots Tag.E6 d4Support,
      (w * e6T3W * w⁻¹) • β ∈ parabolicRoots Tag.E6 d4Support := by
    intro β hβ
    rw [← hw] at hβ ⊢
    obtain ⟨α, hα, rfl⟩ := hβ
    exact ⟨e6T3W • α, hvS α hα, by simp [mul_smul]⟩
  obtain ⟨L, hL, hLT⟩ := weylMatrix_conj_e6T3W_mem_orbit w
  obtain ⟨e, he, hWe⟩ := d4TrialityWeylType_of_conj hL hLT hT
  have hnwM := canonicalRep_mem_monomialSubgroup (τ := Tag.E6) Ω w
  have hnWM := canonicalRep_mem_monomialSubgroup (τ := Tag.E6) Ω tw6W
  set δw : WeylGroup Tag.E6 := tw6Delta w with hδw
  have hnδM := canonicalRep_mem_monomialSubgroup (τ := Tag.E6) Ω δw
  obtain ⟨m₀, hm₀M, hm₀W, hm₀P⟩ := exists_monomial_eq_diagramMap_on_d4 (Ω := Ω)
  set m₁ : ModGL Tag.E6 Ω := n * tw6N Ω * (canonicalRep (coxeterSystem Tag.E6) Ω δw)⁻¹
    with hm₁def
  have hm₁M : m₁ ∈ monomialSubgroup Tag.E6 Ω := mul_mem (mul_mem hnwM hnWM) (inv_mem hnδM)
  set m : ModGL Tag.E6 Ω := m₁ * m₀ with hmdef
  have hm : m ∈ monomialSubgroup Tag.E6 Ω := mul_mem hm₁M hm₀M
  have hcan : weylQuotientHom Tag.E6 Ω ⟨n, hnwM⟩ = w :=
    weylQuotientHom_eq (mapsRootLines_canonicalRep w)
  have hcanW : weylQuotientHom Tag.E6 Ω ⟨tw6N Ω, hnWM⟩ = tw6W :=
    weylQuotientHom_eq (mapsRootLines_canonicalRep tw6W)
  have hcanδ : weylQuotientHom Tag.E6 Ω ⟨canonicalRep (coxeterSystem Tag.E6) Ω δw, hnδM⟩ = δw :=
    weylQuotientHom_eq (mapsRootLines_canonicalRep δw)
  have hwm : weylQuotientHom Tag.E6 Ω ⟨m, hm⟩ = (w * tw6W * δw⁻¹) * tw6Wt := by
    have e' : (⟨m, hm⟩ : monomialSubgroup Tag.E6 Ω) =
        ⟨n, hnwM⟩ * ⟨tw6N Ω, hnWM⟩ * ⟨canonicalRep (coxeterSystem Tag.E6) Ω δw, hnδM⟩⁻¹ *
          ⟨m₀, hm₀M⟩ := rfl
    rw [e', map_mul, map_mul, map_mul, map_inv, hcan, hcanW, hcanδ, hm₀W]
  have hWneg : ∀ β : Fin Tag.D4.rank → ℤ, IsRoot Tag.D4 β →
      ((w * tw6W * δw⁻¹) * tw6Wt) • d4Lat β = -((w * e6T3W * w⁻¹) • d4Lat β) := by
    intro β _
    have hδ : δw⁻¹ = tw6Delta w⁻¹ := tw6Delta_inv w
    rw [mul_smul, tw6Wt_smul_d4Lat, mul_smul, hδ, weylTwist_E6_smul_permLattice, mul_smul,
      tw6W_smul, permLattice_e6Rho_e6Rho, mul_smul, mul_smul, smul_neg]
  obtain ⟨g, hg, hgconj⟩ := exists_conj_eq_d4Theta ℓ f hf hFr hm
    (by rw [hwm]; exact tw6_weylType_neg hWe hWneg)
  set P := rootSpan Tag.E6 Ω S ⊓ twistedFixedPoints (tw6N Ω) (twistE6 Ω Fr)
    with hPdef
  have hθ_eq : ∀ z ∈ subsystemGroup Tag.E6 Ω d4Support,
      tw6ThetaConj Ω Fr w z = m * baseChangeGL Fr z * m⁻¹ := fun z hz => by
    have hFz : baseChangeGL Fr z ∈ subsystemGroup Tag.E6 Ω d4Support :=
      baseChangeGL_mem_subsystemGroupE6 Fr hz
    have h0 := hm₀P _ hFz
    rw [tw6ThetaConj_eq_mono w z]
    have h1 : twistE6 Ω Fr z = tw6P Ω * baseChangeGL Fr z * (tw6P Ω)⁻¹ := by
      rw [baseChangeGL_eq_entrywise]
      rfl
    rw [h1, ← h0, hmdef, hm₁def, hn, hδw]
    group
  have hPmap : ∀ z, z ∈ P.map (MulAut.conj n).toMonoidHom ↔
      (z ∈ subsystemGroup Tag.E6 Ω d4Support ∧ m * baseChangeGL Fr z * m⁻¹ = z) := by
    intro z
    constructor
    · rintro ⟨y, hy, rfl⟩
      have hz : n * y * n⁻¹ ∈ subsystemGroup Tag.E6 Ω d4Support := by
        rw [← hQ]
        exact ⟨y, hy.1, rfl⟩
      refine ⟨hz, ?_⟩
      have h1 : tw6Theta Ω Fr y = y := mem_twistedFixedPoints.1 hy.2
      have h2 := tw6ThetaConj_conj (Ω := Ω) (Fr := Fr) w y
      rw [h1, hθ_eq _ hz] at h2
      exact h2
    · rintro ⟨hz, hfix⟩
      have hzQ := hz
      rw [← hQ] at hz
      obtain ⟨y, hy, hyz⟩ := hz
      change n * y * n⁻¹ = z at hyz
      refine ⟨y, ⟨hy, mem_twistedFixedPoints.2 ?_⟩, hyz⟩
      have h2 := tw6ThetaConj_conj (Ω := Ω) (Fr := Fr) w y
      rw [hyz, hθ_eq _ hzQ, hfix] at h2
      have h3 : n * y * n⁻¹ = n * tw6Theta Ω Fr y * n⁻¹ := by rw [hyz]; exact h2
      exact (mul_left_cancel (mul_right_cancel h3)).symm
  have hconjL : P.map (MulAut.conj n).toMonoidHom =
      (d4Layer Fr e).map (MulAut.conj g⁻¹).toMonoidHom := by
    ext z
    rw [hPmap z]
    constructor
    · rintro ⟨hz, hfix⟩
      have hiff := fixed_iff_conj_mem_d4ThetaFixed (Fr := Fr) (e := e) (m := m) (g := g) hg hgconj hz
      have hmem : (⟨g * z * g⁻¹, mul_mem (mul_mem hg hz) (inv_mem hg)⟩ :
          subsystemGroup Tag.E6 Ω d4Support) ∈ d4ThetaFixed Ω Fr e := hiff.1 hfix
      refine ⟨g * z * g⁻¹, ⟨_, hmem, rfl⟩, ?_⟩
      change g⁻¹ * (g * z * g⁻¹) * g⁻¹⁻¹ = z
      group
    · rintro ⟨l, ⟨l', hl', rfl⟩, rfl⟩
      have hz : g⁻¹ * (l' : ModGL Tag.E6 Ω) * g⁻¹⁻¹ ∈ subsystemGroup Tag.E6 Ω d4Support :=
        mul_mem (mul_mem (inv_mem hg) l'.2) (by simpa using hg)
      refine ⟨hz, ?_⟩
      have hiff := fixed_iff_conj_mem_d4ThetaFixed (Fr := Fr) (e := e) (m := m) (g := g) hg hgconj hz
      refine hiff.2 ?_
      have : (⟨g * (g⁻¹ * (l' : ModGL Tag.E6 Ω) * g⁻¹⁻¹) * g⁻¹,
          mul_mem (mul_mem hg hz) (inv_mem hg)⟩ : subsystemGroup Tag.E6 Ω d4Support) = l' :=
        Subtype.ext (by group)
      rw [this]
      exact hl'
  obtain ⟨-, -, -, -, -, -, htr, -⟩ :=
    E6_finite_A2_D4_layers_detect_full_module_commutants ℓ f hℓ hf K hK Ω Fr hFr
  have hset : ∀ (A : Subgroup (ModGL Tag.E6 Ω)) (u : ModGL Tag.E6 Ω),
      ((A.map (MulAut.conj u).toMonoidHom : Subgroup (ModGL Tag.E6 Ω)) : Set (ModGL Tag.E6 Ω)) =
        (fun g => u * g * u⁻¹) '' (A : Set (ModGL Tag.E6 Ω)) := fun A u => by
    rw [Subgroup.coe_map]
    rfl
  have hQset : (fun x => g⁻¹ * x * g⁻¹⁻¹) ''
      (subsystemGroup Tag.E6 Ω d4Support : Set (ModGL Tag.E6 Ω)) =
      (subsystemGroup Tag.E6 Ω d4Support : Set (ModGL Tag.E6 Ω)) := by
    ext y
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact mul_mem (mul_mem (inv_mem hg) hu) (by simpa using hg)
    · intro hy
      exact ⟨g * y * g⁻¹, mul_mem (mul_mem hg hy) (inv_mem hg), by group⟩
  have hcomm : e6Commutant (((P.map (MulAut.conj n).toMonoidHom : Subgroup (ModGL Tag.E6 Ω)) :
      Set (ModGL Tag.E6 Ω))) =
      e6Commutant (subsystemGroup Tag.E6 Ω d4Support : Set (ModGL Tag.E6 Ω)) := by
    rw [hconjL, hset, (htr g⁻¹).2.2.1 e he, hQset]
  have hk₃ := natCard_cubicSubfield (Ω := Ω) (ℓ := ℓ) hf
  have : IsAlgClosure (cubicSubfield (Ω := Ω) ℓ f) Ω :=
    ⟨inferInstance, isAlgebraic_cubicSubfield hK⟩
  have : CharP (cubicSubfield (Ω := Ω) ℓ f) ℓ := inferInstance
  let σ : cubicSubfield (Ω := Ω) ℓ f →+* cubicSubfield (Ω := Ω) ℓ f :=
    iterateFrobenius (cubicSubfield (Ω := Ω) ℓ f) ℓ (f * e)
  have hσ : ∀ c, σ c = c ^ ((ℓ ^ f) ^ e) := fun c => by
    rw [iterateFrobenius_def, pow_mul]
  obtain ⟨φ, -⟩ := exists_d4ThetaFixed_equiv (K := cubicSubfield (Ω := Ω) ℓ f) hℓ hf hk₃ he hσ hFr
  obtain ⟨-, -, -, hsimple, hnc⟩ :=
    triality_both_field_orientations_simple_full_ambient_fixed_group ℓ f hℓ hf
      (cubicSubfield (Ω := Ω) ℓ f) hk₃ Ω e he σ hσ Fr hFr
  have hfinK₃ : Finite (cubicSubfield (Ω := Ω) ℓ f) :=
    Nat.finite_of_card_ne_zero (by rw [hk₃]; exact pow_ne_zero _ (pow_ne_zero _ hℓ.ne_zero))
  have : Finite (ModGL TwistTag.D4.tag (cubicSubfield (Ω := Ω) ℓ f)) := finite_modGL
  have : Finite ↥(graphFixedRootGroup TwistTag.D4 (cubicSubfield (Ω := Ω) ℓ f) σ) := inferInstance
  have hqsΘ : CFSG.IsQuasisimple ↥(d4ThetaFixed Ω Fr e) :=
    CFSG.LieType.Universal.Unitary.isQuasisimple_of_mulEquiv φ.symm
      (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hnc).1
  have hequiv : ↥P ≃* ↥(d4ThetaFixed Ω Fr e) :=
    (((Subgroup.equivMapOfInjective P (MulAut.conj n).toMonoidHom
        (MulAut.conj n).injective).trans (MulEquiv.subgroupCongr hconjL)).trans
      (Subgroup.equivMapOfInjective (d4Layer Fr e) (MulAut.conj g⁻¹).toMonoidHom
        (MulAut.conj g⁻¹).injective).symm).trans
      (Subgroup.equivMapOfInjective (d4ThetaFixed Ω Fr e)
        (subsystemGroup Tag.E6 Ω d4Support).subtype (Subgroup.subtype_injective _)).symm
  have hfinP : Finite ↥P := by
    have : Finite ↥(d4ThetaFixed Ω Fr e) := Finite.of_equiv _ φ.symm.toEquiv
    exact Finite.of_equiv _ hequiv.symm.toEquiv
  have hqsP : CFSG.IsQuasisimple ↥P :=
    CFSG.LieType.Universal.Unitary.isQuasisimple_of_mulEquiv hequiv.symm hqsΘ
  refine ⟨hQ, hfinP, hqsP, hcomm, ⟨n⁻¹ * g⁻¹, fun B => ?_⟩, e, g, he, hconjL, ⟨hequiv⟩⟩
  have hι : ∀ b : K, algebraMap K Ω b ^ (ℓ ^ f) = algebraMap K Ω b := fun b => by
    rw [← map_pow]
    congr 1
    rw [← hK, Nat.card_eq_fintype_card, FiniteField.pow_card]
  have hB := simpleRootSL2_mem_d4Layer (Fr := Fr) hFr he (algebraMap K Ω) hι B
  have hmem : g⁻¹ * simpleRootSL2 Tag.E6 Ω (d4Idx 2)
      (Matrix.SpecialLinearGroup.map (algebraMap K Ω) B) * g⁻¹⁻¹ ∈
        P.map (MulAut.conj n).toMonoidHom := by
    rw [hconjL]
    exact ⟨_, hB, rfl⟩
  obtain ⟨y, hy, hyeq⟩ := hmem
  have hyeq' : n * y * n⁻¹ = g⁻¹ * simpleRootSL2 Tag.E6 Ω (d4Idx 2)
      (Matrix.SpecialLinearGroup.map (algebraMap K Ω) B) * g⁻¹⁻¹ := hyeq
  have this : n⁻¹ * g⁻¹ * simpleRootSL2 Tag.E6 Ω (d4Idx 2)
      (Matrix.SpecialLinearGroup.map (algebraMap K Ω) B) * (n⁻¹ * g⁻¹)⁻¹ = y := by
    have h3 : y = n⁻¹ * (n * y * n⁻¹) * n := by group
    rw [h3, hyeq']
    group
  rw [this]
  exact hy

end CFSG.HardMathSupport.Lang.SeitzPlane
