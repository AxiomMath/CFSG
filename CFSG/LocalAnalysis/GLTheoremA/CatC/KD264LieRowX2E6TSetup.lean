module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowX2E6LMain
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowX2E6LCent
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.TorusAtTwE6
public import CFSG.LieType.SeitzGeneration.ExcTorusTwE6Three
public import CFSG.LieType.SeitzGeneration.ExcTorusTwE6Four
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerBridge
public import CFSG.Sporadic.Schreier.J4SProfileNode
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.AlgSetupUntw
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.PlanesSetup
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.FrobeniusOnRoots
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerFivePairRigid
public import CFSG.HardMathSupport.Lang.E6Descent.OuterFixed27TwistedE6Normalizer
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQThreeTwE6TwoModel
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerSylow
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.BigAnyDefs
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.CentralizerTrivialPoly
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.ComponentsExc
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.RigidAssembly
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.RigidField
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.RigidNorm
public import CFSG.LocalAnalysis.GLTheoremA.S10.Bridge
public import CFSG.LocalAnalysis.GLTheoremA.S10.Inputs105
public import CFSG.LocalAnalysis.GLTheoremA.S10.InputsBeta
public import CFSG.LocalAnalysis.GLTheoremA.S11.Defs
public import CFSG.LocalAnalysis.GLTheoremA.S3.Inputs
public import CFSG.LocalAnalysis.GLTheoremA.S9.Inputs
public import CFSG.LocalAnalysis.GLTheoremA.Sec5Setup
public import CFSG.RankThree.Chevalley.SteinbergBID4CentralKernel
public import CFSG.RankThree.PartOne.KE.E8D4Family

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie.X2E6.T

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.HardMathSupport.Lang.E6Descent
open CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
open CFSG.StandardType CFSG.StandardType.NoOffTwE6Three
open CFSG.RankThree.Classical2 (twistE6)
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

section Setup

variable {K : Type} [Field K] [Finite K] {Ω : Type} [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]

@[expose] noncomputable def modelDatum (Fr : Ω →+* Ω) (hFr : ∀ c, Fr c = c ^ 2 ^ 1)
    {g : ModGL Tag.E6 Ω} (hg : g ∈ adjointGroup Tag.E6 Ω)
    (hgn : g⁻¹ * twistE6 Ω Fr g = TwistedDiag.n0 Ω) : LangDatum Tag.E6 Ω :=
  LangDatum.ofTwist TwistTag.E6 Fr (2 ^ 1) hFr twE6W0 hg (by
    have h : twistE6 Ω Fr g = g * TwistedDiag.n0 Ω := by
      rw [← hgn, mul_inv_cancel_left]
    exact h)

@[expose] noncomputable def modelEmb (K : Type) [Field K] (σ : K ≃+* K) (Ω : Type) [Field Ω]
    [Algebra K Ω] : twistedE6RootGroup K σ →* ModGL Tag.E6 Ω :=
  (baseChangeGL (algebraMap K Ω)).comp (twistedE6RootGroup K σ).subtype

theorem modelEmb_injective (σ : K ≃+* K) : Function.Injective (modelEmb K σ Ω) :=
  (baseChangeGL_injective _).comp (Subgroup.subtype_injective _)

theorem modelDescent (hK : Nat.card K = (2 ^ 1) ^ 2) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ 2 ^ 1)
    (Fr : Ω →+* Ω) (hFr : ∀ c, Fr c = c ^ 2 ^ 1) {g : ModGL Tag.E6 Ω}
    (hg : g ∈ adjointGroup Tag.E6 Ω) (hgn : g⁻¹ * twistE6 Ω Fr g = TwistedDiag.n0 Ω) :
    LangDescent (modelDatum Fr hFr hg hgn) 5 (modelEmb K σ Ω) :=
  langDescent_twE6 (K := K) (L := Ω) (ℓ := 2) (f := 1) Nat.prime_two le_rfl hK σ hσ hFr
    (modelDatum Fr hFr hg hgn) rfl (by norm_num) (by norm_num)

theorem charP_two_of_card (hK : Nat.card K = (2 ^ 1) ^ 2) : CharP Ω 2 := by
  haveI : Fintype K := Fintype.ofFinite K
  haveI hcharK : CharP K 2 := charP_of_card_eq_prime_pow (p := 2) (f := 2)
    (by rw [← Nat.card_eq_fintype_card, hK]; norm_num)
  exact charP_of_injective_algebraMap (algebraMap K Ω).injective 2

theorem exists_modelSetup [IsAlgClosed Ω] (hK : Nat.card K = (2 ^ 1) ^ 2) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ 2 ^ 1) (Fr : Ω →+* Ω) (hFr : ∀ c, Fr c = c ^ 2 ^ 1)
    {g : ModGL Tag.E6 Ω} (hg : g ∈ adjointGroup Tag.E6 Ω)
    (hgn : g⁻¹ * twistE6 Ω Fr g = TwistedDiag.n0 Ω) :
    ∃ S : LangSetup Tag.E6 Ω 5, S.D = modelDatum Fr hFr hg hgn := by
  haveI := charP_two_of_card (K := K) (Ω := Ω) hK
  have hq2 : (2 ^ 1 : ℕ) = 2 := by norm_num
  have hqpow : IsPrimePow (modelDatum Fr hFr hg hgn).q ∧
      (((modelDatum Fr hFr hg hgn).q : ℕ) : Ω) = 0 := by
    refine ⟨?_, ?_⟩
    · show IsPrimePow (2 ^ 1)
      rw [hq2]
      exact Nat.prime_two.isPrimePow
    · show (((2 ^ 1 : ℕ)) : Ω) = 0
      rw [hq2]
      exact CharP.cast_eq_zero Ω 2
  obtain ⟨S, hSD, -⟩ := exists_langSetup_of_descent_nosylow frobeniusOnRoots_proved
    (modelDatum Fr hFr hg hgn) (p := 5) (by norm_num) (Or.inl le_rfl) hqpow
    (by show ¬ 5 ∣ 2 ^ 1; norm_num) (modelEmb K σ Ω) (modelEmb_injective σ)
    (modelDescent hK σ hσ Fr hFr hg hgn)
  exact ⟨S, hSD⟩

theorem rho_eq_neg [IsAlgClosed Ω] (hq : (0 : ℕ) < 2 ^ 1) (Fr : Ω →+* Ω)
    (hFr : ∀ c, Fr c = c ^ 2 ^ 1)
    {g : ModGL Tag.E6 Ω} (hg : g ∈ adjointGroup Tag.E6 Ω)
    (hgn : g⁻¹ * twistE6 Ω Fr g = TwistedDiag.n0 Ω)
    {S : LangSetup Tag.E6 Ω 5} (hSD : S.D = modelDatum Fr hFr hg hgn)
    {γ : Fin Tag.E6.rank → ℤ} (hγ : IsRoot Tag.E6 γ) : S.ρ γ = -γ := by
  have hg0 := (modelDatum Fr hFr hg hgn).lang
  have hFD : FrobRootMap (LangDatum.ofTwist TwistTag.E6 Fr (2 ^ 1) hFr twE6W0 hg hg0) S.ρ := by
    have := S.frob
    rw [hSD] at this
    exact this
  exact (frobRootMap_ofTwist_apply hq hFr hg hg0 hFD hγ).trans
    (CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQ3.twE6W0_smul_permLattice γ)

theorem psi6_mem_torus [IsAlgClosed Ω] (Fr : Ω →+* Ω) (hFr : ∀ c, Fr c = c ^ 2 ^ 1)
    {g : ModGL Tag.E6 Ω} (hg : g ∈ adjointGroup Tag.E6 Ω)
    (hgn : g⁻¹ * twistE6 Ω Fr g = TwistedDiag.n0 Ω) {ζ : Ωˣ} (hζ : ζ ^ 3 = 1)
    (u : Multiplicative (Fin 6 → ZMod 3)) :
    Psi6 hζ u ∈ (modelDatum Fr hFr hg hgn).torus := by
  have hmem : Psi6 hζ u ∈ torusGroup Tag.E6 Ω := by
    rw [Psi6_apply]
    exact rootDiagUnit_mem_torusGroup _
  refine CFSG.RankThree.PartOne.KE.mem_twistedTorusOf.2 ⟨hmem, ?_⟩
  have h1 : TwistedDiag.theta Fr (Psi6 hζ u) = Psi6 hζ u := by
    rw [Psi6_apply]
    refine (TwistedDiag.theta_rootDiagUnit_eq_iff Fr hFr _).2 fun i => ?_
    have h3 : DiagTorus.theta ζ (Multiplicative.toAdd u i) ^ 3 = 1 := by
      unfold DiagTorus.theta
      rw [← pow_mul, mul_comm, pow_mul, hζ, one_pow]
    simpa using h3
  have h2 := TwistedDiag.theta_apply Fr (Psi6 hζ u)
  rw [h1] at h2
  exact h2.symm

@[expose] noncomputable def modelPhi (σ : K ≃+* K) (g : ModGL Tag.E6 Ω) :
    twistedE6RootGroup K σ →* ModGL Tag.E6 Ω :=
  (MulAut.conj g⁻¹).toMonoidHom.comp (modelEmb K σ Ω)

theorem modelPhi_apply (σ : K ≃+* K) (g : ModGL Tag.E6 Ω) (c : twistedE6RootGroup K σ) :
    modelPhi σ g c = g⁻¹ * modelEmb K σ Ω c * g := by
  simp [modelPhi, MulAut.conj_apply]

theorem modelPhi_injective (σ : K ≃+* K) (g : ModGL Tag.E6 Ω) :
    Function.Injective (modelPhi (K := K) (Ω := Ω) σ g) :=
  (MulAut.conj g⁻¹).injective.comp (modelEmb_injective σ)

theorem range_modelPhi (hK : Nat.card K = (2 ^ 1) ^ 2) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ 2 ^ 1) (Fr : Ω →+* Ω) (hFr : ∀ c, Fr c = c ^ 2 ^ 1)
    {g : ModGL Tag.E6 Ω} (hg : g ∈ adjointGroup Tag.E6 Ω)
    (hgn : g⁻¹ * twistE6 Ω Fr g = TwistedDiag.n0 Ω) :
    (modelPhi σ g).range = (modelDatum Fr hFr hg hgn).Γ := by
  have h := (modelDescent hK σ hσ Fr hFr hg hgn).Γ_eq
  rw [h, ← MonoidHom.range_comp] at *
  rfl

theorem iInf_fixSubgroup_eq_comap [IsAlgClosed Ω] (hK : Nat.card K = (2 ^ 1) ^ 2) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ 2 ^ 1) (Fr : Ω →+* Ω) (hFr : ∀ c, Fr c = c ^ 2 ^ 1)
    {g : ModGL Tag.E6 Ω} (hg : g ∈ adjointGroup Tag.E6 Ω)
    (hgn : g⁻¹ * twistE6 Ω Fr g = TwistedDiag.n0 Ω) {ζ : Ωˣ} (hζ : ζ ^ 3 = 1)
    (G : Subgroup (Multiplicative (Fin 6 → ZMod 3))) :
    (⨅ f ∈ G.map (torusAut hK σ hσ Fr hFr hg hgn hζ),
        CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup f) =
      (Subgroup.centralizer ((Psi6 hζ : Multiplicative (Fin 6 → ZMod 3) →* ModGL Tag.E6 Ω) ''
        (G : Set (Multiplicative (Fin 6 → ZMod 3))))).comap (modelPhi σ g) := by
  ext c
  rw [mem_iInf_fixSubgroup_torusAut_iff hK σ hσ Fr hFr hg hgn hζ G c, Subgroup.mem_comap,
    Subgroup.mem_centralizer_iff]
  constructor
  · rintro h _ ⟨u, hu, rfl⟩
    have h1 : (g * Psi6 hζ u * g⁻¹) * modelEmb K σ Ω c =
        modelEmb K σ Ω c * (g * Psi6 hζ u * g⁻¹) := h u hu
    rw [modelPhi_apply]
    calc Psi6 hζ u * (g⁻¹ * modelEmb K σ Ω c * g)
        = g⁻¹ * ((g * Psi6 hζ u * g⁻¹) * modelEmb K σ Ω c) * g := by group
      _ = g⁻¹ * (modelEmb K σ Ω c * (g * Psi6 hζ u * g⁻¹)) * g := by rw [h1]
      _ = _ := by group
  · intro h u hu
    have h1 := h _ ⟨u, hu, rfl⟩
    rw [modelPhi_apply] at h1
    have h2 : (g * Psi6 hζ u * g⁻¹) * modelEmb K σ Ω c =
        modelEmb K σ Ω c * (g * Psi6 hζ u * g⁻¹) := by
      calc (g * Psi6 hζ u * g⁻¹) * modelEmb K σ Ω c
          = g * (Psi6 hζ u * (g⁻¹ * modelEmb K σ Ω c * g)) * g⁻¹ := by group
        _ = g * (g⁻¹ * modelEmb K σ Ω c * g * Psi6 hζ u) * g⁻¹ := by rw [h1]
        _ = _ := by group
    exact h2

theorem natCard_quotCenter_eq {A B : Type*} [Group A] [Group B] (e : A ≃* B) :
    Nat.card (A ⧸ Subgroup.center A) = Nat.card (B ⧸ Subgroup.center B) :=
  Nat.card_congr (QuotientGroup.congr (Subgroup.center A) (Subgroup.center B) e
    (Subgroup.map_center_eq e)).toEquiv

@[expose] noncomputable def jgEquiv {A B : Type*} [Group A] [Group B] (J : Subgroup B)
    (φ : A →* B) (hφ : Function.Injective φ) (hJ : J ≤ φ.range) : ↥(J.comap φ) ≃* ↥J :=
  (Subgroup.equivMapOfInjective (J.comap φ) φ hφ).trans
    (MulEquiv.subgroupCongr (Subgroup.map_comap_eq_self hJ))

theorem exists_component_of_lang [IsAlgClosed Ω] (hK : Nat.card K = (2 ^ 1) ^ 2) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ 2 ^ 1) (Fr : Ω →+* Ω) (hFr : ∀ c, Fr c = c ^ 2 ^ 1)
    {g : ModGL Tag.E6 Ω} (hg : g ∈ adjointGroup Tag.E6 Ω)
    (hgn : g⁻¹ * twistE6 Ω Fr g = TwistedDiag.n0 Ω) {ζ : Ωˣ} (hζ : ζ ^ 3 = 1)
    (G : Subgroup (Multiplicative (Fin 6 → ZMod 3))) (Jg : Subgroup (ModGL Tag.E6 Ω))
    (hJ : CFSG.Open.IsSubnormal Jg ((modelDatum Fr hFr hg hgn).Γ ⊓
      Subgroup.centralizer ((Psi6 hζ : Multiplicative (Fin 6 → ZMod 3) →* ModGL Tag.E6 Ω) ''
        (G : Set (Multiplicative (Fin 6 → ZMod 3))))))
    (hq : CFSG.Open.IsQuasisimple ↥Jg)
    (h3 : 3 ∣ Nat.card (↥Jg ⧸ Subgroup.center ↥Jg)) :
    ∃ J : Subgroup (twistedE6RootGroup K σ),
      CFSG.Open.IsSubnormal J (⨅ f ∈ G.map (torusAut hK σ hσ Fr hFr hg hgn hζ),
        CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup f) ∧
      CFSG.Open.IsQuasisimple ↥J ∧ 3 ∣ Nat.card (↥J ⧸ Subgroup.center ↥J) := by
  set φ := modelPhi (K := K) (Ω := Ω) σ g with hφ
  have hinj : Function.Injective φ := modelPhi_injective σ g
  have hrange : φ.range = (modelDatum Fr hFr hg hgn).Γ := range_modelPhi hK σ hσ Fr hFr hg hgn
  have hJle : Jg ≤ φ.range := by
    rw [hrange]
    exact (hJ.le).trans inf_le_left
  refine ⟨Jg.comap φ, ?_, ?_, ?_⟩
  · have h1 := hJ.comap φ
    have h2 : ((modelDatum Fr hFr hg hgn).Γ ⊓
        Subgroup.centralizer ((Psi6 hζ : Multiplicative (Fin 6 → ZMod 3) →* ModGL Tag.E6 Ω) ''
          (G : Set (Multiplicative (Fin 6 → ZMod 3))))).comap φ =
        ⨅ f ∈ G.map (torusAut hK σ hσ Fr hFr hg hgn hζ),
          CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup f := by
      rw [Subgroup.comap_inf, iInf_fixSubgroup_eq_comap hK σ hσ Fr hFr hg hgn hζ G]
      have : ((modelDatum Fr hFr hg hgn).Γ).comap φ = ⊤ := by
        rw [← hrange]
        exact eq_top_iff.2 fun c _ => Subgroup.mem_comap.2 ⟨c, rfl⟩
      rw [this, top_inf_eq]
    rwa [h2] at h1
  · exact (CFSG.Open.IsQuasisimple.congr (jgEquiv Jg φ hinj hJle)).2 hq
  · rw [natCard_quotCenter_eq (jgEquiv Jg φ hinj hJle)]
    exact h3

end Setup

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie.X2E6.T

end
