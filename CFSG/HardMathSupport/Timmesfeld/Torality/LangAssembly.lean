module

public import CFSG.HardMathSupport.Timmesfeld.Torality.FamilyBruhat
public import CFSG.HardMathSupport.Timmesfeld.Torality.Conjugacy
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.BadThreeLang
public import CFSG.LieType.AlgebraicGroups.ConnectedToralLangFrobenius
public import CFSG.LieType.AlgebraicGroups.ToralTwistPinningFrobenius
import CFSG.LieType.AlgebraicGroups.ConvolutionPoints
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerResiduals
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.Reduction
public import CFSG.HardMathSupport.Timmesfeld.Torality.FamilyCover
public import CFSG.LieType.Chevalley.EvenTrialityOuterInvolutions
public import CFSG.LieType.Chevalley.OddTrialityCosetInvolutions
public import CFSG.LieType.SeitzGeneration.ExtSeitzReeF4Cyclic
public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsCentModel
public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsFieldAut
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueUStatement
public import CFSG.LocalAnalysis.ComponentClassification.GSLitType
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpExclusion
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrCentralSylowMaximality
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedGSAContainedSource
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedLayerOddCoreUnbalancingTriple
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherEvenOrthogonalModel
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.TypeB2
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.Unitary
public import CFSG.RankThree.CentralLiftSO.SplitTorusWeyl
public import CFSG.RankThree.Classical.SteinbergBJSymplecticSquareZeroCentralizer
public import CFSG.RankThree.PartOne.BRANCH.RankRee
public import CFSG.RankThree.PartOne.CTP.StrongPBridgeRest
public import CFSG.RankThree.PartOne.KC.LinearCommutatorOdd
public import CFSG.RankThree.PartOne.KC.LinearDegreeFive
public import CFSG.RankThree.PartOne.KC.OrthogonalD4WitnessEven
public import CFSG.RankThree.PartOne.KC.OrthogonalD4WitnessOdd
public import CFSG.RankThree.PartOne.KC.UnitaryHigherCrossPrimeTorus
public import CFSG.RankThree.PartOne.KC.UnitaryPlaneEndpoints
public import CFSG.RankThree.PartOne.KD4T.Certs
public import CFSG.RankThree.PartOne.KE.StabGeneral
public import CFSG.RankThree.PartOne.N143.Weyl613Defs
public import CFSG.RankThree.PartOne.N143X.KF64WSimple
public import CFSG.RankThree.PartOne.S11d.OutExceptional
public import CFSG.RankThree.PartOne.S11d.OutLinear
public import CFSG.RankThree.PartTwo.KFacts.KS14SzLie
public import CFSG.RankThree.PartTwo.Sec4.Census.Interface
public import CFSG.RankThree.SteinbergR3EOrthogonalCoprimeCyclic
public import CFSG.SignalizerFunctorTheorem.Nonsolvable.SolComponent
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_3_3
public import Certificates.Certificate1
public import Certificates.Certificate2

public noncomputable section

namespace CFSG.HardMathSupport.Timmesfeld.Torality

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.RankThree.PartOne.KE WithConv CFSG.HardMathSupport.Timmesfeld.CrossChar

open scoped CFSG.ConvolutionPoints

set_option linter.unusedSectionVars false

theorem exists_mem_lang_conj {Γ : Type*} [Group Γ] (F : Γ →* Γ) {M : Subgroup Γ} {Q g m : Γ}
    (hm : m ∈ M) (hn : g⁻¹ * F g = m * Q)
    (hLang : ∀ c ∈ M, ∃ z ∈ M, z⁻¹ * (Q * F z * Q⁻¹) = c) :
    ∃ z ∈ M, (g * z)⁻¹ * F (g * z) = Q := by
  obtain ⟨z, hz, hzc⟩ := hLang m hm
  refine ⟨z⁻¹, M.inv_mem hz, ?_⟩
  have h1 : Q * F z * Q⁻¹ = z * m := by
    calc Q * F z * Q⁻¹ = z * (z⁻¹ * (Q * F z * Q⁻¹)) := by group
      _ = z * m := by rw [hzc]
  have h2 : Q * (F z)⁻¹ * Q⁻¹ = (z * m)⁻¹ := by
    rw [← h1]
    group
  calc (g * z⁻¹)⁻¹ * F (g * z⁻¹) = z * (g⁻¹ * F g) * (F z)⁻¹ := by
        simp only [map_mul, map_inv, mul_inv_rev, inv_inv, mul_assoc]
    _ = z * (m * Q) * (F z)⁻¹ := by rw [hn]
    _ = z * m * (Q * (F z)⁻¹ * Q⁻¹) * Q := by group
    _ = Q := by rw [h2]; group

section Concrete


variable {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] (ℓ : ℕ) [Fact ℓ.Prime] [CharP L ℓ]
  {ι : Type} (a : ι → Fin τ.rank → Lˣ)

theorem entrywiseFrobGL_mem_familyGroup (e : ℕ) {g : ModGL τ L}
    (hg : g ∈ familyGroup (K := L) a) : entrywiseFrobGL τ L ℓ e g ∈ familyGroup (K := L) a := by
  have hmap : (familyGroup (K := L) a).map (entrywiseFrobGL τ L ℓ e) ≤ familyGroup a := by
    rw [familyGroup, Subgroup.map_sup]
    refine sup_le ?_ ?_
    · rintro _ ⟨h, hh, rfl⟩
      obtain ⟨l, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hh
      rw [entrywiseFrobGL_rootDiagUnit_eq_map]
      exact Subgroup.mem_sup_left (rootDiagUnit_mem_torusGroup _)
    · rw [rootSpan, Subgroup.map_iSup]
      refine iSup_le fun α => ?_
      rw [Subgroup.map_iSup]
      refine iSup_le fun hα => ?_
      rw [rootSubgroup, MonoidHom.map_closure, Subgroup.closure_le]
      rintro _ ⟨_, ⟨c, rfl⟩, rfl⟩
      exact Subgroup.mem_sup_right (le_iSup₂_of_le (f := fun β (_ : β ∈ familyKernel a) =>
        rootSubgroup τ L β) α hα le_rfl (Subgroup.subset_closure
          ⟨iterateFrobenius L ℓ e c, (entrywiseFrobGL_pinnedX ℓ e α c).symm⟩))
  exact hmap ⟨g, hg, rfl⟩

theorem lang_familyGroup (e : ℕ) (he : 1 ≤ e) (Q : ModGL τ L)
    (hQ : Q ∈ Subgroup.normalizer (familyGroup (K := L) a : Set (ModGL τ L))) :
    ∀ c ∈ familyGroup (K := L) a, ∃ z ∈ familyGroup (K := L) a,
      z⁻¹ * (Q * entrywiseFrobGL τ L ℓ e z * Q⁻¹) = c := by
  have hZ : IsConnectedAlgebraicSubgroup L
      ((familyGroup (K := L) a).map (modGLPoint τ L).toMonoidHom) := by
    have := isConnectedAlgebraicSubgroup_torus_sup_rootSpan_kernelRoots (τ := τ) (k := L)
      (familyChar a)
    rwa [kernelRoots_familyChar] at this
  have hst : ∀ g ∈ familyGroup (K := L) a, frobTwistGL τ L ℓ e Q g ∈ familyGroup (K := L) a :=
    fun g hg => by
      rw [frobTwistGL_apply]
      exact (Subgroup.mem_normalizer_iff.1 hQ _).1 (entrywiseFrobGL_mem_familyGroup ℓ a e hg)
  obtain ⟨-, -, -, hlang⟩ := exists_frobTwist_restriction ℓ hZ he Q hst
  intro c hc
  obtain ⟨z, hz, hzc⟩ := hlang c hc
  exact ⟨z, hz, by rw [frobTwistGL_apply] at hzc; exact hzc⟩

theorem rootChar_pow' (b : Fin τ.rank → Lˣ) (n : ℕ) (v : Fin τ.rank → ℤ) :
    rootChar (b ^ n) v = rootChar b v ^ n := by
  simp only [rootChar, Pi.pow_apply, ← Finset.prod_pow]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, mul_comm]

theorem rootChar_pow_eq_one {p : ℕ} (b : Fin τ.rank → Lˣ) (hb : ∀ i, b i ^ p = 1)
    (v : Fin τ.rank → ℤ) : rootChar b v ^ p = 1 := by
  rw [← rootChar_pow']
  have : b ^ p = 1 := funext hb
  rw [this]
  simp [rootChar]

theorem entrywiseFrobGL_rootDiagUnit_eq_pow (e : ℕ) (b : Fin τ.rank → Lˣ) :
    entrywiseFrobGL τ L ℓ e (rootDiagUnit τ b) = rootDiagUnit τ (b ^ ℓ ^ e) := by
  rw [entrywiseFrobGL_rootDiagUnit_eq_map]
  congr 1

theorem rootDiagUnit_eq_conj_frob {e : ℕ} {b : Fin τ.rank → Lˣ} {w : WeylGroup τ}
    (hw : ∀ v, rootChar b (w • v) = rootChar b v ^ ℓ ^ e) :
    rootDiagUnit τ b = canonicalRep (coxeterSystem τ) L w *
      entrywiseFrobGL τ L ℓ e (rootDiagUnit τ b) * (canonicalRep (coxeterSystem τ) L w)⁻¹ := by
  rw [entrywiseFrobGL_rootDiagUnit_eq_pow, rootDiagUnit_eq_conj_canonicalRep_iff]
  intro v
  rw [hw, rootChar_pow']

theorem image_familyKernel_of_pow {e p : ℕ} (hpq : Nat.Coprime p (ℓ ^ e))
    (a : ι → Fin τ.rank → Lˣ) (hexp : ∀ s i, a s i ^ p = 1) {w : WeylGroup τ}
    (hw : ∀ s v, rootChar (a s) (w • v) = rootChar (a s) v ^ ℓ ^ e) :
    (fun α => w • α) '' familyKernel a = familyKernel a := by
  have key : ∀ x : Lˣ, x ^ p = 1 → x ^ ℓ ^ e = 1 → x = 1 := fun x h1 h2 => by
    have h := Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h1) (orderOf_dvd_of_pow_eq_one h2)
    rw [hpq] at h
    exact orderOf_eq_one_iff.1 (Nat.dvd_one.1 h)
  ext β
  constructor
  · rintro ⟨α, ⟨hα, hχ⟩, rfl⟩
    refine ⟨IsRoot.smul hα w, fun s => ?_⟩
    rw [hw, hχ s, one_pow]
  · rintro ⟨hβ, hχ⟩
    refine ⟨w⁻¹ • β, ⟨IsRoot.smul hβ w⁻¹, fun s => ?_⟩, smul_inv_smul w β⟩
    have h := hw s (w⁻¹ • β)
    rw [smul_inv_smul, hχ s] at h
    exact key _ (rootChar_pow_eq_one (a s) (hexp s) _) h.symm

theorem exists_lang_datum_of_plane (e : ℕ) (he : 1 ≤ e) {p : ℕ}
    (hpq : Nat.Coprime p (ℓ ^ e)) (a : ι → Fin τ.rank → Lˣ) (hexp : ∀ s i, a s i ^ p = 1)
    {g : ModGL τ L} (hg : g ∈ adjointGroup τ L)
    (hn : ∀ s, (g⁻¹ * entrywiseFrobGL τ L ℓ e g) * entrywiseFrobGL τ L ℓ e (rootDiagUnit τ (a s)) *
      (g⁻¹ * entrywiseFrobGL τ L ℓ e g)⁻¹ = rootDiagUnit τ (a s)) :
    ∃ (w' : WeylGroup τ) (z : ModGL τ L), z ∈ familyGroup (K := L) a ∧
      (g * z)⁻¹ * entrywiseFrobGL τ L ℓ e (g * z) = canonicalRep (coxeterSystem τ) L w' := by
  have hnG0 : g⁻¹ * entrywiseFrobGL τ L ℓ e g ∈ adjointGroup τ L :=
    mul_mem (inv_mem hg) (entrywiseFrobGL_mem ℓ e hg)
  obtain ⟨w, hwconj⟩ := exists_weyl_of_conj_family τ L a (fun s => a s ^ ℓ ^ e) hnG0 (fun s => by
    rw [← entrywiseFrobGL_rootDiagUnit_eq_pow]
    exact hn s)
  have hw : ∀ s v, rootChar (a s) (w • v) = rootChar (a s) v ^ ℓ ^ e := by
    intro s v
    have := (rootDiagUnit_eq_conj_canonicalRep_iff (K := L) (a s) (a s ^ ℓ ^ e) w).1 (hwconj s) v
    rw [this, rootChar_pow']
  obtain ⟨F, hF⟩ : ∃ F : ModGL τ L →* ModGL τ L, F = entrywiseFrobGL τ L ℓ e := ⟨_, rfl⟩
  obtain ⟨nw, hnw⟩ : ∃ nw : ModGL τ L, nw = canonicalRep (coxeterSystem τ) L w := ⟨_, rfl⟩
  rw [← hF] at hn ⊢
  have hnG : g⁻¹ * F g ∈ adjointGroup τ L :=
    mul_mem (inv_mem hg) (hF ▸ entrywiseFrobGL_mem ℓ e hg)
  have hnwG : nw ∈ adjointGroup τ L := hnw ▸ canonicalRep_mem_adjointGroup _ L w
  have hc : (g⁻¹ * F g) * nw⁻¹ ∈ familyCentralizer τ L a := by
    refine mem_familyCentralizer.2 ⟨mul_mem hnG (inv_mem hnwG), fun s => ?_⟩
    have h1 := rootDiagUnit_eq_conj_frob ℓ (hw s)
    rw [← hnw, ← hF] at h1
    have h2 : nw⁻¹ * rootDiagUnit τ (a s) * nw = F (rootDiagUnit τ (a s)) := by
      calc nw⁻¹ * rootDiagUnit τ (a s) * nw
          = nw⁻¹ * (nw * F (rootDiagUnit τ (a s)) * nw⁻¹) * nw := by rw [← h1]
        _ = F (rootDiagUnit τ (a s)) := by group
    have h3 : ((g⁻¹ * F g) * nw⁻¹) * rootDiagUnit τ (a s) * ((g⁻¹ * F g) * nw⁻¹)⁻¹ =
        rootDiagUnit τ (a s) := by
      calc ((g⁻¹ * F g) * nw⁻¹) * rootDiagUnit τ (a s) * ((g⁻¹ * F g) * nw⁻¹)⁻¹
          = (g⁻¹ * F g) * (nw⁻¹ * rootDiagUnit τ (a s) * nw) * (g⁻¹ * F g)⁻¹ := by group
        _ = rootDiagUnit τ (a s) := by rw [h2]; exact hn s
    rw [mul_inv_eq_iff_eq_mul]
    rw [mul_inv_eq_iff_eq_mul] at h3
    exact h3.symm
  obtain ⟨w₁, hw₁, m, hm, hcm⟩ := familyCentralizer_le_mul τ L a hc
  obtain ⟨k, hk, hkk⟩ := canonicalRep_mul_mem (R := L) w₁ w
  have hkM : k ∈ familyGroup (K := L) a := Subgroup.mem_sup_left hk
  have hn' : g⁻¹ * F g = (m * k) * canonicalRep (coxeterSystem τ) L (w₁ * w) := by
    have : g⁻¹ * F g = (g⁻¹ * F g) * nw⁻¹ * nw := by group
    rw [this, hcm, mul_assoc m, hnw, hkk]
    group
  have himg := image_familyKernel_of_pow ℓ hpq a hexp hw
  have hQ : canonicalRep (coxeterSystem τ) L (w₁ * w) ∈
      Subgroup.normalizer (familyGroup (K := L) a : Set (ModGL τ L)) := by
    have h1 : canonicalRep (coxeterSystem τ) L (w₁ * w) =
        k⁻¹ * (canonicalRep (coxeterSystem τ) L w₁ * canonicalRep (coxeterSystem τ) L w) := by
      rw [hkk]
      group
    rw [h1]
    exact mul_mem (inv_mem (Subgroup.le_normalizer hkM))
      (mul_mem (canonicalRep_mem_normalizer_familyGroup hw₁)
        (canonicalRep_mem_normalizer_of_image himg))
  obtain ⟨z, hz, hzF⟩ := exists_mem_lang_conj F (M := familyGroup (K := L) a)
    (mul_mem hm hkM) hn' (by rw [hF]; exact lang_familyGroup ℓ a e he _ hQ)
  exact ⟨w₁ * w, z, hz, hzF⟩

end Concrete

section Final


@[expose] def PlanesToralBar (τ : Tag) (p : ℕ) : Prop :=
  ∀ (K : Type) [Field K] [Finite K], ¬ p ∣ Nat.card K →
    ∀ A : Subgroup (ModGL τ (AlgebraicClosure K)), A ≤ adjointGroup τ (AlgebraicClosure K) →
      (∀ x ∈ A, ∀ y ∈ A, x * y = y * x) → (∀ x ∈ A, x ^ p = 1) → Nat.card A = p ^ 2 →
      ∃ g ∈ adjointGroup τ (AlgebraicClosure K), ∀ x ∈ A, g⁻¹ * x * g ∈ torusGroup τ (AlgebraicClosure K)

theorem langToralPlane_of_bar {τ : Tag} {p : ℕ} (hp : p.Prime) (hbar : PlanesToralBar τ p) :
    LangToralPlane τ p := by
  intro K _ _ hpK A hAp hAcard
  classical
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨f, hℓ, hf⟩ := FiniteField.card K (ringChar K)
  have : Fact (ringChar K).Prime := ⟨hℓ⟩
  have : CharP K (ringChar K) := ringChar.charP K
  set ℓ := ringChar K with hℓdef
  have hq : Nat.card K = ℓ ^ (f : ℕ) := by rw [Nat.card_eq_fintype_card]; exact hf
  have he : 1 ≤ (f : ℕ) := f.pos
  set L := AlgebraicClosure K with hLdef
  have : CharP L ℓ := charP_of_injective_algebraMap (algebraMap K L).injective _
  have hLchar : ringChar L ≠ p := by
    rw [ringChar.eq L ℓ]
    intro h
    exact hpK (by rw [hq, h]; exact dvd_pow_self p (by omega : (f : ℕ) ≠ 0))
  have hpq : Nat.Coprime p (ℓ ^ (f : ℕ)) :=
    (Nat.Prime.coprime_iff_not_dvd hp).2 (hq ▸ hpK)
  set ι : K →+* L := algebraMap K L with hι
  set φ : ↥(adjointGroup τ K) →* ModGL τ L :=
    (baseChangeGL ι).comp (adjointGroup τ K).subtype with hφ
  have hφinj : Function.Injective φ :=
    (baseChangeGL_injective ι).comp Subtype.val_injective
  set AL : Subgroup (ModGL τ L) := A.map φ with hAL
  have hAL_le : AL ≤ adjointGroup τ L := by
    rintro _ ⟨x, -, rfl⟩
    exact CFSG.LieType.Chevalley.baseChangeGL_mem_adjointGroup ι x.2
  have hALp : ∀ y ∈ AL, y ^ p = 1 := by
    rintro _ ⟨x, hx, rfl⟩
    rw [← map_pow, hAp x hx, map_one]
  have hALcard : Nat.card AL = p ^ 2 := by
    rw [hAL, ← Nat.card_congr (Subgroup.equivMapOfInjective A φ hφinj).toEquiv]
    exact hAcard
  have hALcomm : ∀ x ∈ AL, ∀ y ∈ AL, x * y = y * x := by
    have : Fact p.Prime := ⟨hp⟩
    intro x hx y hy
    have hc := (IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := p) (G := AL) hALcard).is_comm
    exact congrArg Subtype.val (hc.comm ⟨x, hx⟩ ⟨y, hy⟩)
  obtain ⟨g, hgG, hg⟩ := hbar K hpK AL hAL_le hALcomm hALp hALcard
  have hT : ∀ x : A, g⁻¹ * φ x * g ∈ torusGroup τ L := fun x => hg _ ⟨x, x.2, rfl⟩
  choose a ha using fun x : A => exists_rootDiagUnit_eq_of_mem_torusGroup (hT x)
  have hexp : ∀ (x : A) i, a x i ^ p = 1 := by
    intro x
    have h1 : rootDiagUnit τ (a x ^ p) = rootDiagUnit τ 1 := by
      have : rootDiagUnit τ (a x ^ p) = rootDiagUnit τ (a x) ^ p :=
        ((rootDiagUnitHom τ L).map_pow (a x) p)
      rw [this, ← ha x, rootDiagUnit_one]
      calc (g⁻¹ * φ x * g) ^ p = g⁻¹ * (φ x) ^ p * g := by
            have := conj_pow (a := g⁻¹) (b := φ x) (i := p)
            rwa [inv_inv] at this
        _ = 1 := by
            rw [← map_pow, hAp x x.2, map_one]
            group
    have h2 : a x ^ p = 1 := CFSG.LieType.Chevalley.rootDiagUnit_injective h1
    exact fun i => congrFun h2 i
  have hFix : ∀ y : ModGL τ K,
      entrywiseFrobGL τ L ℓ (f : ℕ) (baseChangeGL ι y) = baseChangeGL ι y := by
    intro y
    have hcomp : (iterateFrobenius L ℓ (f : ℕ)).comp ι = ι := by
      refine RingHom.ext fun c => ?_
      change (iterateFrobenius L ℓ f) (ι c) = ι c
      rw [iterateFrobenius_def, ← map_pow]
      congr 1
      rw [← hf]
      exact FiniteField.pow_card c
    rw [entrywiseFrobGL, CFSG.LieType.Chevalley.units_map_entrywiseHom_eq_baseChangeGL,
      CFSG.LieType.Chevalley.baseChangeGL_baseChangeGL, hcomp]
  have hFix' : ∀ x : A, entrywiseFrobGL τ L ℓ (f : ℕ) (φ x) = φ x := fun x => hFix (x : ModGL τ K)
  have hn : ∀ x : A, (g⁻¹ * entrywiseFrobGL τ L ℓ (f : ℕ) g) *
      entrywiseFrobGL τ L ℓ (f : ℕ) (rootDiagUnit τ (a x)) *
      (g⁻¹ * entrywiseFrobGL τ L ℓ (f : ℕ) g)⁻¹ = rootDiagUnit τ (a x) := by
    intro x
    rw [← ha x, map_mul, map_mul, map_inv, hFix' x]
    group
  obtain ⟨w', z, hz, hlang⟩ := exists_lang_datum_of_plane ℓ (f : ℕ) he hpq a hexp hgG hn
  have hzC := familyGroup_le_familyCentralizer (K := L) a hz
  obtain ⟨hzG, hzcomm⟩ := mem_familyCentralizer.1 hzC
  have hu : entrywiseFrobGL τ L ℓ (f : ℕ) (g * z) =
      (g * z) * canonicalRep (coxeterSystem τ) L w' := inv_mul_eq_iff_eq_mul.1 hlang
  refine ⟨w', iterateFrobenius L ℓ (f : ℕ), fun c => ?_, g * z, mul_mem hgG hzG, hu, 1, ?_⟩
  · rw [iterateFrobenius_def, hq]
  · intro x hx
    set xA : A := ⟨x, hx⟩ with hxA
    set d := rootDiagUnit τ (a xA) with hd
    have hzd : z⁻¹ * d * z = d := by
      have := hzcomm xA
      rw [← hd, mul_inv_eq_iff_eq_mul] at this
      calc z⁻¹ * d * z = z⁻¹ * (d * z) := by group
        _ = z⁻¹ * (z * d) := by rw [this]
        _ = d := by group
    have ht : (g * z)⁻¹ * baseChangeGL ι (x : ModGL τ K) * (g * z) = d := by
      have h0 : φ xA = baseChangeGL ι (x : ModGL τ K) := rfl
      calc (g * z)⁻¹ * baseChangeGL ι (x : ModGL τ K) * (g * z)
          = z⁻¹ * (g⁻¹ * φ xA * g) * z := by rw [h0]; group
        _ = d := by rw [ha xA, hzd]
    refine ⟨(g * z)⁻¹ * baseChangeGL ι (x : ModGL τ K) * (g * z), ?_, ?_⟩
    · rw [SetLike.mem_coe, mem_twistedTorusOf, ht]
      refine ⟨rootDiagUnit_mem_torusGroup _, ?_⟩
      have hfx : entrywiseFrobGL τ L ℓ (f : ℕ) (baseChangeGL ι (x : ModGL τ K)) =
          baseChangeGL ι (x : ModGL τ K) := hFix _
      have hFd : entrywiseFrobGL τ L ℓ (f : ℕ) d =
          (canonicalRep (coxeterSystem τ) L w')⁻¹ * d * canonicalRep (coxeterSystem τ) L w' := by
        rw [← ht, map_mul, map_mul, map_inv, hfx, hu]
        group
      change canonicalRep (coxeterSystem τ) L w' * entrywiseFrobGL τ L ℓ (f : ℕ) d *
        (canonicalRep (coxeterSystem τ) L w')⁻¹ = d
      rw [hFd]
      group
    · change (g * z) * ((g * z)⁻¹ * baseChangeGL ι (x : ModGL τ K) * (g * z)) * (g * z)⁻¹ =
        baseChangeGL ι ((1 * x * 1⁻¹ : ↥(adjointGroup τ K)) : ModGL τ K)
      simp only [one_mul, inv_one, mul_one]
      group

end Final

end CFSG.HardMathSupport.Timmesfeld.Torality
