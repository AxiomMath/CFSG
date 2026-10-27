module

public import CFSG.ClassicalInvolution.Asc77.WP3SCUM4U
public import CFSG.ClassicalInvolution.Asc77.WP3SCUBGU
public import CFSG.ClassicalInvolution.Asc77.WP3SCUModel4
public import CFSG.ClassicalInvolution.RouteD.TypeULocal
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate80
public import Certificates.Certificate81
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate115
public import Certificates.Certificate116
public import Certificates.Certificate117
public import Certificates.Certificate120
public import Certificates.Certificate123
public import CFSG.ClassicalInvolution.Asc77.AscE184Basic
public import CFSG.ClassicalInvolution.Asc77.AscE184OddQuot
public import CFSG.ClassicalInvolution.Asc77.AscE184Sec
public import CFSG.ClassicalInvolution.Asc77.AscE186CentA
public import CFSG.ClassicalInvolution.Asc77.AscE186QuotOdd
public import CFSG.ClassicalInvolution.Asc77.AscSixZW
public import CFSG.ClassicalInvolution.Asc77.Lemma310
public import CFSG.ClassicalInvolution.Asc77.ThmEStatement
public import CFSG.ClassicalInvolution.Asc77.WP3ChainVRank3
public import CFSG.ClassicalInvolution.Asc77.WP3ChainVToral
public import CFSG.ClassicalInvolution.Asc77.WP3L54Thm54
public import CFSG.ClassicalInvolution.Balance.QNineFuzzyFree
public import CFSG.ClassicalInvolution.Balance.StrongLocalBalanceGlue
public import CFSG.ClassicalInvolution.Balance.StrongPowDiagMain
public import CFSG.ClassicalInvolution.Balance.StrongPowSuMain
public import CFSG.ClassicalInvolution.Balance.Theorem5Models
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalIsogeny
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalTwistedE6Conj
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalTwistedE6Roots
public import CFSG.ClassicalInvolution.RouteD.TypeUChain
public import CFSG.Goldschmidt.Statements
public import CFSG.Goldschmidt.StatementsH
public import CFSG.Goldschmidt.StatementsX
public import CFSG.LocalAnalysis.ComponentClassification.BadTwoComponentSubgroup
public import CFSG.LocalAnalysis.ComponentClassification.QuasisimpleNormalizerCommutator
public import CFSG.LocalAnalysis.LargeEvenClassification.CyclicCongruenceCut
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerImageCompletion
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerPreimages
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerRestrictionCompletion
public import CFSG.LocalAnalysis.SignalizerFunctor
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldPrimeOrderFixedSubfield
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.OrderThreeNormalizer
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGammaL2PSLRangeCentralizer
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinInvolutionCount
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinRestrictionSixCount
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinUDecomposition
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseEquationEleven
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseEquationTen
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseEquationTenStructuralIdentities
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCasePSL2FieldProjectionArithmetic
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCasePSL2OrderPSubgroupCount
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Suzuki.OddGraphReconstruction
public import Certificates.Certificate1
public import Certificates.Certificate10
public import Certificates.Certificate11
public import Certificates.Certificate12
public import Certificates.Certificate2
public import Certificates.Certificate3
public import Certificates.Certificate4
public import Certificates.Certificate42
public import Certificates.Certificate44
public import Certificates.Certificate5
public import Certificates.Certificate6
public import Certificates.Certificate7
public import Certificates.Certificate8
public import Certificates.Certificate9

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Models CFSG.ClassicalInvolution.Phan
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Balance.StrongBalance
  CFSG.ClassicalInvolution.Balance.StrongBalance.Unitary CFSG.Assembly.LowTwoRank
  CFSG.LieType.BorelTits CFSG.ClassicalInvolution.Balance

section Transport

theorem BlockGeom4.of_equiv {K K' : Type} [Group K] [Group K'] (e : K ≃* K')
    {𝓕 : Set (Subgroup K)} {𝓕' : Set (Subgroup K')}
    (h : ∀ R, R ∈ 𝓕 ↔ R.map e.toMonoidHom ∈ 𝓕') (hg : BlockGeom4 𝓕') : BlockGeom4 𝓕 := by
  have hcen : ∀ x : K, x ∈ Subgroup.center K → e x ∈ Subgroup.center K' := by
    intro x hx
    rw [Subgroup.mem_center_iff] at hx ⊢
    intro g
    obtain ⟨g', rfl⟩ := e.surjective g
    rw [← map_mul, ← map_mul, hx g']
  have hcomm : ∀ {R R₁ : Subgroup K}, (∀ r ∈ R, ∀ s ∈ R₁, r * s = s * r) →
      ∀ r ∈ R.map e.toMonoidHom, ∀ s ∈ R₁.map e.toMonoidHom, r * s = s * r := by
    intro R R₁ hc
    rintro _ ⟨r, hr, rfl⟩ _ ⟨s, hs, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom]
    rw [← map_mul, ← map_mul, hc r hr s hs]
  refine ⟨?_, ?_⟩
  · intro R hR R₁ hR₁ R₂ hR₂ h1 h2
    exact Subgroup.map_injective e.injective
      (hg.uniq (R.map e.toMonoidHom) ((h R).1 hR) (R₁.map e.toMonoidHom) ((h R₁).1 hR₁)
        (R₂.map e.toMonoidHom) ((h R₂).1 hR₂) (hcomm h1) (hcomm h2))
  · intro R hR R' hR' r hr hrc hr1 hcr
    have key := hg.centralizes (R.map e.toMonoidHom) ((h R).1 hR) (R'.map e.toMonoidHom)
      ((h R').1 hR') (e r) ⟨r, hr, rfl⟩
      (by
        rintro _ ⟨s, hs, rfl⟩
        simp only [MulEquiv.coe_toMonoidHom]
        rw [← map_mul, ← map_mul, hrc s hs])
      (fun h1 => hr1 (e.injective (by rw [h1, map_one])))
      (by
        rintro _ ⟨s, hs, rfl⟩
        have := hcen _ (hcr s hs)
        simpa only [MulEquiv.coe_toMonoidHom, map_mul, map_inv] using this)
    rcases key with h1 | h1
    · exact Or.inl (Subgroup.map_injective e.injective h1)
    · refine Or.inr fun s hs s' hs' => ?_
      have := h1 (e s) ⟨s, hs, rfl⟩ (e s') ⟨s', hs', rfl⟩
      rw [← map_mul, ← map_mul] at this
      exact e.injective this

end Transport

section Central

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p]

theorem mul_self_eq_one_of_mem_center_longRootSetU (hK : Nat.card K = (p ^ f) ^ 2) (hp : p ≠ 2)
    {n : ℕ} {hn : 2 ≤ n} {R : Subgroup (Su K p f n)}
    (hR : R ∈ longRootSetU (K := K) (p := p) (f := f) hn) {c : Su K p f n} (hc : c ∈ R)
    (hcc : ∀ r ∈ R, c * r = r * c) : c * c = 1 := by
  obtain ⟨d, hd⟩ := hR
  have h2F : (2 : CFSG.LieType.Steinberg.fixedSubfield K p f) ≠ 0 :=
    CFSG.Semidihedral.OddFieldSL2.two_ne_zero_of_odd_card _ (odd_natCard_fixedSubfield hK hp)
  have hcl := hd.isClassicalSL2 hK hp
  rcases CFSG.ClassicalInvolution.ModelFacts.eq_one_or_eq_of_isClassicalSL2_center h2F hcl hc
    hcc with rfl | rfl
  · exact mul_one 1
  · have := pow_orderOf_eq_one c
    rwa [hcl.orderOf_eq_two, sq] at this

end Central

section Toral

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p] {n : ℕ}
  {H : Type} [Group H]

local notation "cU" => conjSUid (unitaryInvolution K p f) n

theorem toralDiagGU_of_diag (ψ : Su K p f n →* H) {x : Su K p f n} (hx2 : x * x = 1) {v : H}
    (Y₀ : GUid (unitaryInvolution K p f) n) (hY2 : Y₀ * Y₀ = 1)
    (hYx : (Y₀ : GL (Fin n) K) * (x : GL (Fin n) K) = (x : GL (Fin n) K) * Y₀)
    (hact : ∀ y, v * ψ y * v⁻¹ = ψ (cU Y₀ y))
    {F₀ : Subgroup H} (hF₀ : F₀ ≤ Subgroup.closure ({ψ x, v} ∪ (Subgroup.center H : Set H))) :
    ToralDiagGU 2 ψ F₀ := by
  set X₀ : GUid (unitaryInvolution K p f) n := suToGU _ n x with hX₀
  have hX2 : X₀ * X₀ = 1 := by rw [hX₀, ← map_mul, hx2, map_one]
  have hXY : X₀ * Y₀ = Y₀ * X₀ := Subtype.ext hYx.symm
  let P : Subgroup (GUid (unitaryInvolution K p f) n) := Subgroup.closure ({X₀, Y₀} : Set _)
  have hP : ∀ a ∈ P, ∀ b ∈ P, a * b = b * a := by
    refine ChainFrame.commutes_closure ?_
    intro a ha b hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · rfl
    · exact hXY
    · exact hXY.symm
    · rfl
  have hXm : X₀ ∈ P := Subgroup.subset_closure (by simp)
  have hYm : Y₀ ∈ P := Subgroup.subset_closure (by simp)
  have hcx : ∀ y, ψ x * ψ y * (ψ x)⁻¹ = ψ (cU X₀ y) := by
    intro y
    have : cU X₀ y = x * y * x⁻¹ := by
      apply Subtype.ext
      simp only [coe_conjSUid, hX₀, coe_suToGU, Subgroup.coe_mul, Subgroup.coe_inv]
    rw [this, map_mul, map_mul, map_inv]
  let Good : Subgroup H :=
    { carrier := {g | ∃ a ∈ P, a * a = 1 ∧ ∀ y, g * ψ y * g⁻¹ = ψ (cU a y)}
      one_mem' := ⟨1, P.one_mem, by simp, fun y => by simp⟩
      mul_mem' := by
        rintro g₁ g₂ ⟨a₁, ha₁, ha₁2, h₁⟩ ⟨a₂, ha₂, ha₂2, h₂⟩
        refine ⟨a₁ * a₂, P.mul_mem ha₁ ha₂, ?_, fun y => ?_⟩
        · calc a₁ * a₂ * (a₁ * a₂) = a₁ * (a₂ * a₁) * a₂ := by group
            _ = a₁ * (a₁ * a₂) * a₂ := by rw [hP a₂ ha₂ a₁ ha₁]
            _ = (a₁ * a₁) * (a₂ * a₂) := by group
            _ = 1 := by rw [ha₁2, ha₂2, one_mul]
        · calc g₁ * g₂ * ψ y * (g₁ * g₂)⁻¹ = g₁ * (g₂ * ψ y * g₂⁻¹) * g₁⁻¹ := by group
            _ = ψ (cU (a₁ * a₂) y) := by
                rw [h₂, h₁, map_mul, MulAut.mul_apply]
      inv_mem' := by
        rintro g ⟨a, ha, ha2, h⟩
        refine ⟨a⁻¹, P.inv_mem ha, ?_, fun y => ?_⟩
        · calc a⁻¹ * a⁻¹ = (a * a)⁻¹ := by group
            _ = 1 := by rw [ha2]; group
        · have h1 := h (cU a⁻¹ y)
          have e1 : cU a (cU a⁻¹ y) = y := by
            rw [← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one, MulAut.one_apply]
          rw [e1] at h1
          calc g⁻¹ * ψ y * g⁻¹⁻¹ = g⁻¹ * (g * ψ (cU a⁻¹ y) * g⁻¹) * g⁻¹⁻¹ := by
                rw [← h1]
            _ = ψ (cU a⁻¹ y) := by group }
  have hgood : F₀ ≤ Good := by
    refine hF₀.trans ((Subgroup.closure_le Good).mpr ?_)
    intro g hg
    rcases hg with hg | hg
    · rcases hg with rfl | rfl
      · exact ⟨X₀, hXm, hX2, fun y => hcx y⟩
      · exact ⟨Y₀, hYm, hY2, fun y => hact y⟩
    · have hcc := Subgroup.mem_center_iff.mp hg
      refine ⟨1, P.one_mem, by simp, fun y => ?_⟩
      rw [map_one, MulAut.one_apply]
      calc g * ψ y * g⁻¹ = (ψ y * g) * g⁻¹ := by rw [← hcc (ψ y)]
        _ = ψ y := by group
  refine ⟨P, hP, fun g hg => ?_⟩
  obtain ⟨a, ha, ha2, haa⟩ := hgood hg
  exact ⟨a, ha, by rw [pow_two]; exact ha2, haa⟩

end Toral

theorem pairToral_psu_of_diag {p e : ℕ} [Fact p.Prime] {H : Type} [Group H]
    (ψ : (modelUniv .PSU 4 p e Fact.out).K →* H)
    (φ : (modelUniv .PSU 4 p e Fact.out).K ≃* Su (GaloisField p (2 * e)) p e 4)
    {x : (modelUniv .PSU 4 p e Fact.out).K} (hx2 : φ x * φ x = 1) {v : H}
    (Y₀ : GUid (unitaryInvolution (GaloisField p (2 * e)) p e) 4) (hY2 : Y₀ * Y₀ = 1)
    (hYx : (Y₀ : GL (Fin 4) (GaloisField p (2 * e))) *
      ((φ x : Su (GaloisField p (2 * e)) p e 4) : GL (Fin 4) (GaloisField p (2 * e))) =
      ((φ x : Su (GaloisField p (2 * e)) p e 4) : GL (Fin 4) (GaloisField p (2 * e))) * Y₀)
    (hact : ∀ y : Su (GaloisField p (2 * e)) p e 4,
      v * ψ (φ.symm y) * v⁻¹ =
        ψ (φ.symm (conjSUid (unitaryInvolution (GaloisField p (2 * e)) p e) 4 Y₀ y))) :
    PairToral .PSU 4 p e Fact.out ψ (ψ x) v := by
  intro F₀ hF₀
  have hψx : ψ x = (ψ.comp φ.symm.toMonoidHom) (φ x) := by simp
  refine ⟨(fun h => by cases h), fun _ => ⟨φ, ?_⟩, (fun h => by cases h), (fun h => by cases h),
    (fun h => by cases h), (fun h => by cases h), (fun _ h => absurd rfl h)⟩
  exact toralDiagGU_of_diag (ψ.comp φ.symm.toMonoidHom) hx2 Y₀ hY2 hYx
    (fun y => by simpa using hact y) (by rw [← hψx]; exact hF₀)

theorem rankFourFacts_psu {p e : ℕ} [Fact p.Prime] (n : ℕ) (hp2 : p ≠ 2) (h5 : 5 ≤ p ^ e) :
    RankFourFacts .PSU n p e := by
  intro hn
  subst hn
  have he : 1 ≤ e := by
    rcases Nat.eq_zero_or_pos e with rfl | he
    · simp at h5
    · exact he
  have hadm : StatedLieAdmissible .PSU 4 p e :=
    ⟨Fact.out, he, by norm_num, fun h => by
      have := congrArg Prod.fst h
      simp at this⟩
  obtain ⟨φ, hφ⟩ := CFSG.ClassicalInvolution.RouteD.psu_model_equiv hp2 hadm
  have hK : Nat.card (GaloisField p (2 * e)) = (p ^ e) ^ 2 :=
    CFSG.LieType.Universal.card_galoisField_two_mul p e he
  refine ⟨BlockGeom4.of_equiv φ hφ (blockGeom4_longRootSetU hK hp2 h5), ?_⟩
  intro H _ ψ hker R hR v hv hv2 hvR
  set ψ' : Su (GaloisField p (2 * e)) p e 4 →* H := ψ.comp φ.symm.toMonoidHom with hψ'
  have hker' : ψ'.ker ≤ Subgroup.center (Su (GaloisField p (2 * e)) p e 4) :=
    BootRank3.ker_comp_symm_le_center φ ψ hker
  have hrange : ψ'.range = ψ.range := BootRank3.range_comp_symm φ ψ
  have hψ'φ : ∀ r, ψ' (φ r) = ψ r := fun r => by simp [hψ']
  have hRl := (hφ R).1 hR
  have hv' : v ∈ Subgroup.normalizer (ψ'.range : Set H) := by rw [hrange]; exact hv
  have hvR' : ∀ r ∈ R.map φ.toMonoidHom, v * ψ' r = ψ' r * v := by
    rintro _ ⟨r, hr, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, hψ'φ]
    exact hvR r hr
  rcases su4_dichotomy hK hp2 h5 ψ' hker' hRl hv' hv2 hvR' with ⟨R'', hR''l, hc, hv''⟩ |
      ⟨Y₀, hY2, hYR, hact⟩
  · refine Or.inl ⟨R''.map φ.symm.toMonoidHom, (hφ _).2 ?_, ?_, ?_⟩
    · rw [Subgroup.map_map]
      have : φ.toMonoidHom.comp φ.symm.toMonoidHom = MonoidHom.id _ := by ext; simp
      rw [this, Subgroup.map_id]
      exact hR''l
    · rintro r hr _ ⟨s', hs', rfl⟩
      have := hc (φ r) ⟨r, hr, rfl⟩ s' hs'
      simp only [MulEquiv.coe_toMonoidHom] at this ⊢
      apply φ.injective
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
      exact this
    · rintro _ ⟨s', hs', rfl⟩
      have := hv'' s' hs'
      simpa [hψ'] using this
  · refine Or.inr fun x hxR hxc => ?_
    have hxl : φ x ∈ R.map φ.toMonoidHom := ⟨x, hxR, rfl⟩
    have hx2 : φ x * φ x = 1 :=
      mul_self_eq_one_of_mem_center_longRootSetU hK hp2 hRl hxl (by
        rintro _ ⟨r, hr, rfl⟩
        simp only [MulEquiv.coe_toMonoidHom]
        rw [← map_mul, ← map_mul, hxc r hr])
    exact pairToral_psu_of_diag ψ φ hx2 Y₀ hY2 (hYR (φ x) hxl)
      (fun y => by simpa [hψ'] using hact y)

end CFSG.ClassicalInvolution.Asc77
