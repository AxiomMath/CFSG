module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB58ReChoice
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB58NFb
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB58NFl
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB58NFr
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB58SubData
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB58SubCPrime
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB5bTypesHW
public import CFSG.ClassicalInvolution.SmallCases.Sporadic.QuasiAssembly
public import CFSG.LieType.Chevalley.C2E6StandardFixedData
public import CFSG.LieType.Chevalley.C2E6UnitaryFourImages
public import CFSG.LieType.Chevalley.E6SecondGraphFullCentralizer
public import CFSG.LieType.Chevalley.SimplyLacedFieldTwoCover
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafL34Main
public import CFSG.LocalAnalysis.ComponentClassification.EvenPumpDefs
public import CFSG.LocalAnalysis.ComponentClassification.EvenPumpSporHN
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB58SubSyl
public import CFSG.LocalAnalysis.ComponentClassification.RestrictedStdFamilies
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpWedge
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionNormalTwoFixedPointHull
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionThreePointFullTransport
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureConjugation
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureProperPair
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureSylowAssemblyData
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureSylowAssemblyProper
public import CFSG.Open.QuasithinDefs
public import CFSG.Sporadic.HeldB.AllFixed
public import CFSG.Sporadic.Schreier.J1QT
public import CFSG.Sporadic.Schreier.LyFixedSet
public import CFSG.Sporadic.SchreierLemmas.FrattiniProfile
public import CFSG.Sporadic.ThSchreier.ThSchreierCase

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.LocalCores CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)
open scoped commutatorElement

namespace Hyp52.SubSecStmtAux

section Row515

variable {X : Type} [Group X] [Finite X]

theorem row515_of_eq {h h' : Hyp52 X} (ha : h'.a = h.a) (hJ : h'.J = h.J) (hK : h'.K = h.K)
    (hr : h.Row515) : h'.Row515 := by
  have key : ∀ (a : X) (J K : Subgroup X),
      (Nonempty (OddBar J ≃* alternatingGroup (Fin 6)) ∧ conjugate K a = K ∧
        Nonempty (OddBar K ≃* alternatingGroup (Fin 10))) →
      ∀ (a' : X) (J' K' : Subgroup X), a' = a → J' = J → K' = K →
        (Nonempty (OddBar J' ≃* alternatingGroup (Fin 6)) ∧ conjugate K' a' = K' ∧
          Nonempty (OddBar K' ≃* alternatingGroup (Fin 10))) := by
    intro a J K hr a' J' K' ha hJ hK
    subst ha hJ hK
    exact hr
  exact key h.a h.J h.K hr h'.a h'.J h'.K ha hJ hK

theorem noFusion_row515 [IsSimpleGroup X] (h15 : NoFusionB2Row515Statement58)
    (hnonab : ∃ u v : X, u * v ≠ v * u) (hK : Assembly.KProper Blueprint.Catalog X)
    (hz : ∃ z : X, orderOf z = 2 ∧ oddCore (centralizer ({z} : Set X)) ≠ ⊥)
    (hU : ¬ OutcomeLocal.UOutcome X) (h : Hyp52 X)
    (hmax : GSMaximalUnbalancingTriple h.a h.x h.J) (hiso : GSIsoAt h.a h.J)
    (hnB1 : ¬ ConclusionB1 h.J) (hnB2a : ¬ ConclusionB2a h.a h.J) (hWh : h.NoFusionW)
    (hT : h.T ≠ h.B ⊔ zpowers h.a) (hrow : h.Row515) {y : X} (hc : h.SecCond y)
    (hSyl : Seven.IsSylowIn (h.S ⊓ h.secG0 y) (centralizer ({h.a} : Set X) ⊓ h.secG0 y))
    (g : X) (hgG : g ∈ h.secG0 y)
    (hgN : g ∈ normalizer ((h.secJ0 y ⊔ h.secB0 y : Subgroup X) : Set X))
    (hgS : g ∈ normalizer ((h.S ⊓ h.secG0 y : Subgroup X) : Set X))
    (hg2 : IsPGroup 2 (zpowers g)) (hga : g * h.a * g⁻¹ * h.a⁻¹ ∈ h.secB0 y) :
    g * h.a = h.a * g := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set S0 := h.S ⊓ h.secG0 y with hS0
  set R := S0 ⊔ zpowers g with hRdef
  have hS02 : IsPGroup 2 S0 := h.isPGroup_S.to_le inf_le_left
  have hgS0 : zpowers g ≤ normalizer (S0 : Set X) := zpowers_le.mpr hgS
  have hR2 : IsPGroup 2 R := IsPGroup.to_sup_of_normal_left' hS02 hg2 hgS0
  have hRG : R ≤ h.secG0 y := sup_le inf_le_right (zpowers_le.mpr hgG)
  have hRN : R ≤ normalizer (S0 : Set X) := sup_le le_normalizer hgS0
  let F : Subgroup X :=
    { carrier := {t | t ∈ normalizer (h.secB0 y : Set X) ∧ t * h.a * t⁻¹ * h.a⁻¹ ∈ h.secB0 y}
      one_mem' := ⟨one_mem _, by simp⟩
      mul_mem' := by
        rintro t₁ t₂ ⟨ht₁N, ht₁⟩ ⟨ht₂N, ht₂⟩
        refine ⟨mul_mem ht₁N ht₂N, ?_⟩
        rw [show t₁ * t₂ * h.a * (t₁ * t₂)⁻¹ * h.a⁻¹ =
          (t₁ * (t₂ * h.a * t₂⁻¹ * h.a⁻¹) * t₁⁻¹) * (t₁ * h.a * t₁⁻¹ * h.a⁻¹) by group]
        exact mul_mem ((mem_normalizer_iff.mp ht₁N _).mp ht₂) ht₁
      inv_mem' := by
        rintro t ⟨htN, ht⟩
        refine ⟨inv_mem htN, ?_⟩
        rw [show t⁻¹ * h.a * t⁻¹⁻¹ * h.a⁻¹ = t⁻¹ * (t * h.a * t⁻¹ * h.a⁻¹)⁻¹ * t⁻¹⁻¹ by group]
        exact (mem_normalizer_iff.mp (inv_mem htN) _).mp (inv_mem ht) }
  have hS0F : S0 ≤ F := by
    intro s hs
    refine ⟨(mem_inf.mp hs).2, ?_⟩
    rw [show s * h.a * s⁻¹ * h.a⁻¹ = 1 by rw [h.comm_a (mem_inf.mp hs).1]; group]
    exact one_mem _
  have hgF : g ∈ F := ⟨hgG, hga⟩
  have hRF : R ≤ F := sup_le hS0F (zpowers_le.mpr hgF)
  have hRB : ∀ t ∈ R, t * h.a * t⁻¹ = (t * h.a * t⁻¹ * h.a⁻¹) * h.a ∧
      t * h.a * t⁻¹ * h.a⁻¹ ∈ h.secB0 y := fun t ht => ⟨by group, (hRF ht).2⟩
  by_cases hb2 : R ⊓ normalizer (h.B : Set X) ≤ S0
  · refine h15 X hnonab hK hz hU h hmax hiso hnB1 hnB2a y hc hSyl g hgG hgN hgS hg2 hga hb2 ?_
      hT hrow
    intro t ht hBP
    obtain ⟨heq, hmem⟩ := hRB t ht
    exact h.card_inf_normalizer_conjugate_B_le (h.secB0_le_B y hmem) heq hBP
  · exfalso
    obtain ⟨w, hwRN, hwS0⟩ := IsConcreteLE.not_le_iff_exists.mp hb2
    obtain ⟨hwR, hwN⟩ := mem_inf.mp hwRN
    obtain ⟨heq, hmem⟩ := hRB w hwR
    have hQ : h.Q = S0 ⊓ normalizer (h.B : Set X) := by
      apply le_antisymm
      · exact le_inf (le_inf inf_le_left hc.Q_le) inf_le_right
      · exact le_inf (inf_le_left.trans inf_le_left) inf_le_right
    have hwQ : w ∈ normalizer (h.Q : Set X) := by
      rw [hQ]
      exact Six.mem_normalizer_inf (hRN hwR) (le_normalizer hwN)
    have haR : h.a ∈ R :=
      mem_sup_left (mem_inf.mpr ⟨h.a_mem_S, Hyp52.a_mem_secG0 hc.Q_le⟩)
    have hcomm := hWh w hwN hwQ R hR2 hwR haR _ (h.secB0_le_B y hmem) heq
    apply hwS0
    have hwY : w ∈ centralizer ({h.a} : Set X) ⊓ h.secG0 y :=
      mem_inf.mpr ⟨mem_centralizer_singleton_iff.mpr hcomm, hRG hwR⟩
    exact OS1.mem_of_isSylowIn hSyl hwY (hRN hwR) (hR2.to_le (zpowers_le.mpr hwR))

theorem exists_secSylow_reChoice58_row515 [IsSimpleGroup X] (hS : SchreierFor Blueprint.Catalog)
    (hnonab : ∃ u v : X, u * v ≠ v * u) (hK : Assembly.KProper Blueprint.Catalog X)
    (hz : ∃ z : X, orderOf z = 2 ∧ oddCore (centralizer ({z} : Set X)) ≠ ⊥)
    (hU : ¬ OutcomeLocal.UOutcome X) (h15 : NoFusionB2Row515Statement58)
    (hW : ∀ (X : Type) [Group X] [Finite X] (h : Hyp52 X), NF58Setting X h → h.NoFusionW)
    (h : Hyp52 X) (hmax : GSMaximalUnbalancingTriple h.a h.x h.J) (hiso : GSIsoAt h.a h.J)
    (hnB1 : ¬ ConclusionB1 h.J) (hnB2a : ¬ ConclusionB2a h.a h.J)
    (hT : h.T ≠ h.B ⊔ zpowers h.a) (hrow : h.Row515)
    (hCN : centralizer ({h.a} : Set X) ≤ normalizer (h.J : Set X))
    (hSa : ∃ R : Sylow 2 ↥(centralizer ({h.a} : Set X)),
      (R : Subgroup _) = h.S.subgroupOf (centralizer ({h.a} : Set X)))
    {y : X} (hc : h.SecCond y) :
    ∃ h' : Hyp52 X, h'.a = h.a ∧ h'.J = h.J ∧ h'.B = h.B ∧ h'.K = h.K ∧
      (∃ c ∈ centralizer ({h.a} : Set X) ⊓ normalizer (h.J : Set X),
        h'.S = conjugate h.S c ∧ h'.x = c⁻¹ * h.x * c) ∧
      h'.Q = h.Q ∧ h'.T = h.T ∧ h'.SecCond y ∧ h'.SecSylow y := by
  obtain ⟨h', ha', hJ', hB', hK', ⟨c, hcmem, hS', hx'⟩, hQ', hT', hc', hsylB⟩ :=
    h.exists_reChoice58 hS hnonab hK hmax hiso hCN hSa hc
  have hmax' : GSMaximalUnbalancingTriple h'.a h'.x h'.J := by
    rw [ha', hx', hJ']
    exact ⟨gsUnbalancingTriple_conj hmax.1 (mem_inf.mp hcmem).1 (mem_inf.mp hcmem).2, hmax.2⟩
  have hiso' : GSIsoAt h'.a h'.J := by
    rw [ha', hJ']
    exact hiso
  have hnB1' : ¬ ConclusionB1 h'.J := by rw [hJ']; exact hnB1
  have hnB2a' : ¬ ConclusionB2a h'.a h'.J := by rw [ha', hJ']; exact hnB2a
  have hWh' : h'.NoFusionW :=
    hW X h' ⟨inferInstance, hnonab, hK, hz, hU, hmax', hiso', hnB1', hnB2a'⟩
  have hT'' : h'.T ≠ h'.B ⊔ zpowers h'.a := by
    rw [hT', hB', ha']
    exact hT
  have hA' := fun g hgG hgN hgS hg2 hga =>
    noFusion_row515 h15 hnonab hK hz hU h' hmax' hiso' hnB1' hnB2a' hWh' hT''
      (row515_of_eq ha' hJ' hK' hrow) hc' hsylB g hgG hgN hgS hg2 hga
  exact ⟨h', ha', hJ', hB', hK', ⟨c, hcmem, hS', hx'⟩, hQ', hT', hc',
    Hyp52.secSylow_of_noFusion (Hyp52.a_mem_secG0 hc'.Q_le) hA' hsylB⟩

theorem sectionData_of_row515 [IsSimpleGroup X] (hS : SchreierFor Blueprint.Catalog)
    (hnonab : ∃ u v : X, u * v ≠ v * u) (hK : Assembly.KProper Blueprint.Catalog X)
    (hz : ∃ z : X, orderOf z = 2 ∧ oddCore (centralizer ({z} : Set X)) ≠ ⊥)
    (hU : ¬ OutcomeLocal.UOutcome X) (h15 : NoFusionB2Row515Statement58)
    (hW : ∀ (X : Type) [Group X] [Finite X] (h : Hyp52 X), NF58Setting X h → h.NoFusionW)
    (h : Hyp52 X) (hmax : GSMaximalUnbalancingTriple h.a h.x h.J) (hiso : GSIsoAt h.a h.J)
    (hnB1 : ¬ ConclusionB1 h.J) (hnB2a : ¬ ConclusionB2a h.a h.J)
    (hT : h.T ≠ h.B ⊔ zpowers h.a) (hrow : h.Row515)
    (hCN : centralizer ({h.a} : Set X) ≤ normalizer (h.J : Set X))
    (hSa : ∃ R : Sylow 2 ↥(centralizer ({h.a} : Set X)),
      (R : Subgroup _) = h.S.subgroupOf (centralizer ({h.a} : Set X)))
    {y : X} (hc : h.SecCond y) : h.SectionData := by
  obtain ⟨h', ha', hJ', hB', hK', -, -, hT', hc', hSyl⟩ :=
    exists_secSylow_reChoice58_row515 hS hnonab hK hz hU h15 hW h hmax hiso hnB1 hnB2a hT hrow
      hCN hSa hc
  exact sectionData_of_eq ha' hJ' hB' hK' hT' (Hyp52.sectionData_of_secCond hc' hSyl)

end Row515

section Row516

section Quotient

variable {H : Type} [Group H] [Finite H]

local notation "π" => QuotientGroup.mk' (pPrimeCore 2 H)

theorem map_conjugate_eq_iff_of_pComponent {B K : Subgroup H} {a : H}
    (haB : a ∈ normalizer (B : Set H)) (hKW : K ≤ normalizer (B : Set H))
    (hKc : IsPComponent 2 (K.subgroupOf (normalizer (B : Set H)))) :
    conjugate (K.map π) (π a) = K.map π ↔ conjugate K a = K := by
  have hO := OddQuot.not_two_dvd_card_ker (H := H)
  rw [← map_conjugate]
  constructor
  · intro heq
    obtain ⟨haX, hac⟩ := OddQuot.isPComponent_conjugate_subgroupOf haB hKW hKc
    exact OddQuot.eq_of_map_eq π hO haX hKW hac hKc heq
  · intro heq
    rw [heq]

theorem map_mem_sup_coreActionKernel_iff_of_pComponent {B K : Subgroup H} {a : H}
    (haB : a ∈ normalizer (B : Set H)) (hKW : K ≤ normalizer (B : Set H))
    (hKc : IsPComponent 2 (K.subgroupOf (normalizer (B : Set H)))) :
    π a ∈ K.map π ⊔ coreActionKernel (K.map π) ↔ a ∈ K ⊔ coreActionKernel K := by
  have hO := OddQuot.not_two_dvd_card_ker (H := H)
  have hmap := OddQuot.map_inf_coreActionKernel (le_refl (normalizer (K : Set H)))
  constructor
  · intro ha
    obtain ⟨k', hk', c', hc', hkc⟩ := B5a.exists_mul_of_mem_sup_coreActionKernel ha
    obtain ⟨k, hk, rfl⟩ := mem_map.mp hk'
    have hcc : π (k⁻¹ * a) = c' := by
      rw [map_mul, map_inv, eq_inv_mul_of_mul_eq hkc]
    have hcW : k⁻¹ * a ∈ normalizer (B : Set H) :=
      mul_mem (inv_mem (hKW hk)) haB
    have hcN : k⁻¹ * a ∈ normalizer (K : Set H) := by
      obtain ⟨hcX, hcc'⟩ := OddQuot.isPComponent_conjugate_subgroupOf hcW hKW hKc
      have heq : conjugate K (k⁻¹ * a) = K :=
        OddQuot.eq_of_map_eq π hO hcX hKW hcc' hKc (by
          rw [map_conjugate, hcc]
          exact conjugate_eq_of_mem_normalizer (mem_coreActionKernel.mp hc').1)
      exact mem_normalizer_of_conjugate_eq heq
    have h1 : π (k⁻¹ * a) ∈ (normalizer (K : Set H) ⊓ coreActionKernel K).map π := by
      rw [hmap, hcc]
      exact mem_inf.mpr ⟨hcc ▸ mem_map_of_mem π hcN, hc'⟩
    obtain ⟨d, hd, hdc⟩ := mem_map.mp h1
    have ho : d⁻¹ * (k⁻¹ * a) ∈ pPrimeCore 2 H := by
      rw [← QuotientGroup.ker_mk' (pPrimeCore 2 H), MonoidHom.mem_ker, map_mul, map_inv, hdc,
        inv_mul_cancel]
    have hoN : d⁻¹ * (k⁻¹ * a) ∈ normalizer (K : Set H) :=
      mul_mem (inv_mem (mem_inf.mp hd).1) hcN
    have hoK : d⁻¹ * (k⁻¹ * a) ∈ coreActionKernel K := by
      refine mem_coreActionKernel.mpr ⟨hoN, fun t ht => ?_⟩
      apply OddQuot.inf_pPrimeCore_le_oddCoreIn K
      set o := d⁻¹ * (k⁻¹ * a) with hodef
      refine mem_inf.mpr ⟨?_, ?_⟩
      · have h2 := (mem_normalizer_iff.mp (inv_mem hoN) t).mp ht
        rw [inv_inv] at h2
        rw [show t⁻¹ * o⁻¹ * t * o = t⁻¹ * (o⁻¹ * t * o) by group]
        exact mul_mem (inv_mem ht) h2
      · have h2 : t⁻¹ * o⁻¹ * t⁻¹⁻¹ ∈ pPrimeCore 2 H :=
          (inferInstance : (pPrimeCore 2 H).Normal).conj_mem _ (inv_mem ho) t⁻¹
        rw [inv_inv] at h2
        exact mul_mem h2 ho
    have hcK : k⁻¹ * a ∈ coreActionKernel K := by
      rw [show k⁻¹ * a = d * (d⁻¹ * (k⁻¹ * a)) by group]
      exact mul_mem (mem_inf.mp hd).2 hoK
    rw [show a = k * (k⁻¹ * a) by group]
    exact mul_mem (mem_sup_left hk) (mem_sup_right hcK)
  · intro ha
    obtain ⟨k, hk, c, hcK, hkc⟩ := B5a.exists_mul_of_mem_sup_coreActionKernel ha
    rw [← hkc, map_mul]
    refine mul_mem (mem_sup_left (mem_map_of_mem π hk)) (mem_sup_right ?_)
    have h1 : π c ∈ (normalizer (K : Set H) ⊓ coreActionKernel K).map π :=
      mem_map_of_mem π (mem_inf.mpr ⟨(mem_coreActionKernel.mp hcK).1, hcK⟩)
    rw [hmap] at h1
    exact (mem_inf.mp h1).2

end Quotient

variable {X : Type} [Group X] [Finite X] {h : Hyp52 X} {y : X}

theorem fusionZStar_equiv_of_image (hc : h.SecCond y)
    {K' : Subgroup (↥(h.secSubImg y) ⧸ pPrimeCore 2 ↥(h.secSubImg y))}
    (hK' : K' = (h.subK y).map (QuotientGroup.mk' (pPrimeCore 2 ↥(h.secSubImg y)))) :
    Nonempty (↥K' ⧸ Open.fusionZStar ↥K' ≃* ↥h.K ⧸ Open.fusionZStar ↥h.K) := by
  subst hK'
  obtain ⟨e1⟩ := OddQuot.nonempty_quotient_fusionZStar_equiv _ OddQuot.not_two_dvd_card_ker
    (h.subK y)
  obtain ⟨e2⟩ := TwoQuot.nonempty_fusionZStar_equiv_of_pPrimeCore_equiv
    (UnbalancingLocal.Correspondence.quotientPPrimeCoreCongr 2
      (subgroupOfEquivOfLe (secImage_K_le hc)))
  obtain ⟨e3⟩ := nonempty_secK_fusionZStar_equiv (h := h) (y := y)
  exact ⟨e1.symm.trans (e2.trans e3)⟩

theorem pPrimeCore_equiv_of_image
    {J' : Subgroup (↥(h.secSubImg y) ⧸ pPrimeCore 2 ↥(h.secSubImg y))}
    (hJ' : J' = (h.subJ y).map (QuotientGroup.mk' (pPrimeCore 2 ↥(h.secSubImg y))))
    (hZ : center (↥h.J ⧸ pPrimeCore 2 ↥h.J) = ⊥) :
    Nonempty (↥J' ⧸ pPrimeCore 2 ↥J' ≃* ↥h.J ⧸ pPrimeCore 2 ↥h.J) := by
  subst hJ'
  obtain ⟨e1⟩ := OddQuot.nonempty_quotient_pPrimeCore_equiv _ OddQuot.not_two_dvd_card_ker
    (h.subJ y)
  obtain ⟨e3⟩ := nonempty_secJ_pPrimeCore_equiv (y := y) hZ
  exact ⟨e1.symm.trans ((UnbalancingLocal.Correspondence.quotientPPrimeCoreCongr 2
    (subgroupOfEquivOfLe (h.secImage_secJ0_le y))).trans e3)⟩

theorem conj_inner_equiv_of_image (hc : h.SecCond y)
    {a' : ↥(h.secSubImg y) ⧸ pPrimeCore 2 ↥(h.secSubImg y)}
    {K' : Subgroup (↥(h.secSubImg y) ⧸ pPrimeCore 2 ↥(h.secSubImg y))}
    (ha' : a' = QuotientGroup.mk' (pPrimeCore 2 ↥(h.secSubImg y)) hc.subA)
    (hK' : K' = (h.subK y).map (QuotientGroup.mk' (pPrimeCore 2 ↥(h.secSubImg y)))) :
    (conjugate K' a' = K' ↔ conjugate h.K h.a = h.K) ∧
      (a' ∈ K' ⊔ coreActionKernel K' ↔ h.a ∈ h.K ⊔ coreActionKernel h.K) := by
  subst ha' hK'
  obtain ⟨hKW, hKc⟩ := hc.isPComponent_subK
  exact ⟨(map_conjugate_eq_iff_of_pComponent hc.subA_mem_normalizer hKW hKc).trans
      hc.conjugate_subK_eq_iff,
    (map_mem_sup_coreActionKernel_iff_of_pComponent hc.subA_mem_normalizer hKW hKc).trans
      hc.subA_mem_sup_iff⟩

theorem false_of_row516_inner (hR16 : Row516InnerStatementHW) (hc : h.SecCond y)
    (hCN : centralizer ({h.a} : Set X) ≤ normalizer (h.J : Set X))
    (hSa : ∃ R : Sylow 2 ↥(centralizer ({h.a} : Set X)),
      (R : Subgroup _) = h.S.subgroupOf (centralizer ({h.a} : Set X)))
    (hWh : h.NoFusionW) (hrow : h.Row516) (hin : h.a ∈ h.K ⊔ coreActionKernel h.K) : False := by
  obtain ⟨h', ha', hJ', -, hK', -⟩ := hc.exists_hyp59W_subsection hCN hSa hWh
  obtain ⟨p, f, hp, hp2, hf, hJ, hKa, hK⟩ := hrow
  have hJs : IsSimpleGroup (OddBar h.J) := isSimpleGroup_of_lieModel_psl_two hJ
  obtain ⟨eJ⟩ := pPrimeCore_equiv_of_image hJ'
    (center_eq_bot_of_isSimpleGroup_of_isQuasisimple h.isQuasisimple_J)
  obtain ⟨eK⟩ := fusionZStar_equiv_of_image hc hK'
  obtain ⟨hconj, hinner⟩ := conj_inner_equiv_of_image hc ha' hK'
  have hJ'' : Blueprint.LieModel (OddBar h'.J) .PSL 2 p (2 * f) :=
    lieModel_of_mulEquiv_ne_zero eJ.symm (by norm_num) hJ
  have hK'' : Blueprint.LieModel (ZStarBar h'.K) .PSL 4 p f ∨
      Blueprint.LieModel (ZStarBar h'.K) .PSU 4 p f ∨
      ∃ e : ℕ, f = 2 * e ∧ Blueprint.LieModel (ZStarBar h'.K) .POmegaMinus 4 p e := by
    rcases hK with hL | hL | ⟨e, he, hL⟩
    · exact Or.inl (lieModel_of_mulEquiv_ne_zero eK.symm (by norm_num) hL)
    · exact Or.inr (Or.inl (lieModel_of_mulEquiv_ne_zero eK.symm (by norm_num) hL))
    · exact Or.inr (Or.inr ⟨e, he, lieModel_of_mulEquiv_ne_zero eK.symm (by norm_num) hL⟩)
  exact hR16 _ h' ⟨p, f, hp, hp2, hf, hJ'', hconj.mpr hKa, hK''⟩ (hinner.mpr hin)

end Row516

end Hyp52.SubSecStmtAux

theorem sectionStatement_of_sub (hS : SchreierFor Blueprint.Catalog) (hB1 : ConjFixStatement)
    (hCF23 : CFProp23Fusion) (hCF24 : CFProp24c) (hCFc : CFProp23Center)
    (hCFi : CFProp23IndexElim) (hCFr : CFProp23IndexReduced) (hSol : SolomonTwoSubgroupAltInput)
    (hW : ∀ (X : Type) [Group X] [Finite X] (h : Hyp52 X), NF58Setting X h → h.NoFusionW)
    (h15 : NoFusionB2Row515Statement58) (hR16 : Row516InnerStatementHW) : SectionStatement := by
  intro X _ _ _ hnonab hK hz hU h hmax hiso hnB1 hnB2a
  by_cases hBP : h.P ≤ normalizer (h.B : Set X)
  · refine Hyp52.sectionData_of_normal hBP ?_
    rw [← hmax.1.2.1]
    exact pow_orderOf_eq_one h.x
  · have hCN := h.centralizer_le_normalizer_J hB1 sylowKernelStatement hCF23 hCF24 hCFc
    obtain ⟨-, hSa⟩ := h.S_sylow_centralizer hB1 sylowKernelStatement hCF23 hCF24 hCFc
    have hc := (h.isX0_x0 hBP).secCond
    have hWh : h.NoFusionW :=
      hW X h ⟨inferInstance, hnonab, hK, hz, hU, hmax, hiso, hnB1, hnB2a⟩
    by_cases hT : h.T = h.B ⊔ zpowers h.a
    · exact h.sectionData_of_T_eq hS hnonab hK hmax hiso hCN hSa hc hT hWh
    · rcases h.row515_or_row516Inner_of_T_ne hnonab hK hz hU hB1 hCF23 hCFi hCFr hSol
        sylowKernelStatement hCF24 hT with h515 | ⟨h516, hin⟩
      · exact Hyp52.SubSecStmtAux.sectionData_of_row515 hS hnonab hK hz hU h15 hW h hmax hiso
          hnB1 hnB2a hT h515 hCN hSa hc
      · exact (Hyp52.SubSecStmtAux.false_of_row516_inner hR16 hc hCN hSa hWh h516 hin).elim

end CFSG.ComponentClassification.GSThmB
