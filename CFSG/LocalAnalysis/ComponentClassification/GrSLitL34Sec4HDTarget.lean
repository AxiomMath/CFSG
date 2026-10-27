module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeMaxWeak
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeW
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4Single

public section

namespace CFSG.ComponentClassification.GrSLit.HeDiag

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ComponentClassification.UnbalancedGS
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)

variable {X : Type} [Group X] [Finite X]

theorem held_equiv_of_isPComponent (hMult : TBLit.HeldTrivialMultiplier) {F L : Subgroup X}
    (hLF : L ≤ F) (hL : IsPComponent 2 (L.subgroupOf F))
    (hHe : IsHeldType (L ⧸ Open.fusionZStar L)) :
    Nonempty (L ⧸ pPrimeCore 2 L ≃* Blueprint.NativeSporadic.He) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, -, hq⟩ := (CatalogueBPrimeJoin.pComponent_subgroupOf_iff 2 L F hLF).mp hL
  obtain ⟨e⟩ := nonempty_quotient_center_equiv_fusionZStar L
  obtain ⟨f⟩ := hHe
  have hZ := hMult (L ⧸ pPrimeCore 2 L) hq ⟨e.trans f⟩
  exact ⟨(QuotientGroup.quotientBot.symm.trans
    (QuotientGroup.quotientMulEquivOfEq hZ.symm)).trans (e.trans f)⟩

omit [Finite X] in
theorem conjugate_eq_of_mem_normalizer {L : Subgroup X} {a : X}
    (ha : a ∈ normalizer (L : Set X)) : conjugate L a = L := by
  ext x
  rw [mem_conjugate_iff]
  exact ((mem_normalizer_iff.mp ha) x).symm

theorem exists_held_target
    (hMax : MaximalTwoComponentInputHe)
    (hS : SchreierFor Blueprint.Catalog) (hHN : HeldNotProperFixedInput)
    (h64 : HeldSylowElementarySixtyFour) (hMult : TBLit.HeldTrivialMultiplier)
    [IsSimpleGroup X] (hnab : ∃ x y : X, x * y ≠ y * x)
    (hK : Assembly.KProper Blueprint.Catalog X) (hU : ¬ OutcomeLocal.UOutcome X) {a r : X}
    {L : Subgroup X} (ha : orderOf a = 2) (hr : orderOf r = 2) (har : a * r = r * a)
    (hLa : L ≤ centralizer ({a} : Set X))
    (hLc : IsPComponent 2 (L.subgroupOf (centralizer ({a} : Set X))))
    (e : L ⧸ pPrimeCore 2 L ≃* Blueprint.NativeSporadic.He)
    (hrL : r ∈ normalizer (L : Set X))
    (hLr : ∀ j ∈ L, j⁻¹ * r⁻¹ * j * r ∈ (pPrimeCore 2 L).map L.subtype) :
    ∃ L' : Subgroup X, L' ≤ centralizer ({r} : Set X) ∧
      IsPComponent 2 (L'.subgroupOf (centralizer ({r} : Set X))) ∧
      centralizer ({r} : Set X) ≤ normalizer (L' : Set X) ∧
      Nonempty (L' ⧸ pPrimeCore 2 L' ≃* Blueprint.NativeSporadic.He) ∧
      gsFixedLayer L r ≤ L' ∧ gsFixedLayer L r ⊔ (pPrimeCore 2 L').map L'.subtype = L' := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set T := gsFixedLayer L r with hTdef
  have hrZ : r ∉ center X := GSLit.not_mem_center_of_orderOf_eq_two hnab hr
  have hLaa : conjugate L a = L := conjugate_eq_self_of_le_centralizer hLa
  have hKe : ∀ k ∈ L ⊔ conjugate L a, k⁻¹ * r⁻¹ * k * r ∈
      (pPrimeCore 2 (centralizer ({a} : Set X))).map (centralizer ({a} : Set X)).subtype := by
    intro k hk
    rw [hLaa, sup_idem] at hk
    exact GSLit.map_pPrimeCore_le_of_isPComponent hLa hLc (hLr k hk)
  obtain ⟨-, -, -, -, hTab, hTpc, hTV, hVE, -, -, φ, -⟩ :=
    UGSChain.kProper_core_trivial_orbit_fixed_layer_containment_of_schreier hS hK (a := a)
      (b := a) (e := r) ha hr rfl har hrZ hLa hLc hKe
  have haCr : a ∈ centralizer ({r} : Set X) := mem_centralizer_singleton_iff.mpr har
  obtain ⟨L', hL'r, hL'c, hTK, hTKpc⟩ :=
    UnbalancedCorr.exists_orbit_component ha haCr hTab hTpc (hTV.trans hVE)
  have hW : GSWeakCorr a L r L' := ⟨ha, hr, har, hLa, hLc, hL'r, hL'c, hrL, hLr, hTK⟩
  obtain ⟨g⟩ := nonempty_fusionZStar_equiv_held e
  have hHe' : IsHeldType (L' ⧸ Open.fusionZStar L') := by
    rcases gsWeakCorr_type_dichotomy hS hK hW hrZ with ⟨f⟩ | ⟨hMa, hTM, hTpc', hlt, ⟨eT⟩⟩
    · obtain ⟨f⟩ := f
      exact ⟨f.symm.trans g⟩
    · exfalso
      have hdtop : centralizer ({r} : Set X) ≠ ⊤ := by
        intro htop
        exact hrZ (mem_center_iff.mpr fun x => mem_centralizer_singleton_iff.mp
          (by rw [htop]; exact mem_top x))
      have hcat := catalog_fusionZStar_of_isPComponent hK hdtop hL'r hL'c
      exact properFixedComponents_notHeld hHN X a r L' T ha hr har hL'r hL'c hMa hTM hTpc' hlt
        hcat ⟨eT.symm.trans g⟩
  obtain ⟨e'⟩ := held_equiv_of_isPComponent hMult hL'r hL'c hHe'
  have hmax' : GSWeakMaximalComponent L' :=
    gsWeakMaximalComponent_of_held hS hHN hnab hK hr hL'r hL'c hHe'
  have hrN : r ∈ normalizer (L' : Set X) := mem_normalizer_of_commute fun x hx =>
    (mem_centralizer_singleton_iff.mp (hL'r hx)).symm
  obtain ⟨S', hSyl', -⟩ := exists_isSylowTwoIn_mem hrN hr
  obtain ⟨E, hET, -, hEe, hE64⟩ := exists_elem_sixtyFour e' h64 inf_le_right
    (hSyl'.isPGroup.to_le inf_le_left) (card_inf_eq_1024 e' hSyl')
  have hrank : 3 ≤ pRank 2 ↥L' := three_le_pRank_of_le hEe (by omega) (hET.trans inf_le_right)
  have hgs : GSMaximalSetting X r L' :=
    ⟨inferInstance, hnab, hK, hU, hr, hL'r, hL'c, hmax', hrank, Sol78.not_psp4_of_held e',
      Or.inr (nonempty_fusionZStar_equiv_held e')⟩
  have hCN := GrS4.centralizer_le_normalizer_of_gsMaximalSetting_he hMax hgs hHe'
  have hL'a : conjugate L' a = L' := conjugate_eq_of_mem_normalizer (hCN haCr)
  have hTL' : T ≤ L' := by
    have h := hTK
    rwa [hL'a, sup_idem] at h
  have hTKC : T ≤ (L' ⊔ conjugate L' a) ⊓ centralizer ({a} : Set X) :=
    le_inf hTK (hTab.trans inf_le_left)
  obtain ⟨-, -, heq⟩ := UGSChain.orbit_fixed_component_comparison ha har hL'r hL'c hTKC hTKpc
  have hidx : (pPrimeCore 2 T).index = (pPrimeCore 2 L').index := by
    rw [index_eq_card, index_eq_card, Nat.card_congr φ.toEquiv, Nat.card_congr e.toEquiv,
      Nat.card_congr e'.toEquiv]
  exact ⟨L', hL'r, hL'c, hCN, ⟨e'⟩, hTL', (heq hidx).2 hL'a.symm⟩

end CFSG.ComponentClassification.GrSLit.HeDiag
