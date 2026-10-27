module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5SRank
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeKFixed
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34RCenterTrivial
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34ProperFixedSimple
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrKernelFactors

public section

namespace CFSG.ComponentClassification.GrSLit.L34Sec5S

open CFSG Subgroup
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

theorem pRank_le_one_of_quasisimple (hCT : L34ProperFixedCenterTrivial)
    (hPFS : L34ProperFixedSimpleRank) {Q : Type} [Group Q] [Finite Q] (hQ : IsQuasisimple Q)
    (hZ : IsPGroup 2 (center Q)) (hcat : Blueprint.Catalog (Q ⧸ center Q))
    (hHe : IsEmpty (Q ≃* Blueprint.NativeSporadic.He)) {σ : MulAut Q}
    (hσ : ∀ y, σ (σ y) = y) {P : Subgroup Q} (hPF : P ≤ fixedSubgroup σ)
    (hP : IsPComponent 2 (P.subgroupOf (fixedSubgroup σ))) (hPne : P ≠ ⊤)
    (htype : IsL34Type (P ⧸ Open.fusionZStar P)) : pRank 2 ↥(Open.fusionZStar ↥P) ≤ 1 := by
  by_contra hr
  have hrank : 2 ≤ pRank 2 ↥(Open.fusionZStar ↥P) := by omega
  have hZ1 := hCT Q hQ hZ hcat σ hσ P hPF hP hPne htype hrank
  have : IsSimpleGroup Q := UnbalancedCorr.isSimpleGroup_of_isQuasisimple_of_center_eq_bot hQ hZ1
  have eQ : Q ⧸ center Q ≃* Q :=
    (QuotientGroup.quotientMulEquivOfEq hZ1).trans QuotientGroup.quotientBot
  have hcatQ : Blueprint.Catalog Q := SectionRank.catalog_of_mulEquiv eQ.symm hcat
  rcases hPFS Q inferInstance (UnbalancedCorr.exists_ne_of_isQuasisimple hQ) hcatQ σ hσ P hPF hP
    hPne htype with hH | hle
  · obtain ⟨eH⟩ := hH
    exact hHe.false eH
  · exact hr hle

theorem exists_quotient_fixed_component {G : Type} [Group G] [Finite G] {a : G}
    {M T : Subgroup G} (ha : orderOf a = 2) (hMa : conjugate M a = M)
    (hTM : T ≤ M ⊓ centralizer ({a} : Set G))
    (hTp : IsPComponent 2 (T.subgroupOf (M ⊓ centralizer ({a} : Set G))))
    (hlt : (pPrimeCore 2 T).index < (pPrimeCore 2 M).index) :
    ∃ (σ : MulAut (M ⧸ pPrimeCore 2 M)) (P : Subgroup (M ⧸ pPrimeCore 2 M)),
      (∀ y, σ (σ y) = y) ∧ P ≤ fixedSubgroup σ ∧ IsPComponent 2 (P.subgroupOf (fixedSubgroup σ)) ∧
        P ≠ ⊤ ∧ Nonempty (T ⧸ Open.fusionZStar T ≃* P ⧸ Open.fusionZStar P) ∧
        Nonempty (T ⧸ pPrimeCore 2 T ≃* P ⧸ pPrimeCore 2 P) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have haa : a * a = 1 := by rw [← pow_two, ← ha, pow_orderOf_eq_one]
  have haN : a ∈ normalizer (M : Set G) := by
    rw [mem_normalizer_iff]
    intro y
    rw [← UnbalancedLayer.mem_conjugate_iff, hMa]
  set c : MulAut M := M.normalizerMonoidHom ⟨a, haN⟩ with hcdef
  have hcapp : ∀ x : M, ((c x : M) : G) = a * x * a⁻¹ := fun x => rfl
  have hc2 : ∀ x, c (c x) = x := by
    intro x
    apply Subtype.ext
    rw [hcapp, hcapp]
    calc a * (a * (x : G) * a⁻¹) * a⁻¹ = (a * a) * x * (a * a)⁻¹ := by group
      _ = x := by rw [haa]; group
  have hfixC : fixedSubgroup c = (M ⊓ centralizer ({a} : Set G)).subgroupOf M := by
    ext x
    rw [LocalAnalysis.ComponentInitial.mem_fixedSubgroup_iff, mem_subgroupOf, mem_inf,
      mem_centralizer_singleton_iff]
    constructor
    · intro hx
      have h1 := congrArg Subtype.val hx
      rw [hcapp] at h1
      refine ⟨x.2, ?_⟩
      calc (x : G) * a = a * x * a⁻¹ * a := by rw [h1]
        _ = a * x := by group
    · rintro ⟨-, hx⟩
      apply Subtype.ext
      rw [hcapp]
      calc a * (x : G) * a⁻¹ = x * a * a⁻¹ := by rw [hx]
        _ = x := by group
  set T' := T.subgroupOf M with hT'def
  have hTM' : T ≤ M := hTM.trans inf_le_left
  have hT'C : T' ≤ fixedSubgroup c := by
    rw [hfixC]
    intro x hx
    rw [mem_subgroupOf] at hx ⊢
    exact hTM hx
  have hT'p : IsPComponent 2 (T'.subgroupOf (fixedSubgroup c)) := by
    rw [hfixC]
    exact (UnbalancedCorr.isPComponent_subgroupOf_subgroupOf_iff' (L := T) inf_le_left 2
      Nat.prime_two).mpr hTp
  let eT : T ≃* T' := (subgroupOfEquivOfLe hTM').symm
  have hlt' : (pPrimeCore 2 T').index < (pPrimeCore 2 M).index := by
    rw [index_eq_card, index_eq_card,
      ← UnbalancingLocal.Correspondence.card_quotient_pPrimeCore_congr eT, ← index_eq_card,
      ← index_eq_card]
    exact hlt
  obtain ⟨σ, P, hσ, hPF, hP, hPne, f, hf, hfk, -⟩ :=
    HeK.exists_quasisimple_fixed_component c hc2 hT'C hT'p hlt'
  set F : T →* P := f.comp eT.toMonoidHom with hFdef
  have hF : Function.Surjective F := hf.comp eT.surjective
  have hFk : ¬ 2 ∣ Nat.card F.ker := by
    let g : F.ker →* f.ker := (eT.toMonoidHom.comp F.ker.subtype).codRestrict f.ker fun k => k.2
    have hg : Function.Injective g := fun k₁ k₂ h => by
      have h' := congrArg (fun x : f.ker => (x : T')) h
      exact Subtype.ext (eT.injective h')
    exact fun h2 => hfk (h2.trans (Subgroup.card_dvd_of_injective g hg))
  exact ⟨σ, P, hσ, hPF, hP, hPne,
    GSThmB.OddQuot.nonempty_fusionZStar_equiv_of_surjective F hF hFk,
    GSThmB.OddQuot.nonempty_pPrimeCore_equiv_of_surjective F hF hFk⟩

theorem false_of_proper_fixed_rank (hCT : L34ProperFixedCenterTrivial)
    (hPFS : L34ProperFixedSimpleRank) {G : Type} [Group G] [Finite G]
    (hK : Assembly.KProper Blueprint.Catalog G) {a b : G} {M T : Subgroup G}
    (ha : orderOf a = 2) (hbtop : centralizer ({b} : Set G) ≠ ⊤)
    (hMb : M ≤ centralizer ({b} : Set G))
    (hMp : IsPComponent 2 (M.subgroupOf (centralizer ({b} : Set G))))
    (hHe : IsEmpty (M ⧸ pPrimeCore 2 M ≃* Blueprint.NativeSporadic.He))
    (hMa : conjugate M a = M) (hTM : T ≤ M ⊓ centralizer ({a} : Set G))
    (hTp : IsPComponent 2 (T.subgroupOf (M ⊓ centralizer ({a} : Set G))))
    (hlt : (pPrimeCore 2 T).index < (pPrimeCore 2 M).index)
    (htype : IsL34Type (T ⧸ Open.fusionZStar T))
    (hrank : 2 ≤ pRank 2 ↥(Open.fusionZStar ↥T)) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨σ, P, hσ, hPF, hP, hPne, ⟨eZ⟩, ⟨eO⟩⟩ :=
    exists_quotient_fixed_component ha hMa hTM hTp hlt
  have hMq : IsQuasisimple (M ⧸ pPrimeCore 2 M) :=
    ((CatalogueBPrimeJoin.pComponent_subgroupOf_iff 2 M _ hMb).1 hMp).2.2
  obtain ⟨eS⟩ := nonempty_quotient_center_equiv_fusionZStar M
  have hcat : Blueprint.Catalog ((M ⧸ pPrimeCore 2 M) ⧸ center (M ⧸ pPrimeCore 2 M)) :=
    SectionRank.catalog_of_mulEquiv eS (catalog_fusionZStar_of_isPComponent hK hbtop hMb hMp)
  have hle := pRank_le_one_of_quasisimple hCT hPFS hMq (HeK.isPGroup_center_quotient M) hcat hHe
    hσ hPF hP hPne (LieType.CurtisTits.lieModel_of_mulEquiv eZ htype)
  rw [← pRank_fusionZStar_congr eO] at hle
  omega

end CFSG.ComponentClassification.GrSLit.L34Sec5S
