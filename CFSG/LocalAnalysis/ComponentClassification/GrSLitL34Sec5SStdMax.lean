module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5SStdInputs
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeMax
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitInputs

public section

namespace CFSG.ComponentClassification.GrSLit.L34Sec5S

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)

variable {G : Type} [Group G] [Finite G]

theorem card_fusionZStar_lt_of_fixed {a b : G} {M T : Subgroup G} (ha : orderOf a = 2)
    (hb : orderOf b = 2) (hab : a * b = b * a) (hMb : M ≤ centralizer ({b} : Set G))
    (hMp : IsPComponent 2 (M.subgroupOf (centralizer ({b} : Set G))))
    (hMa : conjugate M a = M) (hTM : T ≤ M ⊓ centralizer ({a} : Set G))
    (hTp : IsPComponent 2 (T.subgroupOf (M ⊓ centralizer ({a} : Set G))))
    (hlt : (pPrimeCore 2 T).index < (pPrimeCore 2 M).index) :
    Nat.card (T ⧸ Open.fusionZStar T) < Nat.card (M ⧸ Open.fusionZStar M) := by
  have h : SimpleFixedComponents (fun K _ => Nat.card K ≤ Nat.card (M ⧸ Open.fusionZStar M))
      (fun K _ => Nat.card K < Nat.card (M ⧸ Open.fusionZStar M)) := by
    intro S _ _ _ _ hτ σ _ P _ _ hPne
    have h1 : Nat.card (P ⧸ Open.fusionZStar P) ≤ Nat.card P :=
      Nat.le_of_dvd Nat.card_pos (Subgroup.card_quotient_dvd_card _)
    have h2 : Nat.card P < Nat.card S :=
      lt_of_not_ge fun h => hPne (Subgroup.eq_top_of_le_card _ h)
    omega
  exact properFixedComponents_of_simple
    (fun _ _ _ _ e h => by rwa [Nat.card_congr e.toEquiv])
    (fun _ _ _ _ e h => by rwa [Nat.card_congr e.toEquiv])
    h G a b M T ha hb hab hMb hMp hMa hTM hTp hlt le_rfl

theorem not_suzONan_of_fixed (hC4 : SuzONanNotProperFixedCatalog)
    (hK : Assembly.KProper Blueprint.Catalog G) {a b : G} {M T : Subgroup G}
    (ha : orderOf a = 2) (hb : orderOf b = 2) (hab : a * b = b * a)
    (hbtop : centralizer ({b} : Set G) ≠ ⊤) (hMb : M ≤ centralizer ({b} : Set G))
    (hMp : IsPComponent 2 (M.subgroupOf (centralizer ({b} : Set G))))
    (hMa : conjugate M a = M) (hTM : T ≤ M ⊓ centralizer ({a} : Set G))
    (hTp : IsPComponent 2 (T.subgroupOf (M ⊓ centralizer ({a} : Set G))))
    (hlt : (pPrimeCore 2 T).index < (pPrimeCore 2 M).index) :
    ¬ Blueprint.NativeSporadic.IsSporadic (T ⧸ Open.fusionZStar T) .Suz ∧
      ¬ Blueprint.NativeSporadic.IsSporadic (T ⧸ Open.fusionZStar T) .ONan := by
  have h : SimpleFixedComponents (fun K _ => Blueprint.Catalog K)
      (fun K _ => ¬ Blueprint.NativeSporadic.IsSporadic K .Suz ∧
        ¬ Blueprint.NativeSporadic.IsSporadic K .ONan) :=
    fun S _ _ hs hna hc σ hσ P hPF hP hPne => hC4 S hs hna hc σ hσ P hPF hP hPne
  exact properFixedComponents_of_simple
    (fun _ _ _ _ e hc => SectionRank.catalog_of_mulEquiv e hc)
    (fun _ _ _ _ e h => ⟨fun ⟨f⟩ => h.1 ⟨e.symm.trans f⟩, fun ⟨f⟩ => h.2 ⟨e.symm.trans f⟩⟩)
    h G a b M T ha hb hab hMb hMp hMa hTM hTp hlt
    (catalog_fusionZStar_of_isPComponent hK hbtop hMb hMp)

theorem lieModel_two_mul_of_fixed (hC5 : L3TwoPowProperFixedCatalog)
    (hK : Assembly.KProper Blueprint.Catalog G) {a b : G} {M T : Subgroup G}
    (ha : orderOf a = 2) (hb : orderOf b = 2) (hab : a * b = b * a)
    (hbtop : centralizer ({b} : Set G) ≠ ⊤) (hMb : M ≤ centralizer ({b} : Set G))
    (hMp : IsPComponent 2 (M.subgroupOf (centralizer ({b} : Set G))))
    (hMa : conjugate M a = M) (hTM : T ≤ M ⊓ centralizer ({a} : Set G))
    (hTp : IsPComponent 2 (T.subgroupOf (M ⊓ centralizer ({a} : Set G))))
    (hlt : (pPrimeCore 2 T).index < (pPrimeCore 2 M).index) {n : ℕ} (hn : 4 ≤ n)
    (hev : Even n) (hT : Blueprint.LieModel (T ⧸ Open.fusionZStar T) .PSL 3 2 n) :
    Blueprint.LieModel (M ⧸ Open.fusionZStar M) .PSL 3 2 (2 * n) := by
  by_contra hne
  have h : SimpleFixedComponents
      (fun K _ => Blueprint.Catalog K ∧ ¬ Blueprint.LieModel K .PSL 3 2 (2 * n))
      (fun K _ => ¬ Blueprint.LieModel K .PSL 3 2 n) :=
    fun S _ _ hs hna hc σ hσ P hPF hP hPne hL =>
      hc.2 (hC5 n hn hev S hs hna hc.1 σ hσ P hPF hP hPne hL)
  exact properFixedComponents_of_simple
    (fun _ _ _ _ e hc => ⟨SectionRank.catalog_of_mulEquiv e hc.1,
      fun hL => hc.2 (LieType.CurtisTits.lieModel_of_mulEquiv e hL)⟩)
    (fun _ _ _ _ e h hL => h (LieType.CurtisTits.lieModel_of_mulEquiv e hL))
    h G a b M T ha hb hab hMb hMp hMa hTM hTp hlt
    ⟨catalog_fusionZStar_of_isPComponent hK hbtop hMb hMp, hne⟩ hT

omit [Finite G] in
theorem centralizer_ne_top_of_not_mem_center {b : G} (hbZ : b ∉ center G) :
    centralizer ({b} : Set G) ≠ ⊤ := fun htop =>
  hbZ (mem_center_iff.mpr fun g => mem_centralizer_singleton_iff.mp (htop ▸ mem_top g))

theorem gsWeakMaximalComponent_of_suzONan (hS : SchreierFor Blueprint.Catalog)
    (hC4 : SuzONanNotProperFixedCatalog) (hG : L34BaseSetting G) {b : G} {M : Subgroup G}
    (hb : orderOf b = 2) (hMb : M ≤ centralizer ({b} : Set G))
    (hMp : IsPComponent 2 (M.subgroupOf (centralizer ({b} : Set G))))
    (htype : Blueprint.NativeSporadic.IsSporadic (M ⧸ Open.fusionZStar M) .Suz ∨
      Blueprint.NativeSporadic.IsSporadic (M ⧸ Open.fusionZStar M) .ONan) :
    GSWeakMaximalComponent M := by
  obtain ⟨hsimple, hna, hK, -, -, -, -, -⟩ := id hG
  have := hsimple
  refine ⟨⟨b, hb, hMb, hMp⟩, fun M' hM => ?_⟩
  induction hM with
  | refl => exact ⟨MulEquiv.refl _⟩
  | @tail L' M' _ hst ih =>
    obtain ⟨a', b', hC⟩ := hst
    obtain ⟨e₁⟩ := ih
    have hb'Z : b' ∉ center G := GSLit.not_mem_center_of_orderOf_eq_two hna hC.2.1
    rcases gsWeakCorr_type_dichotomy hS hK hC hb'Z with he | ⟨hMa, hTM, hTp, hlt, ⟨e⟩⟩
    · obtain ⟨e₂⟩ := he
      exact ⟨e₁.trans e₂⟩
    · exfalso
      have h := not_suzONan_of_fixed hC4 hK hC.1 hC.2.1 hC.2.2.1
        (centralizer_ne_top_of_not_mem_center hb'Z) hC.2.2.2.2.2.1 hC.2.2.2.2.2.2.1 hMa hTM
        hTp hlt
      rcases htype with hS | hO
      · obtain ⟨f⟩ : Nonempty (M ⧸ Open.fusionZStar M ≃* Blueprint.NativeSporadic.Carrier .Suz) :=
          hS
        exact h.1 ⟨((e₁.trans e).symm).trans f⟩
      · obtain ⟨f⟩ : Nonempty (M ⧸ Open.fusionZStar M ≃* Blueprint.NativeSporadic.Carrier .ONan) :=
          hO
        exact h.2 ⟨((e₁.trans e).symm).trans f⟩

end CFSG.ComponentClassification.GrSLit.L34Sec5S
