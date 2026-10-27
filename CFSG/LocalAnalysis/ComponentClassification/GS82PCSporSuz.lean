module

public import CFSG.LocalAnalysis.ComponentClassification.GS82PCSporOrd
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.ResidualA8Proof
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog7CF24Main

public section

set_option linter.unusedSectionVars false

namespace CFSG.ComponentClassification.GS82PumpInputs.PCSpor

open CFSG Subgroup CFSG.Blueprint CFSG.ComponentClassification.CatLeaf HarrisLit.T1.SporRow
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

theorem eq_eight_of_factorial_div_two {n : ℕ} (h : n.factorial / 2 = 20160) : n = 8 := by
  by_cases hn : n < 9
  · interval_cases n <;> simp_all [Nat.factorial]
  · have h1 : Nat.factorial 9 ≤ n.factorial := Nat.factorial_le (not_lt.1 hn)
    have h2 : Nat.factorial 9 / 2 ≤ n.factorial / 2 := Nat.div_le_div_right h1
    rw [h] at h2
    exact absurd h2 (by decide)


theorem false_of_suz (hMcard : Nat.card Open.MonsterY443Derived = Open.monsterOrder)
    (hfree : CatalogueU.SporadicOddCoreFree .Suz)
    {Y : Type} [Group Y] [Finite Y] {β : MulAut Y} {T : Subgroup Y} (h : Setting Y β T)
    (hTtop : T ≠ ⊤) (hZ : Nat.card (center Y) = 2)
    (e : Y ⧸ center Y ≃* NativeSporadic.Carrier .Suz) : False := by
  have : IsSimpleGroup (Quot Y) := isSimpleGroup_quot h.quasisimple h.oddCore
  have hna := nonabelian_quot h.quasisimple h.oddCore
  set e' := (quotEquiv h.oddCore).trans e
  obtain ⟨σ, hI⟩ := exists_image_of_oddCore h hTtop (oddCore_fixed_eq_bot hfree hna e')
  have hσ2 : orderOf σ = 2 :=
    orderOf_eq_prime (by rw [sq]; exact MulEquiv.ext fun y => hI.proper.1 y) hI.proper.ne_one
  obtain ⟨hd, hin, hout⟩ := SporTable.comp_data hMcard hfree hna e' hI.proper
  obtain ⟨eT⟩ := hI.fus
  set P := T.map (rho Y) with hPdef
  set c := Nat.card (P ⧸ Open.fusionZStar P) with hcdef
  have hcT : Nat.card (T ⧸ Open.fusionZStar T) = c := Nat.card_congr eT.toEquiv
  have hrow : CatFC.SporadicInnerRow .Suz c ∨ CatFC.SporadicOuterRow .Suz c := by
    by_cases hσ : σ ∈ (MulAut.conj : Quot Y →* MulAut (Quot Y)).range
    · exact Or.inl (hin hσ)
    · exact Or.inr (hout hσ)
  rcases h.typC with ⟨t, n, p, f, hp, hp2, -, hLm⟩ | ⟨n, hn, hA⟩ | ⟨hL, hEA⟩
  ·
    have hO := oddLieOrder_of_lieModel hp hp2 hLm
    rw [hcT] at hO
    obtain ⟨h1, h2⟩ := SporTable.tableExcl_Suz c hO hd
    rcases hrow with hr | hr
    · exact h1 hr
    · exact h2 hr
  ·
    obtain ⟨-, -, ⟨eA⟩⟩ := hA
    have : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.2 (by omega)
    have hcn : c = n.factorial / 2 := by
      rw [← hcT, card_fusionZStar_eq, Nat.card_congr eA.toEquiv, Nat.card_eq_fintype_card,
        card_alternatingGroup, Fintype.card_fin]
    simp only [CatFC.SporadicInnerRow, CatFC.SporadicOuterRow] at hrow
    rcases hrow with hr | hr | hr
    · have hn8 : n = 8 := eq_eight_of_factorial_div_two (hcn ▸ hr)
      subst hn8
      obtain ⟨eP⟩ := hI.quotP
      obtain ⟨eTZ⟩ := GrSLit.nonempty_quotient_center_equiv_fusionZStar T
      exact CatFC.heSuzONNoAltEight_proved (Quot Y) inferInstance hna (Or.inr (Or.inl ⟨e'⟩)) σ
        hσ2 _ hI.compP ⟨eP.symm.trans (eT.symm.trans (eTZ.symm.trans eA))⟩
    · exact factorial_div_two_ne (c := 95040) (N := 11) (by decide) (by decide) n (hcn ▸ hr)
    · exact factorial_div_two_ne (c := 604800) (N := 12) (by decide) (by decide) n (hcn ▸ hr)
  ·
    set eO := equivQuotOddCore hI.oddCoreT
    have eZ : T ⧸ center T ≃* (T ⧸ pPrimeCore 2 T) ⧸ center (T ⧸ pPrimeCore 2 T) :=
      QuotientGroup.congr _ _ eO (Subgroup.map_center_eq eO)
    have hLT : LieModel (T ⧸ center T) .PSL 3 2 2 := Blueprint.LieModel.of_mulEquiv eZ.symm hL
    have hFix : fixedSubgroup β = CatFactsL4U4.OutInv.fixSub β := by
      ext x
      exact Iff.rfl
    have hge := GSThmB.cf24CenterGe Y h.quasisimple (isPGroup_center_of_pPrimeCore_eq_bot h.oddCore)
      ⟨e⟩ β (MulEquiv.ext h.inv) T (hFix ▸ h.le) (hFix ▸ hI.compT) hLT
    have hcard : Nat.card (center T) ≤ 2 := by
      rw [← hZ, ← Subgroup.card_map_of_injective T.subtype_injective]
      exact Subgroup.card_le_of_le hge
    have hcard' : Nat.card (center (T ⧸ pPrimeCore 2 T)) ≤ 2 := by
      rw [← Subgroup.map_center_eq eO, Subgroup.card_map_of_injective eO.injective]
      exact hcard
    exact hEA (isElementaryAbelian_center_of_card_le_two hcard')

end CFSG.ComponentClassification.GS82PumpInputs.PCSpor
