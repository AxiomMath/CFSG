module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.G24ModelChev
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.G24ModelAction
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.G24AutRep
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.IsoOfGeneratorCard
public import CFSG.Sporadic.Co1Block.TwoBD
public import CFSG.Timmesfeld.Orders.ExceptionalUntwisted
public import Certificates.Certificate27211

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.G24Model

open scoped Pointwise

attribute [local instance] CFSG.EvenSporadicStandard.Induction.AutBound.glVecAction

open CFSG.Fischer CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.Quasithin.G2U
  CFSG.Sporadic.Co1Block CFSG.Monster.B.Co2.Native CFSG.EvenSporadicStandard.G24Aut
  CFSG.EvenSporadicStandard.Induction.AutBound

section Gens


theorem Cmat_eq_closure : Cmat = Subgroup.closure genSet := by
  refine le_antisymm Cmat_le_closure ((Subgroup.closure_le _).2 ?_)
  rintro u ⟨j, hj⟩
  obtain ⟨u', hu', hj'⟩ := exists_gen_unit j
  have : u = u' := Units.ext (hj.trans hj'.symm)
  exact this ▸ hu'

noncomputable def genElt (j : Fin 16) : GL (Fin 14) F4 := (exists_gen_unit j).choose

theorem genElt_spec (j : Fin 16) :
    genElt j ∈ Cmat ∧ (genElt j : Matrix (Fin 14) (Fin 14) F4) = Gmat j :=
  (exists_gen_unit j).choose_spec

theorem genElt_mem (j : Fin 16) : genElt j ∈ genSet := ⟨j, (genElt_spec j).2⟩

noncomputable def gE (l : Nat) : Subgroup.closure genSet :=
  if h : l < 16 then ⟨genElt ⟨l, h⟩, Subgroup.subset_closure (genElt_mem _)⟩ else 1

end Gens

section Act


theorem exists_pi : ∃ π : Subgroup.closure genSet →* Equiv.Perm (Fin nLines),
    ∀ (g : Subgroup.closure genSet) (k : Fin nLines), (g : GL (Fin 14) F4) • lineOf k =
      lineOf (π g k) :=
  exists_hexHom (S := genSet) fun _ hu => hu

theorem hom_apply_gE {π : Subgroup.closure genSet →* Equiv.Perm (Fin nLines)}
    (hπ : ∀ (g : Subgroup.closure genSet) (k : Fin nLines),
      (g : GL (Fin 14) F4) • lineOf k = lineOf (π g k)) (j : Fin 16) (k : Fin nLines) :
    π (gE j) k = pgFin j k := by
  have h : gE (j : Nat) = ⟨genElt j, Subgroup.subset_closure (genElt_mem j)⟩ := by
    simp [gE, j.2]
  rw [h]
  exact hom_apply_gen hπ (genElt_mem j) (genElt_spec j).2 k

theorem rep_gE {π : Subgroup.closure genSet →* Equiv.Perm (Fin nLines)}
    (hπ : ∀ (g : Subgroup.closure genSet) (k : Fin nLines),
      (g : GL (Fin 14) F4) • lineOf k = lineOf (π g k)) :
    ∀ l < pgArrs.size, CFSG.Monster.B.Co2.Rep nn pgArrs[l]! (π (gE l)) := by
  intro l hl x
  have hl16 : l < 16 := by simpa [pgArrs] using hl
  have h := hom_apply_gE hπ ⟨l, hl16⟩ x
  have e : gE l = gE ((⟨l, hl16⟩ : Fin 16) : Nat) := rfl
  rw [e, h]
  rw [pgArrs, getElem!_ofFn' _ hl16, getElem!_ofFn' _ x.2]
  rfl

end Act

section Match


theorem matchOK_parts : waWord.all (· < 16) = true ∧ wbWord.all (· < 16) = true ∧
    eqA nn (prodA pgArrs waWord) xa = true ∧ eqA nn (prodA pgArrs wbWord) ya = true := by
  have h := Certificates.certificate27211
  unfold matchOK at h
  simp only [Bool.and_eq_true] at h
  exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩

end Match

section Main


theorem prod_gE {π : Subgroup.closure genSet →* Equiv.Perm (Fin nLines)}
    (hπ : ∀ (g : Subgroup.closure genSet) (k : Fin nLines),
      (g : GL (Fin 14) F4) • lineOf k = lineOf (π g k)) :
    π ((waWord.map gE).prod) = xBar ∧ π ((wbWord.map gE).prod) = yBar := by
  obtain ⟨hwa, hwb, hxa, hya⟩ := matchOK_parts
  have hsize : pgArrs.size = 16 := by simp [pgArrs]
  have hlt : ∀ {w : List Nat}, w.all (· < 16) = true → ∀ l ∈ w, l < pgArrs.size := by
    intro w hw l hl
    rw [hsize]
    exact of_decide_eq_true (List.all_eq_true.1 hw l hl)
  have hrep := rep_gE hπ
  have key : ∀ {w : List Nat} {t : Array Nat} {g : Equiv.Perm (Fin nLines)},
      w.all (· < 16) = true → CFSG.Monster.B.Co2.Rep nn t g →
        eqA nn (prodA pgArrs w) t = true → π ((w.map gE).prod) = g := by
    intro w t g hw hg heq
    have h1 := rep_prodA (gs := fun l => π (gE l)) hrep w (hlt hw)
    have h2 := (CFSG.Monster.B.Co2.eqA_iff h1 hg).1 heq
    rw [map_list_prod, List.map_map]
    exact h2
  exact ⟨(key hwa (strong_rep (by norm_num : 0 < 6)) hxa).trans strong0_eq,
    (key hwb (strong_rep (by norm_num : 1 < 6)) hya).trans strong1_eq⟩

theorem card_closure_genSet : Nat.card (Subgroup.closure genSet) = 251596800 := by
  rw [← Cmat_eq_closure, Cmat, Subgroup.card_map_of_injective e₀.injective,
    CFSG.Timmesfeld.ExceptionalOrders.card_adjointGroup_G2, Nat.card_eq_fintype_card, F4.card]
  decide

theorem twoBD_equiv : Nonempty (↥twoBD ≃* Subgroup.closure genSet) := by
  obtain ⟨π, hπ⟩ := exists_pi
  obtain ⟨ha, hb⟩ := prod_gE hπ
  have himg : π '' ({(waWord.map gE).prod, (wbWord.map gE).prod} :
      Set (Subgroup.closure genSet)) = {xBar, yBar} := by
    rw [Set.image_pair, ha, hb]
  have hcard : Nat.card (Subgroup.closure genSet) ≤
      Nat.card (Subgroup.closure (π '' ({(waWord.map gE).prod, (wbWord.map gE).prod} :
        Set (Subgroup.closure genSet)))) := by
    rw [himg]
    show _ ≤ Nat.card twoBD
    rw [card_twoBD, card_closure_genSet]
  have : Finite (Subgroup.closure genSet) := Nat.finite_of_card_ne_zero (by
    rw [card_closure_genSet]
    norm_num)
  obtain ⟨-, hinj, hrange⟩ := injective_and_range_of_card_le π
    {(waWord.map gE).prod, (wbWord.map gE).prod} hcard
  rw [himg] at hrange
  exact ⟨((MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hrange)).symm⟩

theorem twoBD_equiv_adjointQuotient : Nonempty (↥twoBD ≃* AdjointQuotient .G2 F4) := by
  obtain ⟨e1⟩ := twoBD_equiv
  have hZ : Subgroup.center ↥(adjointGroup .G2 F4) = ⊥ :=
    CFSG.LieType.Chevalley.center_adjointGroup_eq_bot
  let e2 : ↥(Subgroup.closure genSet) ≃* ↥Cmat := MulEquiv.subgroupCongr Cmat_eq_closure.symm
  let e3 : ↥Cmat ≃* ↥(adjointGroup .G2 F4) :=
    (Subgroup.equivMapOfInjective _ e₀.toMonoidHom e₀.injective).symm
  let e4 : ↥(adjointGroup .G2 F4) ≃* AdjointQuotient .G2 F4 :=
    ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm
  exact ⟨e1.trans (e2.trans (e3.trans e4))⟩

theorem g24Model_proved : LieModel ↥twoBD .G2 0 2 2 := by
  refine Or.inr (Or.inl ⟨rfl, by decide, ⟨Nat.prime_two, by norm_num, rfl, by norm_num⟩, ?_⟩)
  exact ⟨F4, inferInstance, inferInstance, by rw [Nat.card_eq_fintype_card, F4.card]; norm_num,
    twoBD_equiv_adjointQuotient⟩

end Main

end CFSG.EvenSporadicStandard.G24Model
