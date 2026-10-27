module

public import CFSG.LocalAnalysis.StandardType.TitsThreeOvergroup
public import Certificates.Certificate31072
import CFSG.Adapters.TauCetiLieModels
import CFSG.Models.Blueprint
public import CFSG.Certificates.CosetTablePresented
public import CFSG.GH74.KGroups.L33Inputs
import CFSG.HardMathSupport.Dickson.BMRows.M13L33Base

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TenThirteen

open CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four CFSG.AGLEmbedding.FusD2
open CFSG.StandardType.TitsOvergroup CFSG.StandardType.TitsThree CFSG.StandardType.TitsGenerators
open CFSG.HardMathSupport.Dickson.BMRows.M13L33 CFSG.CosetTable
open CFSG.LocalAnalysis.RankThreeTheoremC.TenThirteen.TitsL33

@[expose] def threeFourTwoQThree : TauCeti.PrimePower := ⟨3, 1, Nat.prime_three, Nat.one_pos⟩

theorem valid_A_two_threeFourTwoQThree : (TauCeti.LieTypeIndex.A 2 threeFourTwoQThree).Valid := by
  simp [threeFourTwoQThree]

@[expose] def threeFourTwoL33Index : TauCeti.ValidLieTypeIndex :=
  ⟨.A 2 threeFourTwoQThree, valid_A_two_threeFourTwoQThree⟩

private theorem nonempty_catL33_mulEquiv_QP :
    Nonempty ((TauCeti.CFSGIndex.lie threeFourTwoL33Index).Group ≃*
      CFSG.GH74.KGroups.L33.QP.originalSubgroup) := by
  have hL := CFSG.Models.lieModel_A 2 threeFourTwoQThree valid_A_two_threeFourTwoQThree
    (MulEquiv.refl _)
  exact CFSG.GH74.KGroups.L33.equiv_of_lieModel (CFSG.Models.LieModel.toBlueprint (by decide) hL)

private theorem wordVal_relWord {G : Type*} [Group G] (S : List G) {a b : List ℤ}
    (ha : ∀ z ∈ a, z ≠ 0) (hb : ∀ z ∈ b, z ≠ 0) (r : List (Fin 2 × Bool)) :
    wordVal S (relWord a b r) = evalRel ![wordVal S a, wordVal S b] r := by
  induction r with
  | nil => simp [relWord, evalRel, wordVal]
  | cons l r ih =>
    have e1 : relWord a b (l :: r) = letterWord a b l ++ relWord a b r := by
      simp [relWord]
    have e2 : evalRel ![wordVal S a, wordVal S b] (l :: r) =
        cond l.2 (![wordVal S a, wordVal S b] l.1) (![wordVal S a, wordVal S b] l.1)⁻¹ *
          evalRel ![wordVal S a, wordVal S b] r := by
      simp [evalRel]
    rw [e1, e2, wordVal_append, ih]
    congr 1
    obtain ⟨i, s⟩ := l
    fin_cases i <;> cases s <;>
      simp [letterWord, wordVal_invWord S _ ha, wordVal_invWord S _ hb]

theorem nonempty_pairSide_mulEquiv_catL33
    {k : ℕ} (hk : k < 2) :
    Nonempty (↥(pairSide pairData titsS k) ≃*
      (TauCeti.CFSGIndex.lie threeFourTwoL33Index).Group) := by
  classical
  have hc : titsThreeCheck () = true := Certificates.certificate465005
  obtain ⟨hpair, -, hloc⟩ := titsThreeCheck_parts hc
  obtain ⟨hInv, -, -, -, hSide, -, -, -⟩ := pairCheck_parts hpair
  have hS := sound_pairData hInv
  have hgs : ∀ j, TabRep ((lLocalData k ()).gT.getD j (idTab (lLocalData k ()).n))
      ((sideGensVals k).getD j 1) := sideGens_rep hS k
  have hInvk : Certificates.MaxD2Perm.checkInv (lLocalData k ()) = true := by
    have h := hloc k hk
    simp only [Certificates.MaxD2Perm.check, Bool.and_eq_true] at h
    exact h.1.1.1.1.1.1.1
  have hgi := CFSG.AGLEmbedding.MaxD2.giT_rep hgs hInvk
  have hrep : ∀ w, TabRep (Certificates.MaxD2Perm.wT (lLocalData k ()) w)
      (wordVal (sideGensVals k) w) := CFSG.AGLEmbedding.MaxD2.wT_rep hgs hgi
  have h31 : l33CheckAt k = true := by
    have h := Certificates.certificate31072
    simp only [titsL33Check, allBelow_eq_true] at h
    exact h k hk
  simp only [l33CheckAt, Bool.and_eq_true, List.all_eq_true, beq_iff_eq, Bool.not_eq_true',
    beq_eq_false_iff_ne] at h31
  obtain ⟨hrels, ha1⟩ := h31
  have haz : ∀ z ∈ l33AWords.getD k [], z ≠ 0 := by
    interval_cases k <;> decide
  have hbz : ∀ z ∈ l33BWords.getD k [], z ≠ 0 := by
    interval_cases k <;> decide
  set aW := l33AWords.getD k [] with haW
  set bW := l33BWords.getD k [] with hbW
  set f : Fin 2 → Equiv.Perm (Fin 1755) :=
    ![wordVal (sideGensVals k) aW, wordVal (sideGensVals k) bW] with hf
  have hfrel : ∀ r ∈ l33Rels, evalRel f r = 1 := by
    intro r hr
    rw [hf, ← wordVal_relWord _ haz hbz]
    exact (hrep _).perm_eq (hrels r hr ▸ TabRep.idTab)
  have hf0 : f 0 ≠ 1 := by
    intro h1
    have h1' : wordVal (sideGensVals k) aW = 1 := h1
    refine ha1 ((hrep aW).tab_eq ?_)
    rw [h1']
    exact TabRep.idTab
  set φ := l33Hom f hfrel with hφ
  have hφinj : Function.Injective φ := by
    haveI := isSimple_pg
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal φ.ker with h | h
    · exact (MonoidHom.ker_eq_bot_iff φ).mp h
    · exfalso
      apply hf0
      rw [← l33Hom_of f hfrel 0]
      exact MonoidHom.mem_ker.mp (h ▸ Subgroup.mem_top _)
  have hmem : ∀ g ∈ sideGensVals k, g ∈ pairSide pairData titsS k := fun g hg =>
    Subgroup.subset_closure hg
  have hrange : φ.range ≤ pairSide pairData titsS k := by
    rw [hφ, range_l33Hom, Subgroup.closure_le]
    rintro _ ⟨i, rfl⟩
    fin_cases i
    · exact wordVal_mem _ _ hmem aW
    · exact wordVal_mem _ _ hmem bW
  have hcardPG : Nat.card (PG 2 l33Rels) = 5616 := by
    rw [Nat.card_congr l33Equiv.toEquiv,
      CFSG.GH74.KGroups.card_group _ CFSG.GH74.KGroups.L33.QP13_ok,
      CFSG.GH74.KGroups.L33.QP13_valid.2]
  have hcardL : Nat.card ↥(pairSide pairData titsS k) = 5616 :=
    (card_pairSide hS hSide (k := k) (by simp [pairData]; omega)).trans (sideOrder_getD hk).1
  have hcardR : Nat.card ↥φ.range = 5616 := by
    rw [← hcardPG]
    exact (Nat.card_congr (MonoidHom.ofInjective hφinj).toEquiv).symm
  have heq : φ.range = pairSide pairData titsS k :=
    Subgroup.eq_of_le_of_card_ge hrange (by rw [hcardL, hcardR])
  obtain ⟨e₁⟩ := CFSG.GH74.KGroups.L33.equiv_P13_P
  obtain ⟨e₂⟩ := nonempty_catL33_mulEquiv_QP
  exact ⟨(((MulEquiv.subgroupCongr heq).symm.trans (MonoidHom.ofInjective hφinj).symm).trans
    l33Equiv).trans (e₁.trans e₂.symm)⟩

end CFSG.LocalAnalysis.RankThreeTheoremC.TenThirteen
