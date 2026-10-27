module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch5Sec2LocalProp526
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch5Sec2LocalProp526Bd
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch5Sec2LocalProp526TrS331

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin
open CFSG.GH74.QTGen4.DSGen4

@[expose] def Stmt5_2_6_L2K_rank2_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T M L V H B D L₂ : Subgroup G) (n : ℕ),
    Hyp5_2_4 G T M L V H B D L₂ n → ¬ IsBenderAny (O2Q (oTwoUpper H)) →
    (∃ P : Subgroup G, IsMaxParabolicOver (oTwoUpper H) (T ⊓ oTwoUpper H) P ∧
      quasithinIsCComponent L₂ P) →
    DSALocConcl_F4 L L₂ (sec52S M H) → False

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G]

theorem perfectCore_G2_eq_F4 (h331 : Stmt3_3_1_F4) (hR : L2RankOneSylowFact)
    (hF : RankOneListedFacts.{0}) (hF11 : StmtF11_5_2_F4) (hbor : Stmt5_2_6_borel_F4)
    {T M L V H B D L₂ : Subgroup G} {n : ℕ} (hyp : Hyp5_2_4 G T M L V H B D L₂ n) :
    perfectCore (sec52G2 M H D L₂) = L₂ := by
  have h111 := Hyp111R.of_hyp111 hF (hF11 G T M L V H B D L₂ n hyp)
  obtain ⟨-, hG2, -⟩ := hyp.parabolics_eq_F4 h331 hR (hbor G T M L V H B D L₂ n hyp)
  have hL₂p : ⁅L₂, L₂⁆ = L₂ := by
    obtain ⟨K₁, hK₁, -, hcase⟩ := hyp.choice
    rcases hcase with ⟨-, rfl⟩ | ⟨-, -, P, -, hL₂P⟩
    · exact hK₁.2.1
    · exact hL₂P.2.1
  rw [hG2]
  exact Vol2.Ch11.SecS.perfectCore_sup_eq hL₂p (F1.isSolvable_bigB h111)
    (F1.bigB_le_normalizer_left h111).2

namespace Hyp5_2_4

variable {T M L V H B D L₂ : Subgroup G} {n : ℕ}

theorem cases_of_loc_F4 (h331 : Stmt3_3_1_F4) (hR : L2RankOneSylowFact)
    (hbor : Stmt5_2_6_borel_F4) (hyp : Hyp5_2_4 G T M L V H B D L₂ n)
    (hA1 : F112A1Loc L L₂)
    (hamal : IsAmalgamOfGroup (RankTwoAmalgam.ofSubgroups (L ⊔ bigB L L₂ (sec52S M H))
      (L₂ ⊔ bigB L L₂ (sec52S M H))) (IsLieOverTwo .PSL 3 2)) :
    Cases5_2_6 (sec52Alpha M L H B D L₂) L L₂ n := by
  obtain ⟨hb1, ht1, hb2, ht2⟩ := hA1
  have hfn := hyp.eq_of_isLin2Type_L ht1
  subst hfn
  exact Or.inl ⟨hyp.isAmalgamOfGroup_of_orient_F4 h331 hR hbor (Or.inl ⟨rfl, rfl⟩) hamal,
    hb1, ht1, hb2, ht2⟩

end Hyp5_2_4

theorem stmt5_2_6_tr_of_F4 (h331 : Stmt3_3_1_F4)
    (hR : L2RankOneSylowFact) (hF : RankOneListedFacts.{0}) (hF11 : StmtF11_5_2_F4)
    (hbor : Stmt5_2_6_borel_F4) (h524 : Stmt5_2_4_F4) (h510 : Stmt5_1_10_F4)
    (h38 : Vol2Native.A38ForSQTKCat) (hU3 : FactU3Cover) (hC58 : TheoremC58)
    (h317 : AS317Sylow) (h512 : Stmt5_1_2_F4) (hrk2 : Stmt5_2_6_L2K_rank2_F4) :
    Stmt5_2_6_tr_F4 := by
  rintro G _ _ T M L V H B D L₂ n hyp ⟨hloc, hamal⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := hyp.toHyp5_0_1
  have hN := hyp.notation59
  have hA1 : F112A1Loc L L₂ := hloc.1
  have hSL : sec52S M H ≤ L := hloc.2.1.2.2.1
  have hSL₂ : sec52S M H ≤ L₂ := hloc.2.1.2.2.2
  have hL₂K : L₂ = oTwoUpper H := by
    obtain ⟨K₁, hK₁, hKeq, hcase⟩ := hyp.choice
    rcases hcase with ⟨hbend, hL₂K₁⟩ | ⟨hnb, hK₁K, P, hP, hL₂P⟩
    · subst K₁
      exact hyp.eq_oTwoUpper_of_bender_F4 h38 hF hU3 h510 h524 hK₁ hKeq hbend (Or.inl hSL₂)
    · subst K₁
      exact (hrk2 G T M L V H B D L₂ n hyp hnb ⟨P, hP, hL₂P⟩ hloc).elim
  subst hL₂K
  set S := sec52S M H with hSdef
  set K := oTwoUpper H with hKdef
  have hG2 := perfectCore_G2_eq_F4 h331 hR hF hF11 hbor hyp
  have hTS := pCoreOf_sup_T_eq hyp.toHyp5_1_8
  have hBodd : Odd (Nat.card ↥(B ⊓ K)) :=
    Odd.of_dvd_nat hN.1.2.1 (Subgroup.card_dvd_of_le inf_le_left)
  have hBL : B ⊓ K ≤ Subgroup.normalizer (L : Set G) :=
    (inf_le_left.trans (hN.1.1.trans inf_le_left)).trans h.normal
  have hG1eq : sec52G1 M L H B K = L ⊔ (B ⊓ K) := by
    show L ⊔ S ⊔ (B ⊓ K) = L ⊔ (B ⊓ K)
    rw [sup_eq_left.mpr hSL]
  have hG2eq : sec52G2 M H D K = K ⊔ D := by
    show D ⊔ S ⊔ K = K ⊔ D
    apply le_antisymm
    · exact sup_le (sup_le le_sup_right (hSL₂.trans le_sup_left)) le_sup_left
    · exact sup_le le_sup_right (le_sup_left.trans le_sup_left)
  refine ⟨rfl, hG2.symm, ?_, ?_, hyp.cases_of_loc_F4 h331 hR hbor hA1 hamal, hTS,
    Or.inl ⟨hSL, hSL₂, by rw [sup_eq_left.mpr hSL], by rw [sup_eq_left.mpr hSL₂]⟩⟩
  · rw [hG1eq]
    exact pCoreOf_sup_of_odd hBL hBodd
  · rw [hG2eq]
    exact pCoreOf_sup_of_odd hyp.D_le hN.2.1.2.1

end CFSG.Quasithin.H13
