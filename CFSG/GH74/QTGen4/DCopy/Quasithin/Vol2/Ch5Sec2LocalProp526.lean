module

public import CFSG.GH74.QTGen4.DSGen4.Statements
public import CFSG.Quasithin.Vol2.Ch5Sec2LocalProp526
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch5Statements
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch5StatementsB
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch5Sec2LocalProp526S331
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch5StatementsBS331
public import CFSG.Quasithin.EmptyFaithful.S1422Setting

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits
open CFSG.GH74.QTGen4.DSGen4

@[expose] def DSALocConcl_F4 {G : Type} [Group G] (L1 L2 S : Subgroup G) : Prop :=
  F112A1Loc L1 L2 ∧ (perfectCore L1 = L1 ∧ perfectCore L2 = L2 ∧ S ≤ L1 ∧ S ≤ L2) ∧
    ¬ centerOf S ≤ Subgroup.centralizer (L1 : Set G) ∧
    ¬ centerOf S ≤ Subgroup.centralizer (L2 : Set G)

@[expose] def Stmt5_2_6_tr_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T M L V H B D L₂ : Subgroup G) (n : ℕ),
    Hyp5_2_4 G T M L V H B D L₂ n →
    (DSALocConcl_F4 L L₂ (sec52S M H) ∧
      IsAmalgamOfGroup (RankTwoAmalgam.ofSubgroups (L ⊔ bigB L L₂ (sec52S M H))
        (L₂ ⊔ bigB L L₂ (sec52S M H))) (IsLieOverTwo .PSL 3 2)) →
      L₂ = oTwoUpper H ∧ oTwoUpper H = perfectCore (sec52G2 M H D L₂) ∧
      pCoreOf 2 (sec52G1 M L H B L₂) = pCoreOf 2 L ∧
      pCoreOf 2 (sec52G2 M H D L₂) = pCoreOf 2 (oTwoUpper H) ∧
      Cases5_2_6 (sec52Alpha M L H B D L₂) L (oTwoUpper H) n ∧
      pCoreOf 2 (oTwoUpper H ⊔ T) = pCoreOf 2 (oTwoUpper H ⊔ sec52S M H) ∧
      ((sec52S M H ≤ L ∧ sec52S M H ≤ oTwoUpper H ∧
          pCoreOf 2 (L ⊔ sec52S M H) = pCoreOf 2 L ∧
          pCoreOf 2 (oTwoUpper H ⊔ sec52S M H) = pCoreOf 2 (oTwoUpper H)) ∨
        (∃ m : ℕ, n = 2 * m ∧ 2 < n ∧ IsU4ExtTwo m (sec52Alpha M L H B D L₂) ∧
          ∃ t : G, orderOf t = 2 ∧ t ∉ pCoreOf 2 (oTwoUpper H) ∧
            pCoreOf 2 (oTwoUpper H ⊔ sec52S M H) =
              pCoreOf 2 (oTwoUpper H) ⊔ Subgroup.zpowers t ∧
            ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 2 ^ m ∧
              ∃ P : Subgroup ↥(CFSG.Assembly.LowTwoRank.StatedSp 2 F),
                IsMaxParabolic2 ⊤ P ∧
                Nonempty (↥(oTwoUpper H ⊓ Subgroup.centralizer ({t} : Set G)) ≃*
                  ↥(perfectCore P))))

theorem stmt5_2_6_of_F4 (h331 : Stmt3_3_1_F4) (hR : L2RankOneSylowFact) (hF : RankOneListedFacts.{0})
    (hF11 : StmtF11_5_2_F4) (hDSA : DSALoc_F4) (hAmal : DSAAmal_F4) (h524 : Stmt5_2_4_F4)
    (hbor : Stmt5_2_6_borel_F4) (htr : Stmt5_2_6_tr_F4) : Stmt5_2_6_F4 := by
  intro G _ _ T M L V H B D L₂ n hyp
  have h := hyp.toHyp5_0_1
  set S := sec52S M H with hSdef
  have h111 := hF11 G T M L V H B D L₂ n hyp
  obtain ⟨-, hweak, -, -⟩ := prop_F19_of_listed hF h111
  have hbor2 : S ⊔ borelOf L₂ S = S ⊔ (B ⊓ L₂) := hbor G T M L V H B D L₂ n hyp
  obtain ⟨-, -, ⟨hBS, -, -⟩, -⟩ := h524 G T M L V H B D L₂ n hyp
  obtain ⟨hG1, hG2, -⟩ := hyp.parabolics_eq_F4 h331 hR hbor2

  have hSn : (S.subgroupOf (S ⊔ borelOf L₂ S)).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left, hbor2]
    exact sup_le Subgroup.le_normalizer (inf_le_left.trans hBS)
  have hLns : ¬ Group.IsSolvable ↥L := not_isSolvable_of_perfect h.commutator_eq h.maximal.1.2.1.1
  have hL₂ns : ¬ Group.IsSolvable ↥L₂ := by
    obtain ⟨K₁, hK₁, -, hcase⟩ := hyp.choice
    rcases hcase with ⟨-, rfl⟩ | ⟨-, -, P, -, hL₂P⟩
    · exact not_isSolvable_of_perfect hK₁.2.1 hK₁.1
    · exact not_isSolvable_of_perfect hL₂P.2.1 hL₂P.1
  have hqt := CFSG.Quasithin.isQuasithinSub_of_qtke h.qtke (L ⊔ L₂ ⊔ S)
  have hds := hDSA G L L₂ S h111 hqt (Or.inr hSn) hLns hL₂ns
  have hamal := hAmal G L L₂ S h111 hqt (Or.inr hSn) hLns hL₂ns
  refine ⟨?_, htr G T M L V H B D L₂ n hyp ⟨hds, hamal⟩⟩
  rw [hG1, hG2]
  exact hweak

end CFSG.Quasithin.H13
