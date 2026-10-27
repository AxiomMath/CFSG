module

public import CFSG.CGT.PushingUpLit.BHS7.CoverKey
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftPieceCommon
public import CFSG.LocalAnalysis.QuasithinUnique.RankOneRecognitionCover

public section

namespace CFSG.CGT.PushingUpLit.BHS7

open Subgroup CFSG.Open CFSG.Quasithin CFSG.Quasithin.BlueprintB2 CFSG.QuasithinUnique
  CFSG.QuasithinUnique.Setup CFSG.QuasithinUnique.Setup.Wreath CFSG.QuasithinUnique.Setup.Campbell
  CFSG.QuasithinUnique.Setup.Lift.Piece
open scoped commutatorElement

theorem Kodd_eq_oddOrderSubgroup_top (G : Type*) [Group G] :
    Kodd G = oddOrderSubgroup (⊤ : Subgroup G) := by
  unfold Kodd pPrimeGen oddOrderSubgroup
  congr 1
  ext x
  exact and_congr_right fun _ => Nat.coprime_two_right

theorem map_Kodd_subtype' {Ω : Type*} [Group Ω] (H : Subgroup Ω) :
    (Kodd ↥H).map H.subtype = oddOrderSubgroup H := by
  unfold Kodd pPrimeGen oddOrderSubgroup
  rw [MonoidHom.map_closure]
  congr 1
  ext y
  constructor
  · rintro ⟨x, ⟨-, hx⟩, rfl⟩
    refine ⟨x.2, ?_⟩
    show Odd (orderOf (x : Ω))
    rw [Subgroup.orderOf_coe]
    exact Nat.coprime_two_right.mp hx
  · rintro ⟨hyH, hy⟩
    refine ⟨⟨y, hyH⟩, ⟨trivial, ?_⟩, rfl⟩
    rw [Subgroup.orderOf_mk]
    exact Nat.coprime_two_right.mpr hy

section Cover

variable {H : Type*} [Group H] [Finite H] {k : Type} [Field k] [Finite k] [CharP k 2]
  {R M V : Subgroup H} {ρ : H →* Gamma k} {φ : V →* Multiplicative (Fin 2 → k)}

theorem natural_pCore_inf_kodd_le_vmod (h : IsNatQuotSetting R M V ρ φ)
    (hchar : CharTwo (⊤ : Subgroup H)) (hnc : NoCharNormal R ⊤)
    (hJ : ⁅elemThompsonIn 2 R, V⁆ ≠ ⊥) :
    CFSG.pCore 2 ↥(baumannOvergroup R) ⊓ Kodd ↥(baumannOvergroup R) ≤
      Vmod ↥(baumannOvergroup R) := by
  classical
  obtain ⟨hSyl, -, -, -, ⟨α, hZ, hSα⟩, hQK, hVE, -⟩ :=
    h.actual_Campbell_natural_minimal_parabolic_output hchar hnc hJ
  have hQS : CFSG.pCore 2 ↥(baumannOvergroup R) ≤
      (elemBaumannIn 2 R).subgroupOf (baumannOvergroup R) := le_of_le_of_eq le_sup_left hSα.symm
  have hUc : ∀ q ∈ CFSG.pCore 2 ↥(baumannOvergroup R), ∀ u ∈ Vmod ↥(baumannOvergroup R),
      q * u = u * q := fun q hq u hu => (mem_centerTorsion_iff.mp (hVE hu)).2.1 q hq
  have hE : ∀ (N : Subgroup (Kodd ↥(baumannOvergroup R))) [N.Normal],
      IsPGroup 2 (Kodd ↥(baumannOvergroup R) ⧸ N) → N = ⊤ := by
    rw [Kodd_eq_oddOrderSubgroup_top]
    exact hasNoTwoQuotient_oddOrderSubgroup ⊤
  have hSylTop : IsSylowTwoOf ((elemBaumannIn 2 R).subgroupOf (baumannOvergroup R))
      (⊤ : Subgroup ↥(baumannOvergroup R)) := by
    refine ⟨le_top, ?_, ?_⟩
    · exact hSyl.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hSyl.1).symm
    · have h1 : (((elemBaumannIn 2 R).subgroupOf (baumannOvergroup R)).subgroupOf
          (⊤ : Subgroup ↥(baumannOvergroup R))).index =
          ((elemBaumannIn 2 R).subgroupOf (baumannOvergroup R)).index :=
        Subgroup.index_comap_of_surjective _ (f := (⊤ : Subgroup ↥(baumannOvergroup R)).subtype)
          (fun x => ⟨⟨x, trivial⟩, rfl⟩)
      rw [h1]
      exact hSyl.2.2
  have hsub : ((Kodd ↥(baumannOvergroup R)).subgroupOf
      (⊤ : Subgroup ↥(baumannOvergroup R))).IsSubnormal := by
    have : ((Kodd ↥(baumannOvergroup R)).subgroupOf
      (⊤ : Subgroup ↥(baumannOvergroup R))).Normal := inferInstance
    exact this.isSubnormal
  have hSylE := RankOneRecog.isSylowTwoOf_inf_of_subnormal hSylTop le_top hsub
  exact inf_le_of_aimg_cover α hQS hQK.symm hUc hSα hZ hE hSylE

theorem natural_blockQ_le_blockU (h : IsNatQuotSetting R M V ρ φ)
    (hchar : CharTwo (⊤ : Subgroup H)) (hnc : NoCharNormal R ⊤)
    (hJ : ⁅elemThompsonIn 2 R, V⁆ ≠ ⊥) {n : ℕ} (hn : 1 ≤ n) (hcard : Nat.card k = 2 ^ n)
    (hGb : baumannOvergroup R = ⊤) :
    blockQ (oddOrderSubgroup (⊤ : Subgroup H)) ≤ blockU (oddOrderSubgroup (⊤ : Subgroup H)) := by
  classical
  have hcover := natural_pCore_inf_kodd_le_vmod h hchar hnc hJ
  obtain ⟨-, -, -, -, hU, -⟩ := natural_chi0_block_ext h hchar hnc hJ hn hcard hGb
  obtain ⟨-, -, -, -, -, hQK, -⟩ := h.actual_Campbell_natural_minimal_parabolic_output hchar hnc hJ
  have hA : (CFSG.pCore 2 ↥(baumannOvergroup R)).map (baumannOvergroup R).subtype =
      blockQ (baumannOvergroup R) := (blockQ_eq_map _).symm
  have hB : (Kodd ↥(baumannOvergroup R)).map (baumannOvergroup R).subtype =
      oddOrderSubgroup (baumannOvergroup R) := map_Kodd_subtype' _
  have hC : (Vmod ↥(baumannOvergroup R)).map (baumannOvergroup R).subtype =
      ⁅blockQ (baumannOvergroup R), oddOrderSubgroup (baumannOvergroup R)⁆ := by
    rw [← hQK, Subgroup.map_commutator, hA, hB]
  have hmap := Subgroup.map_mono (f := (baumannOvergroup R).subtype) hcover
  rw [Subgroup.map_inf_eq _ _ _ (baumannOvergroup R).subtype_injective, hA, hB, hC, hGb] at hmap
  have hLn : (oddOrderSubgroup (⊤ : Subgroup H)).Normal := h.normal_L
  have hLn' : ((oddOrderSubgroup (⊤ : Subgroup H)).subgroupOf (⊤ : Subgroup H)).Normal :=
    inferInstance
  have hLQ : blockQ (oddOrderSubgroup (⊤ : Subgroup H)) ≤ blockQ (⊤ : Subgroup H) :=
    CFSG.RankThreeEvenClassification.Helpers.pCoreOf_le_pCoreOf_of_normal 2 _ _ le_top hLn'
  calc blockQ (oddOrderSubgroup (⊤ : Subgroup H))
      ≤ blockQ (⊤ : Subgroup H) ⊓ oddOrderSubgroup (⊤ : Subgroup H) :=
        le_inf hLQ (blockQ_le_self _)
    _ ≤ ⁅blockQ (⊤ : Subgroup H), oddOrderSubgroup (⊤ : Subgroup H)⁆ := hmap
    _ = blockU (oddOrderSubgroup (⊤ : Subgroup H)) := hU.symm

end Cover

end CFSG.CGT.PushingUpLit.BHS7
