module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265FSz
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265SF1
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10FSeitzB2

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S265

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.Blueprint CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S10

section Iso

theorem s265e_centerQuot_equiv_map {X : Type} [Group X] {Kb : Subgroup X} (hKb : commutator ↥Kb = ⊤) :
    Nonempty (↥Kb ⧸ Subgroup.center ↥Kb ≃*
      ↥(Kb.map (QuotientGroup.mk' (Subgroup.center X))) ⧸
        Subgroup.center ↥(Kb.map (QuotientGroup.mk' (Subgroup.center X)))) := by
  haveI : Group.IsPerfect ↥Kb := ⟨hKb⟩
  set π := QuotientGroup.mk' (Subgroup.center X)
  have hker : (π.subgroupMap Kb).ker ≤ Subgroup.center ↥Kb := by
    intro k hk
    rw [MonoidHom.mem_ker] at hk
    have h1 : π (k : X) = 1 := congrArg Subtype.val hk
    have hkZ : (k : X) ∈ Subgroup.center X := (QuotientGroup.eq_one_iff _).1 h1
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (Subgroup.mem_center_iff.1 hkZ (g : X))
  exact Y10F.quotEquiv_of_perfect_central (π.subgroupMap Kb) (π.subgroupMap_surjective Kb)
    inferInstance hker

theorem s265e_centerQuot_equiv_subgroupOf {Ω : Type} [Group Ω] {S K : Subgroup Ω} (hKS : K ≤ S) :
    Nonempty (↥K ⧸ Subgroup.center ↥K ≃*
      ↥(K.subgroupOf S) ⧸ Subgroup.center ↥(K.subgroupOf S)) :=
  ⟨QuotientGroup.congr _ _ (Subgroup.subgroupOfEquivOfLe hKS).symm
    (Subgroup.map_center_eq _)⟩

end Iso

section Models

private theorem s265e_sz32_model {R : Type} [Group R] (h : catalogIs R tySz32) :
    SuzukiModel R 2 5 := by
  obtain ⟨i, hi, ⟨e⟩⟩ := h
  cases i with
  | cyclic _ _ => exact hi.elim
  | alternating _ _ => exact hi.elim
  | sporadic _ => exact hi.elim
  | lie d =>
    obtain ⟨d1, hv⟩ := d
    cases d1 with
    | suzuki m =>
      have hm : m = 2 := by
        rcases m with _ | _ | _ | m <;> first | rfl | (exfalso; exact hi)
      subst hm
      have hS := CFSG.RankThree.PartTwo.Sec4.Census.suzukiModel_of_index 2 hv
      have hL : CFSG.Blueprint.LieModel (TauCeti.CFSGIndex.lie ⟨.suzuki 2, hv⟩).Group .twistedB2 0 2 5 :=
        Or.inr (Or.inr (Or.inr ⟨rfl, rfl, hS⟩))
      exact (LieModel.suzukiModel (LieModel.of_mulEquiv e.symm hL)).2
    | _ => exact hi.elim

variable {Ω : Type} [Group Ω] [Finite Ω]

theorem s265e_lieModel_sz {K : Subgroup Ω} (hKq : CFSG.Open.IsQuasisimple ↥K)
    (hSz : catalogIs (PSimple 5 K) tySz32) {Q : Type} [Group Q]
    (e : ↥K ⧸ Subgroup.center ↥K ≃* Q) : LieModel Q .twistedB2 0 2 5 := by
  have hM := s265e_sz32_model hSz
  haveI : Nontrivial (PSimple 5 K) := (CFSG.LieType.Simplicity.fam_2b2_simplicity _ 2 5 hM).1
  obtain ⟨θ⟩ := SF.nonempty_centerQuot_equiv_pSimple (p := 5) hKq
  exact LieModel.of_mulEquiv (θ.symm.trans e) (Or.inr (Or.inr (Or.inr ⟨rfl, rfl, hM⟩)))

section Tits


private theorem s265e_tits_model {R : Type} [Group R] (h : catalogIs R tyTits) :
    ReeTitsModel R .Tits 2 1 := by
  obtain ⟨i, hi, ⟨e⟩⟩ := h
  cases i with
  | cyclic _ _ => exact hi.elim
  | alternating _ _ => exact hi.elim
  | sporadic _ => exact hi.elim
  | lie d =>
    obtain ⟨d1, hv⟩ := d
    cases d1 with
    | tits => exact CFSG.StandardType.ChevTwo.reeTitsModel_of_tits hv e
    | _ => exact hi.elim

theorem s265e_lieModel_tits {K : Subgroup Ω} (hKq : CFSG.Open.IsQuasisimple ↥K)
    (hT : catalogIs (PSimple 5 K) tyTits) {Q : Type} [Group Q]
    (e : ↥K ⧸ Subgroup.center ↥K ≃* Q) : LieModel Q .Tits 0 2 1 := by
  have hR := s265e_tits_model hT
  haveI : Nontrivial (PSimple 5 K) := (CFSG.LieType.Simplicity.fam_tits_simplicity _ 2 1 hR).1
  obtain ⟨θ⟩ := SF.nonempty_centerQuot_equiv_pSimple (p := 5) hKq
  exact LieModel.of_mulEquiv (θ.symm.trans e) (Or.inr (Or.inr (Or.inl ⟨rfl, by decide, hR⟩)))

theorem s265e_lieModel {K : Subgroup Ω} (hKq : CFSG.Open.IsQuasisimple ↥K)
    (hE : catalogIs (PSimple 5 K) tyE) {Q : Type} [Group Q]
    (e : ↥K ⧸ Subgroup.center ↥K ≃* Q) :
    LieModel Q .twistedB2 0 2 5 ∨ LieModel Q .Tits 0 2 1 :=
  (tyE_split hE).imp (fun hSz => s265e_lieModel_sz hKq hSz e)
    (fun hT => s265e_lieModel_tits hKq hT e)

end Tits

end Models

end CFSG.LocalAnalysis.GLTheoremA.S265

end
