module

public import CFSG.LocalAnalysis.GLTheoremA.S10.Inputs103
import CFSG.Milestones.CL_LIT_Borel_Tits_local_parabolic
import CFSG.RankThree.PartTwo.Sec19.KS1919U48
import CFSG.LocalAnalysis.GLTheoremA.S4.FullCover.MultLie
import CFSG.Models.Blueprint
import CFSG.RankThree.PartOne.S12.ModelTransport
public import CFSG.Blueprint.Catalog

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 TauCeti

private theorem u42_exists_lieIndex {S : Type} [Group S] {P : LieTypeIndex → Prop}
    (h : catalogIs S (onLie P)) :
    ∃ (d : LieTypeIndex) (hv : d.Valid), P d ∧
      Nonempty (S ≃* ValidLieTypeIndex.Group ⟨d, hv⟩) := by
  obtain ⟨i, hi, ⟨e⟩⟩ := h
  cases i with
  | cyclic _ _ => exact hi.elim
  | alternating _ _ => exact hi.elim
  | sporadic _ => exact hi.elim
  | lie j => exact ⟨j.1, j.2, hi, ⟨e⟩⟩

private theorem u42_lieIndex {S : Type} [Group S] (h : catalogIs S S9.isU4eight) :
    ∃ (q : PrimePower) (hv : (LieTypeIndex.twistedA 3 q).Valid), q.card = 8 ∧
      Nonempty (S ≃* ValidLieTypeIndex.Group ⟨.twistedA 3 q, hv⟩) := by
  obtain ⟨d, hv, hP, ⟨e⟩⟩ := u42_exists_lieIndex h
  cases d with
  | twistedA r q =>
    rcases r with _ | _ | _ | _ | r
    · exact hP.elim
    · exact hP.elim
    · exact hP.elim
    · exact ⟨q, hv, hP, ⟨e⟩⟩
    · exact hP.elim
  | _ => exact hP.elim

private theorem u42_model_iso {S : Type} [Group S] (h : catalogIs S S9.isU4eight) :
    CFSG.Blueprint.LieModel S .PSU (3 + 1) 2 3 ∧ Nonempty (S ≃* CFSG.PGLModel.projSU 4 2 3) := by
  obtain ⟨q, hv, hq, ⟨e⟩⟩ := u42_lieIndex h
  obtain ⟨h1, h2⟩ := primePower_eq_of_card_eq Nat.prime_two (s := 3) (by norm_num)
    (hq.trans (by norm_num))
  have hm := lieModel_twistedA' 3 q hv e
  rw [h1, h2] at hm
  refine ⟨hm.toBlueprint (by decide), ?_⟩
  obtain ⟨-, K, _, _, hK, ⟨e'⟩⟩ := hm.statedClassicalModel (by decide)
  haveI : Fintype K := Fintype.ofFinite K
  haveI : Fintype (GaloisField 2 (2 * 3)) := Fintype.ofFinite _
  have hc : Fintype.card K = Fintype.card (GaloisField 2 (2 * 3)) := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hK,
      GaloisField.card 2 (2 * 3) (by norm_num)]
    norm_num
  let ψ₀ : CFSG.PGLModel.projSU 4 2 3 ≃* StatedProj (StatedSU 4 (2 ^ 3) (GaloisField 2 (2 * 3))) :=
    (MulEquiv.subgroupCongr
      (CFSG.RankThree.PartOne.projImage_statedSU_eq_projSU 4 2 3).symm).trans
      (CFSG.Adapters.RankTwoModelTransports.statedProjEquivMapMk _).symm
  exact ⟨e'.trans ((CFSG.Open.StatedSUFieldChange.statedProjSUEquiv
    (FiniteField.ringEquivOfCardEq hc) 4 (2 ^ 3)).trans ψ₀.symm)⟩

theorem i1015U42At_holds (G : Type) [Group G] [Finite G] : I1015U42At G := by
  intro X L E T _ hU hEL hE hTL hT2 hEN hTnot
  obtain ⟨hmB, ⟨ψ⟩⟩ := u42_model_iso hU
  have hT0 : T ≠ ⊥ := fun h => hTnot (by rw [h]; exact bot_le)
  have hUr : IsPGroup 2 (T.subgroupOf L) := IsPGroup.comap_subtype hT2
  have hU0 : T.subgroupOf L ≠ ⊥ := by
    intro h
    rw [Subgroup.subgroupOf_eq_bot] at h
    apply hT0
    have := disjoint_iff.1 h
    rwa [inf_eq_left.2 hTL] at this
  obtain ⟨S, P, hP, hNU, -, -, hSN, -⟩ :=
    CFSG.Milestones.cl_lit_borel_tits_local_parabolic_all_models ↥L .PSU (3 + 1) 2 3 hmB
      (T.subgroupOf L) hU0 hUr
  have hPP : CFSG.RankThree.PartTwo.Sec19.IsProperParabolic P :=
    ⟨hP, S, hSN (by decide)⟩
  have hE'P : E.subgroupOf L ≤ P := by
    intro x hx
    refine hNU ?_
    rw [Subgroup.mem_normalizer_iff]
    intro h
    have hn := Subgroup.mem_normalizer_iff.1 (hEN (Subgroup.mem_subgroupOf.1 hx)) (h : G)
    simpa [Subgroup.mem_subgroupOf] using hn
  have hcomm : ∀ x ∈ E.subgroupOf L, ∀ y ∈ E.subgroupOf L, x * y = y * x := by
    intro x hx y hy
    apply Subtype.ext
    have := congrArg Subtype.val (hE.1.is_comm.comm ⟨x.1, Subgroup.mem_subgroupOf.1 hx⟩
      ⟨y.1, Subgroup.mem_subgroupOf.1 hy⟩)
    simpa using this
  have hexp : ∀ x ∈ E.subgroupOf L, x ^ 3 = 1 := by
    intro x hx
    apply Subtype.ext
    simpa using hE.2 x.1 (Subgroup.mem_subgroupOf.1 hx)
  have hk := CFSG.RankThree.PartTwo.Sec19.ks1919U48 ↥L ⟨ψ⟩ P hPP (E.subgroupOf L) hE'P hcomm hexp
  have hcard : Nat.card (E.subgroupOf L) = Nat.card E :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEL).toEquiv
  rw [← hcard]
  exact hk.trans (by norm_num)

end CFSG.LocalAnalysis.GLTheoremA
