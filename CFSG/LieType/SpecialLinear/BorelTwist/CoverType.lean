module

public import CFSG.LieType.SpecialLinear.BorelTwist.Basic
public import CFSG.LieType.SpecialLinear.EndNode.CoverDatum
public import CFSG.LieType.SpecialLinear.Block222.Basic

public section

namespace CFSG.LieType.SpecialLinear

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.ComponentClassification
  CFSG.LieType.Universal.SpecialLinear
  CFSG.Quasithin.SmithCurtis CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisTw
open scoped MatrixGroups

variable (m : ℕ) (F : Type) [Field F] [Finite F] [CharP F 2]

omit [Finite F] in
private theorem neg_eq_self_charTwo (c : F) : -c = c := CharTwo.neg_eq c

private theorem coe_rankOne_xEquiv_lXEquiv (s : Fin m) (c : F) :
    (((((rankOne m F 2).xEquiv s).trans ((coverId m F 2).lXEquiv s)) c :
      ↥((curtisDatum m F 2).X s)) : SpecialLinearGroup (Fin (m + 1)) F) =
      (rankOne m F 2).x s c := rfl

private theorem coe_rankOne_xEquiv_lXEquiv_rev (s : Fin m) (c : F) :
    (((((rankOne m F 2).xEquiv (Fin.rev s)).trans
      ((coverId m F 2).lXEquiv (Fin.rev s))) c :
      ↥((curtisDatum m F 2).X (Fin.rev s))) : SpecialLinearGroup (Fin (m + 1)) F) =
      (rankOne m F 2).x (Fin.rev s) c := rfl

theorem heckeT_comp_borelGraph {k V : Type*} [Field k] [AddCommGroup V] [Module k V]
    (ρ : Representation k (SpecialLinearGroup (Fin (m + 1)) F) V) (s : Fin m) (v : V) :
    (curtisDatum m F 2).heckeT (ρ.comp (borelGraph (m + 1) F).toMonoidHom) s v =
      (curtisDatum m F 2).heckeT ρ (Fin.rev s) v := by
  let : Fintype F := Fintype.ofFinite F
  let : Fintype ↥((curtisDatum m F 2).X s) := Fintype.ofFinite _
  let : Fintype ↥((curtisDatum m F 2).X (Fin.rev s)) := Fintype.ofFinite _
  rw [CurtisDatum.heckeT_apply, CurtisDatum.heckeT_apply]
  let es : F ≃ ↥((curtisDatum m F 2).X s) :=
    ((rankOne m F 2).xEquiv s).trans ((coverId m F 2).lXEquiv s)
  let eb : F ≃ ↥((curtisDatum m F 2).X (Fin.rev s)) :=
    ((rankOne m F 2).xEquiv (Fin.rev s)).trans
      ((coverId m F 2).lXEquiv (Fin.rev s))
  have hn_s : (coverId m F 2).nhat s = (curtisDatum m F 2).n s := by
    rw [CentralCoverData.nhat]
    have h := (coverId m F 2).map_nhatW ((curtisCoxeterSystem m).simple s)
    simp only [MonoidHom.id_apply] at h
    rw [h, CentralCoverData.nW_simple]
  have hn_b : (coverId m F 2).nhat (Fin.rev s) = (curtisDatum m F 2).n (Fin.rev s) := by
    rw [CentralCoverData.nhat]
    have h := (coverId m F 2).map_nhatW ((curtisCoxeterSystem m).simple (Fin.rev s))
    simp only [MonoidHom.id_apply] at h
    rw [h, CentralCoverData.nW_simple]
  have hsmall : (∑ x : ↥((curtisDatum m F 2).X s),
      ρ.comp (borelGraph (m + 1) F).toMonoidHom
        ((x : SpecialLinearGroup (Fin (m + 1)) F) * (curtisDatum m F 2).n s) v) =
      ∑ c : F, ρ.comp (borelGraph (m + 1) F).toMonoidHom
        (((rankOne m F 2).x s c) * (coverId m F 2).nhat s) v := by
    refine (Fintype.sum_equiv es _ _ ?_).symm
    intro c
    rw [coe_rankOne_xEquiv_lXEquiv, hn_s]
  have hbig : (∑ c : F, ρ (((rankOne m F 2).x (Fin.rev s) c) *
        (coverId m F 2).nhat (Fin.rev s)) v) =
      ∑ y : ↥((curtisDatum m F 2).X (Fin.rev s)),
        ρ ((y : SpecialLinearGroup (Fin (m + 1)) F) * (curtisDatum m F 2).n (Fin.rev s)) v := by
    refine Fintype.sum_equiv eb _ _ ?_
    intro c
    rw [coe_rankOne_xEquiv_lXEquiv_rev, hn_b]
  rw [hsmall, ← hbig]
  refine Finset.sum_congr rfl fun c _ => ?_
  have hn_s' : (curtisDatum m F 2).n s = weylRep m F s := rfl
  have hn_b' : (curtisDatum m F 2).n (Fin.rev s) = weylRep m F (Fin.rev s) := rfl
  rw [MonoidHom.comp_apply]
  simp only [MulEquiv.coe_toMonoidHom]
  rw [map_mul (borelGraph (m + 1) F)]
  rw [hn_s, hn_s', hn_b, hn_b']
  change ρ ((borelGraph (m + 1) F)
      (SpecialLinearGroup.transvection (Fin.castSucc_lt_succ.ne) c) *
      (borelGraph (m + 1) F) (weylRep m F s)) v =
    ρ ((rankOne m F 2).x (Fin.rev s) c * weylRep m F (Fin.rev s)) v
  rw [borelGraph_transvection, borelGraph_weylRep, neg_eq_self_charTwo]
  have hx : SpecialLinearGroup.transvection
      (fun h => (Fin.castSucc_lt_succ (i := s)).ne (Fin.rev_injective h).symm) c =
      (rankOne m F 2).x (Fin.rev s) c := by
    rw [rankOne]
    change SpecialLinearGroup.transvection
      (fun h => (Fin.castSucc_lt_succ (i := s)).ne (Fin.rev_injective h).symm) c =
      SpecialLinearGroup.transvection
        (Fin.castSucc_lt_succ (i := Fin.rev s)).ne c
    exact transvection_congr F (castSucc_rev m s).symm (succ_rev m s).symm _ c
  rw [hx]



theorem coverId_datum_heckeT_eq {k V : Type*} [Field k] [AddCommGroup V] [Module k V]
    (ρ : Representation k (SpecialLinearGroup (Fin (m + 1)) F) V) (s : Fin m) (v : V) :
    (coverId m F 2).datum.heckeT ρ s v = (curtisDatum m F 2).heckeT ρ s v := by
  let : Fintype ↥((curtisDatum m F 2).X s) := Fintype.ofFinite _
  let : Fintype ↥((coverId m F 2).lX s) := Fintype.ofFinite _
  let : Fintype ↥((coverId m F 2).datum.X s) := Fintype.ofFinite _
  rw [CurtisDatum.heckeT_apply, CurtisDatum.heckeT_apply]
  let e : ↥((coverId m F 2).datum.X s) ≃ ↥((curtisDatum m F 2).X s) :=
    (Equiv.cast (congrArg (fun t : Subgroup (SpecialLinearGroup (Fin (m + 1)) F) => ↥t)
      (show (coverId m F 2).datum.X s = (coverId m F 2).lX s from rfl))).trans
      ((coverId m F 2).lXEquiv s)
  refine Fintype.sum_equiv e _ _ ?_
  intro x
  change ρ ((x : SpecialLinearGroup (Fin (m + 1)) F) * (coverId m F 2).nhat s) v =
    ρ (((e x : ↥((curtisDatum m F 2).X s)) : SpecialLinearGroup (Fin (m + 1)) F) *
      (curtisDatum m F 2).n s) v
  have hx : (((e x : ↥((curtisDatum m F 2).X s)) : SpecialLinearGroup (Fin (m + 1)) F)) =
      (x : SpecialLinearGroup (Fin (m + 1)) F) := rfl
  rw [hx]
  have hn : (coverId m F 2).nhat s = (curtisDatum m F 2).n s := by
    rw [CentralCoverData.nhat]
    have h := (coverId m F 2).map_nhatW ((curtisCoxeterSystem m).simple s)
    simp only [MonoidHom.id_apply] at h
    rw [h, CentralCoverData.nW_simple]
  rw [hn]

theorem heckeT_comp_borelGraph_coverId {k V : Type*} [Field k] [AddCommGroup V] [Module k V]
    (ρ : Representation k (SpecialLinearGroup (Fin (m + 1)) F) V) (s : Fin m) (v : V) :
    (coverId m F 2).datum.heckeT (ρ.comp (borelGraph (m + 1) F).toMonoidHom) s v =
      (coverId m F 2).datum.heckeT ρ (Fin.rev s) v := by
  rw [coverId_datum_heckeT_eq, coverId_datum_heckeT_eq, heckeT_comp_borelGraph]

theorem mem_map_revPerm {J : Finset (Fin m)} {s : Fin m} :
    s ∈ J.map Fin.revPerm.toEmbedding ↔ Fin.rev s ∈ J := by
  rw [Finset.mem_map]
  constructor
  · rintro ⟨a, ha, h⟩
    rw [← h]
    simpa [Fin.revPerm] using ha
  · intro hs
    exact ⟨Fin.rev s, hs, by simp [Fin.revPerm]⟩

theorem isCoverType_comp_borelGraph {k V : Type*} [Field k] [AddCommGroup V] [Module k V]
    {ρ : Representation k (SpecialLinearGroup (Fin (m + 1)) F) V} {y : V} {χ : _ → k}
    {J : Finset (Fin m)}
    (ht : IsCoverType (rankOne m F 2) ρ y χ J) :
    IsCoverType (rankOne m F 2) (ρ.comp (borelGraph (m + 1) F).toMonoidHom) y
      (χ ∘ (borelGraph (m + 1) F)) (J.map Fin.revPerm.toEmbedding) := by
  unfold IsCoverType at ht ⊢
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [CurtisDatum.mem_fixU] at ht ⊢
    rw [coverId_datum_U m F 2] at ht
    intro u hu
    rw [coverId_datum_U m F 2] at hu
    rw [MonoidHom.comp_apply]
    change ρ ((borelGraph (m + 1) F) u) y = y
    exact ht.1 _ (borelGraph_mem_U m F hu)
  · exact ht.2.1
  · intro h hh
    rw [MonoidHom.comp_apply]
    change ρ ((borelGraph (m + 1) F) h) y = χ ((borelGraph (m + 1) F) h) • y
    exact ht.2.2.1 _ (borelGraph_mem_H m F hh)
  · intro s
    rw [mem_map_revPerm, ht.2.2.2 (Fin.rev s)]
    constructor
    · rintro ⟨hχ, hT⟩
      refine ⟨?_, ?_⟩
      · intro u
        change χ ((borelGraph (m + 1) F) ((rankOne m F 2).hh s u)) = 1
        rw [show (rankOne m F 2).hh s u = hdiag m F s u from rfl, borelGraph_hdiag]
        exact hχ u
      · rwa [heckeT_comp_borelGraph_coverId]
    · rintro ⟨hχ, hT⟩
      refine ⟨?_, ?_⟩
      · intro u
        have h := hχ u
        change χ ((borelGraph (m + 1) F) ((rankOne m F 2).hh s u)) = 1 at h
        rw [show (rankOne m F 2).hh s u = hdiag m F s u from rfl, borelGraph_hdiag] at h
        exact h
      · rwa [← heckeT_comp_borelGraph_coverId]



@[expose] def borelStdSet (J : Finset (Fin m)) (ε : ℕ) : Finset (Fin m) :=
  if ε = 0 then J else J.map Fin.revPerm.toEmbedding

@[expose] noncomputable def borelStdChar {k : Type*} (χ : SpecialLinearGroup (Fin (m + 1)) F → k)
    (σ : F ≃+* F) (ε : ℕ) : SpecialLinearGroup (Fin (m + 1)) F → k :=
  if ε = 0 then χ ∘ CatalogueBHigherLinearField.slFieldAut (Fin (m + 1)) F σ
  else (χ ∘ CatalogueBHigherLinearField.slFieldAut (Fin (m + 1)) F σ) ∘
    borelGraph (m + 1) F

end CFSG.LieType.SpecialLinear
