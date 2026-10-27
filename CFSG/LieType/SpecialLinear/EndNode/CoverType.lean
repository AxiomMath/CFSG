module

public import CFSG.LieType.SpecialLinear.EndNode.Smith
public import CFSG.LieType.SpecialLinear.EndNode.CoverDatum

public section

namespace CFSG.LieType.SpecialLinear

open Matrix CFSG.LieType.Universal.SpecialLinear CFSG.Quasithin.SmithCurtis
  CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisTw

noncomputable section

variable (m : ℕ) (F : Type) [Field F] [Finite F] (p : ℕ) [Fact p.Prime] [CharP F p]

private theorem embedSucc_rankOne_x (s : Fin m) (c : F) :
    embedSucc m F ((rankOne m F p).x s c) =
      (rankOne (m+1) F p).x s.succ c := by
  change embedSucc m F
      (SpecialLinearGroup.transvection ((Fin.castSucc_lt_succ (i := s)).ne) c) =
    SpecialLinearGroup.transvection ((Fin.castSucc_lt_succ (i := s.succ)).ne) c
  rw [embedSucc_transvection]

private theorem embedCastSucc_rankOne_x (s : Fin m) (c : F) :
    embedCastSucc m F ((rankOne m F p).x s c) =
      (rankOne (m+1) F p).x s.castSucc c := by
  change embedCastSucc m F
      (SpecialLinearGroup.transvection ((Fin.castSucc_lt_succ (i := s)).ne) c) =
    SpecialLinearGroup.transvection ((Fin.castSucc_lt_succ (i := s.castSucc)).ne) c
  rw [embedCastSucc_transvection]

private theorem embedSucc_rankOne_nhat (s : Fin m) :
    embedSucc m F ((coverId m F p).nhat s) =
      (coverId (m+1) F p).nhat s.succ := by
  change embedSucc m F ((coverId m F p).nhatW ((curtisCoxeterSystem m).simple s)) =
    (coverId (m+1) F p).nhatW ((curtisCoxeterSystem (m+1)).simple s.succ)
  rw [coverId_nhatW, coverId_nhatW, embedSucc_weylRep]

private theorem embedCastSucc_rankOne_nhat (s : Fin m) :
    embedCastSucc m F ((coverId m F p).nhat s) =
      (coverId (m+1) F p).nhat s.castSucc := by
  change embedCastSucc m F ((coverId m F p).nhatW ((curtisCoxeterSystem m).simple s)) =
    (coverId (m+1) F p).nhatW ((curtisCoxeterSystem (m+1)).simple s.castSucc)
  rw [coverId_nhatW, coverId_nhatW, embedCastSucc_weylRep]

private theorem embedSucc_rankOne_term (s : Fin m) (c : F) :
    embedSucc m F ((rankOne m F p).x s c * (coverId m F p).nhat s) =
      (rankOne (m+1) F p).x s.succ c * (coverId (m+1) F p).nhat s.succ := by
  rw [map_mul, embedSucc_rankOne_x, embedSucc_rankOne_nhat]

private theorem embedCastSucc_rankOne_term (s : Fin m) (c : F) :
    embedCastSucc m F ((rankOne m F p).x s c * (coverId m F p).nhat s) =
      (rankOne (m+1) F p).x s.castSucc c * (coverId (m+1) F p).nhat s.castSucc := by
  rw [map_mul, embedCastSucc_rankOne_x, embedCastSucc_rankOne_nhat]

omit [Fact (Nat.Prime p)] in
theorem embedSucc_mem_H {g : SLm1 m F} (hg : g ∈ (curtisDatum m F p).H) :
    embedSucc m F g ∈ (curtisDatum (m+1) F p).H := by
  change g ∈ ⨆ k, torus m F k at hg
  change embedSucc m F g ∈ ⨆ k, torus (m+1) F k
  rw [mem_iSup_torus_iff] at hg ⊢
  rw [coe_embedSucc]
  intro i j hij
  rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨i, rfl⟩ <;>
    rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨j, rfl⟩
  · exact absurd rfl hij
  · rw [embedSuccMat_apply_zero_succ]
  · rw [embedSuccMat_apply_succ_zero]
  · rw [embedSuccMat_apply_succ_succ]
    exact hg (fun h => hij (by rw [h]))

omit [Fact (Nat.Prime p)] in
theorem embedCastSucc_mem_H {g : SLm1 m F} (hg : g ∈ (curtisDatum m F p).H) :
    embedCastSucc m F g ∈ (curtisDatum (m+1) F p).H := by
  change g ∈ ⨆ k, torus m F k at hg
  change embedCastSucc m F g ∈ ⨆ k, torus (m+1) F k
  rw [mem_iSup_torus_iff] at hg ⊢
  rw [coe_embedCastSucc_eq_fromBlocksLast]
  intro i j hij
  rcases Fin.eq_castSucc_or_eq_last i with ⟨i, rfl⟩ | rfl <;>
    rcases Fin.eq_castSucc_or_eq_last j with ⟨j, rfl⟩ | rfl
  · rw [fromBlocksLast_apply_castSucc_castSucc]
    exact hg (fun h => hij (by rw [h]))
  · rw [fromBlocksLast_apply_castSucc_last]
    simp
  · rw [fromBlocksLast_apply_last_castSucc]
    simp
  · exact absurd rfl hij


private theorem coe_rankOne_xEquiv_lXEquiv (s : Fin m) (c : F) :
    (((((rankOne m F p).xEquiv s).trans ((coverId m F p).lXEquiv s)) c :
      ↥((curtisDatum m F p).X s)) : SLm1 m F) = (rankOne m F p).x s c := rfl

private theorem coe_rankOne_xEquiv_lXEquiv_succ (s : Fin m) (c : F) :
    (((((rankOne (m+1) F p).xEquiv s.succ).trans
      ((coverId (m+1) F p).lXEquiv s.succ)) c :
      ↥((curtisDatum (m+1) F p).X s.succ)) : SLm2 m F) =
      (rankOne (m+1) F p).x s.succ c := rfl

private theorem coe_rankOne_xEquiv_lXEquiv_cast (s : Fin m) (c : F) :
    (((((rankOne (m+1) F p).xEquiv s.castSucc).trans
      ((coverId (m+1) F p).lXEquiv s.castSucc)) c :
      ↥((curtisDatum (m+1) F p).X s.castSucc)) : SLm2 m F) =
      (rankOne (m+1) F p).x s.castSucc c := rfl

theorem heckeT_comp_embedSucc {k V : Type*} [Field k] [AddCommGroup V] [Module k V]
    (ρ : Representation k (SLm2 m F) V) (s : Fin m) (v : V) :
    (curtisDatum m F p).heckeT (ρ.comp (embedSucc m F)) s v =
      (curtisDatum (m+1) F p).heckeT ρ s.succ v := by
  let : Fintype F := Fintype.ofFinite F
  let : Fintype ↥((curtisDatum m F p).X s) := Fintype.ofFinite _
  let : Fintype ↥((curtisDatum (m+1) F p).X s.succ) := Fintype.ofFinite _
  rw [CurtisDatum.heckeT_apply, CurtisDatum.heckeT_apply]
  change (∑ x : ↥((curtisDatum m F p).X s),
      ρ (embedSucc m F ((x : SLm1 m F) * (curtisDatum m F p).n s)) v) =
    ∑ y : ↥((curtisDatum (m+1) F p).X s.succ),
      ρ ((y : SLm2 m F) * (curtisDatum (m+1) F p).n s.succ) v
  let es : F ≃ ↥((curtisDatum m F p).X s) :=
    ((rankOne m F p).xEquiv s).trans ((coverId m F p).lXEquiv s)
  let eb : F ≃ ↥((curtisDatum (m+1) F p).X s.succ) :=
    ((rankOne (m+1) F p).xEquiv s.succ).trans
      ((coverId (m+1) F p).lXEquiv s.succ)
  have hn_s : (coverId m F p).nhat s = (curtisDatum m F p).n s := by
    rw [CentralCoverData.nhat]
    have h := (coverId m F p).map_nhatW ((curtisCoxeterSystem m).simple s)
    simp only [MonoidHom.id_apply] at h
    rw [h, CentralCoverData.nW_simple]
  have hn_b : (coverId (m+1) F p).nhat s.succ =
      (curtisDatum (m+1) F p).n s.succ := by
    rw [CentralCoverData.nhat]
    have h := (coverId (m+1) F p).map_nhatW ((curtisCoxeterSystem (m+1)).simple s.succ)
    simp only [MonoidHom.id_apply] at h
    rw [h, CentralCoverData.nW_simple]
  have hsmall : (∑ x : ↥((curtisDatum m F p).X s),
      ρ (embedSucc m F ((x : SLm1 m F) * (curtisDatum m F p).n s)) v) =
      ∑ c : F, ρ (embedSucc m F
        (((rankOne m F p).x s c) * (coverId m F p).nhat s)) v := by
    refine (Fintype.sum_equiv es _ _ ?_).symm
    intro c
    rw [coe_rankOne_xEquiv_lXEquiv, hn_s]
  have hbig : (∑ c : F, ρ ((rankOne (m+1) F p).x s.succ c *
        (coverId (m+1) F p).nhat s.succ) v) =
      ∑ y : ↥((curtisDatum (m+1) F p).X s.succ),
        ρ ((y : SLm2 m F) * (curtisDatum (m+1) F p).n s.succ) v := by
    refine Fintype.sum_equiv eb _ _ ?_
    intro c
    rw [coe_rankOne_xEquiv_lXEquiv_succ, hn_b]
  rw [hsmall, ← hbig]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [embedSucc_rankOne_term, hn_b]

theorem heckeT_comp_embedCastSucc {k V : Type*} [Field k] [AddCommGroup V] [Module k V]
    (ρ : Representation k (SLm2 m F) V) (s : Fin m) (v : V) :
    (curtisDatum m F p).heckeT (ρ.comp (embedCastSucc m F)) s v =
      (curtisDatum (m+1) F p).heckeT ρ s.castSucc v := by
  let : Fintype F := Fintype.ofFinite F
  let : Fintype ↥((curtisDatum m F p).X s) := Fintype.ofFinite _
  let : Fintype ↥((curtisDatum (m+1) F p).X s.castSucc) := Fintype.ofFinite _
  rw [CurtisDatum.heckeT_apply, CurtisDatum.heckeT_apply]
  change (∑ x : ↥((curtisDatum m F p).X s),
      ρ (embedCastSucc m F ((x : SLm1 m F) * (curtisDatum m F p).n s)) v) =
    ∑ y : ↥((curtisDatum (m+1) F p).X s.castSucc),
      ρ ((y : SLm2 m F) * (curtisDatum (m+1) F p).n s.castSucc) v
  let es : F ≃ ↥((curtisDatum m F p).X s) :=
    ((rankOne m F p).xEquiv s).trans ((coverId m F p).lXEquiv s)
  let eb : F ≃ ↥((curtisDatum (m+1) F p).X s.castSucc) :=
    ((rankOne (m+1) F p).xEquiv s.castSucc).trans
      ((coverId (m+1) F p).lXEquiv s.castSucc)
  have hn_s : (coverId m F p).nhat s = (curtisDatum m F p).n s := by
    rw [CentralCoverData.nhat]
    have h := (coverId m F p).map_nhatW ((curtisCoxeterSystem m).simple s)
    simp only [MonoidHom.id_apply] at h
    rw [h, CentralCoverData.nW_simple]
  have hn_b : (coverId (m+1) F p).nhat s.castSucc =
      (curtisDatum (m+1) F p).n s.castSucc := by
    rw [CentralCoverData.nhat]
    have h := (coverId (m+1) F p).map_nhatW
      ((curtisCoxeterSystem (m+1)).simple s.castSucc)
    simp only [MonoidHom.id_apply] at h
    rw [h, CentralCoverData.nW_simple]
  have hsmall : (∑ x : ↥((curtisDatum m F p).X s),
      ρ (embedCastSucc m F ((x : SLm1 m F) * (curtisDatum m F p).n s)) v) =
      ∑ c : F, ρ (embedCastSucc m F
        (((rankOne m F p).x s c) * (coverId m F p).nhat s)) v := by
    refine (Fintype.sum_equiv es _ _ ?_).symm
    intro c
    rw [coe_rankOne_xEquiv_lXEquiv, hn_s]
  have hbig : (∑ c : F, ρ ((rankOne (m+1) F p).x s.castSucc c *
        (coverId (m+1) F p).nhat s.castSucc) v) =
      ∑ y : ↥((curtisDatum (m+1) F p).X s.castSucc),
        ρ ((y : SLm2 m F) * (curtisDatum (m+1) F p).n s.castSucc) v := by
    refine Fintype.sum_equiv eb _ _ ?_
    intro c
    rw [coe_rankOne_xEquiv_lXEquiv_cast, hn_b]
  rw [hsmall, ← hbig]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [embedCastSucc_rankOne_term, hn_b]

theorem mem_firstRowFix_of_isCoverType {k V : Type*} [Field k] [AddCommGroup V] [Module k V]
    {ρ : Representation k (SLm2 m F) V} {y : V} {χ : SLm2 m F → k}
    {J : Finset (Fin (m+1))}
    (ht : IsCoverType (rankOne (m+1) F p) ρ y χ J) :
    y ∈ firstRowFix m F ρ := by
  rw [firstRowFix, mem_fixSub]
  intro g hg
  have hgU : g ∈ (curtisDatum (m+1) F p).U := firstRowRadical_le_U m F p hg
  have hyU := ht.1
  rw [CurtisDatum.mem_fixU] at hyU
  rw [coverId_datum_U (m+1) F p] at hyU
  exact hyU g hgU

theorem mem_lastColFix_of_isCoverType {k V : Type*} [Field k] [AddCommGroup V] [Module k V]
    {ρ : Representation k (SLm2 m F) V} {y : V} {χ : SLm2 m F → k}
    {J : Finset (Fin (m+1))}
    (ht : IsCoverType (rankOne (m+1) F p) ρ y χ J) :
    y ∈ lastColFix m F ρ := by
  rw [lastColFix, mem_fixSub]
  intro g hg
  have hgU : g ∈ (curtisDatum (m+1) F p).U := lastColRadical_le_U m F p hg
  have hyU := ht.1
  rw [CurtisDatum.mem_fixU] at hyU
  rw [coverId_datum_U (m+1) F p] at hyU
  exact hyU g hgU

private theorem coverId_datum_heckeT_eq_small {k V : Type*} [Field k] [AddCommGroup V]
    [Module k V] (ρ : Representation k (SLm1 m F) V) (s : Fin m) (v : V) :
    (coverId m F p).datum.heckeT ρ s v = (curtisDatum m F p).heckeT ρ s v := by
  let : Fintype ↥((curtisDatum m F p).X s) := Fintype.ofFinite _
  let : Fintype ↥((coverId m F p).lX s) := Fintype.ofFinite _
  let : Fintype ↥((coverId m F p).datum.X s) := Fintype.ofFinite _
  rw [CurtisDatum.heckeT_apply, CurtisDatum.heckeT_apply]
  let e : ↥((coverId m F p).datum.X s) ≃ ↥((curtisDatum m F p).X s) :=
    (Equiv.cast (congrArg (fun t : Subgroup (SLm1 m F) => ↥t) (show (coverId m F p).datum.X s = (coverId m F p).lX s from rfl))).trans
      ((coverId m F p).lXEquiv s)
  refine Fintype.sum_equiv e _ _ ?_
  intro x
  change ρ ((x : SLm1 m F) * (coverId m F p).nhat s) v =
    ρ (((e x : ↥((curtisDatum m F p).X s)) : SLm1 m F) *
      (curtisDatum m F p).n s) v
  have hx : (((e x : ↥((curtisDatum m F p).X s)) : SLm1 m F)) =
      (x : SLm1 m F) := rfl
  rw [hx]
  have hn : (coverId m F p).nhat s = (curtisDatum m F p).n s := by
    rw [CentralCoverData.nhat]
    have h := (coverId m F p).map_nhatW ((curtisCoxeterSystem m).simple s)
    simp only [MonoidHom.id_apply] at h
    rw [h, CentralCoverData.nW_simple]
  rw [hn]

private theorem coverId_datum_heckeT_eq_big {k V : Type*} [Field k] [AddCommGroup V]
    [Module k V] (ρ : Representation k (SLm2 m F) V) (s : Fin (m+1)) (v : V) :
    (coverId (m+1) F p).datum.heckeT ρ s v =
      (curtisDatum (m+1) F p).heckeT ρ s v := by
  let : Fintype ↥((curtisDatum (m+1) F p).X s) := Fintype.ofFinite _
  let : Fintype ↥((coverId (m+1) F p).lX s) := Fintype.ofFinite _
  let : Fintype ↥((coverId (m+1) F p).datum.X s) := Fintype.ofFinite _
  rw [CurtisDatum.heckeT_apply, CurtisDatum.heckeT_apply]
  let e : ↥((coverId (m+1) F p).datum.X s) ≃ ↥((curtisDatum (m+1) F p).X s) :=
    (Equiv.cast (congrArg (fun t : Subgroup (SLm2 m F) => ↥t) (show (coverId (m+1) F p).datum.X s =
      (coverId (m+1) F p).lX s from rfl))).trans ((coverId (m+1) F p).lXEquiv s)
  refine Fintype.sum_equiv e _ _ ?_
  intro x
  change ρ ((x : SLm2 m F) * (coverId (m+1) F p).nhat s) v =
    ρ (((e x : ↥((curtisDatum (m+1) F p).X s)) : SLm2 m F) *
      (curtisDatum (m+1) F p).n s) v
  have hx : (((e x : ↥((curtisDatum (m+1) F p).X s)) : SLm2 m F)) =
      (x : SLm2 m F) := rfl
  rw [hx]
  have hn : (coverId (m+1) F p).nhat s = (curtisDatum (m+1) F p).n s := by
    rw [CentralCoverData.nhat]
    have h := (coverId (m+1) F p).map_nhatW ((curtisCoxeterSystem (m+1)).simple s)
    simp only [MonoidHom.id_apply] at h
    rw [h, CentralCoverData.nW_simple]
  rw [hn]

omit [Fact (Nat.Prime p)] in
private theorem coe_heckeT_restrictRep {k V : Type*} [Field k] [AddCommGroup V] [Module k V]
    (ρ : Representation k (SLm1 m F) V) (W : Submodule k V)
    (hW : ∀ g : SLm1 m F, ∀ w ∈ W, ρ g w ∈ W) (s : Fin m) (v : W) :
    (((curtisDatum m F p).heckeT (restrictRep ρ W hW) s v : W) : V) =
      (curtisDatum m F p).heckeT ρ s v := by
  let : Fintype ↥((curtisDatum m F p).X s) := Fintype.ofFinite _
  rw [CurtisDatum.heckeT_apply, CurtisDatum.heckeT_apply]
  simp only [Submodule.coe_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [restrictRep_apply]

theorem coe_heckeT_firstNodeRestrict {k V : Type*} [Field k] [AddCommGroup V] [Module k V]
    {ρ : Representation k (SLm2 m F) V} {y : V} {χ : SLm2 m F → k}
    {J : Finset (Fin (m+1))}
    (ht : IsCoverType (rankOne (m+1) F p) ρ y χ J) (s : Fin m) :
    (((coverId m F p).datum.heckeT (firstNodeRestrict m F ρ) s
        ⟨y, mem_firstRowFix_of_isCoverType (m := m) (F := F) (p := p) ht⟩ :
      ↥(firstRowFix m F ρ)) : V) =
      (coverId (m+1) F p).datum.heckeT ρ s.succ y := by
  rw [coverId_datum_heckeT_eq_small (m := m) (F := F) (p := p) (ρ := firstNodeRestrict m F ρ) (s := s)
      ⟨y, mem_firstRowFix_of_isCoverType (m := m) (F := F) (p := p) ht⟩]
  unfold firstNodeRestrict
  rw [coe_heckeT_restrictRep (m := m) (F := F) (p := p) (ρ := ρ.comp (embedSucc m F))
      (W := firstRowFix m F ρ) (hW := firstRowFix_stable_embedSucc m F ρ) s
      ⟨y, mem_firstRowFix_of_isCoverType (m := m) (F := F) (p := p) ht⟩]
  rw [heckeT_comp_embedSucc (m := m) (F := F) (p := p) (ρ := ρ) (s := s) (v := y)]
  rw [← coverId_datum_heckeT_eq_big (m := m) (F := F) (p := p) (ρ := ρ)
    (s := s.succ) (v := y)]

theorem coe_heckeT_lastNodeRestrict {k V : Type*} [Field k] [AddCommGroup V] [Module k V]
    {ρ : Representation k (SLm2 m F) V} {y : V} {χ : SLm2 m F → k}
    {J : Finset (Fin (m+1))}
    (ht : IsCoverType (rankOne (m+1) F p) ρ y χ J) (s : Fin m) :
    (((coverId m F p).datum.heckeT (lastNodeRestrict m F ρ) s
        ⟨y, mem_lastColFix_of_isCoverType (m := m) (F := F) (p := p) ht⟩ :
      ↥(lastColFix m F ρ)) : V) =
      (coverId (m+1) F p).datum.heckeT ρ s.castSucc y := by
  rw [coverId_datum_heckeT_eq_small (m := m) (F := F) (p := p) (ρ := lastNodeRestrict m F ρ) (s := s)
      ⟨y, mem_lastColFix_of_isCoverType (m := m) (F := F) (p := p) ht⟩]
  unfold lastNodeRestrict
  rw [coe_heckeT_restrictRep (m := m) (F := F) (p := p) (ρ := ρ.comp (embedCastSucc m F))
      (W := lastColFix m F ρ) (hW := lastColFix_stable_embedCastSucc m F ρ) s
      ⟨y, mem_lastColFix_of_isCoverType (m := m) (F := F) (p := p) ht⟩]
  rw [heckeT_comp_embedCastSucc (m := m) (F := F) (p := p) (ρ := ρ) (s := s) (v := y)]
  rw [← coverId_datum_heckeT_eq_big (m := m) (F := F) (p := p) (ρ := ρ)
    (s := s.castSucc) (v := y)]

theorem firstNodeRestrict_isCoverType {k V : Type*} [Field k] [AddCommGroup V] [Module k V]
    {ρ : Representation k (SLm2 m F) V} {y : V} {χ : SLm2 m F → k}
    {J : Finset (Fin (m+1))}
    (ht : IsCoverType (rankOne (m+1) F p) ρ y χ J) :
    IsCoverType (rankOne m F p) (firstNodeRestrict m F ρ)
      ⟨y, mem_firstRowFix_of_isCoverType (m := m) (F := F) (p := p) ht⟩
      (χ ∘ embedSucc m F)
      (Finset.univ.filter fun s : Fin m => s.succ ∈ J) := by
  let hyW := mem_firstRowFix_of_isCoverType (m := m) (F := F) (p := p) ht
  unfold IsCoverType
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [CurtisDatum.mem_fixU]
    intro u hu
    apply Subtype.ext
    unfold firstNodeRestrict
    rw [restrictRep_apply]
    change ρ (embedSucc m F u) y = y
    have hu' : u ∈ (curtisDatum m F p).U := by
      rwa [coverId_datum_U m F p] at hu
    have huB : embedSucc m F u ∈ (curtisDatum (m+1) F p).U :=
      embedSucc_mem_U m F p hu'
    have hyU := ht.1
    rw [CurtisDatum.mem_fixU] at hyU
    rw [coverId_datum_U (m+1) F p] at hyU
    exact hyU (embedSucc m F u) huB
  · intro h
    exact ht.2.1 (congrArg Subtype.val h)
  · intro h hh
    apply Subtype.ext
    unfold firstNodeRestrict
    rw [restrictRep_apply]
    change ρ (embedSucc m F h) y = χ (embedSucc m F h) • y
    have hh' : h ∈ (curtisDatum m F p).H := by
      rwa [Subgroup.comap_id] at hh
    have hhB : embedSucc m F h ∈ (curtisDatum (m+1) F p).H :=
      embedSucc_mem_H (m := m) (F := F) (p := p) hh'
    have hchar := ht.2.2.1
    rw [Subgroup.comap_id] at hchar
    exact hchar (embedSucc m F h) hhB
  · intro s
    rw [Finset.mem_filter]
    simp only [Finset.mem_univ, true_and]
    have hcoeeq := coe_heckeT_firstNodeRestrict (m := m) (F := F) (p := p) ht s
    have hiff : ((coverId m F p).datum.heckeT (firstNodeRestrict m F ρ) s
        ⟨y, hyW⟩ = 0) ↔
        ((coverId (m+1) F p).datum.heckeT ρ s.succ y = 0) := by
      constructor
      · intro h
        rw [← hcoeeq, h]
        rfl
      · intro h
        apply Subtype.ext
        rw [hcoeeq, h]
        rfl
    constructor
    · intro hs
      have hbig := (ht.2.2.2 s.succ).mp hs
      refine ⟨?_, hiff.mpr hbig.2⟩
      intro u
      simpa [Function.comp_apply, rankOne, embedSucc_hdiag] using hbig.1 u
    · intro hs
      apply (ht.2.2.2 s.succ).mpr
      refine ⟨?_, hiff.mp hs.2⟩
      intro u
      simpa [Function.comp_apply, rankOne, embedSucc_hdiag] using hs.1 u

theorem lastNodeRestrict_isCoverType {k V : Type*} [Field k] [AddCommGroup V] [Module k V]
    {ρ : Representation k (SLm2 m F) V} {y : V} {χ : SLm2 m F → k}
    {J : Finset (Fin (m+1))}
    (ht : IsCoverType (rankOne (m+1) F p) ρ y χ J) :
    IsCoverType (rankOne m F p) (lastNodeRestrict m F ρ)
      ⟨y, mem_lastColFix_of_isCoverType (m := m) (F := F) (p := p) ht⟩
      (χ ∘ embedCastSucc m F)
      (Finset.univ.filter fun s : Fin m => s.castSucc ∈ J) := by
  let hyW := mem_lastColFix_of_isCoverType (m := m) (F := F) (p := p) ht
  unfold IsCoverType
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [CurtisDatum.mem_fixU]
    intro u hu
    apply Subtype.ext
    unfold lastNodeRestrict
    rw [restrictRep_apply]
    change ρ (embedCastSucc m F u) y = y
    have hu' : u ∈ (curtisDatum m F p).U := by
      rwa [coverId_datum_U m F p] at hu
    have huB : embedCastSucc m F u ∈ (curtisDatum (m+1) F p).U :=
      embedCastSucc_mem_U m F p hu'
    have hyU := ht.1
    rw [CurtisDatum.mem_fixU] at hyU
    rw [coverId_datum_U (m+1) F p] at hyU
    exact hyU (embedCastSucc m F u) huB
  · intro h
    exact ht.2.1 (congrArg Subtype.val h)
  · intro h hh
    apply Subtype.ext
    unfold lastNodeRestrict
    rw [restrictRep_apply]
    change ρ (embedCastSucc m F h) y = χ (embedCastSucc m F h) • y
    have hh' : h ∈ (curtisDatum m F p).H := by
      rwa [Subgroup.comap_id] at hh
    have hhB : embedCastSucc m F h ∈ (curtisDatum (m+1) F p).H :=
      embedCastSucc_mem_H (m := m) (F := F) (p := p) hh'
    have hchar := ht.2.2.1
    rw [Subgroup.comap_id] at hchar
    exact hchar (embedCastSucc m F h) hhB
  · intro s
    rw [Finset.mem_filter]
    simp only [Finset.mem_univ, true_and]
    have hcoeeq := coe_heckeT_lastNodeRestrict (m := m) (F := F) (p := p) ht s
    have hiff : ((coverId m F p).datum.heckeT (lastNodeRestrict m F ρ) s
        ⟨y, hyW⟩ = 0) ↔
        ((coverId (m+1) F p).datum.heckeT ρ s.castSucc y = 0) := by
      constructor
      · intro h
        rw [← hcoeeq, h]
        rfl
      · intro h
        apply Subtype.ext
        rw [hcoeeq, h]
        rfl
    constructor
    · intro hs
      have hbig := (ht.2.2.2 s.castSucc).mp hs
      refine ⟨?_, hiff.mpr hbig.2⟩
      intro u
      simpa [Function.comp_apply, rankOne, embedCastSucc_hdiag] using hbig.1 u
    · intro hs
      apply (ht.2.2.2 s.castSucc).mpr
      refine ⟨?_, hiff.mp hs.2⟩
      intro u
      simpa [Function.comp_apply, rankOne, embedCastSucc_hdiag] using hs.1 u

theorem firstNodeRestrict_isSimple_of_isCoverType {k V : Type*} [Field k] [CharP k p]
    [AddCommGroup V] [Module k V] {ρ : Representation k (SLm2 m F) V} {y : V}
    {χ : SLm2 m F → k} {J : Finset (Fin (m+1))}
    (hρ : IsSimpleRep ρ) (hsplit : SplitOver k (curtisDatum (m+1) F p).H)
    (ht : IsCoverType (rankOne (m+1) F p) ρ y χ J) :
    IsSimpleRep (firstNodeRestrict m F ρ) :=
  firstNodeRestrict_isSimple (m := m) (F := F) (p := p) (ρ := ρ) hρ hsplit
    (mem_firstRowFix_of_isCoverType (m := m) (F := F) (p := p) ht) ht.2.1

theorem lastNodeRestrict_isSimple_of_isCoverType {k V : Type*} [Field k] [CharP k p]
    [AddCommGroup V] [Module k V] {ρ : Representation k (SLm2 m F) V} {y : V}
    {χ : SLm2 m F → k} {J : Finset (Fin (m+1))}
    (hρ : IsSimpleRep ρ) (hsplit : SplitOver k (curtisDatum (m+1) F p).H)
    (ht : IsCoverType (rankOne (m+1) F p) ρ y χ J) :
    IsSimpleRep (lastNodeRestrict m F ρ) :=
  lastNodeRestrict_isSimple (m := m) (F := F) (p := p) (ρ := ρ) hρ hsplit
    (mem_lastColFix_of_isCoverType (m := m) (F := F) (p := p) ht) ht.2.1


end

end CFSG.LieType.SpecialLinear
