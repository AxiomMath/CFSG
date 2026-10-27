module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3A6iCard
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3A6iPerm
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3A6iRels
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeAut
public import CFSG.Timmesfeld.Final.Simple

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6

open CFSG.CosetTable CFSG.EvenSmallLie.OmegaEight

universe u

@[expose] noncomputable def curtisGen (i : Fin 8) : omegaT := ⟨gen i.val, gen_mem_omegaT i.2⟩

theorem coe_curtisGen (i : Fin 8) : (curtisGen i : Equiv.Perm (Fin 360)) = curtisPerm i := rfl

theorem coe_lift_curtisGen (x : FreeGroup (Fin 8)) :
    ((FreeGroup.lift curtisGen x : omegaT) : Equiv.Perm (Fin 360)) =
      FreeGroup.lift curtisPerm x := by
  have h : omegaT.subtype.comp (FreeGroup.lift curtisGen) = FreeGroup.lift curtisPerm :=
    FreeGroup.ext_hom _ _ fun i => by simp [coe_curtisGen]
  exact DFunLike.congr_fun h x

theorem lift_curtisGen_eq_one {r : List (Fin 8 × Bool)} (hr : r ∈ curtisPG) :
    FreeGroup.lift curtisGen (FreeGroup.mk r) = 1 :=
  Subtype.ext ((coe_lift_curtisGen _).trans (lift_curtisPerm_eq_one hr))

theorem curtisGen_rels : ∀ r ∈ curtisRels, curtisEval (List.ofFn curtisGen) r = 1 := by
  intro r hr
  rw [curtisEval_ofFn]
  exact lift_curtisGen_eq_one (by simp only [curtisPG, List.mem_map]; exact ⟨r, hr, rfl⟩)

theorem curtisRelations_curtisGen :
    CurtisRelations (fun i => (List.ofFn curtisGen).getD (2 * i) 1)
      (fun i => (List.ofFn curtisGen).getD (2 * i + 1) 1) :=
  (curtisRels_iff _).1 curtisGen_rels

theorem closure_curtisGen : Subgroup.closure (Set.range curtisGen) = ⊤ := by
  have hmap : (Subgroup.closure (Set.range curtisGen)).map omegaT.subtype =
      Subgroup.closure (Set.range curtisPerm) := by
    rw [MonoidHom.map_closure, ← Set.range_comp]
    rfl
  have hle : omegaT ≤ (Subgroup.closure (Set.range curtisGen)).map omegaT.subtype := by
    rw [hmap, omegaT_eq, Subgroup.closure_le]
    rintro _ ⟨j, hj, rfl⟩
    exact Subgroup.subset_closure ⟨⟨j, hj⟩, rfl⟩
  rw [eq_top_iff]
  rintro x -
  obtain ⟨y, hy, hyx⟩ := hle x.2
  rwa [show y = x from Subtype.ext hyx] at hy

theorem curtisToGroup_gen_bijective :
    Function.Bijective (curtisToGroup (t := curtisGen) curtisGen_rels) := by
  obtain ⟨hfin, hcard⟩ := card_curtisPG_le
  exact (curtisToGroup_surjective curtisGen_rels closure_curtisGen).bijective_of_nat_card_le
    (by rw [card_omegaT]; exact hcard.trans (by norm_num))

theorem curtisOmegaT_isSimple : IsSimpleGroup omegaT :=
  CFSG.Timmesfeld.isSimpleGroup_of_lieModel lieModel_omegaT

theorem curtisD42_recognition {Y : Type u} [Group Y] [Nontrivial Y] (t : Fin 8 → Y)
    (hrel : ∀ r ∈ curtisRels, curtisEval (List.ofFn t) r = 1)
    (hgen : Subgroup.closure (Set.range t) = ⊤) : Nonempty (Y ≃* omegaT) := by
  haveI := curtisOmegaT_isSimple
  have hφs := curtisToGroup_surjective hrel hgen
  have hψ := curtisToGroup_gen_bijective
  have hφi : Function.Injective (curtisToGroup hrel) := by
    rw [← MonoidHom.ker_eq_bot_iff]
    have hN : ((curtisToGroup hrel).ker.map
        (curtisToGroup (t := curtisGen) curtisGen_rels)).Normal :=
      Subgroup.Normal.map inferInstance _ hψ.2
    rcases @IsSimpleGroup.eq_bot_or_eq_top_of_normal _ _ _ _ hN with h | h
    · rw [eq_bot_iff]
      intro x hx
      have : curtisToGroup (t := curtisGen) curtisGen_rels x ∈
          (curtisToGroup hrel).ker.map (curtisToGroup (t := curtisGen) curtisGen_rels) :=
        ⟨x, hx, rfl⟩
      rw [h, Subgroup.mem_bot] at this
      exact Subgroup.mem_bot.2 (hψ.1 (by rw [this, map_one]))
    · exfalso
      have hall : ∀ x, x ∈ (curtisToGroup hrel).ker := by
        intro x
        have : curtisToGroup (t := curtisGen) curtisGen_rels x ∈
            (curtisToGroup hrel).ker.map (curtisToGroup (t := curtisGen) curtisGen_rels) := by
          rw [h]; trivial
        obtain ⟨n, hn, hnx⟩ := this
        rwa [← hψ.1 hnx]
      obtain ⟨y, hy⟩ := exists_ne (1 : Y)
      obtain ⟨x, rfl⟩ := hφs y
      exact hy (MonoidHom.mem_ker.1 (hall x))
  exact ⟨(MulEquiv.ofBijective _ ⟨hφi, hφs⟩).symm.trans (MulEquiv.ofBijective _ hψ)⟩

theorem curtisD42_lieModel {Y : Type} [Group Y] [Nontrivial Y] (t : Fin 8 → Y)
    (hrel : ∀ r ∈ curtisRels, curtisEval (List.ofFn t) r = 1)
    (hgen : Subgroup.closure (Set.range t) = ⊤) :
    CFSG.Blueprint.LieModel Y .POmegaPlus 4 2 1 := by
  obtain ⟨e⟩ := curtisD42_recognition t hrel hgen
  exact CFSG.LieType.CurtisTits.lieModel_of_mulEquiv e.symm lieModel_omegaT

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6
