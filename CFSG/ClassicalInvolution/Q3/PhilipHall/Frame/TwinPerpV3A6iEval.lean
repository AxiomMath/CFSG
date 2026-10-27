module

public import Certificates.Data.TwinPerpV3A6iCurtis

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6

open CFSG.CosetTable CFSG.ClassicalInvolution.Phan.Q3G

@[expose] def curtisEval {G : Type*} [Group G] (gens : List G) (w : List ℕ) : G :=
  w.foldl (fun acc k => acc * if k % 2 = 0 then gens.getD (k / 2) 1 else (gens.getD (k / 2) 1)⁻¹) 1

theorem decodeWord_cons_some {n c : ℕ} {l : Fin n × Bool} (h : decodeLetter n c = some l)
    (w : List ℕ) : decodeWord n (c :: w) = l :: decodeWord n w := by
  simp only [decodeWord, List.filterMap_cons_some h]

theorem decodeWord_cons_none {n c : ℕ} (h : decodeLetter n c = none) (w : List ℕ) :
    decodeWord n (c :: w) = decodeWord n w := by
  simp only [decodeWord, List.filterMap_cons_none h]

theorem curtisEval_foldl {G : Type*} [Group G] (t : Fin 8 → G) (w : List ℕ) (acc : G) :
    w.foldl (fun acc k => acc * if k % 2 = 0 then (List.ofFn t).getD (k / 2) 1
        else ((List.ofFn t).getD (k / 2) 1)⁻¹) acc =
      acc * FreeGroup.lift t (FreeGroup.mk (decodeWord 8 w)) := by
  induction w generalizing acc with
  | nil => simp [decodeWord, ← FreeGroup.one_eq_mk]
  | cons k w ih =>
    rw [List.foldl_cons, ih]
    by_cases h : k / 2 < 8
    · have hd : decodeLetter 8 k = some (⟨k / 2, h⟩, decide (k % 2 = 0)) := by
        simp [decodeLetter, h]
      have hg : (List.ofFn t).getD (k / 2) 1 = t ⟨k / 2, h⟩ := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn, dif_pos h]
        rfl
      rw [decodeWord_cons_some hd, FreeGroup.lift_mk, FreeGroup.lift_mk, List.map_cons,
        List.prod_cons, hg, mul_assoc]
      by_cases hk : k % 2 = 0 <;> simp [hk]
    · have hd : decodeLetter 8 k = none := by simp [decodeLetter, h]
      have hg : (List.ofFn t).getD (k / 2) 1 = 1 := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn, dif_neg h]
        rfl
      rw [decodeWord_cons_none hd, hg, inv_one, ite_self, mul_one]

theorem curtisEval_ofFn {G : Type*} [Group G] (t : Fin 8 → G) (w : List ℕ) :
    curtisEval (List.ofFn t) w = FreeGroup.lift t (FreeGroup.mk (decodeWord 8 w)) := by
  rw [curtisEval, curtisEval_foldl, one_mul]

theorem lift_eq_one_of_curtisEval {G : Type*} [Group G] {t : Fin 8 → G}
    (hrel : ∀ r ∈ curtisRels, curtisEval (List.ofFn t) r = 1) :
    ∀ r ∈ {r : FreeGroup (Fin 8) | r ∈ curtisPG.map FreeGroup.mk}, FreeGroup.lift t r = 1 := by
  intro r hr
  simp only [Set.mem_ofPred_eq, curtisPG, List.map_map, List.mem_map] at hr
  obtain ⟨w, hw, rfl⟩ := hr
  rw [← hrel w hw, curtisEval_ofFn]
  rfl

@[expose] def curtisToGroup {G : Type*} [Group G] {t : Fin 8 → G}
    (hrel : ∀ r ∈ curtisRels, curtisEval (List.ofFn t) r = 1) : PG 8 curtisPG →* G :=
  PresentedGroup.toGroup (f := t) (lift_eq_one_of_curtisEval hrel)

theorem curtisToGroup_of {G : Type*} [Group G] {t : Fin 8 → G}
    (hrel : ∀ r ∈ curtisRels, curtisEval (List.ofFn t) r = 1) (i : Fin 8) :
    curtisToGroup hrel (PresentedGroup.of i) = t i :=
  PresentedGroup.toGroup.of _

theorem curtisToGroup_surjective {G : Type*} [Group G] {t : Fin 8 → G}
    (hrel : ∀ r ∈ curtisRels, curtisEval (List.ofFn t) r = 1)
    (hgen : Subgroup.closure (Set.range t) = ⊤) : Function.Surjective (curtisToGroup hrel) := by
  rw [← MonoidHom.range_eq_top, eq_top_iff, ← hgen, Subgroup.closure_le]
  rintro _ ⟨i, rfl⟩
  exact ⟨PresentedGroup.of i, curtisToGroup_of hrel i⟩

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6
