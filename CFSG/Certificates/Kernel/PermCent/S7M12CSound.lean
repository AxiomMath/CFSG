module

public import Certificates.Data.Kernel.PermCent.S7M12C
public import Certificates.Data.S7M12

public section

namespace CFSG.Certificates.Kernel.PkCV.S7M12C

open CFSG.Blueprint CFSG.ComponentClassification.M12Cover.SylowTable
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf CFSG.Sporadic.Mathieu
  Certificates.S5RowsM12 Certificates.S7M12 CFSG.KC.Enum

theorem codeOK_of_isCode {c : List ℕ} {σ : Equiv.Perm (Fin 12)} (h : IsCode c σ) :
    codeOK c = true := by
  simp only [codeOK, List.all_eq_true, List.mem_range, Bool.and_eq_true, decide_eq_true_eq,
    Bool.or_eq_true, beq_iff_eq, bne_iff_ne, ne_eq]
  intro a ha
  have ea : nth 0 c a = (σ ⟨a, ha⟩ : ℕ) := h.2 ⟨a, ha⟩
  refine ⟨ea ▸ (σ _).2, fun b hb => ?_⟩
  have eb : nth 0 c b = (σ ⟨b, hb⟩ : ℕ) := h.2 ⟨b, hb⟩
  by_cases hab : a = b
  · exact Or.inl hab
  · refine Or.inr fun e => hab ?_
    rw [ea, eb] at e
    exact congrArg Fin.val (σ.injective (Fin.ext e))

theorem ev_cvL {c : List ℕ} {σ : Equiv.Perm (Fin 12)} (h : IsCode c σ) : ev (cvL c) = σ := by
  have hk := codeOK_of_isCode h
  ext i
  rw [ev_apply]
  simp only [cvL, dif_pos hk]
  change pg (wC 12) (CFSG.KS.mask (wC 12)) (pmk 12 (wC 12) (nth 0 c)) i = _
  rw [pg_pmk Small.lt (fun x hx => (codeOK_lt hk x hx).trans hw) i.2]
  exact h.2 i

theorem evHom_apply (a : CV 12) : evHom 12 a = ev a := rfl

theorem fixPts_ev (c : CV 12) : M12Model.fixPts (ev c) = fpC c := by
  unfold M12Model.fixPts fpC
  have e : (Finset.univ.filter fun i : Fin 12 => ev c i = i) =
      ((List.finRange 12).filter fun i => decide (ev c i = i)).toFinset := by
    ext i
    simp [List.mem_filter, List.mem_finRange]
  rw [e, List.toFinset_card_of_nodup ((List.nodup_finRange 12).filter _)]

theorem sub_eltM {x : ℕ} (hx : x < 64) :
    NativeSporadic.M12.subtype (M12Model.eltM x) = evHom 12 (eC x) := by
  rw [evHom_apply, eC]
  exact (ev_cvL (M12Model.isCode_eltM hx)).symm

theorem sub_d0 : NativeSporadic.M12.subtype M12Model.d0 = evHom 12 D0c := by
  have h : M12Model.dPow 1 = d0L := rfl
  have hc := M12Model.isCode_d0
  rw [h] at hc
  rw [evHom_apply, D0c]
  exact (ev_cvL hc).symm

theorem sub_a : NativeSporadic.M12.subtype m12a = evHom 12 Ac := by
  rw [evHom_apply, Ac]
  exact (ev_cvL M12Model.isCode_a).symm

theorem sub_b : NativeSporadic.M12.subtype m12b = evHom 12 Bc := by
  rw [evHom_apply, Bc]
  exact (ev_cvL M12Model.isCode_b).symm

theorem sub_wM (w : List ℕ) :
    NativeSporadic.M12.subtype (M12Model.wM w) = evHom 12 (wordC Ac Bc w) := by
  have h : wordC Ac Bc w = M12Model.word Ac Bc w := rfl
  rw [h, M12Model.map_word, ← sub_a, ← sub_b]
  exact M12Model.map_word _ _ _ _

theorem flatMap_congr' {α β : Type*} {f g : α → List β} :
    ∀ {l : List α}, (∀ x ∈ l, f x = g x) → l.flatMap f = l.flatMap g
  | [], _ => rfl
  | a :: l, h => by
    rw [List.flatMap_cons, List.flatMap_cons, h a List.mem_cons_self,
      flatMap_congr' fun x hx => h x (List.mem_cons_of_mem a hx)]

theorem sylowL_map : (sylowL ()).map NativeSporadic.M12.subtype = SLc.map (evHom 12) := by
  rw [sylowL, SLc, List.map_map, List.map_map]
  exact List.map_congr_left fun x hx => sub_eltM (List.mem_range.1 hx)

theorem czL_map : (czL ()).map NativeSporadic.M12.subtype = CZc.map (evHom 12) := by
  rw [czL, CZc, List.map_flatMap, List.map_flatMap]
  refine flatMap_congr' fun x hx => ?_
  simp only [List.map_cons, List.map_nil, map_mul, sub_eltM (List.mem_range.1 hx), sub_d0]

theorem conjL_map : (conjL ()).map NativeSporadic.M12.subtype = CLc.map (evHom 12) := by
  simp only [conjL, CLc, List.map_cons, List.map_nil, sub_wM]

theorem sub_edgeE : NativeSporadic.M12.subtype (edgeE ()) = evHom 12 Ec := sub_wM _

theorem factAL_map : (factAL ()).map NativeSporadic.M12.subtype = FAc.map (evHom 12) := by
  simp only [factAL, FAc, List.map_cons, List.map_nil, map_inv, sub_edgeE, sub_d0,
    sub_eltM (x := 1) (by norm_num), sub_eltM (x := 3) (by norm_num)]

theorem factBL_map : (factBL ()).map NativeSporadic.M12.subtype = FBc.map (evHom 12) := by
  simp only [factBL, FBc, List.map_cons, List.map_nil, map_inv, sub_edgeE, sub_d0]

end CFSG.Certificates.Kernel.PkCV.S7M12C

end
