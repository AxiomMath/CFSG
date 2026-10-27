
module

public import CFSG.Certificates.Kernel.Th.Max3S.Leaves

public section

namespace CFSG.KC.Th.Max3S

open CFSG.KC.Th CFSG.KC.Th.Gen

variable {D : Max3Data}

theorem mem_leaves_segPre {b : Bool} (hb : b ∈ segPre D) : b ∈ leaves D := by
  rw [leaves]
  exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (hb))))))))))

theorem mem_leaves_segNF {b : Bool} (hb : b ∈ segNF D) : b ∈ leaves D := by
  rw [leaves]
  exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ hb)))))))))

theorem mem_leaves_seg92 {b : Bool} (hb : b ∈ seg92 D) : b ∈ leaves D := by
  rw [leaves]
  exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ hb)))))))

theorem mem_leaves_segQQ {b : Bool} (hb : b ∈ segQQ D) : b ∈ leaves D := by
  rw [leaves]
  exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ hb))))))

theorem mem_leaves_segQC {b : Bool} (hb : b ∈ segQC D) : b ∈ leaves D := by
  rw [leaves]
  exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ hb)))))

theorem mem_leaves_segXY {b : Bool} (hb : b ∈ segXY D) : b ∈ leaves D := by
  rw [leaves]
  exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ hb))))

theorem mem_leaves_segND {b : Bool} (hb : b ∈ segND D) : b ∈ leaves D := by
  rw [leaves]
  exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ hb)))

theorem mem_leaves_seg89 {b : Bool} (hb : b ∈ seg89 D) : b ∈ leaves D := by
  rw [leaves]
  exact List.mem_append_left _ (List.mem_append_right _ hb)

theorem consts_leaf (h : max3Chk D = true) :
    BigS.constsOK D.ThS_c D.ThS_rm D.ThS_tm0 D.ThS_tm1 D.ThS_tm2 D.ThS_tm3 D.ThS_tm4 D.ThS_tm5
      D.ThS_tm6 D.ThS_tm7 D.ThS_up D.ThS_dg D.ThS_ONE = true :=
  leaves_true D h _ (mem_leaves_segPre (List.Mem.head _))

theorem decA_leaf (h : max3Chk D = true) : SeedS.decOK D.ThSeed_SA D.ThSeed_LA = true :=
  leaves_true D h _ (mem_leaves_segPre (.tail _ (List.Mem.head _)))

theorem t8_leaf (h : max3Chk D = true) :
    eqN (BigS.powB D.ThS_c D.ThS_rm D.ThS_ONE (D.ThM3_RB 5) 3 2) D.ThS_ONE = true :=
  leaves_true D h _ (mem_leaves_seg92 (List.Mem.head _))

theorem s8_leaf (h : max3Chk D = true) :
    eqN (BigS.powB D.ThS_c D.ThS_rm D.ThS_ONE (D.ThM3_RB 11) 19 5) D.ThS_ONE = true :=
  leaves_true D h _ (mem_leaves_seg92 (.tail _ (List.Mem.head _)))

theorem xx_leaf (h : max3Chk D = true) :
    eqN (mulB D.ThS_c D.ThS_rm (D.ThM3_RB 13) (D.ThM3_RB 13)) D.ThS_ONE = true :=
  leaves_true D h _ (mem_leaves_seg92 (.tail _ (.tail _ (List.Mem.head _))))

theorem y6_leaf (h : max3Chk D = true) :
    eqN (BigS.powB D.ThS_c D.ThS_rm D.ThS_ONE (D.ThM3_RB 14) 6 3) D.ThS_ONE = true :=
  leaves_true D h _ (mem_leaves_seg92 (.tail _ (.tail _ (.tail _ (List.Mem.head _)))))

theorem za_leaf (h : max3Chk D = true) : eqN (D.ThM3_RB 16) D.ThSeed_SA = true :=
  leaves_true D h _ (mem_leaves_seg92 (.tail _ (.tail _ (.tail _ (.tail _ (List.Mem.head _))))))

theorem z1_leaf (h : max3Chk D = true) : neN (D.ThM3_RB 16) D.ThS_ONE = true :=
  leaves_true D h _
    (mem_leaves_seg92 (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (List.Mem.head _)))))))

theorem zz_leaf (h : max3Chk D = true) :
    eqN (mulB D.ThS_c D.ThS_rm (D.ThM3_RB 16) (D.ThM3_RB 16)) D.ThS_ONE = true :=
  leaves_true D h _ (mem_leaves_seg92
    (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (List.Mem.head _))))))))

theorem zx_leaf (h : max3Chk D = true) :
    eqN (mulB D.ThS_c D.ThS_rm (D.ThM3_RB 16) (D.ThM3_RB 13))
      (mulB D.ThS_c D.ThS_rm (D.ThM3_RB 13) (D.ThM3_RB 16)) = true :=
  leaves_true D h _ (mem_leaves_seg92
    (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (List.Mem.head _)))))))))

theorem zy_leaf (h : max3Chk D = true) :
    eqN (mulB D.ThS_c D.ThS_rm (D.ThM3_RB 16) (D.ThM3_RB 14))
      (mulB D.ThS_c D.ThS_rm (D.ThM3_RB 14) (D.ThM3_RB 16)) = true :=
  leaves_true D h _ (mem_leaves_seg92
    (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _
      (List.Mem.head _))))))))))

theorem nfReg_true (h : max3Chk D = true) (k : Fin 512) : nfReg D k = true := by
  refine leaves_true D h _ (mem_leaves_segNF ?_)
  rw [segNF, List.mem_ofFn]
  exact ⟨k, rfl⟩

theorem qqChk_true (h : max3Chk D = true) (i : Fin 8) : qqChk D i = true := by
  refine leaves_true D h _ (mem_leaves_segQQ ?_)
  rw [segQQ, List.mem_flatten]
  exact ⟨_, (List.mem_ofFn ..).2 ⟨i, rfl⟩, List.Mem.head _⟩

theorem zqChk_true (h : max3Chk D = true) (i : Fin 8) : zqChk D i = true := by
  refine leaves_true D h _ (mem_leaves_segQQ ?_)
  rw [segQQ, List.mem_flatten]
  exact ⟨_, (List.mem_ofFn ..).2 ⟨i, rfl⟩, .tail _ (List.Mem.head _)⟩

theorem qcChk_true (h : max3Chk D = true) (i j : Fin 8) : qcChk D i j = true := by
  refine leaves_true D h _ (mem_leaves_segQC ?_)
  rw [segQC, List.mem_flatten]
  exact ⟨_, (List.mem_ofFn ..).2 ⟨i, rfl⟩, (List.mem_ofFn ..).2 ⟨j, rfl⟩⟩

theorem xqChk_true (h : max3Chk D = true) (i : Fin 8) : xqChk D i = true := by
  refine leaves_true D h _ (mem_leaves_segXY ?_)
  rw [segXY, List.mem_flatten]
  exact ⟨_, (List.mem_ofFn ..).2 ⟨i, rfl⟩, List.Mem.head _⟩

theorem yqChk_true (h : max3Chk D = true) (i : Fin 8) : yqChk D i = true := by
  refine leaves_true D h _ (mem_leaves_segXY ?_)
  rw [segXY, List.mem_flatten]
  exact ⟨_, (List.mem_ofFn ..).2 ⟨i, rfl⟩, .tail _ (List.Mem.head _)⟩

theorem i1Chk_true (h : max3Chk D = true) (k : Fin 512) : i1Chk D k = true := by
  refine leaves_true D h _ (mem_leaves_seg89 ?_)
  rw [seg89, List.mem_flatten]
  exact ⟨_, (List.mem_ofFn ..).2 ⟨k, rfl⟩, List.Mem.head _⟩

theorem i2Chk_true (h : max3Chk D = true) (k : Fin 512) : i2Chk D k = true := by
  refine leaves_true D h _ (mem_leaves_seg89 ?_)
  rw [seg89, List.mem_flatten]
  exact ⟨_, (List.mem_ofFn ..).2 ⟨k, rfl⟩, .tail _ (List.Mem.head _)⟩

theorem i3Chk_true (h : max3Chk D = true) (k : Fin 512) : i3Chk D k = true := by
  refine leaves_true D h _ (mem_leaves_seg89 ?_)
  rw [seg89, List.mem_flatten]
  exact ⟨_, (List.mem_ofFn ..).2 ⟨k, rfl⟩, .tail _ (.tail _ (List.Mem.head _))⟩

theorem chain_of_zipWith (f : ℕ → ℕ → Bool) :
    ∀ l : List ℕ, (∀ b ∈ List.zipWith f l l.tail, b = true) → List.IsChain (fun a b => f a b = true) l
  | [], _ => List.IsChain.nil
  | [a], _ => List.IsChain.singleton a
  | a :: c :: t, H => by
    have hz : List.zipWith f (a :: c :: t) (c :: t) = f a c :: List.zipWith f (c :: t) t := rfl
    refine List.IsChain.cons_cons (H (f a c) (by rw [List.tail_cons, hz]; exact List.Mem.head _)) ?_
    refine chain_of_zipWith f (c :: t) fun b hb => H b ?_
    rw [List.tail_cons, hz]
    exact List.Mem.tail _ hb

theorem ndChain_chain (h : max3Chk D = true) :
    List.IsChain (fun a b => D.ThM3_RB (25 + a) < D.ThM3_RB (25 + b)) ndChain := by
  have hc := chain_of_zipWith (fun a b => ltN (D.ThM3_RB (25 + a)) (D.ThM3_RB (25 + b))) ndChain
    fun b hb => leaves_true D h b (mem_leaves_segND hb)
  exact hc.imp fun a b hab => Nat.le_of_ble_eq_true hab

end CFSG.KC.Th.Max3S

end
