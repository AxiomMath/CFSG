module

public import Certificates.Data.Kernel.Bounds.TableE
public import CFSG.Certificates.Kernel.CosetBoundsE
public import CFSG.Certificates.Kernel.Misc.Coset.PG

public section

namespace CFSG.KC.MiscCoset

open CFSG.CosetTable CFSG.Certificates

variable {m : ℕ}

theorem index_le_of_tableOkE (ws : List (List (Fin m × Bool))) {rels : List (List (ℕ × Bool))}
    (hrels : ws.map encW = rels) {inv L eps nLab nT N RW RM nR nS nW nF : ℕ}
    {F D Wd Wd2 R S : ℕ → ℕ} {amap : ℕ} {words : List (List (ℕ × Bool))} {walk cov : List ℕ}
    (h : KB.tableOkE inv L eps nLab nT N RW RM nR nS nW nF F D Wd Wd2 R S amap rels words walk cov =
      true) (hm : m < 256) (htop : KB.topOk amap m = true) :
    (KB.wordSub (pgGen ws) words).FiniteIndex ∧ (KB.wordSub (pgGen ws) words).index ≤ N := by
  obtain ⟨-, h0, hN⟩ := KB.tableOkE_sound_alpha (pgGen ws)
    (fun r hr _ => sword_rels ws hrels r hr) h
  rw [alphaSub_top ws hm htop, Subgroup.relIndex_top_right] at h0 hN
  exact ⟨⟨h0⟩, hN⟩

theorem TableFactE.genSub_index (ws : List (List (Fin m × Bool))) (hm : m < 256) (T : List (Fin m))
    {N : ℕ} (h : KB.TableFactE m (ws.map encW) (T.map fun x => [(x.val, true)]) N) :
    (genSub {r : FreeGroup (Fin m) | r ∈ ws.map FreeGroup.mk} T).FiniteIndex ∧
      (genSub {r : FreeGroup (Fin m) | r ∈ ws.map FreeGroup.mk} T).index ≤ N := by
  unfold KB.TableFactE at h
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h, htop⟩ := h
  have := index_le_of_tableOkE ws rfl h hm htop
  rwa [wordSub_letters] at this

section
variable {rels : List (List (ℕ × Bool))} {inv L eps nLab nT N RW RM nR nS nW nF : ℕ}
  {F D Wd Wd2 R S : ℕ → ℕ} {amap : ℕ} {words : List (List (ℕ × Bool))} {walk cov : List ℕ}

theorem genSub_index_le_of_tableOkE (ws : List (List (Fin m × Bool))) (hrels : ws.map encW = rels)
    (h : KB.tableOkE inv L eps nLab nT N RW RM nR nS nW nF F D Wd Wd2 R S amap rels words walk cov =
      true) (hm : m < 256) (htop : KB.topOk amap m = true) (T : List (Fin m))
    (hw : words = T.map fun x => [(x.val, true)]) :
    (genSub {r : FreeGroup (Fin m) | r ∈ ws.map FreeGroup.mk} T).FiniteIndex ∧
      (genSub {r : FreeGroup (Fin m) | r ∈ ws.map FreeGroup.mk} T).index ≤ N := by
  have := index_le_of_tableOkE ws hrels h hm htop
  rwa [hw, wordSub_letters] at this

theorem zpowers_index_le_of_tableOkE (ws : List (List (Fin m × Bool)))
    (hrels : ws.map encW = rels)
    (h : KB.tableOkE inv L eps nLab nT N RW RM nR nS nW nF F D Wd Wd2 R S amap rels words walk cov =
      true) (hm : m < 256) (htop : KB.topOk amap m = true) (u : List (Fin m × Bool))
    (hw : words = [encW u]) :
    (Subgroup.zpowers (PresentedGroup.mk {r : FreeGroup (Fin m) | r ∈ ws.map FreeGroup.mk}
        (FreeGroup.mk u))).FiniteIndex ∧
      (Subgroup.zpowers (PresentedGroup.mk {r : FreeGroup (Fin m) | r ∈ ws.map FreeGroup.mk}
        (FreeGroup.mk u))).index ≤ N := by
  have := index_le_of_tableOkE ws hrels h hm htop
  rwa [hw, wordSub_single] at this

end

end CFSG.KC.MiscCoset

end
