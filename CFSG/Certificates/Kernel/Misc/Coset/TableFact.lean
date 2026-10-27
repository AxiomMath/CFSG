module

public import Certificates.Data.Kernel.Bounds.TableFact
public import CFSG.Certificates.Kernel.Misc.Coset.PG
public import CFSG.Certificates.Kernel.Misc.Coset.PGChain

public section

namespace CFSG.KC.MiscCoset

open CFSG.CosetTable CFSG.Certificates

variable {m : ℕ}

theorem TableFact.genSub_index (ws : List (List (Fin m × Bool))) (hm : m < 256) (T : List (Fin m))
    {N : ℕ} (h : KB.TableFact m (ws.map encW) (T.map fun x => [(x.val, true)]) N) :
    (genSub {r : FreeGroup (Fin m) | r ∈ ws.map FreeGroup.mk} T).FiniteIndex ∧
      (genSub {r : FreeGroup (Fin m) | r ∈ ws.map FreeGroup.mk} T).index ≤ N := by
  unfold KB.TableFact at h
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h, htop⟩ := h
  exact genSub_index_le_of_tableOk ws rfl h hm htop T rfl

theorem TableFact.card (ws : List (List (Fin m × Bool))) (hm : m < 256) {N : ℕ}
    (h : KB.TableFact m (ws.map encW) [] N) : Finite (PG m ws) ∧ Nat.card (PG m ws) ≤ N := by
  unfold KB.TableFact at h
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h, htop⟩ := h
  exact card_le_of_tableOk ws rfl h hm htop rfl

theorem TableFact.zpowers_index (ws : List (List (Fin m × Bool))) (hm : m < 256)
    (u : List (Fin m × Bool)) {N : ℕ} (h : KB.TableFact m (ws.map encW) [encW u] N) :
    (Subgroup.zpowers (PresentedGroup.mk {r : FreeGroup (Fin m) | r ∈ ws.map FreeGroup.mk}
        (FreeGroup.mk u))).FiniteIndex ∧
      (Subgroup.zpowers (PresentedGroup.mk {r : FreeGroup (Fin m) | r ∈ ws.map FreeGroup.mk}
        (FreeGroup.mk u))).index ≤ N := by
  unfold KB.TableFact at h
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h, htop⟩ := h
  exact zpowers_index_le_of_tableOk ws rfl h hm htop u rfl

theorem TableFact.card_restrict (ws : List (List (Fin m × Bool))) (hm : m < 256) (T : List (Fin m))
    (hT : T.length < 256) {n N : ℕ}
    (hi : KB.TableFact m (ws.map encW) (T.map fun x => [(x.val, true)]) n)
    (hr : KB.TableFact T.length ((restrictWords T ws).map encW) [] N) :
    Finite (PG m ws) ∧ Nat.card (PG m ws) ≤ n * N :=
  card_le_of_index_restrict ws T (TableFact.genSub_index ws hm T hi)
    (TableFact.card (restrictWords T ws) hT hr)

end CFSG.KC.MiscCoset
