module

import all Certificates.Data.Census
public import CFSG.Certificates.Kernel.GilmanCensus.RelSound

public section

namespace Certificates.GilmanCensusK

open Certificates.Census Std

@[expose] def kerPure (dt : Data) (m : Nat) : Array (Array Nat) :=
  null3 ((bitsOf m).map (dt.F[·]!)) dt.d

@[expose] def CacheOK (dt : Data) (c : Cache) : Prop :=
  (∀ m l, c.lab[m]? = some l → l = labelPure dt m) ∧ (∀ m k, c.ker[m]? = some k → k = kerPure dt m)

theorem kernelM_ok {dt : Data} {c : Cache} (hc : CacheOK dt c) (m : Nat) :
    ((kernelM dt m).run c).1 = kerPure dt m ∧ CacheOK dt ((kernelM dt m).run c).2 ∧
      ((kernelM dt m).run c).2.bad = c.bad := by
  cases hl : c.ker[m]? with
  | some l =>
    simp [kernelM, hl, StateT.run, get, getThe, MonadStateOf.get, StateT.get, bind, StateT.bind,
      pure, StateT.pure]
    exact ⟨hc.2 m l hl, hc⟩
  | none =>
    simp [kernelM, hl, StateT.run, get, getThe, MonadStateOf.get, StateT.get, bind, StateT.bind,
      pure, StateT.pure, modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet]
    refine ⟨?_, ?_⟩
    · rfl
    refine ⟨hc.1, ?_⟩
    intro m' l' h'
    simp only [HashMap.getElem?_insert] at h'
    split at h'
    · rename_i he
      have : m = m' := by simpa using he
      subst this
      simp at h'
      exact h'.symm
    · exact hc.2 m' l' h'

theorem kerPure_eq {dt : Data} {dk : DK} (h : Rel dt dk) (m : Nat) (hm : m < 2 ^ dk.N) :
    LL (kerPure dt m) = kernelK dk m := by
  have h128 := pow_mono_128 m dk.N hm (Nat.le_of_lt h.Nlt)
  unfold kerPure kernelK
  have hsz : ∀ r ∈ (Array.map (fun x => dt.F[x]!) (bitsOf m)).toList, r.size = dt.d := by
    intro r hr
    rw [bitsOf_eq m h128] at hr
    simp only [List.map_toArray, List.toList_toArray, List.mem_map] at hr
    obtain ⟨i, hi, rfl⟩ := hr
    have hiN := bitsK_lt m dk.N i hm hi
    have hFs : dt.F.size = dk.N := by rw [← length_LL, h.F, h.FN]
    apply h.Fsz
    rw [getElem!_pos dt.F i (by omega)]
    exact Array.getElem_mem_toList _
  rw [null3_eq _ _ hsz, h.d, bitsOf_eq m h128]
  congr 1
  simp only [LL, List.map_toArray, List.toList_toArray, List.map_map]
  apply List.map_congr_left
  intro i _
  exact fK_eq h i

end Certificates.GilmanCensusK

end
