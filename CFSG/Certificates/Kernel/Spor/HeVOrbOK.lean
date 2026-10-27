module

public import CFSG.Certificates.Kernel.Spor.HeVOrb
import CFSG.Certificates.Kernel.Spor.PChainSound

public section

namespace CFSG.KS.HeVO

open CFSG.KS CFSG.KS.PEnum CFSG.KS.VO CFSG.Sporadic.He.Native CFSG.Sporadic.Th.Native

theorem vecOrbitOK_of {p d N : Nat} {A B : Array (Array Nat)} {T : Nat → Array Nat}
    {AL BE PA LA : Nat → Nat} (hN : 0 < N) (hN32 : N < 2 ^ 32)
    (hinj : ∀ i < N, ∀ j < N, T i = T j → i = j)
    (hcan : ∀ i < N, canonV p d (T i) = true)
    (hpt : ∀ i < N, r32 AL i < N ∧ r32 BE i < N ∧
      mulVec p d A (T i) = T (r32 AL i) ∧ mulVec p d B (T i) = T (r32 BE i))
    (hcnt : vorbCnt N AL BE PA LA = N) (chunks : Nat) :
    vecOrbitOK p d A B (T 0) (vRec N T AL BE PA LA) chunks = true := by
  have hsz : (vRec N T AL BE PA LA).keys.size = N := by simp [vRec]
  have hpt' : ∀ i < N, (vRec N T AL BE PA LA).keys[i]! = T i :=
    fun i hi => TBfs.ofFn_get (f := fun i => T i) hi
  have hap : ∀ i < N, ap (vRec N T AL BE PA LA).alpha i = r32 AL i :=
    fun i hi => TBfs.ap_ofFn hi
  have hbp : ∀ i < N, ap (vRec N T AL BE PA LA).beta i = r32 BE i :=
    fun i hi => TBfs.ap_ofFn hi
  have hpp : ∀ i < N, ap (vRec N T AL BE PA LA).par i = r32 PA i :=
    fun i hi => TBfs.ap_ofFn hi
  have hlp : ∀ i < N, ap (vRec N T AL BE PA LA).lab i = r32 LA i :=
    fun i hi => TBfs.ap_ofFn hi
  have hidx : ∀ i < N, (indexOf (vRec N T AL BE PA LA).keys).getD
      ((vRec N T AL BE PA LA).keys[i]!) (vRec N T AL BE PA LA).keys.size = i := by
    intro i hi
    have hv := VOR.vindex_get (pts := (vRec N T AL BE PA LA).keys) (k := id)
      (fun a ha b hb e => by
        rw [hsz] at ha hb
        simp only [id] at e
        rw [hpt' a ha, hpt' b hb] at e
        exact hinj a ha b hb e) i (by rw [hsz]; exact hi)
    simp only [id] at hv
    unfold indexOf
    rw [Std.HashMap.getD_eq_getD_getElem?, hv]
    rfl
  have htree := VOR.tree_facts hN hcnt
  unfold vecOrbitOK
  simp only [Bool.and_eq_true, decide_eq_true_eq, hsz, beq_iff_eq]
  refine ⟨⟨⟨hN, hN32⟩, hpt' 0 hN⟩, PC.parAll_of fun i hi => ?_⟩
  obtain ⟨haN, hbN, ha, hb⟩ := hpt i hi
  have hix := hidx i hi
  rw [hsz] at hix
  unfold vecCheckAt
  simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq, hsz]
  rw [hpt' i hi] at hix ⊢
  rw [hap i hi, hbp i hi, hpt' _ haN, hpt' _ hbN, ha, hb, hix]
  refine ⟨⟨⟨⟨⟨⟨hcan i hi, rfl⟩, haN⟩, rfl⟩, hbN⟩, rfl⟩, ?_⟩
  by_cases h0 : i = 0
  · exact Or.inl h0
  · right
    obtain ⟨hlt, ht⟩ := htree i (by omega) hi
    rw [hpp i hi, hlp i hi, hap _ (by omega), hbp _ (by omega)]
    exact ⟨hlt, ht⟩

end CFSG.KS.HeVO

end
