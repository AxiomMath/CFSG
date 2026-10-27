module

public import CFSG.Certificates.NativeSetOrbit
public import Certificates.Data.CFSGNative.Co3Schreier.Orbit

public section

namespace CFSG.ClassicalInvolution

open CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2 CFSG.Sporadic.Schreier.Co3.Native
open scoped Pointwise

theorem keysSortedOK_nodup {sets : Array (List ℕ)} (h : keysSortedOK sets = true) :
    sets.toList.Nodup := by
  have hchain : ∀ l : List ℕ, strictlyIncreasing l = true → l.Pairwise (· < ·) := by
    intro l hl
    rw [← List.isChain_iff_pairwise]
    induction l with
    | nil => exact List.IsChain.nil
    | cons a l ih =>
      cases l with
      | nil => exact List.IsChain.singleton a
      | cons b l =>
        simp only [strictlyIncreasing, Bool.and_eq_true, decide_eq_true_eq] at hl
        exact List.IsChain.cons_cons hl.1 (ih hl.2)
  have h1 := (hchain _ h).nodup
  have h2 : (sets.toList.map setKey).Nodup := ((List.mergeSort_perm _ _).nodup_iff).1 h1
  exact h2.of_map setKey

theorem ncard_orbit_fixed_ge {n : ℕ} (H : Subgroup (Equiv.Perm (Fin n))) (gens : Array (Array ℕ))
    (Gs : ℕ → Equiv.Perm (Fin n)) (hrep : ∀ k < gens.size, Rep n gens[k]! (Gs k))
    (hmem : ∀ k < gens.size, Gs k ∈ H) {z : Equiv.Perm (Fin n)} {zArr : Array ℕ}
    (hz : Rep n zArr z) {sets : Array (List ℕ)} {par lab : Array ℕ}
    (hok : translatesOK gens (fixedList n zArr) sets par lab = true)
    (hkeys : keysSortedOK sets = true) :
    sets.size ≤ (Set.range fun g : H => g • {p : Fin n | z p = p}).ncard := by
  have h := le_ncard_orbit_of_translatesOK (H := H) hrep hmem (pointList_fixedList zArr) hok
    (keysSortedOK_nodup hkeys)
  rwa [finSet_fixedList hz] at h

end CFSG.ClassicalInvolution
