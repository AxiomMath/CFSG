module

public import CFSG.Certificates.Kernel.MonsterB.ArrBfsSound
public import CFSG.RankThree.Native.PermEnumeration

public section

namespace CFSG.KC.EnumBfs

open CFSG.KC.Bfs CFSG.Monster.B.Fischer CFSG.RankThree.Native CFSG.Monster.B.Co2.Native

theorem enumOK_enumBfs {n : ℕ} {gs : Array (Array ℕ)} {ps : List ℕ} {c : ArrCert} {fuel : ℕ}
    (h : enumOK n gs ps c = true) (hf : c.pts.size ≤ fuel) :
    enumOK n gs ps (enumBfs n gs ps fuel) = true ∧ (enumBfs n gs ps fuel).pts.size = c.pts.size := by
  classical
  have hgs : allLt gs.size (fun k => validA n gs[k]!) = true := by
    simp only [enumOK, Bool.and_eq_true] at h
    exact h.1
  have hc : arrCertOK (leftA n gs) gs.size (validA n) (keyA n ps) (idA n) c = true := by
    simp only [enumOK, Bool.and_eq_true] at h
    exact h.2
  set S : Finset (Array ℕ) := c.pts.toList.toFinset with hSdef
  have hmem : ∀ x, x ∈ S ↔ ∃ i < c.pts.size, c.pts[i]! = x := by
    intro x
    rw [hSdef, List.mem_toFinset, Array.mem_toList_iff, Array.mem_iff_getElem]
    constructor
    · rintro ⟨i, hi, rfl⟩
      exact ⟨i, hi, getElem!_pos c.pts i hi⟩
    · rintro ⟨i, hi, rfl⟩
      exact ⟨i, hi, (getElem!_pos c.pts i hi).symm⟩
  have hroot : idA n ∈ S := (hmem _).2 ⟨0, arrCertOK_pos hc, arrCertOK_root hc⟩
  have hcl : ∀ x ∈ S, ∀ k < gs.size, leftA n gs k x ∈ S := by
    intro x hx k hk
    obtain ⟨i, hi, rfl⟩ := (hmem x).1 hx
    obtain ⟨hj, e⟩ := arrCertOK_edge hc hi hk
    exact (hmem _).2 ⟨_, hj, e⟩
  have hR : ∀ x ∈ S, Reach (leftA n gs) gs.size (idA n) x := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := (hmem x).1 hx
    induction i using Nat.strong_induction_on with
    | _ i ih =>
      rcases Nat.eq_zero_or_pos i with rfl | hi0
      · rw [arrCertOK_root hc]
        exact Reach.root
      · obtain ⟨hp, hl, e⟩ := arrCertOK_tree hc hi0 hi
        rw [e]
        exact Reach.step _ hl (ih _ hp (hp.trans hi) ((hmem _).2 ⟨_, hp.trans hi, rfl⟩))
  have hS := reach_iff_of_closed hroot hcl hR
  have hv : ∀ x ∈ S, validA n x = true := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := (hmem x).1 hx
    exact arrCertOK_valid hc hi
  have hkey : ∀ x ∈ S, ∀ y ∈ S, keyA n ps x = keyA n ps y → x = y := by
    intro x hx y hy e
    obtain ⟨i, hi, rfl⟩ := (hmem x).1 hx
    obtain ⟨j, hj, rfl⟩ := (hmem y).1 hy
    rw [arrCertOK_keys_inj hc hi hj e]
  have hnd : c.pts.toList.Nodup := by
    rw [List.nodup_iff_injective_get]
    intro a b e
    have ha : (a : ℕ) < c.pts.size := by simpa using a.2
    have hb : (b : ℕ) < c.pts.size := by simpa using b.2
    have e' : c.pts[(a : ℕ)]! = c.pts[(b : ℕ)]! := by
      rw [getElem!_pos c.pts _ ha, getElem!_pos c.pts _ hb]
      simpa using e
    exact Fin.ext (arrCertOK_keys_inj hc ha hb (congrArg (keyA n ps) e'))
  have hcard : S.card = c.pts.size := by
    rw [hSdef, List.toFinset_card_of_nodup hnd, Array.length_toList]
  obtain ⟨hcert, -, hsize, -⟩ := arrBfs_spec (act := leftA n gs) (ngen := gs.size)
    (valid := validA n) (key := keyA n ps) (root := idA n) (fuel := fuel) S hS hv hkey
    (by rw [hcard]; exact hf)
  refine ⟨?_, hsize.trans hcard⟩
  unfold enumOK enumBfs
  rw [Bool.and_eq_true]
  exact ⟨hgs, hcert⟩

end CFSG.KC.EnumBfs

end
