module

public import CFSG.Certificates.Kernel.Spor.PK.BFS

public section

namespace CFSG.KS.PK

private theorem os_getD_mem {l : List Nat} {i : Nat} (h : i < l.length) : l.getD i 0 ∈ l := by
  simp [List.getD_eq_getElem?_getD, h]

private theorem os_exists_getD {l : List Nat} {p : Nat} (h : p ∈ l) :
    ∃ i, ∃ _ : i < l.length, l.getD i 0 = p := by
  obtain ⟨i, hi, e⟩ := List.mem_iff_getElem.1 h
  exact ⟨i, hi, by simp [List.getD_eq_getElem?_getD, hi, e]⟩

private theorem os_head_getD {O : List Nat} {r : Nat} (h0 : O.head? = some r) :
    O.getD 0 0 = r ∧ r ∈ O := by
  cases O with
  | nil => simp at h0
  | cons a t =>
    simp only [List.head?_cons, Option.some.injEq] at h0
    subst h0
    simp

private theorem os_pts_mem {n : Nat} {F : Nat → Nat → Nat} {lv : List Nat} {r : Nat} {s : BS}
    (hs : RunOK n F lv r s) {O : List Nat} (hr : r ∈ O) (hcl : ∀ p ∈ O, ∀ l ∈ lv, F l p ∈ O) :
    ∀ k, k < s.pts.length → s.pts.getD k 0 ∈ O := by
  intro k
  induction k using Nat.strongRecOn with
  | _ k ih =>
    intro hk
    by_cases hk0 : 0 < k
    · have hpar := hs.par_lt k hk0 hk
      rw [← hs.edge k hk0 hk]
      exact hcl _ (ih _ hpar (by omega)) _ (hs.lab_mem k hk0 hk)
    · have hk' : k = 0 := by omega
      subst hk'
      rw [hs.root]
      exact hr

private theorem os_mem_of_reach {F : Nat → Nat → Nat} {lv : List Nat} {r : Nat} {S O : List Nat}
    (hr : r ∈ S) (hO0 : O.getD 0 0 = r)
    (hreach : ∀ i < O.length, 0 < i → ∃ a < i, ∃ l ∈ lv, F l (O.getD a 0) = O.getD i 0)
    (hcl : ∀ p ∈ S, ∀ l ∈ lv, F l p ∈ S) :
    ∀ i, i < O.length → O.getD i 0 ∈ S := by
  intro i
  induction i using Nat.strongRecOn with
  | _ i ih =>
    intro hi
    by_cases hi0 : 0 < i
    · obtain ⟨a, ha, l, hl, e⟩ := hreach i hi hi0
      rw [← e]
      exact hcl _ (ih a ha (by omega)) l hl
    · have hi' : i = 0 := by omega
      subst hi'
      rw [hO0]
      exact hr

theorem run_perm_of_closed {n : Nat} {F : Nat → Nat → Nat} {lv : List Nat} {r : Nat}
    {O : List Nat} (hF : ∀ l ∈ lv, ∀ x < n, F l x < n) (hr : r < n) (hO : O.Nodup)
    (hOn : ∀ p ∈ O, p < n) (h0 : O.head? = some r)
    (hreach : ∀ i < O.length, 0 < i → ∃ a < i, ∃ l ∈ lv, F l (O.getD a 0) = O.getD i 0)
    (hcl : ∀ p ∈ O, ∀ l ∈ lv, F l p ∈ O) :
    (BS.run F lv n r).pts.Perm O := by
  obtain ⟨hO0, hrO⟩ := os_head_getD h0
  have hok := run_ok hF hr (lv := lv) (F := F)
  rw [List.perm_ext_iff_of_nodup hok.nodup hO]
  intro p
  constructor
  · intro hp
    obtain ⟨k, hk, rfl⟩ := os_exists_getD hp
    exact os_pts_mem hok hrO hcl k hk
  · intro hp
    obtain ⟨i, hi, rfl⟩ := os_exists_getD hp
    have hrs : r ∈ (BS.run F lv n r).pts := by
      have := os_getD_mem hok.pos
      rwa [hok.root] at this
    exact os_mem_of_reach hrs hO0 hreach (run_closed hF hr) i hi

end CFSG.KS.PK

end
