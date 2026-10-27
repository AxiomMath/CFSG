module

public import CFSG.Certificates.Kernel.Spor.PK.NatChain
public import Certificates.Data.CFSGNative.HN.LevelChain

public section

namespace CFSG.KS.RouteP

open CFSG.Sporadic.Th.Native CFSG.Perm.Native CFSG.KS.PK

variable {n root : Nat} {letters : Array Table} {lv : Array Nat}

theorem toNat_ofNat_of_lt' {k : Nat} (hk : k < 2 ^ 32) : (UInt32.ofNat k).toNat = k := by
  rw [UInt32.toNat_ofNat']
  exact Nat.mod_eq_of_lt hk

theorem hF_toList (hF : ∀ l ∈ lv, ∀ x < n, ap letters[l]! x < n) :
    ∀ l ∈ lv.toList, ∀ x < n, tabF letters l x < n :=
  fun l hl x hx => hF l (by simpa using hl) x hx

theorem treeOK_treeBFS (hn : n < 2 ^ 32) (hr : root < n)
    (hF : ∀ l ∈ lv, ∀ x < n, ap letters[l]! x < n) (hlv : ∀ l ∈ lv, l < 2 ^ 32) :
    treeOK n root (treeBFS n root letters lv) letters lv = true := by
  have hF' := hF_toList hF
  rw [treeBFS_eq hn hr hF']
  have := treeOK_treeOf (letters := letters) hn (run_ok hF' hr) (run_closed hF' hr)
    (fun l hl => hlv l (by simpa using hl))
  rwa [Array.toArray_toList] at this

theorem treeBFS_pts (hn : n < 2 ^ 32) (hr : root < n)
    (hF : ∀ l ∈ lv, ∀ x < n, ap letters[l]! x < n) :
    (treeBFS n root letters lv).pts =
      ((BS.run (tabF letters) lv.toList n root).pts.map UInt32.ofNat).toArray := by
  rw [treeBFS_eq hn hr (hF_toList hF)]
  rfl

theorem mem_run_pts_iff (hr : root < n) (hF : ∀ l ∈ lv, ∀ x < n, ap letters[l]! x < n)
    {O : Nat → Bool} (hroot : O root = true) (hlt : ∀ x, O x = true → x < n)
    (hcl : ∀ x, O x = true → ∀ l ∈ lv, O (ap letters[l]! x) = true)
    (hmin : ∀ P : Nat → Prop, P root → (∀ x, P x → ∀ l ∈ lv, P (ap letters[l]! x)) →
      ∀ x, O x = true → P x) (x : Nat) :
    x ∈ (BS.run (tabF letters) lv.toList n root).pts ↔ O x = true := by
  have hF' := hF_toList hF
  have hok := run_ok hF' hr
  have hrc := run_closed hF' hr
  generalize BS.run (tabF letters) lv.toList n root = s at hok hrc ⊢
  constructor
  · intro hx
    obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.1 hx
    have key : ∀ k (hk : k < s.pts.length), O (s.pts.getD k 0) = true := by
      intro k
      induction k using Nat.strongRecOn with
      | _ k ih =>
        intro hk
        by_cases hk0 : 0 < k
        · rw [← hok.edge k hk0 hk]
          exact hcl _ (ih _ (hok.par_lt k hk0 hk) (by have := hok.par_lt k hk0 hk; omega)) _
            (by simpa using hok.lab_mem k hk0 hk)
        · have : k = 0 := by omega
          subst this
          rw [hok.root]
          exact hroot
    have := key k hk
    simpa [List.getD_eq_getElem?_getD, hk] using this
  · intro hx
    refine hmin (fun y => y ∈ s.pts) ?_ ?_ x hx
    · have := hok.pos
      have e := hok.root
      rw [← e]
      simp [List.getD_eq_getElem?_getD, this]
    · intro y hy l hl
      exact hrc y hy l (by simpa using hl)

theorem treeBFS_size (hn : n < 2 ^ 32) (hr : root < n)
    (hF : ∀ l ∈ lv, ∀ x < n, ap letters[l]! x < n)
    {O : Nat → Bool} {m : Nat} (hroot : O root = true) (hlt : ∀ x, O x = true → x < n)
    (hcl : ∀ x, O x = true → ∀ l ∈ lv, O (ap letters[l]! x) = true)
    (hmin : ∀ P : Nat → Prop, P root → (∀ x, P x → ∀ l ∈ lv, P (ap letters[l]! x)) →
      ∀ x, O x = true → P x)
    (hm : ((List.range n).filter O).length = m) :
    (treeBFS n root letters lv).pts.size = m := by
  rw [treeBFS_pts hn hr hF]
  simp only [List.size_toArray, List.length_map]
  rw [← hm]
  have hok := run_ok (hF_toList hF) hr
  apply List.Perm.length_eq
  rw [List.perm_ext_iff_of_nodup hok.nodup (List.nodup_range.filter _)]
  intro x
  rw [mem_run_pts_iff hr hF hroot hlt hcl hmin, List.mem_filter, List.mem_range]
  constructor
  · intro h
    exact ⟨hlt x h, h⟩
  · intro h
    exact h.2

theorem exists_treeBFS_pts_iff (hn : n < 2 ^ 32) (hr : root < n)
    (hF : ∀ l ∈ lv, ∀ x < n, ap letters[l]! x < n)
    {O : Nat → Bool} (hroot : O root = true) (hlt : ∀ x, O x = true → x < n)
    (hcl : ∀ x, O x = true → ∀ l ∈ lv, O (ap letters[l]! x) = true)
    (hmin : ∀ P : Nat → Prop, P root → (∀ x, P x → ∀ l ∈ lv, P (ap letters[l]! x)) →
      ∀ x, O x = true → P x) (x : Nat) :
    (∃ k < (treeBFS n root letters lv).pts.size, ap (treeBFS n root letters lv).pts k = x) ↔
      O x = true := by
  have hok := run_ok (hF_toList hF) hr
  rw [← mem_run_pts_iff hr hF hroot hlt hcl hmin, treeBFS_pts hn hr hF]
  have hl : ∀ p ∈ (BS.run (tabF letters) lv.toList n root).pts, p < 2 ^ 32 :=
    fun p hp => Nat.lt_trans (hok.lt p hp) hn
  generalize (BS.run (tabF letters) lv.toList n root).pts = l at hl ⊢
  constructor
  · rintro ⟨k, hk, rfl⟩
    simp only [List.size_toArray, List.length_map] at hk
    unfold ap
    rw [getElem!_pos _ k (by simpa using hk)]
    simp only [List.getElem_toArray, List.getElem_map]
    rw [toNat_ofNat_of_lt' (hl _ (List.getElem_mem hk))]
    exact List.getElem_mem hk
  · intro hx
    obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.1 hx
    refine ⟨k, by simpa using hk, ?_⟩
    unfold ap
    rw [getElem!_pos _ k (by simpa using hk)]
    simp only [List.getElem_toArray, List.getElem_map]
    exact toNat_ofNat_of_lt' (hl _ (List.getElem_mem hk))

open CFSG.Sporadic.LevelChain.Native in
theorem levelTrees_get {starts base : Array Nat} {i : Nat} (hi : i < base.size) :
    (levelTrees n letters starts base)[i]! = treeBFS n base[i]! letters (levelLv starts i) := by
  unfold levelTrees
  rw [getElem!_pos _ i (by simpa using hi), Array.getElem_ofFn]

open CFSG.Sporadic.LevelChain.Native in
theorem treeOK_levelTrees (hn : n < 2 ^ 32) {starts base : Array Nat} {i : Nat} (hi : i < base.size)
    (hb : base[i]! < n) (hF : ∀ l ∈ levelLv starts i, ∀ x < n, ap letters[l]! x < n)
    (hlv : ∀ l ∈ levelLv starts i, l < 2 ^ 32) :
    treeOK n base[i]! (levelTrees n letters starts base)[i]! letters (levelLv starts i) = true := by
  rw [levelTrees_get hi]
  exact treeOK_treeBFS hn hb hF hlv

end CFSG.KS.RouteP

end
