module

public import CFSG.Certificates.Kernel.Spor.HBfsClosed
public import CFSG.Certificates.Kernel.SporSch.ClassOneSound
public import CFSG.Certificates.Kernel.SporSch.ConjClosureSpec
public import CFSG.LocalAnalysis.EvenSporadicStandard.RuStd.FactsB2Inputs

public section

namespace CFSG.KS.ClassOneH

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native
open CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native CFSG.KS.HBfs CFSG.KS.Tbl
open CFSG.EvenSporadicStandard.HypOne CFSG.EvenSporadicStandard.RuStd

variable {n : Nat}

theorem hashIndex_foldl (L : Array Table) (k : UInt64) :
    ∀ m : Nat, ((List.range m).foldl (fun mp i => mp.insert (hkey n L[i]!) i)
      (∅ : Std.HashMap UInt64 Nat))[k]? = none ∨
      ∃ i < m, hkey n L[i]! = k ∧
        ((List.range m).foldl (fun mp i => mp.insert (hkey n L[i]!) i)
          (∅ : Std.HashMap UInt64 Nat))[k]? = some i
  | 0 => Or.inl (by simp)
  | m + 1 => by
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil,
      Std.HashMap.getElem?_insert]
    by_cases e : (hkey n L[m]! == k) = true
    · rw [if_pos e]
      exact Or.inr ⟨m, by omega, beq_iff_eq.1 e, rfl⟩
    · rw [if_neg e]
      rcases hashIndex_foldl L k m with h | ⟨i, hi, hk, h⟩
      · exact Or.inl h
      · exact Or.inr ⟨i, by omega, hk, h⟩

theorem hashIndex_get {L : Array Table}
    (hd : ∀ a < L.size, ∀ b < L.size, hkey n L[a]! = hkey n L[b]! → a = b) {i : Nat}
    (hi : i < L.size) : (hashIndex n L)[hkey n L[i]!]? = some i := by
  unfold hashIndex
  have key : ∀ m ≤ L.size, i < m → ((List.range m).foldl (fun mp i => mp.insert (hkey n L[i]!) i)
      (∅ : Std.HashMap UInt64 Nat))[hkey n L[i]!]? = some i := by
    intro m
    induction m with
    | zero => intro _ h; omega
    | succ m ih =>
      intro hm him
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil,
        Std.HashMap.getElem?_insert]
      by_cases e : (hkey n L[m]! == hkey n L[i]!) = true
      · rw [if_pos e, hd m (by omega) i hi (beq_iff_eq.1 e)]
      · rw [if_neg e]
        rcases Nat.lt_succ_iff_lt_or_eq.1 him with a | rfl
        · exact ih (by omega) a
        · exact absurd (beq_iff_eq.2 rfl) e
  exact key L.size (Nat.le_refl _) hi

theorem memTH_of_rep {L : Array Table}
    (hd : ∀ a < L.size, ∀ b < L.size, hkey n L[a]! = hkey n L[b]! → a = b) {i : Nat}
    (hi : i < L.size) {y : Table} {g : Equiv.Perm (Fin n)} (hL : Rep n L[i]! g) (hy : Rep n y g) :
    memTH n L (hashIndex n L) y = true := by
  unfold memTH
  rw [hkey_eq_hkeyOf hy, ← hkey_eq_hkeyOf hL, hashIndex_get hd hi]
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨hi, (CFSG.KS.Tbl.tblEq_iff_eq hy hL).2 rfl⟩

section Closure

variable {gens gensInv : Array Table} {γ : Nat → Equiv.Perm (Fin n)}
  {C : Set (Equiv.Perm (Fin n))}

theorem conjClosureH_one (hn : n < 2 ^ 32)
    (hg : ∀ l < gens.size, Rep n gens[l]! (γ l) ∧ Rep n gensInv[l]! (γ l)⁻¹)
    (hCf : C.Finite) (hCcl : ∀ l < gens.size, ∀ x ∈ C, γ l * x * (γ l)⁻¹ ∈ C)
    (hmin : ∀ g ∈ C, ∀ D : Set (Equiv.Perm (Fin n)), D.Finite → g ∈ D →
      (∀ l < gens.size, ∀ y ∈ D, γ l * y * (γ l)⁻¹ ∈ D) → C ⊆ D)
    (hinj : Set.InjOn (hkeyOf n) C)
    {x : Table} {g₀ : Equiv.Perm (Fin n)} (hx : Rep n x g₀) (hg₀ : g₀ ∈ C) {cap : Nat}
    (hcap : C.ncard ≤ cap) :
    conjTreeOK n gens gensInv x (conjClosureH n gens gensInv x cap).1
        (conjClosureH n gens gensInv x cap).2.1 (conjClosureH n gens gensInv x cap).2.2 = true ∧
      (∀ a < (conjClosureH n gens gensInv x cap).1.size,
        ∀ b < (conjClosureH n gens gensInv x cap).1.size,
        hkey n (conjClosureH n gens gensInv x cap).1[a]! =
          hkey n (conjClosureH n gens gensInv x cap).1[b]! → a = b) ∧
      (conjClosureH n gens gensInv x cap).1.size = C.ncard ∧
      (∀ i < (conjClosureH n gens gensInv x cap).1.size,
        ∃ y ∈ C, Rep n (conjClosureH n gens gensInv x cap).1[i]! y) ∧
      ∀ y ∈ C, ∃ i < (conjClosureH n gens gensInv x cap).1.size,
        Rep n (conjClosureH n gens gensInv x cap).1[i]! y := by
  classical
  let Good : Table → Prop := fun T => ∃ g ∈ C, Rep n T g
  let K : Finset UInt64 := hCf.toFinset.image (hkeyOf n)
  have hK : ∀ T, Good T → hkey n T ∈ K := by
    rintro T ⟨g, hgC, hT⟩
    rw [hkey_eq_hkeyOf hT]
    exact Finset.mem_image.2 ⟨g, hCf.mem_toFinset.2 hgC, rfl⟩
  have hKc : K.card ≤ cap := by
    refine (Finset.card_image_le).trans ?_
    rw [← Set.ncard_eq_toFinset_card C hCf]
    exact hcap
  have hstep : ∀ l < gens.size, ∀ T, Good T → Good (conjT n gens[l]! gensInv[l]! T) := by
    rintro l hl T ⟨g, hgC, hT⟩
    exact ⟨_, hCcl l hl g hgC, rep_conjT (hg l hl).1 (hg l hl).2 hT⟩
  have R := hbfs_closed (key := hkey n) (st := fun l y => conjT n gens[l]! gensInv[l]! y)
    (root := x) (Good := Good) ⟨g₀, hg₀, hx⟩ hstep hK hKc
  have e1 : conjClosureH n gens gensInv x cap =
      hbfs (hkey n) (fun l y => conjT n gens[l]! gensInv[l]! y) gens.size x cap := rfl
  rw [← e1] at R
  generalize conjClosureH n gens gensInv x cap = r at R ⊢
  obtain ⟨E, par, lab⟩ := r
  obtain ⟨rpos, rps, rls, rroot, rgood, rinj, rtree, rclose⟩ := R
  simp only at rpos rps rls rroot rgood rinj rtree rclose ⊢
  choose! φ hφC hφ using rgood
  let D : Set (Equiv.Perm (Fin n)) := φ '' {i | i < E.size}
  have hDC : D ⊆ C := by
    rintro _ ⟨i, hi, rfl⟩
    exact hφC i hi
  have hφ0 : φ 0 = g₀ := by
    have := hφ 0 rpos
    rw [rroot] at this
    exact CFSG.KS.ClassOne.rep_unique this hx
  have hDcl : ∀ l < gens.size, ∀ y ∈ D, γ l * y * (γ l)⁻¹ ∈ D := by
    rintro l hl _ ⟨i, hi, rfl⟩
    obtain ⟨q, hq, e⟩ := rclose i hi l hl
    have h1 := rep_conjT (hg l hl).1 (hg l hl).2 (hφ i hi)
    refine ⟨q, hq, hinj (hφC q hq) (hCcl l hl _ (hφC i hi)) ?_⟩
    rw [← hkey_eq_hkeyOf (hφ q hq), ← hkey_eq_hkeyOf h1]
    exact e.symm
  have hCD : C ⊆ D := hmin g₀ hg₀ D (hCf.subset hDC) ⟨0, rpos, hφ0⟩ hDcl
  have hφinj : Set.InjOn φ {i | i < E.size} := fun a ha b hb e =>
    rinj a ha b hb (by rw [hkey_eq_hkeyOf (hφ a ha), hkey_eq_hkeyOf (hφ b hb), e])
  have hsize : E.size = C.ncard := by
    rw [← Set.Subset.antisymm hDC hCD, hφinj.ncard_image,
      show {i | i < E.size} = ((Finset.range E.size : Finset Nat) : Set Nat) by ext; simp,
      Set.ncard_coe_finset, Finset.card_range]
  refine ⟨?_, rinj, hsize, fun i hi => ⟨φ i, hφC i hi, hφ i hi⟩, fun y hy => ?_⟩
  · unfold conjTreeOK
    simp only [Bool.and_eq_true, decide_eq_true_eq, allIn_eq_true]
    refine ⟨⟨rpos, by rw [rroot]; exact CFSG.KS.ClassOne.tblEq_refl x⟩, fun k _ hk => ?_⟩
    obtain ⟨t1, t2, t3⟩ := rtree k (by omega) hk
    refine ⟨⟨t1, t2⟩, ?_⟩
    rw [← t3]
    exact CFSG.KS.ClassOne.tblEq_refl _
  · obtain ⟨i, hi, rfl⟩ := hCD hy
    exact ⟨i, hi, hφ i hi⟩

theorem hkeysDistinct_of {L : Array Table}
    (hd : ∀ a < L.size, ∀ b < L.size, hkey n L[a]! = hkey n L[b]! → a = b) :
    hkeysDistinct n L.toList = true := by
  unfold hkeysDistinct
  apply strictlyIncreasing_of_pairwise
  have hs := List.pairwise_mergeSort (le := fun a b : Nat => decide (a ≤ b))
    (fun a b c hab hbc => by simp only [decide_eq_true_eq] at *; omega)
    (fun a b => by simp only [Bool.or_eq_true, decide_eq_true_eq]; omega)
    (L.toList.map fun T => (hkey n T).toNat)
  have h : (L.toList.map fun T => (hkey n T).toNat).Nodup := by
    rw [List.nodup_iff_injective_get]
    intro a b e
    simp only [List.get_eq_getElem, List.getElem_map, Array.getElem_toList] at e
    have ha : a.val < L.size := by simpa using a.isLt
    have hb : b.val < L.size := by simpa using b.isLt
    rw [← getElem!_pos L a.val ha, ← getElem!_pos L b.val hb] at e
    exact Fin.ext (hd a ha b hb (UInt64.toNat_inj.1 e))
  have hnd := (List.mergeSort_perm (L.toList.map fun T => (hkey n T).toNat)
    (fun a b : Nat => decide (a ≤ b))).nodup_iff.2 h
  refine (hs.and (List.nodup_iff_pairwise_ne.1 hnd)).imp fun ⟨h1, h2⟩ => ?_
  simp only [decide_eq_true_eq] at h1
  omega

theorem classCheckOf_one (hn : n < 2 ^ 32)
    (hg : ∀ l < gens.size, Rep n gens[l]! (γ l) ∧ Rep n gensInv[l]! (γ l)⁻¹)
    (hCf : C.Finite) (hCcl : ∀ l < gens.size, ∀ x ∈ C, γ l * x * (γ l)⁻¹ ∈ C)
    (hmin : ∀ g ∈ C, ∀ D : Set (Equiv.Perm (Fin n)), D.Finite → g ∈ D →
      (∀ l < gens.size, ∀ y ∈ D, γ l * y * (γ l)⁻¹ ∈ D) → C ⊆ D)
    (hinj : Set.InjOn (hkeyOf n) C)
    {x : Table} {g₀ : Equiv.Perm (Fin n)} (hx : Rep n x g₀) (hg₀ : g₀ ∈ C) {cap N : Nat}
    (hcap : C.ncard ≤ cap) (hN : C.ncard = N) :
    classCheckOf n gens gensInv x (conjClosureH n gens gensInv x cap) N = true := by
  obtain ⟨htree, hd, hsize, hin, hall⟩ :=
    conjClosureH_one hn hg hCf hCcl hmin hinj hx hg₀ hcap
  generalize conjClosureH n gens gensInv x cap = r at htree hd hsize hin hall ⊢
  obtain ⟨E, par, lab⟩ := r
  simp only at htree hd hsize hin hall ⊢
  have hCinv : ∀ l < gens.size, ∀ y ∈ C, (γ l)⁻¹ * y * (γ l)⁻¹⁻¹ ∈ C := by
    intro l hl
    have hcl := CFSG.KS.SporSch.ClsSpec.conj_closed (gs := {γ l}) (S := C)
      (fun g hg y hy => by rw [Set.mem_singleton_iff.1 hg]; exact hCcl l hl y hy)
    exact hcl _ (Subgroup.inv_mem _ (Subgroup.subset_closure rfl))
  unfold classCheckOf conjClosedH
  simp only [Bool.and_eq_true, beq_iff_eq, Array.all_eq_true, List.all_eq_true, List.mem_range]
  refine ⟨⟨⟨htree, fun k hk l hl => ?_⟩, hkeysDistinct_of hd⟩, hsize.trans hN⟩
  have hk' : k < E.size := hk
  rw [← getElem!_pos E k hk']
  obtain ⟨y, hyC, hy⟩ := hin k hk'
  obtain ⟨i1, hi1, h1⟩ := hall _ (hCcl l hl y hyC)
  obtain ⟨i2, hi2, h2⟩ := hall _ (hCinv l hl y hyC)
  refine ⟨memTH_of_rep hd hi1 h1 (rep_conjT (hg l hl).1 (hg l hl).2 hy),
    memTH_of_rep hd hi2 h2 (rep_conjT (hg l hl).2 ?_ hy)⟩
  rw [inv_inv]
  exact (hg l hl).1

end Closure

end CFSG.KS.ClassOneH

end
