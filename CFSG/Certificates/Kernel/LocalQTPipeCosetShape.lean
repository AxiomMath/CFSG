module

public import CFSG.Certificates.Kernel.LocalQTPipeCosetBfs
public import CFSG.Certificates.Kernel.LocalQTPipeBasic

public section

namespace CFSG.KC.LQT.PPC

open CFSG.KC.Ord CFSG.KC.LQT.P CFSG.KC.LQT.S CFSG.KC.LQT.L CFSG.KC.LQT.PW CFSG.KC.LQT.BC
open CFSG.KC.LQT.PP CFSG.KC.LQT.BW.Pf CFSG.KC.LQT.PPB
open CFSG.QuasithinUnique.Setup.X1 CFSG.QuasithinUnique.K1.SporadicPerm
open CFSG.KC.LQT.P (letB impB allL anyL orB_iff andB_iff notB_iff impB_iff beq_iff blt_iff letB_eq)

theorem foldl_repList {N : Nat} (repR : Array Nat) (hN : ∀ i, i < N → True) :
    ∀ (l : List Nat) (acc : List Nat), (∀ i ∈ l, i < N) → (∀ y ∈ acc, ∃ i < N, y = repR.getD i 0) →
      (∀ y ∈ l.foldl (fun acc i =>
          if acc.contains (repR.getD i 0) then acc else repR.getD i 0 :: acc) acc,
        ∃ i < N, y = repR.getD i 0) ∧
      (∀ i ∈ l, repR.getD i 0 ∈ l.foldl (fun acc i =>
          if acc.contains (repR.getD i 0) then acc else repR.getD i 0 :: acc) acc) := by
  intro l
  induction l with
  | nil => intro acc _ h; exact ⟨h, by simp⟩
  | cons i l ih =>
    intro acc hl hacc
    have hiN : i < N := hl i List.mem_cons_self
    simp only [List.foldl_cons]
    have hl' : ∀ j ∈ l, j < N := fun j hj => hl j (List.mem_cons_of_mem _ hj)
    have mono : ∀ (l : List Nat) (acc : List Nat) , ∀ y ∈ acc, y ∈ l.foldl (fun acc i =>
        if acc.contains (repR.getD i 0) then acc else repR.getD i 0 :: acc) acc := by
      intro l
      induction l with
      | nil => intro acc y hy; exact hy
      | cons j l ihl =>
        intro acc y hy
        simp only [List.foldl_cons]
        apply ihl
        by_cases h : acc.contains (repR.getD j 0) = true
        · rw [if_pos h]; exact hy
        · rw [if_neg h]; exact List.mem_cons_of_mem _ hy
    by_cases h : (acc.contains (repR.getD i 0)) = true
    · rw [if_pos h]
      obtain ⟨a1, a2⟩ := ih acc hl' hacc
      refine ⟨a1, fun j hj => ?_⟩
      rcases List.mem_cons.1 hj with rfl | hj
      · exact mono l acc _ (List.contains_iff_mem.1 h)
      · exact a2 j hj
    · rw [if_neg h]
      have hacc' : ∀ y ∈ repR.getD i 0 :: acc, ∃ i < N, y = repR.getD i 0 := by
        intro y hy
        rcases List.mem_cons.1 hy with rfl | hy
        · exact ⟨i, hiN, rfl⟩
        · exact hacc y hy
      obtain ⟨a1, a2⟩ := ih _ hl' hacc'
      refine ⟨a1, fun j hj => ?_⟩
      rcases List.mem_cons.1 hj with rfl | hj
      · exact mono l _ _ List.mem_cons_self
      · exact a2 j hj

theorem repList_spec (N : Nat) (repR : Array Nat) :
    (∀ y ∈ repList N repR, ∃ i < N, y = repR.getD i 0) ∧
      ∀ i < N, repR.getD i 0 ∈ repList N repR := by
  have := foldl_repList (N := N) repR (fun _ _ => trivial) (List.range N) []
    (by simp) (by simp)
  unfold repList
  exact ⟨this.1, fun i hi => this.2 i (List.mem_range.2 hi)⟩

theorem blocksOf_size' (ROm : List (Array Nat)) (N : Nat) (Aa Ab par gen : Array Nat)
    (xs : Array (List Nat)) : (blocksOf ROm N Aa Ab par gen xs).size = xs.size := by
  simp [blocksOf]

theorem blocksOf_getD' (ROm : List (Array Nat)) (N : Nat) (Aa Ab par gen : Array Nat)
    (xs : Array (List Nat)) {h : Nat} (hh : h < xs.size) :
    (blocksOf ROm N Aa Ab par gen xs).getD h #[] =
      bfsVis N (gensOm ROm N Aa Ab par gen (xs.getD h [])) 0 := by
  unfold blocksOf
  rw [Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?, Array.getElem?_map,
    Array.getElem?_eq_getElem hh]
  rfl

theorem beq_full_iff {N m : Nat} (hm : ∀ i, N ≤ i → m.testBit i = false) :
    Nat.beq m (Nat.sub (Nat.shiftLeft 1 N) 1) = true ↔ ∀ i < N, m.testBit i = true := by
  rw [beq_iff]
  change m = Nat.shiftLeft 1 N - 1 ↔ _
  rw [shiftLeft_one]
  constructor
  · intro h i hi
    rw [h, Nat.testBit_two_pow_sub_one]; simpa using hi
  · intro h
    apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.testBit_two_pow_sub_one]
    by_cases hi : i < N
    · simp [hi, h i hi]
    · simp [hi, hm i (by omega)]

theorem beq_sub_iff {N m m' : Nat} (hm : ∀ i, N ≤ i → m.testBit i = false) :
    Nat.beq (Nat.land m m') m = true ↔ ∀ i < N, m.testBit i = true → m'.testBit i = true := by
  rw [beq_iff]
  change m &&& m' = m ↔ _
  constructor
  · intro h i _ hi
    have := congrArg (fun z => z.testBit i) h
    simp only [Nat.testBit_and, hi, Bool.true_and] at this
    exact this
  · intro h
    apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.testBit_and]
    by_cases hi : i < N
    · cases hmi : m.testBit i
      · simp
      · simp [h i hi hmi]
    · simp [hm i (by omega)]

theorem blkSize_popK {N m : Nat} {b : Array Bool}
    (hb : ∀ i < N, b.getD i false = true ↔ m.testBit i = true) : blkSize N b = popK N m := by
  rw [blkSize_eq', popK_eq]
  congr 1
  apply List.filter_congr
  intro i hi
  have := hb i (List.mem_range.1 hi)
  cases h1 : b.getD i false <;> cases h2 : m.testBit i <;> simp_all

theorem shapeOK_of_shapeK {N : Nat} {BM : List Nat} {h₁ h₂ : Nat} (blocks : Array (Array Bool))
    (hsz : blocks.size = BM.length)
    (hb : ∀ h < blocks.size, ∀ i < N,
      (blocks.getD h #[]).getD i false = true ↔ (getK BM h).testBit i = true)
    (hhi : ∀ h < blocks.size, ∀ i, N ≤ i → (getK BM h).testBit i = false)
    (hs : shapeK N BM h₁ h₂ = true) : shapeOK N blocks := by
  unfold shapeK at hs
  simp only [allBs_cons, allBs_nil, Bool.and_true, Bool.and_eq_true] at hs
  obtain ⟨s1, s2, s3, s4, s5, s6, s7, s8⟩ := hs
  rw [blt_iff, lenA_eq] at s1 s2
  have bm : ∀ b ∈ BM, ∃ h < blocks.size, getK BM h = b := by
    intro b hb'
    obtain ⟨h, hh, e⟩ := List.mem_iff_getElem.1 hb'
    refine ⟨h, by omega, ?_⟩
    rw [getK_eq, List.getD_eq_getElem _ _ hh, e]
  have memBM : ∀ h < blocks.size, getK BM h ∈ BM := by
    intro h hh
    rw [getK_eq, List.getD_eq_getElem _ _ (by omega)]
    exact List.getElem_mem _
  have full_iff : ∀ h < blocks.size, blkFull N (blocks.getD h #[]) ↔
      Nat.beq (getK BM h) (Nat.sub (Nat.shiftLeft 1 N) 1) = true := by
    intro h hh
    rw [beq_full_iff (hhi h hh)]
    unfold blkFull
    exact ⟨fun H i hi => (hb h hh i hi).1 (H i hi), fun H i hi => (hb h hh i hi).2 (H i hi)⟩
  have sub_iff : ∀ h < blocks.size, ∀ h' < blocks.size, blkSub N (blocks.getD h #[])
      (blocks.getD h' #[]) ↔ Nat.beq (Nat.land (getK BM h) (getK BM h')) (getK BM h) = true := by
    intro h hh h' hh'
    rw [beq_sub_iff (hhi h hh)]
    unfold blkSub
    exact ⟨fun H i hi hm => (hb h' hh' i hi).1 (H i hi ((hb h hh i hi).2 hm)),
      fun H i hi hm => (hb h' hh' i hi).2 (H i hi ((hb h hh i hi).1 hm))⟩
  refine ⟨h₁, by omega, h₂, by omega, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [full_iff h₁ (by omega)]
    simpa [notB_iff] using s3
  · rw [full_iff h₂ (by omega)]
    simpa [notB_iff] using s4
  · rw [blkSize_popK (hb h₁ (by omega)), blkSize_popK (hb h₂ (by omega))]
    intro e
    rw [notB_iff] at s5
    exact s5 (beq_iff.2 e)
  · intro h hh hsub
    rw [allL_iff] at s6
    have := s6 (getK BM h) (memBM h hh)
    rw [impB_iff, orB_iff] at this
    rcases this ((sub_iff h₁ (by omega) h hh).1 hsub) with H | H
    · exact Or.inl ((sub_iff h hh h₁ (by omega)).2 H)
    · exact Or.inr ((full_iff h hh).2 H)
  · intro h hh hsub
    rw [allL_iff] at s7
    have := s7 (getK BM h) (memBM h hh)
    rw [impB_iff, orB_iff] at this
    rcases this ((sub_iff h₂ (by omega) h hh).1 hsub) with H | H
    · exact Or.inl ((sub_iff h hh h₂ (by omega)).2 H)
    · exact Or.inr ((full_iff h hh).2 H)
  · intro h hh hnf
    rw [allL_iff] at s8
    have := s8 (getK BM h) (memBM h hh)
    rw [impB_iff, orB_iff, notB_iff] at this
    rcases this (fun H => hnf ((full_iff h hh).2 H)) with H | H
    · exact Or.inl ((sub_iff h hh h₁ (by omega)).2 H)
    · exact Or.inr ((sub_iff h hh h₂ (by omega)).2 H)

end CFSG.KC.LQT.PPC
