module

public import CFSG.Certificates.Kernel.Fi22LH.Rows
public import CFSG.Certificates.Kernel.Fi22LH.OrbSets
import CFSG.Certificates.Kernel.Fi22LH.TreeSpec
import CFSG.Certificates.Kernel.Fi22LH.CommTree
import CFSG.Certificates.Kernel.Fi22LH.Maps
import CFSG.Certificates.Kernel.Fi22LH.Prim
import CFSG.Certificates.Kernel.Fi22LH.Acc
import Mathlib.Data.Fintype.EquivFin

public section

namespace CFSG.KS.Fi22LH

open CFSG.Sporadic.Fi22.Native CFSG.Sporadic.Th.Native CFSG.Perm.Native CFSG.KS.TW CFSG.KC.Enum

variable {D : LHData}

theorem getElem!_map' {α β : Type} [Inhabited α] [Inhabited β] (a : Array α) (f : α → β) {i : Nat}
    (hi : i < a.size) : (a.map f)[i]! = f a[i]! := by
  rw [getElem!_pos _ i (by simpa using hi), Array.getElem_map, getElem!_pos a i hi]

theorem tabDec_of_lt {n none : Nat} {f : Nat → Nat} (h : ∀ x < n, f x < none) :
    tabDec n none f = Array.ofFn (n := n) fun x => UInt32.ofNat (f x.val) := by
  unfold tabDec
  congr 1
  funext x
  rw [if_neg (Nat.ne_of_lt (h x x.2))]

theorem rootW_spec {R X : Nat → Nat} {lb rq : Nat} (hr : rootW R X lb rq = true) :
    closedK R lb (bs lb) = true ∧ fd (X 0) 0 4095 = 0 ∧
      bsF 351 (fun k => fd (X k) 0 4095) 9 0 = bs lb ∧
      posK (fun k => fd (X k) 0 4095) (fun x => ent rq x) 4095 3510 351 = true ∧
      bfsT (fun h l => ent (R (ent lb l)) (fd (X h) 0 4095)) 351 (fun x => ent rq x)
        (fun k => fd (X k) 12 511) (fun k => fd (X k) 21 511) 351 = true := by
  unfold rootW rootK at hr
  rw [strictB_eq] at hr
  simp only [bAnd_eq, Bool.and_eq_true, Nat.beq_eq] at hr
  obtain ⟨h1, h2, h3, h4, h5⟩ := hr
  exact ⟨h1, h2, h3, h4, h5⟩

theorem root_himg (hO : OrbOK) (h : LHChecks D) {S : Array Nat} {X : Nat → Nat} {lbn : Nat}
    (hS : S.size = 351) (hSj : ∀ j < 351, ent lbn j = S[j]!) (hinc : incK lbn = true) :
    ∀ k < 351, fd (X k) 0 4095 < 3510 → ∀ l < 351,
      ap (S.map fun s => (tauAll orbL)[s]!)[l]! (fd (X k) 0 4095) =
          ent (D.R (ent lbn l)) (fd (X k) 0 4095) ∧
        ent (D.R (ent lbn l)) (fd (X k) 0 4095) < 3510 := by
  intro k _ hx l hl
  have hl' : ent lbn l < 3510 := (incK_spec hinc).2 l hl
  rw [getElem!_map' _ _ (by omega), ← hSj l hl]
  exact (tauAll_TR hO h _ hl').2 _ hx

theorem rootTree_gen (hO : OrbOK) (h : LHChecks D) {S : Array Nat} {X : Nat → Nat} {lb rq : Nat}
    (hS : S.size = 351) (hSj : ∀ j < 351, ent lb j = S[j]!) (hinc : incK lb = true)
    (hr : rootW D.R X lb rq = true) :
    treeBFS 3510 0 (S.map fun s => (tauAll orbL)[s]!) (Array.range 351) = rootDec X rq := by
  obtain ⟨-, h0, -, hpos, hbfs⟩ := rootW_spec hr
  obtain ⟨-, he⟩ := treeBFS_eq_of (n := 3510) (root := 0) (nl := 351) (N := 351) (none := 4095)
    (by decide) (by decide) (by decide) (by decide) h0 (root_himg (X := X) hO h hS hSj hinc) hpos hbfs
  rw [he]
  unfold rootDec
  rw [tabDec_of_lt (f := fun k => fd (X k) 0 4095) fun x _ => Nat.lt_of_le_of_lt (fd_le _ _ _) (by decide),
    tabDec_of_lt (f := fun k => fd (X k) 12 511) fun x _ => Nat.lt_of_le_of_lt (fd_le _ _ _) (by decide),
    tabDec_of_lt (f := fun k => fd (X k) 21 511) fun x _ => Nat.lt_of_le_of_lt (fd_le _ _ _) (by decide)]
  rfl

theorem rootTree_eq0 (hO : OrbOK) (h : LHChecks D) :
    treeBFS 3510 0 ((lhData ())[0]!.map fun s => (tauAll orbL)[s]!) (Array.range 351) =
      rootDec D.X D.rq0 :=
  rootTree_gen hO h lhData0_size h.lb0 (walk_rest h.walkA).2.1 h.rootX

theorem rootTree_eq1 (hO : OrbOK) (h : LHChecks D) :
    treeBFS 3510 0 ((lhData ())[1]!.map fun s => (tauAll orbL)[s]!) (Array.range 351) =
      rootDec D.Y D.rq1 :=
  rootTree_gen hO h lhData1_size h.lb1 (walk_rest h.walkB).2.1 h.rootY

theorem rootTreeOK_gen (hO : OrbOK) (h : LHChecks D) {S : Array Nat} {X : Nat → Nat} {lb rq : Nat}
    (hS : S.size = 351) (hSj : ∀ j < 351, ent lb j = S[j]!) (hinc : incK lb = true)
    (hr : rootW D.R X lb rq = true) :
    rootTreeOK (tauAll orbL) S (S.map fun s => (tauAll orbL)[s]!) (rootDec X rq) = true := by
  obtain ⟨-, h0, hb, hpos, hbfs⟩ := rootW_spec hr
  have himg := root_himg (X := X) hO h hS hSj hinc
  have hdec := rootTree_gen hO h hS hSj hinc hr
  obtain ⟨⟨-, -, hpts⟩, he⟩ := treeBFS_eq_of (n := 3510) (root := 0) (nl := 351) (N := 351)
    (none := 4095) (by decide) (by decide) (by decide) (by decide) h0 himg hpos hbfs
  rw [hdec] at he
  have hP1 : ∀ k < 351, ent rq (fd (X k) 0 4095) = k := by
    unfold posK at hpos
    rw [bAnd_eq, Bool.and_eq_true] at hpos
    exact fun k hk => Nat.eq_of_beq_eq_true (allN_iff.1 hpos.1 k hk)
  unfold rootTreeOK
  rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true, Array.all_eq_true]
  refine ⟨⟨⟨by rw [Array.size_map, hS]; rfl, ?_⟩, ?_⟩, ?_⟩
  · rw [allIn_iff]
    intro l hl
    rw [beq_iff_eq, getElem!_map' _ _ (by omega)]
  · exact treeOK_of (by decide) (by decide) (by decide) (by decide) (by decide) h0 himg hpos
      hbfs he
  · intro j hj
    have hx : S[j] = ent lb j := by rw [hSj j (by omega), getElem!_pos S j hj]
    obtain ⟨k, hk, hkx⟩ := (testBit_bsF_zero (n := 351) (d := 9) (by decide)
      (fun k => fd (X k) 0 4095) (ent lb j)).1 (by
        rw [hb, testBit_bs]; exact ⟨j, by omega, rfl⟩)
    rw [hx, he, ← hkx]
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, Array.size_ofFn]
    have hpk := hpts k hk
    rw [ap_ofFn (g := fun x => if ent rq x = 4095 then none32 else UInt32.ofNat (ent rq x)) hpk]
    rw [hP1 k hk, if_neg (by omega), toNat_ofNat32 (by omega),
      ap_ofFn (g := fun k => UInt32.ofNat (fd (X k) 0 4095)) hk, toNat_ofNat32 (by omega)]
    exact ⟨hk, rfl⟩

theorem c_rootTree0 (hO : OrbOK) (h : LHChecks D) :
    rootTreeOK (tauAll orbL) (lhData ())[0]! ((lhData ())[0]!.map fun s => (tauAll orbL)[s]!)
      (rootDec D.X D.rq0) = true :=
  rootTreeOK_gen hO h lhData0_size h.lb0 (walk_rest h.walkA).2.1 h.rootX

theorem c_rootTree1 (hO : OrbOK) (h : LHChecks D) :
    rootTreeOK (tauAll orbL) (lhData ())[1]! ((lhData ())[1]!.map fun s => (tauAll orbL)[s]!)
      (rootDec D.Y D.rq1) = true :=
  rootTreeOK_gen hO h lhData1_size h.lb1 (walk_rest h.walkB).2.1 h.rootY

theorem swapK_spec {R C QA QB : Nat → Nat} {u lb0 lb1 u0 u1 : Nat}
    (hs : swapK R C QA QB u lb0 lb1 u0 u1 = true) :
    fd (C 0) 0 4095 = nbK 0 ∧
      posK (fun k => fd (C k) 0 4095) (fun x => fd (C x) 27 4095) 4095 3510 3510 = true ∧
      bfsT (fun h l => ent (R (nbK l)) (fd (C h) 0 4095)) 6 (fun x => fd (C x) 27 4095)
        (fun k => fd (C k) 12 4095) (fun k => fd (C k) 24 7) 3510 = true ∧
      ent u (fd (C 0) 0 4095) = uiK 0 ∧
      (∀ k < 3510, k ≠ 0 → ent u (fd (C k) 0 4095) =
        ent (R (uiK (fd (C k) 24 7))) (ent u (fd (C (fd (C k) 12 4095)) 0 4095))) ∧
      (∀ x < 3510, ent u x < 3510 ∧ ent u (ent u x) = x) ∧ u0 < 14080 ∧ u1 < 14080 ∧
      (∀ j < 351, (sb (QB u0)).testBit (ent u (ent lb0 j)) = true) ∧
      (∀ j < 351, (sb (QA u1)).testBit (ent u (ent lb1 j)) = true) := by
  unfold swapK at hs
  simp only [bAnd_eq, Bool.and_eq_true, Nat.beq_eq, Nat.blt_eq] at hs
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := hs
  refine ⟨h1, h2, h3, h4, fun k hk hk0 => ?_, fun x hx => ?_, h7, h8, fun j hj => ?_,
    fun j hj => ?_⟩
  · have := allN_iff.1 h5 k hk
    rw [bIf_eq, beq_false hk0, if_neg (by simp), strictB_eq] at this
    exact Nat.eq_of_beq_eq_true this
  · have := allN_iff.1 h6 x hx
    rw [Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at this
    exact this
  · rw [strictB_eq] at h9
    have := allN_iff.1 h9 j hj
    rwa [memB_eq] at this
  · rw [strictB_eq] at h10
    have := allN_iff.1 h10 j hj
    rwa [memB_eq] at this

theorem nfpBase_get : ∀ l < 6, nfpBase[l]! = nbK l := by decide

theorem nbK_lt {l : Nat} (hl : l < 6) : nbK l < 3510 := by
  rw [← nfpBase_get l hl]
  revert l
  decide

theorem clos_himg (hO : OrbOK) (h : LHChecks D) : ∀ k < 3510, fd (D.C k) 0 4095 < 3510 → ∀ l < 6,
    ap (nfpBase.map (tabOf orbL))[l]! (fd (D.C k) 0 4095) =
        ent (D.R (nbK l)) (fd (D.C k) 0 4095) ∧
      ent (D.R (nbK l)) (fd (D.C k) 0 4095) < 3510 := by
  intro k _ hx l hl
  have hb := nbK_lt hl
  rw [getElem!_map' _ _ (by change l < 6; exact hl), nfpBase_get l hl, ← tauAll_get hb]
  exact (tauAll_TR hO h _ hb).2 _ hx

theorem clos_facts (hO : OrbOK) (h : LHChecks D) :
    (∀ k < 3510, fd (D.C k) 0 4095 < 3510) ∧ (∀ x < 3510, ∃ k < 3510, fd (D.C k) 0 4095 = x) ∧
      ∀ k, 0 < k → k < 3510 → fd (D.C k) 12 4095 < k ∧ fd (D.C k) 24 7 < 6 ∧
        ent (D.R (nbK (fd (D.C k) 24 7))) (fd (D.C (fd (D.C k) 12 4095)) 0 4095) =
          fd (D.C k) 0 4095 := by
  obtain ⟨h0, hpos, hbfs, -⟩ := swapK_spec h.swap
  have hroot : fd (D.C 0) 0 4095 = nfpBase[0]! := by rw [h0, nfpBase_get 0 (by decide)]
  obtain ⟨⟨-, -, hpts⟩, -⟩ := treeBFS_eq_of (n := 3510) (nl := 6) (N := 3510) (none := 4095)
    (by decide) (by decide) (by decide) (by decide) hroot (clos_himg hO h) hpos hbfs
  have hP1 : ∀ k < 3510, fd (D.C (fd (D.C k) 0 4095)) 27 4095 = k := by
    unfold posK at hpos
    rw [bAnd_eq, Bool.and_eq_true] at hpos
    exact fun k hk => Nat.eq_of_beq_eq_true (allN_iff.1 hpos.1 k hk)
  obtain ⟨-, htr⟩ := bfsT_facts (n := 3510) (by decide) hpos hbfs fun k hk l hl =>
    (clos_himg hO h k hk (hpts k hk) l hl).2
  refine ⟨hpts, fun x hx => ?_, htr⟩
  let f : Fin 3510 → Fin 3510 := fun k => ⟨fd (D.C k) 0 4095, hpts k k.2⟩
  have hf : Function.Injective f := by
    intro a b e
    have e' : fd (D.C a) 0 4095 = fd (D.C b) 0 4095 := congrArg Fin.val e
    apply Fin.ext
    rw [← hP1 a a.2, ← hP1 b b.2, e']
  obtain ⟨k, hk⟩ := Finite.surjective_of_injective hf ⟨x, hx⟩
  exact ⟨k, k.2, congrArg Fin.val hk⟩

theorem closTree_eq (hO : OrbOK) (h : LHChecks D) :
    closTree (nfpBase.map (tabOf orbL)) 6 = closDec D.C := by
  obtain ⟨h0, hpos, hbfs, -⟩ := swapK_spec h.swap
  have hroot : fd (D.C 0) 0 4095 = nfpBase[0]! := by rw [h0, nfpBase_get 0 (by decide)]
  have himg := clos_himg hO h
  unfold closTree
  obtain ⟨-, he⟩ := treeBFS_eq_of (n := 3510) (nl := 6) (N := 3510) (none := 4095)
    (by decide) (by decide) (by decide) (by decide) hroot himg hpos hbfs
  rw [he]
  unfold closDec
  rw [tabDec_of_lt (f := fun k => fd (D.C k) 0 4095) fun x _ => Nat.lt_of_le_of_lt (fd_le _ _ _)
      (by decide),
    tabDec_of_lt (f := fun k => fd (D.C k) 12 4095) fun x _ => Nat.lt_of_le_of_lt (fd_le _ _ _)
      (by decide),
    tabDec_of_lt (f := fun k => fd (D.C k) 24 7) fun x _ => Nat.lt_of_le_of_lt (fd_le _ _ _)
      (by decide)]
  rfl

theorem commTree_eq0 (hO : OrbOK) (h : LHChecks D) :
    commTree (tauAll orbL) (lhData ())[0]! = (Array.ofFn (n := 351) fun k => fd (D.X k.val) 30 4095,
      Array.ofFn (n := 351) fun k => fd (D.X k.val) 42 511) :=
  commTree_eq_of (tauAll_TR hO h) lhData0_size (fun j hj => (h.lb0 j hj).symm)
    (walk_rest h.walkA).2.1 (walk_rest h.walkA).2.2 h.commX

theorem commTree_eq1 (hO : OrbOK) (h : LHChecks D) :
    commTree (tauAll orbL) (lhData ())[1]! = (Array.ofFn (n := 351) fun k => fd (D.Y k.val) 30 4095,
      Array.ofFn (n := 351) fun k => fd (D.Y k.val) 42 511) :=
  commTree_eq_of (tauAll_TR hO h) lhData1_size (fun j hj => (h.lb1 j hj).symm)
    (walk_rest h.walkB).2.1 (walk_rest h.walkB).2.2 h.commY

theorem ofFn_get' {n : Nat} (f : Nat → Nat) {k : Nat} (hk : k < n) :
    (Array.ofFn (n := n) fun i => f i.val)[k]! = f k := by
  rw [getElem!_pos _ k (by rw [Array.size_ofFn]; exact hk), Array.getElem_ofFn]

theorem commTreeOK_gen (hO : OrbOK) (h : LHChecks D) {S : Array Nat} {X : Nat → Nat} {lb cq : Nat}
    (hS : S.size = 351) (hSj : ∀ j < 351, ent lb j = S[j]!) (hinc : incK lb = true)
    (hc : commK D.R X lb cq = true) :
    commTreeOK (tauAll orbL) S (bitsOf S) (Array.ofFn (n := 351) fun k => fd (X k.val) 30 4095)
      (Array.ofFn (n := 351) fun k => fd (X k.val) 42 511) = true := by
  obtain ⟨ho0, -, hpos, -⟩ := commK_spec hc
  obtain ⟨hall, hord⟩ := comm_ord hinc hpos
  have hfacts := commK_facts hc
  have hmem : ∀ j < 351, ent lb j ∈ S := fun j hj => by
    rw [hSj j hj, getElem!_pos S j (by omega)]
    exact Array.getElem_mem _
  have hlt : ∀ a ∈ S, a < 3520 := by
    intro a ha
    obtain ⟨j, hj, rfl⟩ := Array.mem_iff_getElem.1 ha
    have := (incK_spec hinc).2 j (by omega)
    rw [hSj j (by omega), getElem!_pos S j hj] at this
    omega
  have hB := bitsIs_bitsOf hlt
  unfold commTreeOK
  rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true, Array.all_eq_true]
  refine ⟨⟨⟨⟨by rw [Array.size_ofFn]; rfl, by rw [Array.size_ofFn]; rfl⟩, ?_⟩, ?_⟩, ?_⟩
  · rw [ofFn_get' (n := 351) (fun k => fd (X k) 30 4095) (by decide), ho0]
    rfl
  · rw [allIn_lo]
    intro k hk1 hk2
    obtain ⟨t1, ⟨j, hj, t2⟩, t3⟩ := hfacts k (by omega) hk2
    have hp : fd (X k) 42 511 < 351 := by omega
    rw [ofFn_get' (n := 351) (fun k => fd (X k) 42 511) hk2,
      ofFn_get' (n := 351) (fun k => fd (X k) 30 4095) hk2,
      ofFn_get' (n := 351) (fun k => fd (X k) 30 4095) hp]
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, bne_iff_ne, ne_eq]
    have hxlt : fd (X (fd (X k) 42 511)) 30 4095 < 3510 := by
      obtain ⟨j', hj', e⟩ := hall _ hp
      rw [← e, (hpos j' hj').2]
      exact (incK_spec hinc).2 j' hj'
    have hylt : fd (X k) 30 4095 < 3510 := by rw [t2]; exact (incK_spec hinc).2 j hj
    refine ⟨⟨⟨t1, ?_⟩, ?_⟩, ?_⟩
    · rw [(hB.2 _ (by omega)), t2]
      exact hmem j hj
    · rw [((tauAll_TR hO h _ hxlt).2 _ hylt).1]
      exact t3
    · intro e
      have := hord _ hp k hk2 e
      omega
  · intro j' hj'
    obtain ⟨j, hj, e⟩ := Array.mem_iff_getElem.1 (Array.getElem_mem hj')
    rw [Array.contains_iff_mem, Array.mem_iff_getElem]
    have hx : S[j'] = ent lb j' := by rw [hSj j' (by omega), getElem!_pos S j' hj']
    refine ⟨posC cq j', by rw [Array.size_ofFn]; exact (hpos j' (by omega)).1, ?_⟩
    rw [Array.getElem_ofFn, hx]
    exact (hpos j' (by omega)).2

theorem c_commTree0 (hO : OrbOK) (h : LHChecks D) :
    commTreeOK (tauAll orbL) (lhData ())[0]! (bitsOf (lhData ())[0]!)
      (Array.ofFn (n := 351) fun k => fd (D.X k.val) 30 4095)
      (Array.ofFn (n := 351) fun k => fd (D.X k.val) 42 511) = true :=
  commTreeOK_gen hO h lhData0_size h.lb0 (walk_rest h.walkA).2.1 h.commX

theorem c_commTree1 (hO : OrbOK) (h : LHChecks D) :
    commTreeOK (tauAll orbL) (lhData ())[1]! (bitsOf (lhData ())[1]!)
      (Array.ofFn (n := 351) fun k => fd (D.Y k.val) 30 4095)
      (Array.ofFn (n := 351) fun k => fd (D.Y k.val) 42 511) = true :=
  commTreeOK_gen hO h lhData1_size h.lb1 (walk_rest h.walkB).2.1 h.commY

end CFSG.KS.Fi22LH
