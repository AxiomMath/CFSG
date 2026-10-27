module

public import CFSG.Certificates.Kernel.SporSch.MathieuBTSound
public import Certificates.Data.CFSGNative.PairSchreier.Counts
import CFSG.Certificates.Kernel.SporSch.ChainKZTot
import CFSG.Sporadic.Schreier.PairChain
import CFSG.Sporadic.Schreier.PairCounts
public import CFSG.Sporadic.Schreier.MathieuOddCoreWords

public section

namespace CFSG.KS.SporSch.MBT

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.MEnum CFSG.KS.M11 CFSG.KS.SporSch.MOC
open CFSG.Certificates.Native CFSG.Sporadic.Schreier.PairNative CFSG.Monster.B.Co2.Native
open CFSG.Certificates CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native CFSG.Monster.B.Mathieu

@[expose] def ChainS (n w : Nat) (PS PSI LR TR TRI : Nat → Nat) (kS kO nb BP : Nat)
    (S : Array (Array Nat)) (base : Array Nat) (D : List (List Int)) (NS CH : Nat) : Prop :=
  Binds n w PS kS nb BP S base ∧
    headK n w (mask w) (n * w) (pidn n w) PS PSI kS kO D nb BP = true ∧
    LevelsOK n w PS PSI LR TR TRI kS nb BP ∧ n ≤ NS * CH ∧
    ∀ i < nb, ∀ s < NS, schK n w (mask w) (n * w) (pidn n w) PS PSI LR TR TRI kS BP nb i
      (stepsAt n w PS kS BP i) (s * CH) CH = true

@[expose] def condWords (conds : List (List Bool × Nat)) : List (List Nat × Nat) :=
  conds.map fun c => (c.1.map fun b => if b then 1 else 0, c.2)

variable {n w : Nat} {PS PSI LR TR TRI : Nat → Nat} {kS kO nb BP NS CH : Nat}
  {S : Array (Array Nat)} {base : Array Nat} {D : List (List Int)}

private theorem bAnd_eq' (a b : Bool) : Bool.rec (motive := fun _ => Bool) false b a = (a && b) := by
  cases a <;> rfl

theorem perm_of_chainS (hQ : ChainS n w PS PSI LR TR TRI kS kO nb BP S base D NS CH) {j : Nat}
    (hj : j < kO) : ∃ g : Equiv.Perm (Fin n), imageList g = (unpack n w (PS j)).toList := by
  have hh := hQ.2.1
  unfold headK at hh
  simp only [bAnd_eq', Bool.and_eq_true] at hh
  obtain ⟨-, -, hko, -, hp, -⟩ := hh
  have hko' : kO ≤ kS := Nat.le_of_ble_eq_true hko
  exact ⟨_, imageList_of_prep (Orb.prep_of_rep (CFSG.Monster.B.Co2.rep_permOfArr
    (Orb.isInvA_unpack (CFSG.KS.allN_spec hp j (by omega)))).1)⟩

theorem chainK_of_chainS_gens (hQ : ChainS n w PS PSI LR TR TRI kS kO nb BP S base D NS CH)
    {gens : List (Equiv.Perm (Fin n))} (hlen : gens.length = kO)
    (hgen : ∀ j < gens.length, imageList (gens.getD j 1) = (unpack n w (PS j)).toList)
    (hnd : base.toList.Nodup) :
    ∃ bv : Vector (Fin n) nb, bv.toList.Nodup ∧
      ChainK n w gens D bv PS PSI LR TR TRI kS BP NS CH ∧ strongArr n w kS PS = S ∧
        CFSG.KS.SporSch.MOC.baseArr w nb BP = base ∧
        bv.toList.map Fin.val = base.toList := by
  subst hlen
  obtain ⟨hb, hh, hl, hNS, hs⟩ := hQ
  have hbl := Orb.base_lt_of_levels hb hl
  have hpt : ∀ t < nb, pg w (mask w) BP t < n := fun t ht => by
    rw [← hb.2.2.2.2.2.2 t ht]
    exact hbl t ht
  have hbase : (List.range nb).map (pg w (mask w) BP) = base.toList := by
    apply List.ext_getElem (by simp [hb.2.2.2.2.2.1])
    intro i h1 h2
    have hi : i < nb := by simpa using h1
    simp only [List.getElem_map, List.getElem_range, Array.getElem_toList]
    rw [← hb.2.2.2.2.2.2 i hi, getElem!_pos base i (by rw [hb.2.2.2.2.2.1]; exact hi)]
  let bv : Vector (Fin n) nb := Vector.ofFn fun i => ⟨pg w (mask w) BP i, hpt i i.2⟩
  have hbvm : bv.toList.map Fin.val = (List.range nb).map (pg w (mask w) BP) := by
    apply List.ext_getElem (by simp [bv])
    intro i h1 h2
    simp [bv]
  refine ⟨bv, ?_, ⟨hb.1, hb.2.1, hb.2.2.1, hgen, hbvm, hh, hl, hNS, hs⟩, ?_, ?_, ?_⟩
  · apply List.Nodup.of_map Fin.val
    rw [hbvm, hbase]
    exact hnd
  · apply Array.ext
    · rw [hb.2.2.2.1]
      simp [strongArr]
    · intro j h1 h2
      have hj : j < kS := by simpa [strongArr] using h1
      rw [← getElem!_pos S j h2, hb.2.2.2.2.1 j hj]
      simp [strongArr]
  · apply Array.ext
    · rw [hb.2.2.2.2.2.1]
      simp [CFSG.KS.SporSch.MOC.baseArr]
    · intro t h1 h2
      have ht : t < nb := by simpa [CFSG.KS.SporSch.MOC.baseArr] using h1
      rw [← getElem!_pos base t h2, hb.2.2.2.2.2.2 t ht]
      simp [CFSG.KS.SporSch.MOC.baseArr]
  · rw [hbvm, hbase]

private theorem wordElts_cond {M : Type*} [Group M] (x y : M) (mx my : Nat) (pat : List Bool) :
    wordElts x y mx my (pat.map fun b => if b then 1 else 0) =
      pat.map fun b => if b then y else x := by
  induction pat with
  | nil => rfl
  | cons b pat ih =>
    simp only [wordElts, List.map_cons, List.flatMap_cons] at ih ⊢
    rw [ih]
    cases b <;> rfl

private theorem wsVal_condWords {conds : List (List Bool × Nat)} (hpos : ∀ c ∈ conds, 0 < c.2)
    (mx my : Nat) (x y : Equiv.Perm (Fin n)) :
    wsVal mx my (condWords conds) x y = true ↔
      ∀ c ∈ conds, orderOf (c.1.map fun b => if b then y else x).prod = c.2 := by
  unfold wsVal condWords
  rw [List.all_map, List.all_eq_true]
  refine forall_congr' fun c => forall_congr' fun hc => ?_
  simp only [Function.comp_apply, wordElts_cond, Bool.or_eq_true, decide_eq_true_eq]
  have := hpos c hc
  constructor
  · rintro (h | h)
    · omega
    · exact h
  · exact Or.inr

theorem pcount_sound (hQ : ChainS n w PS PSI LR TR TRI kS kO nb BP S base D NS CH)
    (hnd : base.toList.Nodup) (hk64 : nb ≤ 64)
    {XL CL : List Nat} (hE : ClassEqK n w LR TR TRI BP nb XL CL) {bs : List Nat}
    (hbs : bs = base.toList) {groups : List (List Nat)} (hg : groups.flatten = List.range nb)
    {m : Nat} (hm : 1 < m) :
    countOrd bs m (blocksOf n (rawLevels n S base) groups) =
      sumOrdK n w (mask w) (ordK LR nb) XL CL m XL.length := by
  have hgen : ∀ j : Fin kO, ∃ g : Equiv.Perm (Fin n), imageList g = (unpack n w (PS j)).toList :=
    fun j => perm_of_chainS hQ j.2
  choose g hg' using hgen
  obtain ⟨bv, hbv, hK, hS, hb, hbm⟩ := chainK_of_chainS_gens hQ (gens := List.ofFn g)
    (by simp) (fun j hj => by
      have hj' : j < kO := by simpa using hj
      rw [List.getD_eq_getElem _ _ hj, List.getElem_ofFn]
      exact hg' ⟨j, hj'⟩) hnd
  have hn : 1 ≤ n := hQ.1.1
  obtain ⟨hAr, hraw⟩ := chainK_arrays hn hbv hK
  have hV := (chainK_check hn hbv hK).1
  have h32 := chainK_h32 hK
  set Q := certificate hn (List.ofFn g) D bv hbv
  have hF : BaseFaithful Q.originalSubgroup bs := by
    have h := baseFaithful_of_valid hV
    have e : Q.base.toList.map Fin.val = bs := by
      rw [hbs, ← hbm]
      rfl
    rwa [e] at h
  have hlt : ∀ b ∈ bs, b < n := by
    intro b hb'
    rw [hbs, ← hbm] at hb'
    obtain ⟨i, -, rfl⟩ := List.mem_map.1 hb'
    exact i.2
  have hm0 : 0 < m := by omega
  rw [← (classEq_sound hn hbv hK hE hm hk64).1]
  subst hS hb
  rw [countOrd_eq, ← card_eq_countW hAr Nat.one_pos hraw (groups := groups) hg
    (f := ordPred bs m) (Pr := fun y => orderOf y = m) (fun v g hv hgm => ordB_iff hF hlt hv hgm hm0),
    (forall₂_orderTables h32 Q hm0).length_eq, List.length_reverse,
    ← List.countP_eq_length_filter,
    card_subtype_eq_countP Q.originalSubgroup (enumeration Q) (enumeration_nodup Q hV)
      (mem_enumeration_iff Q hV) (fun y => orderOf y = m)]

theorem ppair_sound (hQ : ChainS n w PS PSI LR TR TRI kS kO nb BP S base D NS CH) (hkO : kO = 2)
    (hnd : base.toList.Nodup) (hk64 : nb ≤ 64)
    {XL CL : List Nat} (hE : ClassEqK n w LR TR TRI BP nb XL CL) {bs : List Nat}
    (hbs : bs = base.toList) {groups : List (List Nat)} (hg : groups.flatten = List.range nb)
    {mx my r cap : Nat} {d : ClsD}
    (hcls : ClsOK n w (unpack n w (PS 0)).toList (unpack n w (PS 1)).toList mx cap [d])
    (hRc : canonK n w (mask w) (n * w) d.R = true)
    (hRs : siftK n w (mask w) (n * w) (pidn n w) LR TRI BP nb 0 d.R = true)
    {x : List (Array Nat)} (hx : x = [unpack n w d.R]) (hmx : 0 < mx) (hmy : 0 < my) (hr : 1 < r)
    {conds : List (List Bool × Nat)} (hc : ([false, true], r) ∈ conds)
    (hpos : ∀ c ∈ conds, 0 < c.2) {SC : List (List (List Nat))}
    (hSC : ZScans n w mx my r (condWords conds) XL [d] SC) :
    d.c * countPair bs my x conds (blocksOf n (rawLevels n S base) groups) =
      zTotK n w (mask w) (ordK LR nb) XL CL SC r XL.length := by
  subst hkO
  obtain ⟨gA, hA⟩ := perm_of_chainS hQ (j := 0) (by decide)
  obtain ⟨gB, hB⟩ := perm_of_chainS hQ (j := 1) (by decide)
  obtain ⟨bv, hbv, hK, hS, hb, hbm⟩ := chainK_of_chainS_gens hQ (gens := [gA, gB]) rfl
    (fun j hj => by
      have hj2 : j < 2 := hj
      rcases (by omega : j = 0 ∨ j = 1) with rfl | rfl
      · exact hA
      · exact hB) hnd
  have hn : 1 ≤ n := hQ.1.1
  obtain ⟨hAr, hraw⟩ := chainK_arrays hn hbv hK
  have hV := (chainK_check hn hbv hK).1
  have hsz := chainK_szOK hK
  set Q := certificate hn [gA, gB] D bv hbv
  have hF : BaseFaithful Q.originalSubgroup bs := by
    have h := baseFaithful_of_valid hV
    have e : Q.base.toList.map Fin.val = bs := by
      rw [hbs, ← hbm]
      rfl
    rwa [e] at h
  have hlt : ∀ b ∈ bs, b < n := by
    intro b hb'
    rw [hbs, ← hbm] at hb'
    obtain ⟨i, -, rfl⟩ := List.mem_map.1 hb'
    exact i.2
  obtain ⟨ρ, pρ, hρG⟩ := rep_of_sift hK hn hbv (R := d.R) (by rw [bAnd_eq', hRc, hRs]; rfl)
  have hρ : imageList ρ = (unpack n w d.R).toList := imageList_of_prep pρ
  have hRl : [ρ].length = [d].length ∧ ∀ j < [d].length,
      imageList ([ρ].getD j 1) = (unpack n w ([d].getD j clsD0).R).toList := ⟨rfl, fun j hj => by
    obtain rfl : j = 0 := by simpa using hj
    exact hρ⟩
  have hws : ([0, 1], r) ∈ condWords conds := List.mem_map.2 ⟨([false, true], r), hc, rfl⟩
  have hz := zReps_sound hn hbv hK hE hk64 hA.symm hB.symm hcls (fun j hj => by
      obtain rfl : j = 0 := by simpa using hj
      change bAnd(canonK n w (mask w) (n * w) d.R,
        siftK n w (mask w) (n * w) (pidn n w) LR TRI BP nb 0 d.R) = true
      rw [bAnd_eq', hRc, hRs]
      rfl) hRl hmx hmy hr hws hSC
  have hsizes := (chainK_reps3 hA.symm hB.symm hsz hcls hRl hmx
    (X := List.replicate ([d].map ClsD.c).sum #[]) (by simp)).2.1
  simp only [repSizes, List.map_cons, List.map_nil, List.cons.injEq, and_true] at hsizes
  rw [← hz]
  unfold repsTotal
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero, hsizes]
  congr 1
  rw [countP_orderTables_words hK hn hbv hmy _ ρ]
  simp only [one_mul, List.map_id']
  have hxR : RepW n x ρ := by
    rw [hx]
    exact RepW.single (rep_of_imageList hρ)
  subst hS hb
  rw [countPair_eq, ← card_eq_countW hAr Nat.one_pos hraw (groups := groups) hg
    (f := pairPred bs my x conds) (Pr := fun y => orderOf y = my ∧
      ∀ c ∈ conds, orderOf (c.1.map fun b => if b then y else ρ).prod = c.2)
    (fun v g hv hgm => by
      rw [pairPred, Bool.and_eq_true, ordB_iff hF hlt hv hgm hmy,
        condsOK_iff hF hlt hxR hv hρG hgm hpos]),
    card_subtype_eq_countP Q.originalSubgroup (enumeration Q) (enumeration_nodup Q hV)
      (mem_enumeration_iff Q hV) (fun y => orderOf y = my ∧
        ∀ c ∈ conds, orderOf (c.1.map fun b => if b then y else ρ).prod = c.2)]
  congr 1
  funext y
  apply Bool.eq_iff_iff.2
  rw [Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq, wsVal_condWords hpos]

end CFSG.KS.SporSch.MBT

end
