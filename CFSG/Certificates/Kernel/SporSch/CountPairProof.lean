module

public import CFSG.Certificates.Kernel.SporSch.ChainSProof
public import CFSG.Sporadic.Schreier.PairChain
public import CFSG.Sporadic.Schreier.PairCounts

public section

namespace CFSG.KS.SporSch.MBT

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.SporSch.MOC
open CFSG.Certificates CFSG.Certificates.Native CFSG.Sporadic.Schreier
open CFSG.Sporadic.Schreier.PairNative
open CFSG.Monster.B.Co2.Native CFSG.Monster.B.Mathieu Finset

variable {n w : Nat} {PS PSI LR TR TRI : Nat → Nat} {kS nb BP NS CH : Nat}
  {S : Array (Array Nat)} {base : Array Nat} {D : List (List Int)} {gA gB : Equiv.Perm (Fin n)}

open scoped Classical

theorem patP_coe {H : Subgroup (Equiv.Perm (Fin n))} (x y : H) (pat : List Bool) :
    ((patP x y pat : H) : Equiv.Perm (Fin n)) = patP (x : Equiv.Perm (Fin n)) y pat := by
  induction pat with
  | nil => rfl
  | cons b pat ih =>
    simp only [patP, List.map_cons, List.prod_cons, Subgroup.coe_mul] at ih ⊢
    rw [ih]
    cases b <;> rfl

theorem countPair_proved (hQ : ChainS n w PS PSI LR TR TRI kS 2 nb BP S base D NS CH)
    (hA : imageList gA = (unpack n w (PS 0)).toList)
    (hB : imageList gB = (unpack n w (PS 1)).toList) (hnd : base.toList.Nodup) {bs : List Nat}
    (hbs : bs = base.toList) {groups : List (List Nat)} (hg : groups.flatten = List.range nb)
    (x : gen2 gA gB) {X : Nat}
    (hX : imageList (x : Equiv.Perm (Fin n)) = (unpack n w X).toList) {my : Nat} (hmy : 0 < my)
    {conds : List (List Bool × Nat)} (hpos : ∀ c ∈ conds, 0 < c.2) :
    countPair bs my [unpack n w X] conds (blocksOf n (rawLevels n S base) groups) =
      #(univ.filter fun y : gen2 gA gB =>
        orderOf y = my ∧ ∀ c ∈ conds, orderOf (patP x y c.1) = c.2) := by
  obtain ⟨bv, hbv, hK, hS, hb, hbm⟩ := chainK_of_chainS hQ hA hB hnd
  have hn : 1 ≤ n := hQ.1.1
  obtain ⟨hAr, hraw⟩ := chainK_arrays hn hbv hK
  have hV := (chainK_check hn hbv hK).1
  set Q := certificate hn [gA, gB] D bv hbv
  have hGK : Q.originalSubgroup = gen2 gA gB := orig_pair hn hbv
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
  have hxR : RepW n [unpack n w X] (x : Equiv.Perm (Fin n)) := RepW.single (rep_of_imageList hX)
  have hxG : (x : Equiv.Perm (Fin n)) ∈ Q.originalSubgroup := by
    rw [hGK]
    exact x.2
  subst hS hb
  rw [countPair_eq, ← card_eq_countW hAr Nat.one_pos hraw (groups := groups) hg
    (Pr := fun y => orderOf y = my ∧
      ∀ c ∈ conds, orderOf (patP (x : Equiv.Perm (Fin n)) y c.1) = c.2)
    (fun v g hv hgm => ?_)]
  · rw [hGK, Nat.card_eq_fintype_card, Fintype.card_subtype]
    congr 1
    ext y
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, ← Subgroup.orderOf_coe, patP_coe]
  · rw [pairPred, Bool.and_eq_true, ordB_iff hF hlt hv hgm hmy,
      condsOK_iff hF hlt hxR hv hxG hgm hpos]
    rfl

theorem countOrd_proved (hQ : ChainS n w PS PSI LR TR TRI kS 2 nb BP S base D NS CH)
    (hA : imageList gA = (unpack n w (PS 0)).toList)
    (hB : imageList gB = (unpack n w (PS 1)).toList) (hnd : base.toList.Nodup) {bs : List Nat}
    (hbs : bs = base.toList) {groups : List (List Nat)} (hg : groups.flatten = List.range nb)
    {m : Nat} (hm : 0 < m) :
    countOrd bs m (blocksOf n (rawLevels n S base) groups) =
      #(univ.filter fun y : gen2 gA gB => orderOf y = m) := by
  let a : gen2 gA gB := ⟨gA, Subgroup.subset_closure (by simp)⟩
  have h := countPair_proved hQ hA hB hnd hbs hg a (X := PS 0) hA hm (conds := [])
    (fun c hc => absurd hc List.not_mem_nil)
  have e : pairPred bs m [unpack n w (PS 0)] [] = ordPred bs m := by
    funext y
    simp [pairPred, ordPred, condsOK]
  unfold countPair at h
  rw [e] at h
  unfold countOrd
  rw [h]
  refine congrArg Finset.card (Finset.filter_congr fun y _ => ?_)
  simp

theorem countPair_sound (hQ : ChainS n w PS PSI LR TR TRI kS 2 nb BP S base D NS CH)
    (hA : imageList gA = (unpack n w (PS 0)).toList)
    (hB : imageList gB = (unpack n w (PS 1)).toList) (hnd : base.toList.Nodup) {bs : List Nat}
    (hbs : bs = base.toList) {groups : List (List Nat)} (hg : groups.flatten = List.range nb)
    (x : gen2 gA gB) {X : Nat}
    (hX : imageList (x : Equiv.Perm (Fin n)) = (unpack n w X).toList) {my : Nat} (hmy : 0 < my)
    {conds : List (List Bool × Nat)} (hpos : ∀ c ∈ conds, 0 < c.2) :
    countPair bs my [unpack n w X] conds (blocksOf n (rawLevels n S base) groups) =
      #(univ.filter fun y : gen2 gA gB =>
        orderOf y = my ∧ ∀ c ∈ conds, orderOf (patP x y c.1) = c.2) :=
  countPair_proved hQ hA hB hnd hbs hg x hX hmy hpos

end CFSG.KS.SporSch.MBT

end
