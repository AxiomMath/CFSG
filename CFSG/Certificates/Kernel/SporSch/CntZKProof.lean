module

public import CFSG.Certificates.Kernel.SporSch.ClsCardProof

public section

namespace CFSG.KS.SporSch.MBT

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Raw.Orb CFSG.KS.Prim CFSG.KS.SporSch.MOC
open CFSG.Certificates CFSG.Sporadic.Schreier CFSG.Monster.B.Co2.Native CFSG.Monster.B.Mathieu
open Finset

variable {n w : Nat} {PS PSI LR TR TRI : Nat → Nat} {kS nb BP NS CH : Nat}
  {S : Array (Array Nat)} {base : Array Nat} {D : List (List Int)} {gA gB : Equiv.Perm (Fin n)}

open scoped Classical

theorem wordElts_prod {M : Type*} [Group M] (x y : M) (mx my : Nat) (wd : List Nat) :
    (wordElts x y mx my wd).prod = xyWordP x y (x ^ (mx - 1)) (y ^ (my - 1)) wd := by
  induction wd with
  | nil => rfl
  | cons l wd ih =>
    have e1 : wordElts x y mx my (l :: wd) = (if l = 0 then [x] else if l = 1 then [y]
        else if l = 2 then List.replicate (mx - 1) x else List.replicate (my - 1) y) ++
        wordElts x y mx my wd := by
      simp [wordElts]
    have e2 : xyWordP x y (x ^ (mx - 1)) (y ^ (my - 1)) (l :: wd) = (if l = 0 then x
        else if l = 1 then y else if l = 2 then x ^ (mx - 1) else y ^ (my - 1)) *
        xyWordP x y (x ^ (mx - 1)) (y ^ (my - 1)) wd := by
      simp [xyWordP]
    rw [e1, e2, List.prod_append, ih]
    congr 1
    split_ifs <;> simp [List.prod_replicate]

theorem xyWordP_coe {H : Subgroup (Equiv.Perm (Fin n))} (x y xi yi : H) (wd : List Nat) :
    ((xyWordP x y xi yi wd : H) : Equiv.Perm (Fin n)) =
      xyWordP (x : Equiv.Perm (Fin n)) y xi yi wd := by
  induction wd with
  | nil => rfl
  | cons l wd ih =>
    simp only [xyWordP, List.map_cons, List.prod_cons, Subgroup.coe_mul] at ih ⊢
    rw [ih]
    split_ifs <;> rfl

theorem cntZK_proved (hQ : ChainS n w PS PSI LR TR TRI kS 2 nb BP S base D NS CH)
    (hA : imageList gA = (unpack n w (PS 0)).toList)
    (hB : imageList gB = (unpack n w (PS 1)).toList) (hnd : base.toList.Nodup)
    {mx my cap : Nat} {d : ClsD}
    (hcls : ClsOK n w (unpack n w (PS 0)).toList (unpack n w (PS 1)).toList mx cap [d])
    (r : gen2 gA gB) (hR : imageList (r : Equiv.Perm (Fin n)) = (unpack n w d.R).toList)
    (z : gen2 gA gB) {Z : Nat} (hZ : imageList (z : Equiv.Perm (Fin n)) = (unpack n w Z).toList)
    (hmx : 0 < mx) (hmy : 0 < my)
    {ws : List (List Nat × Nat)} {row : List Nat} (hL : d.c ≤ row.length * 256)
    (hrow : ∀ b < row.length,
      cntZK n w (mask w) (pidn n w) mx my ws Z d (b * 256) 256 = row.getD b 0) :
    row.sum = #(univ.filter fun x : gen2 gA gB => IsConj r x ∧
      orderOf (x ^ (mx - 1) * z) = my ∧ ∀ p ∈ ws, p.2 = 0 ∨
        orderOf (xyWordP x (x ^ (mx - 1) * z) (x ^ (mx - 1)) ((x ^ (mx - 1) * z) ^ (my - 1))
          p.1) = p.2) := by
  obtain ⟨bv, -, hK, -, -, -⟩ := chainK_of_chainS hQ hA hB hnd
  have pr := prep_of_imageList hR
  have pZ := prep_of_imageList hZ
  have hc := datum_class hK hA.symm hB.symm hcls (j := 0) (by simp) pr
  obtain ⟨pA, pAi, pB, pBi, h32, hw⟩ := gens_prep hK hA.symm hB.symm
  obtain ⟨hd, he, -⟩ := hcls 0 (by simp)
  have hE := entry_mem_class h32 pA pAi pB pBi hd he pr
  have hro : orderOf r = mx := by
    rw [← Subgroup.orderOf_coe]
    exact hc.2.2.2
  have hT : ∀ x : gen2 gA gB, IsConj r x → ∀ {X : Nat}, PRep n w X x →
      (zTest n w (mask w) (pidn n w) mx my ws Z X = true ↔
        orderOf (x ^ (mx - 1) * z) = my ∧ ∀ p ∈ ws, p.2 = 0 ∨
          orderOf (xyWordP x (x ^ (mx - 1) * z) (x ^ (mx - 1)) ((x ^ (mx - 1) * z) ^ (my - 1))
            p.1) = p.2) := by
    intro x hx X pX
    have hxo' : orderOf x = mx := by
      obtain ⟨c, rfl⟩ := isConj_iff.1 hx
      rw [← hro]
      exact (MulAut.conj c).orderOf_eq r
    have hxo : orderOf (x : Equiv.Perm (Fin n)) = mx := by
      rw [Subgroup.orderOf_coe]
      exact hxo'
    have hinv : x ^ (mx - 1) = x⁻¹ := by
      apply eq_inv_of_mul_eq_one_left
      rw [← pow_succ, Nat.sub_add_cancel hmx, ← hxo', pow_orderOf_eq_one]
    have hy : x ^ (mx - 1) * z = x⁻¹ * z := by rw [hinv]
    rw [zTest_iff hK hmx hmy ws pX hxo pZ, hy]
    have e1 : (x : Equiv.Perm (Fin n))⁻¹ * z = ((x⁻¹ * z : gen2 gA gB) : Equiv.Perm (Fin n)) := by
      simp
    rw [e1, Subgroup.orderOf_coe]
    refine and_congr_right fun _ => ?_
    unfold wsVal
    rw [List.all_eq_true]
    refine forall_congr' fun p => forall_congr' fun _ => ?_
    simp only [wordElts_prod, ← Subgroup.coe_pow, ← xyWordP_coe, Subgroup.orderOf_coe,
      Bool.or_eq_true, decide_eq_true_eq]
  have hmemK : ∀ y ∈ CFSG.Sporadic.SmallOddCore.conjClass (gen2 gA gB) (r : Equiv.Perm (Fin n)),
      y ∈ gen2 gA gB := by
    rintro _ ⟨c, hc', rfl⟩
    exact (gen2 gA gB).mul_mem ((gen2 gA gB).mul_mem hc' r.2) ((gen2 gA gB).inv_mem hc')
  rw [sum_blocks (fun k => zTest n w (mask w) (pidn n w) mx my ws Z (d.ST k)) d.c row hL
    (fun b hb => by rw [← hrow b hb, cntZK_eq]), ← Finset.card_filter]
  refine Finset.card_bij (fun k hk => (⟨Classical.choose (hE k (Finset.mem_range.1
      (Finset.mem_filter.1 hk).1)), hmemK _ (Classical.choose_spec (hE k (Finset.mem_range.1
      (Finset.mem_filter.1 hk).1))).1⟩ : gen2 gA gB)) (fun k hk => ?_)
    (fun a ha b hb e => ?_) (fun x hx => ?_)
  · have hs := Classical.choose_spec (hE k (Finset.mem_range.1 (Finset.mem_filter.1 hk).1))
    have hcj : IsConj r ⟨_, hmemK _ hs.1⟩ := (isConj_iff_mem _ _).2 hs.1
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hcj, (hT _ hcj hs.2).1 (Finset.mem_filter.1 hk).2⟩
  · have p1 := (Classical.choose_spec (hE a (Finset.mem_range.1 (Finset.mem_filter.1 ha).1))).2
    have p2 := (Classical.choose_spec (hE b (Finset.mem_range.1 (Finset.mem_filter.1 hb).1))).2
    have e' := congrArg Subtype.val e
    simp only at e'
    rw [e'] at p1
    exact entry_inj hw he (Finset.mem_range.1 (Finset.mem_filter.1 ha).1)
      (Finset.mem_range.1 (Finset.mem_filter.1 hb).1) p1 p2
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
    obtain ⟨hxc, hcond⟩ := hx
    obtain ⟨k', hk', pk⟩ := (hc.1 x).1 ((isConj_iff_mem r x).1 hxc)
    have hk'' : k' ∈ (Finset.range d.c).filter fun k =>
        zTest n w (mask w) (pidn n w) mx my ws Z (d.ST k) = true :=
      Finset.mem_filter.2 ⟨Finset.mem_range.2 hk', (hT x hxc pk).2 hcond⟩
    exact ⟨k', hk'', Subtype.ext (MOC.prep_unique (Classical.choose_spec (hE k' hk')).2 pk)⟩

theorem cntZK_sound (_hsz : szOK n w = true) {tA tB : List Nat} (hA : imageList gA = tA)
    (hB : imageList gB = tB) (hQ : ChainS n w PS PSI LR TR TRI kS 2 nb BP S base D NS CH)
    (htA : tA = (unpack n w (PS 0)).toList) (htB : tB = (unpack n w (PS 1)).toList)
    (hnd : base.toList.Nodup) {mx my cap : Nat} {d : ClsD} (hcls : ClsOK n w tA tB mx cap [d])
    (r : gen2 gA gB) (hR : imageList (r : Equiv.Perm (Fin n)) = (unpack n w d.R).toList)
    (z : gen2 gA gB) {Z : Nat} (hZ : imageList (z : Equiv.Perm (Fin n)) = (unpack n w Z).toList)
    (_hZc : canonK n w (mask w) (n * w) Z = true) (hmx : 0 < mx) (hmy : 0 < my)
    {ws : List (List Nat × Nat)} {row : List Nat} (hL : d.c ≤ row.length * 256)
    (hrow : ∀ b < row.length,
      cntZK n w (mask w) (pidn n w) mx my ws Z d (b * 256) 256 = row.getD b 0) :
    row.sum = #(univ.filter fun x : gen2 gA gB => IsConj r x ∧
      orderOf (x ^ (mx - 1) * z) = my ∧ ∀ p ∈ ws, p.2 = 0 ∨
        orderOf (xyWordP x (x ^ (mx - 1) * z) (x ^ (mx - 1)) ((x ^ (mx - 1) * z) ^ (my - 1))
          p.1) = p.2) := by
  subst htA htB
  exact cntZK_proved hQ hA hB hnd hcls r hR z hZ hmx hmy hL hrow

end CFSG.KS.SporSch.MBT

end
