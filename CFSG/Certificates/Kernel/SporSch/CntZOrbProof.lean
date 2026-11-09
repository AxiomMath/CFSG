module

public import CFSG.Certificates.Kernel.SporSch.CntZKProof
public import Certificates.Data.Kernel.SporSch.ZOrbK
public import CFSG.Certificates.Kernel.Spor.Loops

public section

namespace CFSG.KS.SporSch.MBT

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Raw.Orb CFSG.KS.Prim CFSG.KS.SporSch.MOC
open CFSG.Certificates CFSG.Sporadic.Schreier CFSG.Monster.B.Co2.Native CFSG.Monster.B.Mathieu
open Finset

theorem orb_sum (T : Nat → Bool) {c nr q : Nat} (OJ OE RP : Nat → Nat) (hc : c = nr * q)
    (hJ : ∀ k < c, OJ k < nr) (hE : ∀ k < c, OE k < q)
    (hinj : ∀ k < c, ∀ k' < c, OJ k = OJ k' → OE k = OE k' → k = k')
    (hT : ∀ k < c, T k = T (RP (OJ k))) :
    (∑ k ∈ range c, if T k = true then 1 else 0) =
      q * ∑ j ∈ range nr, if T (RP j) = true then 1 else 0 := by
  have hmaps : ∀ k ∈ range c, OJ k ∈ range nr := fun k hk =>
    mem_range.2 (hJ k (mem_range.1 hk))
  have hle : ∀ j ∈ range nr, #((range c).filter fun k => OJ k = j) ≤ q := by
    intro j _
    have := Finset.card_le_card_of_injOn (f := OE) (s := (range c).filter fun k => OJ k = j)
      (t := range q) (fun k hk => by
        simp only [coe_filter, Set.mem_setOf_eq, mem_range] at hk
        exact mem_coe.2 (mem_range.2 (hE k hk.1))) (fun k hk k' hk' e => by
        simp only [coe_filter, Set.mem_setOf_eq, mem_range] at hk hk'
        exact hinj k hk.1 k' hk'.1 (hk.2.trans hk'.2.symm) e)
    simpa using this
  have hsum : ∑ j ∈ range nr, #((range c).filter fun k => OJ k = j) = ∑ _j ∈ range nr, q := by
    rw [← card_eq_sum_card_fiberwise hmaps, card_range, sum_const, card_range, smul_eq_mul, hc]
  have hfib : ∀ j ∈ range nr, #((range c).filter fun k => OJ k = j) = q :=
    (Finset.sum_eq_sum_iff_of_le hle).1 hsum
  calc (∑ k ∈ range c, if T k = true then 1 else 0)
      = ∑ k ∈ range c, (if T (RP (OJ k)) = true then 1 else 0) :=
        Finset.sum_congr rfl fun k hk => by rw [hT k (mem_range.1 hk)]
    _ = ∑ j ∈ range nr, ∑ k ∈ (range c).filter (fun k => OJ k = j),
          (if T (RP (OJ k)) = true then 1 else 0) :=
        (Finset.sum_fiberwise_of_maps_to hmaps _).symm
    _ = ∑ j ∈ range nr, q * (if T (RP j) = true then 1 else 0) := by
        refine Finset.sum_congr rfl fun j hj => ?_
        rw [Finset.sum_const_nat (m := if T (RP j) = true then 1 else 0) fun k hk => by
          rw [(Finset.mem_filter.1 hk).2], hfib j hj]
    _ = q * ∑ j ∈ range nr, if T (RP j) = true then 1 else 0 := (Finset.mul_sum _ _ _).symm

theorem strictB_eqZ (y : Nat) (k : Nat → Bool) : strictB y k = k y := by cases y <;> rfl

@[expose] noncomputable def oF (OT : Nat → Nat) (i k : Nat) : Nat := pg 16 65535 (OT k) i

theorem zOrbK_spec {n w m nr q Z : Nat} {RP OT : Nat → Nat} {d : ClsD} {k : Nat} (hk : k < d.c)
    (h : zOrbK n w m nr q Z RP OT d k = true) :
    oF OT 1 k < nr ∧ oF OT 2 k < q ∧ (oF OT 2 k = 0 → RP (oF OT 1 k) = k) ∧
      (oF OT 2 k ≠ 0 → oF OT 0 k < d.c ∧ oF OT 1 (oF OT 0 k) = oF OT 1 k ∧
        oF OT 2 (oF OT 0 k) + 1 = oF OT 2 k ∧
        pcomp n w m Z (d.ST (oF OT 0 k)) = pcomp n w m (d.ST k) Z) := by
  unfold zOrbK at h
  simp only [strictB_eqZ] at h
  have hk' : Nat.blt k d.c = true := by
    rw [Nat.blt_eq]
    exact hk
  rw [hk'] at h
  simp only at h
  unfold oF
  generalize pg 16 65535 (OT k) 1 = j at h ⊢
  generalize pg 16 65535 (OT k) 2 = e at h ⊢
  generalize pg 16 65535 (OT k) 0 = p at h ⊢
  cases h1 : Nat.blt j nr <;> rw [h1] at h
  · exact absurd h Bool.false_ne_true
  cases h2 : Nat.blt e q <;> rw [h2] at h
  · exact absurd h Bool.false_ne_true
  have hj : j < nr := by
    rw [← Nat.blt_eq]
    exact h1
  have he : e < q := by
    rw [← Nat.blt_eq]
    exact h2
  cases h3 : Nat.beq e 0 <;> rw [h3] at h
  · have he0 : e ≠ 0 := fun h0 => by simp [h0] at h3
    cases h4 : Nat.blt p d.c <;> rw [h4] at h
    · exact absurd h Bool.false_ne_true
    cases h5 : Nat.beq (pg 16 65535 (OT p) 1) j <;> rw [h5] at h
    · exact absurd h Bool.false_ne_true
    cases h6 : Nat.beq (Nat.succ (pg 16 65535 (OT p) 2)) e <;> rw [h6] at h
    · exact absurd h Bool.false_ne_true
    have hp' : p < d.c := by
      rw [← Nat.blt_eq]
      exact h4
    refine ⟨hj, he, fun h0 => absurd h0 he0, fun _ => ⟨hp', Nat.eq_of_beq_eq_true h5,
      Nat.eq_of_beq_eq_true h6, Nat.eq_of_beq_eq_true h⟩⟩
  · have he0 : e = 0 := Nat.eq_of_beq_eq_true h3
    exact ⟨hj, he, fun _ => Nat.eq_of_beq_eq_true h, fun h0 => absurd he0 h0⟩

theorem elems_of_slices {f : Nat → Bool} {c nb : Nat} (hc : c ≤ nb * 256)
    (h : ∀ s < nb, allBlk (Nat.mul 256 s) f 256 = true) : ∀ k < c, f k = true := by
  intro k hk
  have := allBlk_spec (h (k / 256) (by omega)) (k % 256) (Nat.mod_lt _ (by norm_num))
  have e : Nat.add (Nat.mul 256 (k / 256)) (k % 256) = k := by
    change 256 * (k / 256) + k % 256 = k
    omega
  rwa [e] at this

theorem rows_of_slices {f : Nat → Bool} {g C : Nat → Nat} {S : Nat}
    (h : ∀ s < S, allBlk (Nat.mul 1 s) f 1 = true) (hf : ∀ s, f s = Nat.beq (g s) (C s)) :
    ∀ b < ((List.range S).map C).length, g b = ((List.range S).map C).getD b 0 := by
  intro b hb
  rw [List.length_map, List.length_range] at hb
  have h1 := allBlk_spec (h b hb) 0 (by norm_num)
  have e : Nat.add (Nat.mul 1 b) 0 = b := by
    change 1 * b + 0 = b
    omega
  rw [e, hf] at h1
  rw [List.getD_eq_getElem _ _ (by simpa using hb), List.getElem_map, List.getElem_range]
  exact Nat.eq_of_beq_eq_true h1

variable {n w : Nat} {PS PSI LR TR TRI : Nat → Nat} {kS nb BP NS CH : Nat}
  {S : Array (Array Nat)} {base : Array Nat} {D : List (List Int)} {gA gB : Equiv.Perm (Fin n)}

open scoped Classical

theorem orderOf_cj {G : Type*} [Group G] (c x : G) : orderOf (c * x * c⁻¹) = orderOf x :=
  (MulAut.conj c).orderOf_eq x

theorem xyWordP_conj {G : Type*} [Group G] (c x y xi yi : G) (wd : List Nat) :
    xyWordP (c * x * c⁻¹) (c * y * c⁻¹) (c * xi * c⁻¹) (c * yi * c⁻¹) wd =
      c * xyWordP x y xi yi wd * c⁻¹ := by
  induction wd with
  | nil => simp [xyWordP]
  | cons l wd ih =>
    simp only [xyWordP, List.map_cons, List.prod_cons] at ih ⊢
    rw [ih]
    split_ifs <;> group

theorem cntZOrb_sem (hQ : ChainS n w PS PSI LR TR TRI kS 2 nb BP S base D NS CH)
    (hA : imageList gA = (unpack n w (PS 0)).toList)
    (hB : imageList gB = (unpack n w (PS 1)).toList) (hnd : base.toList.Nodup)
    {mx my : Nat} {d : ClsD} (r : gen2 gA gB)
    (hsem : ClsSem n w (gen2 gA gB) (r : Equiv.Perm (Fin n)) mx d)
    (z : gen2 gA gB) {Z : Nat} (hZ : imageList (z : Equiv.Perm (Fin n)) = (unpack n w Z).toList)
    (hmx : 0 < mx) (hmy : 0 < my) {ws : List (List Nat × Nat)}
    {nr q : Nat} {RP OT : Nat → Nat} (hc : d.c = nr * q)
    (u : gen2 gA gB) {U : Nat} (hU : imageList (u : Equiv.Perm (Fin n)) = (unpack n w U).toList)
    (huz : u * z = z * u)
    (hO : ∀ k < d.c, zOrbK n w (mask w) nr q U RP OT d k = true)
    (hRP : zRepLtK nr d.c RP = true) {row : List Nat} (hL : nr ≤ row.length * 256)
    (hrow : ∀ b < row.length,
      cntZK n w (mask w) (pidn n w) mx my ws Z (clsSub d nr RP) (b * 256) 256 = row.getD b 0) :
    q * row.sum = #(univ.filter fun x : gen2 gA gB => IsConj r x ∧
      orderOf (x ^ (mx - 1) * z) = my ∧ ∀ p ∈ ws, p.2 = 0 ∨
        orderOf (xyWordP x (x ^ (mx - 1) * z) (x ^ (mx - 1)) ((x ^ (mx - 1) * z) ^ (my - 1))
          p.1) = p.2) := by
  set T : Nat → Bool := fun k => zTest n w (mask w) (pidn n w) mx my ws Z (d.ST k) with hTdef
  set rowF : List Nat := (List.range (d.c / 256 + 1)).map fun b =>
    cntZK n w (mask w) (pidn n w) mx my ws Z d (b * 256) 256 with hrowF
  have hF := cntZK_sem hQ hA hB hnd r hsem z hZ hmx hmy (row := rowF)
    (by rw [hrowF, List.length_map, List.length_range]; omega)
    (fun b hb => by
      rw [hrowF, List.length_map, List.length_range] at hb
      rw [hrowF, List.getD_eq_getElem _ _ (by simpa using hb), List.getElem_map,
        List.getElem_range])
  rw [← hF]
  have hsF : rowF.sum = ∑ k ∈ range d.c, if T k = true then 1 else 0 :=
    sum_blocks T d.c rowF (by rw [hrowF, List.length_map, List.length_range]; omega)
      (fun b hb => by
        rw [hrowF, List.length_map, List.length_range] at hb
        rw [hrowF, List.getD_eq_getElem _ _ (by simpa using hb), List.getElem_map,
          List.getElem_range, cntZK_eq])
  have hsR : row.sum = ∑ j ∈ range nr, if T (RP j) = true then 1 else 0 :=
    sum_blocks (fun j => T (RP j)) nr row hL (fun b hb => by rw [← hrow b hb, cntZK_eq]; rfl)
  rw [hsF, hsR]
  obtain ⟨bv, -, hK, -, -, -⟩ := chainK_of_chainS hQ hA hB hnd
  have pZ := prep_of_imageList hZ
  have pU := prep_of_imageList hU
  obtain ⟨-, -, -, -, h32, hw⟩ := gens_prep hK hA.symm hB.symm
  have hE := hsem.1
  have hro : orderOf r = mx := by
    rw [← Subgroup.orderOf_coe]
    exact hsem.2.2.2
  have hmemK : ∀ y ∈ CFSG.Sporadic.SmallOddCore.conjClass (gen2 gA gB) (r : Equiv.Perm (Fin n)),
      y ∈ gen2 gA gB := by
    rintro _ ⟨c, hc', rfl⟩
    exact (gen2 gA gB).mul_mem ((gen2 gA gB).mul_mem hc' r.2) ((gen2 gA gB).inv_mem hc')
  let Cond : gen2 gA gB → Prop := fun x => orderOf (x ^ (mx - 1) * z) = my ∧ ∀ p ∈ ws, p.2 = 0 ∨
    orderOf (xyWordP x (x ^ (mx - 1) * z) (x ^ (mx - 1)) ((x ^ (mx - 1) * z) ^ (my - 1)) p.1) = p.2
  have hT : ∀ x : gen2 gA gB, IsConj r x → ∀ {X : Nat}, PRep n w X x →
      (zTest n w (mask w) (pidn n w) mx my ws Z X = true ↔ Cond x) := by
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
    simp only [Cond]
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
  have hCond : ∀ (c x : gen2 gA gB), c * z = z * c → (Cond (c * x * c⁻¹) ↔ Cond x) := by
    intro c x hcz
    have hp : ∀ e : Nat, (c * x * c⁻¹) ^ e = c * x ^ e * c⁻¹ := fun e => conj_pow
    have hci : c⁻¹ * z = z * c⁻¹ := by
      rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, hcz, mul_inv_cancel_right]
    have hy : c * x ^ (mx - 1) * c⁻¹ * z = c * (x ^ (mx - 1) * z) * c⁻¹ := by
      rw [mul_assoc _ c⁻¹ z, hci]
      simp only [mul_assoc]
    have hyp : ∀ e : Nat, (c * (x ^ (mx - 1) * z) * c⁻¹) ^ e = c * (x ^ (mx - 1) * z) ^ e * c⁻¹ :=
      fun e => conj_pow
    simp only [Cond, hp, hy, hyp, xyWordP_conj, orderOf_cj]
  let el : ∀ k, k < d.c → Equiv.Perm (Fin n) := fun k hk => Classical.choose (hE k hk)
  have hel : ∀ k (hk : k < d.c), el k hk ∈ CFSG.Sporadic.SmallOddCore.conjClass (gen2 gA gB)
      (r : Equiv.Perm (Fin n)) ∧ PRep n w (d.ST k) (el k hk) :=
    fun k hk => Classical.choose_spec (hE k hk)
  have hRP' : ∀ j < nr, RP j < d.c := by
    intro j hj
    have := hRP
    unfold zRepLtK at this
    have h := allN_spec this j hj
    rwa [Nat.blt_eq] at h
  have hJ : ∀ k < d.c, oF OT 1 k < nr := fun k hk => (zOrbK_spec hk (hO k hk)).1
  have hE2 : ∀ k < d.c, oF OT 2 k < q := fun k hk => (zOrbK_spec hk (hO k hk)).2.1
  have horb : ∀ e, ∀ k (hk : k < d.c), oF OT 2 k = e →
      el k hk = (u : Equiv.Perm (Fin n)) ^ e * el (RP (oF OT 1 k)) (hRP' _ (hJ k hk)) *
        ((u : Equiv.Perm (Fin n)) ^ e)⁻¹ := by
    intro e
    induction e with
    | zero =>
      intro k hk he0
      have hrk := (zOrbK_spec hk (hO k hk)).2.2.1 he0
      have : ∀ k' (hk' : k' < d.c), k' = k → el k hk = el k' hk' := by
        rintro k' hk' rfl
        rfl
      rw [pow_zero, one_mul, inv_one, mul_one]
      exact this _ (hRP' _ (hJ k hk)) hrk
    | succ e ih =>
      intro k hk hek
      obtain ⟨hp, hpj, hpe, hpc⟩ := (zOrbK_spec hk (hO k hk)).2.2.2 (by omega)
      have ihp := ih _ hp (by omega)
      have q1 := prep_pcomp h32 pU (hel _ hp).2
      have q2 := prep_pcomp h32 (hel k hk).2 pU
      rw [hpc] at q1
      have hzz : (u : Equiv.Perm (Fin n)) * el _ hp = el k hk * u := MOC.prep_unique q1 q2
      have hk' : el k hk = (u : Equiv.Perm (Fin n)) * el _ hp * (u : Equiv.Perm (Fin n))⁻¹ := by
        rw [hzz, mul_inv_cancel_right]
      rw [hk', ihp]
      have : ∀ j₁ j₂ (h₁ : j₁ < nr) (h₂ : j₂ < nr), j₁ = j₂ →
          el (RP j₁) (hRP' _ h₁) = el (RP j₂) (hRP' _ h₂) := by
        rintro j₁ j₂ h₁ h₂ rfl
        rfl
      rw [this _ _ (hJ _ hp) (hJ k hk) hpj]
      group
  refine (orb_sum T (oF OT 1) (oF OT 2) RP hc hJ hE2 ?_ ?_).symm
  · intro k hk k' hk' ej ee
    have h1 := horb _ k hk rfl
    have h2 := horb _ k' hk' rfl
    rw [ee] at h1
    have : ∀ j₁ j₂ (h₁ : j₁ < nr) (h₂ : j₂ < nr), j₁ = j₂ →
        el (RP j₁) (hRP' _ h₁) = el (RP j₂) (hRP' _ h₂) := by
      rintro j₁ j₂ h₁ h₂ rfl
      rfl
    rw [this _ _ (hJ k hk) (hJ k' hk') ej, ← h2] at h1
    have p1 := (hel k hk).2
    rw [h1] at p1
    exact entry_inj_sem hw hsem.2.2.1 hk hk' p1 (hel k' hk').2
  · intro k hk
    have hk2 := hRP' _ (hJ k hk)
    have hx := horb _ k hk rfl
    set j := oF OT 1 k
    set e := oF OT 2 k
    let xk : gen2 gA gB := ⟨el k hk, hmemK _ (hel k hk).1⟩
    let xj : gen2 gA gB := ⟨el (RP j) hk2, hmemK _ (hel _ hk2).1⟩
    have hck : IsConj r xk := (isConj_iff_mem _ _).2 (hel k hk).1
    have hcj : IsConj r xj := (isConj_iff_mem _ _).2 (hel _ hk2).1
    have hxe : xk = u ^ e * xj * (u ^ e)⁻¹ := Subtype.ext (by simpa using hx)
    have hzc : u ^ e * z = z * u ^ e := (Commute.pow_left huz e).eq
    have hk1 := hT xk hck (hel k hk).2
    have hj1 := hT xj hcj (hel _ hk2).2
    rw [hxe] at hk1
    rw [hCond _ _ hzc] at hk1
    simp only [hTdef]
    rw [Bool.eq_iff_iff, hk1, hj1]

theorem cntZOrb_proved (hQ : ChainS n w PS PSI LR TR TRI kS 2 nb BP S base D NS CH)
    (hA : imageList gA = (unpack n w (PS 0)).toList)
    (hB : imageList gB = (unpack n w (PS 1)).toList) (hnd : base.toList.Nodup)
    {mx my cap : Nat} {d : ClsD}
    (hcls : ClsOK n w (unpack n w (PS 0)).toList (unpack n w (PS 1)).toList mx cap [d])
    (r : gen2 gA gB) (hR : imageList (r : Equiv.Perm (Fin n)) = (unpack n w d.R).toList)
    (z : gen2 gA gB) {Z : Nat} (hZ : imageList (z : Equiv.Perm (Fin n)) = (unpack n w Z).toList)
    (hmx : 0 < mx) (hmy : 0 < my) {ws : List (List Nat × Nat)}
    {nr q : Nat} {RP OT : Nat → Nat} (hc : d.c = nr * q)
    (u : gen2 gA gB) {U : Nat} (hU : imageList (u : Equiv.Perm (Fin n)) = (unpack n w U).toList)
    (huz : u * z = z * u)
    (hO : ∀ k < d.c, zOrbK n w (mask w) nr q U RP OT d k = true)
    (hRP : zRepLtK nr d.c RP = true) {row : List Nat} (hL : nr ≤ row.length * 256)
    (hrow : ∀ b < row.length,
      cntZK n w (mask w) (pidn n w) mx my ws Z (clsSub d nr RP) (b * 256) 256 = row.getD b 0) :
    q * row.sum = #(univ.filter fun x : gen2 gA gB => IsConj r x ∧
      orderOf (x ^ (mx - 1) * z) = my ∧ ∀ p ∈ ws, p.2 = 0 ∨
        orderOf (xyWordP x (x ^ (mx - 1) * z) (x ^ (mx - 1)) ((x ^ (mx - 1) * z) ^ (my - 1))
          p.1) = p.2) :=
  cntZOrb_sem hQ hA hB hnd r (clsSem_of_clsOK hQ hA hB hnd hcls (prep_of_imageList hR)) z hZ hmx
    hmy hc u hU huz hO hRP hL hrow

end CFSG.KS.SporSch.MBT

end
