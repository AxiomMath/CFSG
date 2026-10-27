module

public import CFSG.Certificates.Kernel.Spor.PK.M11Pk
public import CFSG.Certificates.Kernel.Spor.PK.Cls
public import CFSG.Certificates.Kernel.Spor.PK.RawSim
public import CFSG.Sporadic.Schreier.Enumeration

public section

namespace CFSG.KS.PK

open CFSG.Certificates CFSG.Sporadic.Schreier CFSG.KS.M11

private theorem map_idxOf_of_nodup {α β : Type*} [BEq α] [LawfulBEq α] {l : List α}
    (hl : l.Nodup) (g : Nat → β) :
    l.map (fun v => g (l.idxOf v)) = (List.range l.length).map g := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp [hl.idxOf_getElem]

section

variable {n : Nat} {hn : 1 ≤ n} {F : Nat → Nat → Nat} {NL k : Nat} {bs : Vector (Fin n) k}
  {hbs : bs.toList.Nodup}

private theorem levelTransversals_rawOf (hF : PairsOK n F NL) (i : Fin k) :
    levelTransversals (rawOf n hn F NL bs hbs) i =
      (List.range (BS.run F (lvAt F NL (bs.toList.map Fin.val) i.val) n
          (bs.get i).val).pts.length).map
        fun j => permOf n (BS.trans F (BS.run F (lvAt F NL (bs.toList.map Fin.val) i.val) n
          (bs.get i).val) j) := by
  have hkeys := rawOf_keys (hn := hn) (hbs := hbs) hF i
  have hok : RunOK n F (lvAt F NL (bs.toList.map Fin.val) i.val) (bs.get i).val
      (BS.run F (lvAt F NL (bs.toList.map Fin.val) i.val) n (bs.get i).val) :=
    run_ok (fun l hl x hx => (hF.2 l (lvAt_sub _ _ _ _ l hl)).1.1 x hx) (bs.get i).isLt
  have hnd := hok.nodup
  have htr := rawOf_transversal (hn := hn) (hbs := hbs) hF i
  set s := BS.run F (lvAt F NL (bs.toList.map Fin.val) i.val) n (bs.get i).val with hs
  show ((rawOf n hn F NL bs hbs).orbitSearch i).keys.map
    (fun x => (((rawOf n hn F NL bs hbs).orbitSearch i).transversal? x).getD 1) = _
  rw [← map_idxOf_of_nodup hnd]
  have e := congrArg (List.map fun v => permOf n (BS.trans F s (s.pts.idxOf v))) hkeys
  rw [List.map_map] at e
  rw [← e]
  refine List.map_congr_left fun x hx => ?_
  have hxmem : x.val ∈ s.pts := by
    rw [← hkeys]
    exact List.mem_map_of_mem hx
  show ((rawOf n hn F NL bs hbs).transversal? i x).getD 1 = _
  rw [htr x]
  dsimp only
  rw [if_pos hxmem]
  rfl

private theorem enumeration_rawOf (hF : PairsOK n F NL) :
    enumeration (rawOf n hn F NL bs hbs) =
      products ((List.finRange k).map fun i =>
        (List.range (BS.run F (lvAt F NL (bs.toList.map Fin.val) i.val) n
            (bs.get i).val).pts.length).map
          fun j => permOf n (BS.trans F (BS.run F (lvAt F NL (bs.toList.map Fin.val) i.val) n
            (bs.get i).val) j)) :=
  congrArg products (List.map_congr_left fun i _ => levelTransversals_rawOf hF i)

end

private theorem products_four {M : Type*} [Monoid M] (A0 A1 A2 A3 : List Nat)
    (P0 P1 P2 P3 : Nat → M) :
    products [A0.map P0, A1.map P1, A2.map P2, A3.map P3] =
      A0.flatMap fun k0 => A1.flatMap fun k1 => A2.flatMap fun k2 => A3.map fun k3 =>
        P0 k0 * (P1 k1 * (P2 k2 * (P3 k3 * 1))) := by
  simp [products, List.flatMap_map, List.map_flatMap, List.map_map, ← List.map_eq_flatMap,
    Function.comp_def]

private theorem permOf_mul4 {f0 f1 f2 f3 : Nat → Nat} (h0 : IsPermN 11 f0) (h1 : IsPermN 11 f1)
    (h2 : IsPermN 11 f2) (h3 : IsPermN 11 f3) :
    permOf 11 f0 * (permOf 11 f1 * (permOf 11 f2 * (permOf 11 f3 * 1))) =
      permOf 11 (fd 4 (enc 4 (fun x => f0 (f1 (f2 (f3 x)))) 11)) := by
  have h : IsPermN 11 fun x => f0 (f1 (f2 (f3 x))) := h0.comp (h1.comp (h2.comp h3))
  rw [mul_one, permOf_mul h2 h3, permOf_mul h1 (h2.comp h3), permOf_mul h0 (h1.comp (h2.comp h3))]
  exact permOf_congr fun x hx =>
    (fd_enc (fun i hi => lt_of_lt_of_le (h.1 i hi) (by norm_num)) hx).symm

private theorem flatMap_congr_mem {α β : Type*} {l : List α} {f g : α → List β}
    (h : ∀ x ∈ l, f x = g x) : l.flatMap f = l.flatMap g := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.flatMap_cons, List.flatMap_cons, h a List.mem_cons_self,
      ih fun x hx => h x (List.mem_cons_of_mem a hx)]

private theorem products_prodsA {F : Nat → Nat → Nat} {s0 s1 s2 s3 : BS}
    (h0 : ∀ k < s0.pts.length, IsPermN 11 (BS.trans F s0 k))
    (h1 : ∀ k < s1.pts.length, IsPermN 11 (BS.trans F s1 k))
    (h2 : ∀ k < s2.pts.length, IsPermN 11 (BS.trans F s2 k))
    (h3 : ∀ k < s3.pts.length, IsPermN 11 (BS.trans F s3 k)) :
    products [(List.range s0.pts.length).map fun j => permOf 11 (BS.trans F s0 j),
        (List.range s1.pts.length).map fun j => permOf 11 (BS.trans F s1 j),
        (List.range s2.pts.length).map fun j => permOf 11 (BS.trans F s2 j),
        (List.range s3.pts.length).map fun j => permOf 11 (BS.trans F s3 j)] =
      (prodsA F s0 s1 s2 s3).map fun g => permOf 11 (fd 4 g) := by
  rw [products_four]
  unfold prodsA
  simp only [List.map_flatMap, List.map_map]
  refine flatMap_congr_mem fun k0 hk0 => flatMap_congr_mem fun k1 hk1 =>
    flatMap_congr_mem fun k2 hk2 => List.map_congr_left fun k3 hk3 => ?_
  exact permOf_mul4 (h0 k0 (List.mem_range.1 hk0)) (h1 k1 (List.mem_range.1 hk1))
    (h2 k2 (List.mem_range.1 hk2)) (h3 k3 (List.mem_range.1 hk3))

theorem enumeration_rawOf4 {F : Nat → Nat → Nat} {NL : Nat} (hF : PairsOK 11 F NL)
    (hbs : (#v[0, 1, 2, 3] : Vector (Fin 11) 4).toList.Nodup) :
    enumeration (rawOf 11 (by decide) F NL #v[0, 1, 2, 3] hbs) =
      (prodsA F (BS.run F (lvAt F NL [0, 1, 2, 3] 0) 11 0) (BS.run F (lvAt F NL [0, 1, 2, 3] 1) 11 1)
        (BS.run F (lvAt F NL [0, 1, 2, 3] 2) 11 2) (BS.run F (lvAt F NL [0, 1, 2, 3] 3) 11 3)).map
        fun g => permOf 11 (fd 4 g) := by
  rw [enumeration_rawOf hF]
  have hfin : List.finRange 4 = [0, 1, 2, 3] := rfl
  rw [hfin]
  simp only [List.map_cons, List.map_nil]
  have hlv : ∀ i l, l ∈ lvAt F NL [0, 1, 2, 3] i → IsPermN 11 (F l) := fun i l hl =>
    (hF.2 l (lvAt_sub _ _ _ _ l hl)).1
  have hperm : ∀ i < 11, ∀ k < (BS.run F (lvAt F NL [0, 1, 2, 3] i) 11 i).pts.length,
      IsPermN 11 (BS.trans F (BS.run F (lvAt F NL [0, 1, 2, 3] i) 11 i) k) := fun i hi k hk =>
    trans_isPermN (run_ok (fun l hl x hx => (hlv i l hl).1 x hx) hi) (hlv i) hk
  exact products_prodsA (hperm 0 (by norm_num)) (hperm 1 (by norm_num)) (hperm 2 (by norm_num))
    (hperm 3 (by norm_num))

theorem perm_enumeration {n : Nat} {Q Q' : RawSchreierDatum n} (hQ : Q.check = true)
    (hQ' : Q'.check = true) (h0 : Q.levelSubgroup 0 = Q'.levelSubgroup 0) :
    (enumeration Q).Perm (enumeration Q') := by
  rw [List.perm_ext_iff_of_nodup (enumeration_nodup Q hQ) (enumeration_nodup Q' hQ')]
  intro g
  rw [mem_enumeration_iff Q hQ, mem_enumeration_iff Q' hQ',
    ← Q.levelSubgroup_zero_eq_original hQ, ← Q'.levelSubgroup_zero_eq_original hQ', h0]

theorem length_filter_eq_of_perm {α : Type*} {E E' : List α} (h : E.Perm E') (p : α → Bool) :
    (E.filter p).length = (E'.filter p).length :=
  (h.filter p).length_eq

theorem length_filter_product_eq_of_perm {α : Type*} {E E' : List α} (h : E.Perm E')
    (p q : α → Bool) (r : α × α → Bool) :
    (((E.filter p) ×ˢ (E.filter q)).filter r).length =
      (((E'.filter p) ×ˢ (E'.filter q)).filter r).length :=
  (((h.filter p).product (h.filter q)).filter r).length_eq

private theorem length_filter_product {α β : Type*} (l₁ : List α) (l₂ : List β)
    (r : α × β → Bool) :
    ((l₁ ×ˢ l₂).filter r).length = (l₁.map fun a => l₂.countP fun b => r (a, b)).sum := by
  induction l₁ with
  | nil => simp
  | cons a l₁ ih =>
    rw [List.product_cons, List.filter_append, List.length_append, ih, List.map_cons,
      List.sum_cons, List.filter_map, List.length_map, List.countP_eq_length_filter]
    rfl

private theorem invPair_pinvS {g : Nat} (hg : IsPermN 11 (fd 4 g)) :
    CFSG.KS.M11Class.invPair (CFSG.KC.Enum.pidn 11 4) g (CFSG.KS.pinvS 11 4 15 g) = true := by
  have hinv : CFSG.KS.pinvS 11 4 15 g = enc 4 (finv 11 (fd 4 g)) 11 :=
    pinvS_eq (n := 11) (w := 4) (p := g) (g := finv 11 (fd 4 g)) (by decide) hg.1
      (fun j hj => finv_spec hg hj) (fun i hi => finv_apply hg hi)
  have hfd : ∀ i < 11, fd 4 (CFSG.KS.pinvS 11 4 15 g) i = finv 11 (fd 4 g) i := fun i hi => by
    rw [hinv]
    exact fd_enc (fun j _ => lt_of_lt_of_le (finv_lt (by norm_num) _ _) (by norm_num)) hi
  refine invPair_iff.2 ⟨fun i hi => ⟨hg.1 i hi, ?_⟩, fun i hi => ?_, fun i hi => ?_⟩
  · rw [hfd i hi]
    exact finv_lt (by norm_num) _ _
  · rw [hfd i hi]
    exact (finv_spec hg hi).2
  · rw [hfd _ (hg.1 i hi)]
    exact finv_apply hg hi

private theorem orderIs_permOf {f : Nat → Nat} (hf : IsPermN 11 f) {m : Nat} (hm : 0 < m)
    {σ : Equiv.Perm (Fin 11)} (hσ : σ = permOf 11 f) : orderIs σ m = (ordF 11 f == m) := by
  apply Bool.eq_iff_iff.2
  rw [orderIs_iff σ hm, hσ, orderOf_permOf hf, beq_iff_eq]

theorem pairCntL_pairsOf {X Y : List Nat}
    (hX : ∀ g ∈ X, g < 2 ^ (4 * 11) ∧ IsPermN 11 (fd 4 g))
    (hY : ∀ g ∈ Y, g < 2 ^ (4 * 11) ∧ IsPermN 11 (fd 4 g)) :
    pairCntL (pairsOf X) (pairsOf Y) =
      (((X.map fun g => permOf 11 (fd 4 g)) ×ˢ (Y.map fun g => permOf 11 (fd 4 g))).filter
        fun q => orderIs (q.1 * q.2) 11 && orderIs (q.1 * q.2 * q.1⁻¹ * q.2⁻¹) 6).length := by
  rw [length_filter_product, pairCntL_eq,
    show pairsOf X = X.map (fun g => (g, CFSG.KS.pinvS 11 4 15 g)) from rfl, List.map_map,
    List.map_map]
  refine congrArg List.sum (List.map_congr_left fun x hx => ?_)
  have hxp : IsPermN 11 (fd 4 x) := (hX x hx).2
  simp only [Function.comp_apply]
  rw [rowCnt_eq, show pairsOf Y = Y.map (fun g => (g, CFSG.KS.pinvS 11 4 15 g)) from rfl,
    List.countP_map, List.countP_map]
  refine List.countP_congr fun y hy => ?_
  have hyp : IsPermN 11 (fd 4 y) := (hY y hy).2
  simp only [Function.comp_apply]
  rw [pairOK_eq (invPair_pinvS hxp) (invPair_pinvS hyp)]
  have hcomm : permOf 11 (fd 4 x) * permOf 11 (fd 4 y) * (permOf 11 (fd 4 x))⁻¹ *
      (permOf 11 (fd 4 y))⁻¹ =
      permOf 11 (fun i => fd 4 x (fd 4 y (finv 11 (fd 4 x) (finv 11 (fd 4 y) i)))) := by
    rw [permOf_inv hxp, permOf_inv hyp, permOf_mul hxp hyp, permOf_mul (hxp.comp hyp) hxp.finv,
      permOf_mul ((hxp.comp hyp).comp hxp.finv) hyp.finv]
  rw [orderIs_permOf (hxp.comp hyp) (by norm_num) (permOf_mul hxp hyp),
    orderIs_permOf (hxp.comp (hyp.comp (hxp.finv.comp hyp.finv))) (by norm_num) hcomm]

end CFSG.KS.PK

end
