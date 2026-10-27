module

public import CFSG.Certificates.Kernel.SporSch.ChainKPack
public import Certificates.Data.Kernel.SporSch.MathieuOC2

public section

namespace CFSG.KS.SporSch.MOC

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Raw.Orb CFSG.KS.Prim CFSG.KS.M11
open CFSG.Certificates CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native CFSG.Sporadic.Th
open CFSG.Sporadic.Th.Native CFSG.Monster.B.Mathieu

@[expose] def Cnt2 (LR : Nat → Nat) (CS : List (List Nat)) (f : Nat → Nat → Nat) : Prop :=
  CS.length = rcnt (LR 0) ∧ ∀ k₀ < rcnt (LR 0), (CS.getD k₀ []).length = rcnt (LR 1) ∧
    ∀ k₁ < rcnt (LR 1), f k₀ k₁ = (CS.getD k₀ []).getD k₁ 0

@[expose] noncomputable def trL (n w : Nat) (LR TR : Nat → Nat) (i : Nat) :
    List (Equiv.Perm (Fin n)) :=
  (List.range (rcnt (LR i))).map (trP n w LR TR i)

theorem enumFrom_zero (n w m nw : Nat) (LR TR : Nat → Nat) (p : Nat → Bool) (i g s : Nat) :
    enumFrom n w m nw LR TR p 0 i g s = if p g = true then s + 1 else s := by
  change nIf(p g, Nat.succ s, s) = _
  rw [Orb.nIf_eq]

theorem enumFrom_succ (n w m nw : Nat) (LR TR : Nat → Nat) (p : Nat → Bool) (d i g s : Nat) :
    enumFrom n w m nw LR TR p (d + 1) i g s = (List.range (rcnt (LR i))).foldl
      (fun s k => enumFrom n w m nw LR TR p d (i + 1) (pcomp n w m g (TR (roff n nw (LR i) + k)))
        s) s := by
  have e : enumFrom n w m nw LR TR p (d + 1) i g s = strictN (LR i) (fun R =>
      foldUp (rcnt R) (fun k s => strictN (pcomp n w m g (TR (Nat.add (roff n nw R) k)))
        (fun h => enumFrom n w m nw LR TR p d (Nat.succ i) h s)) s) := rfl
  rw [e, Orb.strictN_eq, foldUp_eq]
  congr 1
  funext s k
  rw [Orb.strictN_eq]
  rfl

theorem foldl_eq_add {f : Nat → Nat → Nat} {X : Nat → Nat} :
    ∀ (l : List Nat), (∀ k ∈ l, ∀ s, f s k = s + X k) → ∀ s, l.foldl f s = s + (l.map X).sum
  | [], _, s => by simp
  | k :: l, h, s => by
    rw [List.foldl_cons, h k List.mem_cons_self s,
      foldl_eq_add l (fun k' hk' => h k' (List.mem_cons_of_mem k hk')), List.map_cons,
      List.sum_cons, Nat.add_assoc]

theorem countP_products_cons {M : Type*} [Group M] (q : M → Bool) (g : M) (T : List M)
    (Ts : List (List M)) :
    ((products (T :: Ts)).map (g * ·)).countP q =
      (T.map fun t => ((products Ts).map ((g * t) * ·)).countP q).sum := by
  rw [products_map_mul, List.countP_flatMap]
  rfl

theorem range_map_succ {α : Type*} (f : Nat → α) (i d : Nat) :
    (List.range (d + 1)).map (fun t => f (i + t)) =
      f i :: (List.range d).map fun t => f (i + 1 + t) := by
  rw [List.range_succ_eq_map, List.map_cons, List.map_map]
  congr 1
  apply List.map_congr_left
  intro t _
  simp only [Function.comp_apply]
  congr 1
  omega

theorem sum_range_getD {CS : List Nat} {c : Nat} (hc : CS.length = c) {f : Nat → Nat}
    (hf : ∀ k < c, f k = CS.getD k 0) : ((List.range c).map f).sum = CS.sum := by
  congr 1
  apply List.ext_getElem (by simp [hc])
  intro k h1 h2
  simp only [List.getElem_map, List.getElem_range]
  rw [hf k (by simpa using h1), List.getD_eq_getElem]

theorem sum_counts2 {LR : Nat → Nat} {CS : List (List Nat)} {f : Nat → Nat → Nat}
    (hc : Cnt2 LR CS f) :
    ((List.range (rcnt (LR 0))).map fun k₀ => ((List.range (rcnt (LR 1))).map fun k₁ =>
      f k₀ k₁).sum).sum = (CS.map List.sum).sum := by
  obtain ⟨h0, h1⟩ := hc
  refine sum_range_getD (CS := CS.map List.sum) (by simpa using h0) fun k₀ hk₀ => ?_
  have hlt : k₀ < CS.length := by omega
  have := sum_range_getD (h1 k₀ hk₀).1 (h1 k₀ hk₀).2
  rw [List.getD_eq_getElem _ _ hlt] at this
  rw [List.getD_eq_getElem _ _ (by simpa using hlt), List.getElem_map, this]

variable {n w : Nat} {gens : List (Equiv.Perm (Fin n))} {words : List (List Int)} {k : Nat}
  {bv : Vector (Fin n) k} {PS PSI LR TR TRI : Nat → Nat} {kS BP NS CH : Nat}

section Chain

variable (hQ : ChainK n w gens words bv PS PSI LR TR TRI kS BP NS CH)
include hQ

theorem chainK_szOK : szOK n w = true := by
  have h1 := hQ.2.1
  have h2 := hQ.2.2.1
  unfold szOK
  rw [bAnd_eq, Bool.and_eq_true, Nat.blt_eq, Nat.blt_eq]
  refine ⟨Nat.lt_of_lt_of_le h2 (by decide), ?_⟩
  change n + 1 < 1 <<< w
  rw [Nat.one_shiftLeft]
  exact h1

theorem tr_facts {i k' : Nat} (hi : i < k) (hk : k' < rcnt (LR i)) :
    PRep n w (TR (roff n (n * w) (LR i) + k')) (trP n w LR TR i k') ∧
      TR (roff n (n * w) (LR i) + k') >>> (n * w) = 0 :=
  ⟨((chainK_agree hQ hi).2 k' hk).1,
    (permOK_facts ((levelK_facts (hQ.2.2.2.2.2.2.1 i hi)).2.2.2.2.2 k' hk)).1⟩

theorem enumFrom_spec {p : Nat → Bool} {q : Equiv.Perm (Fin n) → Bool}
    (hp : ∀ P x, PRep n w P x → P >>> (n * w) = 0 → p P = q x) :
    ∀ d i, i + d ≤ k → ∀ G g s, PRep n w G g → G >>> (n * w) = 0 →
      enumFrom n w (mask w) (n * w) LR TR p d i G s =
        s + ((products ((List.range d).map fun t => trL n w LR TR (i + t))).map (g * ·)).countP q
  | 0, i, _, G, g, s, hG, sG => by
    rw [enumFrom_zero, hp G g hG sG]
    simp only [List.range_zero, List.map_nil, products, List.map_cons, mul_one,
      List.countP_singleton]
    split <;> simp_all
  | d + 1, i, hd, G, g, s, hG, sG => by
    have hn := chainK_h32 hQ
    have hw := PF.w_pos hQ.2.1
    rw [enumFrom_succ, range_map_succ, countP_products_cons, trL, List.map_map]
    refine foldl_eq_add _ (fun k' hk' s => ?_) s
    have hk := List.mem_range.1 hk'
    obtain ⟨h1, -⟩ := tr_facts hQ (by omega) hk
    rw [enumFrom_spec hp d (i + 1) (by omega) _ (g * trP n w LR TR i k') s (prep_pcomp hn hG h1)
      (PF.pcomp_shr _ _ hn hw)]
    rfl

variable (hn : 1 ≤ n) (hbs : bv.toList.Nodup)
include hn hbs

theorem finRange_levelTransversals :
    (List.finRange (certificate hn gens words bv hbs).baseCount).map
      (levelTransversals (certificate hn gens words bv hbs)) =
      (List.range k).map (trL n w LR TR) := by
  apply List.ext_getElem (by simp [certificate])
  intro i h1 h2
  have hi : i < k := by simpa using h2
  simp only [List.getElem_map, List.getElem_finRange, List.getElem_range]
  exact levelTransversals_eq hQ hn hbs hi

theorem enumeration_trL :
    enumeration (certificate hn gens words bv hbs) =
      products ((List.range k).map (trL n w LR TR)) := by
  rw [enumeration, finRange_levelTransversals hQ hn hbs]

theorem countP_coset1 (hk : 0 < k) (q : Equiv.Perm (Fin n) → Bool) (g₀ : Equiv.Perm (Fin n)) :
    ((enumeration (certificate hn gens words bv hbs)).map (g₀ * ·)).countP q =
      ((List.range (rcnt (LR 0))).map fun k₀ =>
        ((products ((List.range (k - 1)).map fun t => trL n w LR TR (1 + t))).map
          ((g₀ * trP n w LR TR 0 k₀) * ·)).countP q).sum := by
  obtain ⟨d, rfl⟩ : ∃ d, k = d + 1 := ⟨k - 1, by omega⟩
  have e := range_map_succ (trL n w LR TR) 0 d
  simp only [Nat.zero_add] at e
  rw [enumeration_trL hQ hn hbs, e, countP_products_cons, trL, List.map_map, Nat.add_sub_cancel]
  rfl

theorem countP_coset2 (hk : 2 ≤ k) (q : Equiv.Perm (Fin n) → Bool) (g₀ : Equiv.Perm (Fin n)) :
    ((enumeration (certificate hn gens words bv hbs)).map (g₀ * ·)).countP q =
      ((List.range (rcnt (LR 0))).map fun k₀ => ((List.range (rcnt (LR 1))).map fun k₁ =>
        ((products ((List.range (k - 2)).map fun t => trL n w LR TR (2 + t))).map
          ((g₀ * trP n w LR TR 0 k₀ * trP n w LR TR 1 k₁) * ·)).countP q).sum).sum := by
  rw [countP_coset1 hQ hn hbs (by omega)]
  congr 1
  apply List.map_congr_left
  intro k₀ _
  obtain ⟨d, rfl⟩ : ∃ d, k = d + 2 := ⟨k - 2, by omega⟩
  have e : d + 2 - 1 = d + 1 := rfl
  rw [Nat.add_sub_cancel, e, range_map_succ, countP_products_cons, trL, List.map_map]
  rfl

theorem chainK_cosetCount' {g₀ : Equiv.Perm (Fin n)} {G₀ e : Nat}
    (hg₀ : imageList g₀ = (unpack n w G₀).toList) (he : 0 < e) (hk : 0 < k) {CS : List Nat}
    (hCS : CS.length = rcnt (LR 0))
    (hc : ∀ k₀ < rcnt (LR 0), cntOrdK n w (mask w) (n * w) (pidn n w) LR TR k G₀ e k₀ =
      CS.getD k₀ 0) :
    (cosetOrderTables (certificate hn gens words bv hbs) g₀ e).length = CS.sum := by
  have hn32 := chainK_h32 hQ
  have hw := PF.w_pos hQ.2.1
  have hsz := chainK_szOK hQ
  rw [(forall₂_cosetOrderTables hn32 _ g₀ he).length_eq, List.length_reverse,
    ← List.countP_eq_length_filter, countP_coset1 hQ hn hbs hk]
  refine sum_range_getD hCS fun k₀ hk₀ => ?_
  rw [← hc k₀ hk₀]
  obtain ⟨h1, -⟩ := tr_facts hQ hk hk₀
  have e1 : cntOrdK n w (mask w) (n * w) (pidn n w) LR TR k G₀ e k₀ =
      enumFrom n w (mask w) (n * w) LR TR (fun g => ordIs n w (mask w) (pidn n w) g (e - 1))
        (k - 1) 1 (pcomp n w (mask w) G₀ (TR (roff n (n * w) (LR 0) + k₀))) 0 := by
    unfold cntOrdK
    rw [Orb.strictN_eq]
    rfl
  rw [e1, enumFrom_spec hQ (q := fun x => decide (orderOf x = e))
    (fun P x hP sP => ordIs_eq hsz hP sP he) (k - 1) 1 (by omega) _ _ 0
    (prep_pcomp hn32 (prep_of_imageList hg₀) h1) (PF.pcomp_shr _ _ hn32 hw), Nat.zero_add]

theorem chainK_cosetCount2' {g₀ : Equiv.Perm (Fin n)} {G₀ e : Nat}
    (hg₀ : imageList g₀ = (unpack n w G₀).toList) (he : 0 < e) (hk : 2 ≤ k)
    {CS : List (List Nat)}
    (hc : Cnt2 LR CS (cntOrd2K n w (mask w) (n * w) (pidn n w) LR TR k G₀ e)) :
    (cosetOrderTables (certificate hn gens words bv hbs) g₀ e).length = (CS.map List.sum).sum := by
  have hn32 := chainK_h32 hQ
  have hw := PF.w_pos hQ.2.1
  have hsz := chainK_szOK hQ
  rw [(forall₂_cosetOrderTables hn32 _ g₀ he).length_eq, List.length_reverse,
    ← List.countP_eq_length_filter, countP_coset2 hQ hn hbs hk, ← sum_counts2 hc]
  congr 1
  apply List.map_congr_left
  intro k₀ hk₀
  congr 1
  apply List.map_congr_left
  intro k₁ hk₁
  obtain ⟨t0, -⟩ := tr_facts hQ (by omega) (List.mem_range.1 hk₀)
  obtain ⟨t1, -⟩ := tr_facts hQ (by omega) (List.mem_range.1 hk₁)
  have e1 : cntOrd2K n w (mask w) (n * w) (pidn n w) LR TR k G₀ e k₀ k₁ =
      enumFrom n w (mask w) (n * w) LR TR (fun g => ordIs n w (mask w) (pidn n w) g (e - 1))
        (k - 2) 2 (pcomp n w (mask w) (pcomp n w (mask w) G₀ (TR (roff n (n * w) (LR 0) + k₀)))
          (TR (roff n (n * w) (LR 1) + k₁))) 0 := by
    unfold cntOrd2K start2
    rw [Orb.strictN_eq, Orb.strictN_eq]
    rfl
  rw [e1, enumFrom_spec hQ (q := fun x => decide (orderOf x = e))
    (fun P x hP sP => ordIs_eq hsz hP sP he) (k - 2) 2 (by omega) _ _ 0
    (prep_pcomp hn32 (prep_pcomp hn32 (prep_of_imageList hg₀) t0) t1)
    (PF.pcomp_shr _ _ hn32 hw), Nat.zero_add]

theorem chainK_commCount' {g₀ gA gB : Equiv.Perm (Fin n)} {G₀ A B : Nat}
    (hg₀ : imageList g₀ = (unpack n w G₀).toList)
    (hA : imageList gA = (unpack n w A).toList) (hB : imageList gB = (unpack n w B).toList)
    (hk : 2 ≤ k) {CS : List (List Nat)}
    (hc : Cnt2 LR CS (cntCommK n w (mask w) (n * w) LR TR k G₀ A B)) :
    countProducts n (commAll n [toTable gA, toTable gB])
      (levelTables (certificate hn gens words bv hbs)) (toTable g₀) = (CS.map List.sum).sum := by
  have hn32 := chainK_h32 hQ
  have hw := PF.w_pos hQ.2.1
  have pA := prep_of_imageList hA
  have pB := prep_of_imageList hB
  set q : Equiv.Perm (Fin n) → Bool :=
    fun x => decide (x * gA = gA * x) && decide (x * gB = gB * x)
  rw [countProducts_spec (P := fun x => q x = true) (fun T x hT => by
      simp only [commAll, List.all_cons, List.all_nil, Bool.and_true, q]
      rw [commT_eq hT (rep_toTable hn32 gA), commT_eq hT (rep_toTable hn32 gB)])
    (forall₂_levelTables hn32 _) (rep_toTable hn32 g₀), finRange_levelTransversals hQ hn hbs,
    ← enumeration_trL hQ hn hbs]
  simp only [Bool.decide_eq_true]
  rw [countP_coset2 hQ hn hbs hk, ← sum_counts2 hc]
  congr 1
  apply List.map_congr_left
  intro k₀ hk₀
  congr 1
  apply List.map_congr_left
  intro k₁ hk₁
  obtain ⟨t0, -⟩ := tr_facts hQ (by omega) (List.mem_range.1 hk₀)
  obtain ⟨t1, -⟩ := tr_facts hQ (by omega) (List.mem_range.1 hk₁)
  have e1 : cntCommK n w (mask w) (n * w) LR TR k G₀ A B k₀ k₁ =
      enumFrom n w (mask w) (n * w) LR TR (fun g =>
          (Nat.beq (pcomp n w (mask w) g A) (pcomp n w (mask w) A g) &&
            Nat.beq (pcomp n w (mask w) g B) (pcomp n w (mask w) B g)))
        (k - 2) 2 (pcomp n w (mask w) (pcomp n w (mask w) G₀ (TR (roff n (n * w) (LR 0) + k₀)))
          (TR (roff n (n * w) (LR 1) + k₁))) 0 := by
    unfold cntCommK start2
    rw [Orb.strictN_eq, Orb.strictN_eq]
    simp only [bAnd_eq]
    rfl
  rw [e1, enumFrom_spec hQ (q := q) (fun P x hP _ => by
      rw [beq_pcomp_iff hn32 hw hP pA pA hP, beq_pcomp_iff hn32 hw hP pB pB hP])
    (k - 2) 2 (by omega) _ _ 0 (prep_pcomp hn32 (prep_pcomp hn32 (prep_of_imageList hg₀) t0) t1)
    (PF.pcomp_shr _ _ hn32 hw), Nat.zero_add]

end Chain

end CFSG.KS.SporSch.MOC

end
