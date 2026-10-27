module

public import CFSG.Certificates.Kernel.SporSch.MOCChain
public import CFSG.Sporadic.Schreier.MathieuOddCoreCentral
public import CFSG.Certificates.Kernel.Spor.RawSiftK

public section

namespace CFSG.KS.SporSch.MOC

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Raw.Orb CFSG.Certificates CFSG.Certificates.Native
open CFSG.Certificates.ChainArrays
open CFSG.Sporadic.Schreier CFSG.Monster.B.Co2.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Mathieu

@[expose] noncomputable def trP (n w : Nat) (LR TR : Nat → Nat) (i k : Nat) : Equiv.Perm (Fin n) :=
  permOfArr n (unpack n w (TR (roff n (n * w) (LR i) + k)))

@[expose] noncomputable def elemRP (n w : Nat) (LR TR : Nat → Nat) :
    Nat → Nat → Equiv.Perm (Fin n) → Equiv.Perm (Fin n)
  | 0, _, acc => acc
  | d + 1, j, acc => elemRP n w LR TR d (j / rcnt (LR d)) (trP n w LR TR d (j % rcnt (LR d)) * acc)

@[expose] noncomputable def elemP (n w : Nat) (LR TR : Nat → Nat) (k j : Nat) : Equiv.Perm (Fin n) :=
  elemRP n w LR TR k j 1

@[expose] noncomputable def trLists (n w : Nat) (LR TR : Nat → Nat) (d : Nat) :
    List (List (Equiv.Perm (Fin n))) :=
  (List.range d).map fun i => (List.range (rcnt (LR i))).map (trP n w LR TR i)

theorem elemR_zero (n w m nw : Nat) (LR TR : Nat → Nat) (j acc : Nat) :
    elemR n w m nw LR TR 0 j acc = acc := rfl

theorem elemR_succ (n w m nw : Nat) (LR TR : Nat → Nat) (d j acc : Nat) :
    elemR n w m nw LR TR (d + 1) j acc = elemR n w m nw LR TR d (j / rcnt (LR d))
      (pcomp n w m (TR (roff n nw (LR d) + j % rcnt (LR d))) acc) := by
  unfold elemR
  simp only [strictN_eq]
  rfl

theorem products_append_single {M : Type*} [Monoid M] (T : List M) :
    ∀ A : List (List M), products (A ++ [T]) = (products A).flatMap fun p => T.map (p * ·)
  | [] => by simp [products]
  | T0 :: A => by
    rw [List.cons_append, products, products, products_append_single T A, List.flatMap_assoc]
    congr 1
    funext t
    rw [List.map_flatMap, List.flatMap_map]
    congr 1
    funext p
    rw [List.map_map]
    congr 1
    funext x
    simp [mul_assoc]

theorem getElem?_flatMap_uniform {α β γ : Type*} (T : List β) (f : α → β → γ) :
    ∀ (L : List α) (a b : Nat) (ha : a < L.length) (hb : b < T.length),
      (L.flatMap fun p => T.map (f p))[a * T.length + b]? = some (f L[a] T[b])
  | [], _, _, ha, _ => absurd ha (Nat.not_lt_zero _)
  | x :: L, a, b, ha, hb => by
    rw [List.flatMap_cons]
    rcases a with _ | a
    · rw [Nat.zero_mul, Nat.zero_add, List.getElem?_append_left (by simpa using hb)]
      simp [List.getElem?_eq_getElem hb]
    · rw [List.getElem?_append_right (by simp; nlinarith)]
      have e : (a + 1) * T.length + b - (T.map (f x)).length = a * T.length + b := by
        simp only [List.length_map]
        rw [Nat.succ_mul]
        omega
      rw [e, getElem?_flatMap_uniform T f L a b (by simpa using ha) hb]
      simp

theorem trLists_succ (n w : Nat) (LR TR : Nat → Nat) (d : Nat) :
    trLists n w LR TR (d + 1) =
      trLists n w LR TR d ++ [(List.range (rcnt (LR d))).map (trP n w LR TR d)] := by
  simp [trLists, List.range_succ]

theorem length_products_trLists (n w : Nat) (LR TR : Nat → Nat) (d : Nat) :
    (products (trLists n w LR TR d)).length = ordK LR d := by
  rw [length_products, ordK_eq]
  simp [trLists, List.map_map, Function.comp_def]

theorem elemRP_eq (n w : Nat) (LR TR : Nat → Nat) :
    ∀ (d j : Nat) (hj : j < ordK LR d) (acc : Equiv.Perm (Fin n)),
      elemRP n w LR TR d j acc =
        (products (trLists n w LR TR d))[j]'(by rw [length_products_trLists]; exact hj) * acc
  | 0, j, hj, acc => by
    have : j = 0 := by simpa [ordK] using hj
    subst this
    simp [elemRP, trLists, products]
  | d + 1, j, hj, acc => by
    set c := rcnt (LR d)
    have hord : ordK LR (d + 1) = c * ordK LR d := rfl
    have hc : 0 < c := by
      rcases Nat.eq_zero_or_pos c with h | h
      · rw [hord, h, Nat.zero_mul] at hj
        exact absurd hj (Nat.not_lt_zero _)
      · exact h
    have hq : j / c < ordK LR d := by
      rw [Nat.div_lt_iff_lt_mul hc]
      rw [hord] at hj
      linarith [Nat.mul_comm c (ordK LR d)]
    have hr : j % c < c := Nat.mod_lt j hc
    rw [elemRP, elemRP_eq n w LR TR d (j / c) hq, ← mul_assoc]
    congr 1
    have hj' : j = (j / c) * ((List.range c).map (trP n w LR TR d)).length + j % c := by
      simp only [List.length_map, List.length_range]
      rw [Nat.mul_comm]
      exact (Nat.div_add_mod j c).symm
    have hP := getElem?_flatMap_uniform ((List.range c).map (trP n w LR TR d)) (· * ·)
      (products (trLists n w LR TR d)) (j / c) (j % c)
      (by rw [length_products_trLists]; exact hq) (by simpa using hr)
    rw [← hj', ← products_append_single, ← trLists_succ] at hP
    rw [List.getElem?_eq_getElem] at hP
    simpa [c] using hP.symm

variable {n w : Nat} {gens : List (Equiv.Perm (Fin n))} {words : List (List Int)} {k : Nat}
  {bv : Vector (Fin n) k} {PS PSI LR TR TRI : Nat → Nat} {kS BP NS CH : Nat}

section Chain

variable (hQ : ChainK n w gens words bv PS PSI LR TR TRI kS BP NS CH)
include hQ

theorem chainK_perm : allN kS (fun j => permOK n w (mask w) (n * w) (PS j) (PSI j)) = true :=
  (head_facts hQ.2.2.2.2.2.1).1

theorem chainK_n24 : n < 16777216 := by
  have := hQ.2.2.1
  omega

theorem chainK_agree {i : Nat} (hi : i < k) :
    Agree n w (LR i) (lev n (strongArr n w kS PS) (baseArr w k BP) i) (trP n w LR TR i) ∧
      ∀ k' < rcnt (LR i), PRep n w (TR (roff n (n * w) (LR i) + k')) (trP n w LR TR i k') ∧
        PRep n w (TRI (roff n (n * w) (LR i) + k')) (trP n w LR TR i k')⁻¹ := by
  have hb := binds_of hQ
  exact agree_levelK hb (chainK_perm hQ) (base_lt_of_levels hb hQ.2.2.2.2.2.2.1) hi
    (hQ.2.2.2.2.2.2.1 i hi)

theorem rcnt_pos {i : Nat} (hi : i < k) : 0 < rcnt (LR i) := by
  obtain ⟨_, _, hR, _⟩ := levelK_facts (hQ.2.2.2.2.2.2.1 i hi)
  exact hR.c_pos

theorem prep_elemR : ∀ d ≤ k, ∀ (j ACC : Nat) (acc : Equiv.Perm (Fin n)), PRep n w ACC acc →
    PRep n w (elemR n w (mask w) (n * w) LR TR d j ACC) (elemRP n w LR TR d j acc)
  | 0, _, _, _, _, h => h
  | d + 1, hd, j, ACC, acc, h => by
    rw [elemR_succ, elemRP]
    have hr : j % rcnt (LR d) < rcnt (LR d) := Nat.mod_lt j (rcnt_pos hQ (by omega))
    exact prep_elemR d (by omega) _ _ _
      (prep_pcomp (by have := chainK_n24 hQ; omega) ((chainK_agree hQ (by omega)).2 _ hr).1 h)

theorem prep_elemK (j : Nat) :
    PRep n w (elemK n w (mask w) (n * w) (pidn n w) LR TR k j) (elemP n w LR TR k j) :=
  prep_elemR hQ k le_rfl j _ 1 (prep_pidn (chainK_n24 hQ) hQ.2.1)

theorem elemK_shr (j : Nat) : elemK n w (mask w) (n * w) (pidn n w) LR TR k j >>> (n * w) = 0 := by
  have hw := PF.w_pos hQ.2.1
  have h32 : n < 2 ^ 32 := by have := chainK_n24 hQ; omega
  unfold elemK
  rcases k with _ | d
  · exact PF.pidn_shr (chainK_n24 hQ) hQ.2.1
  · suffices ∀ d' j ACC, ACC >>> (n * w) = 0 →
        elemR n w (mask w) (n * w) LR TR d' j ACC >>> (n * w) = 0 by
      rw [elemR_succ]
      exact this d _ _ (PF.pcomp_shr _ _ h32 hw)
    intro d'
    induction d' with
    | zero => intro j ACC h; exact h
    | succ d' ih =>
      intro j ACC _
      rw [elemR_succ]
      exact ih _ _ (PF.pcomp_shr _ _ h32 hw)

variable (hn : 1 ≤ n) (hbs : bv.toList.Nodup)
include hn hbs

theorem levelTransversals_eq {i : Nat} (hi : i < k) :
    levelTransversals (certificate hn gens words bv hbs) ⟨i, hi⟩ =
      (List.range (rcnt (LR i))).map (trP n w LR TR i) := by
  obtain ⟨hA, hraw⟩ := chainK_arrays hn hbs hQ
  have hF := chainCheckFacts hraw
  have hAg := (chainK_agree hQ hi).1
  dsimp only [levelTransversals]
  rw [hA.orbitSearch_eq hF hi]
  simp only [SchreierOrbitState.keys, List.map_map, hAg.cnt]
  apply List.map_congr_left
  intro k' hk'
  have hk : k' < (lev n (strongArr n w kS PS) (baseArr w k BP) i).pts.size :=
    List.mem_range.1 hk'
  have ht := hA.transversal_of_lt hF hi hk
  rw [hA.orbitSearch_eq hF hi] at ht
  simp only [Function.comp_apply, ht, Option.getD_some]
  exact (hA.rep_levT hF hi hk).unique (hAg.tr k' hk).1

theorem enumeration_eq :
    enumeration (certificate hn gens words bv hbs) =
      (List.range (ordK LR k)).map (elemP n w LR TR k) := by
  have e : (List.finRange (certificate hn gens words bv hbs).baseCount).map
      (levelTransversals (certificate hn gens words bv hbs)) = trLists n w LR TR k := by
    apply List.ext_getElem (by simp [trLists, certificate])
    intro i h1 h2
    have hi : i < k := by simpa [trLists] using h2
    simp only [List.getElem_map, List.getElem_finRange, trLists, List.getElem_range]
    exact levelTransversals_eq hQ hn hbs hi
  rw [enumeration, e]
  apply List.ext_getElem (by simp [length_products_trLists])
  intro j h1 h2
  have hj : j < ordK LR k := by simpa using h2
  simp only [List.getElem_map, List.getElem_range]
  rw [elemP, elemRP_eq n w LR TR k j hj, mul_one]

theorem chainK_valid : ValidSchreier (certificate hn gens words bv hbs) :=
  (chainK_check hn hbs hQ).1

theorem elemP_mem (j : Nat) :
    elemP n w LR TR k j ∈ (certificate hn gens words bv hbs).originalSubgroup := by
  have hV := chainK_valid hQ hn hbs
  set Q := certificate hn gens words bv hbs
  have htr : ∀ i < k, ∀ k' < rcnt (LR i), trP n w LR TR i k' ∈ Q.originalSubgroup := by
    intro i hi k' hk'
    have hmem : trP n w LR TR i k' ∈ levelTransversals Q ⟨i, hi⟩ := by
      rw [levelTransversals_eq hQ hn hbs hi]
      exact List.mem_map.2 ⟨k', List.mem_range.2 hk', rfl⟩
    have := mem_levelSubgroup_of_mem_levelTransversals Q ⟨i, hi⟩ hmem
    rw [← Q.levelSubgroup_zero_eq_original hV]
    exact Q.levelSubgroup_antitone 0 i (Nat.zero_le _) this
  suffices ∀ d ≤ k, ∀ j acc, acc ∈ Q.originalSubgroup → elemRP n w LR TR d j acc ∈ Q.originalSubgroup
    from this k le_rfl j 1 (Subgroup.one_mem _)
  intro d
  induction d with
  | zero => intro _ j acc h; exact h
  | succ d ih =>
    intro hd j acc h
    rw [elemRP]
    exact ih (by omega) _ _ (Subgroup.mul_mem _ (htr d (by omega) _
      (Nat.mod_lt j (rcnt_pos hQ (by omega)))) h)

theorem forall₂_allTables_elem :
    List.Forall₂ (CFSG.Sporadic.Th.Rep n) (allTables (certificate hn gens words bv hbs))
      ((List.range (ordK LR k)).map (elemP n w LR TR k)).reverse := by
  rw [← enumeration_eq hQ hn hbs]
  exact forall₂_allTables (by have := chainK_n24 hQ; omega) _

theorem elemP_nodup : ((List.range (ordK LR k)).map (elemP n w LR TR k)).Nodup := by
  rw [← enumeration_eq hQ hn hbs]
  exact enumeration_nodup _ (chainK_valid hQ hn hbs)

theorem mem_elemP_iff (g : Equiv.Perm (Fin n)) :
    g ∈ (List.range (ordK LR k)).map (elemP n w LR TR k) ↔
      g ∈ (certificate hn gens words bv hbs).originalSubgroup := by
  rw [← enumeration_eq hQ hn hbs]
  exact mem_enumeration_iff _ (chainK_valid hQ hn hbs) g

end Chain

end CFSG.KS.SporSch.MOC

end
