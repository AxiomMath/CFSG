module

public import Certificates.Certificate36401
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Group

public section

namespace CFSG.OddStandard.AltStdSmall4.ModT10

open T10

theorem inQ_iff (x : T10) : inQ x = true ↔ x ∈ Qm := by
  simp only [inQ, Bool.and_eq_true, beq_iff_eq]
  exact ⟨fun ⟨⟨⟨hs, ha⟩, hb⟩, hc⟩ => ⟨hs, ha, hb, hc⟩, fun ⟨hs, ha, hb, hc⟩ => ⟨⟨⟨hs, ha⟩, hb⟩, hc⟩⟩

theorem inM_iff (x : T10) : inM x = true ↔ x ∈ Mm := by
  simp only [inM, beq_iff_eq]
  rfl

theorem isInv_iff (x : T10) : isInv x = true ↔ x * x = 1 ∧ x ≠ 1 := by
  simp [isInv]

theorem commB_iff (g x : T10) : commB g x = true ↔ g ∈ Subgroup.centralizer ({x} : Set T10) := by
  rw [Subgroup.mem_centralizer_singleton_iff]
  simp [commB]

theorem natCard_subtype (p : T10 → Bool) :
    Nat.card {x : T10 // p x = true} = ((allL ()).filter p).length := by
  rw [Nat.subtype_card ⟨↑((allL ()).filter p), Multiset.coe_nodup.2 (nodup_allL.filter p)⟩
    (fun x => by simp only [Finset.mem_mk, Multiset.mem_coe, List.mem_filter, mem_allL, true_and])]
  rfl

theorem natCard_subgroup (H : Subgroup T10) (p : T10 → Bool) (h : ∀ x, x ∈ H ↔ p x = true) :
    Nat.card H = ((allL ()).filter p).length := by
  rw [← natCard_subtype p]
  exact Nat.card_congr (Equiv.subtypeEquivRight h)

theorem natCard_subgroup_eq_succ (H : Subgroup T10) (p : T10 → Bool)
    (h : ∀ x, x ≠ 1 → (x ∈ H ↔ p x = true)) (h1 : p 1 = false) :
    Nat.card H = ((allL ()).filter p).length + 1 := by
  classical
  let S : Finset T10 := ⟨↑((allL ()).filter p), Multiset.coe_nodup.2 (nodup_allL.filter p)⟩
  have hS : ∀ x, x ∈ S ↔ p x = true := fun x => by
    simp only [S, Finset.mem_mk, Multiset.mem_coe, List.mem_filter, mem_allL, true_and]
  have h1S : (1 : T10) ∉ S := by rw [hS, h1]; exact Bool.false_ne_true
  have hH : ∀ x, x ∈ insert 1 S ↔ x ∈ H := fun x => by
    rw [Finset.mem_insert, hS]
    by_cases hx : x = 1
    · simp only [hx, true_or, H.one_mem]
    · simp only [hx, false_or, h x hx]
  rw [show Nat.card H = (insert 1 S).card from Nat.subtype_card _ hH,
    Finset.card_insert_of_notMem h1S]
  rfl

theorem natCard_invol (H : Subgroup T10) (p : T10 → Bool) (h : ∀ x, x ∈ H ↔ p x = true) :
    Nat.card {y : H // y * y = 1 ∧ y ≠ 1} = ((allL ()).filter fun g => p g && isInv g).length := by
  rw [← natCard_subtype]
  refine Nat.card_congr ((Equiv.subtypeEquivRight fun y => ?_).trans
    ((Equiv.subtypeSubtypeEquivSubtypeInter (· ∈ H) fun g => g * g = 1 ∧ g ≠ 1).trans
      (Equiv.subtypeEquivRight fun g => ?_)))
  · simp only [Subtype.ext_iff, Subgroup.coe_mul, Subgroup.coe_one, ne_eq]
  · rw [Bool.and_eq_true, ← h g, isInv_iff]

theorem natCard_invol_congr {H K : Subgroup T10} (e : H ≃* K) :
    Nat.card {y : H // y * y = 1 ∧ y ≠ 1} = Nat.card {y : K // y * y = 1 ∧ y ≠ 1} :=
  Nat.card_congr (e.toEquiv.subtypeEquiv fun y => by
    show y * y = 1 ∧ y ≠ 1 ↔ e y * e y = 1 ∧ e y ≠ 1
    rw [← map_mul, Ne, MulEquiv.map_eq_one_iff, Ne, MulEquiv.map_eq_one_iff])

@[expose] def vec (x : T10) : Fin 6 → ZMod 2 := ![x.x0, x.x1, x.x2, x.x3, x.x4, x.x5]

@[expose] def ofVec (v : Fin 6 → ZMod 2) : T10 := ⟨v 0, v 1, v 2, v 3, v 4, v 5, 0, 0, 0, 0⟩

theorem ofVec_mem_Qm (v : Fin 6 → ZMod 2) : ofVec v ∈ Qm := ⟨rfl, rfl, rfl, rfl⟩

@[expose] def QmEquiv : Qm ≃ (Fin 6 → ZMod 2) where
  toFun x := vec x
  invFun v := ⟨ofVec v, ofVec_mem_Qm v⟩
  left_inv x := by
    obtain ⟨x, hs, ha, hb, hc⟩ := x
    ext <;> simp [vec, ofVec, hs, ha, hb, hc]
  right_inv v := by
    funext i
    fin_cases i <;> rfl

theorem card_Qm : Nat.card Qm = 64 := by
  rw [Nat.card_congr QmEquiv, Nat.card_fun, Nat.card_zmod, Nat.card_eq_fintype_card,
    Fintype.card_fin]
  rfl

theorem Qm_le_Mm : Qm ≤ Mm := fun _ hx => hx.1

theorem filter_mem_cliques (cm : ℕ → ℕ → Bool) (p : ℕ → Bool) :
    ∀ l : List ℕ, (∀ i ∈ l.filter p, ∀ j ∈ l.filter p, cm i j = true) →
      l.filter p ∈ cliques cm l
  | [], _ => by simp [cliques]
  | k :: ks, h => by
    have hsub : ∀ i ∈ ks.filter p, i ∈ (k :: ks).filter p := fun i hi => by
      rw [List.mem_filter] at hi ⊢
      exact ⟨List.mem_cons_of_mem k hi.1, hi.2⟩
    have ih := filter_mem_cliques cm p ks fun i hi j hj => h i (hsub i hi) j (hsub j hj)
    simp only [cliques, List.mem_append, List.mem_map, List.mem_filter]
    by_cases hk : p k = true
    · right
      have hkk : k ∈ (k :: ks).filter p := List.mem_filter.2 ⟨List.mem_cons_self, hk⟩
      refine ⟨ks.filter p, ⟨ih, ?_⟩, (List.filter_cons_of_pos hk).symm⟩
      rw [Bool.and_eq_true, List.all_eq_true]
      exact ⟨h k hkk k hkk, fun j hj => h k hkk j (hsub j hj)⟩
    · left
      rw [List.filter_cons_of_neg hk]
      exact ih

theorem cmOf_commTab {P : List (T10 × ℕ)} {i j : ℕ} (hi : i < 25) (hj : j < 25) :
    cmOf (commTab P) i j = classesCommute P i j := by
  simp only [cmOf, commTab, Array.getElem?_ofFn, hi, hj, dite_true, Option.getD_some]

theorem map_fst_filter_pairs (L : List T10) (f : T10 → ℕ) (q : T10 × ℕ → Bool) :
    ((L.map fun x => (x, f x)).filter q).map Prod.fst = L.filter fun x => q (x, f x) := by
  induction L with
  | nil => rfl
  | cons y L ih => by_cases h : q (y, f y) <;> simp [List.filter_cons, h, ih]

theorem pairsT_eq :
    pairsT () = ((allL ()).filter isInv).map fun x => (x, clsIdx (orbitsT ()) x) :=
  rfl

theorem orbitsT_eq : orbitsT () = (reps ()).map (orbitOf (allL ())) := rfl

theorem length_reps : (reps ()).length = 25 := rfl

attribute [local irreducible] allL reps orbitsT pairsT

theorem length_orbitsT : (orbitsT ()).length = 25 := by
  rw [orbitsT_eq, List.length_map, length_reps]

theorem mem_orbitOf {L : List T10} {r x : T10} (h : x ∈ orbitOf L r) : ∃ g, g * r * g⁻¹ = x := by
  rw [orbitOf, List.mem_dedup, List.mem_map] at h
  obtain ⟨g, -, hg⟩ := h
  exact ⟨g, hg⟩

theorem mem_orbitsT_clsIdx {x : T10} (h : clsIdx (orbitsT ()) x < (orbitsT ()).length) :
    x ∈ (orbitsT ())[clsIdx (orbitsT ()) x] := by
  have := List.findIdx_getElem (p := fun o : List T10 => o.contains x) (w := h)
  simpa [clsIdx] using this

theorem conj_of_mem_orbitsT {i : ℕ} (hi : i < (orbitsT ()).length) {x y : T10}
    (hx : x ∈ (orbitsT ())[i]) (hy : y ∈ (orbitsT ())[i]) : ∃ g, g * x * g⁻¹ = y := by
  simp only [orbitsT_eq, List.getElem_map] at hx hy
  obtain ⟨g, rfl⟩ := mem_orbitOf hx
  obtain ⟨h, rfl⟩ := mem_orbitOf hy
  exact ⟨h * g⁻¹, by group⟩

theorem conj_of_clsIdx_eq {x y : T10} (hx : clsIdx (orbitsT ()) x < 25)
    (hxy : clsIdx (orbitsT ()) y = clsIdx (orbitsT ()) x) : ∃ g, g * x * g⁻¹ = y := by
  have hx' : clsIdx (orbitsT ()) x < (orbitsT ()).length := by rw [length_orbitsT]; exact hx
  have hy' : clsIdx (orbitsT ()) y < (orbitsT ()).length := by rw [hxy]; exact hx'
  have hmx := mem_orbitsT_clsIdx hx'
  have hmy := mem_orbitsT_clsIdx hy'
  simp only [hxy] at hmy
  exact conj_of_mem_orbitsT hx' hmx hmy

theorem checkA_spec :
    (∀ x, isInv x = true → clsIdx (orbitsT ()) x < 25) ∧
      ∀ S ∈ cliques (cmOf (commTab (pairsT ()))) (List.range 25), leafOK (pairsT ()) S = true := by
  have hA : ((pairsT ()).all fun p => decide (p.2 < 25)) = true ∧
      (cliques (cmOf (commTab (pairsT ()))) (List.range 25)).all (leafOK (pairsT ())) = true :=
    Bool.and_eq_true_iff.1 Certificates.certificate36401.1
  rw [List.all_eq_true, List.all_eq_true] at hA
  refine ⟨fun x hx => ?_, hA.2⟩
  have hmem : (x, clsIdx (orbitsT ()) x) ∈ pairsT () := by
    rw [pairsT_eq]
    exact List.mem_map_of_mem (List.mem_filter.2 ⟨mem_allL x, hx⟩)
  have h := hA.1 _ hmem
  simp only [decide_eq_true_eq] at h
  exact h

theorem leafOK_iff (P : List (T10 × ℕ)) (S : List ℕ) : leafOK P S = true ↔
    ((P.filter fun p => S.contains p.2).map Prod.fst).length ≠ 63 ∨
      ((P.filter fun p => S.contains p.2).map Prod.fst).all inQ = true ∨
      (((P.filter fun p => S.contains p.2).map Prod.fst).filter fun g => commB g tm).length =
        15 := by
  simp only [leafOK, Bool.or_eq_true, bne_iff_ne, ne_eq, beq_iff_eq, or_assoc]

theorem normal_e64 :
    ∀ N : Subgroup T10, N.Normal → (∀ x ∈ N, x ^ 2 = 1) → Nat.card N = 64 → N ≠ Qm →
      Nat.card (N ⊓ Subgroup.centralizer {tm} : Subgroup T10) = 16 := by
  classical
  intro N hN h2 hc hne
  obtain ⟨hcls, hleaf⟩ := checkA_spec
  have hsq : ∀ x ∈ N, x * x = 1 := fun x hx => by rw [← pow_two]; exact h2 x hx
  have hinv : ∀ x ∈ N, x⁻¹ = x := fun x hx => inv_eq_of_mul_eq_one_right (hsq x hx)
  have hinvN : ∀ x ∈ N, x ≠ 1 → isInv x = true := fun x hx h1 =>
    (isInv_iff x).2 ⟨hsq x hx, h1⟩
  have hcomm : ∀ x ∈ N, ∀ y ∈ N, x * y = y * x := fun x hx y hy => by
    have h := hinv (x * y) (N.mul_mem hx hy)
    rw [mul_inv_rev, hinv x hx, hinv y hy] at h
    exact h.symm
  obtain ⟨pN, hpN⟩ : ∃ pN : ℕ → Bool, ∀ i, pN i = true ↔
      ∃ y ∈ N, isInv y = true ∧ clsIdx (orbitsT ()) y = i :=
    ⟨fun i => decide (∃ y ∈ N, isInv y = true ∧ clsIdx (orbitsT ()) y = i),
      fun i => decide_eq_true_iff⟩
  obtain ⟨S, hSdef⟩ : ∃ S : List ℕ, S = (List.range 25).filter pN := ⟨_, rfl⟩
  have hmemS : ∀ i, i ∈ S ↔ i < 25 ∧ pN i = true := fun i => by
    rw [hSdef, List.mem_filter, List.mem_range]
  have memS : ∀ x, isInv x = true → (x ∈ N ↔ clsIdx (orbitsT ()) x ∈ S) := by
    intro x hx
    rw [hmemS, hpN]
    constructor
    · intro hxN
      exact ⟨hcls x hx, x, hxN, hx, rfl⟩
    · rintro ⟨-, y, hyN, hy, hyx⟩
      obtain ⟨g, rfl⟩ := conj_of_clsIdx_eq (hcls y hy) hyx.symm
      exact hN.conj_mem y hyN g
  have hmembers : ∀ i, ∀ x ∈ members (pairsT ()) i,
      isInv x = true ∧ clsIdx (orbitsT ()) x = i := by
    intro i x hx
    rw [members, pairsT_eq, map_fst_filter_pairs, List.mem_filter, List.mem_filter] at hx
    simp only [beq_iff_eq] at hx
    exact ⟨hx.1.2, hx.2⟩
  have hclique : ∀ i ∈ S, ∀ j ∈ S, cmOf (commTab (pairsT ())) i j = true := by
    intro i hi j hj
    rw [cmOf_commTab ((hmemS i).1 hi).1 ((hmemS j).1 hj).1, classesCommute, List.all_eq_true]
    intro x hx
    rw [List.all_eq_true]
    intro y hy
    obtain ⟨hxi, hxc⟩ := hmembers i x hx
    obtain ⟨hyi, hyc⟩ := hmembers j y hy
    have hxN : x ∈ N := (memS x hxi).2 (hxc ▸ hi)
    have hyN : y ∈ N := (memS y hyi).2 (hyc ▸ hj)
    rw [commB, beq_iff_eq]
    exact hcomm x hxN y hyN
  have hS := hleaf S (hSdef ▸ filter_mem_cliques _ pN (List.range 25) (hSdef ▸ hclique))
  have hU : ((pairsT ()).filter fun p => S.contains p.2).map Prod.fst =
      (allL ()).filter fun x => isInv x && decide (x ∈ N) := by
    rw [pairsT_eq, map_fst_filter_pairs, List.filter_filter]
    refine List.filter_congr fun x _ => ?_
    by_cases hx : isInv x = true
    · have h := (memS x hx).symm
      simp only [hx, Bool.and_true, Bool.true_and]
      rw [Bool.eq_iff_iff, List.contains_iff_mem, decide_eq_true_iff]
      exact h
    · simp only [Bool.eq_false_iff.2 hx, Bool.and_false, Bool.false_and]
  rw [leafOK_iff, hU] at hS
  have hcard : Nat.card N = ((allL ()).filter fun x => isInv x && decide (x ∈ N)).length + 1 :=
    natCard_subgroup_eq_succ N _ (fun x hx => by
      rw [Bool.and_eq_true, decide_eq_true_iff]
      exact ⟨fun hxN => ⟨hinvN x hxN hx, hxN⟩, fun h => h.2⟩)
      (by rw [Bool.and_eq_false_imp]; intro h; exact absurd rfl ((isInv_iff 1).1 h).2)
  rcases hS with hS | hS | hS
  · exact absurd (by omega) hS
  · rw [List.all_eq_true] at hS
    refine absurd (Subgroup.eq_of_le_of_card_ge (fun x hxN => ?_) (by rw [card_Qm, hc])) hne
    by_cases h1 : x = 1
    · rw [h1]; exact Qm.one_mem
    · refine (inQ_iff x).1 (hS x (List.mem_filter.2 ⟨mem_allL x, ?_⟩))
      rw [Bool.and_eq_true, decide_eq_true_iff]
      exact ⟨hinvN x hxN h1, hxN⟩
  · have hlist : ((allL ()).filter fun x => isInv x && decide (x ∈ N) && commB x tm) =
        ((allL ()).filter fun x => isInv x && decide (x ∈ N)).filter fun g => commB g tm := by
      rw [List.filter_filter]
      refine List.filter_congr fun x _ => ?_
      rw [Bool.and_comm]
    have hmemC : ∀ x, x ≠ 1 → (x ∈ N ⊓ Subgroup.centralizer {tm} ↔
        (isInv x && decide (x ∈ N) && commB x tm) = true) := fun x hx => by
      rw [Subgroup.mem_inf, ← commB_iff, Bool.and_eq_true, Bool.and_eq_true, decide_eq_true_iff]
      exact ⟨fun h => ⟨⟨hinvN x h.1 hx, h.1⟩, h.2⟩, fun h => ⟨h.1.2, h.2⟩⟩
    have hone : (isInv 1 && decide ((1 : T10) ∈ N) && commB 1 tm) = false := by
      rw [Bool.and_eq_false_imp]
      intro h
      rw [Bool.and_eq_true] at h
      exact absurd rfl ((isInv_iff 1).1 h.1).2
    rw [natCard_subgroup_eq_succ _ _ hmemC hone, hlist, hS]

theorem mem_Mm_of_card :
    ∀ x : T10, x ∉ Qm → x ^ 2 = 1 →
      Nat.card (Qm ⊓ Subgroup.centralizer {x} : Subgroup T10) = 16 → x ∈ Mm := by
  intro x hxQ h2 hc
  have hB : (allL ()).all (fun x => inQ x || !(x * x == 1) || inM x ||
      ((allL ()).filter fun g => inQ g && commB g x).length != 16) = true :=
    Certificates.certificate36401.2.1
  rw [List.all_eq_true] at hB
  have hx := hB x (mem_allL x)
  rw [natCard_subgroup _ (fun g => inQ g && commB g x) (fun g => by
    rw [Subgroup.mem_inf, Bool.and_eq_true, inQ_iff, commB_iff])] at hc
  rw [pow_two] at h2
  rw [← inM_iff]
  rw [Bool.eq_false_iff.2 fun h => hxQ ((inQ_iff x).1 h), show (x * x == 1) = true from
    beq_iff_eq.2 h2, hc] at hx
  simpa using hx

theorem conj_cent :
    ∀ x ∈ Mm, x ∉ Qm → orderOf x = 2 →
      (Nat.card (Subgroup.centralizer {x} : Subgroup T10) = 2 ^ 8 ∨
        Nonempty (Subgroup.centralizer ({x} : Set T10) ≃*
          Subgroup.centralizer ({tm} : Set T10))) →
      ∃ g : T10, g * x * g⁻¹ ∈ Subgroup.centralizer ({tm} : Set T10) := by
  intro x hxM hxQ ho h
  have hC := Certificates.certificate36401.2.2
  simp only [t10CheckC, Bool.and_eq_true, List.all_eq_true] at hC
  have hx := hC.2 x (mem_allL x)
  have hxx : x * x = 1 := by rw [← pow_two, ← ho]; exact pow_orderOf_eq_one x
  have hx1 : x ≠ 1 := by rintro rfl; rw [orderOf_one] at ho; exact absurd ho (by decide)
  have hcx := natCard_subgroup (Subgroup.centralizer ({x} : Set T10)) (fun g => commB g x)
    (fun g => (commB_iff g x).symm)
  have hix := natCard_invol (Subgroup.centralizer ({x} : Set T10)) (fun g => commB g x)
    (fun g => (commB_iff g x).symm)
  have hcT := natCard_subgroup (Subgroup.centralizer ({tm} : Set T10)) (fun g => commB g tm)
    (fun g => (commB_iff g tm).symm)
  have hiT := natCard_invol (Subgroup.centralizer ({tm} : Set T10)) (fun g => commB g tm)
    (fun g => (commB_iff g tm).symm)
  have hsel : ((allL ()).filter fun g => commB g x).length = 256 ∨
      (((allL ()).filter fun g => commB g x).length =
          ((allL ()).filter fun g => commB g tm).length ∧
        ((allL ()).filter fun g => commB g x && isInv g).length =
          ((allL ()).filter fun g => commB g tm && isInv g).length) := by
    rcases h with h | hne
    · left; rw [← hcx, h]; rfl
    · obtain ⟨e⟩ := hne
      right
      exact ⟨by rw [← hcx, ← hcT]; exact Nat.card_congr e.toEquiv,
        by rw [← hix, ← hiT]; exact natCard_invol_congr e⟩
  rw [(inM_iff x).2 hxM, Bool.eq_false_iff.2 fun h => hxQ ((inQ_iff x).1 h),
    (isInv_iff x).2 ⟨hxx, hx1⟩] at hx
  simp only [Bool.not_true, Bool.false_or, Bool.or_eq_true, Bool.not_eq_true',
    Bool.or_eq_false_iff, beq_eq_false_iff_ne, ne_eq, Bool.and_eq_false_imp, beq_iff_eq] at hx
  rcases hx with hx | hx
  · exfalso
    rcases hsel with hs | ⟨hs1, hs2⟩
    · exact hx.1 hs
    · exact hx.2 hs1 hs2
  · obtain ⟨g, -, hg⟩ := List.any_eq_true.1 hx
    exact ⟨g, (commB_iff _ tm).1 hg⟩

end CFSG.OddStandard.AltStdSmall4.ModT10
