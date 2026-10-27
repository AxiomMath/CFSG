module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch.KClassP
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.ModelOrb

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch

open Subgroup CFSG.Sporadic.Fi23 CFSG.EvenSporadicStandard.TwoFi22.FrameJ
open CFSG.EvenSporadicStandard.TwoFi22.DS81.Gen CFSG.Monster.B.Fischer
open CFSG.ComponentClassification.RankTwoSporadic.RootCensus (fixP)

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

section Classes

@[expose] def clsSet (i : Fin 6) : Set Cd := {y | ∃ s : Finset (Fin 23), InCls i s ∧ evC s = y}

theorem exists_clsSet {y : Cd} (hy : y ∈ E0) (hy1 : y ≠ 1) : ∃ i, y ∈ clsSet i := by
  obtain ⟨s, hs3, rfl⟩ := exists_evC hy
  have hs1 : 1 ≤ s.card := by
    rcases Nat.eq_zero_or_pos s.card with h | h
    · exact absurd (by rw [Finset.card_eq_zero.1 h, evC_empty]) hy1
    · exact h
  obtain ⟨i, hi⟩ := exists_cls hs1 hs3
  exact ⟨i, s, hi, rfl⟩

theorem clsSet_unique {i j : Fin 6} {y : Cd} (hi : y ∈ clsSet i) (hj : y ∈ clsSet j) : i = j := by
  obtain ⟨s, hs, rfl⟩ := hi
  obtain ⟨s', hs', hss⟩ := hj
  have h : s' = s := evC_inj (hs'.1.trans_le (clsCard_le j)) (hs.1.trans_le (clsCard_le i)) hss
  exact cls_unique hs (h ▸ hs')

theorem ncard_clsSet (i : Fin 6) : (clsSet i).ncard = ![1, 22, 22, 231, 231, 1540] i := by
  have himg : clsSet i = evC '' {t | InCls i t} := rfl
  rw [himg, Set.InjOn.ncard_image, Gen.ncard_cls]
  intro t ht t' ht' h
  exact evC_inj ((ht.1).trans_le (clsCard_le i)) ((ht'.1).trans_le (clsCard_le i)) h

theorem dCd_mem_clsSet : dCd ∈ clsSet 0 := by
  refine ⟨{0}, inCls_rep 0, Subtype.ext ?_⟩
  rw [evC_val, ev_singleton, fjPt_zero]
  rfl

theorem exists_of_mem_clsSet_three {y : Cd} (hy : y ∈ clsSet 3) :
    ∃ a b : Fin 23, a ≠ 0 ∧ b ≠ 0 ∧ a ≠ b ∧ y = fjQ a * fjQ b := by
  obtain ⟨s, hs, rfl⟩ := hy
  have hc : s.card = 2 := hs.1
  have h0 : (0 : Fin 23) ∉ s := fun h => by
    have := hs.2.1 h
    revert this
    decide
  obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.1 hc
  refine ⟨a, b, fun h => h0 (h ▸ by simp), fun h => h0 (h ▸ by simp), hab, ?_⟩
  have e1 : evC (insert a {b}) = fjQ a * evC {b} :=
    Subtype.ext (ev_insert (by simpa using hab))
  have e2 : evC {b} = fjQ b := Subtype.ext (ev_singleton b)
  rw [show ({a, b} : Finset (Fin 23)) = insert a {b} from rfl, e1, e2]

theorem exists_of_mem_clsSet_four {y : Cd} (hy : y ∈ clsSet 4) :
    ∃ a b : Fin 23, a ≠ 0 ∧ b ≠ 0 ∧ a ≠ b ∧ y = dCd * (fjQ a * fjQ b) := by
  obtain ⟨s, hs, rfl⟩ := hy
  have hc : s.card = 3 := hs.1
  have h0 : (0 : Fin 23) ∈ s := hs.2.2 (by decide)
  have hc' : (s.erase 0).card = 2 := by
    have := Finset.card_erase_add_one h0
    omega
  obtain ⟨a, b, hab, he⟩ := Finset.card_eq_two.1 hc'
  have ha : a ∈ s.erase 0 := by rw [he]; simp
  have hb : b ∈ s.erase 0 := by rw [he]; simp
  have ha0 : a ≠ 0 := (Finset.mem_erase.1 ha).1
  have hb0 : b ≠ 0 := (Finset.mem_erase.1 hb).1
  refine ⟨a, b, ha0, hb0, hab, ?_⟩
  have hs' : s = insert 0 {a, b} := by rw [← he, Finset.insert_erase h0]
  have e0 : (0 : Fin 23) ∉ ({a, b} : Finset (Fin 23)) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨fun h => ha0 h.symm, fun h => hb0 h.symm⟩
  have e1 : evC (insert 0 {a, b}) = fjQ 0 * evC {a, b} := Subtype.ext (ev_insert e0)
  have e2 : evC {a, b} = fjQ a * fjQ b := by
    have e3 : evC (insert a {b}) = fjQ a * evC {b} :=
      Subtype.ext (ev_insert (by simpa using hab))
    have e4 : evC {b} = fjQ b := Subtype.ext (ev_singleton b)
    rw [show ({a, b} : Finset (Fin 23)) = insert a {b} from rfl, e3, e4]
  have e5 : fjQ 0 = dCd := Subtype.ext fjPt_zero
  rw [hs', e1, e2, e5]

end Classes

private theorem sum_aux {p0 p1 p2 p3 p4 p5 : Prop} [Decidable p0] [Decidable p1] [Decidable p2]
    [Decidable p3] [Decidable p4] [Decidable p5] (h0 : p0)
    (h : (if p0 then 1 else 0) + (if p1 then 22 else 0) + (if p2 then 22 else 0) +
      (if p3 then 231 else 0) + (if p4 then 231 else 0) + (if p5 then 1540 else 0) = 276) :
    p1 ∧ p2 := by
  by_cases h1 : p1 <;> by_cases h2 : p2 <;> by_cases h3 : p3 <;> by_cases h4 : p4 <;>
    by_cases h5 : p5 <;> simp_all

section Orbits

theorem clsSet_conj {i : Fin 6} {y y' : Cd} (hy : y ∈ clsSet i) (hy' : y' ∈ clsSet i) :
    ∃ n ∈ normalizer (E0 : Set Cd), n * y * n⁻¹ = y' := by
  have h1 : y ∈ {y : Cd | ∃ n ∈ normalizer (E0 : Set Cd), n * evC (clsRep i) * n⁻¹ = y} := by
    rw [orbit_clsRep]
    exact hy
  have h2 : y' ∈ {y : Cd | ∃ n ∈ normalizer (E0 : Set Cd), n * evC (clsRep i) * n⁻¹ = y} := by
    rw [orbit_clsRep]
    exact hy'
  obtain ⟨n1, hn1, rfl⟩ := h1
  obtain ⟨n2, hn2, rfl⟩ := h2
  refine ⟨n2 * n1⁻¹, mul_mem hn2 (inv_mem hn1), ?_⟩
  group

private theorem dCd_comm (n : Cd) : n * dCd = dCd * n := by
  have h : dCd ∈ center ↥Cd := by
    rw [center_C]
    exact Subgroup.mem_zpowers _
  exact Subgroup.mem_center_iff.1 h n

theorem exists_pair_of_stable {T : Set Cd} (hTE : ∀ y ∈ T, y ∈ E0 ∧ y ≠ 1)
    (hTN : ∀ n ∈ normalizer (E0 : Set Cd), ∀ y ∈ T, n * y * n⁻¹ ∈ T)
    (hd : dCd ∈ T) (hcard : T.ncard = 276) {y : Cd} (hyE : y ∈ E0) (hy1 : y ≠ 1) (hyT : y ∉ T)
    (hdy : dCd * y ∈ T) :
    ∃ a b : Fin 23, a ≠ 0 ∧ b ≠ 0 ∧ a ≠ b ∧ (y = fjQ a * fjQ b ∨ y = dCd * (fjQ a * fjQ b)) := by
  classical
  have hTfin : T.Finite := Set.finite_of_ncard_ne_zero (by omega)
  have hA_fin : ∀ i, (T ∩ clsSet i).Finite := fun i => hTfin.subset Set.inter_subset_left
  have hA_disj : Pairwise (Function.onFun Disjoint fun i => T ∩ clsSet i) := by
    intro i j hij
    exact Set.disjoint_left.2 fun y hyi hyj => hij (clsSet_unique hyi.2 hyj.2)
  have hT_eq : T = ⋃ i, T ∩ clsSet i := by
    ext y
    constructor
    · intro hy
      obtain ⟨i, hi⟩ := exists_clsSet (hTE y hy).1 (hTE y hy).2
      exact Set.mem_iUnion.2 ⟨i, hy, hi⟩
    · intro hy
      obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hy
      exact hi.1
  have hsum : T.ncard = ∑ i, (T ∩ clsSet i).ncard := by
    calc T.ncard = (⋃ i, T ∩ clsSet i).ncard := congrArg Set.ncard hT_eq
      _ = ∑ᶠ i, (T ∩ clsSet i).ncard := Set.ncard_iUnion_of_finite hA_fin hA_disj
      _ = ∑ i, (T ∩ clsSet i).ncard := finsum_eq_sum_of_fintype _
  have hsat : ∀ i, (∃ y' ∈ T, y' ∈ clsSet i) → clsSet i ⊆ T := by
    rintro i ⟨y', hy'T, hy'i⟩ y'' hy''
    obtain ⟨n, hn, rfl⟩ := clsSet_conj hy'i hy''
    exact hTN n hn y' hy'T
  have hAi : ∀ i, (T ∩ clsSet i).ncard =
      if (∃ y' ∈ T, y' ∈ clsSet i) then ![1, 22, 22, 231, 231, 1540] i else 0 := by
    intro i
    by_cases h : ∃ y' ∈ T, y' ∈ clsSet i
    · rw [if_pos h, ← ncard_clsSet i]
      congr 1
      exact Set.inter_eq_right.2 (hsat i h)
    · rw [if_neg h]
      have : T ∩ clsSet i = ∅ := Set.eq_empty_of_forall_notMem fun y hy => h ⟨y, hy.1, hy.2⟩
      rw [this, Set.ncard_empty]
  have hsum' : (if (∃ y' ∈ T, y' ∈ clsSet 0) then 1 else 0) +
      (if (∃ y' ∈ T, y' ∈ clsSet 1) then 22 else 0) +
      (if (∃ y' ∈ T, y' ∈ clsSet 2) then 22 else 0) +
      (if (∃ y' ∈ T, y' ∈ clsSet 3) then 231 else 0) +
      (if (∃ y' ∈ T, y' ∈ clsSet 4) then 231 else 0) +
      (if (∃ y' ∈ T, y' ∈ clsSet 5) then 1540 else 0) = 276 := by
    rw [← hcard, hsum, Fin.sum_univ_six]
    simp only [hAi]
    rfl
  obtain ⟨h1, h2⟩ := sum_aux ⟨dCd, hd, dCd_mem_clsSet⟩ hsum'
  obtain ⟨j, hyj⟩ := exists_clsSet hyE hy1
  have hj : ¬ ∃ y' ∈ T, y' ∈ clsSet j := fun h => hyT (hsat j h hyj)
  have hδ : ∀ y' ∈ clsSet j, dCd * y' ∈ T := by
    intro y' hy'
    obtain ⟨n, hn, rfl⟩ := clsSet_conj hyj hy'
    have e : dCd * (n * y * n⁻¹) = n * (dCd * y) * n⁻¹ := by
      calc dCd * (n * y * n⁻¹) = (dCd * n) * y * n⁻¹ := by group
        _ = (n * dCd) * y * n⁻¹ := by rw [dCd_comm n]
        _ = n * (dCd * y) * n⁻¹ := by group
    rw [e]
    exact hTN n hn _ hdy
  have hle : (clsSet j).ncard ≤ 276 := by
    have hsub : (fun y' => dCd * y') '' clsSet j ⊆ T := by
      rintro _ ⟨y', hy', rfl⟩
      exact hδ y' hy'
    rw [← hcard, ← Set.ncard_image_of_injective (clsSet j) (mul_right_injective dCd)]
    exact Set.ncard_le_ncard hsub hTfin
  have hj3 : j = 3 ∨ j = 4 := by
    fin_cases j
    · exact absurd ⟨dCd, hd, dCd_mem_clsSet⟩ hj
    · exact absurd h1 hj
    · exact absurd h2 hj
    · exact Or.inl rfl
    · exact Or.inr rfl
    · rw [ncard_clsSet] at hle
      exact absurd hle (by decide)
  rcases hj3 with rfl | rfl
  · obtain ⟨a, b, ha, hb, hab, rfl⟩ := exists_of_mem_clsSet_three hyj
    exact ⟨a, b, ha, hb, hab, Or.inl rfl⟩
  · obtain ⟨a, b, ha, hb, hab, rfl⟩ := exists_of_mem_clsSet_four hyj
    exact ⟨a, b, ha, hb, hab, Or.inr rfl⟩

end Orbits

section Fixed

theorem piC_fjQ_mem {a : Fin 23} (ha : a ≠ 0) : piC (fjQ a) ∈ CFSG.Sporadic.Fi22.D := by
  rw [fjQ_eq_ofStar ha]
  exact piC_ofStar_mem_D _

theorem piC_fjQ_ne {a b : Fin 23} (ha : a ≠ 0) (hb : b ≠ 0) (hab : a ≠ b) :
    piC (fjQ a) ≠ piC (fjQ b) := by
  intro h
  have h' : piC (ofStar ⟨fjPt a, fjPt_star ha⟩) = piC (ofStar ⟨fjPt b, fjPt_star hb⟩) := by
    rw [← fjQ_eq_ofStar ha, ← fjQ_eq_ofStar hb]
    exact h
  exact hab (fjPt_injective (congrArg Subtype.val (ofStar_injective_of_piC h')))

theorem fixP_piP_fjQ_mul {a b : Fin 23} (ha : a ≠ 0) (hb : b ≠ 0) (hab : a ≠ b) :
    fixP ((piP (fjQ a * fjQ b) : fi22P) : Equiv.Perm (Fin 3510)) = 182 := by
  have hc : fjQ a * fjQ b = fjQ b * fjQ a := Subtype.ext (fjPt_comm a b)
  have hc' : piC (fjQ a) * piC (fjQ b) = piC (fjQ b) * piC (fjQ a) := by
    rw [← map_mul, ← map_mul, hc]
  show fixP ((fiJP (piC (fjQ a * fjQ b)) : fi22P) : Equiv.Perm (Fin 3510)) = 182
  rw [map_mul]
  exact fixP_fiJP_mul_of_comm (piC_fjQ_mem ha) (piC_fjQ_mem hb) (piC_fjQ_ne ha hb hab) hc'

theorem fixP_piP_of_stable {T : Set Cd} (hTE : ∀ y ∈ T, y ∈ E0 ∧ y ≠ 1)
    (hTN : ∀ n ∈ normalizer (E0 : Set Cd), ∀ y ∈ T, n * y * n⁻¹ ∈ T)
    (hd : dCd ∈ T) (hcard : T.ncard = 276) {y : Cd} (hyE : y ∈ E0) (hy1 : y ≠ 1) (hyT : y ∉ T)
    (hdy : dCd * y ∈ T) :
    fixP ((piP y : fi22P) : Equiv.Perm (Fin 3510)) = 182 := by
  obtain ⟨a, b, ha, hb, hab, h | h⟩ := exists_pair_of_stable hTE hTN hd hcard hyE hy1 hyT hdy
  · rw [h]
    exact fixP_piP_fjQ_mul ha hb hab
  · have hd1 : (piP dCd : fi22P) = 1 := by
      show (fiJP (piC dCd) : fi22P) = 1
      rw [piC_dCd, map_one]
    rw [h, map_mul, hd1, one_mul]
    exact fixP_piP_fjQ_mul ha hb hab

end Fixed

end CFSG.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch
