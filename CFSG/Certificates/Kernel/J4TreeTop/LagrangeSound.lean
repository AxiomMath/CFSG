module

public import CFSG.Certificates.Kernel.J4TreeTop.SylowSound

public section

namespace CFSG.KC.J4TreeS

open CFSG.KC.J4Tree CFSG.KC.J4TreeN CFSG.KC.F2W CFSG.J4Tree.Native CFSG.ASVolI CFSG.Sporadic.J4
open CFSG.Sporadic.J4.QT

theorem coprime_foldr_mul (a : ℕ) :
    ∀ l : List ℕ, (∀ b ∈ l, Nat.gcd a b = 1) → Nat.Coprime a (l.foldr (· * ·) 1)
  | [], _ => Nat.coprime_one_right a
  | b :: l, h => by
    rw [List.foldr_cons]
    exact Nat.Coprime.mul_right (h b List.mem_cons_self)
      (coprime_foldr_mul a l fun b' hb' => h b' (List.mem_cons_of_mem _ hb'))

theorem foldr_lcm_eq_prod : ∀ l : List ℕ, coprimeAll l = true →
    l.foldr Nat.lcm 1 = l.foldr (· * ·) 1
  | [], _ => rfl
  | a :: l, h => by
    simp only [coprimeAll, Bool.and_eq_true, List.all_eq_true, beq_iff_eq] at h
    rw [List.foldr_cons, List.foldr_cons, foldr_lcm_eq_prod l h.2]
    exact Nat.Coprime.lcm_eq_mul (coprime_foldr_mul a l h.1)

theorem foldr_mul_odd : ∀ l : List ℕ, (∀ x ∈ l, x % 2 = 1) → l.foldr (· * ·) 1 % 2 = 1
  | [], _ => rfl
  | a :: l, h => by
    rw [List.foldr_cons, Nat.mul_mod, h a List.mem_cons_self,
      foldr_mul_odd l fun x hx => h x (List.mem_cons_of_mem _ hx)]


theorem topGlob_lagrange {T : Tabs} (hT : tabsOK T = true) (hq : Nat.beq (M QK QiK) oneK = true)
    {i : ℕ} {g : TGlob} (h : topGlobOK T i g = true)
    (hN : Nat.card ↥(Hj ⊓ Subgroup.centralizer (burnsideJ4NP_Rep g.k : Set J)) = treeOrd g.k) :
    Subgroup.closure {s | s ∈ topGs g} =
        Hj ⊓ Subgroup.centralizer (burnsideJ4NP_Rep g.k : Set J) ∧
      IsPGroup 2 ↥(Subgroup.closure {x | x ∈ g.cc.map burnsideJ4NP_treeElt}) ∧
      Nat.card ↥(Subgroup.closure {x | x ∈ g.cc.map burnsideJ4NP_treeElt}) = 2 ^ g.cc.length := by
  obtain ⟨-, -, -, -, -, -, hGC, hP0, h2n, hodd, hcop, hord⟩ := topGlob_sound hT hq h
  set C := Hj ⊓ Subgroup.centralizer (burnsideJ4NP_Rep g.k : Set J) with hC
  set L := Subgroup.closure {s | s ∈ topGs g} with hL
  set P := Subgroup.closure {x | x ∈ g.cc.map burnsideJ4NP_treeElt} with hP
  set prod := (g.odd.map Prod.fst).foldr (· * ·) 1 with hprod
  have hLC : L ≤ C := (Subgroup.closure_le C).mpr hGC
  have hPL : P ≤ L := Subgroup.closure_mono fun x hx => List.mem_append_right _ hx
  have hP2 : IsPGroup 2 ↥P :=
    (CFSG.Quasithin.J4Loc.isPGroup_P0 j4Facts).to_le ((Subgroup.closure_le P0).mpr hP0)
  have hprododd : prod % 2 = 1 := foldr_mul_odd _ fun x hx => by
    obtain ⟨o, ho, rfl⟩ := List.mem_map.mp hx
    exact (hodd o ho).2
  have hPcard : Nat.card P = 2 ^ g.cc.length := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨a, ha⟩ := IsPGroup.iff_card.mp hP2
    have hdvd : 2 ^ a ∣ 2 ^ g.cc.length * prod := by
      rw [← ha, ← hord, ← hN]
      exact Subgroup.card_dvd_of_le (hPL.trans hLC)
    have hcop2 : Nat.Coprime (2 ^ a) prod :=
      Nat.Coprime.pow_left a (Nat.coprime_two_left.mpr (Nat.odd_iff.mpr hprododd))
    have hle : a ≤ g.cc.length :=
      (Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp (hcop2.dvd_of_dvd_mul_right hdvd)
    refine le_antisymm ?_ h2n
    rw [ha]
    exact Nat.pow_le_pow_right (by norm_num) hle
  refine ⟨?_, hP2, hPcard⟩
  let Ps : List (Subgroup J) := P :: g.odd.map fun o =>
    Subgroup.closure {x | x ∈ o.2.1.map fun j => (topGs g).getD j 1}
  have hPs : ∀ Q ∈ Ps, Q ≤ L := by
    intro Q hQ
    rcases List.mem_cons.mp hQ with rfl | hQ
    · exact hPL
    · obtain ⟨o, -, rfl⟩ := List.mem_map.mp hQ
      rw [Subgroup.closure_le]
      intro x hx
      obtain ⟨j, -, rfl⟩ := List.mem_map.mp hx
      by_cases hj : j < (topGs g).length
      · exact Subgroup.subset_closure (getD_mem hj)
      · rw [List.getD_eq_default _ _ (by omega)]
        exact L.one_mem
  have hmap : Ps.map (fun Q : Subgroup J => Nat.card ↥Q) =
      2 ^ g.cc.length :: g.odd.map Prod.fst := by
    simp only [Ps, List.map_cons, List.map_map, hPcard]
    exact congrArg (2 ^ g.cc.length :: ·) (List.map_congr_left fun o ho => (hodd o ho).1)
  refine burnsideJ4NP_eq_of_le_of_lcm_dvd hLC Ps hPs ?_
  rw [hmap, foldr_lcm_eq_prod _ hcop, List.foldr_cons, hN, hord]

end CFSG.KC.J4TreeS
