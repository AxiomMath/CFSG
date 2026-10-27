module

public import Certificates.Certificate2003

public section

namespace CFSG.Literature.GL52

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier
  CFSG.Sporadic.Schreier.Native

theorem card_filter_fin (q : Fin 31 → Prop) [DecidablePred q] :
    (Finset.univ.filter q).card = (List.finRange 31).countP (fun i => decide (q i)) := by
  rw [Fin.univ_def, List.countP_eq_length_filter]
  rfl

theorem fpT_eq_card (T : Table) (π : Equiv.Perm (Fin 31)) (h : Rep 31 T π) :
    fpT T = (Finset.univ.filter fun i : Fin 31 => π i = i).card := by
  rw [card_filter_fin, fpT, ← List.map_coe_finRange_eq_range, List.countP_map]
  congr 1
  funext i
  simp only [Function.comp_apply]
  rw [h i i.2, idx_of_lt _ i.2]
  simp only [Fin.ext_iff]
  exact Bool.eq_iff_iff.2 (by rw [beq_iff_eq, decide_eq_true_iff]; rfl)

theorem ordTest_iff' {T : Table} {π : Equiv.Perm (Fin 31)} (h : Rep 31 T π) {m : ℕ}
    (hm : 0 < m) : ordTest 31 m T = true ↔ orderOf π = m :=
  ordTest_iff perm_faithful h hm

theorem tblEq_iff_eq' {S T : Table} {π σ : Equiv.Perm (Fin 31)} (hS : Rep 31 S π)
    (hT : Rep 31 T σ) : tblEq 31 S T = true ↔ π = σ := by
  rw [tblEq_iff]
  constructor
  · intro he
    refine Equiv.ext fun i => Fin.ext ?_
    have h1 := hS i.val i.isLt
    have h2 := hT i.val i.isLt
    rw [idx_of_lt _ i.isLt] at h1 h2
    have h3 := he i.val i.isLt
    rw [h1, h2] at h3
    exact h3
  · rintro rfl i hi
    rw [hS i hi, hT i hi]

theorem cmtT_iff {T X : Table} {π ξ : Equiv.Perm (Fin 31)} (hT : Rep 31 T π) (hX : Rep 31 X ξ) :
    cmtT T X = true ↔ π * ξ = ξ * π :=
  tblEq_iff_eq' (Rep.compT hT hX) (Rep.compT hX hT)

theorem orderOf_glPerm (g : G) : orderOf (glPerm g) = orderOf g :=
  orderOf_injective _ glPerm_injective g

theorem glPerm_comm_iff (g h : G) : glPerm g * glPerm h = glPerm h * glPerm g ↔ g * h = h * g := by
  rw [← map_mul, ← map_mul]
  exact glPerm_injective.eq_iff

theorem card_order_two :
    Nat.card {g : G // orderOf g = 2} = 6975 :=
  Certificates.certificate2003.1

theorem card_order_three :
    Nat.card {g : G // orderOf g = 3} = 75392 :=
  Certificates.certificate2003.2.2.2.1

theorem card_order_three_fix (k : ℕ) (hk : k = 1 ∨ k = 7) :
    Nat.card {g : G // orderOf g = 3 ∧ fixCount g = k} = if k = 1 then 55552 else 19840 := by
  rcases hk with rfl | rfl
  · exact Certificates.certificate2003.2.2.2.2.1
  · exact Certificates.certificate2003.2.2.2.2.2.1

theorem card_centralizer_tau1 :
    Nat.card (Subgroup.centralizer {glTau1}) = 180 :=
  Certificates.certificate2003.2.2.2.2.2.2.2.2.1

theorem card_centralizer_tau2 :
    Nat.card (Subgroup.centralizer {glTau2}) = 504 :=
  Certificates.certificate2003.2.2.2.2.2.2.2.2.2.1

end CFSG.Literature.GL52
