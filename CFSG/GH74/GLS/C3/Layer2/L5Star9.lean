module

public import CFSG.GH74.GLS.C3.Layer2.L5Fin
public import CFSG.GH74.GLS.C3.Layer2.NumMoved
public import CFSG.GH74.GLS.C3.Layer3.Basic
public import CFSG.GH74.GLS.C3.Layer3.AltInvolutions
public import Mathlib.GroupTheory.Complement
public meta import Mathlib.GroupTheory.SpecificGroups.Alternating
public meta import CFSG.GH74.GLS.C3.Prop121.ModelFive
public meta import CFSG.GH74.GLS.C3.Prop121.ModelFiveS
public meta import CFSG.GH74.GLS.C3.Layer2.FinModelDefs
public meta import CFSG.GH74.GLS.C3.Layer2.FinModelEmb
public meta import CFSG.GH74.GLS.C3.Layer2.NumMoved
public meta import CFSG.GH74.GLS.C3.Layer2.L5Fin
public meta import CFSG.GH74.GLS.C3.Layer3.AltInvolutions
public import CFSG.GH74.GLS.C3.Layer2.L5Star9Inputs
public meta import CFSG.GH74.GLS.C3.Layer2.L5Star9Inputs
public import Certificates.Certificate5072
public import Certificates.Certificate5074
public import Certificates.Certificate5092

public section

namespace CFSG.GH74.GLS.C3.Layer2.L5

open Equiv Perm Subgroup CFSG.GH74.GLS.C3.Prop121 CFSG.GH74.GLS.C3.Layer2
  CFSG.GH74.GLS.C3.Layer2.Model CFSG.GH74.GLS.Layer3
open scoped Pointwise

theorem D9list_mul_chk :
    D9list.all (fun a => D9list.all fun b => decide (a * b ∈ D9list)) = true :=
  Certificates.certificate5074.1

theorem D9list_mul : ∀ a ∈ D9list, ∀ b ∈ D9list, a * b ∈ D9list := by
  have h := D9list_mul_chk
  simpa only [List.all_eq_true, decide_eq_true_eq] using h

theorem D9list_inv_chk :
    D9list.all (fun a => decide (a⁻¹ ∈ D9list)) = true :=
  Certificates.certificate5074.2.1

theorem D9list_inv : ∀ a ∈ D9list, a⁻¹ ∈ D9list := by
  have h := D9list_inv_chk
  simpa only [List.all_eq_true, decide_eq_true_eq] using h

theorem D9list_nodup : D9list.Nodup :=
  Certificates.certificate5074.2.2.1

theorem D9list_length : D9list.length = 24 :=
  Certificates.certificate5074.2.2.2.1

theorem D9_comm_yS_chk :
    D9list.all (fun d => decide (d * yS = yS * d)) = true :=
  Certificates.certificate5074.2.2.2.2.1

theorem D9_comm_yS : ∀ d ∈ D9list, d * yS = yS * d := by
  have h := D9_comm_yS_chk
  simpa only [List.all_eq_true, decide_eq_true_eq] using h

theorem D9_even_chk :
    D9list.all (fun d => decide (sign d = 1)) = true :=
  Certificates.certificate5074.2.2.2.2.2.1

theorem D9_even : ∀ d ∈ D9list, sign d = 1 := by
  have h := D9_even_chk
  simpa only [List.all_eq_true, decide_eq_true_eq] using h

theorem D9_inter_E9_chk :
    D9list.all (fun d => imp (decide (d ∈ E9l)) (decide (d = 1))) = true :=
  Certificates.certificate5074.2.2.2.2.2.2.1

theorem D9_inter_E9 : ∀ d ∈ D9list, d ∈ E9l → d = 1 := by
  have h := D9_inter_E9_chk
  simpa only [List.all_eq_true, imp_eq_true, decide_eq_true_eq] using h

theorem D9_norm_E9_chk :
    D9list.all (fun d => E9l.all fun e => decide (d * e * d⁻¹ ∈ E9l)) = true :=
  Certificates.certificate5074.2.2.2.2.2.2.2.1

theorem D9_norm_E9 : ∀ d ∈ D9list, ∀ e ∈ E9l, d * e * d⁻¹ ∈ E9l := by
  have h := D9_norm_E9_chk
  simpa only [List.all_eq_true, decide_eq_true_eq] using h

theorem D9_faithful_chk :
    D9list.all (fun d => imp (E9l.all fun e => decide (d * e = e * d))
    (decide (d = 1))) = true :=
  Certificates.certificate5074.2.2.2.2.2.2.2.2.1

theorem D9_faithful :
    ∀ d ∈ D9list, (∀ e ∈ E9l, d * e = e * d) → d = 1 := by
  have h := D9_faithful_chk
  simpa only [List.all_eq_true, imp_eq_true, decide_eq_true_eq] using h

theorem E9_comm_yS_chk :
    E9l.all (fun e => decide (e * yS = yS * e)) = true :=
  Certificates.certificate5074.2.2.2.2.2.2.2.2.2.1

theorem E9_comm_yS : ∀ e ∈ E9l, e * yS = yS * e := by
  have h := E9_comm_yS_chk
  simpa only [List.all_eq_true, decide_eq_true_eq] using h

theorem E9_even_chk :
    E9l.all (fun e => decide (sign e = 1)) = true :=
  Certificates.certificate5074.2.2.2.2.2.2.2.2.2.2.1

theorem E9_even : ∀ e ∈ E9l, sign e = 1 := by
  have h := E9_even_chk
  simpa only [List.all_eq_true, decide_eq_true_eq] using h

@[expose] def D9 : Subgroup (Perm (Fin 9)) where
  carrier := {p | p ∈ D9list}
  one_mem' := by
    show (1 : Perm (Fin 9)) ∈ D9list
    simp [D9list, D3list]
  mul_mem' := fun {a b} ha hb => D9list_mul a ha b hb
  inv_mem' := fun {a} ha => D9list_inv a ha

theorem mem_D9 {p : Perm (Fin 9)} : p ∈ D9 ↔ p ∈ D9list := Iff.rfl

theorem card_D9 : Nat.card D9 = 24 := by
  rw [natCard_eq_length D9 D9list D9list_nodup (fun p => Iff.rfl), D9list_length]

theorem D9_le_alt : D9 ≤ alternatingGroup (Fin 9) := fun p hp =>
  mem_alternatingGroup.2 (D9_even p (mem_D9.1 hp))

theorem E9_le_alt :
    E9 ≤ alternatingGroup (Fin 9) := fun p hp =>
  mem_alternatingGroup.2 (E9_even p (mem_E9l.2 hp))

@[expose] def vA :
    alternatingGroup (Fin 9) := ⟨yS, S0_le_alt yS_mem_S0⟩

@[expose] def C2 :
    Subgroup (alternatingGroup (Fin 9)) :=
  Subgroup.centralizer ({vA} : Set (alternatingGroup (Fin 9)))

@[expose] def E9A : Subgroup (alternatingGroup (Fin 9)) :=
  E9.subgroupOf (alternatingGroup (Fin 9))

@[expose] def D9A : Subgroup (alternatingGroup (Fin 9)) :=
  D9.subgroupOf (alternatingGroup (Fin 9))

theorem mem_C2
    {z : alternatingGroup (Fin 9)} : z ∈ C2 ↔ (z : Perm (Fin 9)) * yS = yS * z := by
  rw [C2, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    have h' := congrArg Subtype.val h
    exact h'
  · intro h
    exact Subtype.ext h

theorem numMoved_yPerm9 :
    numMoved (yPerm (by norm_num : 8 ≤ 9)) = 8 :=
  Certificates.certificate5074.2.2.2.2.2.2.2.2.2.2.2.2

theorem card_C2 :
    Nat.card C2 = 192 := by
  have h8 : 8 ≤ 9 := by norm_num
  have hvo : orderOf vA = 2 :=
    orderOf_eq_prime (by rw [sq]; exact Subtype.ext yS_sq)
      (fun h => yS_ne_one (congrArg Subtype.val h))
  have hnm : numMoved ((vA : alternatingGroup (Fin 9)) : Perm (Fin 9)) =
      numMoved ((altY h8 : alternatingGroup (Fin 9)) : Perm (Fin 9)) := by
    show numMoved yS = numMoved (yPerm h8)
    rw [numMoved_yS, numMoved_yPerm9]
  have hconj : IsConj vA (altY h8) :=
    isConj_alternating_of_numMoved_eq 9 _ _ hvo (orderOf_altY h8) hnm
  have h1 := card_centralizer_altY h8
  have h2 := card_centralizer_eq_of_isConj hconj
  have h3 : Nat.card C2 * 2 = 384 := by
    show Nat.card (Subgroup.centralizer ({vA} : Set (alternatingGroup (Fin 9)))) * 2 = 384
    rw [h2, h1]
    norm_num [Nat.factorial]
  omega

theorem E9A_le_C2 :
    E9A ≤ C2 := by
  intro z hz
  rw [mem_C2]
  exact E9_comm_yS _ (mem_E9l.2 hz)

theorem D9A_le_C2 :
    D9A ≤ C2 := by
  intro z hz
  rw [mem_C2]
  exact D9_comm_yS _ (mem_D9.1 hz)

theorem card_E9A :
    Nat.card E9A = 8 := by
  have : Nat.card E9A = Nat.card E9 :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe E9_le_alt).toEquiv
  rw [this, card_E9]

theorem card_D9A : Nat.card D9A = 24 := by
  have : Nat.card D9A = Nat.card D9 :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe D9_le_alt).toEquiv
  rw [this, card_D9]

theorem mem_E2 {z : ↥C2} :
    z ∈ E9A.subgroupOf C2 ↔ ((z : alternatingGroup (Fin 9)) : Perm (Fin 9)) ∈ E9l := by
  rw [mem_E9l]
  exact Iff.rfl

theorem mem_D2
    {z : ↥C2} :
    z ∈ D9A.subgroupOf C2 ↔ ((z : alternatingGroup (Fin 9)) : Perm (Fin 9)) ∈ D9list := Iff.rfl

theorem card_E2 :
    Nat.card (E9A.subgroupOf C2) = 8 :=
  (Nat.card_congr (Subgroup.subgroupOfEquivOfLe E9A_le_C2).toEquiv).trans card_E9A

theorem star9_data :
    ∃ D₂ : Subgroup ↥C2, (E9A.subgroupOf C2).IsComplement' D₂ ∧ (E9A.subgroupOf C2).Normal ∧
      Nat.card C2 = 192 ∧ Nat.card (E9A.subgroupOf C2) = 8 ∧
      (∀ e ∈ E9A.subgroupOf C2, e * e = 1) ∧
      (∀ c : ↥C2, (∀ e ∈ E9A.subgroupOf C2, c * e = e * c) → c ∈ E9A.subgroupOf C2) := by
  have hE : Nat.card (E9A.subgroupOf C2) = 8 :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe E9A_le_C2).toEquiv).trans card_E9A
  have hD : Nat.card (D9A.subgroupOf C2) = 24 :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe D9A_le_C2).toEquiv).trans card_D9A
  have hdisj : Disjoint (E9A.subgroupOf C2) (D9A.subgroupOf C2) := by
    rw [Subgroup.disjoint_def]
    intro z hzE hzD
    have h3 := D9_inter_E9 _ (mem_D2.1 hzD) (mem_E2.1 hzE)
    exact Subtype.ext (Subtype.ext h3)
  have hcard : Nat.card (E9A.subgroupOf C2) * Nat.card (D9A.subgroupOf C2) = Nat.card ↥C2 := by
    rw [hE, hD, card_C2]
  have hcompl : (E9A.subgroupOf C2).IsComplement' (D9A.subgroupOf C2) :=
    Subgroup.isComplement'_of_card_mul_and_disjoint hcard hdisj
  have hmul : ∀ g : ↥C2, ∃ e ∈ E9A.subgroupOf C2, ∃ d ∈ D9A.subgroupOf C2, e * d = g := by
    intro g
    have hg : g ∈ ((E9A.subgroupOf C2 : Subgroup ↥C2) : Set ↥C2) *
        ((D9A.subgroupOf C2 : Subgroup ↥C2) : Set ↥C2) := by
      rw [Subgroup.IsComplement.mul_eq hcompl]
      trivial
    obtain ⟨e, he, d, hd, rfl⟩ := hg
    exact ⟨e, he, d, hd, rfl⟩
  have hnorm : ∀ d ∈ D9A.subgroupOf C2, ∀ e ∈ E9A.subgroupOf C2,
      d * e * d⁻¹ ∈ E9A.subgroupOf C2 := by
    intro d hd e he
    rw [mem_E2]
    have := D9_norm_E9 _ (mem_D2.1 hd) _ (mem_E2.1 he)
    exact this
  have hcomm : ∀ e ∈ E9A.subgroupOf C2, ∀ e' ∈ E9A.subgroupOf C2, e * e' = e' * e := by
    intro e he e' he'
    have := E9_comm_aux _ (mem_E2.1 he) _ (mem_E2.1 he')
    exact Subtype.ext (Subtype.ext this)
  refine ⟨D9A.subgroupOf C2, hcompl, ⟨fun e he g => ?_⟩, card_C2, hE, fun e he => ?_,
    fun g hg => ?_⟩
  · obtain ⟨e', he', d, hd, rfl⟩ := hmul g
    have h1 : e' * d * e * (e' * d)⁻¹ = e' * (d * e * d⁻¹) * e'⁻¹ := by group
    rw [h1]
    exact mul_mem (mul_mem he' (hnorm d hd e he)) (inv_mem he')
  · have := E9_sq_aux _ (mem_E2.1 he)
    exact Subtype.ext (Subtype.ext this)
  · obtain ⟨e', he', d, hd, rfl⟩ := hmul g
    have hdc : ∀ e ∈ E9A.subgroupOf C2, d * e = e * d := by
      intro e he
      have h1 : e' * d * e = e * (e' * d) := hg e he
      have h2 : e' * (d * e) = e' * (e * d) := by
        calc e' * (d * e) = e' * d * e := by group
          _ = e * (e' * d) := h1
          _ = (e * e') * d := by group
          _ = (e' * e) * d := by rw [hcomm e he e' he']
          _ = e' * (e * d) := by group
      exact mul_left_cancel h2
    have hd1 : d = 1 := by
      have hdl := mem_D2.1 hd
      have := D9_faithful _ hdl (by
        intro e he
        have hE' : (⟨⟨e, E9_le_alt (mem_E9l.1 he)⟩, E9A_le_C2 (mem_E9l.1 he)⟩ : ↥C2) ∈
            E9A.subgroupOf C2 := mem_E2.2 he
        have h2 := congrArg (fun z : ↥C2 => ((z : alternatingGroup (Fin 9)) : Perm (Fin 9)))
          (hdc _ hE')
        exact h2)
      exact Subtype.ext (Subtype.ext this)
    rw [hd1, mul_one]
    exact he'

end CFSG.GH74.GLS.C3.Layer2.L5
