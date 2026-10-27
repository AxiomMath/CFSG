module

public import CFSG.Certificates.Kernel.MonsterB.Co2StabBfs
public import Certificates.Data.Kernel.MonsterB.Co2Stab
public import CFSG.Certificates.Kernel.Spor.RawOrbHead

set_option linter.unusedSectionVars false

public section

namespace CFSG.KS.Co2Stab

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Raw.Orb CFSG.Monster.B.Co2.Native CFSG.Monster.B.Co2

@[expose] def offT (t : Nat) : Nat := if t = 0 then 0 else if t = 1 then 1 else 892

@[expose] def szT (t : Nat) : Nat := if t = 0 then 1 else if t = 1 then 891 else 1408

theorem labP_eq (p : Nat) : labP p = if p < 1 then 0 else if p < 892 then 1 else 2 := by
  unfold labP
  rw [nIf_eq, nIf_eq, blt_dec, blt_dec]
  by_cases h1 : p < 1 <;> by_cases h2 : p < 892 <;> simp [h1, h2]

theorem lab_off {t k : Nat} (ht : t < 3) (hk : k < szT t) :
    labP (offT t + k) = t ∧ offT t + k < 2300 := by
  rw [labP_eq]
  unfold offT
  unfold szT at hk
  rcases (by omega : t = 0 ∨ t = 1 ∨ t = 2) with rfl | rfl | rfl <;> simp at hk ⊢ <;> omega

theorem off_lab {p : Nat} (hp : p < 2300) :
    labP p < 3 ∧ offT (labP p) ≤ p ∧ p - offT (labP p) < szT (labP p) := by
  rw [labP_eq]
  unfold offT szT
  by_cases h1 : p < 1 <;> by_cases h2 : p < 892 <;> simp [h1, h2] <;> omega

theorem at12_eq (P p : Nat) : at12 P p = pg 12 (mask 12) P p := rfl

structure StabF (PS : Nat → Nat) (OP OPI WP WG WD : Nat) : Prop where
  op_lt : ∀ p < 2300, at12 OP p < 2300
  opi_op : ∀ p < 2300, at12 OPI (at12 OP p) = p
  opi_lt : ∀ z < 2300, at12 OPI z < 2300
  op_opi : ∀ z < 2300, at12 OP (at12 OPI z) = z
  sorted : ∀ p < 2299, p ≠ 0 → p ≠ 891 → at12 OP p < at12 OP (p + 1)
  closed : ∀ z < 2300, ∀ j < 18,
    labP (at12 OPI (at12 (PS (j + 2)) z)) = labP (at12 OPI z)
  start : ∀ z < 2300, (at12 OPI z = 0 ∨ at12 OPI z = 1 ∨ at12 OPI z = 892) → at12 WD z = 0
  wit : ∀ z < 2300, at12 OPI z ≠ 0 → at12 OPI z ≠ 1 → at12 OPI z ≠ 892 →
    at12 WP z < 2300 ∧ at12 WG z < 18 ∧ at12 (PS (at12 WG z + 2)) (at12 WP z) = z ∧
      at12 WD (at12 WP z) + 1 = at12 WD z

theorem stabF_of {PS : Nat → Nat} {OP OPI WP WG WD : Nat}
    (h : stabK PS OP OPI WP WG WD = true) : StabF PS OP OPI WP WG WD := by
  unfold stabK at h
  obtain ⟨h1, h⟩ := (bAnd_iff _ _).1 h
  obtain ⟨h2, h⟩ := (bAnd_iff _ _).1 h
  obtain ⟨h3, h⟩ := (bAnd_iff _ _).1 h
  obtain ⟨h4, h5⟩ := (bAnd_iff _ _).1 h
  obtain ⟨-, -, f1⟩ := permOK_facts (n := 2300) (w := 12) h1
  obtain ⟨-, -, f2⟩ := permOK_facts (n := 2300) (w := 12) h2
  refine ⟨fun p hp => (f1 p hp).1, fun p hp => (f1 p hp).2, fun z hz => (f2 z hz).1,
    fun z hz => (f2 z hz).2, fun p hp h0 h891 => ?_, fun z hz j hj => ?_, fun z hz hs => ?_,
    fun z hz hs0 hs1 hs2 => ?_⟩
  · have e := allN_spec h3 p hp
    have e1 : Nat.beq p 0 = false := by
      rw [Bool.eq_false_iff]
      intro e3
      exact h0 (Nat.eq_of_beq_eq_true e3)
    rw [e1] at e
    have e2 : Nat.beq p 891 = false := by
      rw [Bool.eq_false_iff]
      intro e3
      exact h891 (Nat.eq_of_beq_eq_true e3)
    rw [e2] at e
    exact Nat.blt_eq.mp e
  · have e := allN_spec h4 z hz
    rw [Orb.strictB_eq] at e
    have e2 := allN_spec e j hj
    rw [Nat.add_eq] at e2
    exact (Nat.eq_of_beq_eq_true e2)
  · have e := allN_spec h5 z hz
    rw [Orb.strictB_eq] at e
    rcases hs with hs | hs | hs <;> rw [hs] at e <;> exact Nat.eq_of_beq_eq_true e
  · have e := allN_spec h5 z hz
    have ne : ∀ c, at12 OPI z ≠ c → Nat.beq (at12 OPI z) c = false := fun c hc => by
      rw [Bool.eq_false_iff]
      exact fun e' => hc (Nat.eq_of_beq_eq_true e')
    rw [Orb.strictB_eq, ne 0 hs0, ne 1 hs1, ne 892 hs2, Orb.strictB_eq, Orb.strictB_eq] at e
    obtain ⟨e1, e⟩ := (bAnd_iff _ _).1 e
    obtain ⟨e2, e⟩ := (bAnd_iff _ _).1 e
    obtain ⟨e3, e4⟩ := (bAnd_iff _ _).1 e
    rw [Nat.add_eq] at e3
    exact ⟨Nat.blt_eq.mp e1, Nat.blt_eq.mp e2, Nat.eq_of_beq_eq_true e3,
      Nat.eq_of_beq_eq_true e4⟩

section Orbits

variable {PS : Nat → Nat} {OP OPI WP WG WD : Nat} {gens orbs : Array (Array Nat)}
  (F : StabF PS OP OPI WP WG WD)
  (hgs : gens.size = 18) (hg : ∀ j < 18, ∀ x < 2300, (gens[j]!)[x]! = at12 (PS (j + 2)) x)
  (hgn : ∀ j < 18, ∀ x < 2300, at12 (PS (j + 2)) x < 2300)
  (ho : orbs.size = 3) (hos : ∀ t < 3, (orbs[t]!).size = szT t)
  (hoe : ∀ t < 3, ∀ k < szT t, (orbs[t]!)[k]! = at12 OP (offT t + k))
include F hgs hg hgn ho hos hoe

theorem gens_lt : ∀ j < gens.size, ∀ x < 2300, (gens[j]!)[x]! < 2300 := fun j hj x hx => by
  rw [hgs] at hj
  rw [hg j hj x hx]
  exact hgn j hj x hx

theorem labels : ∀ z < 2300,
    (orbitLabel 2300 orbs).1[z]! = labP (at12 OPI z) ∧
      (orbitLabel 2300 orbs).2[z]! = at12 OPI z - offT (labP (at12 OPI z)) := by
  have L := labels_orbitLabel (n := 2300) (orbs := orbs) (fun t ht k hk => by
      rw [ho] at ht
      rw [hos t ht] at hk
      rw [hoe t ht k hk]
      exact F.op_lt _ (lab_off ht hk).2)
    (fun t ht k hk t' ht' k' hk' e => by
      rw [ho] at ht ht'
      rw [hos t ht] at hk
      rw [hos t' ht'] at hk'
      rw [hoe t ht k hk, hoe t' ht' k' hk'] at e
      have e2 := congrArg (at12 OPI) e
      rw [F.opi_op _ (lab_off ht hk).2, F.opi_op _ (lab_off ht' hk').2] at e2
      have l1 := (lab_off ht hk).1
      have l2 := (lab_off ht' hk').1
      rw [e2] at l1
      rw [l1] at l2
      subst l2
      exact ⟨rfl, by omega⟩)
  intro z hz
  obtain ⟨hl, hle, hlt⟩ := off_lab (F.opi_lt z hz)
  set t := labP (at12 OPI z)
  set k := at12 OPI z - offT t
  have hz' : (orbs[t]!)[k]! = z := by
    rw [hoe t hl k hlt, show offT t + k = at12 OPI z by omega, F.op_opi z hz]
  have := L t (by rw [ho]; exact hl) k (by rw [hos t hl]; exact hlt)
  rw [hz'] at this
  exact this

theorem lab_gen {z j : Nat} (hz : z < 2300) (hj : j < gens.size) :
    labP (at12 OPI ((gens[j]!)[z]!)) = labP (at12 OPI z) := by
  rw [hgs] at hj
  rw [hg j hj z hz]
  exact F.closed z hz j hj

theorem root_lt {t : Nat} (ht : t < 3) : (orbs[t]!)[0]! < 2300 := by
  rw [hoe t ht 0 (by unfold szT; split_ifs <;> omega)]
  exact F.op_lt _ (lab_off ht (by unfold szT; split_ifs <;> omega)).2

theorem root_pos {t : Nat} (ht : t < 3) : at12 OPI ((orbs[t]!)[0]!) = offT t := by
  rw [hoe t ht 0 (by unfold szT; split_ifs <;> omega), Nat.add_zero]
  exact F.opi_op _ (by unfold offT; split_ifs <;> omega)

theorem reach {t : Nat} (ht : t < 3) : ∀ z < 2300, labP (at12 OPI z) = t →
    0 < (orbitRecord 2300 (orbs[t]!)[0]! gens).1[z]! := by
  have R := recFacts_orbitRecord (root_lt F hgs hg hgn ho hos hoe ht) (gens_lt F hgs hg hgn ho hos hoe)
  intro z
  induction hw : at12 WD z using Nat.strong_induction_on generalizing z with
  | _ m ih =>
    intro hz hl
    by_cases hs : at12 OPI z = 0 ∨ at12 OPI z = 1 ∨ at12 OPI z = 892
    · have hp : at12 OPI z = offT t := by
        rw [← hl, labP_eq]
        unfold offT
        rcases hs with hs | hs | hs <;> rw [hs] <;> decide
      have : z = (orbs[t]!)[0]! := by
        rw [← F.op_opi z hz, hp, hoe t ht 0 (by unfold szT; split_ifs <;> omega), Nat.add_zero]
      rw [this]
      exact R.root_pos
    · obtain ⟨hs0, hs1, hs2⟩ : at12 OPI z ≠ 0 ∧ at12 OPI z ≠ 1 ∧ at12 OPI z ≠ 892 := by omega
      obtain ⟨w1, w2, w3, w4⟩ := F.wit z hz hs0 hs1 hs2
      have hgz : (gens[at12 WG z]!)[at12 WP z]! = z := by
        rw [hg _ w2 _ w1, w3]
      have hly : labP (at12 OPI (at12 WP z)) = t := by
        have e := lab_gen F hgs hg hgn ho hos hoe w1 (by rw [hgs]; exact w2)
        rw [hgz, hl] at e
        exact e.symm
      have := ih (at12 WD (at12 WP z)) (by omega) (at12 WP z) rfl w1 hly
      rw [← hgz]
      exact R.closed _ w1 this _ (by rw [hgs]; exact w2)

theorem reached_in {t : Nat} (ht : t < 3) : ∀ z < 2300,
    0 < (orbitRecord 2300 (orbs[t]!)[0]! gens).1[z]! → labP (at12 OPI z) = t := by
  have R := recFacts_orbitRecord (root_lt F hgs hg hgn ho hos hoe ht) (gens_lt F hgs hg hgn ho hos hoe)
  suffices H : ∀ m, ∀ z < 2300, (orbitRecord 2300 (orbs[t]!)[0]! gens).1[z]! = m → 0 < m →
      labP (at12 OPI z) = t from fun z hz hd => H _ z hz rfl hd
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro z hz hw hd
    by_cases h1 : m = 1
    · rw [R.one z hz (hw.trans h1), root_pos F hgs hg hgn ho hos hoe ht]
      exact (lab_off ht (by unfold szT; split_ifs <;> omega : 0 < szT t)).1
    · obtain ⟨e1, e2, e3, e4, e5⟩ := R.edge z hz (by rw [hw]; exact hd) (by rw [hw]; exact h1)
      have := ih _ (by omega) _ e1 rfl e2
      rw [← e5, lab_gen F hgs hg hgn ho hos hoe e1 e4]
      exact this

theorem orbitsOK_of {sizes : Array Nat} (hss : sizes.size = 3)
    (hsz : ∀ t < 3, sizes[t]! = szT t) :
    orbitsOK 2300 gens orbs sizes (orbitLabel 2300 orbs).1 (orbitLabel 2300 orbs).2
      (orbs.map fun o => orbitRecord 2300 o[0]! gens) = true := by
  have Lb := labels F hgs hg hgn ho hos hoe
  have hrec : ∀ t < 3, (orbs.map fun o => orbitRecord 2300 o[0]! gens)[t]! =
      orbitRecord 2300 (orbs[t]!)[0]! gens := fun t ht => by
    rw [getElem!_pos _ t (by simp [ho]; exact ht), Array.getElem_map, getElem!_pos orbs t (by omega)]
  have hpt : ∀ t < 3, ∀ k < szT t, (orbs[t]!)[k]! < 2300 ∧ at12 OPI ((orbs[t]!)[k]!) = offT t + k :=
    fun t ht k hk => by
      rw [hoe t ht k hk]
      exact ⟨F.op_lt _ (lab_off ht hk).2, F.opi_op _ (lab_off ht hk).2⟩
  have hlab : ∀ t < 3, ∀ k < szT t, labP (at12 OPI ((orbs[t]!)[k]!)) = t := fun t ht k hk => by
    rw [(hpt t ht k hk).2]
    exact (lab_off ht hk).1
  unfold orbitsOK
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, allLt_iff, Array.size_map, ho, hss,
    and_assoc, true_and]
  refine ⟨fun t ht => ?_, fun z hz => ?_, fun t ht k hk j hj => ?_, fun t ht k hk => ?_⟩
  · rw [hsz t ht]
    refine ⟨hos t ht, by unfold szT; split_ifs <;> omega, fun k hk => ?_, fun k hk => ?_⟩
    · obtain ⟨h1, _⟩ := hpt t ht k hk
      exact ⟨h1, by rw [(Lb _ h1).1, hlab t ht k hk]⟩
    · rw [hoe t ht k (by omega), hoe t ht (k + 1) (by omega), ← Nat.add_assoc]
      refine F.sorted _ (by have := (lab_off ht (by omega : k + 1 < szT t)).2; omega) ?_ ?_
      · unfold offT
        unfold szT at hk
        split_ifs at hk ⊢ <;> omega
      · unfold offT
        unfold szT at hk
        split_ifs at hk ⊢ <;> omega
  · obtain ⟨hl, hle, hlt⟩ := off_lab (F.opi_lt z hz)
    rw [(Lb z hz).1, (Lb z hz).2, hsz _ hl]
    refine ⟨hl, hlt, ?_⟩
    rw [hoe _ hl _ hlt, show offT (labP (at12 OPI z)) + (at12 OPI z - offT (labP (at12 OPI z))) =
      at12 OPI z by omega, F.op_opi z hz]
  · rw [hsz t ht] at hk
    obtain ⟨h1, _⟩ := hpt t ht k hk
    have hy := gens_lt F hgs hg hgn ho hos hoe j hj _ h1
    refine ⟨hy, ?_⟩
    rw [(Lb _ hy).1, lab_gen F hgs hg hgn ho hos hoe h1 hj, hlab t ht k hk]
  · rw [hsz t ht] at hk
    obtain ⟨h1, _⟩ := hpt t ht k hk
    have R := recFacts_orbitRecord (root_lt F hgs hg hgn ho hos hoe ht)
      (gens_lt F hgs hg hgn ho hos hoe)
    rw [hrec t ht]
    have hd := reach F hgs hg hgn ho hos hoe ht _ h1 (hlab t ht k hk)
    refine ⟨hd, ?_⟩
    split
    · rename_i h1'
      exact beq_iff_eq.2 (R.one _ h1 h1')
    · rename_i h1'
      obtain ⟨e1, e2, e3, e4, e5⟩ := R.edge _ h1 hd h1'
      simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, and_assoc]
      refine ⟨e1, ?_, e3, e4, e5⟩
      rw [(Lb _ e1).1]
      exact reached_in F hgs hg hgn ho hos hoe ht _ e1 e2

end Orbits

end CFSG.KS.Co2Stab

end
