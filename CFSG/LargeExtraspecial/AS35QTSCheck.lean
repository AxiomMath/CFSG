module

public import Certificates.Certificate21280
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat

public section

namespace CFSG.LargeExtraspecial.AS35QTS

open CFSG.Fischer

theorem mem_il {c : Cd} : c ∈ il ↔ c ∈ codes ∧ mulC c c = e0 ∧ c ≠ e0 := by
  simp only [il, isInv, List.mem_filter, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq]

theorem mem_sl {c : Cd} : c ∈ sl ↔ c ∈ il ∧ c.m ≠ I3 ∧ ∃ s ∈ codes, mulC s s = c := by
  simp only [sl, sq, List.mem_filter, Bool.and_eq_true, bne_iff_ne, ne_eq, List.contains_iff_mem,
    List.mem_map]

theorem mem_dl {c : Cd} : c ∈ dl ↔ c = tau0 ∨ c ∈ sl := by
  simp only [dl, List.mem_cons]

theorem mem_wl {c : Cd} : c ∈ wl ↔ c ∈ il ∧ c ∉ dl := by
  simp only [wl, List.mem_filter, List.contains_eq_mem, Bool.not_eq_true', decide_eq_false_iff_not]

theorem tau0_not_mem_sl : tau0 ∉ sl := fun h => (mem_sl.mp h).2.1 rfl

theorem commB_iff {x y : Cd} : commB x y = true ↔ mulC x y = mulC y x := by
  simp only [commB, beq_iff_eq]

theorem mem_lineIn {t c : Cd} : c ∈ lineIn dl t ↔ c ∈ dl ∧ mulC t c = mulC c t := by
  simp only [lineIn, commB, List.mem_filter, beq_iff_eq]

section


theorem qts_small : unitB I3 = true ∧ mulC e0 e0 = e0 ∧ ∀ g ∈ cgens, unitB g.m = true :=
  Certificates.certificate21280.1

theorem qts_lists : gu3s.length = 648 ∧ gu3s.Nodup ∧ sl.length = 36 ∧ sl.Nodup :=
  Certificates.certificate21280.2.1

theorem qts_q_pow (q : Cd) (hq : q ∈ codes) (hm : q.m = I3) : powC q 4 = e0 :=
  Certificates.certificate21280.2.2.1 q hq hm

theorem qts_root (c : Cd) (hc : c ∈ il) (hm : c.m ≠ I3) :
    ∃ q ∈ codes, q.m = I3 ∧ mulC q q = tau0 ∧ mulC q c = mulC c q :=
  Certificates.certificate21280.2.2.2.1 c hc hm

theorem qts_inv (c : Cd) (hc : c ∈ il) :
    c = tau0 ∨ c ∈ sl ∨ ∃ a ∈ dl, ∃ b ∈ dl, a ≠ b ∧ mulC a b = mulC b a ∧ mulC a b = c :=
  Certificates.certificate21280.2.2.2.2.1 c hc

theorem qts_class (t : Cd) (ht : t ∈ sl) : ∃ m ∈ codes, mulC m t0c = mulC t m :=
  Certificates.certificate21280.2.2.2.2.2.1 t ht

theorem qts_ord (a b : Cd) (ha : a ∈ dl) (hb : b ∈ dl) :
    mulC (mulC a b) (mulC a b) = e0 ∨
      mulC (mulC (mulC a b) (mulC a b)) (mulC a b) = e0 :=
  Certificates.certificate21280.2.2.2.2.2.2.1 a ha b hb

theorem qts_line_parts : (∀ t ∈ sl, (lineIn dl t).length = 5) ∧
    (∀ t ∈ sl, ∀ a ∈ lineIn dl t, ∀ b ∈ lineIn dl t, mulC a b = mulC b a) ∧
    (∀ t ∈ sl, ∀ t' ∈ sl, mulC t t' = mulC t' t → ∀ s ∈ sl,
      (mulC t s = mulC s t ↔ mulC t' s = mulC s t')) ∧
    (∀ t ∈ sl, ∀ a ∈ lineIn dl t, ∀ b ∈ lineIn dl t, ∀ a' ∈ lineIn dl t,
      ∀ b' ∈ lineIn dl t, a ≠ b → a' ≠ b' → mulC a b = mulC a' b' →
        (a = a' ∧ b = b') ∨ (a = b' ∧ b = a')) ∧
    ∀ t ∈ sl, mulC tau0 t ∉ dl :=
  Certificates.certificate21280.2.2.2.2.2.2.2.1

theorem qts_nz : (∀ x ∈ dl, ∀ v ∈ wl, pow72 (mulC x v) = e0) ∧
    ((dl.toFinset ×ˢ wl.toFinset).filter fun p => tau0 ∈ zpowL (mulC p.1 p.2)).card = 1188 :=
  Certificates.certificate21280.2.2.2.2.2.2.2.2.1

theorem qts_nw : (((lineIn dl t0c).toFinset ×ˢ (wl.filter (commB t0c)).toFinset).filter
    fun p => mulC tau0 t0c ∈ zpowL (mulC p.1 p.2)).card = 3 :=
  Certificates.certificate21280.2.2.2.2.2.2.2.2.2.1

theorem qts_swap (p p' : Cd) (hp : p ∈ sl) (hp' : p' ∈ sl) (hne : p ≠ p')
    (hpp : mulC p p' = mulC p' p) :
    (il.toFinset.filter fun v => mulC v p = mulC p' v).card = 16 ∧
      ∀ q ∈ sl, q ≠ p → q ≠ p' → mulC p q = mulC q p → ∀ v ∈ il,
        mulC v p = mulC p' v → mulC v q ≠ mulC q v :=
  Certificates.certificate21280.2.2.2.2.2.2.2.2.2.2.1 p hp p' hp' hne hpp

theorem qts_cent : (codes.filter (commB t0c)).toFinset.card = 2304 :=
  Certificates.certificate21280.2.2.2.2.2.2.2.2.2.2.2.1

theorem qts_center (c : Cd) (hc : c ∈ codes) (hg : ∀ g ∈ cgens, mulC c g = mulC g c) :
    c = e0 ∨ c = tau0 :=
  Certificates.certificate21280.2.2.2.2.2.2.2.2.2.2.2.2 c hc hg

end

end CFSG.LargeExtraspecial.AS35QTS
