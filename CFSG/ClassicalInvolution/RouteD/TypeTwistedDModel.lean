module

public import CFSG.ClassicalInvolution.WeakCT.TwistedSpinModel
public import CFSG.ClassicalInvolution.ModelFacts.Families
public import CFSG.ClassicalInvolution.RouteD.TypeF4Closure

public section

namespace CFSG.ClassicalInvolution.RouteD

open CFSG.LieType CFSG.LieType.Universal CFSG.LieType.Universal.Spin
  CFSG.LieType.Universal.Spin.Twisted CFSG.LieType.RootSystem CFSG.ClassicalInvolution.Generic
open scoped MatrixGroups

section Highest

variable {F : Type} [Field F] {b c : F} (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) {n : ℕ}

@[expose] def twIdx0 (hn : 3 ≤ n) : Fin (n - 1) := ⟨0, by omega⟩

@[expose] def twIdx1 (hn : 3 ≤ n) : Fin (n - 1) := ⟨1, by omega⟩

theorem twIdx0_ne_twIdx1 (hn : 3 ≤ n) : twIdx0 hn ≠ twIdx1 hn := fun h => by
  have := congrArg Fin.val h
  simp [twIdx0, twIdx1] at this

@[expose] def hiMinus (hn : 3 ≤ n) : Fin (n - 1) → ℤ :=
  ofStdB (n - 1) (Pi.single (twIdx0 hn) 1 + Pi.single (twIdx1 hn) 1)

theorem toStdB_hiMinus (hn : 3 ≤ n) :
    toStdB (n - 1) (hiMinus hn) =
      Pi.single (twIdx0 hn) (boolSign true) + Pi.single (twIdx1 hn) (boolSign true) := by
  rw [hiMinus, toStdB_ofStdB, boolSign_true]

theorem toStdB_neg_hiMinus (hn : 3 ≤ n) :
    toStdB (n - 1) (-hiMinus hn) =
      Pi.single (twIdx1 hn) (boolSign false) + Pi.single (twIdx0 hn) (boolSign false) := by
  rw [toStdB_neg, toStdB_hiMinus, boolSign_true, boolSign_false, Pi.single_neg, Pi.single_neg]
  abel

@[expose] noncomputable def rankOneHiMinus (hn : 3 ≤ n) :
    Subgroup (spinGroup (quadMinus n F b c)) :=
  (minusDatum n hirr).rootGroup (hiMinus hn) ⊔ (minusDatum n hirr).rootGroup (-hiMinus hn)

theorem mem_rootGroup_hiMinus_iff (hn : 3 ≤ n) {x : spinGroup (quadMinus n F b c)} :
    x ∈ (minusDatum n hirr).rootGroup (hiMinus hn) ↔
      ∃ a : F, x = (minusFrame n b c).longRoot (twIdx0_ne_twIdx1 hn) true true (.ofAdd a) :=
  mem_minusRootGroup_long_iff n hirr (twIdx0_ne_twIdx1 hn) true true (toStdB_hiMinus hn)

theorem mem_rootGroup_hiMinus_iff' (hn : 3 ≤ n) {x : spinGroup (quadMinus n F b c)} :
    x ∈ (minusDatum n hirr).rootGroup (hiMinus hn) ↔
      ∃ a : F, x = (minusFrame n b c).longRoot (twIdx0_ne_twIdx1 hn).symm true true (.ofAdd a) :=
  mem_minusRootGroup_long_iff n hirr (twIdx0_ne_twIdx1 hn).symm true true (by
    rw [toStdB_hiMinus, add_comm])

theorem mem_rootGroup_neg_hiMinus_iff (hn : 3 ≤ n) {x : spinGroup (quadMinus n F b c)} :
    x ∈ (minusDatum n hirr).rootGroup (-hiMinus hn) ↔
      ∃ a : F, x = (minusFrame n b c).longRoot (twIdx0_ne_twIdx1 hn).symm false false (.ofAdd a) :=
  mem_minusRootGroup_long_iff n hirr (twIdx0_ne_twIdx1 hn).symm false false (toStdB_neg_hiMinus hn)

theorem mem_rootGroup_neg_hiMinus_iff' (hn : 3 ≤ n) {x : spinGroup (quadMinus n F b c)} :
    x ∈ (minusDatum n hirr).rootGroup (-hiMinus hn) ↔
      ∃ a : F, x = (minusFrame n b c).longRoot (twIdx0_ne_twIdx1 hn) false false (.ofAdd a) :=
  mem_minusRootGroup_long_iff n hirr (twIdx0_ne_twIdx1 hn) false false (by
    rw [toStdB_neg_hiMinus, add_comm])

end Highest

section Commute

variable {F : Type} [Field F] {b c : F} (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) {n : ℕ}

theorem commutes_hiMinus_twin (hn : 3 ≤ n) :
    Commutes (rankOneHiMinus hirr hn)
      (CurtisTits.rankOne (minusDatum n hirr).rootGroup (twIdx0 hn)) := by
  have hk : (twIdx0 hn).val + 1 < n - 1 := by simp only [twIdx0]; omega
  have hsucc : (⟨(twIdx0 hn).val + 1, hk⟩ : Fin (n - 1)) = twIdx1 hn := rfl
  have h1 : toStdB (n - 1) (Pi.single (twIdx0 hn) 1) =
      Pi.single (twIdx0 hn) (boolSign true) + Pi.single (twIdx1 hn) (boolSign false) := by
    rw [toStdB_single_of_lt' n hk, hsucc]
  have h2 : toStdB (n - 1) (-Pi.single (twIdx0 hn) 1) =
      Pi.single (twIdx1 hn) (boolSign true) + Pi.single (twIdx0 hn) (boolSign false) := by
    rw [toStdB_neg_single_of_lt' n hk, hsucc]
  have h1' : toStdB (n - 1) (Pi.single (twIdx0 hn) 1) =
      Pi.single (twIdx1 hn) (boolSign false) + Pi.single (twIdx0 hn) (boolSign true) := by
    rw [h1, add_comm]
  have h2' : toStdB (n - 1) (-Pi.single (twIdx0 hn) 1) =
      Pi.single (twIdx0 hn) (boolSign false) + Pi.single (twIdx1 hn) (boolSign true) := by
    rw [h2, add_comm]
  have e1 : ∀ {x}, x ∈ (minusDatum n hirr).rootGroup (Pi.single (twIdx0 hn) 1) ↔
      ∃ a : F, x = (minusFrame n b c).longRoot (twIdx0_ne_twIdx1 hn) true false (.ofAdd a) :=
    fun {x} => mem_minusRootGroup_long_iff n hirr (twIdx0_ne_twIdx1 hn) true false h1
  have e1' : ∀ {x}, x ∈ (minusDatum n hirr).rootGroup (Pi.single (twIdx0 hn) 1) ↔
      ∃ a : F, x = (minusFrame n b c).longRoot (twIdx0_ne_twIdx1 hn).symm false true (.ofAdd a) :=
    fun {x} => mem_minusRootGroup_long_iff n hirr (twIdx0_ne_twIdx1 hn).symm false true h1'
  have e2 : ∀ {x}, x ∈ (minusDatum n hirr).rootGroup (-Pi.single (twIdx0 hn) 1) ↔
      ∃ a : F, x = (minusFrame n b c).longRoot (twIdx0_ne_twIdx1 hn).symm true false (.ofAdd a) :=
    fun {x} => mem_minusRootGroup_long_iff n hirr (twIdx0_ne_twIdx1 hn).symm true false h2
  have e2' : ∀ {x}, x ∈ (minusDatum n hirr).rootGroup (-Pi.single (twIdx0 hn) 1) ↔
      ∃ a : F, x = (minusFrame n b c).longRoot (twIdx0_ne_twIdx1 hn) false true (.ofAdd a) :=
    fun {x} => mem_minusRootGroup_long_iff n hirr (twIdx0_ne_twIdx1 hn) false true h2'
  unfold rankOneHiMinus CurtisTits.rankOne
  refine commutes_sup_sup ?_ ?_ ?_ ?_
  ·
    intro x hx y hy
    obtain ⟨a, rfl⟩ := (mem_rootGroup_hiMinus_iff hirr hn).mp hx
    obtain ⟨d, rfl⟩ := e1.mp hy
    exact (minusFrame n b c).commute_longRoot_longRoot_left (twIdx0_ne_twIdx1 hn)
      (twIdx0_ne_twIdx1 hn) true true false a d |>.eq
  ·
    intro x hx y hy
    obtain ⟨a, rfl⟩ := (mem_rootGroup_hiMinus_iff' hirr hn).mp hx
    obtain ⟨d, rfl⟩ := e2.mp hy
    exact (minusFrame n b c).commute_longRoot_longRoot_left (twIdx0_ne_twIdx1 hn).symm
      (twIdx0_ne_twIdx1 hn).symm true true false a d |>.eq
  ·
    intro x hx y hy
    obtain ⟨a, rfl⟩ := (mem_rootGroup_neg_hiMinus_iff hirr hn).mp hx
    obtain ⟨d, rfl⟩ := e1'.mp hy
    exact (minusFrame n b c).commute_longRoot_longRoot_left (twIdx0_ne_twIdx1 hn).symm
      (twIdx0_ne_twIdx1 hn).symm false false true a d |>.eq
  ·
    intro x hx y hy
    obtain ⟨a, rfl⟩ := (mem_rootGroup_neg_hiMinus_iff' hirr hn).mp hx
    obtain ⟨d, rfl⟩ := e2'.mp hy
    exact (minusFrame n b c).commute_longRoot_longRoot_left (twIdx0_ne_twIdx1 hn)
      (twIdx0_ne_twIdx1 hn) false false true a d |>.eq

theorem commutes_hiMinus_long (hn : 3 ≤ n) {j : Fin (n - 1)} (hj : j.val + 1 < n - 1)
    (h2 : 2 ≤ j.val) :
    Commutes (rankOneHiMinus hirr hn) (CurtisTits.rankOne (minusDatum n hirr).rootGroup j) := by
  have h1 : toStdB (n - 1) (Pi.single j 1) =
      Pi.single j (boolSign true) + Pi.single ⟨j.val + 1, hj⟩ (boolSign false) :=
    toStdB_single_of_lt' n hj
  have h2' : toStdB (n - 1) (-Pi.single j 1) =
      Pi.single ⟨j.val + 1, hj⟩ (boolSign true) + Pi.single j (boolSign false) :=
    toStdB_neg_single_of_lt' n hj
  have e1 : ∀ {x}, x ∈ (minusDatum n hirr).rootGroup (Pi.single j 1) ↔
      ∃ a : F, x = (minusFrame n b c).longRoot (succ_ne_of_lt n hj) true false (.ofAdd a) :=
    fun {x} => mem_minusRootGroup_long_iff n hirr (succ_ne_of_lt n hj) true false h1
  have e2 : ∀ {x}, x ∈ (minusDatum n hirr).rootGroup (-Pi.single j 1) ↔
      ∃ a : F, x = (minusFrame n b c).longRoot (succ_ne_of_lt n hj).symm true false (.ofAdd a) :=
    fun {x} => mem_minusRootGroup_long_iff n hirr (succ_ne_of_lt n hj).symm true false h2'
  have n0j : twIdx0 hn ≠ j := fun h => by
    have := congrArg Fin.val h; simp only [twIdx0] at this; omega
  have n1j : twIdx1 hn ≠ j := fun h => by
    have := congrArg Fin.val h; simp only [twIdx1] at this; omega
  have n0s : twIdx0 hn ≠ (⟨j.val + 1, hj⟩ : Fin (n - 1)) := fun h => by
    have := congrArg Fin.val h; simp only [twIdx0] at this; omega
  have n1s : twIdx1 hn ≠ (⟨j.val + 1, hj⟩ : Fin (n - 1)) := fun h => by
    have := congrArg Fin.val h; simp only [twIdx1] at this; omega
  unfold rankOneHiMinus CurtisTits.rankOne
  refine commutes_sup_sup ?_ ?_ ?_ ?_
  · intro x hx y hy
    obtain ⟨a, rfl⟩ := (mem_rootGroup_hiMinus_iff hirr hn).mp hx
    obtain ⟨d, rfl⟩ := e1.mp hy
    exact (minusFrame n b c).commute_longRoot_longRoot_of_disjoint (twIdx0_ne_twIdx1 hn)
      (succ_ne_of_lt n hj) n0j n0s n1j n1s true true true false a d |>.eq
  · intro x hx y hy
    obtain ⟨a, rfl⟩ := (mem_rootGroup_hiMinus_iff hirr hn).mp hx
    obtain ⟨d, rfl⟩ := e2.mp hy
    exact (minusFrame n b c).commute_longRoot_longRoot_of_disjoint (twIdx0_ne_twIdx1 hn)
      (succ_ne_of_lt n hj).symm n0s n0j n1s n1j true true true false a d |>.eq
  · intro x hx y hy
    obtain ⟨a, rfl⟩ := (mem_rootGroup_neg_hiMinus_iff hirr hn).mp hx
    obtain ⟨d, rfl⟩ := e1.mp hy
    exact (minusFrame n b c).commute_longRoot_longRoot_of_disjoint (twIdx0_ne_twIdx1 hn).symm
      (succ_ne_of_lt n hj) n1j n1s n0j n0s false false true false a d |>.eq
  · intro x hx y hy
    obtain ⟨a, rfl⟩ := (mem_rootGroup_neg_hiMinus_iff hirr hn).mp hx
    obtain ⟨d, rfl⟩ := e2.mp hy
    exact (minusFrame n b c).commute_longRoot_longRoot_of_disjoint (twIdx0_ne_twIdx1 hn).symm
      (succ_ne_of_lt n hj).symm n1s n1j n0s n0j false false true false a d |>.eq

theorem commutes_hiMinus_short (hn : 3 ≤ n) {j : Fin (n - 1)} (hj : ¬ j.val + 1 < n - 1)
    (h2 : 2 ≤ j.val) :
    Commutes (rankOneHiMinus hirr hn) (CurtisTits.rankOne (minusDatum n hirr).rootGroup j) := by
  have e1 : ∀ {x}, x ∈ (minusDatum n hirr).rootGroup (Pi.single j 1) ↔
      ∃ p : Fin 2 → F, x = twShortRoot n hirr j true (.ofAdd p) :=
    fun {x} => mem_minusRootGroup_short_iff n hirr j true (toStdB_single_of_not_lt' n hj)
  have e2 : ∀ {x}, x ∈ (minusDatum n hirr).rootGroup (-Pi.single j 1) ↔
      ∃ p : Fin 2 → F, x = twShortRoot n hirr j false (.ofAdd p) :=
    fun {x} => mem_minusRootGroup_short_iff n hirr j false (toStdB_neg_single_of_not_lt' n hj)
  have n0j : j ≠ twIdx0 hn := fun h => by
    have := congrArg Fin.val h; simp only [twIdx0] at this; omega
  have n1j : j ≠ twIdx1 hn := fun h => by
    have := congrArg Fin.val h; simp only [twIdx1] at this; omega
  unfold rankOneHiMinus CurtisTits.rankOne
  refine commutes_sup_sup ?_ ?_ ?_ ?_
  · intro x hx y hy
    obtain ⟨a, rfl⟩ := (mem_rootGroup_hiMinus_iff hirr hn).mp hx
    obtain ⟨p, rfl⟩ := e1.mp hy
    exact (commute_longRoot_twShortRoot_of_ne n hirr (twIdx0_ne_twIdx1 hn) n0j n1j true true true a
      p).eq
  · intro x hx y hy
    obtain ⟨a, rfl⟩ := (mem_rootGroup_hiMinus_iff hirr hn).mp hx
    obtain ⟨p, rfl⟩ := e2.mp hy
    exact (commute_longRoot_twShortRoot_of_ne n hirr (twIdx0_ne_twIdx1 hn) n0j n1j true true false a
      p).eq
  · intro x hx y hy
    obtain ⟨a, rfl⟩ := (mem_rootGroup_neg_hiMinus_iff hirr hn).mp hx
    obtain ⟨p, rfl⟩ := e1.mp hy
    exact (commute_longRoot_twShortRoot_of_ne n hirr (twIdx0_ne_twIdx1 hn).symm n1j n0j false false
      true a p).eq
  · intro x hx y hy
    obtain ⟨a, rfl⟩ := (mem_rootGroup_neg_hiMinus_iff hirr hn).mp hx
    obtain ⟨p, rfl⟩ := e2.mp hy
    exact (commute_longRoot_twShortRoot_of_ne n hirr (twIdx0_ne_twIdx1 hn).symm n1j n0j false false
      false a p).eq

theorem commutes_rankOneHiMinus (hn : 3 ≤ n) {j : Fin (n - 1)} (h2 : 2 ≤ j.val) :
    Commutes (rankOneHiMinus hirr hn) (CurtisTits.rankOne (minusDatum n hirr).rootGroup j) := by
  by_cases hj : j.val + 1 < n - 1
  · exact commutes_hiMinus_long hirr hn hj h2
  · exact commutes_hiMinus_short hirr hn hj h2

end Commute

section Conj

variable {F : Type} [Field F] {b c : F} (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) {n : ℕ}

theorem twIdx1_ne_twIdx0 (hn : 3 ≤ n) : twIdx1 hn ≠ twIdx0 hn := (twIdx0_ne_twIdx1 hn).symm

theorem shortWeyl_conj_rootGroup_alpha0 (hn : 3 ≤ n) :
    ((minusDatum n hirr).rootGroup (Pi.single (twIdx0 hn) 1)).map
        (MulAut.conj (shortWeyl n hirr (twIdx1 hn))).toMonoidHom =
      (minusDatum n hirr).rootGroup (hiMinus hn) := by
  have hk : (twIdx0 hn).val + 1 < n - 1 := by simp only [twIdx0]; omega
  have hsucc : (⟨(twIdx0 hn).val + 1, hk⟩ : Fin (n - 1)) = twIdx1 hn := rfl
  have h1 : toStdB (n - 1) (Pi.single (twIdx0 hn) 1) =
      Pi.single (twIdx0 hn) (boolSign true) + Pi.single (twIdx1 hn) (boolSign false) := by
    rw [toStdB_single_of_lt' n hk, hsucc]
  have e1 : ∀ {x}, x ∈ (minusDatum n hirr).rootGroup (Pi.single (twIdx0 hn) 1) ↔
      ∃ a : F, x = (minusFrame n b c).longRoot (twIdx0_ne_twIdx1 hn) true false (.ofAdd a) :=
    fun {x} => mem_minusRootGroup_long_iff n hirr (twIdx0_ne_twIdx1 hn) true false h1
  have key := fun a : F =>
    shortWeyl_conj_longRoot n hirr (twIdx1 hn) (twIdx0_ne_twIdx1 hn) true false a
  have hb1 : shortWeylBool (twIdx1 hn) (twIdx0 hn) true = true := by
    simp [shortWeylBool, twIdx0_ne_twIdx1 hn]
  have hb2 : shortWeylBool (twIdx1 hn) (twIdx1 hn) false = true := by simp [shortWeylBool]
  have hs0 : (longWeylSign (twIdx1 hn) (twIdx0 hn) : F) = 1 := by
    simp [longWeylSign, twIdx0_ne_twIdx1 hn]
  have hs1 : (longWeylSign (twIdx1 hn) (twIdx1 hn) : F) = -1 := by simp [longWeylSign]
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨a, rfl⟩ := e1.mp hy
    refine (mem_rootGroup_hiMinus_iff hirr hn).mpr
      ⟨(longWeylSign (twIdx1 hn) (twIdx0 hn) : F) * longWeylSign (twIdx1 hn) (twIdx1 hn) * a, ?_⟩
    change shortWeyl n hirr (twIdx1 hn) * _ * (shortWeyl n hirr (twIdx1 hn))⁻¹ = _
    rw [key a, hb1, hb2]
  · intro hx
    obtain ⟨a, rfl⟩ := (mem_rootGroup_hiMinus_iff hirr hn).mp hx
    refine ⟨(minusFrame n b c).longRoot (twIdx0_ne_twIdx1 hn) true false (.ofAdd (-a)),
      e1.mpr ⟨-a, rfl⟩, ?_⟩
    change shortWeyl n hirr (twIdx1 hn) * _ * (shortWeyl n hirr (twIdx1 hn))⁻¹ = _
    rw [key (-a), hb1, hb2, hs0, hs1]
    congr 2
    ring

theorem shortWeyl_conj_rootGroup_neg_alpha0 (hn : 3 ≤ n) :
    ((minusDatum n hirr).rootGroup (-Pi.single (twIdx0 hn) 1)).map
        (MulAut.conj (shortWeyl n hirr (twIdx1 hn))).toMonoidHom =
      (minusDatum n hirr).rootGroup (-hiMinus hn) := by
  have hk : (twIdx0 hn).val + 1 < n - 1 := by simp only [twIdx0]; omega
  have hsucc : (⟨(twIdx0 hn).val + 1, hk⟩ : Fin (n - 1)) = twIdx1 hn := rfl
  have h2 : toStdB (n - 1) (-Pi.single (twIdx0 hn) 1) =
      Pi.single (twIdx1 hn) (boolSign true) + Pi.single (twIdx0 hn) (boolSign false) := by
    rw [toStdB_neg_single_of_lt' n hk, hsucc]
  have e2 : ∀ {x}, x ∈ (minusDatum n hirr).rootGroup (-Pi.single (twIdx0 hn) 1) ↔
      ∃ a : F, x = (minusFrame n b c).longRoot (twIdx1_ne_twIdx0 hn) true false (.ofAdd a) :=
    fun {x} => mem_minusRootGroup_long_iff n hirr (twIdx1_ne_twIdx0 hn) true false h2
  have key := fun a : F =>
    shortWeyl_conj_longRoot n hirr (twIdx1 hn) (twIdx1_ne_twIdx0 hn) true false a
  have hb1 : shortWeylBool (twIdx1 hn) (twIdx1 hn) true = false := by simp [shortWeylBool]
  have hb2 : shortWeylBool (twIdx1 hn) (twIdx0 hn) false = false := by
    simp [shortWeylBool, twIdx0_ne_twIdx1 hn]
  have hs0 : (longWeylSign (twIdx1 hn) (twIdx0 hn) : F) = 1 := by
    simp [longWeylSign, twIdx0_ne_twIdx1 hn]
  have hs1 : (longWeylSign (twIdx1 hn) (twIdx1 hn) : F) = -1 := by simp [longWeylSign]
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨a, rfl⟩ := e2.mp hy
    refine (mem_rootGroup_neg_hiMinus_iff hirr hn).mpr
      ⟨(longWeylSign (twIdx1 hn) (twIdx1 hn) : F) * longWeylSign (twIdx1 hn) (twIdx0 hn) * a, ?_⟩
    change shortWeyl n hirr (twIdx1 hn) * _ * (shortWeyl n hirr (twIdx1 hn))⁻¹ = _
    rw [key a, hb1, hb2]
  · intro hx
    obtain ⟨a, rfl⟩ := (mem_rootGroup_neg_hiMinus_iff hirr hn).mp hx
    refine ⟨(minusFrame n b c).longRoot (twIdx1_ne_twIdx0 hn) true false (.ofAdd (-a)),
      e2.mpr ⟨-a, rfl⟩, ?_⟩
    change shortWeyl n hirr (twIdx1 hn) * _ * (shortWeyl n hirr (twIdx1 hn))⁻¹ = _
    rw [key (-a), hb1, hb2, hs0, hs1]
    congr 2
    ring

theorem rankOneHiMinus_eq_conj (hn : 3 ≤ n) :
    rankOneHiMinus hirr hn =
      conjSub (shortWeyl n hirr (twIdx1 hn))
        (CurtisTits.rankOne (minusDatum n hirr).rootGroup (twIdx0 hn)) := by
  unfold rankOneHiMinus CurtisTits.rankOne conjSub
  rw [Subgroup.map_sup]
  exact congrArg₂ (· ⊔ ·) (shortWeyl_conj_rootGroup_alpha0 hirr hn).symm
    (shortWeyl_conj_rootGroup_neg_alpha0 hirr hn).symm

end Conj

section Fund

variable {F : Type} [Field F] {b c : F} (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) {n : ℕ}

theorem isLongestRoot_node_minus {k : Fin (n - 1)} (hk : k.val + 1 < n - 1) :
    IsLongestRoot (minusDatum n hirr) (Pi.single k 1) :=
  CFSG.ClassicalInvolution.ModelFacts.isLongest_single_cartanB (m := n - 1) (by omega) rfl _ hk

theorem rankOne_mem_fund_minus {k : Fin (n - 1)} (hk : k.val + 1 < n - 1) :
    CurtisTits.rankOne (minusDatum n hirr).rootGroup k ∈
      fundamentalSubgroups .POmegaMinus (minusDatum n hirr) :=
  ⟨1, Pi.single k 1, Or.inl (isLongestRoot_node_minus hirr hk), by simp [CurtisTits.rankOne]⟩

theorem rankOneHiMinus_mem_fund (hn : 3 ≤ n) :
    rankOneHiMinus hirr hn ∈ fundamentalSubgroups .POmegaMinus (minusDatum n hirr) := by
  have hk : (twIdx0 hn).val + 1 < n - 1 := by simp only [twIdx0]; omega
  exact ⟨shortWeyl n hirr (twIdx1 hn), Pi.single (twIdx0 hn) 1,
    Or.inl (isLongestRoot_node_minus hirr hk), by
      rw [rankOneHiMinus_eq_conj hirr hn]; simp [CurtisTits.rankOne]⟩

theorem finite_spinGroup_quadMinus [Finite F] (n : ℕ) (b c : F) :
    Finite (spinGroup (quadMinus n F b c)) := by
  have : FiniteDimensional F (CliffordAlgebra (quadMinus n F b c)) :=
    finiteDimensional_cliffordAlgebra' _
  have : Finite (CliffordAlgebra (quadMinus n F b c)) := Module.finite_of_finite F
  infer_instance

theorem rankOne_minusDatum_perfect [Finite F] (h4 : 4 ≤ Nat.card F) {k : Fin (n - 1)}
    (hk : k.val + 1 < n - 1) :
    CurtisTits.rankOne (minusDatum n hirr).rootGroup k ≤
      ⁅CurtisTits.rankOne (minusDatum n hirr).rootGroup k,
        CurtisTits.rankOne (minusDatum n hirr).rootGroup k⁆ := by
  have hperf : Group.IsPerfect SL(2, F) := CFSG.ClassicalInvolution.sl2_isPerfect h4
  have h1 : ⁅(⊤ : Subgroup SL(2, F)), (⊤ : Subgroup SL(2, F))⁆ = ⊤ := by
    rw [← commutator_def]
    exact hperf.commutator_eq_top
  rw [CFSG.ClassicalInvolution.WeakCT.rankOne_minusDatum_long hirr hk,
    MonoidHom.range_eq_map, ← Subgroup.map_commutator, h1]

end Fund





end CFSG.ClassicalInvolution.RouteD
