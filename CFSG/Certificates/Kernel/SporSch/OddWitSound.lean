module

public import Certificates.Data.Kernel.SporSch.OddWit
public import Certificates.Data.Odd87F3Check
public import CFSG.Certificates.Kernel.SporSch.ChainKOdd
public import CFSG.Certificates.Kernel.SporSch.ChainKReps

public section

namespace CFSG.KS.SporSch.OddWit

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Raw.Orb CFSG.KS.M11 CFSG.KS.SporSch.MOC
open CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native CFSG.Sporadic.Th
open CFSG.Sporadic.Th.Native Certificates.Odd87F3

variable {n w : Nat}

theorem beq_eq_decide {P Q : Nat} {g h : Equiv.Perm (Fin n)} (hw : 0 < w) (hP : PRep n w P g)
    (hQ : PRep n w Q h) (sP : P >>> (n * w) = 0) (sQ : Q >>> (n * w) = 0) :
    Nat.beq P Q = decide (g = h) := by
  by_cases e : g = h
  · rw [decide_eq_true e]
    have : P = Q := PF.eq_of_fields hw sP sQ fun i hi => by
      rw [hP ⟨i, hi⟩, hQ ⟨i, hi⟩, e]
    rw [this]
    exact Nat.beq_refl _
  · rw [decide_eq_false e]
    cases hb : Nat.beq P Q
    · rfl
    · rw [Nat.eq_of_beq_eq_true hb] at hP
      exact absurd (MOC.prep_unique hP hQ) e

theorem powNe_eq (hsz : szOK n w = true) {y : Nat} {g : Equiv.Perm (Fin n)} (hy : PRep n w y g)
    (e : Nat) : powNe n w e y = decide (g ^ e ≠ 1) := by
  have hf := szOK_facts hsz
  obtain ⟨p1, s1⟩ := prep_powK hsz hy e
  rw [powNe, beq_eq_decide (PF.w_pos hf.2) p1 (prep_pidn hf.1 hf.2) s1 (PF.pidn_shr hf.1 hf.2)]
  by_cases h : g ^ e = 1 <;> simp [h]

theorem pow_ne_of_powNe (hsz : szOK n w = true) {y : Nat} {g : Equiv.Perm (Fin n)}
    (hy : PRep n w y g) {e : Nat} (h : powNe n w e y = true) : g ^ e ≠ 1 := by
  rw [powNe_eq hsz hy] at h
  exact of_decide_eq_true h

theorem prep_cw2 {X C₁ C₂ : Nat} {x c₁ c₂ : Equiv.Perm (Fin n)} (hn : n < 2 ^ 32)
    (hw : n < 2 ^ w) (hX : PRep n w X x) (h₁ : PRep n w C₁ c₁) (h₂ : PRep n w C₂ c₂) :
    PRep n w (cw2 n w (mask w) X C₁ C₂) (x * (c₁ * (x * c₁⁻¹)) * (c₂ * (x * c₂⁻¹))) :=
  prep_pcomp hn (prep_cw1 hn hw hX h₁)
    (prep_pcomp hn h₂ (prep_pcomp hn hX (prep_pinvS hw h₂).1))

theorem exists_of_forall₂_mem {α β : Type*} {R : α → β → Prop} :
    ∀ {l₁ : List α} {l₂ : List β}, List.Forall₂ R l₁ l₂ → ∀ {a}, a ∈ l₁ → ∃ b ∈ l₂, R a b
  | _, _, .nil, _, ha => absurd ha List.not_mem_nil
  | _, _, .cons hab hr, _, ha => by
    rcases List.mem_cons.1 ha with rfl | ha
    · exact ⟨_, List.mem_cons_self, hab⟩
    · obtain ⟨b, hb, h⟩ := exists_of_forall₂_mem hr ha
      exact ⟨b, List.mem_cons_of_mem _ hb, h⟩

theorem witnessOK_of_witPK (hsz : szOK n w = true) {OG : List Nat}
    {og : List (Equiv.Perm (Fin n))} (hOG : List.Forall₂ (PRep n w) OG og) {e X : Nat}
    {x : Equiv.Perm (Fin n)} (hX : PRep n w X x) {T : Table} (hT : Rep n T x)
    (h : witPK n w OG e X = true) :
    witnessOK n e (og.map fun g => (toTable g, toTable g⁻¹)) T = true := by
  have hf := szOK_facts hsz
  have hn : n < 2 ^ 32 := by omega
  have hw : n < 2 ^ w := by omega
  have hpw : ∀ (ws : List Table) (gs : List (Equiv.Perm (Fin n))), List.Forall₂ (Rep n) ws gs →
      gs.prod ^ e ≠ 1 → (!powFixW n ws e) = true := by
    intro ws gs hr hne
    rw [Bool.not_eq_true', ← Bool.not_eq_true, powFixW_iff perm_faithful hr e]
    exact hne
  have hrep : ∀ g : Equiv.Perm (Fin n), Rep n (toTable g) g := rep_toTable hn
  unfold witPK at h
  unfold witnessOK
  rw [Bool.or_eq_true, List.any_eq_true, List.any_eq_true] at h ⊢
  rcases h with ⟨C, hC, hc⟩ | ⟨C₁, hC₁, h⟩
  · obtain ⟨c, hc', pc⟩ := exists_of_forall₂_mem hOG hC
    refine Or.inl ⟨(toTable c, toTable c⁻¹), List.mem_map.2 ⟨c, hc', rfl⟩, ?_⟩
    refine hpw _ [x, c, x, c⁻¹]
      (.cons hT (.cons (hrep c) (.cons hT (.cons (hrep c⁻¹) .nil)))) ?_
    have := pow_ne_of_powNe hsz (prep_cw1 hn hw hX pc) hc
    simpa [List.prod_cons, mul_assoc] using this
  · rw [List.any_eq_true] at h
    obtain ⟨C₂, hC₂, hc⟩ := h
    obtain ⟨c₁, hc₁, p₁⟩ := exists_of_forall₂_mem hOG hC₁
    obtain ⟨c₂, hc₂, p₂⟩ := exists_of_forall₂_mem hOG hC₂
    refine Or.inr ⟨(toTable c₁, toTable c₁⁻¹), List.mem_map.2 ⟨c₁, hc₁, rfl⟩, ?_⟩
    rw [List.any_eq_true]
    refine ⟨(toTable c₂, toTable c₂⁻¹), List.mem_map.2 ⟨c₂, hc₂, rfl⟩, ?_⟩
    refine hpw _ [x, c₁, x, c₁⁻¹, c₂, x, c₂⁻¹]
      (.cons hT (.cons (hrep c₁) (.cons hT (.cons (hrep c₁⁻¹) (.cons (hrep c₂) (.cons hT
        (.cons (hrep c₂⁻¹) .nil))))))) ?_
    have := pow_ne_of_powNe hsz (prep_cw2 hn hw hX p₁ p₂) hc
    simpa [List.prod_cons, mul_assoc] using this

theorem witPK_of_rowsPK {rows : List (Nat × Nat × List Nat)} {X : Nat}
    {x : Equiv.Perm (Fin n)} (hX : PRep n w X x) (h : rowsPK n w rows X = true)
    {r : Nat × Nat × List Nat} (hr : r ∈ rows) (ho : orderOf x = r.1) :
    witPK n w r.2.2 r.2.1 X = true := by
  have e : rowsPK n w rows X = rows.all fun r => !Nat.beq (ordC n w (mask w) X) r.1 ||
      witPK n w r.2.2 r.2.1 X := by
    unfold rowsPK
    cases ordC n w (mask w) X <;> rfl
  rw [e, List.all_eq_true] at h
  have h1 := h r hr
  rw [← orderOf_of_ordC hX, ho, Nat.beq_refl] at h1
  simpa using h1

theorem rowsPK_of_invCandK {gA gB : Equiv.Perm (Fin n)} {A Ai B Bi : Nat} (hn : n < 2 ^ 32)
    (pA : PRep n w A gA) (pAi : PRep n w Ai gA⁻¹) (pB : PRep n w B gB) (pBi : PRep n w Bi gB⁻¹)
    {mx cap : Nat} {d : ClsD} (hd : clsHdK n w (mask w) mx cap d = true)
    (he : ∀ k < d.c, clsElemK n w (mask w) (n * w) A Ai B Bi d k = true)
    {r : Equiv.Perm (Fin n)} (pR : PRep n w d.R r) {rows : List (Nat × Nat × List Nat)}
    {Ui : Nat} {u : Equiv.Perm (Fin n)} (pU : PRep n w Ui u⁻¹)
    (h : invCandK n w rows Ui d = true) {x : Equiv.Perm (Fin n)}
    (hx : u * x = 1 ∨ u * x ∈ CFSG.Sporadic.SmallOddCore.conjClass
      (Subgroup.closure ({gA, gB} : Set (Equiv.Perm (Fin n)))) r) :
    ∃ X, PRep n w X x ∧ rowsPK n w rows X = true := by
  unfold invCandK at h
  rw [Bool.and_eq_true] at h
  have hxu : x = u⁻¹ * (u * x) := by group
  rcases hx with h1 | hc
  · refine ⟨Ui, ?_, h.1⟩
    rw [hxu, h1, mul_one]
    exact pU
  · obtain ⟨k, hk, pk⟩ := (mem_class_iff hn pA pAi pB pBi hd he pR _).1 hc
    refine ⟨pcomp n w (mask w) Ui (d.ST k), ?_, allN_spec h.2 k hk⟩
    rw [hxu]
    exact prep_pcomp hn pU pk

end CFSG.KS.SporSch.OddWit

end
