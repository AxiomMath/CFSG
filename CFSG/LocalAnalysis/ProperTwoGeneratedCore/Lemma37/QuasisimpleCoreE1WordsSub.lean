module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.QuasisimpleCoreE1WordsLabels

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore

variable {G : Type} [Group G] {T Q P₁ S : Subgroup G} {e u y x m : G}

@[expose] noncomputable def e1WordSubgroup (Z : Subgroup G) [Z.Normal] (u m y x : G)
    (P : Fin 64 → Prop) : Subgroup (G ⧸ Z) :=
  Subgroup.closure {s | ∃ v, P v ∧ caseC3Word Z u m y x v = s}

@[expose] noncomputable def e1RBar (Z : Subgroup G) [Z.Normal] (u m y x : G) : Subgroup (G ⧸ Z) :=
  e1WordSubgroup Z u m y x e1R

@[expose] noncomputable def e1EBar (Z : Subgroup G) [Z.Normal] (u m y x : G) : Subgroup (G ⧸ Z) :=
  e1WordSubgroup Z u m y x e1E

namespace CaseC3BCD

variable {Z : Subgroup G} [Z.Normal] (hb : CaseC3BCD T Q P₁ S e u y x m Z) [Finite G]
include hb

theorem mem_e1WordSubgroup_iff {P : Fin 64 → Prop} (h0 : P 0)
    (hmul : ∀ v w, P v → P w → P (c3Mul v w)) {s : G ⧸ Z} :
    s ∈ e1WordSubgroup Z u m y x P ↔ ∃ v, P v ∧ caseC3Word Z u m y x v = s := by
  refine ⟨fun hs => ?_, fun hs => Subgroup.subset_closure hs⟩
  let K : Subgroup (G ⧸ Z) :=
    { carrier := {s | ∃ v, P v ∧ caseC3Word Z u m y x v = s}
      mul_mem' := by
        rintro _ _ ⟨v, hv, rfl⟩ ⟨w, hw, rfl⟩
        exact ⟨c3Mul v w, hmul v w hv hw, (hb.caseC3Word_mul v w).symm⟩
      one_mem' := ⟨0, h0, caseC3Word_zero⟩
      inv_mem' := by
        rintro _ ⟨v, hv, rfl⟩
        exact ⟨c3Inv v, hmul _ _ (hmul _ _ hv hv) hv, (hb.caseC3Word_inv v).symm⟩ }
  exact (Subgroup.closure_le K).mpr (fun s hs => hs) hs

theorem caseC3Word_mem_e1WordSubgroup_iff {P : Fin 64 → Prop} (h0 : P 0)
    (hmul : ∀ v w, P v → P w → P (c3Mul v w)) {v : Fin 64} :
    caseC3Word Z u m y x v ∈ e1WordSubgroup Z u m y x P ↔ P v := by
  rw [hb.mem_e1WordSubgroup_iff h0 hmul]
  exact ⟨fun ⟨w, hw, hwv⟩ => hb.caseC3Word_inj.mp hwv ▸ hw, fun hv => ⟨v, hv, rfl⟩⟩

theorem e1WordSubgroup_le (P : Fin 64 → Prop) :
    e1WordSubgroup Z u m y x P ≤ S.map (QuotientGroup.mk' Z) :=
  (Subgroup.closure_le _).mpr (by
    rintro _ ⟨v, -, rfl⟩
    exact hb.caseC3Word_mem v)

theorem card_subtype_eq {P : G ⧸ Z → Prop} {R : Fin 64 → Prop} [DecidablePred R]
    (hPS : ∀ s, P s → s ∈ S.map (QuotientGroup.mk' Z))
    (hPR : ∀ v, P (caseC3Word Z u m y x v) ↔ R v) :
    Nat.card {s // P s} = (Finset.univ.filter R).card := by
  rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
  refine (Nat.card_congr (Equiv.ofBijective
    (fun v : {v // R v} => (⟨caseC3Word Z u m y x v.1, (hPR v.1).mpr v.2⟩ : {s // P s}))
    ⟨fun v w h => Subtype.ext (hb.caseC3Word_inj.mp (congrArg Subtype.val h)), fun s => ?_⟩)).symm
  obtain ⟨v, hv⟩ := hb.exists_caseC3Word (hPS s.1 s.2)
  exact ⟨⟨v, (hPR v).mp (hv ▸ s.2)⟩, Subtype.ext hv⟩

theorem card_e1WordSubgroup {P : Fin 64 → Prop} [DecidablePred P] (h0 : P 0)
    (hmul : ∀ v w, P v → P w → P (c3Mul v w)) :
    Nat.card (e1WordSubgroup Z u m y x P) = (Finset.univ.filter P).card :=
  hb.card_subtype_eq (fun _ hs => hb.e1WordSubgroup_le P hs)
    (fun _ => hb.caseC3Word_mem_e1WordSubgroup_iff h0 hmul)

omit [Finite G] in
theorem mk_eq_one_of_mem_left_of_mem_map {q : G} (hq : q ∈ Q)
    (hqP : (q : G ⧸ Z) ∈ P₁.map (QuotientGroup.mk' Z)) : (q : G ⧸ Z) = 1 := by
  obtain ⟨p, hp, hpq⟩ := hqP
  have hqP' : q ∈ P₁ := by
    rw [show q = p * (p⁻¹ * q) by group]
    exact P₁.mul_mem hp (hb.le_right (QuotientGroup.eq.mp hpq))
  rcases hb.partC.mem_inf q hq hqP' with h | h
  · rw [h, QuotientGroup.mk_one]
  · rw [h, hb.mk_centralElt]

omit [Finite G] in
theorem mk_eq_one_of_mem_right_of_mem_map {p : G} (hp : p ∈ P₁)
    (hpQ : (p : G ⧸ Z) ∈ Q.map (QuotientGroup.mk' Z)) : (p : G ⧸ Z) = 1 := by
  obtain ⟨q, hq, hqp⟩ := hpQ
  have hpQ' : p ∈ Q := by
    rw [show p = q * (q⁻¹ * p) by group]
    exact Q.mul_mem hq (hb.le_left (QuotientGroup.eq.mp hqp))
  rcases hb.partC.mem_inf p hpQ' hp with h | h
  · rw [h, QuotientGroup.mk_one]
  · rw [h, hb.mk_centralElt]

omit [Finite G] in
theorem caseC3Word_mem_map_right_iff {v : Fin 64} :
    caseC3Word Z u m y x v ∈ P₁.map (QuotientGroup.mk' Z) ↔ v.val % 16 = 0 := by
  have hw := caseC3Word_eq (Z := Z) (u := u) (m := m) (y := y) (x := x) v
  constructor
  · intro h
    have h4 : v.val % 4 = 0 := hb.caseC3Word_mem_sup_iff.mp (Subgroup.map_mono le_sup_right h)
    rw [show v.val / 2 % 2 = 0 by omega, show v.val % 2 = 0 by omega, pow_zero, pow_zero, mul_one,
      mul_one] at hw
    have hp : ((u ^ (v.val / 32 % 2) * m ^ (v.val / 16 % 2) : G) : G ⧸ Z) ∈
        P₁.map (QuotientGroup.mk' Z) := Subgroup.mem_map_of_mem _ (hb.pPart_mem _ _)
    have hq := (P₁.map (QuotientGroup.mk' Z)).mul_mem ((P₁.map (QuotientGroup.mk' Z)).inv_mem hp) h
    rw [hw, ← mul_assoc, inv_mul_cancel, one_mul] at hq
    have := hb.qPart_mk_eq_one (Nat.mod_lt _ (by norm_num)) (Nat.mod_lt _ (by norm_num))
      (hb.mk_eq_one_of_mem_left_of_mem_map (hb.qPart_mem _ _) hq)
    omega
  · intro h
    rw [hw, show v.val / 8 % 2 = 0 by omega, show v.val / 4 % 2 = 0 by omega,
      show v.val / 2 % 2 = 0 by omega, show v.val % 2 = 0 by omega]
    simp only [pow_zero, mul_one, QuotientGroup.mk_one]
    exact Subgroup.mem_map_of_mem _ (hb.pPart_mem _ _)

omit [Finite G] in
theorem caseC3Word_mem_map_left_iff {v : Fin 64} :
    caseC3Word Z u m y x v ∈ Q.map (QuotientGroup.mk' Z) ↔ v.val < 16 ∧ v.val % 4 = 0 := by
  have hw := caseC3Word_eq (Z := Z) (u := u) (m := m) (y := y) (x := x) v
  constructor
  · intro h
    have h4 : v.val % 4 = 0 := hb.caseC3Word_mem_sup_iff.mp (Subgroup.map_mono le_sup_left h)
    rw [show v.val / 2 % 2 = 0 by omega, show v.val % 2 = 0 by omega, pow_zero, pow_zero, mul_one,
      mul_one] at hw
    have hq : (((x * u * x⁻¹) ^ (v.val / 8 % 2) * (x * m * x⁻¹) ^ (v.val / 4 % 2) : G) :
        G ⧸ Z) ∈ Q.map (QuotientGroup.mk' Z) := Subgroup.mem_map_of_mem _ (hb.qPart_mem _ _)
    have hp := (Q.map (QuotientGroup.mk' Z)).mul_mem h ((Q.map (QuotientGroup.mk' Z)).inv_mem hq)
    rw [hw, mul_inv_cancel_right] at hp
    have := hb.pPart_mk_eq_one (Nat.mod_lt _ (by norm_num)) (Nat.mod_lt _ (by norm_num))
      (hb.mk_eq_one_of_mem_right_of_mem_map (hb.pPart_mem _ _) hp)
    omega
  · rintro ⟨h16, h4⟩
    rw [hw, show v.val / 32 % 2 = 0 by omega, show v.val / 16 % 2 = 0 by omega,
      show v.val / 2 % 2 = 0 by omega, show v.val % 2 = 0 by omega]
    simp only [pow_zero, mul_one, QuotientGroup.mk_one, one_mul]
    exact Subgroup.mem_map_of_mem _ (hb.qPart_mem _ _)

theorem mem_e1RBar_iff {s : G ⧸ Z} :
    s ∈ e1RBar Z u m y x ↔ ∃ v, e1R v ∧ caseC3Word Z u m y x v = s :=
  hb.mem_e1WordSubgroup_iff e1R_zero e1R_mul

theorem caseC3Word_mem_e1RBar_iff {v : Fin 64} :
    caseC3Word Z u m y x v ∈ e1RBar Z u m y x ↔ e1R v :=
  hb.caseC3Word_mem_e1WordSubgroup_iff e1R_zero e1R_mul

theorem e1RBar_le : e1RBar Z u m y x ≤ S.map (QuotientGroup.mk' Z) := hb.e1WordSubgroup_le _

theorem card_e1RBar : Nat.card (e1RBar Z u m y x) = 32 :=
  (hb.card_e1WordSubgroup e1R_zero e1R_mul).trans card_e1R

theorem forty_mem_e1RBar : caseC3Word Z u m y x 40 ∈ e1RBar Z u m y x :=
  hb.caseC3Word_mem_e1RBar_iff.mpr e1R_forty

theorem forall_commute_e1RBar_iff {s : G ⧸ Z} (hs : s ∈ e1RBar Z u m y x) :
    (∀ t ∈ e1RBar Z u m y x, s * t = t * s) ↔ s = 1 ∨ s = caseC3Word Z u m y x 40 := by
  obtain ⟨v, hv, rfl⟩ := hb.mem_e1RBar_iff.mp hs
  rw [hb.caseC3Word_eq_one_iff, hb.caseC3Word_inj, ← e1R_center_iff v hv]
  refine ⟨fun h w hw => ?_, fun h t ht => ?_⟩
  · rw [← hb.caseC3Word_inj, ← hb.caseC3Word_mul, ← hb.caseC3Word_mul]
    exact h _ (hb.caseC3Word_mem_e1RBar_iff.mpr hw)
  · obtain ⟨w, hw, rfl⟩ := hb.mem_e1RBar_iff.mp ht
    rw [hb.caseC3Word_mul, hb.caseC3Word_mul, h w hw]

theorem mul_self_of_mem_e1RBar {s : G ⧸ Z} (hs : s ∈ e1RBar Z u m y x) :
    s * s = 1 ∨ s * s = caseC3Word Z u m y x 40 := by
  obtain ⟨v, hv, rfl⟩ := hb.mem_e1RBar_iff.mp hs
  rw [hb.caseC3Word_mul, hb.caseC3Word_eq_one_iff, hb.caseC3Word_inj]
  exact e1R_mul_self v hv

theorem commute_or_of_mem_e1RBar {s t : G ⧸ Z} (hs : s ∈ e1RBar Z u m y x)
    (ht : t ∈ e1RBar Z u m y x) : s * t = t * s ∨ s * t = t * s * caseC3Word Z u m y x 40 := by
  obtain ⟨v, hv, rfl⟩ := hb.mem_e1RBar_iff.mp hs
  obtain ⟨w, hw, rfl⟩ := hb.mem_e1RBar_iff.mp ht
  simp only [hb.caseC3Word_mul, hb.caseC3Word_inj]
  exact e1R_comm v w hv hw

theorem mem_e1EBar_iff {s : G ⧸ Z} :
    s ∈ e1EBar Z u m y x ↔ ∃ v, e1E v ∧ caseC3Word Z u m y x v = s :=
  hb.mem_e1WordSubgroup_iff e1E_zero e1E_mul

theorem caseC3Word_mem_e1EBar_iff {v : Fin 64} :
    caseC3Word Z u m y x v ∈ e1EBar Z u m y x ↔ e1E v :=
  hb.caseC3Word_mem_e1WordSubgroup_iff e1E_zero e1E_mul

theorem card_e1EBar : Nat.card (e1EBar Z u m y x) = 8 :=
  (hb.card_e1WordSubgroup e1E_zero e1E_mul).trans card_e1E

theorem e1EBar_le_e1RBar : e1EBar Z u m y x ≤ e1RBar Z u m y x := fun s hs => by
  obtain ⟨v, hv, rfl⟩ := hb.mem_e1EBar_iff.mp hs
  exact hb.caseC3Word_mem_e1RBar_iff.mpr (e1R_of_e1E v hv)

theorem forty_mem_e1EBar : caseC3Word Z u m y x 40 ∈ e1EBar Z u m y x :=
  hb.caseC3Word_mem_e1EBar_iff.mpr e1E_gens.2.2.2

theorem mul_self_of_mem_e1EBar {s : G ⧸ Z} (hs : s ∈ e1EBar Z u m y x) : s * s = 1 := by
  obtain ⟨v, hv, rfl⟩ := hb.mem_e1EBar_iff.mp hs
  rw [hb.caseC3Word_mul_self_eq_one_iff]
  exact e1E_mul_self v hv

theorem commute_of_mem_e1EBar {s t : G ⧸ Z} (hs : s ∈ e1EBar Z u m y x)
    (ht : t ∈ e1EBar Z u m y x) : s * t = t * s := by
  obtain ⟨v, hv, rfl⟩ := hb.mem_e1EBar_iff.mp hs
  obtain ⟨w, hw, rfl⟩ := hb.mem_e1EBar_iff.mp ht
  rw [hb.caseC3Word_mul, hb.caseC3Word_mul, e1E_comm v w hv hw]

theorem conj_mem_e1EBar {s t : G ⧸ Z} (hs : s ∈ S.map (QuotientGroup.mk' Z))
    (ht : t ∈ e1EBar Z u m y x) : s * t * s⁻¹ ∈ e1EBar Z u m y x := by
  obtain ⟨v, rfl⟩ := hb.exists_caseC3Word hs
  obtain ⟨w, hw, rfl⟩ := hb.mem_e1EBar_iff.mp ht
  rw [hb.caseC3Word_conj]
  exact hb.caseC3Word_mem_e1EBar_iff.mpr (e1E_conj v w hw)

theorem mem_e1EBar_of_forall_commute {s : G ⧸ Z} (hs : s ∈ S.map (QuotientGroup.mk' Z))
    (hc : ∀ t ∈ e1EBar Z u m y x, s * t = t * s) : s ∈ e1EBar Z u m y x := by
  obtain ⟨v, rfl⟩ := hb.exists_caseC3Word hs
  refine hb.caseC3Word_mem_e1EBar_iff.mpr (e1E_of_comm v fun w hw => ?_)
  rw [← hb.caseC3Word_inj, ← hb.caseC3Word_mul, ← hb.caseC3Word_mul]
  exact hc _ (hb.caseC3Word_mem_e1EBar_iff.mpr hw)

theorem e1EBar_eq_closure : e1EBar Z u m y x = Subgroup.closure
    {(u : G ⧸ Z), ((x * u * x⁻¹ : G) : G ⧸ Z), (y : G ⧸ Z)} := by
  apply le_antisymm
  · intro s hs
    obtain ⟨v, hv, rfl⟩ := hb.mem_e1EBar_iff.mp hs
    have hmem : ∀ w : Fin 64, (w = 0 ∨ w = 32 ∨ w = 8 ∨ w = 2) → caseC3Word Z u m y x w ∈
        Subgroup.closure {(u : G ⧸ Z), ((x * u * x⁻¹ : G) : G ⧸ Z), (y : G ⧸ Z)} := by
      rintro w (rfl | rfl | rfl | rfl)
      · rw [caseC3Word_zero]
        exact Subgroup.one_mem _
      · rw [caseC3Word_thirtytwo]
        exact Subgroup.subset_closure (by simp)
      · rw [caseC3Word_eight]
        exact Subgroup.subset_closure (by simp)
      · rw [caseC3Word_two]
        exact Subgroup.subset_closure (by simp)
    rw [e1E_eq_mul v hv, ← hb.caseC3Word_mul, ← hb.caseC3Word_mul]
    refine Subgroup.mul_mem _ (Subgroup.mul_mem _ (hmem _ ?_) (hmem _ ?_)) (hmem _ ?_) <;>
      split_ifs <;> simp
  · rw [Subgroup.closure_le]
    rintro s (rfl | rfl | rfl)
    · rw [← caseC3Word_thirtytwo (Z := Z) (m := m) (y := y) (x := x)]
      exact hb.caseC3Word_mem_e1EBar_iff.mpr e1E_gens.1
    · rw [← caseC3Word_eight (Z := Z) (m := m) (y := y)]
      exact hb.caseC3Word_mem_e1EBar_iff.mpr e1E_gens.2.1
    · rw [← caseC3Word_two (Z := Z) (u := u) (m := m) (x := x)]
      exact hb.caseC3Word_mem_e1EBar_iff.mpr e1E_gens.2.2.1

end CaseC3BCD

end CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore
