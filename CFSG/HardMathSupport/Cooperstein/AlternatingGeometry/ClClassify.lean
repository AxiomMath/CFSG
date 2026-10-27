module

public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.ClStructure
public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.ClBlockTrivial
public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.ClCellDisjoint
public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.ClCells

public section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Cooperstein.AlternatingGeometry

open Equiv Equiv.Perm MulAction

namespace Classif

open Offender

variable {Ω ι : Type*} [Fintype Ω] [DecidableEq Ω] {W : Subgroup (Perm Ω)}

@[expose] def cellsOf (ω : Perm Ω) (E : ι → Subgroup (Perm Ω)) : Set (Finset Ω) :=
  {F | ∃ i, IsCell ω (E i) F}

theorem cellsOf_omega_closed {ω : Perm Ω} {E : ι → Subgroup (Perm Ω)} :
    ∀ F ∈ cellsOf ω E, ∀ z ∈ F, ω z ∈ F := by
  rintro F ⟨i, hF⟩ z hz
  exact hF.2.1 z hz

theorem cellData_of_offender (hW : IsPGroup 2 W) {E : Subgroup (Perm Ω)} (hEW : E ≤ W)
    (hE : IsExp2 E) (h : OffenderShapeConcl E) (hΛ : ∀ z, partner hW z ≠ z) :
    (∀ e ∈ E, ∀ z, e z = z ∨ e z = partner hW z) ∨ ∃ F, IsCell (partner hW) E F := by
  rcases cell_of_offender hW hEW hE h with h1 | ⟨F, hF1, -, hF2, hF3, hF4, hF5⟩
  · exact Or.inl fun e he z => h1 e he z (hΛ z)
  · exact Or.inr ⟨F, hF1, hF2, hF3, hF4, hF5⟩

structure Pre (W : Subgroup (Perm Ω)) (E : ι → Subgroup (Perm Ω)) : Prop where
  twoGroup : IsPGroup 2 W
  le : ∀ i, E i ≤ W
  sup : W ≤ ⨆ i, E i
  exp : ∀ i, IsExp2 (E i)
  shape : ∀ i, OffenderShapeConcl (E i)

structure Setup (W : Subgroup (Perm Ω)) (E : ι → Subgroup (Perm Ω)) : Prop extends Pre W E where
  matched : ∀ z, partner twoGroup z ≠ z

namespace Pre

variable {E : ι → Subgroup (Perm Ω)} (P : Pre W E)

@[expose] def blkTriv (ω : Perm Ω) (hωω : ∀ x, ω (ω x) = x) : Subgroup (Perm Ω) where
  carrier := {w | (∀ z, ω (w z) = w (ω z)) ∧ ∀ z, ω z ≠ z → w z = z ∨ w z = ω z}
  mul_mem' := by
    rintro a b ⟨ha1, ha2⟩ ⟨hb1, hb2⟩
    refine ⟨fun z => ?_, fun z hz => ?_⟩
    · simp only [Perm.mul_apply]; rw [ha1, hb1]
    · simp only [Perm.mul_apply]
      rcases hb2 z hz with h | h
      · rw [h]; exact ha2 z hz
      · rw [h]
        have hz' : ω (ω z) ≠ ω z := by rw [hωω]; exact Ne.symm hz
        rcases ha2 (ω z) hz' with h' | h'
        · exact Or.inr h'
        · exact Or.inl (by rw [h', hωω])
  one_mem' := ⟨fun z => rfl, fun z _ => Or.inl rfl⟩
  inv_mem' := by
    rintro w ⟨h1, h2⟩
    refine ⟨fun z => ?_, fun z hz => ?_⟩
    · have h4 : w (ω (w⁻¹ z)) = ω z := by rw [← h1]; simp
      have := congrArg (⇑w⁻¹) h4
      simpa using this
    · have hww : w (w⁻¹ z) = z := by simp
      have hu : ω (w⁻¹ z) ≠ w⁻¹ z := by
        intro h
        apply hz
        have := h1 (w⁻¹ z)
        rw [hww, h, hww] at this
        exact this
      rcases h2 (w⁻¹ z) hu with h | h
      · left
        rw [hww] at h
        exact h.symm
      · right
        rw [hww] at h
        have := congrArg ω h
        rw [hωω] at this
        exact this.symm

theorem blockTrivial_of_unmatched (hex : ∃ z, partner P.twoGroup z = z) :
    ∀ w ∈ W, ∀ z, partner P.twoGroup z ≠ z → w z = z ∨ w z = partner P.twoGroup z := by
  have hωω := partner_partner P.twoGroup
  have hle : W ≤ blkTriv (partner P.twoGroup) hωω := by
    refine le_trans P.sup (iSup_le fun i => ?_)
    intro e he
    refine ⟨fun z => partner_comm P.twoGroup (P.le i he) z, fun z hz => ?_⟩
    rcases cell_of_offender P.twoGroup (P.le i) (P.exp i) (P.shape i) with h | ⟨F, -, hm, -⟩
    · exact h e he z hz
    · obtain ⟨z0, hz0⟩ := hex
      exact absurd hz0 (hm z0)
  intro w hw z hz
  exact (hle hw).2 z hz

end Pre

namespace Setup

variable {E : ι → Subgroup (Perm Ω)} (S : Setup W E)

@[expose] noncomputable def ω : Perm Ω := partner S.twoGroup

theorem ωω (x : Ω) : S.ω (S.ω x) = x := partner_partner S.twoGroup x

theorem ωinj {x y : Ω} (h : S.ω x = S.ω y) : x = y := by
  have := congrArg S.ω h
  rwa [S.ωω, S.ωω] at this

theorem comm {w : Perm Ω} (hw : w ∈ W) (z : Ω) : S.ω (w z) = w (S.ω z) :=
  partner_comm S.twoGroup hw z

theorem swap_mem (z : Ω) : swap z (S.ω z) ∈ W := swap_partner_mem S.twoGroup (S.matched z)

theorem hmatch (z : Ω) : S.ω z ≠ z := S.matched z

theorem le_Cst : W ≤ Cst S.ω S.ωω (cellsOf S.ω E) cellsOf_omega_closed := by
  refine le_trans S.sup (iSup_le fun i => ?_)
  intro e he
  have hdata := cellData_of_offender S.twoGroup (S.le i) (S.exp i) (S.shape i) S.matched
  refine ⟨fun z => S.comm (S.le i he) z, fun F hF z hz => ?_, fun z hz => ?_⟩
  · have hωz : S.ω z ∈ F := cellsOf_omega_closed F hF z hz
    rcases hdata with h | ⟨F₀, hF₀⟩
    · rcases h e he z with h' | h'
      · rw [h']; exact hz
      · rw [h']; exact hωz
    · obtain ⟨j, hFj⟩ := hF
      rcases cells_eq_or_disjoint S.twoGroup S.ωω S.hmatch (fun w hw z => S.comm hw z)
        S.swap_mem (S.le i) (S.le j) hF₀ hFj with h' | h'
      · subst h'
        exact hF₀.2.2.1 e he z hz
      · have hz0 : z ∉ F₀ := fun h => Finset.disjoint_left.1 h' h hz
        rcases hF₀.2.2.2.1 e he z hz0 with h'' | h''
        · rw [h'']; exact hz
        · rw [h'']; exact hωz
  · rcases hdata with h | ⟨F₀, hF₀⟩
    · exact h e he z
    · exact hF₀.2.2.2.1 e he z (hz F₀ ⟨i, hF₀⟩)

theorem orbit_of_cell {F : Finset Ω} (hF : F ∈ cellsOf S.ω E) {z : Ω} (hz : z ∈ F) :
    (orbit W z : Set Ω) = ↑F := by
  obtain ⟨i, hFi⟩ := hF
  obtain ⟨e, he, hcr⟩ := cell_cross_all S.ωω S.hmatch (fun e he z => S.comm (S.le i he) z) hFi
  have hFeq := cell_eq_of_mem S.ωω S.hmatch hFi.1 hFi.2.1 (hFi.2.2.1 e he) hcr hz
  ext y
  constructor
  · rintro ⟨⟨w, hw⟩, rfl⟩
    exact S.le_Cst hw |>.2.1 F ⟨i, hFi⟩ z hz
  · intro hy
    have hy' : y ∈ F := hy
    rw [hFeq] at hy'
    simp only [Finset.mem_insert, Finset.mem_singleton] at hy'
    rcases hy' with rfl | rfl | rfl | rfl
    · exact mem_orbit_self _
    · exact ⟨⟨swap z (S.ω z), S.swap_mem z⟩, swap_apply_left _ _⟩
    · exact ⟨⟨e, S.le i he⟩, rfl⟩
    · refine ⟨⟨swap (e z) (S.ω (e z)) * e, W.mul_mem (S.swap_mem _) (S.le i he)⟩, ?_⟩
      show (swap (e z) (S.ω (e z)) * e) z = _
      rw [Perm.mul_apply, swap_apply_left]

theorem orbit_of_nocell {z : Ω} (h : ∀ F ∈ cellsOf S.ω E, z ∉ F) :
    (orbit W z : Set Ω) = {z, S.ω z} := by
  ext y
  constructor
  · rintro ⟨⟨w, hw⟩, rfl⟩
    rcases S.le_Cst hw |>.2.2 z h with h' | h'
    · exact Or.inl h'
    · exact Or.inr h'
  · intro hy
    rcases hy with rfl | rfl
    · exact mem_orbit_self _
    · exact ⟨⟨swap z (S.ω z), S.swap_mem z⟩, swap_apply_left _ _⟩

theorem partner_mem_orbit (z : Ω) : S.ω z ∈ orbit W z := by
  exact ⟨⟨swap z (S.ω z), S.swap_mem z⟩, swap_apply_left _ _⟩

include S in
theorem card_orbit (z : Ω) : Nat.card (orbit W z) = 2 ∨ Nat.card (orbit W z) = 4 := by
  by_cases h : ∃ F ∈ cellsOf S.ω E, z ∈ F
  · obtain ⟨F, hF, hz⟩ := h
    right
    rw [Nat.card_coe_set_eq, S.orbit_of_cell hF hz, Set.ncard_coe_finset]
    obtain ⟨i, hFi⟩ := hF
    exact hFi.1
  · left
    push Not at h
    rw [Nat.card_coe_set_eq, S.orbit_of_nocell h, Set.ncard_pair (S.hmatch z).symm]

@[expose] def moved (ω : Perm Ω) (c : Perm Ω) : Finset Ω :=
  Finset.univ.filter fun z => c z ≠ z ∧ c z ≠ ω z

theorem mem_moved {ω c : Perm Ω} {z : Ω} : z ∈ moved ω c ↔ c z ≠ z ∧ c z ≠ ω z := by
  simp [moved]

theorem eq_orbitStab_inf (hbt : ∀ c : Perm Ω, (∀ z, c z = z ∨ c z = S.ω z) → c ∈ W) :
    W = orbitStab W ⊓ commOmega S.ω := by
  apply le_antisymm
  · intro w hw
    exact ⟨le_orbitStab hw, fun z => S.comm hw z⟩
  rintro c ⟨hc1, hc2⟩
  have key : ∀ n, ∀ c : Perm Ω, c ∈ orbitStab W → c ∈ commOmega S.ω →
      (moved S.ω c).card = n → c ∈ W := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
    intro c hc1 hc2 hn
    by_cases h0 : ∀ z, c z = z ∨ c z = S.ω z
    · exact hbt c h0
    push Not at h0
    obtain ⟨z, hz1, hz2⟩ := h0
    have hcz : c z ∈ orbit W z := hc1 z
    by_cases hcell : ∃ F ∈ cellsOf S.ω E, z ∈ F
    swap
    · exfalso
      push Not at hcell
      have h' : c z ∈ ({z, S.ω z} : Set Ω) := by rw [← S.orbit_of_nocell hcell]; exact hcz
      rcases h' with h' | h'
      · exact hz1 h'
      · exact hz2 h'
    obtain ⟨F, hF, hzF⟩ := hcell
    obtain ⟨i, hFi⟩ := hF
    have hFi' := hFi
    obtain ⟨e, he, hcre⟩ := cell_cross_all S.ωω S.hmatch (fun e he z => S.comm (S.le i he) z) hFi
    obtain ⟨hcard, hωF, hEF, hoff, -⟩ := hFi
    have heW : e ∈ W := S.le i he
    have hcF : ∀ y ∈ F, c y ∈ F := by
      intro y hy
      have : c y ∈ (orbit W y : Set Ω) := hc1 y
      rw [S.orbit_of_cell ⟨i, hFi'⟩ hy] at this
      exact this
    have hcF' : ∀ y, y ∉ F → c y ∉ F := by
      intro y hy hcy
      have h1 : orbit W (c y) = orbit W y := orbit_eq_iff.2 (hc1 y)
      have h2 : y ∈ orbit W (c y) := by rw [h1]; exact mem_orbit_self y
      rw [S.orbit_of_cell ⟨i, hFi'⟩ hcy] at h2
      exact hy h2
    have hccr := cross_all_of_cross S.ωω S.hmatch hcard hωF hcF (fun y => mem_commOmega.1 hc2 y)
      hzF hz1 hz2
    have hbt' := blockTrivial_of_two_cross S.ωω S.hmatch hcard hωF hcF (hEF e he) hccr hcre
    have hinv : ∀ w, w ∉ F → e⁻¹ w = w ∨ e⁻¹ w = S.ω w := by
      intro w hw
      obtain ⟨u, hu0⟩ : ∃ u, e⁻¹ w = u := ⟨_, rfl⟩
      have hw' : e u = w := by rw [← hu0]; simp
      have hu : u ∉ F := fun h => hw (by rw [← hw']; exact hEF e he _ h)
      rw [hu0]
      rcases hoff e he u hu with h | h
      · exact Or.inl (by rw [← h, hw'])
      · right
        have : S.ω w = u := by rw [← hw', h, S.ωω]
        exact this.symm
    have heC : e⁻¹ ∈ commOmega S.ω := (commOmega S.ω).inv_mem (fun z => S.comm heW z)
    have hc'1 : e⁻¹ * c ∈ orbitStab W :=
      (orbitStab W).mul_mem ((orbitStab W).inv_mem (le_orbitStab heW)) hc1
    have hc'2 : e⁻¹ * c ∈ commOmega S.ω := (commOmega S.ω).mul_mem heC hc2
    have hsub : moved S.ω (e⁻¹ * c) ⊆ moved S.ω c := by
      intro y hy
      rw [mem_moved] at hy ⊢
      by_cases hyF : y ∈ F
      · exfalso
        rcases hbt' y hyF with h | h
        · exact hy.1 (by rw [Perm.mul_apply]; exact h)
        · exact hy.2 (by rw [Perm.mul_apply]; exact h)
      · by_contra hnot
        have hnot' : c y = y ∨ c y = S.ω y := by
          by_cases h1 : c y = y
          · exact Or.inl h1
          · exact Or.inr (Classical.byContradiction fun h2 => hnot ⟨h1, h2⟩)
        have hcy : c y ∉ F := hcF' y hyF
        rcases hinv (c y) hcy with h | h
        · rcases hnot' with h' | h'
          · exact hy.1 (by rw [Perm.mul_apply, h, h'])
          · exact hy.2 (by rw [Perm.mul_apply, h, h'])
        · rcases hnot' with h' | h'
          · exact hy.2 (by rw [Perm.mul_apply, h, h'])
          · exact hy.1 (by rw [Perm.mul_apply, h, h', S.ωω])
    have hlt : (moved S.ω (e⁻¹ * c)).card < n := by
      rw [← hn]
      apply Finset.card_lt_card
      rw [Finset.ssubset_iff_of_subset hsub]
      refine ⟨z, mem_moved.2 ⟨hz1, hz2⟩, fun h => ?_⟩
      rw [mem_moved] at h
      rcases hbt' z hzF with h' | h'
      · exact h.1 (by rw [Perm.mul_apply]; exact h')
      · exact h.2 (by rw [Perm.mul_apply]; exact h')
    have hmem := ih _ hlt (e⁻¹ * c) hc'1 hc'2 rfl
    have : c = e * (e⁻¹ * c) := by simp
    rw [this]
    exact W.mul_mem heW hmem
  exact key _ c hc1 hc2 rfl

theorem classification :
    (∀ z : Ω, S.ω z ∈ orbit W z) ∧ (∀ z : Ω, Nat.card (orbit W z) = 2 ∨ Nat.card (orbit W z) = 4) ∧
      W = orbitStab W ⊓ commOmega S.ω :=
  ⟨S.partner_mem_orbit, S.card_orbit,
    S.eq_orbitStab_inf fun _ hc => mem_of_blockTrivial S.ωω S.hmatch S.swap_mem hc⟩

end Setup

end Classif

end CFSG.HardMathSupport.Cooperstein.AlternatingGeometry
