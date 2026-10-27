module

public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.OffenderMaster

public section

namespace CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.Offender

open Equiv Equiv.Perm MulAction

set_option linter.unusedSectionVars false

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω] {E : Subgroup (Perm Ω)}

@[expose] def orbitStab (E : Subgroup (Perm Ω)) : Subgroup (Perm Ω) where
  carrier := {σ | ∀ i, σ i ∈ orbit E i}
  mul_mem' := by
    intro σ τ hσ hτ i
    have h1 : τ i ∈ orbit E i := hτ i
    have h2 : σ (τ i) ∈ orbit E (τ i) := hσ (τ i)
    have h3 : orbit E (τ i) = orbit E i := orbit_eq_iff.2 (by simpa using h1)
    show σ (τ i) ∈ orbit E i
    rw [← h3]; exact h2
  one_mem' := fun i => mem_orbit_self i
  inv_mem' := by
    intro σ hσ i
    have h1 : σ (σ⁻¹ i) ∈ orbit E (σ⁻¹ i) := hσ (σ⁻¹ i)
    have h1' : i ∈ orbit E (σ⁻¹ i) := by simpa using h1
    have h3 : orbit E i = orbit E (σ⁻¹ i) := orbit_eq_iff.2 h1'
    show σ⁻¹ i ∈ orbit E i
    rw [h3]; exact mem_orbit_self _

theorem mem_orbitStab {σ : Perm Ω} : σ ∈ orbitStab E ↔ ∀ i, σ i ∈ orbit E i := Iff.rfl

theorem le_orbitStab : E ≤ orbitStab E := fun g hg _ => ⟨⟨g, hg⟩, rfl⟩

@[expose] noncomputable def evalOrb (E : Subgroup (Perm Ω)) (H : Subgroup (Perm Ω)) (hH : H ≤ orbitStab E) :
    H → ∀ ω : Orb E, orbit E ω.out :=
  fun h ω => ⟨(h : Perm Ω) ω.out, hH h.2 _⟩

theorem mem_orbit_out (i : Ω) : i ∈ orbit E (Quotient.mk'' i : Orb E).out := by
  have h' : (orbitRel E Ω) i (Quotient.mk'' i : Orb E).out :=
    Quotient.exact' (Quotient.out_eq' (Quotient.mk'' i)).symm
  exact orbitRel_apply.1 h'

theorem evalOrb_injective_E (hE : IsExp2 E) :
    Function.Injective (evalOrb E E le_orbitStab) := by
  intro a b h
  have hpt : ∀ ω : Orb E, (a : Perm Ω) ω.out = (b : Perm Ω) ω.out := fun ω =>
    congrArg Subtype.val (congrFun h ω)
  apply Subtype.ext
  ext q
  obtain ⟨h0, hh0⟩ := mem_orbit_out (E := E) q
  have hp := hpt (Quotient.mk'' q)
  generalize (Quotient.mk'' q : Orb E).out = x at hh0 hp
  have key : ∀ y : E, (y : Perm Ω) q = (h0 : Perm Ω) ((y : Perm Ω) x) := by
    intro y
    rw [← hh0]
    show ((y : Perm Ω) * (h0 : Perm Ω)) x = ((h0 : Perm Ω) * (y : Perm Ω)) x
    rw [hE.comm y.2 h0.2]
  rw [key a, key b, hp]

theorem eq_of_mem_of_ncard_le {α : Type*} {s : Set α} (hfin : s.Finite) (h2 : s.ncard ≤ 2)
    {a b : α} (ha : a ∈ s) (hb : b ∈ s) (hab : a ≠ b) {y : α} (hy : y ∈ s) : y = a ∨ y = b := by
  by_contra hne
  push Not at hne
  have : 2 < s.ncard := (Set.two_lt_ncard hfin).2 ⟨y, hy, a, ha, b, hb, hne.1, hne.2, hab⟩
  omega

theorem evalOrb_injective_K (hsmall : ∀ i : Ω, Nat.card (orbit E i) ≤ 2) :
    Function.Injective (evalOrb E (orbitStab E) le_rfl) := by
  intro a b h
  have hpt : ∀ ω : Orb E, (a : Perm Ω) ω.out = (b : Perm Ω) ω.out := fun ω =>
    congrArg Subtype.val (congrFun h ω)
  apply Subtype.ext
  have hρ : ∀ x, ((b : Perm Ω)⁻¹ * (a : Perm Ω)) x = x := by
    intro x
    set ω : Orb E := Quotient.mk'' x with hω
    have hx : x ∈ orbit E ω.out := mem_orbit_out x
    have hρo : ((b : Perm Ω)⁻¹ * (a : Perm Ω)) ω.out = ω.out := by
      rw [Perm.mul_apply, hpt ω]; simp
    by_cases hxo : x = ω.out
    · rw [hxo]; exact hρo
    · have hmem : ((b : Perm Ω)⁻¹ * (a : Perm Ω)) x ∈ orbit E ω.out := by
        have h1 : ((b : Perm Ω)⁻¹ * (a : Perm Ω)) ∈ orbitStab E :=
          (orbitStab E).mul_mem ((orbitStab E).inv_mem b.2) a.2
        have h2 := h1 x
        have h3 : orbit E x = orbit E ω.out := orbit_eq_iff.2 hx
        rw [← h3]; exact h2
      have hfin : (orbit E ω.out : Set Ω).Finite := Set.toFinite _
      have hcard : (orbit E ω.out : Set Ω).ncard ≤ 2 := by
        rw [← Nat.card_coe_set_eq]; exact hsmall _
      rcases eq_of_mem_of_ncard_le hfin hcard (mem_orbit_self _) hx (Ne.symm hxo) hmem with h4 | h4
      · exfalso
        apply hxo
        have : ((b : Perm Ω)⁻¹ * (a : Perm Ω)) x = ((b : Perm Ω)⁻¹ * (a : Perm Ω)) ω.out := by
          rw [h4, hρo]
        exact ((b : Perm Ω)⁻¹ * (a : Perm Ω)).injective this
      · exact h4
  ext x
  have := hρ x
  rw [Perm.mul_apply] at this
  have h5 := congrArg (b : Perm Ω) this
  simpa using h5

theorem fixed_of_card_orbit_eq_one {p : Ω} (h : Nat.card (orbit E p) = 1) :
    ∀ g ∈ E, g p = p := by
  intro g hg
  have hu := Nat.card_eq_one_iff_unique.1 h
  have := hu.1
  have : (⟨g p, ⟨⟨g, hg⟩, rfl⟩⟩ : orbit E p) = ⟨p, mem_orbit_self p⟩ := Subsingleton.elim _ _
  exact congrArg Subtype.val this

theorem card_orbit_eq_two_pow {m : Orb E → ℕ}
    (hm : ∀ ω : Orb E, Nat.card (orbit E ω.out) = 2 ^ m ω) (i : Ω) :
    Nat.card (orbit E i) = 2 ^ m (Quotient.mk'' i) := by
  have : orbit E i = orbit E (Quotient.mk'' i : Orb E).out := orbit_eq_iff.2 (mem_orbit_out i)
  rw [this]; exact hm _

theorem card_pi_orbits {m : Orb E → ℕ} (hm : ∀ ω : Orb E, Nat.card (orbit E ω.out) = 2 ^ m ω) :
    Nat.card (∀ ω : Orb E, orbit E ω.out) = 2 ^ ∑ ω, m ω := by
  rw [Nat.card_pi, Finset.prod_congr rfl fun ω _ => hm ω, Finset.prod_pow_eq_pow_sum]

@[expose] def OffenderShapeConcl (E : Subgroup (Perm Ω)) : Prop :=
  ((∃ p, ∀ g ∈ E, g p = p) → (∀ i : Ω, Nat.card (orbit E i) ≤ 2) ∧ E = orbitStab E) ∧
  ((¬ ∃ p, ∀ g ∈ E, g p = p) →
    ((∀ i : Ω, Nat.card (orbit E i) = 2) ∧ Nat.card (orbitStab E) ≤ 2 * Nat.card E) ∨
    ((∃ i : Ω, Nat.card (orbit E i) = 4) ∧
      (∀ i : Ω, Nat.card (orbit E i) = 2 ∨ Nat.card (orbit E i) = 4) ∧
      (∀ i j : Ω, Nat.card (orbit E i) = 4 → Nat.card (orbit E j) = 4 → j ∈ orbit E i) ∧
      Function.Bijective (evalOrb E E le_orbitStab)))

theorem offender_shape [Nonempty Ω] (hE : IsExp2 E) (hoff : offIdx E ≤ Nat.card E)
    (hn : Nat.card Ω = 7 ∨ 9 ≤ Nat.card Ω) : OffenderShapeConcl E := by
  unfold OffenderShapeConcl
  classical
  obtain ⟨m, hm, hE', hid, hm2, hm3, hfix, hnofix⟩ := numerics hE hoff hn
  have hpi := card_pi_orbits hm
  generalize hM : ∑ ω, m ω = M at hE' hid hpi
  generalize hR : Nat.card (Orb E) = R at hid hfix hnofix
  have hr : 0 < 2 ^ R := by positivity
  have hK : (∀ i : Ω, Nat.card (orbit E i) ≤ 2) → Nat.card (orbitStab E) ≤ 2 ^ M := by
    intro hsmall
    have := Nat.card_le_card_of_injective _ (evalOrb_injective_K hsmall)
    rwa [hpi] at this
  refine ⟨?_, ?_⟩
  · intro hf
    obtain ⟨hm1, h2⟩ := hfix hf
    have hsmall : ∀ i : Ω, Nat.card (orbit E i) ≤ 2 := fun i => by
      rw [card_orbit_eq_two_pow hm]
      calc 2 ^ m (Quotient.mk'' i) ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) (hm1 _)
        _ = 2 := by norm_num
    refine ⟨hsmall, ?_⟩
    have hG : ∑ ω, gx (m ω) = 0 :=
      Finset.sum_eq_zero fun ω _ => (gx_eq_zero_iff _).2 (hm1 ω)
    have hge : 2 ^ M ≤ Nat.card E := by
      rw [hG, zero_add] at hid
      rw [hid, pow_add] at h2
      refine Nat.le_of_mul_le_mul_left (c := 2 ^ R) ?_ hr
      calc 2 ^ R * 2 ^ M = 2 ^ M * 2 ^ R := by ring
        _ ≤ 2 ^ R * Nat.card E := h2
    exact Subgroup.eq_of_le_of_card_ge le_orbitStab (le_trans (hK hsmall) hge)
  · intro hnf
    have h2 := hnofix hnf
    have hpos : ∀ ω : Orb E, 1 ≤ m ω := by
      intro ω
      by_contra hlt
      have h0 : m ω = 0 := by omega
      have h1 : Nat.card (orbit E ω.out) = 1 := by rw [hm, h0]; rfl
      exact hnf ⟨ω.out, fixed_of_card_orbit_eq_one h1⟩
    by_cases hbig : ∃ ω0, m ω0 = 2
    · right
      obtain ⟨ω0, h0⟩ := hbig
      have hother : ∀ ω, ω ≠ ω0 → m ω = 1 := by
        intro ω hω
        have h1 := hpos ω
        have h2' := hm2 ω
        have : m ω ≠ 2 := fun h => hω (hm3 ω ω0 h h0)
        omega
      have hG : ∑ ω, gx (m ω) = 1 := by
        rw [Finset.sum_eq_single ω0]
        · rw [h0, gx_two]
        · intro ω _ hω
          rw [hother ω hω]; exact (gx_eq_zero_iff 1).2 le_rfl
        · intro h; exact absurd (Finset.mem_univ _) h
      have hge : 2 ^ M ≤ Nat.card E := by
        rw [hG] at hid
        rw [hid, pow_add, pow_add] at h2
        refine Nat.le_of_mul_le_mul_left (c := 2 * 2 ^ R) ?_ (Nat.mul_pos (by norm_num) hr)
        calc 2 * 2 ^ R * 2 ^ M = 2 ^ 1 * 2 ^ M * 2 ^ R := by ring
          _ ≤ 2 * 2 ^ R * Nat.card E := h2
      have hbij : Function.Bijective (evalOrb E E le_orbitStab) :=
        (evalOrb_injective_E hE).bijective_of_nat_card_le (by rw [hpi]; exact hge)
      refine ⟨⟨ω0.out, ?_⟩, ?_, ?_, hbij⟩
      · rw [hm, h0]; norm_num
      · intro i
        rw [card_orbit_eq_two_pow hm]
        have h1 := hpos (Quotient.mk'' i)
        have h2' := hm2 (Quotient.mk'' i)
        interval_cases h : m (Quotient.mk'' i) <;> simp
      · intro i j hi hj
        rw [card_orbit_eq_two_pow hm] at hi hj
        have hi' : m (Quotient.mk'' i) = 2 :=
          Nat.pow_right_injective (le_refl 2) (by simpa using hi)
        have hj' : m (Quotient.mk'' j) = 2 :=
          Nat.pow_right_injective (le_refl 2) (by simpa using hj)
        have hij : (Quotient.mk'' i : Orb E) = Quotient.mk'' j := hm3 _ _ hi' hj'
        have h5 : (orbitRel E Ω) i j := Quotient.exact' hij
        have h6 : orbit E i = orbit E j := orbit_eq_iff.2 (orbitRel_apply.1 h5)
        rw [h6]; exact mem_orbit_self j
    · left
      push Not at hbig
      have hall : ∀ ω, m ω = 1 := fun ω => by
        have := hpos ω; have := hm2 ω; have := hbig ω; omega
      have hsmall : ∀ i : Ω, Nat.card (orbit E i) = 2 := fun i => by
        rw [card_orbit_eq_two_pow hm, hall]; norm_num
      refine ⟨hsmall, ?_⟩
      have hG : ∑ ω, gx (m ω) = 0 :=
        Finset.sum_eq_zero fun ω _ => (gx_eq_zero_iff _).2 (by rw [hall])
      rw [hG, zero_add] at hid
      rw [hid, pow_add] at h2
      have h3 : 2 ^ M ≤ 2 * Nat.card E := by
        refine Nat.le_of_mul_le_mul_left (c := 2 ^ R) ?_ hr
        calc 2 ^ R * 2 ^ M = 2 ^ M * 2 ^ R := by ring
          _ ≤ 2 * 2 ^ R * Nat.card E := h2
          _ = 2 ^ R * (2 * Nat.card E) := by ring
      exact le_trans (hK fun i => (hsmall i).le) h3

end CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.Offender
