module

public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.OffenderShape
public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.OffenderIndexFixed

public section

namespace CFSG.HardMathSupport.RichardWeiss.ExceptionalClosure

open Equiv Equiv.Perm MulAction
open CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.Offender

set_option linter.unusedSectionVars false

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω] {E : Subgroup (Perm Ω)}

theorem mem_orbit_of_mem {h : Perm Ω} (hh : h ∈ E) (i : Ω) : h i ∈ orbit E i :=
  ⟨⟨h, hh⟩, rfl⟩

theorem zmod2_ne_add_one (a : ZMod 2) : a ≠ a + 1 := by
  revert a; decide

theorem eq_of_card_orbit_two {p a b c : Ω} (h2 : Nat.card (orbit E p) = 2)
    (ha : a ∈ orbit E p) (hb : b ∈ orbit E p) (hc : c ∈ orbit E p) (hba : b ≠ a) (hca : c ≠ a) :
    b = c := by
  obtain ⟨y, hy, huniq⟩ := (Nat.card_eq_two_iff' (⟨a, ha⟩ : orbit E p)).1 h2
  have h1 : (⟨b, hb⟩ : orbit E p) = y := huniq _ (fun h => hba (congrArg Subtype.val h))
  have h2' : (⟨c, hc⟩ : orbit E p) = y := huniq _ (fun h => hca (congrArg Subtype.val h))
  exact congrArg Subtype.val (h1.trans h2'.symm)

theorem no_twist_of_pairs (h2 : ∀ i : Ω, Nat.card (orbit E i) = 2) (h3 : 3 ≤ Nat.card E)
    {x : Ω → ZMod 2} (hx : x ∈ FixUp E) {g : Perm Ω} (hg : g ∈ E)
    (hgx : ∀ i, x (g i) = x i + 1) : False := by
  have hgi : ∀ i, g i ≠ i := fun i h => zmod2_ne_add_one (x i) (by have := hgx i; rwa [h] at this)
  have hpart : ∀ h ∈ E, ∀ i, h i ≠ i → h i = g i := fun h hh i hhi =>
    eq_of_card_orbit_two (h2 i) (mem_orbit_self i) (mem_orbit_of_mem hh i) (mem_orbit_of_mem hg i) hhi (hgi i)
  have hex : ∃ h ∈ E, h ≠ 1 ∧ h ≠ g := by
    by_contra hcon
    push Not at hcon
    let f : E → Bool := fun e => decide ((e : Perm Ω) = 1)
    have hf : Function.Injective f := by
      intro e1 e2 he
      apply Subtype.ext
      have h1 := hcon e1 e1.2
      have h2' := hcon e2 e2.2
      simp only [f, decide_eq_decide] at he
      by_cases h : (e1 : Perm Ω) = 1
      · rw [h, ← he.1 h]
      · have h' : (e2 : Perm Ω) ≠ 1 := fun h'' => h (he.2 h'')
        rw [h1 h, h2' h']
    have := Nat.card_le_card_of_injective f hf
    rw [Nat.card_eq_fintype_card (α := Bool)] at this
    simp at this
    omega
  obtain ⟨h, hhE, hh1, hhg⟩ := hex
  rcases hx.2 h hhE with hfix | htw
  · apply hh1
    ext i
    by_contra hne
    have := hpart h hhE i hne
    have e := hgx i
    rw [← this, hfix i] at e
    exact zmod2_ne_add_one _ e
  · apply hhg
    ext i
    have hne : h i ≠ i := fun he => zmod2_ne_add_one (x i) (by have := htw i; rwa [he] at this)
    exact hpart h hhE i hne

theorem card_FixUp_le_of_no_twist
    (hnt : ∀ x ∈ FixUp E, ∀ g ∈ E, ¬ ∀ i, x (g i) = x i + 1) :
    Nat.card (FixUp E) ≤ 2 ^ Nat.card (Orb E) := by
  have hle : FixUp E ≤ FixP E := by
    intro x hx g hg
    rcases hx.2 g hg with h | h
    · exact h
    · exact absurd h (hnt x hx g hg)
  exact (AddSubgroup.card_le_of_le hle).trans (card_FixP_le E)

theorem no_twist_of_bijective (hbij : Function.Bijective (evalOrb E E le_orbitStab))
    {ω1 ω2 : Orb E} (hne : ω1 ≠ ω2) (h2 : Nat.card (orbit E ω1.out) = 2)
    {x : Ω → ZMod 2} (hx : x ∈ FixUp E) {g : Perm Ω} (hg : g ∈ E)
    (hgx : ∀ i, x (g i) = x i + 1) : False := by
  classical
  obtain ⟨b', hb', -⟩ := (Nat.card_eq_two_iff' (⟨ω1.out, mem_orbit_self _⟩ : orbit E ω1.out)).1 h2
  have hb : (b' : Ω) ∈ orbit E ω1.out := b'.2
  have hba : (b' : Ω) ≠ ω1.out := fun h => hb' (Subtype.ext h)
  let f : ∀ ω : Orb E, orbit E ω.out := fun ω =>
    if hω : ω = ω1 then ⟨b', by subst hω; exact hb⟩ else ⟨ω.out, mem_orbit_self _⟩
  obtain ⟨e, he⟩ := hbij.2 f
  have e1 : (e : Perm Ω) ω1.out = b' := by
    have := congrArg Subtype.val (congrFun he ω1)
    simpa [evalOrb, f] using this
  have e2 : (e : Perm Ω) ω2.out = ω2.out := by
    have := congrArg Subtype.val (congrFun he ω2)
    simpa [evalOrb, f, Ne.symm hne] using this
  have hfix : ∀ i, x ((e : Perm Ω) i) = x i := by
    rcases hx.2 (e : Perm Ω) e.2 with h | h
    · exact h
    · exact absurd (by have := h ω2.out; rwa [e2] at this) (zmod2_ne_add_one _)
  have hgi : g ω1.out ≠ ω1.out := fun h =>
    zmod2_ne_add_one (x ω1.out) (by have := hgx ω1.out; rwa [h] at this)
  have hgb : g ω1.out = b' :=
    eq_of_card_orbit_two h2 (mem_orbit_self _) (mem_orbit_of_mem hg _) hb hgi hba
  have h3 := hfix ω1.out
  rw [e1] at h3
  have h4 := hgx ω1.out
  rw [hgb, h3] at h4
  exact zmod2_ne_add_one _ h4

theorem card_le_offIdx_of_shape [Nonempty Ω] (hE : IsExp2 E) (hoff : offIdx E ≤ Nat.card E)
    (hn : Nat.card Ω = 7 ∨ 9 ≤ Nat.card Ω)
    (hfull : ¬ ((¬ ∃ p, ∀ g ∈ E, g p = p) ∧ (∀ i : Ω, Nat.card (orbit E i) = 2) ∧
                 Nat.card (orbitStab E) = Nat.card E)) :
    Nat.card E ≤ offIdx E := by
  classical
  obtain ⟨m, hm, hE', hid, hm2, hm3, hfix, hnofix⟩ := numerics hE hoff hn
  have hpi := card_pi_orbits hm
  have hr : 0 < 2 ^ Nat.card (Orb E) := by positivity
  by_cases hf : ∃ p, ∀ g ∈ E, g p = p
  · obtain ⟨hm1, -⟩ := hfix hf
    have hG : ∑ ω, gx (m ω) = 0 :=
      Finset.sum_eq_zero fun ω _ => (gx_eq_zero_iff _).2 (hm1 ω)
    obtain ⟨p, hp⟩ := hf
    have key := two_pow_le_offIdx_mul_of_fixed hp
    rw [hG, zero_add] at hid
    have h1 : Nat.card E * 2 ^ Nat.card (Orb E) ≤ 2 ^ Nat.card Ω := by
      calc Nat.card E * 2 ^ Nat.card (Orb E) ≤ (2 ^ ∑ ω, m ω) * 2 ^ Nat.card (Orb E) :=
            Nat.mul_le_mul_right _ hE'
        _ = 2 ^ Nat.card Ω := by rw [hid, ← pow_add]
    exact Nat.le_of_mul_le_mul_right (h1.trans key) hr
  · have hnf : ¬ ∃ p, ∀ g ∈ E, g p = p := hf
    have h2 := hnofix hnf
    have hpos : ∀ ω : Orb E, 1 ≤ m ω := by
      intro ω
      by_contra hlt
      have h0 : m ω = 0 := by omega
      have h1 : Nat.card (orbit E ω.out) = 1 := by rw [hm, h0]; rfl
      exact hnf ⟨ω.out, fixed_of_card_orbit_eq_one h1⟩
    have hFix : Nat.card (FixUp E) ≤ 2 ^ Nat.card (Orb E) := by
      apply card_FixUp_le_of_no_twist
      intro x hx g hg hgx
      by_cases hbig : ∃ ω0, m ω0 = 2
      · obtain ⟨ω0, h0⟩ := hbig
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
        have hM : ∑ ω, m ω = Nat.card (Orb E) + 1 := by
          have : ∀ ω, m ω = 1 + if ω = ω0 then 1 else 0 := fun ω => by
            by_cases h : ω = ω0
            · subst h; simp [h0]
            · simp [h, hother ω h]
          rw [Finset.sum_congr rfl fun ω _ => this ω, Finset.sum_add_distrib]
          simp [Nat.card_eq_fintype_card]
        rw [hG, hM] at hid
        have hge : 2 ^ ∑ ω, m ω ≤ Nat.card E := by
          rw [hM]
          refine Nat.le_of_mul_le_mul_left (c := 2 ^ Nat.card (Orb E) * 2) ?_
            (by positivity)
          calc 2 ^ Nat.card (Orb E) * 2 * 2 ^ (Nat.card (Orb E) + 1)
              = 2 ^ Nat.card Ω := by rw [hid]; ring
            _ ≤ 2 * 2 ^ Nat.card (Orb E) * Nat.card E := h2
            _ = 2 ^ Nat.card (Orb E) * 2 * Nat.card E := by ring
        have hbij : Function.Bijective (evalOrb E E le_orbitStab) :=
          (evalOrb_injective_E hE).bijective_of_nat_card_le (by rw [hpi]; exact hge)
        have hR1 : 1 < Nat.card (Orb E) := by omega
        have : Nontrivial (Orb E) := Finite.one_lt_card_iff_nontrivial.1 hR1
        obtain ⟨ω1, hω1⟩ := exists_ne ω0
        exact no_twist_of_bijective hbij hω1
          (by rw [hm, hother ω1 hω1]; norm_num) hx hg hgx
      · push Not at hbig
        have hall : ∀ ω, m ω = 1 := fun ω => by
          have := hpos ω; have := hm2 ω; have := hbig ω; omega
        have hsmall : ∀ i : Ω, Nat.card (orbit E i) = 2 := fun i => by
          rw [card_orbit_eq_two_pow hm, hall]; norm_num
        have hG : ∑ ω, gx (m ω) = 0 :=
          Finset.sum_eq_zero fun ω _ => (gx_eq_zero_iff _).2 (by rw [hall])
        have hM : ∑ ω, m ω = Nat.card (Orb E) := by
          simp [hall, Nat.card_eq_fintype_card]
        rw [hG, hM, zero_add] at hid
        have h3 : 3 ≤ Nat.card E := by
          by_contra hlt
          push Not at hlt
          have hR4 : 4 ≤ Nat.card (Orb E) := by omega
          have : 2 ^ (2 * Nat.card (Orb E)) ≤ 2 ^ (Nat.card (Orb E) + 2) := by
            calc 2 ^ (2 * Nat.card (Orb E)) = 2 ^ Nat.card Ω := by rw [hid]; ring_nf
              _ ≤ 2 * 2 ^ Nat.card (Orb E) * Nat.card E := h2
              _ ≤ 2 * 2 ^ Nat.card (Orb E) * 2 := Nat.mul_le_mul_left _ (by omega)
              _ = 2 ^ (Nat.card (Orb E) + 2) := by ring
          have := pow_two_le_iff.1 this
          omega
        exact no_twist_of_pairs hsmall h3 hx hg hgx
    have hev := pow_le_two_mul_card_evenVec (Ω := Ω)
    have hmul := offIdx_mul_card (E := E)
    have hA : 2 ^ Nat.card Ω ≤ offIdx E * 2 ^ (Nat.card (Orb E) + 1) := by
      calc 2 ^ Nat.card Ω ≤ 2 * Nat.card (evenVec Ω) := hev
        _ = 2 * (offIdx E * Nat.card (FixUp E)) := by rw [hmul]
        _ ≤ 2 * (offIdx E * 2 ^ Nat.card (Orb E)) :=
            Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hFix)
        _ = offIdx E * 2 ^ (Nat.card (Orb E) + 1) := by ring
    have hB : Nat.card E * 2 ^ (Nat.card (Orb E) + 1) ≤ 2 ^ Nat.card Ω := by
      by_cases hbig : ∃ ω0, m ω0 = 2
      · obtain ⟨ω0, h0⟩ := hbig
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
        have hM : ∑ ω, m ω = Nat.card (Orb E) + 1 := by
          have : ∀ ω, m ω = 1 + if ω = ω0 then 1 else 0 := fun ω => by
            by_cases h : ω = ω0
            · subst h; simp [h0]
            · simp [h, hother ω h]
          rw [Finset.sum_congr rfl fun ω _ => this ω, Finset.sum_add_distrib]
          simp [Nat.card_eq_fintype_card]
        rw [hG, hM] at hid
        calc Nat.card E * 2 ^ (Nat.card (Orb E) + 1)
            ≤ 2 ^ (Nat.card (Orb E) + 1) * 2 ^ (Nat.card (Orb E) + 1) := by
              rw [hM] at hE'; exact Nat.mul_le_mul_right _ hE'
          _ = 2 ^ Nat.card Ω := by rw [hid, ← pow_add]; congr 1; ring
      · push Not at hbig
        have hall : ∀ ω, m ω = 1 := fun ω => by
          have := hpos ω; have := hm2 ω; have := hbig ω; omega
        have hsmall : ∀ i : Ω, Nat.card (orbit E i) = 2 := fun i => by
          rw [card_orbit_eq_two_pow hm, hall]; norm_num
        have hG : ∑ ω, gx (m ω) = 0 :=
          Finset.sum_eq_zero fun ω _ => (gx_eq_zero_iff _).2 (by rw [hall])
        have hM : ∑ ω, m ω = Nat.card (Orb E) := by
          simp [hall, Nat.card_eq_fintype_card]
        rw [hG, hM, zero_add] at hid
        have hstab : Nat.card (orbitStab E) ≤ 2 ^ Nat.card (Orb E) := by
          have := Nat.card_le_card_of_injective _ (evalOrb_injective_K (E := E)
            (fun i => (hsmall i).le))
          rwa [hpi, hM] at this
        have hdvd : Nat.card E ∣ Nat.card (orbitStab E) :=
          Subgroup.card_dvd_of_le le_orbitStab
        have hne : Nat.card (orbitStab E) ≠ Nat.card E := fun h => hfull ⟨hnf, hsmall, h⟩
        obtain ⟨k, hk⟩ := hdvd
        have hEpos : 0 < Nat.card E := Nat.card_pos
        have hk2 : 2 ≤ k := by
          rcases k with _ | _ | k
          · rw [Nat.mul_zero] at hk; exact absurd hk (Nat.card_pos (α := orbitStab E)).ne'
          · exact absurd (by rw [hk]; simp) hne
          · omega
        have h2E : Nat.card E * 2 ≤ 2 ^ Nat.card (Orb E) := by
          calc Nat.card E * 2 ≤ Nat.card E * k := Nat.mul_le_mul_left _ hk2
            _ = Nat.card (orbitStab E) := hk.symm
            _ ≤ _ := hstab
        calc Nat.card E * 2 ^ (Nat.card (Orb E) + 1)
            = (Nat.card E * 2) * 2 ^ Nat.card (Orb E) := by ring
          _ ≤ 2 ^ Nat.card (Orb E) * 2 ^ Nat.card (Orb E) := Nat.mul_le_mul_right _ h2E
          _ = 2 ^ Nat.card Ω := by rw [hid, ← pow_add]
    exact Nat.le_of_mul_le_mul_right (hB.trans hA) (by positivity)

end CFSG.HardMathSupport.RichardWeiss.ExceptionalClosure
