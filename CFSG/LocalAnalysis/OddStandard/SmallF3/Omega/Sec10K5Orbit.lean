module

public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.OddStandard.SmallF3.Omega.K5

theorem card_le_two_pow_of_supp {Ω : Type} [Fintype Ω] [DecidableEq Ω]
    (E : Subgroup (Equiv.Perm Ω)) (hcomm : ∀ e ∈ E, ∀ f ∈ E, e * f = f * e)
    (hsq : ∀ e ∈ E, e * e = 1) (X : Finset Ω) (hsupp : ∀ e ∈ E, ∀ x, e x ≠ x → x ∈ X) :
    Nat.card E ≤ 2 ^ (X.card / 2) := by
  classical
  suffices ∀ n, ∀ (E : Subgroup (Equiv.Perm Ω)) (X : Finset Ω), X.card = n →
      (∀ e ∈ E, ∀ f ∈ E, e * f = f * e) → (∀ e ∈ E, e * e = 1) →
      (∀ e ∈ E, ∀ x, e x ≠ x → x ∈ X) → Nat.card E ≤ 2 ^ (X.card / 2) by
    exact this X.card E X rfl hcomm hsq hsupp
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro E X hXcard hcomm hsq hsupp
    by_cases htriv : ∀ e ∈ E, e = 1
    · have hsub : Subsingleton ↥E :=
        ⟨fun a b => Subtype.ext
          (by rw [htriv (a : Equiv.Perm Ω) a.2, htriv (b : Equiv.Perm Ω) b.2])⟩
      have hcard : Nat.card E ≤ 1 := Finite.card_le_one_iff_subsingleton.mpr hsub
      calc Nat.card E ≤ 1 := hcard
        _ ≤ 2 ^ (X.card / 2) := Nat.one_le_two_pow
    · push Not at htriv
      obtain ⟨e, he, he1⟩ := htriv
      have hmoved : ∃ x, e x ≠ x := by
        by_contra h
        push Not at h
        exact he1 (Equiv.ext (fun x => by simpa using h x))
      obtain ⟨x, hx⟩ := hmoved
      have hxX : x ∈ X := hsupp e he x hx
      let eE : ↥E := ⟨e, he⟩
      have hxmove : eE • x ≠ x := hx
      set m : ℕ := Nat.card (MulAction.orbit ↥E x) with hm
      have hE2 : IsPGroup 2 ↥E := by
        rw [isPGroup_iff_pow_pow_eq_one]
        intro g
        refine ⟨1, ?_⟩
        rw [pow_one]
        apply Subtype.ext
        rw [pow_two]
        exact hsq (g : Equiv.Perm Ω) g.2
      have horbit : m * Nat.card (MulAction.stabilizer ↥E x) = Nat.card ↥E := by
        rw [hm]
        simpa only [Nat.card_eq_fintype_card] using
          (MulAction.card_orbit_mul_card_stabilizer_eq_card_group (G := ↥E) (X := Ω) x)
      haveI : Nontrivial ↥(MulAction.orbit ↥E x) :=
        ⟨⟨⟨x, MulAction.mem_orbit_self x⟩,
          ⟨eE • x, MulAction.mem_orbit x eE⟩,
          fun h => hxmove (Subtype.ext_iff.mp h).symm⟩⟩
      have hm2 : 2 ≤ m := by
        have h1 : 1 < Nat.card (MulAction.orbit ↥E x) :=
          Finite.one_lt_card_iff_nontrivial.mpr inferInstance
        rw [← hm] at h1
        omega
      have hfix : ∀ h ∈ MulAction.stabilizer ↥E x,
          ∀ y ∈ MulAction.orbit ↥E x, h • y = y := by
        intro h hh y hy
        obtain ⟨f, rfl⟩ := MulAction.mem_orbit_iff.mp hy
        have hcf : h * f = f * h :=
          Subtype.ext (hcomm (h : Equiv.Perm Ω) h.2 (f : Equiv.Perm Ω) f.2)
        rw [← mul_smul, hcf, mul_smul, MulAction.mem_stabilizer_iff.mp hh]
      set E' : Subgroup (Equiv.Perm Ω) := (MulAction.stabilizer ↥E x).map E.subtype with hE'
      have hcardE' : Nat.card E' = Nat.card (MulAction.stabilizer ↥E x) := by
        rw [hE']; exact Subgroup.card_subtype E (MulAction.stabilizer ↥E x)
      have hcomm' : ∀ a ∈ E', ∀ b ∈ E', a * b = b * a := by
        intro a ha b hb
        rw [hE', Subgroup.mem_map] at ha
        rw [hE', Subgroup.mem_map] at hb
        obtain ⟨a', ha', rfl⟩ := ha
        obtain ⟨b', hb', rfl⟩ := hb
        rw [← map_mul, ← map_mul]
        exact congrArg E.subtype
          (Subtype.ext (hcomm (a' : Equiv.Perm Ω) a'.2 (b' : Equiv.Perm Ω) b'.2))
      have hsq' : ∀ a ∈ E', a * a = 1 := by
        intro a ha
        rw [hE', Subgroup.mem_map] at ha
        obtain ⟨a', ha', rfl⟩ := ha
        simpa using hsq (a' : Equiv.Perm Ω) a'.2
      set O' : Finset Ω := (MulAction.orbit ↥E x).toFinset with hO'
      have hO'card : O'.card = m := by
        rw [hO', hm]
        exact (Set.ncard_eq_toFinset_card' _).symm
      have hO'X : O' ⊆ X := by
        intro y hy
        rw [hO', Set.mem_toFinset] at hy
        obtain ⟨f, rfl⟩ := MulAction.mem_orbit_iff.mp hy
        apply hsupp e he
        have hne : eE • (f • x) ≠ f • x := by
          intro hc
          have h1 : eE • (f • x) = f • (eE • x) := by
            rw [← mul_smul, ← mul_smul,
              show eE * f = f * eE from
                Subtype.ext (hcomm e he (f : Equiv.Perm Ω) f.2)]
          rw [h1] at hc
          exact hxmove ((smul_left_cancel_iff f).mp hc)
        exact hne
      set X' : Finset Ω := X \ O' with hX'
      have hX'card : X'.card = X.card - m := by
        rw [hX', Finset.card_sdiff_of_subset hO'X, hO'card]
      have hsupp' : ∀ a ∈ E', ∀ y, a y ≠ y → y ∈ X' := by
        intro a ha y hay
        rw [hE', Subgroup.mem_map] at ha
        obtain ⟨h, hhH, rfl⟩ := ha
        rw [hX', Finset.mem_sdiff]
        refine ⟨hsupp (h : Equiv.Perm Ω) h.2 y hay, ?_⟩
        intro hy
        rw [hO', Set.mem_toFinset] at hy
        exact hay (hfix h hhH y hy)
      have hmle : m ≤ X.card := by
        rw [← hO'card]
        exact Finset.card_le_card hO'X
      have hlt : X'.card < n := by
        rw [hX'card]; omega
      have hIH := ih X'.card hlt E' X' rfl hcomm' hsq' hsupp'
      obtain ⟨k, hk⟩ := hE2.card_orbit x
      have hk' : m = 2 ^ k := by rw [hm]; exact hk
      have h2dvd : 2 ∣ m := by
        rw [hk']
        exact dvd_pow_self 2 (by
          rcases Nat.eq_zero_or_pos k with h0 | hpos
          · rw [h0, pow_zero] at hk'; omega
          · omega)
      set j : ℕ := m / 2 with hj
      have hmj : m = 2 * j := by
        rw [hj]; exact (Nat.mul_div_cancel' h2dvd).symm
      have hexp : (X.card - m) / 2 = X.card / 2 - j := by
        have h2j : 2 * j ≤ X.card := by rw [← hmj]; exact hmle
        rw [hmj]; omega
      have hjle : j ≤ X.card / 2 := by
        rw [hj]; exact Nat.div_le_div_right hmle
      calc
        Nat.card ↥E = m * Nat.card (MulAction.stabilizer ↥E x) := horbit.symm
        _ = m * Nat.card E' := by rw [hcardE']
        _ ≤ m * 2 ^ (X'.card / 2) := Nat.mul_le_mul_left m hIH
        _ = m * 2 ^ ((X.card - m) / 2) := by rw [hX'card]
        _ = (2 * j) * 2 ^ ((X.card - m) / 2) := by rw [hmj]
        _ = (2 * j) * 2 ^ (X.card / 2 - j) := by rw [hexp]
        _ ≤ (2 ^ j) * 2 ^ (X.card / 2 - j) :=
              Nat.mul_le_mul_right _ (Nat.mul_le_pow (by norm_num) j)
        _ = 2 ^ (j + (X.card / 2 - j)) := by rw [← pow_add]
        _ = 2 ^ (X.card / 2) := by rw [Nat.add_sub_of_le hjle]

end CFSG.OddStandard.SmallF3.Omega.K5
