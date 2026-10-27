module

public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.OffenderMatching
public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.SwapTypeOffender
public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.SwapInBlocks
public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.PairPresClosure

public section

namespace CFSG.HardMathSupport.Cooperstein.AlternatingGeometry

open Equiv Equiv.Perm MulAction
open CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.Offender

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

@[expose] def BlockData (E : Subgroup (Perm Ω)) (σ : Perm Ω) (c : Ω → Bool) : Prop :=
  (∀ x, σ x ≠ x) ∧ (∀ x, σ (σ x) = x) ∧ (∀ g ∈ E, ∀ x, g x = x ∨ g x = σ x) ∧
    (∀ x, c (σ x) = c x) ∧ (∀ x, c x = true ↔ swap x (σ x) ∉ E) ∧ dblGroup σ c ≤ E

theorem shape_cases {E : Subgroup (Perm Ω)} (h : OffenderShapeConcl E) :
    SwapType E ∨ (∃ x : Ω, Nat.card (orbit E x) = 4) ∨
      ((∀ x : Ω, Nat.card (orbit E x) = 2) ∧ Nat.card (orbitStab E) ≤ 2 * Nat.card E) := by
  by_cases hf : ∃ p, ∀ g ∈ E, g p = p
  · exact Or.inl (h.1 hf)
  · rcases h.2 hf with h1 | ⟨⟨x, hx⟩, -⟩
    · exact Or.inr (Or.inr h1)
    · exact Or.inr (Or.inl ⟨x, hx⟩)

theorem blockData_of_shape {E : Subgroup (Perm Ω)} (hall : ∀ x : Ω, Nat.card (orbit E x) = 2)
    (hord : Nat.card (orbitStab E) ≤ 2 * Nat.card E) : ∃ σ c, BlockData E σ c := by
  obtain ⟨σ, h1, h2, h3, c, h4, h5, h6⟩ := exists_matching_of_orbits_two hall hord
  exact ⟨σ, c, h1, h2, h3, h4, h5, h6⟩

theorem orbit_eq_pair {E : Subgroup (Perm Ω)} {σ : Perm Ω} (hσ1 : ∀ x, σ x ≠ x)
    (hg : ∀ g ∈ E, ∀ x, g x = x ∨ g x = σ x) (hall : ∀ x : Ω, Nat.card (orbit E x) = 2)
    (x : Ω) : orbit E x = {x, σ x} := by
  have hsub : orbit E x ⊆ ({x, σ x} : Set Ω) := by
    rintro _ ⟨⟨g, hgE⟩, rfl⟩
    exact hg g hgE x
  refine Set.eq_of_subset_of_ncard_le hsub ?_ (Set.toFinite _)
  rw [Set.ncard_pair (hσ1 x).symm, ← Nat.card_coe_set_eq, hall x]

open scoped Classical in
theorem offenders_dichotomy (hΩ : 9 ≤ Fintype.card Ω) {P : Subgroup (Perm Ω)}
    (hP : IsPGroup 2 P) {ι : Type*} (E : ι → Subgroup (Perm Ω)) (hEP : ∀ i, E i ≤ P)
    (hsh : ∀ i, OffenderShapeConcl (E i)) :
    (∀ i, SwapType (E i)) ∨ (∃ (i : ι) (x : Ω), Nat.card (orbit (E i) x) = 4) ∨
      (∃ (i : ι) (σ : Perm Ω) (c : Ω → Bool), BlockData (E i) σ c ∧ ∃ x, (cls c x).card = 4) ∨
      ∃ σ : Perm Ω, ∃ (hσ1 : ∀ x, σ x ≠ x) (hσ2 : ∀ x, σ (σ x) = x),
        (⨆ i, E i) ≤ pairPres σ hσ1 hσ2 ∧
        (∀ x y, y ≠ x → y ≠ σ x → swap x (σ x) ∉ (⨆ i, E i) → swap y (σ y) ∉ (⨆ i, E i) →
          swap x (σ x) * swap y (σ y) ∈ (⨆ i, E i)) ∧
        (Finset.univ.filter fun x : Ω => swap x (σ x) ∉ (⨆ i, E i)).card ≠ 2 * 1 ∧
        (Finset.univ.filter fun x : Ω => swap x (σ x) ∉ (⨆ i, E i)).card ≠ 2 * 2 ∧
        (Finset.univ.filter fun x : Ω => swap x (σ x) ∈ (⨆ i, E i)).card ≠ 2 * 2 := by
  have hΩ6 : 6 ≤ Fintype.card Ω := by omega
  by_cases hA : ∀ i, SwapType (E i)
  · exact Or.inl hA
  right
  by_cases hB : ∃ (i : ι) (x : Ω), Nat.card (orbit (E i) x) = 4
  · exact Or.inl hB
  right
  push Not at hA hB
  obtain ⟨i0, hi0⟩ := hA
  have hN1 : ∀ i, ¬ SwapType (E i) → (∀ x : Ω, Nat.card (orbit (E i) x) = 2) ∧
      Nat.card (orbitStab (E i)) ≤ 2 * Nat.card (E i) := by
    intro i hi
    rcases shape_cases (hsh i) with h | ⟨x, hx⟩ | h
    · exact absurd h hi
    · exact absurd hx (hB i x)
    · exact h
  obtain ⟨σ0, c0, hbd0⟩ := blockData_of_shape (hN1 i0 hi0).1 (hN1 i0 hi0).2
  by_cases hC : ∃ (i : ι) (σ : Perm Ω) (c : Ω → Bool), BlockData (E i) σ c ∧ ∃ x, (cls c x).card = 4
  · exact Or.inl hC
  right
  push Not at hC
  obtain ⟨hσ1, hσ2, hg0, hc0, hcol0, hdbl0⟩ := hbd0
  have hdblP : dblGroup σ0 c0 ≤ P := hdbl0.trans (hEP i0)
  have h40 : ∀ x, (cls c0 x).card ≠ 4 := hC i0 σ0 c0 ⟨hσ1, hσ2, hg0, hc0, hcol0, hdbl0⟩
  have hall : ∀ i, E i ≤ pairPres σ0 hσ1 hσ2 := by
    intro i
    by_cases hi : SwapType (E i)
    · refine (le_closure_swaps_of_swapType hi).trans ?_
      rw [Subgroup.closure_le]
      rintro t ⟨htE, a, b, hab, rfl⟩
      have hb : b = σ0 a := eq_matching_of_swap_mem hΩ6 hσ1 hσ2 hc0 h40 hP hdblP hab (hEP i htE)
      rw [hb]
      exact swap_mem_pairPres hσ1 hσ2 a
    · obtain ⟨σ, c, hbd⟩ := blockData_of_shape (hN1 i hi).1 (hN1 i hi).2
      obtain ⟨hs1, hs2, hg, hc, hcol, hdbl⟩ := hbd
      have h4 : ∀ x, (cls c x).card ≠ 4 := hC i σ c ⟨hs1, hs2, hg, hc, hcol, hdbl⟩
      have hσeq : σ0 = σ := eq_of_dblGroup_le_isPGroup hΩ6 hσ1 hσ2 hc0 hs1 hs2 hc h40 h4 hP hdblP
        (hdbl.trans (hEP i))
      intro g hgE z
      rw [hσeq]
      exact hg g hgE z
  have hEW : E i0 ≤ ⨆ i, E i := le_iSup E i0
  have hWK : (⨆ i, E i) ≤ pairPres σ0 hσ1 hσ2 := iSup_le hall
  refine ⟨σ0, hσ1, hσ2, hWK, ?_, ?_⟩
  · intro x y hyx hyσ hx hy
    have hxE : swap x (σ0 x) ∉ E i0 := fun h => hx (hEW h)
    have hyE : swap y (σ0 y) ∉ E i0 := fun h => hy (hEW h)
    have hcx : c0 x = true := (hcol0 x).2 hxE
    have hcy : c0 y = true := (hcol0 y).2 hyE
    exact hEW (hdbl0 (Subgroup.subset_closure ⟨x, y, hyx, hyσ, hcy.trans hcx.symm, rfl⟩))
  have hN := hN1 i0 hi0
  have horb : ∀ x, orbit (E i0) x = {x, σ0 x} := orbit_eq_pair hσ1 hg0 hN.1
  have hKeq : orbitStab (E i0) = pairPres σ0 hσ1 hσ2 := by
    ext g
    rw [mem_orbitStab, mem_pairPres]
    constructor
    · intro h z
      have := h z
      rw [horb z] at this
      simpa using this
    · intro h z
      rw [horb z]
      simpa using h z
  have hlt : E i0 < pairPres σ0 hσ1 hσ2 := by
    refine lt_of_le_of_ne (hall i0) fun heq => hi0 ?_
    refine ⟨fun x => ?_, ?_⟩
    · rw [hN.1 x]
    · rw [hKeq]; exact heq
  have hcardK : Nat.card (pairPres σ0 hσ1 hσ2) = 2 * Nat.card (E i0) := by
    obtain ⟨k, hk⟩ := Subgroup.card_dvd_of_le (hall i0)
    have hle : Nat.card (pairPres σ0 hσ1 hσ2) ≤ 2 * Nat.card (E i0) := by
      rw [← hKeq]; exact hN.2
    have hpos : 0 < Nat.card (E i0) := Nat.card_pos
    have hk2 : k ≤ 2 := by
      by_contra h
      have : 2 * Nat.card (E i0) < Nat.card (E i0) * k := by nlinarith
      omega
    have hk1 : k ≠ 1 := by
      rintro rfl
      rw [mul_one] at hk
      exact hlt.ne (Subgroup.eq_of_le_of_card_ge (hall i0) (by omega))
    have hk0 : k ≠ 0 := by
      rintro rfl
      rw [mul_zero] at hk
      have : 0 < Nat.card (pairPres σ0 hσ1 hσ2) := Nat.card_pos
      omega
    have : k = 2 := by omega
    rw [hk, this, mul_comm]
  have hWcases : (⨆ i, E i) = E i0 ∨ (⨆ i, E i) = pairPres σ0 hσ1 hσ2 := by
    have hd1 := Subgroup.card_dvd_of_le hEW
    have hd2 := Subgroup.card_dvd_of_le hWK
    obtain ⟨j, hj⟩ := hd1
    have hpos : 0 < Nat.card (E i0) := Nat.card_pos
    rw [hj, hcardK] at hd2
    have hj2 : j ∣ 2 := by
      obtain ⟨m, hm⟩ := hd2
      exact ⟨m, by nlinarith⟩
    have hj' : j = 1 ∨ j = 2 := by
      rcases (Nat.dvd_prime Nat.prime_two).1 hj2 with h | h
      · exact Or.inl h
      · exact Or.inr h
    rcases hj' with rfl | rfl
    · left
      exact (Subgroup.eq_of_le_of_card_ge hEW (by omega)).symm
    · right
      exact Subgroup.eq_of_le_of_card_ge hWK (by omega)
  rcases hWcases with hWE | hWK'
  ·
    rw [hWE]
    have hsw : ∀ x, swap x (σ0 x) ∈ E i0 ↔ c0 x = false := by
      intro x
      have h := hcol0 x
      cases hcx : c0 x <;> simp_all
    have hsetT : (Finset.univ.filter fun x : Ω => swap x (σ0 x) ∉ E i0) =
        Finset.univ.filter fun y => c0 y = true := by
      ext y; simp [hcol0 y]
    have hsetF : (Finset.univ.filter fun x : Ω => swap x (σ0 x) ∈ E i0) =
        Finset.univ.filter fun y => c0 y = false := by
      ext y; simp [hsw y]
    refine ⟨?_, ?_, ?_⟩
    · intro h2
      rw [hsetT] at h2
      obtain ⟨x, hx⟩ := Finset.card_pos.1 (by rw [h2]; norm_num)
      have hcx : c0 x = true := by simpa using hx
      have hcls : (cls c0 x).card = 2 := by
        have : cls c0 x = Finset.univ.filter fun y => c0 y = true := by
          unfold cls; rw [hcx]
        rw [this, h2]
      have hpair := cls_eq_pair (σ := σ0) c0 hσ1 hc0 hcls
      have hout : ∀ y, y ≠ x → y ≠ σ0 x → swap y (σ0 y) ∈ E i0 := by
        intro y h1 h2'
        rw [hsw y]
        by_contra hne
        have hyt : c0 y = true := by simpa using hne
        have : y ∈ cls c0 x := by unfold cls; simp [hyt, hcx]
        rw [hpair] at this
        simp only [Finset.mem_insert, Finset.mem_singleton] at this
        rcases this with h | h
        · exact h1 h
        · exact h2' h
      have hfix : ∀ g ∈ E i0, g x = x := by
        intro g hgE
        by_contra hgx
        have hgx' : g x = σ0 x := (hg0 g hgE x).resolve_left hgx
        have hgσ : g (σ0 x) = x := by
          rcases pair_cases hσ1 hσ2 (fun z => hg0 g hgE z) x with ⟨e, -⟩ | ⟨-, e⟩
          · exact absurd e hgx
          · exact e
        have hh : g * swap x (σ0 x) ∈ pairPres σ0 hσ1 hσ2 :=
          (pairPres σ0 hσ1 hσ2).mul_mem (hall i0 hgE) (swap_mem_pairPres hσ1 hσ2 x)
        have hhx : (g * swap x (σ0 x)) x = x := by
          rw [Perm.mul_apply, swap_apply_left, hgσ]
        have hcl := mem_closure_blockSwaps_of_fix hσ1 hσ2 x hh hhx
        have hcl' : g * swap x (σ0 x) ∈ E i0 := by
          refine (Subgroup.closure_le (E i0)).2 ?_ hcl
          rintro _ ⟨y, h1, h2', rfl⟩
          exact hout y h1 h2'
        have : swap x (σ0 x) ∈ E i0 := by
          have := (E i0).mul_mem ((E i0).inv_mem hgE) hcl'
          simpa [mul_assoc] using this
        exact (hcol0 x).1 hcx this
      exact hi0 ((hsh i0).1 ⟨x, hfix⟩)
    · intro h4
      rw [hsetT] at h4
      obtain ⟨x, hx⟩ := Finset.card_pos.1 (by rw [h4]; norm_num)
      have hcx : c0 x = true := by simpa using hx
      apply h40 x
      have : cls c0 x = Finset.univ.filter fun y => c0 y = true := by
        unfold cls; rw [hcx]
      rw [this, h4]
    · intro h4
      rw [hsetF] at h4
      obtain ⟨x, hx⟩ := Finset.card_pos.1 (by rw [h4]; norm_num)
      have hcx : c0 x = false := by simpa using hx
      apply h40 x
      have : cls c0 x = Finset.univ.filter fun y => c0 y = false := by
        unfold cls; rw [hcx]
      rw [this, h4]
  · rw [hWK']
    have hall' : ∀ x, swap x (σ0 x) ∈ pairPres σ0 hσ1 hσ2 := swap_mem_pairPres hσ1 hσ2
    have h0 : (Finset.univ.filter fun x : Ω => swap x (σ0 x) ∉ pairPres σ0 hσ1 hσ2).card = 0 := by
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro x _
      exact not_not.2 (hall' x)
    have h1 : (Finset.univ.filter fun x : Ω => swap x (σ0 x) ∈ pairPres σ0 hσ1 hσ2).card =
        Fintype.card Ω := by
      rw [← Finset.card_univ]
      congr 1
      rw [Finset.filter_eq_self]
      intro x _
      exact hall' x
    refine ⟨?_, ?_, ?_⟩ <;> intro h <;> omega

end CFSG.HardMathSupport.Cooperstein.AlternatingGeometry
