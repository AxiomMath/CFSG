module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Seg27.Perm
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Seg27.Tools
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple
public import Mathlib.Tactic.NormNum.NatFactorial

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

theorem seg27_orbit_ncard_of_A6 {Y : Subgroup (Equiv.Perm (Fin 8))}
    (e : ↥Y ≃* alternatingGroup (Fin 6)) (x : Fin 8) :
    (MulAction.orbit Y x).ncard = 1 ∨ (MulAction.orbit Y x).ncard = 6 := by
  haveI : IsSimpleGroup (alternatingGroup (Fin 6)) :=
    alternatingGroup.isSimpleGroup (by norm_num [Nat.card_fin])
  haveI : IsSimpleGroup ↥Y := e.isSimpleGroup
  have hcardY : Nat.card ↥Y = 360 :=
    calc Nat.card ↥Y = Nat.card (alternatingGroup (Fin 6)) := Nat.card_congr e.toEquiv
      _ = ((6 : ℕ).factorial / 2) := by rw [nat_card_alternatingGroup, Nat.card_fin]
      _ = 360 := by norm_num
  set m : ℕ := (MulAction.orbit Y x).ncard with hm
  have hindex : (MulAction.stabilizer ↥Y x).index = m := by
    rw [hm]
    exact MulAction.index_stabilizer ↥Y x
  have hmul : Nat.card (MulAction.stabilizer ↥Y x) * m = Nat.card ↥Y := by
    rw [← hindex]
    exact Subgroup.card_mul_index (MulAction.stabilizer ↥Y x)
  have hdvd360 : m ∣ 360 := by
    rw [← hcardY]
    exact ⟨Nat.card (MulAction.stabilizer ↥Y x),
      by rw [mul_comm]; exact hmul.symm⟩
  have hm_pos : 0 < m := by
    rw [hm]
    exact (Set.ncard_pos (Set.toFinite (MulAction.orbit Y x))).mpr
      ⟨x, MulAction.mem_orbit_self x⟩
  have hm_le : m ≤ 8 := by
    rw [hm]
    simpa [Nat.card_fin] using Set.ncard_le_card (MulAction.orbit Y x)
  by_cases h1 : m = 1
  · exact Or.inl h1
  right
  have hSt : MulAction.stabilizer ↥Y x ≠ ⊤ := by
    intro htop
    apply h1
    rw [← hindex, htop, Subgroup.index_top]
  have hdvd_fact : 360 ∣ m.factorial := by
    have h := seg27_card_dvd_factorial (MulAction.stabilizer ↥Y x) hSt
    rw [hcardY, hindex] at h
    exact h
  interval_cases m
  · exact absurd rfl h1
  · have h2 : ¬ (360 ∣ (2 : ℕ).factorial) := by norm_num
    exact (h2 hdvd_fact).elim
  · have h3 : ¬ (360 ∣ (3 : ℕ).factorial) := by norm_num
    exact (h3 hdvd_fact).elim
  · have h4 : ¬ (360 ∣ (4 : ℕ).factorial) := by norm_num
    exact (h4 hdvd_fact).elim
  · have h5 : ¬ (360 ∣ (5 : ℕ).factorial) := by norm_num
    exact (h5 hdvd_fact).elim
  · rfl
  · have h7 : ¬ (7 ∣ (360 : ℕ)) := by norm_num
    exact (h7 hdvd360).elim
  · have hcardSt : Nat.card (MulAction.stabilizer ↥Y x) = 45 := by
      apply Nat.mul_right_cancel (show 0 < (8 : ℕ) by norm_num)
      have h := hmul
      rw [hcardY] at h
      simpa using h
    obtain ⟨g, hg⟩ :=
      seg27_exists_orderOf_fifteen (G := ↥(MulAction.stabilizer ↥Y x)) hcardSt
    have h15 :
        orderOf ((e (g : ↥Y) : alternatingGroup (Fin 6)) : Equiv.Perm (Fin 6)) = 15 := by
      calc orderOf ((e (g : ↥Y) : alternatingGroup (Fin 6)) : Equiv.Perm (Fin 6))
          = orderOf (e (g : ↥Y)) := Subgroup.orderOf_coe _
        _ = orderOf (g : ↥Y) := MulEquiv.orderOf_eq e _
        _ = orderOf g := Subgroup.orderOf_coe _
        _ = 15 := hg
    exact (seg27_orderOf_ne_fifteen _ h15).elim

theorem seg27_eq_altFix_of_A6 {Y : Subgroup (Equiv.Perm (Fin 8))}
    (hY : Y ≤ alternatingGroup (Fin 8)) (e : ↥Y ≃* alternatingGroup (Fin 6)) :
    ∃ p q : Fin 8, p ≠ q ∧ Y = seg27AltFix {p, q} := by
  have hcardY : Nat.card ↥Y = 360 :=
    calc Nat.card ↥Y = Nat.card (alternatingGroup (Fin 6)) := Nat.card_congr e.toEquiv
      _ = ((6 : ℕ).factorial / 2) := by rw [nat_card_alternatingGroup, Nat.card_fin]
      _ = 360 := by norm_num
  have hex : ∃ x : Fin 8, (MulAction.orbit Y x).ncard = 6 := by
    by_contra h
    push Not at h
    have hall : ∀ x : Fin 8, (MulAction.orbit Y x).ncard = 1 := by
      intro x
      rcases seg27_orbit_ncard_of_A6 e x with h1 | h6
      · exact h1
      · exact absurd h6 (h x)
    have hbot : Y = ⊥ := by
      rw [Subgroup.eq_bot_iff_forall]
      intro g hg
      apply Equiv.ext
      intro x
      have hsing : MulAction.orbit Y x = {x} := by
        obtain ⟨a, ha⟩ := Set.ncard_eq_one.mp (hall x)
        have hxa : x ∈ ({a} : Set (Fin 8)) := by
          rw [← ha]
          exact MulAction.mem_orbit_self x
        have hax : a = x := (Set.mem_singleton_iff.mp hxa).symm
        rw [ha, hax]
      have hgx : g x ∈ MulAction.orbit Y x := by
        simpa using MulAction.mem_orbit x (⟨g, hg⟩ : Y)
      rw [hsing] at hgx
      simpa using (Set.mem_singleton_iff.mp hgx)
    have hcontra : (360 : ℕ) = 1 := by
      rw [← hcardY, hbot]
      exact Subgroup.card_bot
    norm_num at hcontra
  obtain ⟨x, hx6⟩ := hex
  have hcompl : (MulAction.orbit Y x)ᶜ.ncard = 2 := by
    have h : Nat.card (Fin 8) = 2 + (MulAction.orbit Y x).ncard := by
      simp [hx6, Nat.card_fin]
    exact Set.ncard_compl_of_ncard_eq_add (MulAction.orbit Y x) h
  obtain ⟨p, q, hpq, hpqset⟩ := Set.ncard_eq_two.mp hcompl
  refine ⟨p, q, hpq, ?_⟩
  have hfix : ∀ r, r ∉ MulAction.orbit Y x → ∀ g ∈ Y, g r = r := by
    intro r hr g hg
    have hr1 : (MulAction.orbit Y r).ncard = 1 := by
      rcases seg27_orbit_ncard_of_A6 e r with h1 | h6
      · exact h1
      · exfalso
        have hdisj : Disjoint (MulAction.orbit Y r) (MulAction.orbit Y x) := by
          rw [Set.disjoint_left]
          intro y hyr hyx
          apply hr
          have hor : MulAction.orbit Y r = MulAction.orbit Y x := by
            rw [← (MulAction.orbit_eq_iff).mpr hyr, (MulAction.orbit_eq_iff).mpr hyx]
          rw [← hor]
          exact MulAction.mem_orbit_self r
        have hle : (MulAction.orbit Y r ∪ MulAction.orbit Y x).ncard ≤ 8 := by
          simpa [Nat.card_fin] using
            Set.ncard_le_card (MulAction.orbit Y r ∪ MulAction.orbit Y x)
        have hcard : (MulAction.orbit Y r ∪ MulAction.orbit Y x).ncard = 12 := by
          simp [Set.ncard_union_eq hdisj, h6, hx6]
        rw [hcard] at hle
        norm_num at hle
    have hsing : MulAction.orbit Y r = {r} := by
      obtain ⟨a, ha⟩ := Set.ncard_eq_one.mp hr1
      have hra : r ∈ ({a} : Set (Fin 8)) := by
        rw [← ha]
        exact MulAction.mem_orbit_self r
      have har : a = r := (Set.mem_singleton_iff.mp hra).symm
      rw [ha, har]
    have hgr : g r ∈ MulAction.orbit Y r := by
      simpa using MulAction.mem_orbit r (⟨g, hg⟩ : Y)
    rw [hsing] at hgr
    exact Set.mem_singleton_iff.mp hgr
  have hp : p ∉ MulAction.orbit Y x := by
    rw [← Set.mem_compl_iff, hpqset]
    simp
  have hq : q ∉ MulAction.orbit Y x := by
    rw [← Set.mem_compl_iff, hpqset]
    simp
  have hle : Y ≤ seg27AltFix ({p, q} : Set (Fin 8)) := by
    intro g hg
    rw [seg27_mem_altFix]
    refine ⟨hY hg, ?_⟩
    intro y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with hy | hy
    · rw [hy]
      exact hfix p hp g hg
    · rw [hy]
      exact hfix q hq g hg
  have hcardfix : Nat.card (seg27AltFix ({p, q} : Set (Fin 8))) = 360 :=
    seg27_card_altFix_two hpq
  have hcardle : Nat.card (seg27AltFix ({p, q} : Set (Fin 8))) ≤ Nat.card ↥Y := by
    simp [hcardfix, hcardY]
  exact Subgroup.eq_of_le_of_card_ge hle hcardle

end CFSG.EvenSporadicStandard.HNRecog.Section3
