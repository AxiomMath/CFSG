module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.LinesProof.A8OrbitCard
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.A8.Perm

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

private def linesA8Orbit (S : Subgroup (alternatingGroup (Fin 8))) (i : Fin 8) : Set (Fin 8) :=
  {j : Fin 8 | ∃ g : alternatingGroup (Fin 8), g ∈ S ∧ (g : Equiv.Perm (Fin 8)) i = j}

private lemma linesA8Orbit_mem_self (S : Subgroup (alternatingGroup (Fin 8))) (i : Fin 8) :
    i ∈ linesA8Orbit S i :=
  ⟨1, S.one_mem, rfl⟩

private lemma linesA8Orbit_eq_of_mem {S : Subgroup (alternatingGroup (Fin 8))} {i k : Fin 8}
    (hk : k ∈ linesA8Orbit S i) : linesA8Orbit S k = linesA8Orbit S i := by
  obtain ⟨g, hgS, hgik⟩ := hk
  apply Set.Subset.antisymm
  · rintro j ⟨h, hhS, hhj⟩
    exact ⟨h * g, S.mul_mem hhS hgS,
      by rw [Subgroup.coe_mul, Equiv.Perm.mul_apply, hgik, hhj]⟩
  · rintro j ⟨h, hhS, hhj⟩
    exact ⟨h * g⁻¹, S.mul_mem hhS (S.inv_mem hgS),
      by rw [Subgroup.coe_mul, Subgroup.coe_inv, Equiv.Perm.mul_apply, ← hgik,
        Equiv.Perm.coe_inv, Equiv.symm_apply_apply, hhj]⟩

private lemma linesA8Orbit_image_subset {S : Subgroup (alternatingGroup (Fin 8))}
    {σ : alternatingGroup (Fin 8)} (hn : ∀ g ∈ S, σ * g * σ⁻¹ ∈ S) (i : Fin 8) :
    (σ : Equiv.Perm (Fin 8)) '' linesA8Orbit S i ⊆
      linesA8Orbit S ((σ : Equiv.Perm (Fin 8)) i) := by
  rintro j ⟨x, hx, rfl⟩
  obtain ⟨g, hgS, hgx⟩ := hx
  refine ⟨σ * g * σ⁻¹, hn g hgS, ?_⟩
  show (((σ : Equiv.Perm (Fin 8)) * (g : Equiv.Perm (Fin 8))) *
      (σ : Equiv.Perm (Fin 8))⁻¹) ((σ : Equiv.Perm (Fin 8)) i) =
      (σ : Equiv.Perm (Fin 8)) x
  rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, Equiv.Perm.coe_inv,
    Equiv.symm_apply_apply, hgx]

private lemma linesA8_fixedPointFree (σ : alternatingGroup (Fin 8))
    (hσ : (σ : Equiv.Perm (Fin 8)).cycleType = {2, 2, 2, 2}) :
    ∀ k : Fin 8, (σ : Equiv.Perm (Fin 8)) k ≠ k := by
  have hsupport : (σ : Equiv.Perm (Fin 8)).support = Finset.univ := by
    apply Finset.eq_univ_of_card
    rw [← Equiv.Perm.sum_cycleType, hσ]
    decide
  intro k
  have hk : k ∈ (σ : Equiv.Perm (Fin 8)).support := by
    rw [hsupport]
    exact Finset.mem_univ k
  rwa [Equiv.Perm.mem_support] at hk

theorem linesA8_six_orbit (S : Subgroup (alternatingGroup (Fin 8)))
    (hS : Nonempty (↥S ≃* alternatingGroup (Fin 5))) (σ : alternatingGroup (Fin 8))
    (hσ : (σ : Equiv.Perm (Fin 8)).cycleType = {2, 2, 2, 2})
    (hn : ∀ g ∈ S, σ * g * σ⁻¹ ∈ S) :
    ∃ i : Fin 8, Set.ncard {j : Fin 8 | ∃ g : alternatingGroup (Fin 8), g ∈ S ∧
      (g : Equiv.Perm (Fin 8)) i = j} = 6 := by
  classical
  change ∃ i : Fin 8, (linesA8Orbit S i).ncard = 6
  by_contra hno
  push Not at hno
  let s : Equiv.Perm (Fin 8) := (σ : Equiv.Perm (Fin 8))
  have hs2 : σ ^ 2 = 1 := (sq_eq_one_of_cycleType_two_two_two_two hσ).1
  have hs2' : s ^ 2 = 1 := by
    have h := congrArg (fun g : alternatingGroup (Fin 8) => (g : Equiv.Perm (Fin 8))) hs2
    simpa [s] using h
  have hss : ∀ x : Fin 8, s (s x) = x := by
    intro x
    have h := congrArg (fun p : Equiv.Perm (Fin 8) => p x) hs2'
    simpa [pow_two, Equiv.Perm.coe_mul] using h
  have hS60 : Nat.card ↥S = 60 := by
    obtain ⟨e⟩ := hS
    rw [Nat.card_congr e.toEquiv]
    have h2 : 2 * Nat.card (alternatingGroup (Fin 5)) = 120 := by
      rw [two_mul_nat_card_alternatingGroup (α := Fin 5), Nat.card_perm, Nat.card_fin]
      norm_num
    omega
  have hSne : S ≠ ⊥ := by
    intro hbot
    have h1 : Nat.card ↥S = 1 := by
      rw [hbot]
      exact Subgroup.card_bot
    omega
  obtain ⟨g, hgne⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hSne
  have hgA_ne : (g : alternatingGroup (Fin 8)) ≠ 1 := by
    intro h
    exact hgne (Subtype.ext h)
  have hgmoved : (g : Equiv.Perm (Fin 8)) ≠ 1 := by
    intro h
    exact hgA_ne (Subtype.ext h)
  obtain ⟨i, hi⟩ : ∃ i : Fin 8, (g : Equiv.Perm (Fin 8)) i ≠ i := by
    by_contra h
    push Not at h
    exact hgmoved (Equiv.ext h)
  have hsub : ({i, (g : Equiv.Perm (Fin 8)) i} : Set (Fin 8)) ⊆ linesA8Orbit S i := by
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with hx | hx
    · rw [hx]; exact linesA8Orbit_mem_self S i
    · rw [hx]; exact ⟨(g : alternatingGroup (Fin 8)), g.2, rfl⟩
  have hcard2 : 2 ≤ (linesA8Orbit S i).ncard := by
    have hpair : ({i, (g : Equiv.Perm (Fin 8)) i} : Set (Fin 8)).ncard = 2 :=
      Set.ncard_pair (Ne.symm hi)
    calc 2 = ({i, (g : Equiv.Perm (Fin 8)) i} : Set (Fin 8)).ncard := hpair.symm
      _ ≤ (linesA8Orbit S i).ncard := Set.ncard_le_ncard hsub
  have hmem_i : (linesA8Orbit S i).ncard ∈ ({1, 5, 6} : Set ℕ) := by
    simpa only [linesA8Orbit] using linesA8_orbit_card S hS i
  have hOi5 : (linesA8Orbit S i).ncard = 5 := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem_i
    rcases hmem_i with h | h | h
    · omega
    · exact h
    · exact absurd h (hno i)
  have hmem_j : (linesA8Orbit S (s i)).ncard ∈ ({1, 5, 6} : Set ℕ) := by
    simpa only [linesA8Orbit] using linesA8_orbit_card S hS (s i)
  have himgsub : s '' linesA8Orbit S i ⊆ linesA8Orbit S (s i) :=
    linesA8Orbit_image_subset hn i
  have himgcard : (s '' linesA8Orbit S i).ncard = 5 := by
    rw [Set.ncard_image_of_injective (linesA8Orbit S i) s.injective, hOi5]
  have hge_j : 5 ≤ (linesA8Orbit S (s i)).ncard := by
    calc 5 = (s '' linesA8Orbit S i).ncard := himgcard.symm
      _ ≤ (linesA8Orbit S (s i)).ncard := Set.ncard_le_ncard himgsub
  have hOj5 : (linesA8Orbit S (s i)).ncard = 5 := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem_j
    rcases hmem_j with h | h | h
    · omega
    · exact h
    · exact absurd h (hno (s i))
  have himgeq : s '' linesA8Orbit S i = linesA8Orbit S (s i) :=
    Set.eq_of_subset_of_ncard_le himgsub (by rw [hOj5, himgcard])
  have hunion_le : (linesA8Orbit S i ∪ linesA8Orbit S (s i)).ncard ≤ 8 := by
    have h := Set.ncard_le_ncard (Set.subset_univ (linesA8Orbit S i ∪ linesA8Orbit S (s i)))
    rw [Set.ncard_univ, Nat.card_fin] at h
    exact h
  have hsum := Set.ncard_union_add_ncard_inter (linesA8Orbit S i) (linesA8Orbit S (s i))
  rw [hOi5, hOj5] at hsum
  have hpos : 0 < (linesA8Orbit S i ∩ linesA8Orbit S (s i)).ncard := by omega
  have hne : (linesA8Orbit S i ∩ linesA8Orbit S (s i)).Nonempty :=
    (Set.ncard_pos (s := linesA8Orbit S i ∩ linesA8Orbit S (s i))).mp hpos
  obtain ⟨w, hwi, hwj⟩ := hne
  have hOj_eq : linesA8Orbit S (s i) = linesA8Orbit S i :=
    calc linesA8Orbit S (s i) = linesA8Orbit S w := (linesA8Orbit_eq_of_mem hwj).symm
      _ = linesA8Orbit S i := linesA8Orbit_eq_of_mem hwi
  have hstab : ∀ x : Fin 8, x ∈ linesA8Orbit S i ↔ s x ∈ linesA8Orbit S i := by
    intro x
    constructor
    · intro hx
      have h1 : s x ∈ linesA8Orbit S (s i) := himgsub ⟨x, hx, rfl⟩
      rwa [hOj_eq] at h1
    · intro hsx
      have h1 : s (s x) ∈ linesA8Orbit S (s i) := himgsub ⟨s x, hsx, rfl⟩
      rw [hOj_eq, hss x] at h1
      exact h1
  let f : Equiv.Perm ↥(linesA8Orbit S i) := s.subtypePerm fun x => (hstab x).symm
  have hcardOi : Fintype.card ↥(linesA8Orbit S i) = 5 := by
    rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq]
    exact hOi5
  have hα : ¬ 2 ∣ Fintype.card ↥(linesA8Orbit S i) := by
    rw [hcardOi]
    decide
  have hf2 : f ^ 2 = 1 := by
    apply Equiv.ext
    intro x
    apply Subtype.ext
    change s (s x.1) = x.1
    exact hss x.1
  obtain ⟨a, ha⟩ := Equiv.Perm.exists_fixed_point_of_prime (p := 2) (n := 1) hα
    (by simpa using hf2)
  have hfix : s a.1 = a.1 := by
    have h := congrArg Subtype.val ha
    simpa [f] using h
  exact (linesA8_fixedPointFree σ hσ a.1) hfix

end CFSG.EvenSporadicStandard.HNRecog.Section3