module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Shapes

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

@[expose] def symZeta : Z 2 × Sym 6 := (Multiplicative.ofAdd 1, 1)

private def s6a : Sym 6 := Equiv.swap (0 : Fin 6) 1

private def s6b : Sym 6 := s6a * Equiv.swap 2 3

private def s6c : Sym 6 := s6b * Equiv.swap 4 5

private def s6g : Z 2 := Multiplicative.ofAdd 1

private def symModelReps : Fin 7 → Z 2 × Sym 6 :=
  ![symZeta, (1, s6a), (1, s6b), (1, s6c), (s6g, s6a), (s6g, s6b), (s6g, s6c)]

private theorem cycleType_s6a : s6a.cycleType = {2} := by
  unfold s6a
  rw [← Equiv.Perm.isSwap_iff_cycleType, Equiv.Perm.swap_isSwap_iff]
  decide

private theorem cycleType_s6b : s6b.cycleType = {2, 2} := by
  unfold s6b s6a
  exact Equiv.Perm.cycleType_swap_mul_swap_of_nodup (by decide)

private theorem cycleType_swap45 : (Equiv.swap (4 : Fin 6) 5).cycleType = {2} := by
  rw [← Equiv.Perm.isSwap_iff_cycleType, Equiv.Perm.swap_isSwap_iff]
  decide

private theorem cycleType_s6c : s6c.cycleType = {2, 2, 2} := by
  unfold s6c s6b s6a
  have hd1 : Equiv.Perm.Disjoint (Equiv.swap (0 : Fin 6) 1) (Equiv.swap 4 5) :=
    Equiv.Perm.disjoint_swap_swap (by decide)
  have hd2 : Equiv.Perm.Disjoint (Equiv.swap (2 : Fin 6) 3) (Equiv.swap 4 5) :=
    Equiv.Perm.disjoint_swap_swap (by decide)
  have hd : Equiv.Perm.Disjoint
      (Equiv.swap (0 : Fin 6) 1 * Equiv.swap 2 3) (Equiv.swap 4 5) :=
    hd1.mul_left hd2
  rw [Equiv.Perm.Disjoint.cycleType_mul hd,
    Equiv.Perm.cycleType_swap_mul_swap_of_nodup (by decide), cycleType_swap45]
  decide

private theorem sign_s6b : Equiv.Perm.sign s6b = 1 := by
  rw [Equiv.Perm.sign_of_cycleType, cycleType_s6b]
  decide

private theorem symModelReps_zero : symModelReps 0 = symZeta := by
  simp [symModelReps, symZeta]

private theorem symModelReps_one : symModelReps 1 = (1, s6a) := by
  simp [symModelReps]

private theorem symModelReps_two : symModelReps 2 = (1, s6b) := by
  simp [symModelReps]

private theorem symModelReps_three : symModelReps 3 = (1, s6c) := by
  simp [symModelReps]

private theorem symModelReps_four : symModelReps 4 = (s6g, s6a) := by
  simp [symModelReps, s6g]

private theorem symModelReps_five : symModelReps 5 = (s6g, s6b) := by
  simp [symModelReps, s6g]

private theorem symModelReps_six : symModelReps 6 = (s6g, s6c) := by
  simp [symModelReps, s6g]

private theorem isConj_prod_of_isConj {ε : Z 2} {σ τ : Sym 6} (h : IsConj σ τ) :
    IsConj ((ε, σ) : Z 2 × Sym 6) (ε, τ) := by
  obtain ⟨c, hc⟩ := isConj_iff.mp h
  refine isConj_iff.mpr ⟨(1, c), ?_⟩
  ext <;> simp [hc]

private theorem z2_eq_one_or_gen : ∀ ε : Z 2,
    ε = 1 ∨ ε = Multiplicative.ofAdd (1 : ZMod 2) := by
  decide

theorem sym6_involution_types {σ : Sym 6} (h : σ ^ 2 = 1) :
    σ = 1 ∨ (σ.cycleType = {2} ∧ Equiv.Perm.sign σ = -1) ∨
      (σ.cycleType = {2, 2} ∧ Equiv.Perm.sign σ = 1) ∨
      (σ.cycleType = {2, 2, 2} ∧ Equiv.Perm.sign σ = -1) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcyc : σ.cycleType = Multiset.replicate σ.cycleType.card 2 :=
    Equiv.Perm.cycleType_of_pow_prime_eq_one h
  have hsum : σ.cycleType.sum = 2 * σ.cycleType.card := by
    rw [hcyc, Multiset.sum_replicate, Multiset.card_replicate, nsmul_eq_mul, Nat.cast_id]
    ring
  have hcard : σ.cycleType.card ≤ 3 := by
    have h6 : σ.cycleType.sum ≤ 6 := by simpa using σ.sum_cycleType_le
    omega
  have hsplit : σ.cycleType.card = 0 ∨ σ.cycleType.card = 1 ∨
      σ.cycleType.card = 2 ∨ σ.cycleType.card = 3 := by omega
  rcases hsplit with hm | hm | hm | hm
  · left
    have : σ.cycleType = 0 := by rw [hcyc, hm]; rfl
    exact Equiv.Perm.cycleType_eq_zero.mp this
  · right; left
    refine ⟨?_, ?_⟩
    · rw [hcyc, hm]; rfl
    · rw [Equiv.Perm.sign_of_cycleType, hcyc, hm]
      decide
  · right; right; left
    refine ⟨?_, ?_⟩
    · rw [hcyc, hm]; rfl
    · rw [Equiv.Perm.sign_of_cycleType, hcyc, hm]
      decide
  · right; right; right
    refine ⟨?_, ?_⟩
    · rw [hcyc, hm]; rfl
    · rw [Equiv.Perm.sign_of_cycleType, hcyc, hm]
      decide

theorem symModel_reps : ∃ m : Fin 7 → Z 2 × Sym 6,
    ∀ u : Z 2 × Sym 6, orderOf u = 2 → ∃ j, IsConj u (m j) := by
  refine ⟨symModelReps, ?_⟩
  intro u hu
  obtain ⟨ε, σ⟩ := u
  have hu2 : ((ε, σ) : Z 2 × Sym 6) ^ 2 = 1 := by
    have h := pow_orderOf_eq_one ((ε, σ) : Z 2 × Sym 6)
    rw [hu] at h
    exact h
  have hσ2 : σ ^ 2 = 1 := by
    have h := congrArg Prod.snd hu2
    simpa using h
  have hne : ((ε, σ) : Z 2 × Sym 6) ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hu
    omega
  rcases sym6_involution_types hσ2 with hσ1 | ⟨hc1, _⟩ | ⟨hc2, _⟩ | ⟨hc3, _⟩
  · refine ⟨0, ?_⟩
    have hεne : ε ≠ 1 := by
      intro hε
      apply hne
      rw [hσ1, hε]
      rfl
    have hε : ε = s6g := by
      rcases z2_eq_one_or_gen ε with h | h
      · exact absurd h hεne
      · exact h
    rw [hσ1, hε, symModelReps_zero]
    exact IsConj.refl _
  · have hconj : IsConj σ s6a :=
      Equiv.Perm.isConj_iff_cycleType_eq.mpr (by rw [hc1, cycleType_s6a])
    have hconj' := isConj_prod_of_isConj (ε := ε) hconj
    rcases z2_eq_one_or_gen ε with hε | hε
    · subst hε
      exact ⟨1, by simpa [symModelReps_one] using hconj'⟩
    · subst hε
      exact ⟨4, by simpa [symModelReps_four, s6g] using hconj'⟩
  · have hconj : IsConj σ s6b :=
      Equiv.Perm.isConj_iff_cycleType_eq.mpr (by rw [hc2, cycleType_s6b])
    have hconj' := isConj_prod_of_isConj (ε := ε) hconj
    rcases z2_eq_one_or_gen ε with hε | hε
    · subst hε
      exact ⟨2, by simpa [symModelReps_two] using hconj'⟩
    · subst hε
      exact ⟨5, by simpa [symModelReps_five, s6g] using hconj'⟩
  · have hconj : IsConj σ s6c :=
      Equiv.Perm.isConj_iff_cycleType_eq.mpr (by rw [hc3, cycleType_s6c])
    have hconj' := isConj_prod_of_isConj (ε := ε) hconj
    rcases z2_eq_one_or_gen ε with hε | hε
    · subst hε
      exact ⟨3, by simpa [symModelReps_three] using hconj'⟩
    · subst hε
      exact ⟨6, by simpa [symModelReps_six, s6g] using hconj'⟩

theorem symModel_central {u : Z 2 × Sym 6} (hu : orderOf u = 2)
    (hc : ∀ v : Z 2 × Sym 6, v * u = u * v) : u = symZeta := by
  obtain ⟨ε, σ⟩ := u
  have hσcomm : ∀ v : Sym 6, v * σ = σ * v := by
    intro v
    have h := congrArg Prod.snd (hc (1, v))
    simpa using h
  have hσ1 : σ = 1 := by
    by_contra hne
    have hex : ∃ i : Fin 6, σ i ≠ i := by
      by_contra h
      push Not at h
      exact hne (Equiv.ext h)
    obtain ⟨i, hik⟩ := hex
    have hexj : ∃ j : Fin 6, j ≠ i ∧ j ≠ (σ i) := by
      have hlt : ({i, σ i} : Finset (Fin 6)).card <
          (Finset.univ : Finset (Fin 6)).card := by
        rw [Finset.card_univ, Fintype.card_fin]
        have : ({i, σ i} : Finset (Fin 6)).card ≤ 2 := Finset.card_le_two
        omega
      obtain ⟨j, -, hj⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hj
      exact ⟨j, hj.1, hj.2⟩
    obtain ⟨j, hji, hjk⟩ := hexj
    have happ := congrArg (fun f : Sym 6 => f i) (hσcomm (Equiv.swap i j))
    rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, Equiv.swap_apply_left] at happ
    rw [Equiv.swap_apply_of_ne_of_ne hik (Ne.symm hjk)] at happ
    have : i = j := σ.injective happ
    exact hji this.symm
  have hu1 : orderOf ((ε, σ) : Z 2 × Sym 6) = 2 := hu
  rw [hσ1] at hu1
  have hεne : ε ≠ 1 := by
    intro hε
    rw [hε] at hu1
    rw [show ((1 : Z 2), (1 : Sym 6)) = (1 : Z 2 × Sym 6) from rfl, orderOf_one] at hu1
    omega
  have hε : ε = s6g := by
    rcases z2_eq_one_or_gen ε with h | h
    · exact absurd h hεne
    · exact h
  exact Prod.ext hε hσ1

theorem symModel_mem_derived_iff (u : Z 2 × Sym 6) :
    u ∈ _root_.commutator (Z 2 × Sym 6) ↔ u.1 = 1 ∧ Equiv.Perm.sign u.2 = 1 := by
  constructor
  · intro hu
    refine ⟨?_, ?_⟩
    · have h := Abelianization.commutator_subset_ker (MonoidHom.fst (Z 2) (Sym 6)) hu
      rw [MonoidHom.mem_ker] at h
      simpa using h
    · have h := Abelianization.commutator_subset_ker
        ((Equiv.Perm.sign : Sym 6 →* ℤˣ).comp (MonoidHom.snd (Z 2) (Sym 6))) hu
      simpa [MonoidHom.mem_ker] using h
  · rintro ⟨h1, h2⟩
    have hu : u = ((1 : Z 2), u.2) := by ext <;> simp [h1]
    rw [hu]
    have hσmem : u.2 ∈ _root_.commutator (Sym 6) := by
      rw [alternatingGroup.commutator_perm_eq
        (by norm_num [Nat.card_eq_fintype_card] : 5 ≤ Nat.card (Fin 6))]
      exact Equiv.Perm.mem_alternatingGroup.mpr h2
    have hmem : ((1 : Z 2), u.2) ∈
        Subgroup.map (MonoidHom.inr (Z 2) (Sym 6) : Sym 6 →* Z 2 × Sym 6)
          (_root_.commutator (Sym 6)) :=
      Subgroup.mem_map.mpr ⟨u.2, hσmem, rfl⟩
    have hle : Subgroup.map (MonoidHom.inr (Z 2) (Sym 6) : Sym 6 →* Z 2 × Sym 6)
          (_root_.commutator (Sym 6)) ≤ _root_.commutator (Z 2 × Sym 6) := by
      change Subgroup.map (MonoidHom.inr (Z 2) (Sym 6) : Sym 6 →* Z 2 × Sym 6)
          ⁅(⊤ : Subgroup (Sym 6)), ⊤⁆ ≤ ⁅(⊤ : Subgroup (Z 2 × Sym 6)), ⊤⁆
      rw [Subgroup.map_commutator]
      exact Subgroup.commutator_mono le_top le_top
    exact hle hmem

theorem symModel_exists_derived_involution :
    ∃ u : Z 2 × Sym 6, u ∈ _root_.commutator (Z 2 × Sym 6) ∧ orderOf u = 2 := by
  refine ⟨((1 : Z 2), s6b), ?_, ?_⟩
  · rw [symModel_mem_derived_iff]
    exact ⟨rfl, sign_s6b⟩
  · have ho : orderOf s6b = 2 := by
      rw [← Equiv.Perm.lcm_cycleType, cycleType_s6b]
      decide
    rw [Prod.orderOf_mk, orderOf_one, Nat.lcm_one_left, ho]

end CFSG.EvenSporadicStandard.HNRecog.Section3