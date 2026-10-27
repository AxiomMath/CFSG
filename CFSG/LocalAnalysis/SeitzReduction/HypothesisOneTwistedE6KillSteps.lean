module

public import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneTwistedE6KillAdm
public import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneClassKill
public import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneTwistedE6TwoBasic

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley RootOps
open scoped commutatorElement

variable {K : Type} [Field K]

@[expose] noncomputable def twKillA
    (σ : K →+* K) (i : Fin TwistTag.E6.tag.rank) (c : K) : ModGL TwistTag.E6.tag K :=
  pinnedX TwistTag.E6.tag K (Pi.single i 1) c *
    if TwistTag.E6.perm i = i then 1
    else pinnedX TwistTag.E6.tag K (Pi.single (TwistTag.E6.perm i) 1) (σ c)


theorem twKill_height_add (u v : Fin TwistTag.E6.tag.rank → ℤ) :
    height (u + v) = height u + height v := by
  simp [height, Finset.sum_add_distrib]

theorem twKill_hstr (J : Set (Fin TwistTag.E6.tag.rank)) (i : Fin TwistTag.E6.tag.rank) :
    ∀ δ ∈ parabolicPosRoots TwistTag.E6.tag J,
      ¬IsRoot TwistTag.E6.tag (δ + (2 : ℤ) • Pi.single i 1) :=
  classKill_hstr_of_mem_longSimple
    (mem_classKillLongSimple_of_simplyLaced (Or.inr (Or.inl rfl)) i) J

theorem twKill_single_mem {J : Set (Fin TwistTag.E6.tag.rank)} {j : Fin TwistTag.E6.tag.rank}
    (hj : j ∈ J) : (Pi.single j 1 : Fin TwistTag.E6.tag.rank → ℤ) ∈
      parabolicPosRoots TwistTag.E6.tag J := by
  refine ⟨⟨isRoot_single _ j, fun l hl => ?_⟩, isRoot_single _ j, by rw [height_single]; omega⟩
  have hlj : l ≠ j := fun h => hl (h ▸ hj)
  simp [Pi.single_eq_of_ne hlj]

theorem twKill_single_ne {i j : Fin TwistTag.E6.tag.rank} (h : i ≠ j) :
    (Pi.single i 1 : Fin TwistTag.E6.tag.rank → ℤ) ≠ Pi.single j 1 := fun e => by
  have := congrFun e i
  rw [Pi.single_eq_same, Pi.single_eq_of_ne h] at this
  exact one_ne_zero this

theorem twKill_ne_neg {β γ : Fin TwistTag.E6.tag.rank → ℤ} (hβ : 0 < height β)
    (hγ : 0 < height γ) : β ≠ -γ := fun e => by
  rw [e, height_neg] at hβ
  omega

theorem twKill_not_isRoot_pair {i : Fin TwistTag.E6.tag.rank} (h : TwistTag.E6.perm i ≠ i) :
    ¬IsRoot TwistTag.E6.tag (Pi.single i 1 + Pi.single (TwistTag.E6.perm i) 1) := by
  rw [← isRootB_iff, twKill_check_pair i h]
  exact Bool.false_ne_true

theorem twKill_isRootB_eq_false {v : Fin TwistTag.E6.tag.rank → ℤ} :
    isRootB TwistTag.E6.tag v = false ↔ ¬IsRoot TwistTag.E6.tag v := by
  rw [← isRootB_iff]
  cases isRootB TwistTag.E6.tag v <;> simp

theorem twKill_string_facts {i : Fin TwistTag.E6.tag.rank} (hi : TwistTag.E6.perm i ≠ i)
    {δ : Fin TwistTag.E6.tag.rank → ℤ} (hδ : IsRoot TwistTag.E6.tag δ) (hpos : 0 < height δ)
    (h1 : ¬IsRoot TwistTag.E6.tag (δ - Pi.single i 1))
    (h2 : ¬IsRoot TwistTag.E6.tag (δ - Pi.single (TwistTag.E6.perm i) 1))
    (h3 : IsRoot TwistTag.E6.tag (δ + Pi.single i 1))
    (h4 : ¬IsRoot TwistTag.E6.tag (δ + Pi.single (TwistTag.E6.perm i) 1)) :
    ¬IsRoot TwistTag.E6.tag (δ + Pi.single i 1 + Pi.single (TwistTag.E6.perm i) 1) ∧
      ¬IsRoot TwistTag.E6.tag (δ + Pi.single i 1 - Pi.single (TwistTag.E6.perm i) 1) := by
  obtain ⟨k, hk, rfl⟩ := RootCertificate.exists_root_eq TwistTag.E6.tag.rootCertificate_check hδ
  have := twKill_check_string i hi k (List.mem_range.2 hk) hpos (twKill_isRootB_eq_false.2 h1)
    (twKill_isRootB_eq_false.2 h2) (isRootB_iff.2 h3) (twKill_isRootB_eq_false.2 h4)
  exact ⟨twKill_isRootB_eq_false.1 this.1, twKill_isRootB_eq_false.1 this.2⟩

theorem twKill_square_facts {i : Fin TwistTag.E6.tag.rank} (hi : TwistTag.E6.perm i ≠ i)
    {δ : Fin TwistTag.E6.tag.rank → ℤ} (hδ : IsRoot TwistTag.E6.tag δ) (hpos : 0 < height δ)
    (h1 : ¬IsRoot TwistTag.E6.tag (δ - Pi.single i 1))
    (h2 : ¬IsRoot TwistTag.E6.tag (δ - Pi.single (TwistTag.E6.perm i) 1))
    (h3 : IsRoot TwistTag.E6.tag (δ + Pi.single i 1))
    (h4 : IsRoot TwistTag.E6.tag (δ + Pi.single (TwistTag.E6.perm i) 1)) :
    permLattice TwistTag.E6.perm δ = δ ∧
      IsRoot TwistTag.E6.tag (δ + Pi.single i 1 + Pi.single (TwistTag.E6.perm i) 1) ∧
      ¬IsRoot TwistTag.E6.tag (δ + Pi.single i 1 - Pi.single (TwistTag.E6.perm i) 1) ∧
      ¬IsRoot TwistTag.E6.tag (δ - Pi.single i 1 + Pi.single (TwistTag.E6.perm i) 1) ∧
      ¬IsRoot TwistTag.E6.tag
        (δ + Pi.single i 1 + Pi.single (TwistTag.E6.perm i) 1 + Pi.single i 1) ∧
      ¬IsRoot TwistTag.E6.tag (δ + Pi.single i 1 + Pi.single (TwistTag.E6.perm i) 1 +
        Pi.single (TwistTag.E6.perm i) 1) := by
  obtain ⟨k, hk, rfl⟩ := RootCertificate.exists_root_eq TwistTag.E6.tag.rootCertificate_check hδ
  obtain ⟨e1, e2, e3, e4, e5, e6⟩ := twKill_check_square i hi k (List.mem_range.2 hk) hpos
    (twKill_isRootB_eq_false.2 h1) (twKill_isRootB_eq_false.2 h2) (isRootB_iff.2 h3)
    (isRootB_iff.2 h4)
  exact ⟨List.ofFn_injective e1, isRootB_iff.1 e2, twKill_isRootB_eq_false.1 e3,
    twKill_isRootB_eq_false.1 e4, twKill_isRootB_eq_false.1 e5, twKill_isRootB_eq_false.1 e6⟩

theorem twKillPerp_subset {J : Set (Fin TwistTag.E6.tag.rank)} {i : Fin TwistTag.E6.tag.rank} :
    twKillPerp J i ⊆ parabolicPosRoots TwistTag.E6.tag J \
      {Pi.single i 1, Pi.single (TwistTag.E6.perm i) 1} := by
  rintro δ ⟨h1, h2⟩
  refine ⟨h1.1, fun h => ?_⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h
  rcases h with rfl | rfl
  · exact (classKillPerp_subset h1).2 rfl
  · exact (classKillPerp_subset h2).2 rfl

theorem twKillPerp_closed {J : Set (Fin TwistTag.E6.tag.rank)} {i : Fin TwistTag.E6.tag.rank} :
    ∀ γ ∈ twKillPerp J i, ∀ δ ∈ twKillPerp J i, ∀ a b : ℕ, 1 ≤ a → 1 ≤ b →
      IsRoot TwistTag.E6.tag (a • γ + b • δ) → a • γ + b • δ ∈ twKillPerp J i :=
  fun γ hγ δ hδ a b ha hb hr =>
    ⟨classKillPerp_closed γ hγ.1 δ hδ.1 a b ha hb hr,
      classKillPerp_closed γ hγ.2 δ hδ.2 a b ha hb hr⟩

theorem twKillPerp_perm {J : Set (Fin TwistTag.E6.tag.rank)} (hJ : ∀ j ∈ J, TwistTag.E6.perm j ∈ J)
    {i : Fin TwistTag.E6.tag.rank} {δ : Fin TwistTag.E6.tag.rank → ℤ} (hδ : δ ∈ twKillPerp J i) :
    permLattice TwistTag.E6.perm δ ∈ twKillPerp J i := by
  obtain ⟨⟨hδJ, h1⟩, -, h2⟩ := hδ
  have hJ' := twKill_perm_mem_parabolicPosRoots hJ hδJ
  refine ⟨⟨hJ', ?_⟩, hJ', ?_⟩
  · rw [twKill_classKillPair_permLattice]
    exact h2
  · rw [twKill_classKillPair_permLattice, twistedE6_perm_perm]
    exact h1

theorem twKill_mem_perp_of_min {J : Set (Fin TwistTag.E6.tag.rank)}
    {i : Fin TwistTag.E6.tag.rank} {R : Set (Fin TwistTag.E6.tag.rank → ℤ)} (hR : TwKillAdm J i R)
    {δ : Fin TwistTag.E6.tag.rank → ℤ} (hmin : TwKillMin i R δ)
    (h1 : ¬IsRoot TwistTag.E6.tag (δ + Pi.single i 1))
    (h2 : ¬IsRoot TwistTag.E6.tag (δ + Pi.single (TwistTag.E6.perm i) 1)) :
    δ ∈ twKillPerp J i := by
  obtain ⟨hδJ, hδne⟩ := hR.subset hmin.mem
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hδne
  refine ⟨⟨hδJ, classKillPair_eq_zero hδJ.2.1 hδne.1
      (twKill_ne_neg hδJ.2.2 (by rw [height_single]; omega)) h1
      (hmin.not_isRoot_sub hR (Or.inl rfl))⟩,
    hδJ, classKillPair_eq_zero hδJ.2.1 hδne.2
      (twKill_ne_neg hδJ.2.2 (by rw [height_single]; omega)) h2
      (hmin.not_isRoot_sub hR (Or.inr rfl))⟩

theorem twKillA_of_fixed (σ : K →+* K) {i : Fin TwistTag.E6.tag.rank}
    (h : TwistTag.E6.perm i = i) (c : K) :
    twKillA σ i c = pinnedX TwistTag.E6.tag K (Pi.single i 1) c := by
  simp only [twKillA, h, ↓reduceIte, mul_one]

theorem twKillA_of_ne (σ : K →+* K) {i : Fin TwistTag.E6.tag.rank}
    (h : TwistTag.E6.perm i ≠ i) (c : K) :
    twKillA σ i c = twistedE6PairX σ (Pi.single i 1) c := by
  simp only [twKillA, h, ↓reduceIte, twistedE6PairX, twKill_perm_single]

theorem twKillA_mem (σ : K →+* K) {J : Set (Fin TwistTag.E6.tag.rank)}
    (hJ : ∀ j ∈ J, TwistTag.E6.perm j ∈ J) {i : Fin TwistTag.E6.tag.rank} (hi : i ∈ J) (c : K) :
    twKillA σ i c ∈ rootSpan TwistTag.E6.tag K (parabolicPosRoots TwistTag.E6.tag J) := by
  refine mul_mem (classKill_pinnedX_mem (twKill_single_mem hi) c) ?_
  split_ifs
  · exact one_mem _
  · exact classKill_pinnedX_mem (twKill_single_mem (hJ i hi)) _

theorem twKill_commute_pair {i : Fin TwistTag.E6.tag.rank} (h : TwistTag.E6.perm i ≠ i)
    (c d : K) : Commute (pinnedX TwistTag.E6.tag K (Pi.single i 1) c)
      (pinnedX TwistTag.E6.tag K (Pi.single (TwistTag.E6.perm i) 1) d) :=
  commute_pinnedX_of_not_isRoot_add_E6 (isRoot_single _ i) (isRoot_single _ _)
    (twKill_single_ne (Ne.symm h))
    (twKill_ne_neg (by rw [height_single]; omega) (by rw [height_single]; omega))
    (twKill_not_isRoot_pair h) c d

theorem twKillA_mul_self [CharP K 2] (σ : K →+* K) (i : Fin TwistTag.E6.tag.rank) (c : K) :
    twKillA σ i c * twKillA σ i c = 1 := by
  by_cases h : TwistTag.E6.perm i = i
  · rw [twKillA_of_fixed σ h, classKill_pinnedX_mul_self]
  · simp only [twKillA, h, ↓reduceIte]
    have hc := twKill_commute_pair h c (σ c)
    calc pinnedX TwistTag.E6.tag K (Pi.single i 1) c *
          pinnedX TwistTag.E6.tag K (Pi.single (TwistTag.E6.perm i) 1) (σ c) *
        (pinnedX TwistTag.E6.tag K (Pi.single i 1) c *
          pinnedX TwistTag.E6.tag K (Pi.single (TwistTag.E6.perm i) 1) (σ c))
        = pinnedX TwistTag.E6.tag K (Pi.single i 1) c *
          (pinnedX TwistTag.E6.tag K (Pi.single (TwistTag.E6.perm i) 1) (σ c) *
            pinnedX TwistTag.E6.tag K (Pi.single i 1) c) *
          pinnedX TwistTag.E6.tag K (Pi.single (TwistTag.E6.perm i) 1) (σ c) := by group
      _ = 1 := by
        rw [← hc.eq, ← mul_assoc, classKill_pinnedX_mul_self, one_mul,
          classKill_pinnedX_mul_self]

theorem twKillA_F [CharP K 2] {σ : K →+* K} (hσσ : ∀ x, σ (σ x) = x)
    {i : Fin TwistTag.E6.tag.rank} {c : K} (hcσ : TwistTag.E6.perm i = i → σ c = c) :
    twistHom TwistTag.E6 K σ (twKillA σ i c) = twKillA σ i c := by
  by_cases h : TwistTag.E6.perm i = i
  · rw [twKillA_of_fixed σ h, twKill_F_pinnedX σ (isRoot_single _ i), twKill_perm_single, h,
      hcσ h]
  · rw [twKillA_of_ne σ h]
    exact ((mem_twistedFixedGroup_iff_twistHom _ _ _).1
      (twistedE6PairX_mem_twistedFixedGroup hσσ (isRoot_single _ i) c)).2

theorem twKillA_comm_perp [CharP K 2] (σ : K →+* K) {J : Set (Fin TwistTag.E6.tag.rank)}
    (hJ : ∀ j ∈ J, TwistTag.E6.perm j ∈ J) {i : Fin TwistTag.E6.tag.rank} (hi : i ∈ J) (c : K)
    {z : ModGL TwistTag.E6.tag K} (hz : z ∈ rootSpan TwistTag.E6.tag K (twKillPerp J i)) :
    twKillA σ i c * z = z * twKillA σ i c := by
  have hz1 : z ∈ rootSpan TwistTag.E6.tag K (classKillPerp TwistTag.E6.tag J i) :=
    classKill_rootSpan_mono Set.inter_subset_left hz
  have hz2 : z ∈ rootSpan TwistTag.E6.tag K (classKillPerp TwistTag.E6.tag J (TwistTag.E6.perm i)) :=
    classKill_rootSpan_mono Set.inter_subset_right hz
  have c1 := classKill_comm_perp hi (twKill_hstr J i) c hz1
  unfold twKillA
  split_ifs with h
  · simpa only [mul_one] using c1
  · have c2 := classKill_comm_perp (hJ i hi) (twKill_hstr J (TwistTag.E6.perm i)) (σ c) hz2
    rw [mul_assoc, c2, ← mul_assoc, c1, mul_assoc]

theorem twKillA_string [CharP K 2] (σ : K →+* K) {J : Set (Fin TwistTag.E6.tag.rank)}
    {i : Fin TwistTag.E6.tag.rank} (hi : i ∈ J) (c : K) {R' : Set (Fin TwistTag.E6.tag.rank → ℤ)}
    (hnorm : ∀ v ∈ rootSpan TwistTag.E6.tag K (parabolicPosRoots TwistTag.E6.tag J),
      ∀ m ∈ rootSpan TwistTag.E6.tag K R', v * m * v⁻¹ ∈ rootSpan TwistTag.E6.tag K R')
    {δ : Fin TwistTag.E6.tag.rank → ℤ} (hδ : δ ∈ parabolicPosRoots TwistTag.E6.tag J \
      {Pi.single i 1, Pi.single (TwistTag.E6.perm i) 1})
    (hδa : IsRoot TwistTag.E6.tag (δ + Pi.single i 1))
    (hδs : ¬IsRoot TwistTag.E6.tag (δ - Pi.single i 1))
    (hb : TwistTag.E6.perm i = i ∨
      (¬IsRoot TwistTag.E6.tag (δ + Pi.single (TwistTag.E6.perm i) 1) ∧
        ¬IsRoot TwistTag.E6.tag (δ + Pi.single i 1 + Pi.single (TwistTag.E6.perm i) 1)))
    (hR' : ∀ p q : ℕ, 1 ≤ p → 2 ≤ q →
      IsRoot TwistTag.E6.tag (p • Pi.single i 1 + q • δ) → p • Pi.single i 1 + q • δ ∈ R') :
    (∀ g : K, (pinnedX TwistTag.E6.tag K (δ + Pi.single i 1) (c * g) *
        pinnedX TwistTag.E6.tag K δ g)⁻¹ *
        (twKillA σ i c * pinnedX TwistTag.E6.tag K δ g * twKillA σ i c) ∈
          rootSpan TwistTag.E6.tag K R') ∧
      ∀ e : K, twKillA σ i c * pinnedX TwistTag.E6.tag K (δ + Pi.single i 1) e =
        pinnedX TwistTag.E6.tag K (δ + Pi.single i 1) e * twKillA σ i c := by
  have hδ' : δ ∈ parabolicPosRoots TwistTag.E6.tag J \ {Pi.single i 1} :=
    ⟨hδ.1, fun h => hδ.2 (Or.inl h)⟩
  have hY := classKill_conj_bottom (twKill_hstr J i) hnorm hδ' hδa hδs hR' c
  have hX := classKill_comm_add_single hi (twKill_hstr J i) hδ' hδa c
  by_cases h : TwistTag.E6.perm i = i
  · rw [twKillA_of_fixed σ h]
    exact ⟨hY, hX⟩
  · obtain ⟨h1, h2⟩ := hb.resolve_left h
    have hδr := hδ.1.2.1
    have hδp := hδ.1.2.2
    have hne : Pi.single (TwistTag.E6.perm i) 1 ≠ δ := fun e => hδ.2 (Or.inr e.symm)
    have hpos1 : (0 : ℤ) < height (Pi.single (TwistTag.E6.perm i) 1 : Fin TwistTag.E6.tag.rank → ℤ) := by
      rw [height_single]; omega
    have hhε : height (δ + Pi.single i 1) = height δ + 1 := by
      rw [twKill_height_add, height_single]
    have hpos2 : 0 < height (δ + Pi.single i 1) := by omega
    have hBY : ∀ g : K, Commute (pinnedX TwistTag.E6.tag K (Pi.single (TwistTag.E6.perm i) 1) (σ c))
        (pinnedX TwistTag.E6.tag K δ g) := fun g =>
      commute_pinnedX_of_not_isRoot_add_E6 (isRoot_single _ _) hδr hne (twKill_ne_neg hpos1 hδp)
        (by rw [add_comm]; exact h1) _ _
    have hBX : ∀ e : K, Commute (pinnedX TwistTag.E6.tag K (Pi.single (TwistTag.E6.perm i) 1) (σ c))
        (pinnedX TwistTag.E6.tag K (δ + Pi.single i 1) e) := fun e =>
      commute_pinnedX_of_not_isRoot_add_E6 (isRoot_single _ _) hδa
        (fun e' => by
          have h' := congrArg height e'
          rw [hhε, height_single] at h'
          omega) (twKill_ne_neg hpos1 hpos2) (by rw [add_comm]; exact h2) _ _
    have hAB := twKill_commute_pair h c (σ c)
    simp only [twKillA, h, ↓reduceIte]
    set X := pinnedX TwistTag.E6.tag K (Pi.single i 1) c
    set B := pinnedX TwistTag.E6.tag K (Pi.single (TwistTag.E6.perm i) 1) (σ c)
    refine ⟨fun g => ?_, fun e => ?_⟩
    · have e1 : X * B * pinnedX TwistTag.E6.tag K δ g * (X * B) =
          X * pinnedX TwistTag.E6.tag K δ g * X := by
        calc X * B * pinnedX TwistTag.E6.tag K δ g * (X * B)
            = X * (B * pinnedX TwistTag.E6.tag K δ g) * (X * B) := by group
          _ = X * (pinnedX TwistTag.E6.tag K δ g * B) * (X * B) := by rw [(hBY g).eq]
          _ = X * pinnedX TwistTag.E6.tag K δ g * (B * X) * B := by group
          _ = X * pinnedX TwistTag.E6.tag K δ g * (X * B) * B := by rw [← hAB.eq]
          _ = X * pinnedX TwistTag.E6.tag K δ g * X * (B * B) := by group
          _ = X * pinnedX TwistTag.E6.tag K δ g * X := by
            rw [classKill_pinnedX_mul_self, mul_one]
      rw [e1]
      exact hY g
    · rw [mul_assoc, (hBX e).eq, ← mul_assoc, hX e, mul_assoc]

theorem twKill_commutator_mem {J : Set (Fin TwistTag.E6.tag.rank)}
    {T R' : Set (Fin TwistTag.E6.tag.rank → ℤ)} (hT : T ⊆ parabolicPosRoots TwistTag.E6.tag J)
    (hnorm : ∀ v ∈ rootSpan TwistTag.E6.tag K (parabolicPosRoots TwistTag.E6.tag J),
      ∀ m ∈ rootSpan TwistTag.E6.tag K R', v * m * v⁻¹ ∈ rootSpan TwistTag.E6.tag K R')
    {β : Fin TwistTag.E6.tag.rank → ℤ} (hβ : β ∈ parabolicPosRoots TwistTag.E6.tag J)
    (hβR : ∀ γ ∈ T, ∀ a b : ℕ, 1 ≤ a → 1 ≤ b →
      IsRoot TwistTag.E6.tag (a • γ + b • β) → a • γ + b • β ∈ R')
    {z : ModGL TwistTag.E6.tag K} (hz : z ∈ rootSpan TwistTag.E6.tag K T) (e : K) :
    ⁅z, pinnedX TwistTag.E6.tag K β e⁆ ∈ rootSpan TwistTag.E6.tag K R' := by
  have hle : ⁅Subgroup.closure {g | ∃ γ ∈ T, ∃ c : K, pinnedX TwistTag.E6.tag K γ c = g},
      Subgroup.closure (Set.range (pinnedX TwistTag.E6.tag K β))⁆ ≤
        rootSpan TwistTag.E6.tag K R' := by
    refine commutator_closure_le_of_le_normalizer
      (G₀ := rootSpan TwistTag.E6.tag K (parabolicPosRoots TwistTag.E6.tag J)) ?_ ?_ ?_ ?_
    · rw [← rootSpan_eq_closure]
      exact classKill_rootSpan_mono hT
    · exact le_iSup₂_of_le (f := fun γ (_ : γ ∈ parabolicPosRoots TwistTag.E6.tag J) =>
        rootSubgroup TwistTag.E6.tag K γ) β hβ le_rfl
    · intro v hv
      refine Subgroup.mem_normalizer_iff.2 fun m => ⟨fun hm => hnorm v hv m hm, fun hm => ?_⟩
      have := hnorm v⁻¹ (inv_mem hv) _ hm
      simpa [mul_assoc] using this
    · rintro _ ⟨γ, hγ, c, rfl⟩ _ ⟨e', rfl⟩
      by_cases hγβ : γ = β
      · subst hγβ
        rw [commutatorElement_def, rootSubgroup_mul_comm K (Subgroup.subset_closure ⟨c, rfl⟩)
          (Subgroup.subset_closure ⟨e', rfl⟩), mul_inv_cancel_right, mul_inv_cancel]
        exact Subgroup.one_mem _
      · have hγJ := hT hγ
        have hmem := commutator_rootSubgroup_le K hγJ.2.1 hβ.2.1 hγJ.2.2 hβ.2.2 hγβ
          (Subgroup.commutator_mem_commutator (Subgroup.subset_closure ⟨c, rfl⟩)
            (Subgroup.subset_closure ⟨e', rfl⟩))
        have hle' : (⨆ (ε : Fin TwistTag.E6.tag.rank → ℤ) (_ : IsRoot TwistTag.E6.tag ε ∧
            ∃ a b : ℕ, 1 ≤ a ∧ 1 ≤ b ∧ ε = a • γ + b • β), rootSubgroup TwistTag.E6.tag K ε) ≤
            rootSpan TwistTag.E6.tag K R' := by
          refine iSup₂_le fun ε hε => ?_
          obtain ⟨hεr, a, b, ha, hb, rfl⟩ := hε
          exact le_iSup₂_of_le _ (hβR γ hγ a b ha hb hεr) le_rfl
        exact hle' hmem
  exact hle (Subgroup.commutator_mem_commutator (by rw [← rootSpan_eq_closure]; exact hz)
    (Subgroup.subset_closure ⟨e, rfl⟩))

end CFSG.SeitzReduction
