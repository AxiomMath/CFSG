module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.FFExc.F4SplitMoves
public import CFSG.HardMathSupport.Cooperstein.Coordinator.FFExc.F4SplitSplitting

public noncomputable section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.FFExc

open CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg.Minuscule Matrix

abbrev nd0 : Fin Tag.E6.rank := ⟨0, by decide⟩
abbrev nd1 : Fin Tag.E6.rank := ⟨1, by decide⟩
abbrev nd2 : Fin Tag.E6.rank := ⟨2, by decide⟩
abbrev nd3 : Fin Tag.E6.rank := ⟨3, by decide⟩
abbrev nd4 : Fin Tag.E6.rank := ⟨4, by decide⟩
abbrev nd5 : Fin Tag.E6.rank := ⟨5, by decide⟩

theorem isRoot_single' (i : Fin Tag.E6.rank) : IsRoot Tag.E6 (Pi.single i 1) := IsRoot.basis i

theorem exists_neg_single : ∀ i : Fin Tag.E6.rank, ∃ k < 72, e6root k = -Pi.single i 1 := by
  decide +kernel

theorem pair_sums_not_root : ∀ p ∈ [(nd0, nd5), (nd2, nd4)],
    (∀ k < 72, e6root k ≠ Pi.single p.2 1 + -Pi.single p.1 1) ∧
    (∀ k < 72, e6root k ≠ -Pi.single p.2 1 + Pi.single p.1 1) ∧
    (∀ k < 72, e6root k ≠ Pi.single p.2 1 + Pi.single p.1 1) ∧
    Pi.single p.2 1 + -Pi.single p.1 1 ≠ (0 : Fin Tag.E6.rank → ℤ) ∧
    -Pi.single p.2 1 + Pi.single p.1 1 ≠ (0 : Fin Tag.E6.rank → ℤ) ∧
    Pi.single p.2 1 + Pi.single p.1 1 ≠ (0 : Fin Tag.E6.rank → ℤ) := by
  decide +kernel

theorem gam_single_zero : graphRoot (Pi.single nd0 1) = Pi.single nd5 1 := by decide +kernel

theorem gam_single_five : graphRoot (Pi.single nd5 1) = Pi.single nd0 1 := by decide +kernel

theorem gam_single_two : graphRoot (Pi.single nd2 1) = Pi.single nd4 1 := by decide +kernel

theorem gam_single_four : graphRoot (Pi.single nd4 1) = Pi.single nd2 1 := by decide +kernel

theorem gam_single_one : graphRoot (Pi.single nd1 1) = Pi.single nd1 1 := by decide +kernel

theorem gam_single_three : graphRoot (Pi.single nd3 1) = Pi.single nd3 1 := by decide +kernel

theorem gam_neg (v : Fin Tag.E6.rank → ℤ) : graphRoot (-v) = -graphRoot v := rfl

theorem fixed_iff {k : ℕ} (hk : k < 72) : graphRoot (e6root k) = e6root k ↔ gamK k = k := by
  rw [graphRoot_root k hk]
  exact ⟨fun h => e6root_inj _ (gamK_lt k hk) _ hk h, fun h => by rw [h]⟩

variable (hV : e6Data.Valid) (K : Type*) [Field K]

@[expose] def orbs : List (List (Fin Tag.E6.rank)) := [[nd0, nd5], [nd2, nd4], [nd3], [nd1]]

@[expose] def sX (l : List (Fin Tag.E6.rank)) (c : K) : hV.minGroup K :=
  (l.map fun i => hV.xm K (Pi.single i 1) c).prod

@[expose] def sY (l : List (Fin Tag.E6.rank)) (c : K) : hV.minGroup K :=
  (l.map fun i => hV.xm K (-Pi.single i 1) c).prod

@[expose] def F4simple : Subgroup (hV.minGroup K) :=
  Subgroup.closure {g | ∃ l ∈ orbs, ∃ c : K, g = sX hV K l c ∨ g = sY hV K l c}

variable {K}

theorem sX_mem_F4simple {l : List (Fin Tag.E6.rank)} (hl : l ∈ orbs) (c : K) : sX hV K l c ∈ F4simple hV K :=
  Subgroup.subset_closure ⟨l, hl, c, Or.inl rfl⟩

theorem sY_mem_F4simple {l : List (Fin Tag.E6.rank)} (hl : l ∈ orbs) (c : K) : sY hV K l c ∈ F4simple hV K :=
  Subgroup.subset_closure ⟨l, hl, c, Or.inr rfl⟩

theorem not_isRoot_of_forall {v : Fin Tag.E6.rank → ℤ} (h : ∀ k < 72, e6root k ≠ v) :
    ¬ IsRoot Tag.E6 v := fun hv => by
  obtain ⟨k, hk, rfl⟩ := RootCertificate.exists_root_eq Tag.E6.rootCertificate_check hv
  exact h k hk rfl

theorem xm_comm_of_not_root {γ δ : Fin Tag.E6.rank → ℤ} (hγ : IsRoot Tag.E6 γ)
    (hδ : IsRoot Tag.E6 δ) (hne : γ + δ ≠ 0) (hnr : ¬ IsRoot Tag.E6 (γ + δ)) (c d : K) :
    hV.xm K γ c * hV.xm K δ d = hV.xm K δ d * hV.xm K γ c :=
  commutatorElement_eq_one_iff_mul_comm.1 ((hV.commutator_xm K hγ hδ hne).2 hnr c d)

section CharTwo

variable [CharP K 2]

theorem nm_conj_root (i : Fin Tag.E6.rank) {k : ℕ} (hk : k < 72) (c : K) :
    hV.nm K i * hV.xm K (e6root k) c * (hV.nm K i)⁻¹ =
      hV.xm K (e6root (Tag.E6.rootCertificate.image k i)) c := by
  obtain ⟨σ, hσ, h⟩ := hV.nm_conj_xm K (isRoot_e6root hk) i
  have hσ1 : σ = 1 := by
    rcases hσ with h1 | h1
    · exact h1
    · rw [h1, CharTwo.neg_eq]
  rw [h, hσ1, one_mul]
  have := MinData.root_image (τ := Tag.E6) (k := k) hk i
  exact congrArg (fun v => hV.xm K v c) this.symm

theorem image_lt' (i : Fin Tag.E6.rank) {k : ℕ} (hk : k < 72) : Tag.E6.rootCertificate.image k i < 72 :=
  MinData.image_lt (τ := Tag.E6) hk i

@[expose] def wMv : ℕ → hV.minGroup K
  | 0 => hV.nm K nd1
  | 1 => hV.nm K nd3
  | 2 => hV.nm K nd0 * hV.nm K nd5
  | _ => hV.nm K nd2 * hV.nm K nd4

theorem wMv_conj (m : ℕ) {k : ℕ} (hk : k < 72) (c : K) :
    wMv hV m * hV.xm K (e6root k) c * (wMv hV m)⁻¹ = hV.xm K (e6root (mvIdx m k)) c := by
  match m with
  | 0 => exact nm_conj_root hV nd1 hk c
  | 1 => exact nm_conj_root hV nd3 hk c
  | 2 =>
    change hV.nm K nd0 * hV.nm K nd5 * hV.xm K (e6root k) c * (hV.nm K nd0 * hV.nm K nd5)⁻¹ = _
    rw [_root_.mul_inv_rev, show hV.nm K nd0 * hV.nm K nd5 * hV.xm K (e6root k) c *
      ((hV.nm K nd5)⁻¹ * (hV.nm K nd0)⁻¹) = hV.nm K nd0 * (hV.nm K nd5 * hV.xm K (e6root k) c *
      (hV.nm K nd5)⁻¹) * (hV.nm K nd0)⁻¹ by group, nm_conj_root hV nd5 hk,
      nm_conj_root hV nd0 (image_lt' nd5 hk)]
    rfl
  | m + 3 =>
    change hV.nm K nd2 * hV.nm K nd4 * hV.xm K (e6root k) c * (hV.nm K nd2 * hV.nm K nd4)⁻¹ = _
    rw [_root_.mul_inv_rev, show hV.nm K nd2 * hV.nm K nd4 * hV.xm K (e6root k) c *
      ((hV.nm K nd4)⁻¹ * (hV.nm K nd2)⁻¹) = hV.nm K nd2 * (hV.nm K nd4 * hV.xm K (e6root k) c *
      (hV.nm K nd4)⁻¹) * (hV.nm K nd2)⁻¹ by group, nm_conj_root hV nd4 hk,
      nm_conj_root hV nd2 (image_lt' nd4 hk)]
    rfl

theorem isRoot_neg_single (i : Fin Tag.E6.rank) : IsRoot Tag.E6 (-Pi.single i 1) := by
  obtain ⟨k, hk, h⟩ := exists_neg_single i
  rw [← h]; exact isRoot_e6root hk

theorem nm_mem_of_single {i : Fin Tag.E6.rank} (hl : [i] ∈ orbs) :
    hV.nm K i ∈ F4simple hV K := by
  have h1 := sX_mem_F4simple hV hl (1 : K)
  have h2 := sY_mem_F4simple hV hl (-1 : K)
  simp only [sX, sY, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one] at h1 h2
  have := mul_mem (mul_mem h1 h2) h1
  simpa [MinData.Valid.nm, MinData.Valid.nt] using this

theorem group_pair_prod {G : Type*} [Group G] (a0 b0 a5 b5 : G) (h1 : a5 * b0 = b0 * a5)
    (h2 : b5 * a0 = a0 * b5) (h3 : a5 * a0 = a0 * a5) :
    a0 * b0 * a0 * (a5 * b5 * a5) = a0 * a5 * (b0 * b5) * (a0 * a5) := by
  have h1' : ∀ X, a5 * (b0 * X) = b0 * (a5 * X) := fun X => by rw [← mul_assoc, h1, mul_assoc]
  have h2' : ∀ X, b5 * (a0 * X) = a0 * (b5 * X) := fun X => by rw [← mul_assoc, h2, mul_assoc]
  have h3' : ∀ X, a5 * (a0 * X) = a0 * (a5 * X) := fun X => by rw [← mul_assoc, h3, mul_assoc]
  simp only [mul_assoc]
  rw [h1', h2', h3']

theorem nm_mul_mem_of_pair {i j : Fin Tag.E6.rank} (hl : [i, j] ∈ orbs)
    (hp : (∀ k < 72, e6root k ≠ Pi.single j 1 + -Pi.single i 1) ∧
      (∀ k < 72, e6root k ≠ -Pi.single j 1 + Pi.single i 1) ∧
      (∀ k < 72, e6root k ≠ Pi.single j 1 + Pi.single i 1) ∧
      Pi.single j 1 + -Pi.single i 1 ≠ (0 : Fin Tag.E6.rank → ℤ) ∧
      -Pi.single j 1 + Pi.single i 1 ≠ (0 : Fin Tag.E6.rank → ℤ) ∧
      Pi.single j 1 + Pi.single i 1 ≠ (0 : Fin Tag.E6.rank → ℤ)) :
    hV.nm K i * hV.nm K j ∈ F4simple hV K := by
  obtain ⟨hp1, hp2, hp3, hn1, hn2, hn3⟩ := hp
  have h1 : hV.xm K (Pi.single j 1) 1 * hV.xm K (-Pi.single i 1) (-1) =
      hV.xm K (-Pi.single i 1) (-1) * hV.xm K (Pi.single j 1) 1 :=
    xm_comm_of_not_root hV (isRoot_single' j) (isRoot_neg_single i) hn1
      (not_isRoot_of_forall hp1) _ _
  have h2 : hV.xm K (-Pi.single j 1) (-1) * hV.xm K (Pi.single i 1) 1 =
      hV.xm K (Pi.single i 1) 1 * hV.xm K (-Pi.single j 1) (-1) :=
    xm_comm_of_not_root hV (isRoot_neg_single j) (isRoot_single' i) hn2
      (not_isRoot_of_forall hp2) _ _
  have h3 : hV.xm K (Pi.single j 1) 1 * hV.xm K (Pi.single i 1) 1 =
      hV.xm K (Pi.single i 1) 1 * hV.xm K (Pi.single j 1) 1 :=
    xm_comm_of_not_root hV (isRoot_single' j) (isRoot_single' i) hn3
      (not_isRoot_of_forall hp3) _ _
  have e := group_pair_prod _ _ _ _ h1 h2 h3
  have hX := sX_mem_F4simple hV hl (1 : K)
  have hY := sY_mem_F4simple hV hl (-1 : K)
  simp only [sX, sY, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one] at hX hY
  have := mul_mem (mul_mem hX hY) hX
  rw [← e] at this
  simpa [MinData.Valid.nm, MinData.Valid.nt, mul_assoc] using this

theorem wMv_mem (m : ℕ) : wMv hV m ∈ F4simple hV (K := K) := by
  match m with
  | 0 => exact nm_mem_of_single hV (i := nd1) (show [nd1] ∈ orbs by decide)
  | 1 => exact nm_mem_of_single hV (i := nd3) (show [nd3] ∈ orbs by decide)
  | 2 =>
    have hl : [nd0, nd5] ∈ orbs := by decide
    exact nm_mul_mem_of_pair hV (i := nd0) (j := nd5) hl
      (pair_sums_not_root (nd0, nd5) List.mem_cons_self)
  | m + 3 =>
    have hl : [nd2, nd4] ∈ orbs := by decide
    exact nm_mul_mem_of_pair hV (i := nd2) (j := nd4) hl
      (pair_sums_not_root (nd2, nd4) (by simp))

theorem gen_root (k : ℕ) (hk : k < 72) (c : K) :
    gen hV K (e6root k) c =
      if gamK k = k then hV.xm K (e6root k) c
      else hV.xm K (e6root k) c * hV.xm K (e6root (gamK k)) c := by
  unfold gen
  by_cases h : gamK k = k
  · rw [ite_eq_left ((fixed_iff hk).2 h), ite_eq_left h]
  · rw [ite_eq_right (fun h' => h ((fixed_iff hk).1 h')), ite_eq_right h, graphRoot_root k hk]

theorem gen_conj (m : ℕ) {k p : ℕ} (hk : k < 72) (hp : p < 72) (hmv : mvIdx m p = k)
    (hfix : gamK k = k ↔ gamK p = p) (hgam : gamK k = mvIdx m (gamK p)) (c : K) :
    wMv hV m * gen hV K (e6root p) c * (wMv hV m)⁻¹ = gen hV K (e6root k) c := by
  rw [gen_root hV p hp, gen_root hV k hk]
  by_cases h : gamK p = p
  · rw [ite_eq_left h, ite_eq_left (hfix.2 h), wMv_conj hV m hp, hmv]
  · rw [ite_eq_right h, ite_eq_right (fun h' => h (hfix.1 h')),
      show wMv hV m * (hV.xm K (e6root p) c * hV.xm K (e6root (gamK p)) c) * (wMv hV m)⁻¹ =
        (wMv hV m * hV.xm K (e6root p) c * (wMv hV m)⁻¹) *
          (wMv hV m * hV.xm K (e6root (gamK p)) c * (wMv hV m)⁻¹) by group,
      wMv_conj hV m hp, wMv_conj hV m (gamK_lt p hp), hmv, ← hgam]

theorem gen_single_pair (i j : Fin Tag.E6.rank) (hg : graphRoot (Pi.single i 1) = Pi.single j 1)
    (hne : (Pi.single j 1 : Fin Tag.E6.rank → ℤ) ≠ Pi.single i 1) (c : K) :
    gen hV K (Pi.single i 1) c = hV.xm K (Pi.single i 1) c * hV.xm K (Pi.single j 1) c := by
  unfold gen
  rw [ite_eq_right (by rw [hg]; exact hne), hg]

theorem gen_single_fix (i : Fin Tag.E6.rank) (hg : graphRoot (Pi.single i 1) = Pi.single i 1)
    (c : K) : gen hV K (Pi.single i 1) c = hV.xm K (Pi.single i 1) c := by
  unfold gen
  rw [ite_eq_left hg]

theorem sX_pair (i j : Fin Tag.E6.rank) (c : K) :
    sX hV K [i, j] c = hV.xm K (Pi.single i 1) c * hV.xm K (Pi.single j 1) c := by
  simp only [sX, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]

theorem sX_single (i : Fin Tag.E6.rank) (c : K) :
    sX hV K [i] c = hV.xm K (Pi.single i 1) c := by
  simp only [sX, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]

theorem gen_pair_mem {i j : Fin Tag.E6.rank} (hl : [i, j] ∈ orbs)
    (hg : graphRoot (Pi.single i 1) = Pi.single j 1)
    (hg' : graphRoot (Pi.single j 1) = Pi.single i 1)
    (hne : (Pi.single j 1 : Fin Tag.E6.rank → ℤ) ≠ Pi.single i 1)
    (hp : (∀ k < 72, e6root k ≠ Pi.single j 1 + Pi.single i 1) ∧
      Pi.single j 1 + Pi.single i 1 ≠ (0 : Fin Tag.E6.rank → ℤ)) (c : K) :
    gen hV K (Pi.single i 1) c ∈ F4simple hV K ∧ gen hV K (Pi.single j 1) c ∈ F4simple hV K := by
  have h := sX_mem_F4simple hV hl c
  rw [sX_pair] at h
  have hc := xm_comm_of_not_root hV (isRoot_single' j) (isRoot_single' i) hp.2
    (not_isRoot_of_forall hp.1) c c
  refine ⟨?_, ?_⟩
  · rw [gen_single_pair hV i j hg (hne) c]; exact h
  · rw [gen_single_pair hV j i hg' (Ne.symm hne) c, hc]; exact h

theorem gen_mem_of_simple (k : ℕ) (hk : k < 6) (c : K) :
    gen hV K (e6root k) c ∈ F4simple hV K := by
  have p1 := pair_sums_not_root (nd0, nd5) List.mem_cons_self
  have p2 := pair_sums_not_root (nd2, nd4) (by simp)
  have P05 := gen_pair_mem hV (i := nd0) (j := nd5) (by decide) gam_single_zero gam_single_five
    (by decide) ⟨p1.2.2.1, p1.2.2.2.2.2⟩ c
  have P24 := gen_pair_mem hV (i := nd2) (j := nd4) (by decide) gam_single_two gam_single_four
    (by decide) ⟨p2.2.2.1, p2.2.2.2.2.2⟩ c
  interval_cases k
  · rw [e6root_simple nd0]; exact P05.1
  · rw [e6root_simple nd1, gen_single_fix hV nd1 gam_single_one]
    have := sX_mem_F4simple hV (l := [nd1]) (by decide) c
    rwa [sX_single] at this
  · rw [e6root_simple nd2]; exact P24.1
  · rw [e6root_simple nd3, gen_single_fix hV nd3 gam_single_three]
    have := sX_mem_F4simple hV (l := [nd3]) (by decide) c
    rwa [sX_single] at this
  · rw [e6root_simple nd4]; exact P24.2
  · rw [e6root_simple nd5]; exact P05.2

theorem F4in27_le_F4simple : F4in27 hV K ≤ F4simple hV K := by
  refine (Subgroup.closure_le _).2 ?_
  rintro _ ⟨α, hα, c, rfl⟩
  obtain ⟨k, hk, rfl⟩ := RootCertificate.exists_root_eq Tag.E6.rootCertificate_check hα
  have key : ∀ k < 72, ∀ c : K, gen hV K (e6root k) c ∈ F4simple hV K := by
    apply reach_all (fun k => ∀ c : K, gen hV K (e6root k) c ∈ F4simple hV K)
    · exact fun k hk c => gen_mem_of_simple hV k hk c
    · intro k p m hmem hP c
      obtain ⟨hk, hp, hmv, hfix, hgam⟩ := ord_step_check _ hmem
      have := mul_mem (mul_mem (wMv_mem hV (K := K) m) (hP c)) (inv_mem (wMv_mem hV (K := K) m))
      rwa [gen_conj hV m hk hp hmv hfix hgam c] at this
  exact key k hk c

theorem gen_pair_gen (α β : Fin Tag.E6.rank → ℤ) (hg : graphRoot α = β) (hne : β ≠ α) (c : K) :
    gen hV K α c = hV.xm K α c * hV.xm K β c := by
  unfold gen
  rw [ite_eq_right (by rw [hg]; exact hne), hg]

theorem gen_fix_gen (α : Fin Tag.E6.rank → ℤ) (hg : graphRoot α = α) (c : K) :
    gen hV K α c = hV.xm K α c := by
  unfold gen
  rw [ite_eq_left hg]

theorem sY_pair (i j : Fin Tag.E6.rank) (c : K) :
    sY hV K [i, j] c = hV.xm K (-Pi.single i 1) c * hV.xm K (-Pi.single j 1) c := by
  simp only [sY, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]

theorem sY_single (i : Fin Tag.E6.rank) (c : K) :
    sY hV K [i] c = hV.xm K (-Pi.single i 1) c := by
  simp only [sY, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]

theorem sX_mem_F4in27 {l : List (Fin Tag.E6.rank)} (hl : l ∈ orbs) (c : K) :
    sX hV K l c ∈ F4in27 hV K := by
  simp only [orbs, List.mem_cons, List.not_mem_nil, or_false] at hl
  rcases hl with rfl | rfl | rfl | rfl
  · rw [sX_pair, ← gen_pair_gen hV _ _ gam_single_zero (by decide)]
    exact gen_mem_F4in27 hV _ (isRoot_single' _) c
  · rw [sX_pair, ← gen_pair_gen hV _ _ gam_single_two (by decide)]
    exact gen_mem_F4in27 hV _ (isRoot_single' _) c
  · rw [sX_single, ← gen_fix_gen hV _ gam_single_three]
    exact gen_mem_F4in27 hV _ (isRoot_single' _) c
  · rw [sX_single, ← gen_fix_gen hV _ gam_single_one]
    exact gen_mem_F4in27 hV _ (isRoot_single' _) c

theorem sY_mem_F4in27 {l : List (Fin Tag.E6.rank)} (hl : l ∈ orbs) (c : K) :
    sY hV K l c ∈ F4in27 hV K := by
  simp only [orbs, List.mem_cons, List.not_mem_nil, or_false] at hl
  rcases hl with rfl | rfl | rfl | rfl
  · rw [sY_pair, ← gen_pair_gen hV _ _ (by rw [gam_neg, gam_single_zero]) (by decide)]
    exact gen_mem_F4in27 hV _ (isRoot_neg_single _) c
  · rw [sY_pair, ← gen_pair_gen hV _ _ (by rw [gam_neg, gam_single_two]) (by decide)]
    exact gen_mem_F4in27 hV _ (isRoot_neg_single _) c
  · rw [sY_single, ← gen_fix_gen hV _ (by rw [gam_neg, gam_single_three])]
    exact gen_mem_F4in27 hV _ (isRoot_neg_single _) c
  · rw [sY_single, ← gen_fix_gen hV _ (by rw [gam_neg, gam_single_one])]
    exact gen_mem_F4in27 hV _ (isRoot_neg_single _) c

theorem F4simple_le_F4in27 : F4simple hV K ≤ F4in27 hV K := by
  refine (Subgroup.closure_le _).2 ?_
  rintro _ ⟨l, hl, c, rfl | rfl⟩
  · exact sX_mem_F4in27 hV hl c
  · exact sY_mem_F4in27 hV hl c

theorem F4in27_eq_F4simple : F4in27 hV K = F4simple hV K :=
  le_antisymm (F4in27_le_F4simple hV) (F4simple_le_F4in27 hV)

end CharTwo

end CFSG.HardMathSupport.Cooperstein.Coordinator.FFExc
