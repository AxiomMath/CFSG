module

import CFSG.LocalAnalysis.SeitzReduction.EnKLHeis
public import CFSG.LocalAnalysis.SeitzReduction.TwistedE6PilotCentralizerT
public import CFSG.RankThree.GF2n.Stroth80.Sec117ConfigBasic

public section

namespace CFSG.SeitzReduction.TwistedE6Pilot

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.RankThree.GF2n.Stroth80 Polynomial

variable {f : ℕ} {K : Type} [Field K]

theorem eq_zero_of_forall_mul_add_mul_frobenius (hf : 1 ≤ f) (hK : Nat.card K = (2 ^ f) ^ 2)
    {σ : K →+* K} (hσ : ∀ c, σ c = c ^ 2 ^ f) {a b e : K}
    (h : ∀ c : K, a * c + b * σ c + e * (c * σ c) = 0) : a = 0 ∧ b = 0 ∧ e = 0 := by
  have := finite_of_card hK
  have : Fintype K := Fintype.ofFinite K
  have hq : 2 ≤ 2 ^ f := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  set p : K[X] := C a * X ^ 1 + C b * X ^ 2 ^ f + C e * X ^ (2 ^ f + 1) with hp
  have hdeg : p.natDegree ≤ 2 ^ f + 1 :=
    natDegree_add_le_of_degree_le (natDegree_add_le_of_degree_le
      ((natDegree_C_mul_X_pow_le a 1).trans (by omega))
      ((natDegree_C_mul_X_pow_le b _).trans (by omega))) (natDegree_C_mul_X_pow_le e _)
  have hp0 : p = 0 := by
    refine eq_zero_of_forall_eval_zero_of_natDegree_lt_card p (fun c => ?_) ?_
    · have hc := h c
      rw [hσ] at hc
      simp only [hp, eval_add, eval_mul, eval_C, eval_pow, eval_X]
      rw [← hc]
      ring
    · rw [Cardinal.mk_fintype, Fintype.card_eq_nat_card, hK]
      exact_mod_cast hdeg.trans_lt (by nlinarith)
  have h1 : (1 : ℕ) ≠ 2 ^ f := by omega
  have h2 : (1 : ℕ) ≠ 2 ^ f + 1 := by omega
  have h3 : 2 ^ f ≠ 2 ^ f + 1 := by omega
  have ca := congrArg (fun p : K[X] => p.coeff 1) hp0
  have cb := congrArg (fun p : K[X] => p.coeff (2 ^ f)) hp0
  have ce := congrArg (fun p : K[X] => p.coeff (2 ^ f + 1)) hp0
  simp only [hp, coeff_add, coeff_C_mul_X_pow, coeff_zero] at ca cb ce
  simp only [h1, h2, h3, h1.symm, h2.symm, h3.symm, if_true, if_false, add_zero,
    zero_add] at ca cb ce
  exact ⟨ca, cb, ce⟩


variable {k : Type} [Field k] [Algebra k K]

local instance twistedE6KLFixedNeZero : NeZero TwistTag.E6.tag.rank := ⟨by decide⟩

open CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Heis in
private theorem permLattice_twistedE6_apply_iθ_eq_zero
    {γ : Fin TwistTag.E6.tag.rank → ℤ} (hγ0 : γ (iθ TwistTag.E6.tag) = 0) :
    permLattice TwistTag.E6.perm γ (iθ TwistTag.E6.tag) = 0 := by
  have hperm : TwistTag.E6.perm (iθ TwistTag.E6.tag) = iθ TwistTag.E6.tag := by decide
  have hsymm : TwistTag.E6.perm.symm (iθ TwistTag.E6.tag) = iθ TwistTag.E6.tag := by
    simpa [hperm] using Equiv.symm_apply_apply TwistTag.E6.perm (iθ TwistTag.E6.tag)
  rw [permLattice]
  simpa [Function.comp_apply, hsymm] using hγ0

open CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Heis in
private theorem twistedE6PairX_conj_eq {σ : K →+* K}
    {α : Fin TwistTag.E6.tag.rank → ℤ} (hα : IsRoot TwistTag.E6.tag α) (c : K)
    (q : ModGL TwistTag.E6.tag K) :
    twistedE6PairX σ α c * q * (twistedE6PairX σ α c)⁻¹ =
      pinnedX TwistTag.E6.tag K (permLattice TwistTag.E6.perm α) (σ c) *
        (pinnedX TwistTag.E6.tag K α c * q * (pinnedX TwistTag.E6.tag K α c)⁻¹) *
        (pinnedX TwistTag.E6.tag K (permLattice TwistTag.E6.perm α) (σ c))⁻¹ := by
  rw [twistedE6PairX]
  have hcomm := (commute_pinnedX_permLattice_twistedE6 hα c (σ c)).eq
  rw [hcomm]
  group

open CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Heis in
private theorem heisCoord_conj_twistedE6PairX_poly [CharP K 2]
    {σ : K →+* K} {α : Fin TwistTag.E6.tag.rank → ℤ} (hα : IsRoot TwistTag.E6.tag α)
    (hα0 : α (iθ TwistTag.E6.tag) = 0) {q : ModGL TwistTag.E6.tag K}
    (hq : q ∈ Qθ TwistTag.E6.tag K)
    (hfix : ∀ c : K, heisCoord TwistTag.E6.tag K
      (twistedE6PairX σ α c * q * (twistedE6PairX σ α c)⁻¹) =
        heisCoord TwistTag.E6.tag K q)
    {ν : Fin TwistTag.E6.tag.rank → ℤ} (hν : ν ∈ rootFinset TwistTag.E6.tag) :
    ∀ c : K,
      heisCoord TwistTag.E6.tag K q (ν - α) * c +
        heisCoord TwistTag.E6.tag K q (ν - permLattice TwistTag.E6.perm α) * σ c +
        (if ν - permLattice TwistTag.E6.perm α ∈ rootFinset TwistTag.E6.tag then
          heisCoord TwistTag.E6.tag K q (ν - α - permLattice TwistTag.E6.perm α) else 0) *
            (c * σ c) = 0 := by
  have hβr : IsRoot TwistTag.E6.tag (permLattice TwistTag.E6.perm α) :=
    hα.permLattice TwistTag.E6.cartan_perm
  have hβ0 := permLattice_twistedE6_apply_iθ_eq_zero hα0
  intro c
  have h1 := (EPilot.heisCoord_conj_pinnedX_of_deg_zero (τ := TwistTag.E6.tag)
    (Or.inl rfl) hα hα0 c hq)
  have h2 := (EPilot.heisCoord_conj_pinnedX_of_deg_zero (τ := TwistTag.E6.tag)
    (Or.inl rfl) hβr hβ0 (σ c) h1.1)
  have hc := congrFun (hfix c) ν
  rw [twistedE6PairX_conj_eq hα c q, h2.2 ν, h1.2 ν,
    h1.2 (ν - permLattice TwistTag.E6.perm α)] at hc
  simp only [if_pos hν] at hc
  by_cases hνβ : ν - permLattice TwistTag.E6.perm α ∈ rootFinset TwistTag.E6.tag
  · simp only [if_pos hνβ] at hc ⊢
    ring_nf at hc ⊢
    linear_combination hc
  · simp only [if_neg hνβ] at hc ⊢
    ring_nf at hc ⊢
    linear_combination hc

open CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Heis in
private theorem heisCoord_conj_twistedE6PairX [CharP K 2] {f : ℕ} (hf : 1 ≤ f)
    (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K →+* K} (hσ : ∀ c, σ c = c ^ 2 ^ f)
    {α : Fin TwistTag.E6.tag.rank → ℤ} (hα : IsRoot TwistTag.E6.tag α)
    (hα0 : α (iθ TwistTag.E6.tag) = 0) {q : ModGL TwistTag.E6.tag K}
    (hq : q ∈ Qθ TwistTag.E6.tag K)
    (hfix : ∀ c : K, heisCoord TwistTag.E6.tag K
      (twistedE6PairX σ α c * q * (twistedE6PairX σ α c)⁻¹) =
        heisCoord TwistTag.E6.tag K q)
    {ν : Fin TwistTag.E6.tag.rank → ℤ} (hν : ν ∈ rootFinset TwistTag.E6.tag) :
    heisCoord TwistTag.E6.tag K q (ν - α) = 0 ∧
      heisCoord TwistTag.E6.tag K q (ν - permLattice TwistTag.E6.perm α) = 0 := by
  have hpoly := heisCoord_conj_twistedE6PairX_poly hα hα0 hq hfix hν
  have hres := eq_zero_of_forall_mul_add_mul_frobenius (K := K) hf hK hσ hpoly
  exact ⟨hres.1, hres.2.1⟩

open CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Heis in
private theorem heisCoord_eq_of_mul_inv_mem_highRoot {q q' : ModGL TwistTag.E6.tag K}
    (hq : q ∈ Qθ TwistTag.E6.tag K) (h : q' * q⁻¹ ∈ Uθ TwistTag.E6.tag K) :
    heisCoord TwistTag.E6.tag K q' = heisCoord TwistTag.E6.tag K q := by
  have hz : q' * q⁻¹ ∈ Qθ TwistTag.E6.tag K := Uθ_le_Qθ h
  have hz0 : heisCoord TwistTag.E6.tag K (q' * q⁻¹) = 0 :=
    ((heisCoord_spec TwistTag.E6.tag K).eq_zero_iff _ hz).2 h
  have hmul := (heisCoord_spec TwistTag.E6.tag K).mul (q' * q⁻¹) hz q hq
  have hqeq : (q' * q⁻¹) * q = q' := by group
  rw [hqeq, hz0, zero_add] at hmul
  exact hmul

open CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Heis in
private theorem heisCoord_eq_zero_of_fixed_pos_twistedE6PairX [CharP K 2] {f : ℕ}
    (hf : 1 ≤ f) (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K →+* K}
    (hσ : ∀ c, σ c = c ^ 2 ^ f) {q : ModGL TwistTag.E6.tag K}
    (hq : q ∈ Qθ TwistTag.E6.tag K)
    (hfix : ∀ (j : Fin TwistTag.E6.tag.rank), j ≠ 1 → ∀ c : K,
      heisCoord TwistTag.E6.tag K (twistedE6PairX σ (Pi.single j 1) c * q *
        (twistedE6PairX σ (Pi.single j 1) c)⁻¹) = heisCoord TwistTag.E6.tag K q)
    {μ : Fin TwistTag.E6.tag.rank → ℤ} (hμ : μ ∈ Deg1 TwistTag.E6.tag)
    (hμne : μ ≠ e6HighestRoot - Pi.single (iθ TwistTag.E6.tag) 1) :
    heisCoord TwistTag.E6.tag K q μ = 0 := by
  obtain ⟨hμr, hμ1⟩ := CoordAux.mem_Deg1.1 hμ
  obtain ⟨j, hj, hν⟩ := EPilot.exists_add_single_mem_rootFinset_of_deg_one
    (τ := TwistTag.E6.tag) (Or.inl rfl) μ (mem_rootFinset.2 hμr) hμ1 (by
      change μ ≠ e6HighestRoot - Pi.single (iθ TwistTag.E6.tag) 1
      exact hμne)
  have hres := heisCoord_conj_twistedE6PairX (K := K) hf hK hσ (isRoot_single _ j)
    (by simp [Ne.symm hj]) hq (hfix j hj) hν
  simpa [add_sub_cancel_right] using hres.1

open CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Heis in
private theorem heisCoord_eq_zero_of_fixed_neg_twistedE6PairX [CharP K 2] {f : ℕ}
    (hf : 1 ≤ f) (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K →+* K}
    (hσ : ∀ c, σ c = c ^ 2 ^ f) {q : ModGL TwistTag.E6.tag K}
    (hq : q ∈ Qθ TwistTag.E6.tag K)
    (hfix : ∀ (j : Fin TwistTag.E6.tag.rank), j ≠ 1 → ∀ c : K,
      heisCoord TwistTag.E6.tag K (twistedE6PairX σ (-Pi.single j 1) c * q *
        (twistedE6PairX σ (-Pi.single j 1) c)⁻¹) = heisCoord TwistTag.E6.tag K q)
    {μ : Fin TwistTag.E6.tag.rank → ℤ} (hμ : μ ∈ Deg1 TwistTag.E6.tag)
    (hμne : μ ≠ Pi.single (iθ TwistTag.E6.tag) 1) :
    heisCoord TwistTag.E6.tag K q μ = 0 := by
  obtain ⟨hμr, hμ1⟩ := CoordAux.mem_Deg1.1 hμ
  obtain ⟨j, hj, hν⟩ := EPilot.exists_sub_single_mem_rootFinset_of_deg_one
    (τ := TwistTag.E6.tag) (Or.inl rfl) μ (mem_rootFinset.2 hμr) hμ1 hμne
  have hres := heisCoord_conj_twistedE6PairX (K := K) hf hK hσ
    (CFSG.LieType.Chevalley.IsRoot.neg (isRoot_single _ j)) (by simp [Ne.symm hj]) hq
    (hfix j hj) hν
  have hsub : (μ - Pi.single j 1) - -Pi.single j 1 = μ := by abel
  simpa [hsub] using hres.1

open CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Heis in
private theorem commute_pinnedX_e6HighestRoot_of_deg_zero [CharP K 2]
    {γ : Fin TwistTag.E6.tag.rank → ℤ} (hγ : IsRoot TwistTag.E6.tag γ)
    (hγ0 : γ (iθ TwistTag.E6.tag) = 0) (c d : K) :
    Commute (pinnedX TwistTag.E6.tag K γ c) (pinnedX TwistTag.E6.tag K e6HighestRoot d) := by
  have hdeg : (γ + e6HighestRoot) (iθ TwistTag.E6.tag) = 2 := by
    rw [Pi.add_apply, hγ0, zero_add]
    decide
  have hn : ¬ IsRoot TwistTag.E6.tag (γ + e6HighestRoot) := by
    intro hr
    have hh := CoordAux.eq_highRoot_of_two_le hr (by simp [hdeg])
    have heq : γ + e6HighestRoot = e6HighestRoot := by
      change γ + e6HighestRoot = e6HighestRoot at hh
      exact hh
    have heq' : γ + e6HighestRoot = 0 + e6HighestRoot := by simpa using heq
    exact hγ.ne_zero (add_right_cancel heq')
  have hne : γ ≠ -e6HighestRoot := by
    intro h
    have h1 := congrFun h (iθ TwistTag.E6.tag)
    rw [hγ0] at h1
    have h2 : (-e6HighestRoot) (iθ TwistTag.E6.tag) = -2 := by decide
    rw [h2] at h1
    norm_num at h1
  exact CFSG.SeitzReduction.commute_pinnedX_of_oddDeriv (τ := TwistTag.E6.tag) hγ
    isRoot_e6HighestRoot hne hn c d

open CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Heis in
private theorem twistedE6PairX_mem_posUnipotent {σ : K →+* K}
    {γ : Fin TwistTag.E6.tag.rank → ℤ} (hγ : IsRoot TwistTag.E6.tag γ)
    (hp : 0 < height γ) (c : K) :
    twistedE6PairX σ γ c ∈ posUnipotent TwistTag.E6.tag K := by
  rw [twistedE6PairX]
  refine mul_mem (pinnedX_mem_rootSpan
    (S := {α : Fin TwistTag.E6.tag.rank → ℤ | IsRoot TwistTag.E6.tag α ∧ 0 < height α})
    ⟨hγ, hp⟩ c) ?_
  exact pinnedX_mem_rootSpan
    (S := {α : Fin TwistTag.E6.tag.rank → ℤ | IsRoot TwistTag.E6.tag α ∧ 0 < height α})
    ⟨hγ.permLattice TwistTag.E6.cartan_perm, by rw [height_permLattice]; exact hp⟩ (σ c)

open CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Heis in
private theorem twistedE6PairX_mem_negUnipotent {σ : K →+* K}
    {γ : Fin TwistTag.E6.tag.rank → ℤ} (hγ : IsRoot TwistTag.E6.tag γ)
    (hn : height γ < 0) (c : K) :
    twistedE6PairX σ γ c ∈ negUnipotent TwistTag.E6.tag K := by
  rw [twistedE6PairX]
  refine mul_mem (pinnedX_mem_rootSpan
    (S := {α : Fin TwistTag.E6.tag.rank → ℤ | IsRoot TwistTag.E6.tag α ∧ height α < 0})
    ⟨hγ, hn⟩ c) ?_
  exact pinnedX_mem_rootSpan
    (S := {α : Fin TwistTag.E6.tag.rank → ℤ | IsRoot TwistTag.E6.tag α ∧ height α < 0})
    ⟨hγ.permLattice TwistTag.E6.cartan_perm, by rw [height_permLattice]; exact hn⟩ (σ c)

open CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Heis in
private theorem twistedE6PairX_mem_su6Levi [CharP K 2] {σ : K →+* K}
    (hσσ : ∀ c, σ (σ c) = c) {γ : Fin TwistTag.E6.tag.rank → ℤ}
    (hγ : IsRoot TwistTag.E6.tag γ) (hγ0 : γ (iθ TwistTag.E6.tag) = 0) (c : K) :
    twistedE6PairX σ γ c ∈ su6Levi σ := by
  refine mem_inf.2 ⟨?_, twistedE6PairX_mem_graphFixedRootGroup hσσ hγ c⟩
  rw [twistedE6PairX]
  refine mul_mem (pinnedX_mem_subsystemGroup_setA hγ hγ0 c) ?_
  have hρ : IsRoot TwistTag.E6.tag (permLattice TwistTag.E6.perm γ) :=
    hγ.permLattice TwistTag.E6.cartan_perm
  have hρ0 : permLattice TwistTag.E6.perm γ (iθ TwistTag.E6.tag) = 0 := by
    have hperm : TwistTag.E6.perm (iθ TwistTag.E6.tag) = iθ TwistTag.E6.tag := by decide
    have hsymm : TwistTag.E6.perm.symm (iθ TwistTag.E6.tag) = iθ TwistTag.E6.tag := by
      simpa [hperm] using Equiv.symm_apply_apply TwistTag.E6.perm (iθ TwistTag.E6.tag)
    rw [permLattice]
    simpa [Function.comp_apply, hsymm] using hγ0
  exact pinnedX_mem_subsystemGroup_setA hρ hρ0 (σ c)

open CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Heis in
private theorem commute_twistedE6PairX_e6HighestRoot_of_deg_zero [CharP K 2]
    {γ : Fin TwistTag.E6.tag.rank → ℤ} (hγ : IsRoot TwistTag.E6.tag γ)
    (hγ0 : γ (iθ TwistTag.E6.tag) = 0) (σ : K →+* K) (c d : K) :
    Commute (twistedE6PairX σ γ c) (pinnedX TwistTag.E6.tag K e6HighestRoot d) := by
  have hρ0 : permLattice TwistTag.E6.perm γ (iθ TwistTag.E6.tag) = 0 := by
    have hperm : TwistTag.E6.perm (iθ TwistTag.E6.tag) = iθ TwistTag.E6.tag := by decide
    have hsymm : TwistTag.E6.perm.symm (iθ TwistTag.E6.tag) = iθ TwistTag.E6.tag := by
      simpa [hperm] using Equiv.symm_apply_apply TwistTag.E6.perm (iθ TwistTag.E6.tag)
    rw [permLattice]
    simpa [Function.comp_apply, hsymm] using hγ0
  rw [twistedE6PairX]
  exact (commute_pinnedX_e6HighestRoot_of_deg_zero hγ hγ0 c d).mul_left
    (commute_pinnedX_e6HighestRoot_of_deg_zero
      (hγ.permLattice TwistTag.E6.cartan_perm) hρ0 (σ c) d)

private noncomputable def twistedE6PositiveGenerators (σ : K →+* K) :
    Set (ModGL TwistTag.E6.tag K) :=
  {g | ∃ (j : Fin TwistTag.E6.tag.rank) (_hj : j ≠ 1) (c : K),
    g = twistedE6PairX σ (Pi.single j 1) c}

private noncomputable def twistedE6NegativeGenerators (σ : K →+* K) :
    Set (ModGL TwistTag.E6.tag K) :=
  {g | ∃ (j : Fin TwistTag.E6.tag.rank) (_hj : j ≠ 1) (c : K),
    g = twistedE6PairX σ (-Pi.single j 1) c}

private noncomputable def twistedE6PositiveGroup (σ : K →+* K) :
    Subgroup (graphFixedRootGroup TwistTag.E6 K σ) :=
  (Subgroup.closure (twistedE6PositiveGenerators σ)).subgroupOf
    (graphFixedRootGroup TwistTag.E6 K σ)

private noncomputable def twistedE6NegativeGroup (σ : K →+* K) :
    Subgroup (graphFixedRootGroup TwistTag.E6 K σ) :=
  (Subgroup.closure (twistedE6NegativeGenerators σ)).subgroupOf
    (graphFixedRootGroup TwistTag.E6 K σ)

private noncomputable def twistedE6Z (σ : K →+* K) :
    Subgroup (graphFixedRootGroup TwistTag.E6 K σ) :=
  (rootSubgroup TwistTag.E6.tag K e6HighestRoot).subgroupOf
    (graphFixedRootGroup TwistTag.E6 K σ)

open CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Heis in
private noncomputable def twistedE6V (σ : K →+* K) :
    Set (graphFixedRootGroup TwistTag.E6 K σ) :=
  {x | (x : ModGL TwistTag.E6.tag K) ∈ Qθ TwistTag.E6.tag K ∧
    ∀ ν, ν ≠ e6HighestRoot - Pi.single (iθ TwistTag.E6.tag) 1 →
      heisCoord TwistTag.E6.tag K (x : ModGL TwistTag.E6.tag K) ν = 0}

open CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Heis in
private noncomputable def twistedE6V' (σ : K →+* K) :
    Set (graphFixedRootGroup TwistTag.E6 K σ) :=
  {x | (x : ModGL TwistTag.E6.tag K) ∈ Qθ TwistTag.E6.tag K ∧
    ∀ ν, ν ≠ Pi.single (iθ TwistTag.E6.tag) 1 →
      heisCoord TwistTag.E6.tag K (x : ModGL TwistTag.E6.tag K) ν = 0}

open CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Heis in
private theorem tRadical_le_Qθ {σ : K →+* K} :
    tRadical σ ≤ Qθ TwistTag.E6.tag K := by
  intro y hy
  have hy' := (mem_inf.1 hy).1
  rwa [show E6GraphLevi.setA =
    CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Heis.Jθ TwistTag.E6.tag from rfl] at hy'

private theorem twistedE6PositiveGroup_le_su6 [CharP K 2] {σ : K →+* K}
    (hσσ : ∀ c, σ (σ c) = c) :
    twistedE6PositiveGroup σ ≤
      (su6Levi σ).subgroupOf (graphFixedRootGroup TwistTag.E6 K σ) := by
  refine Subgroup.subgroupOf_mono _ ?_
  refine (Subgroup.closure_le (su6Levi σ)).2 ?_
  rintro g ⟨j, hj, c, rfl⟩
  exact twistedE6PairX_mem_su6Levi (σ := σ) (γ := Pi.single j 1) hσσ
    (isRoot_single _ j) (by
      rw [show CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Heis.iθ
        TwistTag.E6.tag = (1 : Fin TwistTag.E6.tag.rank) from rfl]
      simp [Ne.symm hj]) c

private theorem twistedE6NegativeGroup_le_su6 [CharP K 2] {σ : K →+* K}
    (hσσ : ∀ c, σ (σ c) = c) :
    twistedE6NegativeGroup σ ≤
      (su6Levi σ).subgroupOf (graphFixedRootGroup TwistTag.E6 K σ) := by
  refine Subgroup.subgroupOf_mono _ ?_
  refine (Subgroup.closure_le (su6Levi σ)).2 ?_
  rintro g ⟨j, hj, c, rfl⟩
  exact twistedE6PairX_mem_su6Levi (σ := σ) (γ := -Pi.single j 1) hσσ
    (CFSG.LieType.Chevalley.IsRoot.neg (isRoot_single _ j)) (by
      rw [show CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Heis.iθ
        TwistTag.E6.tag = (1 : Fin TwistTag.E6.tag.rank) from rfl]
      simp [Pi.neg_apply, Ne.symm hj]) c

private theorem twistedE6PositiveGroup_le_posUnipotent {σ : K →+* K} :
    twistedE6PositiveGroup σ ≤
      (posUnipotent TwistTag.E6.tag K).subgroupOf
        (graphFixedRootGroup TwistTag.E6 K σ) := by
  refine Subgroup.subgroupOf_mono _ ?_
  refine (Subgroup.closure_le (posUnipotent TwistTag.E6.tag K)).2 ?_
  rintro g ⟨j, hj, c, rfl⟩
  exact twistedE6PairX_mem_posUnipotent (σ := σ) (γ := Pi.single j 1)
    (isRoot_single _ j) (by simp [height, Pi.single, Function.update]) c

private theorem twistedE6NegativeGroup_le_negUnipotent {σ : K →+* K} :
    twistedE6NegativeGroup σ ≤
      (negUnipotent TwistTag.E6.tag K).subgroupOf
        (graphFixedRootGroup TwistTag.E6 K σ) := by
  refine Subgroup.subgroupOf_mono _ ?_
  refine (Subgroup.closure_le (negUnipotent TwistTag.E6.tag K)).2 ?_
  rintro g ⟨j, hj, c, rfl⟩
  exact twistedE6PairX_mem_negUnipotent (σ := σ) (γ := -Pi.single j 1)
    (CFSG.LieType.Chevalley.IsRoot.neg (isRoot_single _ j))
    (by simp [height, Pi.single, Function.update]) c

private theorem twistedE6PositiveGroup_isPGroup [Finite K] [CharP K 2] {σ : K →+* K} :
    IsPGroup 2 (twistedE6PositiveGroup σ) := by
  have hpos2 : IsPGroup 2 (posUnipotent TwistTag.E6.tag K) :=
    ((positive_root_triangularity.{0, 0} TwistTag.E6.tag).2 K 2).2.1
  exact (hpos2.comap_subtype (K := graphFixedRootGroup TwistTag.E6 K σ)).to_le
    (twistedE6PositiveGroup_le_posUnipotent (σ := σ))

private theorem twistedE6NegativeGroup_isPGroup [Finite K] [CharP K 2] {σ : K →+* K} :
    IsPGroup 2 (twistedE6NegativeGroup σ) := by
  have hneg2 : IsPGroup 2 (negUnipotent TwistTag.E6.tag K) :=
    ((positive_root_triangularity.{0, 0} TwistTag.E6.tag).2 K 2).2.2.2
  exact (hneg2.comap_subtype (K := graphFixedRootGroup TwistTag.E6 K σ)).to_le
    (twistedE6NegativeGroup_le_negUnipotent (σ := σ))

private theorem twistedE6PositiveGroup_le_N [CharP K 2] {σ : K →+* K}
    (hσσ : ∀ c, σ (σ c) = c) {N : Subgroup (graphFixedRootGroup TwistTag.E6 K σ)}
    (hLN : (su6Levi σ).subgroupOf (graphFixedRootGroup TwistTag.E6 K σ) ≤ N) :
    twistedE6PositiveGroup σ ≤ N :=
  (twistedE6PositiveGroup_le_su6 hσσ).trans hLN

private theorem twistedE6NegativeGroup_le_N [CharP K 2] {σ : K →+* K}
    (hσσ : ∀ c, σ (σ c) = c) {N : Subgroup (graphFixedRootGroup TwistTag.E6 K σ)}
    (hLN : (su6Levi σ).subgroupOf (graphFixedRootGroup TwistTag.E6 K σ) ≤ N) :
    twistedE6NegativeGroup σ ≤ N :=
  (twistedE6NegativeGroup_le_su6 hσσ).trans hLN

private theorem twistedE6A_conj_mem_Z [CharP K 2] {σ : K →+* K}
    {A : Subgroup (graphFixedRootGroup TwistTag.E6 K σ)}
    (hAQ : A ≤ (tRadical σ).subgroupOf (graphFixedRootGroup TwistTag.E6 K σ)) :
    ∀ x ∈ A, ∀ z ∈ twistedE6Z σ, x * z * x⁻¹ ∈ twistedE6Z σ := by
  intro x hx z hz
  have hzθ : (z : ModGL TwistTag.E6.tag K) ∈
      CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Heis.Uθ TwistTag.E6.tag K :=
    Subgroup.mem_subgroupOf.1 hz
  have hxQ : (x : ModGL TwistTag.E6.tag K) ∈
      CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Heis.Qθ TwistTag.E6.tag K :=
    tRadical_le_Qθ (Subgroup.mem_subgroupOf.1 (hAQ hx))
  have hxpos : (x : ModGL TwistTag.E6.tag K) ∈ posUnipotent TwistTag.E6.tag K :=
    parabolicRadical_le_posUnipotent
      (CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Heis.Jθ TwistTag.E6.tag) hxQ
  have hcomm : (z : ModGL TwistTag.E6.tag K) * (x : ModGL TwistTag.E6.tag K) =
      (x : ModGL TwistTag.E6.tag K) * (z : ModGL TwistTag.E6.tag K) :=
    CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Heis.CoordAux.Uθ_comm hzθ hxpos
  have hEq : x * z * x⁻¹ = z := Subtype.ext (by
    show (x : ModGL TwistTag.E6.tag K) * (z : ModGL TwistTag.E6.tag K) *
        (x : ModGL TwistTag.E6.tag K)⁻¹ = (z : ModGL TwistTag.E6.tag K)
    rw [hcomm.symm]
    group)
  rw [hEq]
  exact hz

private theorem twistedE6PositiveGroup_centralizes_Z [CharP K 2] {σ : K →+* K} :
    ∀ u ∈ twistedE6PositiveGroup σ, ∀ z ∈ twistedE6Z σ,
      u * z * u⁻¹ ∈ twistedE6Z σ := by
  intro u hu z hz
  have hupos : (u : ModGL TwistTag.E6.tag K) ∈ posUnipotent TwistTag.E6.tag K :=
    Subgroup.mem_subgroupOf.1
      (twistedE6PositiveGroup_le_posUnipotent (σ := σ) hu)
  obtain ⟨c, hc⟩ := mem_rootSubgroup.1 (Subgroup.mem_subgroupOf.1 hz)
  have hcomm := (commute_e6HighestRoot_of_mem_posUnipotent K hupos c).eq
  have hEq : u * z * u⁻¹ = z := Subtype.ext (by
    show (u : ModGL TwistTag.E6.tag K) * (z : ModGL TwistTag.E6.tag K) *
        (u : ModGL TwistTag.E6.tag K)⁻¹ = (z : ModGL TwistTag.E6.tag K)
    rw [← hc]
    have h : (u : ModGL TwistTag.E6.tag K) * pinnedX TwistTag.E6.tag K e6HighestRoot c *
        (u : ModGL TwistTag.E6.tag K)⁻¹ =
          pinnedX TwistTag.E6.tag K e6HighestRoot c := by
      rw [hcomm]
      group
    exact h)
  rw [hEq]
  exact hz

private theorem twistedE6NegativeGroup_le_centralizer_Z [CharP K 2] {σ : K →+* K} :
    twistedE6NegativeGroup σ ≤
      (Subgroup.centralizer (rootSubgroup TwistTag.E6.tag K e6HighestRoot :
        Set (ModGL TwistTag.E6.tag K))).subgroupOf
        (graphFixedRootGroup TwistTag.E6 K σ) := by
  refine Subgroup.subgroupOf_mono _ ?_
  refine (Subgroup.closure_le (Subgroup.centralizer
    (rootSubgroup TwistTag.E6.tag K e6HighestRoot :
      Set (ModGL TwistTag.E6.tag K)))).2 ?_
  rintro g ⟨j, hj, c, rfl⟩
  change twistedE6PairX σ (-Pi.single j 1) c ∈
    Subgroup.centralizer (rootSubgroup TwistTag.E6.tag K e6HighestRoot :
      Set (ModGL TwistTag.E6.tag K))
  rw [Subgroup.mem_centralizer_iff]
  intro w hw
  obtain ⟨d, rfl⟩ := mem_rootSubgroup.1 hw
  have hneg0 : (-Pi.single j 1 : Fin TwistTag.E6.tag.rank → ℤ)
      (CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Heis.iθ TwistTag.E6.tag) = 0 := by
    rw [show CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Heis.iθ
      TwistTag.E6.tag = (1 : Fin TwistTag.E6.tag.rank) from rfl]
    simp [Pi.neg_apply, Ne.symm hj]
  have hcomm : Commute (twistedE6PairX σ (-Pi.single j 1) c)
      (pinnedX TwistTag.E6.tag K e6HighestRoot d) :=
    commute_twistedE6PairX_e6HighestRoot_of_deg_zero
      (γ := -Pi.single j 1)
      (CFSG.LieType.Chevalley.IsRoot.neg (isRoot_single _ j)) hneg0 σ c d
  exact hcomm.eq.symm

private theorem twistedE6NegativeGroup_centralizes_Z [CharP K 2] {σ : K →+* K} :
    ∀ u ∈ twistedE6NegativeGroup σ, ∀ z ∈ twistedE6Z σ,
      u * z * u⁻¹ ∈ twistedE6Z σ := by
  intro u hu z hz
  have hcomm : (z : ModGL TwistTag.E6.tag K) * (u : ModGL TwistTag.E6.tag K) =
      (u : ModGL TwistTag.E6.tag K) * (z : ModGL TwistTag.E6.tag K) :=
    Subgroup.mem_centralizer_iff.1
      (Subgroup.mem_subgroupOf.1 (twistedE6NegativeGroup_le_centralizer_Z hu))
      _ (Subgroup.mem_subgroupOf.1 hz)
  have hEq : u * z * u⁻¹ = z := Subtype.ext (by
    show (u : ModGL TwistTag.E6.tag K) * (z : ModGL TwistTag.E6.tag K) *
        (u : ModGL TwistTag.E6.tag K)⁻¹ = (z : ModGL TwistTag.E6.tag K)
    rw [← hcomm]
    group)
  rw [hEq]
  exact hz

private theorem heisCoord_eq_of_mul_inv_mem_Z [CharP K 2] {σ : K →+* K}
    {q q' : graphFixedRootGroup TwistTag.E6 K σ}
    (hq : (q : ModGL TwistTag.E6.tag K) ∈
      CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Heis.Qθ TwistTag.E6.tag K)
    (hz : q' * q⁻¹ ∈ twistedE6Z σ) :
    CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Heis.heisCoord
        TwistTag.E6.tag K (q' : ModGL TwistTag.E6.tag K) =
      CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Heis.heisCoord
        TwistTag.E6.tag K (q : ModGL TwistTag.E6.tag K) := by
  have hzθ : (q' : ModGL TwistTag.E6.tag K) * (q : ModGL TwistTag.E6.tag K)⁻¹ ∈
      CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Heis.Uθ TwistTag.E6.tag K := by
    change ((q' * q⁻¹ : graphFixedRootGroup TwistTag.E6 K σ) :
      ModGL TwistTag.E6.tag K) ∈ rootSubgroup TwistTag.E6.tag K e6HighestRoot
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using
      (Subgroup.mem_subgroupOf.1 hz)
  exact heisCoord_eq_of_mul_inv_mem_highRoot hq hzθ

private theorem twistedE6_mem_V_of_fixed_pos [CharP K 2] {f : ℕ} (hf : 1 ≤ f)
    (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K →+* K} (hσ : ∀ c, σ c = c ^ 2 ^ f)
    (hσσ : ∀ c, σ (σ c) = c) {a : ℕ}
    {N A : Subgroup (graphFixedRootGroup TwistTag.E6 K σ)}
    (h : IsKLConfig (stdRepC (apply_apply_eq hK hσ) 0) a N A)
    (hLN : (su6Levi σ).subgroupOf (graphFixedRootGroup TwistTag.E6 K σ) ≤ N)
    (hAQ : A ≤ (tRadical σ).subgroupOf (graphFixedRootGroup TwistTag.E6 K σ))
    {x : graphFixedRootGroup TwistTag.E6 K σ} (hx : x ∈ A)
    (hfix : ∀ u ∈ twistedE6PositiveGroup σ, u * x * u⁻¹ * x⁻¹ ∈ twistedE6Z σ) :
    x ∈ twistedE6V σ := by
  have hxRad : (x : ModGL TwistTag.E6.tag K) ∈ tRadical σ :=
    Subgroup.mem_subgroupOf.1 (hAQ hx)
  have hxQ : (x : ModGL TwistTag.E6.tag K) ∈
      CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Heis.Qθ TwistTag.E6.tag K :=
    tRadical_le_Qθ hxRad
  refine ⟨hxQ, ?_⟩
  intro μ hμne
  by_cases hμD : μ ∈ CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Heis.Deg1
      TwistTag.E6.tag
  · refine heisCoord_eq_zero_of_fixed_pos_twistedE6PairX (K := K) hf hK hσ hxQ ?_ hμD hμne
    intro j hj c
    let u : graphFixedRootGroup TwistTag.E6 K σ :=
      ⟨twistedE6PairX σ (Pi.single j 1) c,
        twistedE6PairX_mem_graphFixedRootGroup hσσ (isRoot_single _ j) c⟩
    have hu : u ∈ twistedE6PositiveGroup σ :=
      Subgroup.mem_subgroupOf.2 (Subgroup.subset_closure ⟨j, hj, c, rfl⟩)
    have hx'Rad : ((u * x * u⁻¹ : graphFixedRootGroup TwistTag.E6 K σ) :
        ModGL TwistTag.E6.tag K) ∈ tRadical σ :=
      Subgroup.mem_subgroupOf.1
        (hAQ (h.conj_mem u (twistedE6PositiveGroup_le_N hσσ hLN hu) x hx))
    simpa [u] using heisCoord_eq_of_mul_inv_mem_Z hxQ (hfix u hu)
  · exact (CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Heis.heisCoord_spec
      TwistTag.E6.tag K).support x hxQ μ hμD

private theorem twistedE6_mem_V'_of_fixed_neg [CharP K 2] {f : ℕ} (hf : 1 ≤ f)
    (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K →+* K} (hσ : ∀ c, σ c = c ^ 2 ^ f)
    (hσσ : ∀ c, σ (σ c) = c) {a : ℕ}
    {N A : Subgroup (graphFixedRootGroup TwistTag.E6 K σ)}
    (h : IsKLConfig (stdRepC (apply_apply_eq hK hσ) 0) a N A)
    (hLN : (su6Levi σ).subgroupOf (graphFixedRootGroup TwistTag.E6 K σ) ≤ N)
    (hAQ : A ≤ (tRadical σ).subgroupOf (graphFixedRootGroup TwistTag.E6 K σ))
    {x : graphFixedRootGroup TwistTag.E6 K σ} (hx : x ∈ A)
    (hfix : ∀ u ∈ twistedE6NegativeGroup σ, u * x * u⁻¹ * x⁻¹ ∈ twistedE6Z σ) :
    x ∈ twistedE6V' σ := by
  have hxRad : (x : ModGL TwistTag.E6.tag K) ∈ tRadical σ :=
    Subgroup.mem_subgroupOf.1 (hAQ hx)
  have hxQ : (x : ModGL TwistTag.E6.tag K) ∈
      CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Heis.Qθ TwistTag.E6.tag K :=
    tRadical_le_Qθ hxRad
  refine ⟨hxQ, ?_⟩
  intro μ hμne
  by_cases hμD : μ ∈ CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Heis.Deg1
      TwistTag.E6.tag
  · refine heisCoord_eq_zero_of_fixed_neg_twistedE6PairX (K := K) hf hK hσ hxQ ?_ hμD hμne
    intro j hj c
    let u : graphFixedRootGroup TwistTag.E6 K σ :=
      ⟨twistedE6PairX σ (-Pi.single j 1) c,
        twistedE6PairX_mem_graphFixedRootGroup hσσ
          (CFSG.LieType.Chevalley.IsRoot.neg (isRoot_single _ j)) c⟩
    have hu : u ∈ twistedE6NegativeGroup σ :=
      Subgroup.mem_subgroupOf.2 (Subgroup.subset_closure ⟨j, hj, c, rfl⟩)
    have hx'Rad : ((u * x * u⁻¹ : graphFixedRootGroup TwistTag.E6 K σ) :
        ModGL TwistTag.E6.tag K) ∈ tRadical σ :=
      Subgroup.mem_subgroupOf.1
        (hAQ (h.conj_mem u (twistedE6NegativeGroup_le_N hσσ hLN hu) x hx))
    simpa [u] using heisCoord_eq_of_mul_inv_mem_Z hxQ (hfix u hu)
  · exact (CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Heis.heisCoord_spec
      TwistTag.E6.tag K).support x hxQ μ hμD

private theorem twistedE6_mul_ne_mul_of_mem_V [CharP K 2] {σ : K →+* K}
    {v v' : graphFixedRootGroup TwistTag.E6 K σ}
    (hv : v ∈ twistedE6V σ) (hv' : v' ∈ twistedE6V' σ)
    (hvZ : v ∉ twistedE6Z σ) (hv'Z : v' ∉ twistedE6Z σ) :
    v * v' ≠ v' * v := by
  have hv0 : (v : ModGL TwistTag.E6.tag K) ∈
      CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Heis.Qθ TwistTag.E6.tag K ∧
      ∀ ν, ν ≠ e6HighestRoot - Pi.single
        (CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Heis.iθ TwistTag.E6.tag) 1 →
        CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Heis.heisCoord
          TwistTag.E6.tag K (v : ModGL TwistTag.E6.tag K) ν = 0 := hv
  have hv'0 : (v' : ModGL TwistTag.E6.tag K) ∈
      CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Heis.Qθ TwistTag.E6.tag K ∧
      ∀ ν, ν ≠ Pi.single
        (CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Heis.iθ TwistTag.E6.tag) 1 →
        CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Heis.heisCoord
          TwistTag.E6.tag K (v' : ModGL TwistTag.E6.tag K) ν = 0 := hv'
  have hvU : (v : ModGL TwistTag.E6.tag K) ∉
      CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Heis.Uθ TwistTag.E6.tag K := by
    intro h
    change (v : ModGL TwistTag.E6.tag K) ∈ rootSubgroup TwistTag.E6.tag K e6HighestRoot at h
    exact hvZ (Subgroup.mem_subgroupOf.2 h)
  have hv'U : (v' : ModGL TwistTag.E6.tag K) ∉
      CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Heis.Uθ TwistTag.E6.tag K := by
    intro h
    change (v' : ModGL TwistTag.E6.tag K) ∈ rootSubgroup TwistTag.E6.tag K e6HighestRoot at h
    exact hv'Z (Subgroup.mem_subgroupOf.2 h)
  intro hcommC
  have hcomm : (v : ModGL TwistTag.E6.tag K) * (v' : ModGL TwistTag.E6.tag K) =
      (v' : ModGL TwistTag.E6.tag K) * (v : ModGL TwistTag.E6.tag K) :=
    congrArg Subtype.val hcommC
  refine EPilot.mul_ne_mul_of_heisCoord_support (τ := TwistTag.E6.tag) (Or.inl rfl)
    hv0.1 hv'0.1 ?_ ?_ hvU hv'U hcomm
  · intro μ hμ
    change μ ≠ e6HighestRoot - Pi.single
      (CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Heis.iθ TwistTag.E6.tag) 1 at hμ
    simpa using hv0.2 μ hμ
  · intro μ hμ
    simpa using hv'0.2 μ hμ

private theorem twistedE6_le_Z_of_isKLConfig [Finite K] [CharP K 2] {f : ℕ}
    (hf : 1 ≤ f) (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K →+* K}
    (hσ : ∀ c, σ c = c ^ 2 ^ f) {a : ℕ}
    {N A : Subgroup (graphFixedRootGroup TwistTag.E6 K σ)}
    (h : IsKLConfig (stdRepC (apply_apply_eq hK hσ) 0) a N A)
    (hLN : (su6Levi σ).subgroupOf (graphFixedRootGroup TwistTag.E6 K σ) ≤ N)
    (hAQ : A ≤ (tRadical σ).subgroupOf (graphFixedRootGroup TwistTag.E6 K σ)) :
    A ≤ twistedE6Z σ := by
  have hσσ : ∀ c, σ (σ c) = c := apply_apply_eq hK hσ
  let hfinModGL : Finite (ModGL TwistTag.E6.tag K) := finite_modGL (τ := TwistTag.E6.tag)
  let hfinC : Finite (graphFixedRootGroup TwistTag.E6 K σ) := Subtype.finite
  exact le_of_fixed_of_ne_commute
    (A := A) (Z₀ := twistedE6Z σ)
    (U := twistedE6PositiveGroup σ) (U' := twistedE6NegativeGroup σ)
    (V := twistedE6V σ) (V' := twistedE6V' σ)
    h.comm h.isPGroup
    (twistedE6A_conj_mem_Z hAQ)
    (twistedE6PositiveGroup_isPGroup (σ := σ))
    (fun u hu x hx => h.conj_mem u (twistedE6PositiveGroup_le_N hσσ hLN hu) x hx)
    (twistedE6PositiveGroup_centralizes_Z (σ := σ))
    (twistedE6NegativeGroup_isPGroup (σ := σ))
    (fun u hu x hx => h.conj_mem u (twistedE6NegativeGroup_le_N hσσ hLN hu) x hx)
    (twistedE6NegativeGroup_centralizes_Z (σ := σ))
    (fun x hx hfix => twistedE6_mem_V_of_fixed_pos hf hK hσ hσσ h hLN hAQ hx hfix)
    (fun x hx hfix => twistedE6_mem_V'_of_fixed_neg hf hK hσ hσσ h hLN hAQ hx hfix)
    (fun v hv v' hv' hvZ hv'Z => twistedE6_mul_ne_mul_of_mem_V hv hv' hvZ hv'Z)

theorem le_rootSubgroup_of_isKLConfig_twistedE6 [CharP K 2] (hf : 1 ≤ f)
    (hk : Nat.card k = 2 ^ f) (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K →+* K}
    (hσ : ∀ c, σ c = c ^ 2 ^ f) {a : ℕ} {N A : Subgroup (graphFixedRootGroup TwistTag.E6 K σ)}
    (h : IsKLConfig (stdRepC (apply_apply_eq hK hσ) 0) a N A)
    (hLN : (su6Levi σ).subgroupOf (graphFixedRootGroup TwistTag.E6 K σ) ≤ N)
    (hAQ : A ≤ (tRadical σ).subgroupOf (graphFixedRootGroup TwistTag.E6 K σ)) :
    ∀ x ∈ A, (x : ModGL TwistTag.E6.tag K) ∈ rootSubgroup TwistTag.E6.tag K e6HighestRoot := by
  have hk' : Nat.card k = 2 ^ f := hk
  have halg : Algebra k K := inferInstance
  let hfinK : Finite K := finite_of_card hK
  have hA := twistedE6_le_Z_of_isKLConfig (K := K) hf hK hσ h hLN hAQ
  intro x hx
  exact Subgroup.mem_subgroupOf.1 (hA hx)

end CFSG.SeitzReduction.TwistedE6Pilot
