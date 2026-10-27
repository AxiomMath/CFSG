module

public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Detect.F4.CaseData
public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Detect.F4.MPart

public noncomputable section

namespace CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.DetectF4

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.SeitzReduction
open Heis

set_option linter.unusedSectionVars false

private def c3STheta (v : Fin Tag.F4.rank → ℤ) : Fin Tag.F4.rank → ℤ :=
  reflect .F4 0 (sGamma (reflect .F4 0 v))

private theorem c3_sGamma_root : ∀ γ ∈ rootFinset .F4, sGamma γ ∈ rootFinset .F4 := by
  decide +kernel

private theorem c3_sTheta_involutive : ∀ γ ∈ rootFinset .F4,
    c3STheta γ ∈ rootFinset .F4 ∧ c3STheta (c3STheta γ) = γ := by
  decide +kernel

private theorem c3_sTheta_deg_neg_one : ∀ β ∈ rootFinset .F4, β 0 = -1 →
    c3STheta β = theta + β ∧ (theta + β) 0 = 1 := by
  decide +kernel

private theorem c3_sTheta_R1 :
    c3STheta alpha1 = -root1342 ∧ c3STheta root1342 = -alpha1 ∧ c3STheta theta = -theta := by
  decide +kernel

private theorem c3_reflect_root1342 : reflect .F4 0 root1342 = theta := by decide +kernel

private theorem c3_reflect_neg_root1342 : reflect .F4 0 (-root1342) = -theta := by decide +kernel

private theorem c3_neg_theta_mem : -theta ∈ rootFinset .F4 := by decide +kernel

private theorem c3_neg_theta_comm_data : ∀ β ∈ rootFinset .F4, β 0 = 0 →
    -theta ≠ β ∧ -theta ≠ -β ∧
      ∀ p ∈ commCandidates, p.1 • (-theta) + p.2 • β ∉ rootFinset .F4 := by
  decide +kernel

private abbrev c3Phi0 : Set (Fin Tag.F4.rank → ℤ) := {γ | IsRoot Tag.F4 γ ∧ γ 0 = 0}

private theorem c3_conjSub_inv_conjSub {G : Type*} [Group G] (g : G) (A : Subgroup G) :
    conjSub g⁻¹ (conjSub g A) = A := by
  rw [← conjSub_mul, inv_mul_cancel, conjSub_one]

private theorem c3_conjSub_eq_of_mem_normalizer {G : Type*} [Group G] {A : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (A : Set G)) : conjSub g A = A := by
  ext x
  rw [mem_conjSub_iff]
  have h := (Subgroup.mem_normalizer_iff.1 (inv_mem hg) x).symm
  simpa using h


section Helpers

variable (K : Type) [Field K]

private def c3NTheta : ModGL Tag.F4 K := nA K * nB K * (nA K)⁻¹

private theorem c3_nB_split :
    ∃ a ∈ rootSubgroup Tag.F4 K root1342, ∃ b ∈ rootSubgroup Tag.F4 K (-root1342),
      ∃ a' ∈ rootSubgroup Tag.F4 K root1342, nB K = a * b * a' := by
  have hx : ∀ c, nOmega K * xUnit Tag.F4 K 1 c * (nOmega K)⁻¹ ∈
      rootSubgroup Tag.F4 K root1342 := by
    intro c
    obtain ⟨ε, -, h⟩ := exists_prod_weylElt_mul_pinnedX_mul_inv K f4Word
      (IsRoot.basis (τ := Tag.F4) 1)
    rw [← pinnedX_single]
    have h' := h c
    rw [wordProd_smul_eq_foldr, f4Word_single_one] at h'
    unfold nOmega
    rw [h']
    exact mem_rootSubgroup.2 ⟨_, rfl⟩
  have hy : ∀ c, nOmega K * yUnit Tag.F4 K 1 c * (nOmega K)⁻¹ ∈
      rootSubgroup Tag.F4 K (-root1342) := by
    intro c
    obtain ⟨ε, -, h⟩ := exists_prod_weylElt_mul_pinnedX_mul_inv K f4Word
      (isRoot_neg_single Tag.F4 1)
    rw [← pinnedX_neg_single]
    have h' := h c
    rw [wordProd_smul_eq_foldr, show f4Word.foldr (reflect .F4) (-Pi.single 1 1) =
      -root1342 by rw [← f4Word_single_one, ← wordProd_smul_eq_foldr, ← wordProd_smul_eq_foldr,
        smul_neg]] at h'
    unfold nOmega
    rw [h']
    exact mem_rootSubgroup.2 ⟨_, rfl⟩
  refine ⟨_, hx 1, _, hy (-1), _, hx 1, ?_⟩
  rw [nB, weylElt_one_eq]
  group

private theorem c3_nTheta_mem : c3NTheta K ∈ rootSpan Tag.F4 K {theta, -theta} := by
  obtain ⟨a, ha, b, hb, a', ha', hnB⟩ := c3_nB_split K
  have key : ∀ (x : ModGL Tag.F4 K) (δ : Fin Tag.F4.rank → ℤ), IsRoot Tag.F4 δ →
      x ∈ rootSubgroup Tag.F4 K δ →
      nA K * x * (nA K)⁻¹ ∈ rootSubgroup Tag.F4 K (reflect Tag.F4 0 δ) := by
    intro x δ hδ hx
    rw [← conjSub_nA K hδ, mem_conjSub_iff]
    have e : (nA K)⁻¹ * (nA K * x * (nA K)⁻¹) * nA K = x := by group
    rw [e]
    exact hx
  have e : c3NTheta K =
      (nA K * a * (nA K)⁻¹) * (nA K * b * (nA K)⁻¹) * (nA K * a' * (nA K)⁻¹) := by
    rw [c3NTheta, hnB]
    group
  have h1 := key a root1342 isRoot_root1342 ha
  have h2 := key b (-root1342) isRoot_neg_root1342 hb
  have h3 := key a' root1342 isRoot_root1342 ha'
  rw [c3_reflect_root1342] at h1 h3
  rw [c3_reflect_neg_root1342] at h2
  rw [e]
  exact mul_mem (mul_mem (rootSubgroup_le_rootSpan_aux (by simp) K h1)
    (rootSubgroup_le_rootSpan_aux (by simp) K h2))
    (rootSubgroup_le_rootSpan_aux (by simp) K h3)

private theorem c3_conj_nTheta {γ : Fin Tag.F4.rank → ℤ} (hγ : IsRoot Tag.F4 γ) :
    conjSub (c3NTheta K) (rootSubgroup Tag.F4 K γ) = rootSubgroup Tag.F4 K (c3STheta γ) := by
  have h1 : IsRoot Tag.F4 (reflect Tag.F4 0 γ) := IsRoot.reflect 0 hγ
  have h2 : IsRoot Tag.F4 (sGamma (reflect Tag.F4 0 γ)) :=
    mem_rootFinset.1 (c3_sGamma_root _ (mem_rootFinset.2 h1))
  have e1 : conjSub (nA K)⁻¹ (rootSubgroup Tag.F4 K γ) =
      rootSubgroup Tag.F4 K (reflect Tag.F4 0 γ) := by
    have h := conjSub_nA K h1
    rw [reflect_reflect] at h
    rw [← h, c3_conjSub_inv_conjSub]
  rw [c3NTheta, conjSub_mul, conjSub_mul, e1, conjSub_nB K h1, conjSub_nA K h2]
  rfl

private theorem c3_conj_nTheta_inv {γ : Fin Tag.F4.rank → ℤ} (hγ : IsRoot Tag.F4 γ) :
    conjSub (c3NTheta K)⁻¹ (rootSubgroup Tag.F4 K γ) = rootSubgroup Tag.F4 K (c3STheta γ) := by
  obtain ⟨h1, h2⟩ := c3_sTheta_involutive γ (mem_rootFinset.2 hγ)
  have h := c3_conj_nTheta K (mem_rootFinset.1 h1)
  rw [h2] at h
  rw [← h, c3_conjSub_inv_conjSub]

private theorem c3_commute_theta {γ : Fin Tag.F4.rank → ℤ} (hγ : IsRoot Tag.F4 γ) (hd : γ 0 = 0)
    (s t : K) : Commute (pinnedX Tag.F4 K theta s) (pinnedX Tag.F4 K γ t) := by
  obtain ⟨hne, hne'⟩ := theta_ne_of_deg γ (mem_rootFinset.2 hγ) (Or.inl hd)
  refine Heis.commute_pinnedX_of_commPairs_nil Tag.F4 K isRoot_theta hγ hne hne' ?_ s t
  refine List.eq_nil_iff_forall_not_mem.2 fun p hp => ?_
  rw [mem_commPairs] at hp
  exact commCandidates_theta_data γ (mem_rootFinset.2 hγ) (Or.inl hd) p hp.1
    (mem_rootFinset.2 hp.2)

private theorem c3_commute_neg_theta {γ : Fin Tag.F4.rank → ℤ} (hγ : IsRoot Tag.F4 γ)
    (hd : γ 0 = 0) (s t : K) :
    Commute (pinnedX Tag.F4 K (-theta) s) (pinnedX Tag.F4 K γ t) := by
  obtain ⟨hne, hne', hc⟩ := c3_neg_theta_comm_data γ (mem_rootFinset.2 hγ) hd
  refine Heis.commute_pinnedX_of_commPairs_nil Tag.F4 K (mem_rootFinset.1 c3_neg_theta_mem) hγ
    hne hne' ?_ s t
  refine List.eq_nil_iff_forall_not_mem.2 fun p hp => ?_
  rw [mem_commPairs] at hp
  exact hc p hp.1 (mem_rootFinset.2 hp.2)

private theorem c3_nTheta_comm {m : ModGL Tag.F4 K} (hm : m ∈ rootSpan Tag.F4 K c3Phi0) :
    c3NTheta K * m = m * c3NTheta K := by
  refine rootSpan_commute_of_gen' (S₁ := {theta, -theta}) (S₂ := c3Phi0) ?_ _ (c3_nTheta_mem K)
    m hm
  intro α hα β hβ c d
  rcases hα with rfl | hα
  · exact (c3_commute_theta K hβ.1 hβ.2 c d).eq
  · rw [Set.mem_singleton_iff] at hα
    subst hα
    exact (c3_commute_neg_theta K hβ.1 hβ.2 c d).eq

private theorem c3_single_mem_Phi0 {j : Fin Tag.F4.rank} (hj : j ∈ Jθ Tag.F4) :
    (Pi.single j 1 : Fin Tag.F4.rank → ℤ) ∈ c3Phi0 := by
  refine ⟨isRoot_single Tag.F4 j, ?_⟩
  have h : j ≠ 0 := hj
  exact Pi.single_eq_of_ne (Ne.symm h) 1

private theorem c3_neg_single_mem_Phi0 {j : Fin Tag.F4.rank} (hj : j ∈ Jθ Tag.F4) :
    (-Pi.single j 1 : Fin Tag.F4.rank → ℤ) ∈ c3Phi0 := by
  refine ⟨isRoot_neg_single Tag.F4 j, ?_⟩
  have h : j ≠ 0 := hj
  simp [Pi.single_eq_of_ne (Ne.symm h)]

private theorem c3_Lθ_split {l : ModGL Tag.F4 K} (hl : l ∈ Lθ Tag.F4 K) :
    ∃ m ∈ rootSpan Tag.F4 K c3Phi0, ∃ t ∈ torusGroup Tag.F4 K, l = m * t := by
  have hN : torusGroup Tag.F4 K ≤
      Subgroup.normalizer (rootSpan Tag.F4 K c3Phi0 : Set (ModGL Tag.F4 K)) :=
    torusGroup_le_normalizer_rootSpan fun _ hα => hα.1
  have hle : Lθ Tag.F4 K ≤ rootSpan Tag.F4 K c3Phi0 ⊔ torusGroup Tag.F4 K := by
    refine sup_le le_sup_right ((Subgroup.closure_le _).2 ?_)
    rintro _ ⟨j, hj, c, rfl | rfl⟩
    · refine Subgroup.mem_sup_left ?_
      rw [← pinnedX_single]
      exact pinnedX_mem_rootSpan (c3_single_mem_Phi0 hj) c
    · refine Subgroup.mem_sup_left ?_
      rw [← pinnedX_neg_single]
      exact pinnedX_mem_rootSpan (c3_neg_single_mem_Phi0 hj) c
  have h := hle hl
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left _ _ hN] at h
  obtain ⟨m, hm, t, ht, rfl⟩ := h
  exact ⟨m, hm, t, ht, rfl⟩

private theorem c3_factor {q : ModGL Tag.F4 K} (hq : q ∈ Qθ Tag.F4 K)
    (h : ∀ β ∈ mRoots, heisCoord Tag.F4 K q β = 0) :
    ∃ u ∈ Uθ Tag.F4 K, ∃ c₁ c₂ : K,
      q = u * (pinnedX Tag.F4 K alpha1 c₁ * pinnedX Tag.F4 K root1342 c₂) := by
  classical
  have hs := heisCoord_spec Tag.F4 K
  set c₁ := heisCoord Tag.F4 K q alpha1 with hc₁
  set c₂ := heisCoord Tag.F4 K q root1342 with hc₂
  have hp1 := pinnedX_mem_Qθ K alpha1_deg1 c₁
  have hp2 := pinnedX_mem_Qθ K root1342_deg1 c₂
  have hsQ : pinnedX Tag.F4 K alpha1 c₁ * pinnedX Tag.F4 K root1342 c₂ ∈ Qθ Tag.F4 K :=
    mul_mem hp1 hp2
  have hcs : heisCoord Tag.F4 K (pinnedX Tag.F4 K alpha1 c₁ * pinnedX Tag.F4 K root1342 c₂) =
      Pi.single alpha1 c₁ + Pi.single root1342 c₂ := by
    rw [hs.mul _ hp1 _ hp2, hs.pinnedX_deg1 alpha1 alpha1_deg1 c₁,
      hs.pinnedX_deg1 root1342 root1342_deg1 c₂]
  have hzero : heisCoord Tag.F4 K
      (q * (pinnedX Tag.F4 K alpha1 c₁ * pinnedX Tag.F4 K root1342 c₂)⁻¹) = 0 := by
    rw [hs.mul q hq _ (inv_mem hsQ), heisCoord_inv hsQ, hcs]
    funext ν
    simp only [Pi.add_apply, Pi.neg_apply, Pi.zero_apply]
    by_cases h1 : ν = alpha1
    · subst h1
      rw [Pi.single_eq_same, Pi.single_eq_of_ne alpha1_ne_root1342]
      simp [hc₁]
    · by_cases h2 : ν = root1342
      · subst h2
        rw [Pi.single_eq_of_ne (Ne.symm alpha1_ne_root1342), Pi.single_eq_same]
        simp [hc₂]
      · rw [Pi.single_eq_of_ne h1, Pi.single_eq_of_ne h2]
        by_cases hD : ν ∈ Deg1 Tag.F4
        · rcases Deg1_cases hD with h3 | h3 | h3
          · exact absurd h3 h1
          · exact absurd h3 h2
          · simp [h ν h3]
        · simp [hs.support q hq ν hD]
  have hU := (hs.eq_zero_iff _ (mul_mem hq (inv_mem hsQ))).1 hzero
  exact ⟨_, hU, c₁, c₂, by group⟩

end Helpers

theorem case3_dichotomy (K : Type) [Field K] {l : ModGL Tag.F4 K} (hl : l ∈ Lθ Tag.F4 K)
    {β : Fin Tag.F4.rank → ℤ} (hβ : IsRoot Tag.F4 β) (hlong : IsLongRoot Tag.F4 β)
    (hdeg : β 0 = -1) :
    (∃ c ∈ conjSub l (rootSubgroup Tag.F4 K (theta + β)), MElement K c) ∨
      conjSub l (rootSubgroup Tag.F4 K β) ≤ R1neg K := by
  classical
  have _ := hlong
  by_cases hM : ∃ c ∈ conjSub l (rootSubgroup Tag.F4 K (theta + β)), MElement K c
  · exact Or.inl hM
  refine Or.inr ?_
  have hM' : ∀ c ∈ conjSub l (rootSubgroup Tag.F4 K (theta + β)), ∀ ν ∈ mRoots,
      heisCoord Tag.F4 K c ν = 0 := by
    intro c hc ν hν
    by_contra h0
    exact hM ⟨c, hc, ν, hν, h0⟩
  obtain ⟨hsβ, hdeg1⟩ := c3_sTheta_deg_neg_one β (mem_rootFinset.2 hβ) hdeg
  have hδroot : IsRoot Tag.F4 (theta + β) := by
    have := c3_sTheta_involutive β (mem_rootFinset.2 hβ)
    rw [hsβ] at this
    exact mem_rootFinset.1 this.1
  have hδ : theta + β ∈ Deg1 Tag.F4 := deg1_iff.2 ⟨hδroot, hdeg1⟩
  obtain ⟨m, hm, t, ht, rfl⟩ := c3_Lθ_split K hl
  have hlP : m * t ∈ Pθ Tag.F4 K := parabolicLevi_le_parabolicSubgroup (Jθ Tag.F4) hl
  obtain ⟨s, hsdef⟩ : ∃ s : ModGL Tag.F4 K, s = c3NTheta K := ⟨_, rfl⟩
  have hcomm : s * m = m * s := by
    rw [hsdef]
    exact c3_nTheta_comm K hm
  have hS : ∀ δ, IsRoot Tag.F4 δ → ∀ y ∈ rootSubgroup Tag.F4 K δ,
      s * y * s⁻¹ ∈ rootSubgroup Tag.F4 K (c3STheta δ) := by
    intro δ hδr y hy
    rw [← c3_conj_nTheta K hδr, ← hsdef, mem_conjSub_iff]
    rw [show s⁻¹ * (s * y * s⁻¹) * s = y by group]
    exact hy
  have hS' : ∀ δ, IsRoot Tag.F4 δ → ∀ y ∈ rootSubgroup Tag.F4 K δ,
      s⁻¹ * y * s ∈ rootSubgroup Tag.F4 K (c3STheta δ) := by
    intro δ hδr y hy
    rw [← c3_conj_nTheta_inv K hδr, ← hsdef, mem_conjSub_iff]
    rw [show (s⁻¹)⁻¹ * (s⁻¹ * y * s) * s⁻¹ = y by group]
    exact hy
  intro g hg
  have e1 : conjSub (m * t) (rootSubgroup Tag.F4 K β) = conjSub m (rootSubgroup Tag.F4 K β) := by
    rw [conjSub_mul, c3_conjSub_eq_of_mem_normalizer
      (CFSG.StandardType.RootCentExc.torusGroup_le_normalizer_rootSubgroup (K := K) hβ ht)]
  have e2 : conjSub (m * t) (rootSubgroup Tag.F4 K (theta + β)) =
      conjSub m (rootSubgroup Tag.F4 K (theta + β)) := by
    rw [conjSub_mul, c3_conjSub_eq_of_mem_normalizer
      (CFSG.StandardType.RootCentExc.torusGroup_le_normalizer_rootSubgroup (K := K) hδroot ht)]
  rw [e1, mem_conjSub_iff] at hg
  obtain ⟨u, hu⟩ := mem_rootSubgroup.1 hg
  have hg' : g = m * pinnedX Tag.F4 K β u * m⁻¹ := by
    rw [hu]
    group
  have hq : s * g * s⁻¹ = m * (s * pinnedX Tag.F4 K β u * s⁻¹) * m⁻¹ := by
    rw [hg']
    calc s * (m * pinnedX Tag.F4 K β u * m⁻¹) * s⁻¹
        = (s * m) * pinnedX Tag.F4 K β u * (s * m)⁻¹ := by group
      _ = (m * s) * pinnedX Tag.F4 K β u * (m * s)⁻¹ := by rw [hcomm]
      _ = m * (s * pinnedX Tag.F4 K β u * s⁻¹) * m⁻¹ := by group
  have hx : s * pinnedX Tag.F4 K β u * s⁻¹ ∈ rootSubgroup Tag.F4 K (theta + β) := by
    have h := hS β hβ _ (mem_rootSubgroup.2 ⟨u, rfl⟩)
    rw [hsβ] at h
    exact h
  have hqmem : s * g * s⁻¹ ∈ conjSub (m * t) (rootSubgroup Tag.F4 K (theta + β)) := by
    rw [e2, mem_conjSub_iff, hq]
    rw [show m⁻¹ * (m * (s * pinnedX Tag.F4 K β u * s⁻¹) * m⁻¹) * m =
      s * pinnedX Tag.F4 K β u * s⁻¹ by group]
    exact hx
  have hQ : s * g * s⁻¹ ∈ Qθ Tag.F4 K := by
    have hqm := mem_conjSub_iff.1 hqmem
    obtain ⟨c, hc⟩ := mem_rootSubgroup.1 hqm
    have hcQ := pinnedX_mem_Qθ K hδ c
    have hN := (Subgroup.mem_normalizer_iff.1
      (parabolicSubgroup_le_normalizer_parabolicRadical (Jθ Tag.F4) hlP) _).1 hcQ
    rw [hc] at hN
    rw [show (m * t) * ((m * t)⁻¹ * (s * g * s⁻¹) * (m * t)) * (m * t)⁻¹ = s * g * s⁻¹ by group]
      at hN
    exact hN
  obtain ⟨u₀, hu₀, c₁, c₂, hfac⟩ := c3_factor K hQ (fun ν hν => hM' _ hqmem ν hν)
  obtain ⟨hA, hB, hC⟩ := c3_sTheta_R1
  have f1 : s⁻¹ * u₀ * s ∈ R1neg K := by
    have := hS' theta isRoot_theta u₀ hu₀
    rw [hC] at this
    exact rootSubgroup_le_rootSpan_aux (by simp [R1negRoots]) K this
  have f2 : s⁻¹ * pinnedX Tag.F4 K alpha1 c₁ * s ∈ R1neg K := by
    have := hS' alpha1 isRoot_alpha1 _ (mem_rootSubgroup.2 ⟨c₁, rfl⟩)
    rw [hA] at this
    exact rootSubgroup_le_rootSpan_aux (by simp [R1negRoots]) K this
  have f3 : s⁻¹ * pinnedX Tag.F4 K root1342 c₂ * s ∈ R1neg K := by
    have := hS' root1342 isRoot_root1342 _ (mem_rootSubgroup.2 ⟨c₂, rfl⟩)
    rw [hB] at this
    exact rootSubgroup_le_rootSpan_aux (by simp [R1negRoots]) K this
  have hgq : g = s⁻¹ * (s * g * s⁻¹) * s := by group
  rw [hgq, hfac]
  rw [show s⁻¹ * (u₀ * (pinnedX Tag.F4 K alpha1 c₁ * pinnedX Tag.F4 K root1342 c₂)) * s =
    (s⁻¹ * u₀ * s) * (s⁻¹ * pinnedX Tag.F4 K alpha1 c₁ * s) *
      (s⁻¹ * pinnedX Tag.F4 K root1342 c₂ * s) by group]
  exact mul_mem (mul_mem f1 f2) f3

end CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.DetectF4
