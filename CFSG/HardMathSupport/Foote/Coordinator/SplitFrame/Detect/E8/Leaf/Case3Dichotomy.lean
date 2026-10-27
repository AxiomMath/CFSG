module

public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Detect.E8.CaseData
public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Detect.E8.Transport

public noncomputable section

namespace CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.DetectE8

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.SeitzReduction
open CFSG.LieType.Steinberg.Adjoint Heis

set_option linter.unusedSectionVars false

namespace Case3Aux

private theorem c3_sTheta_deg_neg_one : ∀ β ∈ rootFinset .E8, β 7 = -1 →
    sTheta β = theta + β ∧ (theta + β) 7 = 1 := by
  decide +kernel

private theorem c3_sTheta_Sq : ∀ γ ∈ theta :: sRootsList,
    sTheta (sTheta γ) = γ ∧ (sTheta γ) 4 % 5 = 0 ∧ (sTheta γ) 7 < 0 := by
  decide +kernel

private abbrev c3Phi0 : Set (Fin Tag.E8.rank → ℤ) := {γ | IsRoot Tag.E8 γ ∧ γ 7 = 0}

private abbrev c3Sq : Set (Fin Tag.E8.rank → ℤ) := {r | r = theta ∨ r ∈ sRootsList}

end Case3Aux


namespace Case3Aux

section Helpers

private theorem c3_neg_theta_comm_data {β : Fin Tag.E8.rank → ℤ} (hβ : IsRoot Tag.E8 β)
    (hd : β 7 = 0) :
    -theta ≠ β ∧ -theta ≠ -β ∧
      ∀ p ∈ commCandidates, p.1 • (-theta) + p.2 • β ∉ rootFinset .E8 := by
  have hβ' : -β ∈ rootFinset .E8 := mem_rootFinset.2 (isRoot_neg_iff.2 hβ)
  have hd' : (-β) 7 = 0 := by rw [Pi.neg_apply, hd, neg_zero]
  obtain ⟨h1, h2⟩ := theta_ne_of_deg (-β) hβ' (Or.inl hd')
  refine ⟨fun h => h1 (by rw [← h, neg_neg]), fun h => h2 (by rw [neg_neg]; exact neg_inj.1 h),
    ?_⟩
  intro p hp hmem
  refine commCandidates_theta_data (-β) hβ' (Or.inl hd') p hp ?_
  have e : p.1 • theta + p.2 • (-β) = -(p.1 • (-theta) + p.2 • β) := by
    simp only [smul_neg, neg_add_rev, neg_neg]
    abel
  rw [e]
  exact mem_rootFinset.2 (isRoot_neg_iff.2 (mem_rootFinset.1 hmem))

private theorem c3_isRoot_neg_theta : IsRoot Tag.E8 (-theta) :=
  isRoot_neg_iff.2 (mem_rootFinset.1 theta_mem)

variable (K : Type) [Field K]

private theorem c3_conjSub_rootSpan_le {g : ModGL Tag.E8 K} {S T : Set (Fin Tag.E8.rank → ℤ)}
    (h : ∀ γ ∈ S, conjSub g (rootSubgroup Tag.E8 K γ) ≤ rootSpan Tag.E8 K T) :
    conjSub g (rootSpan Tag.E8 K S) ≤ rootSpan Tag.E8 K T := by
  unfold conjSub
  rw [Subgroup.map_le_iff_le_comap]
  refine iSup₂_le fun γ hγ => ?_
  rw [← Subgroup.map_le_iff_le_comap]
  exact h γ hγ

private theorem c3_nTheta_mem : nTheta K ∈ rootSpan Tag.E8 K {theta, -theta} := by
  have hx : ∀ c, nOmega K * xUnit Tag.E8 K 7 c * (nOmega K)⁻¹ ∈
      rootSpan Tag.E8 K {theta, -theta} := by
    intro c
    obtain ⟨ε, -, h⟩ := exists_prod_weylElt_mul_pinnedX_mul_inv K omegaW
      (IsRoot.basis (τ := Tag.E8) 7)
    rw [← pinnedX_single]
    have h' := h c
    rw [wordProd_smul_foldr, omegaW_single] at h'
    unfold nOmega
    rw [h']
    exact pinnedX_mem_rootSpan (by simp) _
  have hy : ∀ c, nOmega K * yUnit Tag.E8 K 7 c * (nOmega K)⁻¹ ∈
      rootSpan Tag.E8 K {theta, -theta} := by
    intro c
    obtain ⟨ε, -, h⟩ := exists_prod_weylElt_mul_pinnedX_mul_inv K omegaW
      (isRoot_neg_single Tag.E8 7)
    rw [← pinnedX_neg_single]
    have h' := h c
    rw [wordProd_smul_foldr, show omegaW.foldr (reflect .E8) (-Pi.single 7 1) = -theta by
      rw [← omegaW_single, ← wordProd_smul_foldr, ← wordProd_smul_foldr, smul_neg]] at h'
    unfold nOmega
    rw [h']
    exact pinnedX_mem_rootSpan (by simp) _
  have e : nTheta K = (nOmega K * xUnit Tag.E8 K 7 1 * (nOmega K)⁻¹) *
      (nOmega K * yUnit Tag.E8 K 7 (-1) * (nOmega K)⁻¹) *
      (nOmega K * xUnit Tag.E8 K 7 1 * (nOmega K)⁻¹) := by
    rw [nTheta, weylElt_one_eq]
    group
  rw [e]
  exact mul_mem (mul_mem (hx _) (hy _)) (hx _)

private theorem c3_commute_theta {γ : Fin Tag.E8.rank → ℤ} (hγ : IsRoot Tag.E8 γ) (hd : γ 7 = 0)
    (s t : K) : Commute (pinnedX Tag.E8 K theta s) (pinnedX Tag.E8 K γ t) := by
  obtain ⟨hne, hne'⟩ := theta_ne_of_deg γ (mem_rootFinset.2 hγ) (Or.inl hd)
  refine Heis.commute_pinnedX_of_commPairs_nil Tag.E8 K (mem_rootFinset.1 theta_mem) hγ hne hne'
    ?_ s t
  refine List.eq_nil_iff_forall_not_mem.2 fun p hp => ?_
  rw [mem_commPairs] at hp
  exact commCandidates_theta_data γ (mem_rootFinset.2 hγ) (Or.inl hd) p hp.1
    (mem_rootFinset.2 hp.2)

private theorem c3_commute_neg_theta {γ : Fin Tag.E8.rank → ℤ} (hγ : IsRoot Tag.E8 γ)
    (hd : γ 7 = 0) (s t : K) :
    Commute (pinnedX Tag.E8 K (-theta) s) (pinnedX Tag.E8 K γ t) := by
  obtain ⟨hne, hne', hc⟩ := c3_neg_theta_comm_data hγ hd
  refine Heis.commute_pinnedX_of_commPairs_nil Tag.E8 K c3_isRoot_neg_theta hγ hne hne' ?_ s t
  refine List.eq_nil_iff_forall_not_mem.2 fun p hp => ?_
  rw [mem_commPairs] at hp
  exact hc p hp.1 (mem_rootFinset.2 hp.2)

private theorem c3_nTheta_comm {m : ModGL Tag.E8 K} (hm : m ∈ rootSpan Tag.E8 K c3Phi0) :
    nTheta K * m = m * nTheta K := by
  refine rootSpan_commute_of_gen' (S₁ := {theta, -theta}) (S₂ := c3Phi0) ?_ _ (c3_nTheta_mem K)
    m hm
  intro α hα β hβ c d
  rcases hα with rfl | hα
  · exact (c3_commute_theta K hβ.1 hβ.2 c d).eq
  · rw [Set.mem_singleton_iff] at hα
    subst hα
    exact (c3_commute_neg_theta K hβ.1 hβ.2 c d).eq

private theorem c3_single_mem_Phi0 {j : Fin Tag.E8.rank} (hj : j ∈ Jθ Tag.E8) :
    (Pi.single j 1 : Fin Tag.E8.rank → ℤ) ∈ c3Phi0 := by
  refine ⟨isRoot_single Tag.E8 j, ?_⟩
  have h : j ≠ 7 := hj
  exact Pi.single_eq_of_ne (Ne.symm h) 1

private theorem c3_neg_single_mem_Phi0 {j : Fin Tag.E8.rank} (hj : j ∈ Jθ Tag.E8) :
    (-Pi.single j 1 : Fin Tag.E8.rank → ℤ) ∈ c3Phi0 := by
  refine ⟨isRoot_neg_single Tag.E8 j, ?_⟩
  have h : j ≠ 7 := hj
  simp [Pi.single_eq_of_ne (Ne.symm h)]

private theorem c3_Lθ_split {l : ModGL Tag.E8 K} (hl : l ∈ Lθ Tag.E8 K) :
    ∃ m ∈ rootSpan Tag.E8 K c3Phi0, ∃ t ∈ torusGroup Tag.E8 K, l = m * t := by
  have hN : torusGroup Tag.E8 K ≤
      Subgroup.normalizer (rootSpan Tag.E8 K c3Phi0 : Set (ModGL Tag.E8 K)) :=
    torusGroup_le_normalizer_rootSpan fun _ hα => hα.1
  have hle : Lθ Tag.E8 K ≤ rootSpan Tag.E8 K c3Phi0 ⊔ torusGroup Tag.E8 K := by
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

private theorem c3_factor {q : ModGL Tag.E8 K} (hq : q ∈ Qθ Tag.E8 K)
    (h : ∀ β ∈ mRoots, heisCoord Tag.E8 K q β = 0) : q ∈ rootSpan Tag.E8 K c3Sq := by
  classical
  have hs := heisCoord_spec Tag.E8 K
  have hD : ∀ β ∈ sRootsList, β ∈ Deg1 Tag.E8 := fun β hβ => by
    obtain ⟨h1, h2, -⟩ := sRootsList_data β hβ
    exact ⟨mem_rootFinset.1 h1, h2⟩
  have hsupp : ∀ ν, ν ∉ sRootsList → heisCoord Tag.E8 K q ν = 0 := by
    intro ν hν
    by_cases hD1 : ν ∈ Deg1 Tag.E8
    · rcases Deg1_cases hD1 with hm | hsr
      · exact h ν hm
      · exact absurd (sRootsList_cover ν (Finset.mem_filter.1 hsr).1 hD1.2
          (Finset.mem_filter.1 hsr).2.2) hν
    · exact hs.support q hq ν hD1
  obtain ⟨u, hu, e⟩ := exists_prodX_of_support sRootsList_nodup hD hq hsupp
  rw [e]
  refine mul_mem (rootSubgroup_le_rootSpan_of_mem (S := c3Sq) (α := theta) (Or.inl rfl) hu) ?_
  exact CoordAux.prodX_mem_rootSpan (fun α hα => Or.inr hα) _

private theorem c3_conjSub_inv_nTheta_le :
    conjSub (nTheta K)⁻¹ (rootSpan Tag.E8 K c3Sq) ≤ R1neg K := by
  refine c3_conjSub_rootSpan_le K fun γ hγ => ?_
  have hγm : γ ∈ theta :: sRootsList := by
    rcases hγ with rfl | h
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ h
  have hγr : IsRoot Tag.E8 γ := by
    rcases List.mem_cons.1 hγm with rfl | h
    · exact mem_rootFinset.1 theta_mem
    · exact mem_rootFinset.1 (sRootsList_data γ h).1
  obtain ⟨hinv, h4, h7⟩ := c3_sTheta_Sq γ hγm
  have h := conjSub_nTheta K (isRoot_sTheta hγr)
  rw [hinv] at h
  have e : conjSub (nTheta K)⁻¹ (rootSubgroup Tag.E8 K γ) =
      rootSubgroup Tag.E8 K (sTheta γ) := by
    rw [← h]
    exact conjSub_inv_conjSub _ _
  rw [e]
  exact rootSubgroup_le_rootSpan_of_mem (S := R1negRoots) (α := sTheta γ)
    ⟨isRoot_sTheta hγr, h4, h7⟩

end Helpers

end Case3Aux

open Case3Aux

theorem case3_dichotomy (K : Type) [Field K] {l : ModGL Tag.E8 K} (hl : l ∈ Lθ Tag.E8 K)
    {β : Fin Tag.E8.rank → ℤ} (hβ : IsRoot Tag.E8 β) (hdeg : β 7 = -1) :
    (∃ c ∈ conjSub l (rootSubgroup Tag.E8 K (theta + β)), MElement K c) ∨
      conjSub l (rootSubgroup Tag.E8 K β) ≤ R1neg K := by
  classical
  by_cases hM : ∃ c ∈ conjSub l (rootSubgroup Tag.E8 K (theta + β)), MElement K c
  · exact Or.inl hM
  refine Or.inr ?_
  have hM' : ∀ c ∈ conjSub l (rootSubgroup Tag.E8 K (theta + β)), ∀ ν ∈ mRoots,
      heisCoord Tag.E8 K c ν = 0 := by
    intro c hc ν hν
    by_contra h0
    exact hM ⟨c, hc, ν, hν, h0⟩
  obtain ⟨hsβ, hdeg1⟩ := c3_sTheta_deg_neg_one β (mem_rootFinset.2 hβ) hdeg
  have hδroot : IsRoot Tag.E8 (theta + β) := hsβ ▸ isRoot_sTheta hβ
  have hδ : theta + β ∈ Deg1 Tag.E8 := mem_Deg1_E8.2 ⟨hδroot, hdeg1⟩
  obtain ⟨m, hm, t, ht, rfl⟩ := c3_Lθ_split K hl
  have hlP : m * t ∈ Pθ Tag.E8 K := parabolicLevi_le_parabolicSubgroup (Jθ Tag.E8) hl
  obtain ⟨s, hsdef⟩ : ∃ s : ModGL Tag.E8 K, s = nTheta K := ⟨_, rfl⟩
  have hcomm : s * m = m * s := by
    rw [hsdef]
    exact c3_nTheta_comm K hm
  have hS : ∀ δ, IsRoot Tag.E8 δ → ∀ y ∈ rootSubgroup Tag.E8 K δ,
      s * y * s⁻¹ ∈ rootSubgroup Tag.E8 K (sTheta δ) := by
    intro δ hδr y hy
    rw [← conjSub_nTheta K hδr, ← hsdef, mem_conjSub_iff]
    rw [show s⁻¹ * (s * y * s⁻¹) * s = y by group]
    exact hy
  intro g hg
  have e1 : conjSub (m * t) (rootSubgroup Tag.E8 K β) = conjSub m (rootSubgroup Tag.E8 K β) := by
    rw [conjSub_mul, conjSub_eq_of_mem_normalizer
      (CFSG.StandardType.RootCentExc.torusGroup_le_normalizer_rootSubgroup (K := K) hβ ht)]
  have e2 : conjSub (m * t) (rootSubgroup Tag.E8 K (theta + β)) =
      conjSub m (rootSubgroup Tag.E8 K (theta + β)) := by
    rw [conjSub_mul, conjSub_eq_of_mem_normalizer
      (CFSG.StandardType.RootCentExc.torusGroup_le_normalizer_rootSubgroup (K := K) hδroot ht)]
  rw [e1, mem_conjSub_iff] at hg
  obtain ⟨u, hu⟩ := mem_rootSubgroup.1 hg
  have hg' : g = m * pinnedX Tag.E8 K β u * m⁻¹ := by
    rw [hu]
    group
  have hq : s * g * s⁻¹ = m * (s * pinnedX Tag.E8 K β u * s⁻¹) * m⁻¹ := by
    rw [hg']
    calc s * (m * pinnedX Tag.E8 K β u * m⁻¹) * s⁻¹
        = (s * m) * pinnedX Tag.E8 K β u * (s * m)⁻¹ := by group
      _ = (m * s) * pinnedX Tag.E8 K β u * (m * s)⁻¹ := by rw [hcomm]
      _ = m * (s * pinnedX Tag.E8 K β u * s⁻¹) * m⁻¹ := by group
  have hx : s * pinnedX Tag.E8 K β u * s⁻¹ ∈ rootSubgroup Tag.E8 K (theta + β) := by
    have h := hS β hβ _ (mem_rootSubgroup.2 ⟨u, rfl⟩)
    rw [hsβ] at h
    exact h
  have hqmem : s * g * s⁻¹ ∈ conjSub (m * t) (rootSubgroup Tag.E8 K (theta + β)) := by
    rw [e2, mem_conjSub_iff, hq]
    rw [show m⁻¹ * (m * (s * pinnedX Tag.E8 K β u * s⁻¹) * m⁻¹) * m =
      s * pinnedX Tag.E8 K β u * s⁻¹ by group]
    exact hx
  have hQ : s * g * s⁻¹ ∈ Qθ Tag.E8 K := by
    have hqm := mem_conjSub_iff.1 hqmem
    obtain ⟨c, hc⟩ := mem_rootSubgroup.1 hqm
    have hcQ := pinnedX_mem_Qθ_of_mem_Deg1 (K := K) hδ c
    have hN := (Subgroup.mem_normalizer_iff.1
      (parabolicSubgroup_le_normalizer_parabolicRadical (Jθ Tag.E8) hlP) _).1 hcQ
    rw [hc] at hN
    rw [show (m * t) * ((m * t)⁻¹ * (s * g * s⁻¹) * (m * t)) * (m * t)⁻¹ = s * g * s⁻¹ by group]
      at hN
    exact hN
  have hq0 : s * g * s⁻¹ ∈ rootSpan Tag.E8 K c3Sq :=
    c3_factor K hQ (fun ν hν => hM' _ hqmem ν hν)
  have hmem : g ∈ conjSub s⁻¹ (rootSpan Tag.E8 K c3Sq) := by
    rw [mem_conjSub_iff, inv_inv]
    exact hq0
  rw [hsdef] at hmem
  exact c3_conjSub_inv_nTheta_le K hmem

end CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.DetectE8
