module

public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Detect.E8.LA
public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Detect.E8.MPart
public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Detect.E8.Leaf.Action
public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Detect.Heis.DegZero

public noncomputable section

namespace CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.DetectE8

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.SeitzReduction
open CFSG.LieType.Steinberg.Adjoint Heis

set_option linter.unusedSectionVars false


theorem LA_core {K : Type} [Field K]
    {a : (Fin Tag.E8.rank → ℤ) → (Fin Tag.E8.rank → ℤ) → ℤ} (h : Adm a)
    (W : Set ((Fin Tag.E8.rank → ℤ) → K))
    (hadd : ∀ c ∈ W, ∀ c' ∈ W, c + c' ∈ W) (hneg : ∀ c ∈ W, -c ∈ W)
    (hsupp : ∀ c ∈ W, ∀ ν, c ν ≠ 0 → ν ∈ mRoots)
    (hstab : ∀ γ ∈ lxRoots, ∀ t : K, ∀ c ∈ W, actFun a γ t c ∈ W)
    (hne : ∃ c ∈ W, c ≠ 0) :
    ∃ ν ∈ mRoots, ∃ e : K, e ≠ 0 ∧ Pi.single ν e ∈ W := by
  obtain ⟨c, hcW, hc0, hfix⟩ := exists_fixed_vector W hadd hneg hsupp hstab hne
  exact words_extract h W hadd hneg hstab hcW hc0
    (fixed_support_tops h (hsupp c hcW) hfix)

theorem actFun_supp {K : Type} [Field K]
    {a : (Fin Tag.E8.rank → ℤ) → (Fin Tag.E8.rank → ℤ) → ℤ} (h : Adm a)
    {γ : Fin Tag.E8.rank → ℤ} (hγ : γ ∈ lxRoots) (t : K)
    {c : (Fin Tag.E8.rank → ℤ) → K} (hc : ∀ ν, ν ∉ mRoots → c ν = 0)
    (ν : Fin Tag.E8.rank → ℤ) (hν : ν ∉ mRoots) : actFun a γ t c ν = 0 := by
  have hγd := lxRoots_data γ hγ
  have hterm : (a γ (ν - γ) : K) * c (ν - γ) = 0 := by
    by_cases hμ : ν - γ ∈ mRoots
    · by_cases hr : γ + (ν - γ) ∈ rootFinset .E8
      · exfalso
        have := add_mem_mRoots γ hγ _ hμ hr
        rw [add_sub_cancel] at this
        exact hν this
      · have := (h γ hγd.1 hγd.2.1 _ (deg1_of_mRoots hμ)).2 hr
        rw [this, Int.cast_zero, zero_mul]
    · rw [hc _ hμ, mul_zero]
  simp only [actFun]
  rw [hc ν hν, mul_assoc, hterm]
  ring

theorem mRoots_ne_sRoots1 {β : Fin Tag.E8.rank → ℤ} (h : β ∈ mRoots) : β ∉ sRoots1 := by
  intro hs
  have h1 := (Finset.mem_filter.1 h).2.2
  have h2 := (Finset.mem_filter.1 hs).2.2
  exact h1 h2

variable (K : Type) [Field K]

theorem lemma3 {H : Subgroup (ModGL Tag.E8 K)} (hX : XS K ≤ H) (hM : MPart K H) :
    ∃ β, IsRoot Tag.E8 β ∧ β ∉ cosetRoots Tag.E8 4 5 ∧ ∃ c : K, c ≠ 0 ∧
      pinnedX Tag.E8 K β c ∈ H := by
  classical
  obtain ⟨a, ha, hact⟩ := exists_action_data K
  have hs := heisCoord_spec Tag.E8 K
  let W : Set ((Fin Tag.E8.rank → ℤ) → K) := {c | ∃ q ∈ H, q ∈ Qθ Tag.E8 K ∧
    heisCoord Tag.E8 K q = c ∧ ∀ ν, ν ∉ mRoots → c ν = 0}
  have hadd : ∀ c ∈ W, ∀ c' ∈ W, c + c' ∈ W := by
    rintro _ ⟨q, hq, hqQ, rfl, hqs⟩ _ ⟨q', hq', hqQ', rfl, hqs'⟩
    refine ⟨q * q', mul_mem hq hq', mul_mem hqQ hqQ', hs.mul q hqQ q' hqQ', fun ν hν => ?_⟩
    simp only [Pi.add_apply, hqs ν hν, hqs' ν hν, add_zero]
  have hneg : ∀ c ∈ W, -c ∈ W := by
    rintro _ ⟨q, hq, hqQ, rfl, hqs⟩
    refine ⟨q⁻¹, inv_mem hq, inv_mem hqQ, heisCoord_inv hqQ, fun ν hν => ?_⟩
    simp only [Pi.neg_apply, hqs ν hν, neg_zero]
  have hsupp : ∀ c ∈ W, ∀ ν, c ν ≠ 0 → ν ∈ mRoots := by
    rintro _ ⟨q, hq, hqQ, rfl, hqs⟩ ν hν
    by_contra hnot
    exact hν (hqs ν hnot)
  have hstab : ∀ γ ∈ lxRoots, ∀ t : K, ∀ c ∈ W, actFun a γ t c ∈ W := by
    rintro γ hγ t _ ⟨q, hq, hqQ, rfl, hqs⟩
    have hγd := lxRoots_data γ hγ
    have hγr : IsRoot Tag.E8 γ := mem_rootFinset.1 hγd.1
    have hxL : pinnedX Tag.E8 K γ t ∈ Lθ Tag.E8 K := pinnedX_mem_Lθ_of_deg_zero hγr hγd.2.1 t
    have hxH : pinnedX Tag.E8 K γ t ∈ H :=
      hX (pinnedX_mem_rootSpan (S := cosetRoots Tag.E8 4 5)
        ⟨hγr, Int.dvd_of_emod_eq_zero hγd.2.2⟩ t)
    have hnorm := Pθ_le_normalizer_Qθ Tag.E8 K (Lθ_le_Pθ Tag.E8 K hxL)
    have hq' : pinnedX Tag.E8 K γ t * q * (pinnedX Tag.E8 K γ t)⁻¹ ∈ Qθ Tag.E8 K :=
      (Subgroup.mem_normalizer_iff.1 hnorm q).1 hqQ
    exact ⟨pinnedX Tag.E8 K γ t * q * (pinnedX Tag.E8 K γ t)⁻¹,
      mul_mem (mul_mem hxH hq) (inv_mem hxH), hq', hact γ hγd.1 hγd.2.1 t q hqQ,
      actFun_supp ha hγ t hqs⟩
  have hne : ∃ c ∈ W, c ≠ 0 := by
    obtain ⟨q, hqH, hqQ, β, hβM, hβ0⟩ := hM
    let f : (Fin Tag.E8.rank → ℤ) → K := fun ν =>
      if ν ∈ sRoots1 then heisCoord Tag.E8 K q ν else 0
    have hf : ∀ ν, ν ∉ Deg1 Tag.E8 → f ν = 0 := by
      intro ν hν
      simp only [f]
      rw [if_neg]
      intro hsr
      exact hν (mem_Deg1_E8.2 ⟨mem_rootFinset.1 (Finset.mem_filter.1 hsr).1,
        (Finset.mem_filter.1 hsr).2.1⟩)
    obtain ⟨s, hsQ, hsc⟩ := hs.surj f hf
    have hsX1 : s ∈ X1 K := by
      refine mem_X1_of_coord_M_zero K hsQ fun β' hβ' => ?_
      rw [hsc]
      simp only [f]
      rw [if_neg (mRoots_ne_sRoots1 hβ')]
    have hsH : s ∈ H := hX (X1_le_XS K hsX1)
    refine ⟨heisCoord Tag.E8 K (q * s⁻¹), ⟨q * s⁻¹, mul_mem hqH (inv_mem hsH),
      mul_mem hqQ (inv_mem hsQ), rfl, fun ν hν => ?_⟩, fun h0 => hβ0 ?_⟩
    · rw [hs.mul q hqQ _ (inv_mem hsQ), heisCoord_inv hsQ, hsc]
      simp only [Pi.add_apply, Pi.neg_apply, f]
      by_cases hν' : ν ∈ sRoots1
      · rw [if_pos hν']
        ring
      · rw [if_neg hν']
        by_cases hD : ν ∈ Deg1 Tag.E8
        · rcases Deg1_cases hD with h | h
          · exact absurd h hν
          · exact absurd h hν'
        · rw [hs.support q hqQ ν hD]
          ring
    · have := congrFun h0 β
      rw [hs.mul q hqQ _ (inv_mem hsQ), heisCoord_inv hsQ, hsc] at this
      simp only [Pi.add_apply, Pi.neg_apply, f, Pi.zero_apply] at this
      rw [if_neg (mRoots_ne_sRoots1 hβM)] at this
      simpa using this
  obtain ⟨ν, hν, e, he, hW⟩ := LA_core ha W hadd hneg hsupp hstab hne
  obtain ⟨q, hqH, hqQ, hqc, -⟩ := hW
  have hνr := mem_mRoots.1 hν
  have hνD : ν ∈ Deg1 Tag.E8 := mem_Deg1_E8.2 ⟨hνr.1, hνr.2.1⟩
  have hq1Q := pinnedX_mem_Qθ_of_mem_Deg1 (K := K) hνD e
  have hzero : heisCoord Tag.E8 K (q * (pinnedX Tag.E8 K ν e)⁻¹) = 0 := by
    rw [hs.mul q hqQ _ (inv_mem hq1Q), heisCoord_inv hq1Q, hs.pinnedX_deg1 ν hνD e, hqc]
    funext x
    simp
  have hU := (hs.eq_zero_iff _ (mul_mem hqQ (inv_mem hq1Q))).1 hzero
  have hUH : q * (pinnedX Tag.E8 K ν e)⁻¹ ∈ H := hX (X1_le_XS K (Uθ_le_X1 K hU))
  have hqe : pinnedX Tag.E8 K ν e = (q * (pinnedX Tag.E8 K ν e)⁻¹)⁻¹ * q := by group
  refine ⟨ν, hνr.1, ?_, e, he, ?_⟩
  · rintro ⟨-, hdvd⟩
    exact hνr.2.2 (Int.emod_eq_zero_of_dvd hdvd)
  · rw [hqe]
    exact mul_mem (inv_mem hUH) hqH

end CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.DetectE8
