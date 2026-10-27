module

public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Detect.F4.MPart
public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Detect.F4.LA
public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Detect.F4.Leaf.Action

public noncomputable section

namespace CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.DetectF4

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.SeitzReduction
open CFSG.LieType.Steinberg.Adjoint Heis

set_option linter.unusedSectionVars false


variable (K : Type) [Field K]

theorem f4ShortList_cases : ∀ γ ∈ f4ShortList,
    γ = Pi.single 2 1 ∨ γ = -Pi.single 2 1 ∨ γ = Pi.single 3 1 ∨ γ = -Pi.single 3 1 ∨
    γ = reflect .F4 2 (Pi.single 3 1) ∨ γ = -reflect .F4 2 (Pi.single 3 1) := by
  decide +kernel

theorem reflect_two_single_three : reflect Tag.F4 2 (Pi.single 3 1) = Pi.single 2 1 + Pi.single 3 1 := by
  decide +kernel

theorem isRoot_reflect_two_single_three : IsRoot Tag.F4 (reflect Tag.F4 2 (Pi.single 3 1)) :=
  IsRoot.reflect 2 (isRoot_single Tag.F4 3)

theorem pinnedX_mem_Lθ_S2 {γ : Fin Tag.F4.rank → ℤ} (hγ : γ ∈ f4ShortList) (t : K) :
    pinnedX Tag.F4 K γ t ∈ Lθ Tag.F4 K := by
  have hJ2 : (2 : Fin Tag.F4.rank) ∈ Heis.Jθ Tag.F4 := by
    show (2 : Fin Tag.F4.rank) ≠ Heis.iθ Tag.F4
    decide +kernel
  have hJ3 : (3 : Fin Tag.F4.rank) ∈ Heis.Jθ Tag.F4 := by
    show (3 : Fin Tag.F4.rank) ≠ Heis.iθ Tag.F4
    decide +kernel
  have hn2 : weylElt Tag.F4 K 2 1 ∈ Lθ Tag.F4 K := weylElt_mem_parabolicLevi hJ2
  rcases f4ShortList_cases γ hγ with rfl | rfl | rfl | rfl | rfl | rfl
  · rw [pinnedX_single]; exact xUnit_mem_parabolicLevi hJ2 t
  · rw [pinnedX_neg_single]; exact yUnit_mem_parabolicLevi hJ2 t
  · rw [pinnedX_single]; exact xUnit_mem_parabolicLevi hJ3 t
  · rw [pinnedX_neg_single]; exact yUnit_mem_parabolicLevi hJ3 t
  · have h := map_conj_weylElt_rootSubgroup K 2 (isRoot_single Tag.F4 3)
    have hmem : pinnedX Tag.F4 K (reflect Tag.F4 2 (Pi.single 3 1)) t ∈
        (rootSubgroup Tag.F4 K (Pi.single 3 1)).map (MulAut.conj (weylElt Tag.F4 K 2 1)).toMonoidHom := by
      rw [h]
      exact mem_rootSubgroup.2 ⟨t, rfl⟩
    obtain ⟨y, hy, hyy⟩ := hmem
    have hy' : y ∈ Lθ Tag.F4 K := by
      obtain ⟨c, rfl⟩ := mem_rootSubgroup.1 hy
      rw [pinnedX_single]
      exact xUnit_mem_parabolicLevi hJ3 c
    rw [← hyy]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    exact mul_mem (mul_mem hn2 hy') (inv_mem hn2)
  · have h := map_conj_weylElt_rootSubgroup K 2 (isRoot_neg_single Tag.F4 3)
    have hr : reflect Tag.F4 2 (-Pi.single 3 1) = -reflect Tag.F4 2 (Pi.single 3 1) := by
      decide +kernel
    rw [hr] at h
    have hmem : pinnedX Tag.F4 K (-reflect Tag.F4 2 (Pi.single 3 1)) t ∈
        (rootSubgroup Tag.F4 K (-Pi.single 3 1)).map (MulAut.conj (weylElt Tag.F4 K 2 1)).toMonoidHom := by
      rw [h]
      exact mem_rootSubgroup.2 ⟨t, rfl⟩
    obtain ⟨y, hy, hyy⟩ := hmem
    have hy' : y ∈ Lθ Tag.F4 K := by
      obtain ⟨c, rfl⟩ := mem_rootSubgroup.1 hy
      rw [pinnedX_neg_single]
      exact yUnit_mem_parabolicLevi hJ3 c
    rw [← hyy]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    exact mul_mem (mul_mem hn2 hy') (inv_mem hn2)

theorem exists_two_ne_of_card [Finite K] (hK : 3 ≤ Nat.card K) : ∃ t : K, t ≠ 0 ∧ t ≠ 1 := by
  classical
  haveI := Fintype.ofFinite K
  by_contra h
  push Not at h
  have hsub : (Finset.univ : Finset K) ⊆ {0, 1} := fun t _ => by
    by_cases h0 : t = 0
    · simp [h0]
    · simp [h t h0]
  have h1 := Finset.card_le_card hsub
  rw [Finset.card_univ, ← Nat.card_eq_fintype_card] at h1
  have h2 : ({0, 1} : Finset K).card ≤ 2 := Finset.card_le_two
  omega

theorem mRoots_ne : ∀ β ∈ mRoots, β ≠ alpha1 ∧ β ≠ root1342 := by decide +kernel

theorem actFun_supp {a1 a2 : (Fin Tag.F4.rank → ℤ) → (Fin Tag.F4.rank → ℤ) → ℤ} (h1 : Adm1 a1)
    (h2 : Adm2 a2) {γ : Fin Tag.F4.rank → ℤ} (hγ : γ ∈ f4ShortList) (t : K)
    {c : (Fin Tag.F4.rank → ℤ) → K} (hc : ∀ ν, ν ∉ mRoots → c ν = 0)
    (ν : Fin Tag.F4.rank → ℤ) (hν : ν ∉ mRoots) : actFun a1 a2 γ t c ν = 0 := by
  have hterm1 : (a1 γ (ν - γ) : K) * c (ν - γ) = 0 := by
    by_cases hμ : ν - γ ∈ mRoots
    · by_cases hr : γ + (ν - γ) ∈ rootFinset .F4
      · exfalso
        have := (add_mem_mRoots γ hγ _ hμ).1 hr
        rw [add_sub_cancel] at this
        exact hν this
      · have := (h1.short γ hγ _ (List.mem_append_left _ hμ)).2 hr
        rw [this, Int.cast_zero, zero_mul]
    · rw [hc _ hμ, mul_zero]
  have hterm2 : (a2 γ (ν - 2 • γ) : K) * c (ν - 2 • γ) = 0 := by
    by_cases hμ : ν - 2 • γ ∈ mRoots
    · by_cases hr : 2 • γ + (ν - 2 • γ) ∈ rootFinset .F4
      · exfalso
        have := (add_mem_mRoots γ hγ _ hμ).2 hr
        rw [add_sub_cancel] at this
        exact hν this
      · have := (h2.short γ hγ _ (List.mem_append_left _ hμ)).2 hr
        rw [this, Int.cast_zero, zero_mul]
    · rw [hc _ hμ, mul_zero]
  simp only [actFun]
  rw [hc ν hν, mul_assoc, hterm1, mul_assoc, hterm2]
  ring

theorem lemma3 [Finite K] (hK : 3 ≤ Nat.card K) {H : Subgroup (ModGL Tag.F4 K)}
    (hX : XS K ≤ H) (hM : MPart K H) :
    ∃ β, IsRoot Tag.F4 β ∧ β ∉ cosetRoots Tag.F4 1 3 ∧ ∃ c : K, c ≠ 0 ∧
      pinnedX Tag.F4 K β c ∈ H := by
  classical
  have hK' := exists_two_ne_of_card K hK
  obtain ⟨a1, a2, h1, h2, hact⟩ := exists_action_data K
  have hs := heisCoord_spec Tag.F4 K
  have hxH : ∀ γ ∈ f4ShortList, ∀ t : K, pinnedX Tag.F4 K γ t ∈ H := fun γ hγ t =>
    hX (X2_le_XS K (pinnedX_mem_rootSpan (S := S2set) hγ t))
  have hxP : ∀ γ ∈ f4ShortList, ∀ t : K, pinnedX Tag.F4 K γ t ∈ Pθ Tag.F4 K := fun γ hγ t =>
    parabolicLevi_le_parabolicSubgroup (Heis.Jθ Tag.F4) (pinnedX_mem_Lθ_S2 K hγ t)
  let W : Set ((Fin Tag.F4.rank → ℤ) → K) := {c | ∃ q ∈ H, q ∈ Qθ Tag.F4 K ∧
    heisCoord Tag.F4 K q = c ∧ ∀ ν, ν ∉ mRoots → c ν = 0}
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
  have hstab : ∀ γ ∈ f4ShortList, ∀ t : K, ∀ c ∈ W, actFun a1 a2 γ t c ∈ W := by
    rintro γ hγ t _ ⟨q, hq, hqQ, rfl, hqs⟩
    have hnorm := parabolicSubgroup_le_normalizer_parabolicRadical (τ := Tag.F4) (K := K)
      (Heis.Jθ Tag.F4) (hxP γ hγ t)
    have hq' : pinnedX Tag.F4 K γ t * q * (pinnedX Tag.F4 K γ t)⁻¹ ∈ Qθ Tag.F4 K :=
      (Subgroup.mem_normalizer_iff.1 hnorm q).1 hqQ
    refine ⟨pinnedX Tag.F4 K γ t * q * (pinnedX Tag.F4 K γ t)⁻¹,
      mul_mem (mul_mem (hxH γ hγ t) hq) (inv_mem (hxH γ hγ t)), hq', hact γ (f4ShortList_deg0 γ hγ).1 (f4ShortList_deg0 γ hγ).2 t q hqQ,
      actFun_supp K h1 h2 hγ t hqs⟩
  have hne : ∃ c ∈ W, c ≠ 0 := by
    obtain ⟨q, hqH, hqQ, β, hβM, hβ0⟩ := hM
    let f : (Fin Tag.F4.rank → ℤ) → K := fun ν =>
      if ν = alpha1 ∨ ν = root1342 then heisCoord Tag.F4 K q ν else 0
    have hf : ∀ ν, ν ∉ Deg1 Tag.F4 → f ν = 0 := by
      intro ν hν
      simp only [f]
      split_ifs with h
      · rcases h with rfl | rfl
        · exact absurd alpha1_deg1 hν
        · exact absurd root1342_deg1 hν
      · rfl
    obtain ⟨s, hsQ, hsc⟩ := hs.surj f hf
    have hsX1 : s ∈ X1 K := by
      refine mem_X1_of_coord_M_zero K hsQ fun β' hβ' => ?_
      rw [hsc]
      simp only [f]
      rw [if_neg]
      push Not
      exact mRoots_ne β' hβ'
    have hsH : s ∈ H := hX (X1_le_XS K hsX1)
    refine ⟨heisCoord Tag.F4 K (q * s⁻¹), ⟨q * s⁻¹, mul_mem hqH (inv_mem hsH),
      mul_mem hqQ (inv_mem hsQ), rfl, fun ν hν => ?_⟩, fun h0 => hβ0 ?_⟩
    · rw [hs.mul q hqQ _ (inv_mem hsQ), heisCoord_inv hsQ, hsc]
      simp only [Pi.add_apply, Pi.neg_apply, f]
      by_cases hν' : ν = alpha1 ∨ ν = root1342
      · rw [if_pos hν']
        ring
      · rw [if_neg hν']
        by_cases hD : ν ∈ Deg1 Tag.F4
        · rcases Deg1_cases hD with h | h | h
          · exact absurd (Or.inl h) hν'
          · exact absurd (Or.inr h) hν'
          · exact absurd h hν
        · rw [hs.support q hqQ ν hD]
          ring
    · have := congrFun h0 β
      rw [hs.mul q hqQ _ (inv_mem hsQ), heisCoord_inv hsQ, hsc] at this
      simp only [Pi.add_apply, Pi.neg_apply, f, Pi.zero_apply] at this
      rw [if_neg (by push Not; exact mRoots_ne β hβM)] at this
      simpa using this
  obtain ⟨ν, hν, e, he, hW⟩ := LA_core hK' h1 h2 W hadd hneg hsupp hstab hne
  obtain ⟨q, hqH, hqQ, hqc, -⟩ := hW
  have hνD : ν ∈ Deg1 Tag.F4 := mem_Deg1_of_mem_deg1Roots (List.mem_append_left _ hν)
  have hq1Q := pinnedX_mem_Qθ K hνD e
  have hzero : heisCoord Tag.F4 K (q * (pinnedX Tag.F4 K ν e)⁻¹) = 0 := by
    rw [hs.mul q hqQ _ (inv_mem hq1Q), heisCoord_inv hq1Q, hs.pinnedX_deg1 ν hνD e, hqc]
    funext x
    simp
  have hU := (hs.eq_zero_iff _ (mul_mem hqQ (inv_mem hq1Q))).1 hzero
  have hUH : q * (pinnedX Tag.F4 K ν e)⁻¹ ∈ H := hX (X1_le_XS K (Uθ_le_X1 K hU))
  have hqe : pinnedX Tag.F4 K ν e = (q * (pinnedX Tag.F4 K ν e)⁻¹)⁻¹ * q := by group
  refine ⟨ν, (mRoots_data ν hν).1 |> mem_rootFinset.1, ?_, e, he, ?_⟩
  · rintro ⟨-, hdvd⟩
    have := (mRoots_data ν hν).2.2
    exact this (Int.emod_eq_zero_of_dvd hdvd)
  · rw [hqe]
    exact mul_mem (inv_mem hUH) hqH

end CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.DetectF4
