module

public import CFSG.LieType.Ree.LargeReeInvolutionCentralizersRankOne

public noncomputable section

namespace CFSG.LieType.Ree.LargeReeInvolution

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley ReeTag

section Bridge

variable {τ : Tag} {K : Type} [Field K]

theorem map_iSup_nativeRootSubgroups
    (P : Root τ → Prop) :
    (⨆ (α : Root τ) (_ : P α), (nativeRootSubgroups τ K).X α).map (adjointGroup τ K).subtype =
      rootSpan τ K {β | ∃ h : IsRoot τ β, P ⟨β, h⟩} := by
  apply le_antisymm
  · rw [Subgroup.map_iSup]
    refine iSup_le fun α => ?_
    rw [Subgroup.map_iSup]
    refine iSup_le fun hα => ?_
    rw [nativeRootSubgroups_X, ← (rootOperatorFamily τ).subgroupOf_rootSubgroup_eq K α,
      Subgroup.subgroupOf_map_subtype]
    exact inf_le_left.trans (le_iSup₂ (f := fun β (_ : β ∈ {β | ∃ h : IsRoot τ β, P ⟨β, h⟩}) =>
      rootSubgroup τ K β) α.1 ⟨α.2, hα⟩)
  · refine iSup₂_le fun β ⟨hβ, hP⟩ => ?_
    have hle : rootSubgroup τ K β ≤ adjointGroup τ K := rootSubgroup_le_adjointGroup β
    have e : rootSubgroup τ K β =
        ((rootOperatorFamily τ).rootSubgroup K ⟨β, hβ⟩).map (adjointGroup τ K).subtype := by
      rw [← (rootOperatorFamily τ).subgroupOf_rootSubgroup_eq K ⟨β, hβ⟩,
        Subgroup.subgroupOf_map_subtype, inf_eq_left.2 hle]
    rw [e]
    refine Subgroup.map_mono ?_
    rw [← nativeRootSubgroups_X]
    exact le_iSup₂ (f := fun (α : Root τ) (_ : P α) => (nativeRootSubgroups τ K).X α) ⟨β, hβ⟩ hP

theorem map_Uplus_eq_rootSpan
    (w : WeylGroup τ) :
    (Uplus τ K w).map (adjointGroup τ K).subtype =
      rootSpan τ K {β | IsRoot τ β ∧ 0 < height β ∧ 0 < height (w • β)} := by
  rw [Uplus, map_iSup_nativeRootSubgroups]
  congr 1
  ext β
  simp only [Set.mem_ofPred_eq, coe_smul_root]
  exact ⟨fun ⟨h, h1, h2⟩ => ⟨h, h1, h2⟩, fun ⟨h, h1, h2⟩ => ⟨h, h1, h2⟩⟩

theorem map_nativeU_eq_posUnipotent
    [Finite K] :
    (nativeData τ K).U.map (adjointGroup τ K).subtype = posUnipotent τ K := by
  change (⨆ (α : Root τ) (_ : 0 < height α.1), (nativeRootSubgroups τ K).X α).map _ = _
  rw [map_iSup_nativeRootSubgroups]
  congr 1
  ext β
  exact ⟨fun ⟨h, h1⟩ => ⟨h, h1⟩, fun ⟨h, h1⟩ => ⟨h, h1⟩⟩

end Bridge

variable {K : Type} [Field K] [Finite K] [CharP K F4.prime] {a : ℕ}

omit [Field K] [Finite K] [CharP K F4.prime] in
theorem fixedOrbitComplementRoots_eq_setOf
    (j : Fin F4.fixedOrbitCount) :
    F4.fixedOrbitComplementRoots j =
      {β | IsRoot F4.tag β ∧ 0 < height β ∧ 0 < height (F4.fixedOrbitElement j • β)} := by
  ext β
  constructor
  · intro hβ
    obtain ⟨hr, hp, -⟩ := mem_fixedOrbitComplementRoots_iff.1 hβ
    refine ⟨hr, hp, ?_⟩
    have h := smul_mem_fixedOrbitComplementRoots hβ
    exact (mem_fixedOrbitComplementRoots_iff.1 h).2.1
  · rintro ⟨hr, hp, hw⟩
    rw [fixedOrbitComplementRoots_eq]
    refine ⟨⟨hr, hp⟩, fun hE => ?_⟩
    have := height_fixedOrbitElement_smul_neg hE
    omega

theorem coe_blockGen_eq
    (j : Fin F4.fixedOrbitCount) :
    ((CFSG.SectionRank.LargeRee.blockGen ⟨j.1, j.2⟩ : F4.relWeylRee) : WeylGroup F4.tag) =
      F4.fixedOrbitElement j := by
  obtain ⟨j, hj⟩ := j
  change j < 2 at hj
  interval_cases j
  · rw [CFSG.SectionRank.LargeRee.coe_blockGen, blockElt_eq]
    rfl
  · rw [CFSG.SectionRank.LargeRee.coe_blockGen, blockElt_eq]
    rfl

theorem map_UplusFixed
    (j : Fin F4.fixedOrbitCount) :
    (CFSG.SectionRank.LargeRee.UplusFixed F4 K a
        (CFSG.SectionRank.LargeRee.blockGen ⟨j.1, j.2⟩ : WeylGroup F4.tag)).map
          (reeFixedEmb K a) = F4.reeFixedOrbitComplementUnipotent K a j := by
  rw [CFSG.SectionRank.LargeRee.UplusFixed, coe_blockGen_eq, reeFixedEmb, ← Subgroup.map_map,
    Subgroup.map_comap_eq, Subgroup.range_subtype,
    Subgroup.map_inf_eq _ _ _ Subtype.val_injective, map_Uplus_eq_rootSpan,
    map_reeFixed_eq_reeGamma, ← fixedOrbitComplementRoots_eq_setOf,
    reeFixedOrbitComplementUnipotent]
  exact inf_comm _ _

theorem map_UminusFixed
    (j : Fin F4.fixedOrbitCount) :
    (CFSG.SectionRank.LargeRee.UminusFixed F4 K a
        (CFSG.SectionRank.LargeRee.blockGen ⟨j.1, j.2⟩ : WeylGroup F4.tag)).map
          (reeFixedEmb K a) = F4.reeFixedOrbitUnipotent K a j := by
  rw [CFSG.SectionRank.LargeRee.UminusFixed, coe_blockGen_eq, reeFixedEmb, ← Subgroup.map_map,
    Subgroup.map_comap_eq, Subgroup.range_subtype,
    Subgroup.map_inf_eq _ _ _ Subtype.val_injective, map_Uminus_eq_rootSpan,
    map_reeFixed_eq_reeGamma, inversionSet_fixedOrbitElement, reeFixedOrbitUnipotent]
  exact inf_comm _ _

theorem map_reeUnipPart :
    (reeUnipPart F4 K a).map (reeFixedEmb K a) =
    F4.reeFixedPosUnipotent K a := by
  rw [reeUnipPart, reeFixedEmb, ← Subgroup.map_map, Subgroup.map_comap_eq,
    Subgroup.range_subtype, Subgroup.map_inf_eq _ _ _ Subtype.val_injective,
    map_nativeU_eq_posUnipotent, map_reeFixed_eq_reeGamma, reeFixedPosUnipotent]
  exact inf_comm _ _

theorem exists_mul_eq_of_mem_reeFixedPosUnipotent
    (j : Fin F4.fixedOrbitCount)
    {u : ModGL F4.tag K} (hu : u ∈ F4.reeFixedPosUnipotent K a) :
    ∃ v ∈ F4.reeFixedOrbitComplementUnipotent K a j,
      ∃ x ∈ F4.reeFixedOrbitUnipotent K a j, v * x = u := by
  rw [← map_reeUnipPart] at hu
  obtain ⟨u', hu', rfl⟩ := hu
  obtain ⟨v, hv, x, hx, rfl⟩ :=
    CFSG.SectionRank.LargeRee.exists_mem_UplusFixed_blockGen_mem_UminusFixed ⟨j.1, j.2⟩ hu'
  refine ⟨reeFixedEmb K a v, ?_, reeFixedEmb K a x, ?_, (map_mul _ _ _).symm⟩
  · rw [← map_UplusFixed]
    exact ⟨v, hv, rfl⟩
  · rw [← map_UminusFixed]
    exact ⟨x, hx, rfl⟩

theorem reeFixedOrbitComplementUnipotent_inf_reeFixedOrbitUnipotent
    (j : Fin F4.fixedOrbitCount) :
    F4.reeFixedOrbitComplementUnipotent K a j ⊓ F4.reeFixedOrbitUnipotent K a j = ⊥ := by
  rw [← map_UplusFixed, ← map_UminusFixed,
    ← Subgroup.map_inf_eq _ _ _ reeFixedEmb_injective,
    CFSG.SectionRank.LargeRee.UplusFixed_inf_UminusFixed, Subgroup.map_bot]

theorem eq_of_mul_eq_mul_complement
    (j : Fin F4.fixedOrbitCount) {v v' x x' : ModGL F4.tag K}
    (hv : v ∈ F4.reeFixedOrbitComplementUnipotent K a j)
    (hv' : v' ∈ F4.reeFixedOrbitComplementUnipotent K a j)
    (hx : x ∈ F4.reeFixedOrbitUnipotent K a j) (hx' : x' ∈ F4.reeFixedOrbitUnipotent K a j)
    (h : v * x = v' * x') : v = v' ∧ x = x' := by
  have e : v'⁻¹ * v = x' * x⁻¹ := by
    rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, ← h, mul_inv_cancel_right]
  have hm : v'⁻¹ * v ∈ F4.reeFixedOrbitComplementUnipotent K a j ⊓
      F4.reeFixedOrbitUnipotent K a j :=
    Subgroup.mem_inf.2 ⟨mul_mem (inv_mem hv') hv, e ▸ mul_mem hx' (inv_mem hx)⟩
  rw [reeFixedOrbitComplementUnipotent_inf_reeFixedOrbitUnipotent, Subgroup.mem_bot] at hm
  have h1 : v = v' := (inv_mul_eq_one.1 hm).symm
  refine ⟨h1, ?_⟩
  rw [h1] at h
  exact mul_left_cancel h

omit [Field K] [Finite K] [CharP K F4.prime] in
theorem fixedOrbitComplementRoots_absorbs
    (j : Fin F4.fixedOrbitCount) :
    ∀ α, IsRoot F4.tag α ∧ 0 < height α → ∀ β ∈ F4.fixedOrbitComplementRoots j, ∀ m n : ℕ,
      1 ≤ m → 1 ≤ n → IsRoot F4.tag (m • α + n • β) →
        m • α + n • β ∈ F4.fixedOrbitComplementRoots j := by
  intro α ⟨hα, hαp⟩ β hβ m n hm hn hr
  obtain ⟨hβr, hβp, i, hi, hβi⟩ := mem_fixedOrbitComplementRoots_iff.1 hβ
  have hnonneg : ∀ {γ : Fin F4.tag.rank → ℤ}, IsRoot F4.tag γ → 0 < height γ → ∀ k, 0 ≤ γ k := by
    intro γ hγ hγp
    rcases hγ.nonneg_or_nonpos with h | h
    · exact h
    · exfalso
      have : height γ ≤ 0 := Finset.sum_nonpos fun k _ => h k
      omega
  have hβi' : 0 < β i := lt_of_le_of_ne (hnonneg hβr hβp i) (Ne.symm hβi)
  have hαi := hnonneg hα hαp i
  refine mem_fixedOrbitComplementRoots_iff.2 ⟨hr, ?_, i, hi, ?_⟩
  · rw [height_nsmul_add_nsmul]
    have : (1 : ℤ) ≤ m := by exact_mod_cast hm
    have : (1 : ℤ) ≤ n := by exact_mod_cast hn
    nlinarith
  · rw [Pi.add_apply, Pi.smul_apply, Pi.smul_apply, nsmul_eq_mul, nsmul_eq_mul]
    have : (1 : ℤ) ≤ n := by exact_mod_cast hn
    have : (0 : ℤ) ≤ m := by exact_mod_cast Nat.zero_le m
    nlinarith

theorem reeFixedOrbitComplementUnipotent_le
    (j : Fin F4.fixedOrbitCount) :
    F4.reeFixedOrbitComplementUnipotent K a j ≤ F4.reeFixedPosUnipotent K a :=
  inf_le_inf_right _ (rootSpan_le_posUnipotent fun _ hα =>
    ⟨(mem_fixedOrbitComplementRoots_iff.1 hα).1, (mem_fixedOrbitComplementRoots_iff.1 hα).2.1⟩)

theorem reeFixedOrbitUnipotent_le
    (j : Fin F4.fixedOrbitCount) :
    F4.reeFixedOrbitUnipotent K a j ≤ F4.reeFixedPosUnipotent K a :=
  inf_le_inf_right _ (rootSpan_le_posUnipotent (fixedOrbitRoots_subset j))

theorem reeFixedPosUnipotent_le_normalizer
    (j : Fin F4.fixedOrbitCount) :
    F4.reeFixedPosUnipotent K a ≤
      Subgroup.normalizer (F4.reeFixedOrbitComplementUnipotent K a j : Set (ModGL F4.tag K)) :=
  fun _ hu => Subgroup.inf_normalizer_le_normalizer_inf (Subgroup.mem_inf.2
    ⟨posUnipotent_le_normalizer_of_absorbs (fun _ hα =>
        ⟨(mem_fixedOrbitComplementRoots_iff.1 hα).1, (mem_fixedOrbitComplementRoots_iff.1 hα).2.1⟩)
      (fixedOrbitComplementRoots_absorbs j) (Subgroup.mem_inf.1 hu).1,
      Subgroup.le_normalizer (Subgroup.mem_inf.1 hu).2⟩)

theorem reeFixedOrbitComplementUnipotent_normal
    (j : Fin F4.fixedOrbitCount) :
    ((F4.reeFixedOrbitComplementUnipotent K a j).subgroupOf (F4.reeFixedPosUnipotent K a)).Normal :=
  Subgroup.normal_subgroupOf_iff_le_normalizer (reeFixedOrbitComplementUnipotent_le j) |>.2
    (reeFixedPosUnipotent_le_normalizer j)

theorem reeFixedTorus_le_normalizer_complement
    (j : Fin F4.fixedOrbitCount) :
    F4.reeFixedTorus K a ≤
      Subgroup.normalizer (F4.reeFixedOrbitComplementUnipotent K a j : Set (ModGL F4.tag K)) :=
  fun _ hh => Subgroup.inf_normalizer_le_normalizer_inf (Subgroup.mem_inf.2
    ⟨torusGroup_le_normalizer_rootSpan (fun _ hα => (mem_fixedOrbitComplementRoots_iff.1 hα).1)
      (Subgroup.mem_inf.1 hh).1, Subgroup.le_normalizer (Subgroup.mem_inf.1 hh).2⟩)

theorem map_conj_reeFixedOrbitComplementUnipotent
    (j : Fin F4.fixedOrbitCount) :
    (F4.reeFixedOrbitComplementUnipotent K a j).map
        (MulAut.conj (canonicalRep (coxeterSystem F4.tag) K (F4.fixedOrbitElement j))).toMonoidHom =
      F4.reeFixedOrbitComplementUnipotent K a j := by
  have hn : canonicalRep (coxeterSystem F4.tag) K (F4.fixedOrbitElement j) ∈ F4.reeGamma K a :=
    (canonicalRep_mem_reeFixedMonomial F4 K a (fixedOrbitElement_mem j)).2
  rw [reeFixedOrbitComplementUnipotent, Subgroup.map_inf_eq _ _ _ (MulAut.conj _).injective,
    (canonical_weyl_root_transport F4.tag K).1 _ _
      fun α hα => (mem_fixedOrbitComplementRoots_iff.1 hα).1,
    (bijOn_fixedOrbitComplementRoots j).image_eq,
    map_conj_eq_of_mem_normalizer (Subgroup.le_normalizer hn)]

theorem exists_mul_eq_of_mem_reeFixedPosUnipotent'
    (j : Fin F4.fixedOrbitCount)
    {u : ModGL F4.tag K} (hu : u ∈ F4.reeFixedPosUnipotent K a) :
    ∃ x ∈ F4.reeFixedOrbitUnipotent K a j,
      ∃ v ∈ F4.reeFixedOrbitComplementUnipotent K a j, x * v = u := by
  obtain ⟨v, hv, x, hx, h⟩ := exists_mul_eq_of_mem_reeFixedPosUnipotent j (inv_mem hu)
  refine ⟨x⁻¹, inv_mem hx, v⁻¹, inv_mem hv, ?_⟩
  rw [← mul_inv_rev, h, inv_inv]

theorem reeFixedOrbitComplementUnipotent_sup
    (j : Fin F4.fixedOrbitCount) :
    F4.reeFixedOrbitComplementUnipotent K a j ⊔ F4.reeFixedOrbitUnipotent K a j =
      F4.reeFixedPosUnipotent K a := by
  refine le_antisymm (sup_le (reeFixedOrbitComplementUnipotent_le j) (reeFixedOrbitUnipotent_le j))
    fun u hu => ?_
  obtain ⟨v, hv, x, hx, rfl⟩ := exists_mul_eq_of_mem_reeFixedPosUnipotent j hu
  exact mul_mem (Subgroup.mem_sup_left hv) (Subgroup.mem_sup_right hx)

theorem card_reeFixedPosUnipotent_eq_mul
    (j : Fin F4.fixedOrbitCount) :
    Nat.card (F4.reeFixedPosUnipotent K a) =
      Nat.card (F4.reeFixedOrbitComplementUnipotent K a j) *
        Nat.card (F4.reeFixedOrbitUnipotent K a j) := by
  rw [← Nat.card_prod]
  refine (Nat.card_congr (Equiv.ofBijective (fun p : F4.reeFixedOrbitComplementUnipotent K a j ×
      F4.reeFixedOrbitUnipotent K a j => (⟨(p.1 : ModGL F4.tag K) * p.2,
        mul_mem (reeFixedOrbitComplementUnipotent_le j p.1.2)
          (reeFixedOrbitUnipotent_le j p.2.2)⟩ : F4.reeFixedPosUnipotent K a)) ⟨?_, ?_⟩)).symm
  · rintro ⟨v, x⟩ ⟨v', x'⟩ h
    obtain ⟨h1, h2⟩ := eq_of_mul_eq_mul_complement j v.2 v'.2 x.2 x'.2 (congrArg Subtype.val h)
    exact Prod.ext (Subtype.ext h1) (Subtype.ext h2)
  · rintro ⟨u, hu⟩
    obtain ⟨v, hv, x, hx, rfl⟩ := exists_mul_eq_of_mem_reeFixedPosUnipotent j hu
    exact ⟨(⟨v, hv⟩, ⟨x, hx⟩), rfl⟩

end CFSG.LieType.Ree.LargeReeInvolution
