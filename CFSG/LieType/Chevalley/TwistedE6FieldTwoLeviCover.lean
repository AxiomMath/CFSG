module

public import CFSG.LocalAnalysis.ComponentInitial.NonsplitOrthogonalCoverFour
public import CFSG.LieType.Chevalley.TwistedE6FieldTwoRelativePairs
public import CFSG.LieType.Chevalley.E7SupportedBruhat
public import CFSG.LieType.Chevalley.C2E6FourthResidueOrder

public noncomputable section

namespace CFSG.LieType.Chevalley.C2E6Std.TwistedE6LeviCover

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley.C2E6Overlap
  CFSG.LieType.Chevalley.C2E6Std.FourthResidue CFSG.Assembly.LowTwoRank
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail
  CFSG.LocalAnalysis.ComponentInitial.NonsplitOrthogonalCover CFSG.ClassicalGroups.Orthogonal
  CFSG.LieType.Universal.Spin CFSG.LieType.Chevalley CFSG.LieType.Chevalley.C2E6Std.RelativeRoots
  CFSG.LieType.Chevalley.RootOps

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

abbrev minusGroup : Subgroup (V0 ≃ₗ[ZMod 2] V0) :=
  orthElementaryGroup (quadTail 3 (minusTailForm (ZMod 2) 1 1))

theorem qBin_eq_minusTailForm : qBin = minusTailForm (ZMod 2) 1 1 := by
  ext z
  rw [qBin_apply, minusTailForm_apply]
  ring

theorem Qminus_eq : Qminus = quadTail 3 (minusTailForm (ZMod 2) 1 1) := by
  rw [← qBin_eq_minusTailForm]

theorem isPerfect_minusGroup : Group.IsPerfect minusGroup := by
  have h := (orthogonal_elementary_perfect regular_Qminus.1 regular_Qminus.2).1
  rwa [Qminus_eq] at h

@[expose] def leviEquiv :
    stdLevi fourthJ ≃* minusGroup :=
  (MonoidHom.ofInjective rhoMinus_injective).trans
    (MulEquiv.subgroupCongr (range_rhoMinus.trans (by rw [Qminus_eq])))

theorem isPerfect_stdLevi_fourthJ
    : Group.IsPerfect (stdLevi fourthJ) :=
  have := isPerfect_minusGroup
  Group.IsPerfect.ofSurjective (f := leviEquiv.symm.toMonoidHom) leviEquiv.symm.surjective

@[expose] def statedMinusEquiv :
    StatedProj (StatedOmega (StatedQuadMinus 4 (ZMod 2) 1 1)) ≃* minusGroup :=
  (tailProjEquiv (minusTailIsometry 4 (ZMod 2) 1 1) (coe_quadMinus 4 (ZMod 2) 1 1)
    (commutator_orthogonalGroup_quadMinus (by norm_num) (by decide))).trans
    ((QuotientGroup.quotientMulEquivOfEq (elemScalars_quadTail_eq_bot (by norm_num))).trans
      QuotientGroup.quotientBot)

theorem lieModel_stdLevi_fourthJ
    : LieModel (stdLevi fourthJ) .POmegaMinus 4 2 1 :=
  Or.inl ⟨by decide, ⟨Nat.prime_two, le_rfl, le_rfl⟩, ZMod 2, inferInstance, inferInstance,
    by rw [Nat.card_zmod, pow_one], 1, 1, by decide,
    ⟨leviEquiv.trans statedMinusEquiv.symm⟩⟩

theorem ker_eq_bot_of_minusGroup {E : Type*} [Group E] [Finite E] [Group.IsPerfect E]
    (θ : E →* minusGroup) (hθ : Function.Surjective θ) (hC : θ.ker ≤ Subgroup.center E)
    (h2 : IsPGroup 2 θ.ker) : θ.ker = ⊥ :=
  ker_eq_bot_of_binShape_three (K := ZMod 2) (Nat.card_zmod 2) θ hθ hC h2

theorem exists_split_of_mulEquiv {X : Type*} [Group X] (L' : Subgroup X) (e : L' ≃* minusGroup)
    {E : Type*} [Group E] [Finite E] (η : E →* X) (hη : Function.Surjective η)
    (hC : η.ker ≤ Subgroup.center E) (h2 : IsPGroup 2 η.ker) :
    ∃ F : Subgroup E, F.map η = L' ∧ (∀ x ∈ F, η x = 1 → x = 1) ∧ F ⊓ η.ker = ⊥ ∧
      L'.comap η = F ⊔ η.ker := by
  have := isPerfect_minusGroup
  have : Group.IsPerfect L' :=
    Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  set F := OrthogonalSplit.leviLift η L' with hF
  have : Group.IsPerfect F := OrthogonalSplit.isPerfect_leviLift η L' hη hC
  set θ : F →* minusGroup := e.toMonoidHom.comp (OrthogonalSplit.leviLiftHom η L') with hθdef
  have hθsurj : Function.Surjective θ :=
    e.surjective.comp (OrthogonalSplit.leviLiftHom_surjective η L' hη)
  have hθker : ∀ u : F, θ u = 1 ↔ η u = 1 := fun u => by
    rw [hθdef, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, e.map_eq_one_iff,
      OrthogonalSplit.leviLiftHom_eq_one_iff]
  have hθC : θ.ker ≤ Subgroup.center F := fun u hu => Subgroup.mem_center_iff.mpr fun g =>
    Subtype.ext (Subgroup.mem_center_iff.mp (hC ((hθker u).mp hu)) g)
  have hθ2 : IsPGroup 2 θ.ker := fun k => by
    obtain ⟨m, hm⟩ := h2 ⟨((k : F) : E), (hθker k).mp k.2⟩
    exact ⟨m, Subtype.ext (Subtype.ext (by
      simpa using congrArg (fun w : η.ker => (w : E)) hm))⟩
  have hbot := ker_eq_bot_of_minusGroup θ hθsurj hθC hθ2
  have hinj : ∀ x ∈ F, η x = 1 → x = 1 := fun x hx hx1 => by
    have hk : (⟨x, hx⟩ : F) ∈ θ.ker := (hθker _).mpr hx1
    rw [hbot, Subgroup.mem_bot] at hk
    exact congrArg Subtype.val hk
  refine ⟨F, OrthogonalSplit.map_leviLift η L' hη, hinj, ?_, ?_⟩
  · exact eq_bot_iff.mpr fun x hx => Subgroup.mem_bot.mpr (hinj x hx.1 hx.2)
  · refine le_antisymm (OrthogonalSplit.comap_le_leviLift_sup_ker η L' hη) (sup_le
      (OrthogonalSplit.leviLift_le_comap η L') fun c hc => ?_)
    rw [Subgroup.mem_comap, show η c = 1 from hc]
    exact one_mem _

abbrev leviG : Subgroup stdGroup :=
  (stdLevi fourthJ).subgroupOf stdGroup

theorem stdLevi_fourthJ_le_stdGroup :
    stdLevi fourthJ ≤ stdGroup :=
  (stdLevi_le_nativeParabolic two_mem_fourthJ).trans (nativeParabolic_le_stdGroup fourthJ)

@[expose] def leviGEquiv :
    leviG ≃* minusGroup :=
  (Subgroup.subgroupOfEquivOfLe stdLevi_fourthJ_le_stdGroup).trans leviEquiv

theorem exists_split_conj_stdLevi
    {E : Type*} [Group E] [Finite E] (η : E →* stdGroup)
    (hη : Function.Surjective η) (hC : η.ker ≤ Subgroup.center E) (h2 : IsPGroup 2 η.ker)
    (g : stdGroup) :
    ∃ F : Subgroup E, F.map η = leviG.map (MulAut.conj g).toMonoidHom ∧
      (∀ x ∈ F, η x = 1 → x = 1) ∧ F ⊓ η.ker = ⊥ ∧
      (leviG.map (MulAut.conj g).toMonoidHom).comap η = F ⊔ η.ker :=
  exists_split_of_mulEquiv _ ((leviG.equivMapOfInjective (MulAut.conj g).toMonoidHom
    (MulAut.conj g).injective).symm.trans leviGEquiv) η hη hC h2

abbrev leviT
    : Subgroup (ModGL TwistTag.E6.tag K) :=
  stdLevi fourthJ

abbrev leviConj
    (n : ModGL TwistTag.E6.tag K) : Subgroup (ModGL TwistTag.E6.tag K) :=
  leviT.map (MulAut.conj n).toMonoidHom

theorem e6Root_zero_five : ∀ k : Fin 72,
    e6Root k ⟨0, by decide⟩ + e6Root k ⟨5, by decide⟩ = 0 →
      e6Root k ⟨0, by decide⟩ = 0 ∧ e6Root k ⟨5, by decide⟩ = 0 := by
  decide +kernel

theorem eq_zero_or_eq_five_of_not_mem_setD {i : Fin 6} (hi : i ∉ setD) : i = 0 ∨ i = 5 := by
  simp only [setD, Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hi
  fin_cases i <;> simp_all

theorem relFibre_subset_parabolicRoots
    {r : Fin Tag.F4.rank → ℤ} (h3 : r ⟨3, by decide⟩ = 0) :
    relFibre r ⊆ parabolicRoots Tag.E6 setD := by
  rintro β ⟨hβ, hβr⟩
  obtain ⟨k, rfl⟩ := exists_e6Root_eq hβ
  have h : e6Root k ⟨0, by decide⟩ + e6Root k ⟨5, by decide⟩ = 0 := by
    have h' := congrFun hβr ⟨3, by decide⟩
    rw [h3] at h'
    exact h'
  obtain ⟨h0, h5⟩ := e6Root_zero_five k h
  refine ⟨isRoot_e6Root k, fun i hi => ?_⟩
  rcases eq_zero_or_eq_five_of_not_mem_setD hi with rfl | rfl
  · exact h0
  · exact h5

theorem rootSpan_le_groupD
    {S : Set (Fin Tag.E6.rank → ℤ)} (hS : S ⊆ parabolicRoots Tag.E6 setD) :
    rootSpan Tag.E6 K S ≤ groupD :=
  (rootSpan_mono hS).trans (subsystemGroup_eq_rootSpan (τ := Tag.E6) (K := K) setD).symm.le

theorem relRootGroup_le_leviT
    {r : Fin Tag.F4.rank → ℤ} (h3 : r ⟨3, by decide⟩ = 0) :
    relRootGroup r ≤ leviT := by
  intro x hx
  change x ∈ stdLevi fourthJ
  rw [stdLevi_fourthJ]
  exact ⟨rootSpan_le_groupD (relFibre_subset_parabolicRoots h3) hx.1, hx.2⟩

theorem f4Euclid_apply_zero (r : Fin Tag.F4.rank → ℤ) :
    f4Euclid r 0 = (r ⟨3, by decide⟩ : ℚ) / 2 := by
  have key : ∀ v : Fin 4 → ℤ, (∑ i, (v i : ℚ) • f4SimpleEuclid i) 0 = (v 3 : ℚ) / 2 := by
    intro v
    rw [Finset.sum_apply, Fin.sum_univ_four]
    simp [f4SimpleEuclid]
    ring
  exact key r

theorem relRootGroup_le_leviT_of_euclid
    {r : Fin Tag.F4.rank → ℤ} (h : f4Euclid r 0 = 0) :
    relRootGroup r ≤ leviT := by
  refine relRootGroup_le_leviT ?_
  have h' := f4Euclid_apply_zero r
  rw [h] at h'
  have h'' : (r ⟨3, by decide⟩ : ℚ) = 0 := by linarith
  exact_mod_cast h''

theorem simple_two_simple_three_single_two :
    simple .F4 ⟨2, by decide⟩ • simple .F4 ⟨3, by decide⟩ •
      (Pi.single ⟨2, by decide⟩ 1 : Fin Tag.F4.rank → ℤ) = Pi.single ⟨3, by decide⟩ 1 := by
  rw [simple_smul, simple_smul]
  decide +kernel

theorem exists_smul_eq_of_fourth_zero
    {r : Fin Tag.F4.rank → ℤ} (hr : IsRoot .F4 r) :
    ∃ (w : WeylGroup .F4) (t : Fin Tag.F4.rank → ℤ), t ⟨3, by decide⟩ = 0 ∧ w • t = r := by
  obtain ⟨w, j, hj⟩ := isRoot_iff_exists_smul_single.1 hr
  by_cases h3 : j = ⟨3, by decide⟩
  · subst h3
    refine ⟨w * (simple .F4 ⟨2, by decide⟩ * simple .F4 ⟨3, by decide⟩),
      Pi.single ⟨2, by decide⟩ 1, by decide, ?_⟩
    rw [mul_smul, mul_smul, simple_two_simple_three_single_two, hj]
  · exact ⟨w, Pi.single j 1, Pi.single_eq_of_ne (Ne.symm h3) 1, hj⟩

theorem exists_conj_levi_root
    {r : Fin Tag.F4.rank → ℤ} (hr : IsRoot .F4 r) :
    ∃ n ∈ graphFixedRootGroup TwistTag.E6 K barHom,
      relRootGroup r ≤ leviConj n ∧ relRootGroup (-r) ≤ leviConj n := by
  obtain ⟨w, t, ht3, rfl⟩ := exists_smul_eq_of_fourth_zero hr
  obtain ⟨w', hw'⟩ := exists_relWeylTwist_lift w
  refine ⟨_, canonicalRep_mem_root hw'.1, ?_, ?_⟩
  · rw [← map_conj_relRootGroup hw' t]
    exact Subgroup.map_mono (relRootGroup_le_leviT ht3)
  · rw [← smul_neg, ← map_conj_relRootGroup hw' (-t)]
    exact Subgroup.map_mono (relRootGroup_le_leviT (by rw [Pi.neg_apply, ht3, neg_zero]))

theorem pairTable_rep_fourth_zero : ∀ row ∈ pairTable .F4,
    ((f4Euclid (orbitCertRoot .F4 row.1) ⬝ᵥ f4Euclid (orbitCertRoot .F4 row.1) = 2 ∧
        f4Euclid (orbitCertRoot .F4 row.2.1) ⬝ᵥ f4Euclid (orbitCertRoot .F4 row.2.1) = 2) ∨
      f4Euclid (orbitCertRoot .F4 row.1) ⬝ᵥ f4Euclid (orbitCertRoot .F4 row.1) ≠
        f4Euclid (orbitCertRoot .F4 row.2.1) ⬝ᵥ f4Euclid (orbitCertRoot .F4 row.2.1) ∨
      (f4Euclid (orbitCertRoot .F4 row.1) ⬝ᵥ f4Euclid (orbitCertRoot .F4 row.1) = 1 ∧
        f4Euclid (orbitCertRoot .F4 row.2.1) ⬝ᵥ f4Euclid (orbitCertRoot .F4 row.2.1) = 1 ∧
        f4Euclid (orbitCertRoot .F4 row.1) ⬝ᵥ f4Euclid (orbitCertRoot .F4 row.2.1) = 0)) →
    orbitCertRoot .F4 row.1 ⟨3, by decide⟩ = 0 ∧ orbitCertRoot .F4 row.2.1 ⟨3, by decide⟩ = 0 := by
  decide +kernel

theorem exists_conj_levi_pair
    {r s : Fin Tag.F4.rank → ℤ} (hr : IsRoot .F4 r)
    (hs : IsRoot .F4 s)
    (htype : (f4Euclid r ⬝ᵥ f4Euclid r = 2 ∧ f4Euclid s ⬝ᵥ f4Euclid s = 2) ∨
      f4Euclid r ⬝ᵥ f4Euclid r ≠ f4Euclid s ⬝ᵥ f4Euclid s ∨
      (f4Euclid r ⬝ᵥ f4Euclid r = 1 ∧ f4Euclid s ⬝ᵥ f4Euclid s = 1 ∧
        f4Euclid r ⬝ᵥ f4Euclid s = 0)) :
    ∃ n ∈ graphFixedRootGroup TwistTag.E6 K barHom,
      relRootGroup r ≤ leviConj n ∧ relRootGroup s ≤ leviConj n := by
  by_cases hrs : r = s
  · subst hrs
    obtain ⟨n, hn, h1, -⟩ := exists_conj_levi_root hr
    exact ⟨n, hn, h1, h1⟩
  by_cases hrs' : r = -s
  · subst hrs'
    obtain ⟨n, hn, h1, h2⟩ := exists_conj_levi_root hs
    exact ⟨n, hn, h2, h1⟩
  obtain ⟨row, hrow, w, hwr, hws⟩ := exists_pairTable_row hr hs hrs hrs'
  have eA := f4Euclid_smul_dotProduct w (orbitCertRoot .F4 row.1) (orbitCertRoot .F4 row.1)
  have eB := f4Euclid_smul_dotProduct w (orbitCertRoot .F4 row.2.1) (orbitCertRoot .F4 row.2.1)
  have eC := f4Euclid_smul_dotProduct w (orbitCertRoot .F4 row.1) (orbitCertRoot .F4 row.2.1)
  simp only [hwr, hws] at eA eB eC
  rw [eA, eB, eC] at htype
  obtain ⟨h1, h2⟩ := pairTable_rep_fourth_zero row hrow htype
  obtain ⟨w', hw'⟩ := exists_relWeylTwist_lift w
  refine ⟨_, canonicalRep_mem_root hw'.1, ?_, ?_⟩
  · rw [← hwr, ← map_conj_relRootGroup hw']
    exact Subgroup.map_mono (relRootGroup_le_leviT h1)
  · rw [← hws, ← map_conj_relRootGroup hw']
    exact Subgroup.map_mono (relRootGroup_le_leviT h2)

theorem map_subtype_leviG_conj
    (g : stdGroup) :
    (leviG.map (MulAut.conj g).toMonoidHom).map stdGroup.subtype =
      leviConj (g : ModGL Tag.E6 K) := by
  rw [Subgroup.map_map]
  have e : stdGroup.subtype.comp (MulAut.conj g).toMonoidHom =
      (MulAut.conj (g : ModGL Tag.E6 K)).toMonoidHom.comp stdGroup.subtype := by
    ext x
    simp [MulAut.conj_apply]
  rw [e, ← Subgroup.map_map, leviG, Subgroup.subgroupOf_map_subtype,
    inf_eq_left.2 stdLevi_fourthJ_le_stdGroup]
  rfl

theorem exists_split_relRootGroup
    {E : Type*} [Group E] [Finite E] (η : E →* stdGroup)
    (hη : Function.Surjective η) (hC : η.ker ≤ Subgroup.center E) (h2 : IsPGroup 2 η.ker)
    {r : Fin Tag.F4.rank → ℤ} (hr : IsRoot .F4 r) :
    ∃ F : Subgroup E, F.map η = (relRootGroup r).comap stdGroup.subtype ∧ F ⊓ η.ker = ⊥ ∧
      ((relRootGroup r).comap stdGroup.subtype).comap η = F ⊔ η.ker := by
  obtain ⟨n, hn, hle, -⟩ := exists_conj_levi_root hr
  obtain ⟨F, hFmap, -, hFker, -⟩ := exists_split_conj_stdLevi η hη hC h2 ⟨n, hn⟩
  set R := (relRootGroup r).comap stdGroup.subtype
  have hRle : R ≤ leviG.map (MulAut.conj (⟨n, hn⟩ : stdGroup)).toMonoidHom := by
    intro x hx
    have hx' : (x : ModGL Tag.E6 K) ∈
        (leviG.map (MulAut.conj (⟨n, hn⟩ : stdGroup)).toMonoidHom).map stdGroup.subtype := by
      rw [map_subtype_leviG_conj]
      exact hle hx
    obtain ⟨y, hy, hyx⟩ := hx'
    rwa [Subtype.ext hyx] at hy
  refine ⟨F ⊓ R.comap η, le_antisymm ?_ fun x hx => ?_, ?_, le_antisymm (fun z hz => ?_) ?_⟩
  · exact (Subgroup.map_mono inf_le_right).trans (Subgroup.map_comap_le η R)
  · obtain ⟨y, hy, rfl⟩ : x ∈ F.map η := hFmap ▸ hRle hx
    exact ⟨y, ⟨hy, hx⟩, rfl⟩
  · exact eq_bot_iff.2 ((inf_le_inf_right _ inf_le_left).trans hFker.le)
  · obtain ⟨y, hy, hyz⟩ : η z ∈ F.map η := hFmap ▸ hRle hz
    have hc : y⁻¹ * z ∈ η.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hyz, inv_mul_cancel]
    have hyR : y ∈ F ⊓ R.comap η := ⟨hy, Subgroup.mem_comap.2 (hyz ▸ hz)⟩
    rw [show z = y * (y⁻¹ * z) by group]
    exact Subgroup.mul_mem_sup hyR hc
  · refine sup_le inf_le_right fun c hc => ?_
    rw [Subgroup.mem_comap, show η c = 1 from hc]
    exact one_mem _

theorem mul_mul_mul_comm_of_central {M : Type*} [Group M] {c₁ : M} (h₁ : ∀ g, c₁ * g = g * c₁)
    (f₁ f₂ c₂ : M) : f₁ * c₁ * (f₂ * c₂) = f₁ * f₂ * (c₁ * c₂) := by
  rw [mul_assoc f₁, ← mul_assoc c₁, h₁ f₂, mul_assoc f₂, (mul_assoc f₁ f₂ (c₁ * c₂)).symm]

theorem commute_preimage_of_le_leviConj
    {E : Type*} [Group E] [Finite E] (η : E →* stdGroup)
    (hη : Function.Surjective η) (hC : η.ker ≤ Subgroup.center E) (h2 : IsPGroup 2 η.ker)
    {n : ModGL TwistTag.E6.tag K} (hn : n ∈ graphFixedRootGroup TwistTag.E6 K barHom)
    {A B : Subgroup (ModGL TwistTag.E6.tag K)} (hA : A ≤ leviConj n) (hB : B ≤ leviConj n)
    (hAB : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) :
    ∀ x ∈ (A.comap stdGroup.subtype).comap η, ∀ y ∈ (B.comap stdGroup.subtype).comap η,
      x * y = y * x := by
  obtain ⟨F, -, hFinj, -, hFcomap⟩ := exists_split_conj_stdLevi η hη hC h2 ⟨n, hn⟩
  have hsub : ∀ {D : Subgroup (ModGL TwistTag.E6.tag K)}, D ≤ leviConj n →
      (D.comap stdGroup.subtype).comap η ≤ F ⊔ η.ker := fun {D} hD z hz => by
    rw [← hFcomap]
    have hz' : ((η z : stdGroup) : ModGL Tag.E6 K) ∈
        (leviG.map (MulAut.conj (⟨n, hn⟩ : stdGroup)).toMonoidHom).map stdGroup.subtype := by
      rw [map_subtype_leviG_conj]
      exact hD hz
    obtain ⟨y, hy, hyz⟩ := hz'
    rw [Subgroup.mem_comap, ← Subtype.ext hyz]
    exact hy
  have hcen : ∀ c ∈ η.ker, ∀ g : E, c * g = g * c := fun c hc g =>
    (Subgroup.mem_center_iff.1 (hC hc) g).symm
  intro x hx y hy
  have hx' : x ∈ ((F ⊔ η.ker : Subgroup E) : Set E) := hsub hA hx
  have hy' : y ∈ ((F ⊔ η.ker : Subgroup E) : Set E) := hsub hB hy
  rw [Subgroup.mul_normal] at hx' hy'
  obtain ⟨f₁, hf₁, c₁, hc₁, rfl⟩ := hx'
  obtain ⟨f₂, hf₂, c₂, hc₂, rfl⟩ := hy'
  have hff : f₁ * f₂ = f₂ * f₁ := by
    have h1 : f₁ * f₂ * (f₂ * f₁)⁻¹ = 1 := by
      refine hFinj _ (mul_mem (mul_mem hf₁ hf₂) (inv_mem (mul_mem hf₂ hf₁))) ?_
      have e₁ : η f₁ = η (f₁ * c₁) := by rw [map_mul, show η c₁ = 1 from hc₁, mul_one]
      have e₂ : η f₂ = η (f₂ * c₂) := by rw [map_mul, show η c₂ = 1 from hc₂, mul_one]
      have hcomm : ((η f₁ : stdGroup) : ModGL Tag.E6 K) * (η f₂ : stdGroup) =
          ((η f₂ : stdGroup) : ModGL Tag.E6 K) * (η f₁ : stdGroup) := by
        rw [e₁, e₂]
        exact hAB _ hx _ hy
      rw [map_mul, map_inv, map_mul, map_mul, mul_inv_eq_one]
      exact Subtype.ext hcomm
    exact mul_inv_eq_one.1 h1
  calc f₁ * c₁ * (f₂ * c₂) = f₁ * f₂ * (c₁ * c₂) :=
        mul_mul_mul_comm_of_central (hcen c₁ hc₁) f₁ f₂ c₂
    _ = f₂ * f₁ * (c₂ * c₁) := by rw [hff, hcen c₁ hc₁ c₂]
    _ = f₂ * c₂ * (f₁ * c₁) := (mul_mul_mul_comm_of_central (hcen c₂ hc₂) f₂ f₁ c₁).symm

end CFSG.LieType.Chevalley.C2E6Std.TwistedE6LeviCover
