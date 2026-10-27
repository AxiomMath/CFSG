module

public import CFSG.LieType.Chevalley.C2E6StandardLevi

public noncomputable section

namespace CFSG.LieType.Chevalley.C2E6Std

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley.C2E6Overlap
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

theorem betaGL_apply (g : ModGL Tag.E6 K) :
    (betaGL g : Module.End K (RootModule Tag.E6 K)) = entrywise barHom g := rfl

theorem betaGL_betaGL (g : ModGL Tag.E6 K) : betaGL (betaGL g) = g := by
  refine Units.ext ?_
  rw [betaGL_apply, betaGL_apply, entrywise_entrywise, barHom_comp_barHom, entrywise_id]

theorem betaGL_injective :
    Function.Injective (betaGL : ModGL Tag.E6 K →* ModGL Tag.E6 K) :=
  Function.LeftInverse.injective betaGL_betaGL

theorem map_betaGL_eq_of_forall {H : Subgroup (ModGL Tag.E6 K)}
    (h : ∀ x ∈ H, betaGL x ∈ H) : H.map betaGL = H :=
  le_antisymm (Subgroup.map_le_iff_le_comap.mpr fun x hx => h x hx)
    fun x hx => ⟨betaGL x, h x hx, betaGL_betaGL x⟩

theorem betaGL_xUnit
    (i : Fin Tag.E6.rank) (c : K) :
    betaGL (xUnit Tag.E6 K i c) = xUnit Tag.E6 K i (barHom c) :=
  Units.ext (entrywise_xOp barHom i c)

theorem betaGL_yUnit
    (i : Fin Tag.E6.rank) (c : K) :
    betaGL (yUnit Tag.E6 K i c) = yUnit Tag.E6 K i (barHom c) :=
  Units.ext (entrywise_yOp barHom i c)

theorem betaGL_weylElt_one
    (i : Fin Tag.E6.rank) :
    betaGL (weylElt Tag.E6 K i 1) = weylElt Tag.E6 K i 1 := by
  refine Units.ext ?_
  rw [betaGL_apply]
  change entrywise barHom (xOp Tag.E6 K i 1 * yOp Tag.E6 K i (-((1⁻¹ : Kˣ) : K)) *
    xOp Tag.E6 K i 1) = xOp Tag.E6 K i 1 * yOp Tag.E6 K i (-((1⁻¹ : Kˣ) : K)) * xOp Tag.E6 K i 1
  rw [entrywise_mul, entrywise_mul, entrywise_xOp, entrywise_yOp, map_neg, inv_one, Units.val_one,
    map_one]

theorem betaGL_canonicalRep
    (w : WeylGroup Tag.E6) :
    betaGL (canonicalRep (coxeterSystem Tag.E6) K w) = canonicalRep (coxeterSystem Tag.E6) K w := by
  obtain ⟨ω, hω, rfl⟩ := (coxeterSystem Tag.E6).exists_isReduced w
  rw [canonicalRep_wordProd hω, map_list_prod, List.map_map]
  exact congrArg List.prod (List.map_congr_left fun i _ => betaGL_weylElt_one i)

theorem betaGL_nativeRep
    (i : Fin 4) : betaGL (nativeRep i) = nativeRep i :=
  betaGL_canonicalRep _

theorem betaGL_rootDiagUnit (a : Fin Tag.E6.rank → Kˣ) :
    betaGL (rootDiagUnit Tag.E6 a) =
      rootDiagUnit Tag.E6 fun i => Units.map barHom.toMonoidHom (a i) :=
  Units.ext (entrywise_rootDiag barHom a)

theorem betaGL_torusElt
    (i : Fin Tag.E6.rank) (t : Kˣ) :
    betaGL (torusElt Tag.E6 K i t) = torusElt Tag.E6 K i (Units.map barHom.toMonoidHom t) := by
  rw [torusElt_eq_rootDiagUnit, torusElt_eq_rootDiagUnit, betaGL_rootDiagUnit]
  congr 1
  funext j
  rw [map_zpow]

abbrev diagE6GL : ModGL Tag.E6 K := diagramMap TwistTag.E6 K

theorem betaGL_diagE6GL : betaGL diagE6GL = diagE6GL :=
  units_map_entrywiseHom_diagramMap barHom

theorem twistHom_eq_conj (g : ModGL Tag.E6 K) :
    twistHom TwistTag.E6 K barHom g = diagE6GL * betaGL g * diagE6GL⁻¹ := rfl

theorem betaGL_twistHom (g : ModGL Tag.E6 K) :
    betaGL (twistHom TwistTag.E6 K barHom g) = twistHom TwistTag.E6 K barHom (betaGL g) := by
  rw [twistHom_eq_conj, twistHom_eq_conj, map_mul, map_mul, map_inv, betaGL_diagE6GL]

theorem map_betaGL_rootSubgroup
    (α : Fin Tag.E6.rank → ℤ) :
    (rootSubgroup Tag.E6 K α).map betaGL = rootSubgroup Tag.E6 K α := by
  have h := map_entrywise_rootSubgroup (τ := Tag.E6) barEquiv α
  rw [barEquiv_toRingHom] at h
  exact h

theorem map_betaGL_rootSpan
    (S : Set (Fin Tag.E6.rank → ℤ)) :
    (rootSpan Tag.E6 K S).map betaGL = rootSpan Tag.E6 K S := by
  rw [rootSpan, Subgroup.map_iSup]
  refine iSup_congr fun α => ?_
  rw [Subgroup.map_iSup]
  exact iSup_congr fun _ => map_betaGL_rootSubgroup α

theorem betaGL_mem_rootSpan
    {S : Set (Fin Tag.E6.rank → ℤ)} {g : ModGL Tag.E6 K}
    (hg : g ∈ rootSpan Tag.E6 K S) : betaGL g ∈ rootSpan Tag.E6 K S := by
  rw [← map_betaGL_rootSpan S]
  exact Subgroup.mem_map_of_mem _ hg

theorem betaGL_mem_torusGroup
    {g : ModGL Tag.E6 K} (hg : g ∈ torusGroup Tag.E6 K) :
    betaGL g ∈ torusGroup Tag.E6 K := by
  have : torusGroup Tag.E6 K ≤ (torusGroup Tag.E6 K).comap betaGL := by
    refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨⟨i, t⟩, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_comap, betaGL_torusElt]
    exact torusElt_mem_torusGroup i _
  exact this hg

theorem betaGL_mem_subsystemGroup
    {X : Set (Fin Tag.E6.rank)} {g : ModGL Tag.E6 K}
    (hg : g ∈ subsystemGroup Tag.E6 K X) : betaGL g ∈ subsystemGroup Tag.E6 K X := by
  have : subsystemGroup Tag.E6 K X ≤ (subsystemGroup Tag.E6 K X).comap betaGL := by
    refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨i, hi, c, rfl | rfl⟩
    · rw [SetLike.mem_coe, Subgroup.mem_comap, betaGL_xUnit]
      exact Subgroup.subset_closure ⟨i, hi, _, Or.inl rfl⟩
    · rw [SetLike.mem_coe, Subgroup.mem_comap, betaGL_yUnit]
      exact Subgroup.subset_closure ⟨i, hi, _, Or.inr rfl⟩
  exact this hg

theorem betaGL_mem_adjointGroup
    {g : ModGL Tag.E6 K} (hg : g ∈ adjointGroup Tag.E6 K) :
    betaGL g ∈ adjointGroup Tag.E6 K := by
  have : adjointGroup Tag.E6 K ≤ (adjointGroup Tag.E6 K).comap betaGL := by
    refine (Subgroup.closure_le _).2 ?_
    rintro x ⟨i, c, hx | hx⟩
    · refine Subgroup.subset_closure ⟨i, barHom c, Or.inl ?_⟩
      rw [betaGL_apply, hx, entrywise_xOp]
    · refine Subgroup.subset_closure ⟨i, barHom c, Or.inr ?_⟩
      rw [betaGL_apply, hx, entrywise_yOp]
  exact this hg

theorem betaGL_mem_stdFixedGroup
    {g : ModGL Tag.E6 K} (hg : g ∈ stdFixedGroup) :
    betaGL g ∈ stdFixedGroup := by
  obtain ⟨hC, hF⟩ := (mem_twistedFixedGroup_iff_twistHom TwistTag.E6 K barHom).mp hg
  refine (mem_twistedFixedGroup_iff_twistHom TwistTag.E6 K barHom).mpr
    ⟨betaGL_mem_adjointGroup hC, ?_⟩
  rw [← betaGL_twistHom]
  exact congrArg betaGL hF

theorem betaGL_mem_inf {A B : Subgroup (ModGL Tag.E6 K)} (hA : ∀ {x}, x ∈ A → betaGL x ∈ A)
    (hB : ∀ {x}, x ∈ B → betaGL x ∈ B) {g : ModGL Tag.E6 K} (hg : g ∈ A ⊓ B) : betaGL g ∈ A ⊓ B :=
  Subgroup.mem_inf.mpr ⟨hA (Subgroup.mem_inf.mp hg).1, hB (Subgroup.mem_inf.mp hg).2⟩

theorem betaGL_mem_sup {A B : Subgroup (ModGL Tag.E6 K)} (hA : ∀ {x}, x ∈ A → betaGL x ∈ A)
    (hB : ∀ {x}, x ∈ B → betaGL x ∈ B) {g : ModGL Tag.E6 K} (hg : g ∈ A ⊔ B) :
    betaGL g ∈ A ⊔ B := by
  have : A ⊔ B ≤ (A ⊔ B).comap betaGL :=
    sup_le (fun _ hx => Subgroup.mem_sup_left (hA hx))
      (fun _ hx => Subgroup.mem_sup_right (hB hx))
  exact this hg

theorem betaGL_mem_stdUnipotent0
    {g : ModGL Tag.E6 K} (hg : g ∈ stdUnipotent0) :
    betaGL g ∈ stdUnipotent0 :=
  betaGL_mem_inf betaGL_mem_rootSpan betaGL_mem_stdFixedGroup hg

theorem betaGL_mem_negUnipotent0
    {g : ModGL Tag.E6 K}
    (hg : g ∈ graphFixedNegUnipotent TwistTag.E6 K barHom) :
    betaGL g ∈ graphFixedNegUnipotent TwistTag.E6 K barHom :=
  betaGL_mem_inf betaGL_mem_rootSpan betaGL_mem_stdFixedGroup hg

theorem betaGL_mem_stdGroup
    {g : ModGL Tag.E6 K} (hg : g ∈ stdGroup) : betaGL g ∈ stdGroup :=
  betaGL_mem_sup betaGL_mem_stdUnipotent0 betaGL_mem_negUnipotent0 hg

theorem betaGL_mem_borelGroup
    {g : ModGL Tag.E6 K} (hg : g ∈ borelGroup Tag.E6 K) :
    betaGL g ∈ borelGroup Tag.E6 K :=
  betaGL_mem_sup betaGL_mem_torusGroup betaGL_mem_rootSpan hg

theorem betaGL_mem_stdBorel0
    {g : ModGL Tag.E6 K} (hg : g ∈ stdBorel0) : betaGL g ∈ stdBorel0 :=
  betaGL_mem_inf betaGL_mem_borelGroup betaGL_mem_stdFixedGroup hg

theorem betaGL_mem_stdBorel
    {g : ModGL Tag.E6 K} (hg : g ∈ stdBorel) : betaGL g ∈ stdBorel :=
  betaGL_mem_inf betaGL_mem_stdBorel0 betaGL_mem_stdGroup hg

theorem betaGL_mem_stdTorus0
    {g : ModGL Tag.E6 K} (hg : g ∈ stdTorus0) : betaGL g ∈ stdTorus0 :=
  betaGL_mem_inf betaGL_mem_torusGroup betaGL_mem_stdFixedGroup hg

theorem betaGL_mem_stdTorus
    {g : ModGL Tag.E6 K} (hg : g ∈ stdTorus) : betaGL g ∈ stdTorus :=
  betaGL_mem_inf betaGL_mem_stdTorus0 betaGL_mem_stdGroup hg

theorem betaGL_mem_stdRadical
    {J : Set (Fin 4)} {g : ModGL Tag.E6 K} (hg : g ∈ stdRadical J) :
    betaGL g ∈ stdRadical J :=
  betaGL_mem_inf betaGL_mem_rootSpan betaGL_mem_stdFixedGroup hg

theorem betaGL_mem_stdLevi
    {J : Set (Fin 4)} {g : ModGL Tag.E6 K} (hg : g ∈ stdLevi J) :
    betaGL g ∈ stdLevi J :=
  betaGL_mem_inf betaGL_mem_subsystemGroup betaGL_mem_stdFixedGroup hg

theorem betaGL_mem_stdLeviUnipotent
    {J : Set (Fin 4)} {g : ModGL Tag.E6 K}
    (hg : g ∈ stdLeviUnipotent J) : betaGL g ∈ stdLeviUnipotent J :=
  betaGL_mem_inf betaGL_mem_rootSpan betaGL_mem_stdFixedGroup hg

theorem betaGL_mem_stdLeviBorel
    {J : Set (Fin 4)} {g : ModGL Tag.E6 K}
    (hg : g ∈ stdLeviBorel J) : betaGL g ∈ stdLeviBorel J :=
  betaGL_mem_sup betaGL_mem_stdTorus betaGL_mem_stdLeviUnipotent hg

theorem betaGL_mem_nativeParabolic
    {J : Set (Fin 4)} {g : ModGL Tag.E6 K}
    (hg : g ∈ nativeParabolic J) : betaGL g ∈ nativeParabolic J := by
  have : nativeParabolic J ≤ (nativeParabolic J).comap betaGL := by
    refine (Subgroup.closure_le _).2 ?_
    rintro x (hx | ⟨i, hi, rfl⟩)
    · exact Subgroup.subset_closure (Or.inl (betaGL_mem_stdBorel hx))
    · rw [SetLike.mem_coe, Subgroup.mem_comap, betaGL_nativeRep]
      exact Subgroup.subset_closure (Or.inr ⟨i, hi, rfl⟩)
  exact this hg

theorem map_betaGL_stdFixedGroup :
    stdFixedGroup.map betaGL = stdFixedGroup :=
  map_betaGL_eq_of_forall fun _ => betaGL_mem_stdFixedGroup

theorem map_betaGL_stdBorel :
    stdBorel.map betaGL = stdBorel :=
  map_betaGL_eq_of_forall fun _ => betaGL_mem_stdBorel

theorem map_betaGL_stdTorus :
    stdTorus.map betaGL = stdTorus :=
  map_betaGL_eq_of_forall fun _ => betaGL_mem_stdTorus

theorem map_betaGL_nativeParabolic
    (J : Set (Fin 4)) :
    (nativeParabolic J).map betaGL = nativeParabolic J :=
  map_betaGL_eq_of_forall fun _ => betaGL_mem_nativeParabolic

theorem map_betaGL_stdRadical
    (J : Set (Fin 4)) : (stdRadical J).map betaGL = stdRadical J :=
  map_betaGL_eq_of_forall fun _ => betaGL_mem_stdRadical

theorem map_betaGL_stdLevi
    (J : Set (Fin 4)) : (stdLevi J).map betaGL = stdLevi J :=
  map_betaGL_eq_of_forall fun _ => betaGL_mem_stdLevi

theorem map_betaGL_stdLeviUnipotent
    (J : Set (Fin 4)) :
    (stdLeviUnipotent J).map betaGL = stdLeviUnipotent J :=
  map_betaGL_eq_of_forall fun _ => betaGL_mem_stdLeviUnipotent

theorem map_betaGL_stdLeviBorel
    (J : Set (Fin 4)) :
    (stdLeviBorel J).map betaGL = stdLeviBorel J :=
  map_betaGL_eq_of_forall fun _ => betaGL_mem_stdLeviBorel

end CFSG.LieType.Chevalley.C2E6Std
