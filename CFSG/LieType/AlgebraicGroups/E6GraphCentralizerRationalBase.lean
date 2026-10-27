module

public import CFSG.LieType.Chevalley.CLSOddE7RationalDerivedIndex
public import CFSG.LieType.Chevalley.OddF4CosetDescent
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBFixedCentralQuotientComponents
public import CFSG.LocalAnalysis.ComponentInitial.LocalComponents
public import CFSG.LieType.AlgebraicGroups.E6GraphCentralizerLangCurves

public noncomputable section

namespace CFSG.LieType.AlgebraicGroups

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.Steinberg.Adjoint
open scoped Pointwise

section Descent

variable {τ : Tag} {K : Type} [Field K] (σ : K ≃+* K)

theorem entrywise_baseChangeGL_fixSubfield
    (y : ModGL τ (fixSubfield σ)) :
    Units.map (entrywiseHom σ.toRingHom) (baseChangeGL (fixSubfield σ).subtype y) =
      baseChangeGL (fixSubfield σ).subtype y := by
  rw [units_map_entrywiseHom_eq_baseChangeGL, baseChangeGL_baseChangeGL,
    show σ.toRingHom.comp (fixSubfield σ).subtype = (fixSubfield σ).subtype from
      RingHom.ext fun c => c.2]

theorem mem_map_rootSpan_of_fixed
    {S : Set (Fin τ.rank → ℤ)} (hS : S.Finite)
    (hcoll : ∀ {m : ℕ} (α : Fin m → Fin τ.rank → ℤ), Function.Injective α → Set.range α = S →
      Set.BijOn (fun c : Fin m → K => (List.ofFn fun k => pinnedX τ K (α k) (c k)).prod)
        Set.univ (rootSpan τ K S))
    {u : ModGL τ K} (hu : u ∈ rootSpan τ K S) (hfix : Units.map (entrywiseHom σ.toRingHom) u = u) :
    u ∈ (rootSpan τ (fixSubfield σ) S).map (baseChangeGL (fixSubfield σ).subtype) := by
  have : Finite S := hS.to_subtype
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin S
  set α : Fin n → Fin τ.rank → ℤ := fun k => (e.symm k : Fin τ.rank → ℤ)
  have hα : Function.Injective α := fun k k' h => e.symm.injective (Subtype.ext h)
  have hαS : ∀ k, α k ∈ S := fun k => (e.symm k).2
  have hrange : Set.range α = S := by
    ext x
    constructor
    · rintro ⟨k, rfl⟩
      exact hαS k
    · intro hx
      exact ⟨e ⟨x, hx⟩, by simp [α]⟩
  have hbij := hcoll α hα hrange
  obtain ⟨c, -, rfl⟩ := hbij.2.2 hu
  have hmap : Units.map (entrywiseHom σ.toRingHom)
      ((List.ofFn fun k => pinnedX τ K (α k) (c k)).prod) =
        (List.ofFn fun k => pinnedX τ K (α k) (σ (c k))).prod := by
    rw [map_list_prod, List.map_ofFn]
    refine congrArg List.prod (congrArg List.ofFn (funext fun k => ?_))
    refine Units.ext ?_
    rw [Function.comp_apply, Units.coe_map]
    exact entrywise_pinnedX σ.toRingHom (α k) (c k)
  rw [hmap] at hfix
  have hc : (fun k => σ (c k)) = c := hbij.2.1 (Set.mem_univ _) (Set.mem_univ _) hfix
  refine ⟨(List.ofFn fun k => pinnedX τ (fixSubfield σ) (α k) ⟨c k, congrFun hc k⟩).prod,
    list_prod_pinnedX_mem_rootSpan α hαS _, ?_⟩
  beta_reduce
  rw [map_list_prod, List.map_ofFn]
  refine congrArg List.prod (congrArg List.ofFn (funext fun k => ?_))
  rw [Function.comp_apply, baseChangeGL_pinnedX]
  rfl

theorem MapsRootLines.baseChangeGL
    {R S : Type} [Field R] [Field S] (f : R →+* S)
    {g : ModGL τ R} {w : WeylGroup τ} (h : MapsRootLines g w) :
    MapsRootLines (CFSG.LieType.Chevalley.baseChangeGL f g) w := by
  intro α hα
  obtain ⟨c, hc⟩ := h α hα
  have hwα := IsRoot.smul hα w
  refine ⟨Units.map f.toMonoidHom c, ?_⟩
  rw [coe_baseChangeGL, rootVec_eq_single_of_isRoot' hα, baseChangeEnd_single,
    ← rootVec_eq_single_of_isRoot' hα, hc, mapRange_smul', rootVec_eq_single_of_isRoot' hwα,
    rootVec_eq_single_of_isRoot' hwα, Finsupp.mapRange_single, map_one]
  rfl

theorem mem_centralizer_of_baseChangeGL
    {R S : Type} [Field R] [Field S] (f : R →+* S)
    {A y : ModGL τ R}
    (h : CFSG.LieType.Chevalley.baseChangeGL f y ∈
      Subgroup.centralizer {CFSG.LieType.Chevalley.baseChangeGL f A}) :
    y ∈ Subgroup.centralizer {A} := by
  rw [Subgroup.mem_centralizer_singleton_iff] at h ⊢
  apply baseChangeGL_injective f
  rw [map_mul, map_mul, h]

end Descent

section Rational

variable {τ : Tag} {K : Type} [Field K] (σ : K ≃+* K) (A : ModGL τ (fixSubfield σ))

abbrev rationalFixedGroup :
    Subgroup (ModGL τ K) :=
  graphCentralizer τ K (CFSG.LieType.Chevalley.baseChangeGL (fixSubfield σ).subtype A) ⊓
    (Units.map (entrywiseHom σ.toRingHom)).eqLocus (MonoidHom.id _)

abbrev rationalFixedTorus :
    Subgroup (ModGL τ K) :=
  torusGroup τ K ⊓ rationalFixedGroup σ A

abbrev rationalRootGroup :
    Subgroup (ModGL τ K) :=
  ((posUnipotent τ (fixSubfield σ) ⊓ graphCentralizer τ (fixSubfield σ) A) ⊔
    (negUnipotent τ (fixSubfield σ) ⊓ graphCentralizer τ (fixSubfield σ) A)).map
      (CFSG.LieType.Chevalley.baseChangeGL (fixSubfield σ).subtype)

theorem baseChangeGL_mem_rationalFixedGroup
    {y : ModGL τ (fixSubfield σ)}
    (hy : y ∈ graphCentralizer τ (fixSubfield σ) A) :
    CFSG.LieType.Chevalley.baseChangeGL (fixSubfield σ).subtype y ∈ rationalFixedGroup σ A := by
  obtain ⟨hyG, hyc⟩ := Subgroup.mem_inf.1 hy
  rw [Subgroup.mem_centralizer_singleton_iff] at hyc
  refine Subgroup.mem_inf.2 ⟨Subgroup.mem_inf.2 ⟨baseChangeGL_mem_adjointGroup _ hyG, ?_⟩,
    entrywise_baseChangeGL_fixSubfield σ y⟩
  rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul, hyc]

theorem rationalRootGroup_le :
    rationalRootGroup σ A ≤ rationalFixedGroup σ A := by
  rintro _ ⟨y, hy, rfl⟩
  have hle : (posUnipotent τ (fixSubfield σ) ⊓ graphCentralizer τ (fixSubfield σ) A) ⊔
      (negUnipotent τ (fixSubfield σ) ⊓ graphCentralizer τ (fixSubfield σ) A) ≤
        graphCentralizer τ (fixSubfield σ) A := sup_le inf_le_right inf_le_right
  exact baseChangeGL_mem_rationalFixedGroup σ A (hle hy)

theorem mem_rationalRootGroup_of_fixed
    {S : Set (Fin τ.rank → ℤ)} (hS : S.Finite)
    (hSpos : rootSpan τ (fixSubfield σ) S ≤ posUnipotent τ (fixSubfield σ))
    (hcoll : ∀ {m : ℕ} (α : Fin m → Fin τ.rank → ℤ), Function.Injective α → Set.range α = S →
      Set.BijOn (fun c : Fin m → K => (List.ofFn fun k => pinnedX τ K (α k) (c k)).prod)
        Set.univ (rootSpan τ K S))
    {u : ModGL τ K} (hu : u ∈ rootSpan τ K S) (huJ : u ∈ rationalFixedGroup σ A) :
    u ∈ rationalRootGroup σ A := by
  obtain ⟨⟨-, huc⟩, hfix⟩ := Subgroup.mem_inf.1 huJ |>.imp_left Subgroup.mem_inf.1
  obtain ⟨y, hy, rfl⟩ := mem_map_rootSpan_of_fixed σ hS hcoll hu hfix
  refine ⟨y, Subgroup.mem_sup_left (Subgroup.mem_inf.2 ⟨hSpos hy, Subgroup.mem_inf.2
    ⟨posUnipotent_le_adjointGroup (hSpos hy),
      mem_centralizer_of_baseChangeGL (fixSubfield σ).subtype huc⟩⟩), rfl⟩

theorem mem_rationalRootGroup_of_posUnipotent
    {u : ModGL τ K} (hu : u ∈ posUnipotent τ K)
    (huJ : u ∈ rationalFixedGroup σ A) : u ∈ rationalRootGroup σ A :=
  mem_rationalRootGroup_of_fixed σ A ((finite_setOf_isRoot τ).subset fun _ hβ => hβ.1) le_rfl
    (fun α hα hr => (positive_root_collection τ K).2 α hα hr) hu huJ

theorem mem_rationalRootGroup_of_inversionSet
    {w : WeylGroup τ} {u : ModGL τ K}
    (hu : u ∈ rootSpan τ K (inversionSet w)) (huJ : u ∈ rationalFixedGroup σ A) :
    u ∈ rationalRootGroup σ A :=
  mem_rationalRootGroup_of_fixed σ A (inversionSet_finite w)
    (rootSpan_le_posUnipotent fun _ h => inversionSet_pos (w := w) h)
    (fun α hα hr => (bruhat_cell_factorization τ K).2.1 w α hα hr) hu huJ

end Rational

section Torus

variable {τ : Tag} {R : Type} [Field R]

theorem conj_rootDiagUnit_mem_rootSpan
    (a : Fin τ.rank → Rˣ) {S : Set (Fin τ.rank → ℤ)}
    (hS : ∀ α ∈ S, IsRoot τ α) {g : ModGL τ R} (hg : g ∈ rootSpan τ R S) :
    rootDiagUnit τ a * g * (rootDiagUnit τ a)⁻¹ ∈ rootSpan τ R S := by
  have hle : rootSpan τ R S ≤
      (rootSpan τ R S).comap (MulAut.conj (rootDiagUnit τ a)).toMonoidHom := by
    refine iSup₂_le fun α hα => (Subgroup.closure_le _).2 ?_
    rintro _ ⟨c, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    have h : rootDiagUnit τ a * pinnedX τ R α c * (rootDiagUnit τ a)⁻¹ =
        pinnedX τ R α ((rootChar a α : R) * c) := by
      rw [mul_inv_eq_iff_eq_mul]
      exact Units.ext (rootDiag_mul_pinnedX a (hS α hα) c)
    rw [h]
    exact pinnedX_mem_rootSpan hα _
  exact hle hg

end Torus

section TorusE6

variable {K : Type} [Field K] (σ : K ≃+* K) (c : Fin TwistTag.E6.tag.rank → (fixSubfield σ)ˣ)

theorem baseChangeGL_rootDiagUnit_mul_diagramMap :
    CFSG.LieType.Chevalley.baseChangeGL (fixSubfield σ).subtype
        (rootDiagUnit TwistTag.E6.tag c * diagramMap TwistTag.E6 (fixSubfield σ)) =
      rootDiagUnit TwistTag.E6.tag (fun i => Units.map (fixSubfield σ).subtype.toMonoidHom (c i)) *
        diagramMap TwistTag.E6 K := by
  rw [map_mul, baseChangeGL_rootDiagUnit, baseChangeGL_diagramMap]

theorem conj_mem_rationalRootGroup
    {h : ModGL TwistTag.E6.tag K}
    (hh : h ∈ rationalFixedTorus σ
      (rootDiagUnit TwistTag.E6.tag c * diagramMap TwistTag.E6 (fixSubfield σ)))
    {x : ModGL TwistTag.E6.tag K}
    (hx : x ∈ rationalRootGroup σ
      (rootDiagUnit TwistTag.E6.tag c * diagramMap TwistTag.E6 (fixSubfield σ))) :
    h * x * h⁻¹ ∈ rationalRootGroup σ
      (rootDiagUnit TwistTag.E6.tag c * diagramMap TwistTag.E6 (fixSubfield σ)) := by
  set AK := rootDiagUnit TwistTag.E6.tag c * diagramMap TwistTag.E6 (fixSubfield σ)
  obtain ⟨hT, hJ⟩ := Subgroup.mem_inf.1 hh
  obtain ⟨hZ, hF⟩ := Subgroup.mem_inf.1 hJ
  obtain ⟨-, hc⟩ := Subgroup.mem_inf.1 hZ
  obtain ⟨a, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hT
  have hσa : ∀ i, σ (a i : K) = a i := by
    have hF' : Units.map (entrywiseHom σ.toRingHom) (rootDiagUnit TwistTag.E6.tag a) =
        rootDiagUnit TwistTag.E6.tag a := hF
    have h0 : Units.map (entrywiseHom σ.toRingHom) (rootDiagUnit TwistTag.E6.tag a) =
        rootDiagUnit TwistTag.E6.tag (fun i => Units.map σ.toRingHom.toMonoidHom (a i)) :=
      Units.ext (entrywise_rootDiag σ.toRingHom a)
    have h1 := rootDiagUnit_injective (h0.symm.trans hF')
    intro i
    exact congrArg Units.val (congrFun h1 i)
  have hσa' : ∀ i, σ ((a i)⁻¹ : Kˣ) = ((a i)⁻¹ : Kˣ) := fun i => by
    rw [Units.val_inv_eq_inv_val, map_inv₀, hσa]
  rw [baseChangeGL_rootDiagUnit_mul_diagramMap, Subgroup.mem_centralizer_singleton_iff,
    rootDiagUnit_commute_iff] at hc
  let aK : Fin TwistTag.E6.tag.rank → (fixSubfield σ)ˣ := fun i =>
    ⟨⟨a i, hσa i⟩, ⟨((a i)⁻¹ : Kˣ), hσa' i⟩, Subtype.ext (Units.mul_inv _),
      Subtype.ext (Units.inv_mul _)⟩
  have haK : rootDiagUnit TwistTag.E6.tag a = CFSG.LieType.Chevalley.baseChangeGL
      (fixSubfield σ).subtype (rootDiagUnit TwistTag.E6.tag aK) := by
    rw [baseChangeGL_rootDiagUnit]
    congr 1
  have haKρ : (fun i => aK (TwistTag.E6.perm.symm i)) = aK := by
    funext i
    exact Units.ext (Subtype.ext (congrArg Units.val (congrFun hc i)))
  have hdc : rootDiagUnit TwistTag.E6.tag aK * AK = AK * rootDiagUnit TwistTag.E6.tag aK :=
    (rootDiagUnit_commute_iff c aK).2 haKρ
  have hconjZ : ∀ y ∈ graphCentralizer TwistTag.E6.tag (fixSubfield σ) AK,
      rootDiagUnit TwistTag.E6.tag aK * y * (rootDiagUnit TwistTag.E6.tag aK)⁻¹ ∈
        graphCentralizer TwistTag.E6.tag (fixSubfield σ) AK := by
    intro y hy
    obtain ⟨hyG, hyc⟩ := Subgroup.mem_inf.1 hy
    rw [Subgroup.mem_centralizer_singleton_iff] at hyc
    refine Subgroup.mem_inf.2 ⟨conj_rootDiagUnit_mem_adjointGroup aK hyG, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hd : Commute (rootDiagUnit TwistTag.E6.tag aK) AK := hdc
    have hy : Commute y AK := hyc
    exact ((hd.mul_left hy).mul_left hd.inv_left).eq
  have hle : (posUnipotent TwistTag.E6.tag (fixSubfield σ) ⊓
      graphCentralizer TwistTag.E6.tag (fixSubfield σ) AK) ⊔
        (negUnipotent TwistTag.E6.tag (fixSubfield σ) ⊓
          graphCentralizer TwistTag.E6.tag (fixSubfield σ) AK) ≤
      ((posUnipotent TwistTag.E6.tag (fixSubfield σ) ⊓
        graphCentralizer TwistTag.E6.tag (fixSubfield σ) AK) ⊔
          (negUnipotent TwistTag.E6.tag (fixSubfield σ) ⊓
            graphCentralizer TwistTag.E6.tag (fixSubfield σ) AK)).comap
        (MulAut.conj (rootDiagUnit TwistTag.E6.tag aK)).toMonoidHom := by
    refine sup_le (fun y hy => ?_) (fun y hy => ?_)
    · obtain ⟨hyU, hyZ⟩ := Subgroup.mem_inf.1 hy
      exact Subgroup.mem_sup_left (Subgroup.mem_inf.2
        ⟨conj_rootDiagUnit_mem_rootSpan aK (fun _ h => h.1) hyU, hconjZ y hyZ⟩)
    · obtain ⟨hyU, hyZ⟩ := Subgroup.mem_inf.1 hy
      exact Subgroup.mem_sup_right (Subgroup.mem_inf.2
        ⟨conj_rootDiagUnit_mem_rootSpan aK (fun _ h => h.1) hyU, hconjZ y hyZ⟩)
  obtain ⟨y, hy, rfl⟩ := hx
  refine ⟨_, hle hy, ?_⟩
  rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, map_mul, map_mul, map_inv, ← haK]

theorem rationalFixedTorus_mul_comm
    (A : ModGL TwistTag.E6.tag (fixSubfield σ))
    {h h' : ModGL TwistTag.E6.tag K} (hh : h ∈ rationalFixedTorus σ A)
    (hh' : h' ∈ rationalFixedTorus σ A) : h * h' = h' * h := by
  obtain ⟨a, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup (Subgroup.mem_inf.1 hh).1
  obtain ⟨a', rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup (Subgroup.mem_inf.1 hh').1
  rw [← rootDiagUnit_mul, ← rootDiagUnit_mul, mul_comm]

theorem rationalRootGroup_normal
    (hJ : (rationalFixedGroup σ
      (rootDiagUnit TwistTag.E6.tag c * diagramMap TwistTag.E6 (fixSubfield σ)) :
        Set (ModGL TwistTag.E6.tag K)) ⊆
      (rationalFixedTorus σ
        (rootDiagUnit TwistTag.E6.tag c * diagramMap TwistTag.E6 (fixSubfield σ)) :
          Set (ModGL TwistTag.E6.tag K)) *
        (rationalRootGroup σ
          (rootDiagUnit TwistTag.E6.tag c * diagramMap TwistTag.E6 (fixSubfield σ)) :
            Set (ModGL TwistTag.E6.tag K))) :
    ((rationalRootGroup σ
      (rootDiagUnit TwistTag.E6.tag c * diagramMap TwistTag.E6 (fixSubfield σ))).subgroupOf
        (rationalFixedGroup σ
          (rootDiagUnit TwistTag.E6.tag c * diagramMap TwistTag.E6 (fixSubfield σ)))).Normal := by
  refine (Subgroup.normal_subgroupOf_iff (rationalRootGroup_le σ _)).2 fun x g hx hg => ?_
  obtain ⟨t, ht, s, hs, rfl⟩ := Set.mem_mul.1 (hJ hg)
  have h1 : s * x * s⁻¹ ∈ rationalRootGroup σ
      (rootDiagUnit TwistTag.E6.tag c * diagramMap TwistTag.E6 (fixSubfield σ)) :=
    mul_mem (mul_mem hs hx) (inv_mem hs)
  have h2 := conj_mem_rationalRootGroup σ c ht h1
  rw [show t * s * x * (t * s)⁻¹ = t * (s * x * s⁻¹) * t⁻¹ by group]
  exact h2

theorem commutator_mem_rationalRootGroup
    (hJ : (rationalFixedGroup σ
      (rootDiagUnit TwistTag.E6.tag c * diagramMap TwistTag.E6 (fixSubfield σ)) :
        Set (ModGL TwistTag.E6.tag K)) ⊆
      (rationalFixedTorus σ
        (rootDiagUnit TwistTag.E6.tag c * diagramMap TwistTag.E6 (fixSubfield σ)) :
          Set (ModGL TwistTag.E6.tag K)) *
        (rationalRootGroup σ
          (rootDiagUnit TwistTag.E6.tag c * diagramMap TwistTag.E6 (fixSubfield σ)) :
            Set (ModGL TwistTag.E6.tag K)))
    {x y : ModGL TwistTag.E6.tag K}
    (hx : x ∈ rationalFixedGroup σ
      (rootDiagUnit TwistTag.E6.tag c * diagramMap TwistTag.E6 (fixSubfield σ)))
    (hy : y ∈ rationalFixedGroup σ
      (rootDiagUnit TwistTag.E6.tag c * diagramMap TwistTag.E6 (fixSubfield σ))) :
    x * y * x⁻¹ * y⁻¹ ∈ rationalRootGroup σ
      (rootDiagUnit TwistTag.E6.tag c * diagramMap TwistTag.E6 (fixSubfield σ)) := by
  obtain ⟨t, ht, s, hs, rfl⟩ := Set.mem_mul.1 (hJ hx)
  obtain ⟨t', ht', s', hs', rfl⟩ := Set.mem_mul.1 (hJ hy)
  have hcS : ∀ {u : ModGL TwistTag.E6.tag K}, u ∈ rationalFixedTorus σ
      (rootDiagUnit TwistTag.E6.tag c * diagramMap TwistTag.E6 (fixSubfield σ)) →
        ∀ {z}, z ∈ rationalRootGroup σ
          (rootDiagUnit TwistTag.E6.tag c * diagramMap TwistTag.E6 (fixSubfield σ)) →
        u * z * u⁻¹ ∈ rationalRootGroup σ
          (rootDiagUnit TwistTag.E6.tag c * diagramMap TwistTag.E6 (fixSubfield σ)) :=
    fun hu _ hz => conj_mem_rationalRootGroup σ c hu hz
  have htt : t * t' * t⁻¹ * t'⁻¹ = 1 := by
    rw [rationalFixedTorus_mul_comm σ _ ht ht']
    group
  have e : t * s * (t' * s') * (t * s)⁻¹ * (t' * s')⁻¹ =
      (t * s * t⁻¹) * ((t * t') * s' * (t * t')⁻¹) * ((t * t') * s⁻¹ * (t * t')⁻¹) *
        ((t * t' * t⁻¹) * s'⁻¹ * (t * t' * t⁻¹)⁻¹) * (t * t' * t⁻¹ * t'⁻¹) := by
    group
  rw [e, htt, mul_one]
  have hT1 := mul_mem ht ht'
  have hT2 : t * t' * t⁻¹ ∈ rationalFixedTorus σ
      (rootDiagUnit TwistTag.E6.tag c * diagramMap TwistTag.E6 (fixSubfield σ)) :=
    mul_mem hT1 (inv_mem ht)
  exact mul_mem (mul_mem (mul_mem (hcS ht hs) (hcS hT1 hs')) (hcS hT1 (inv_mem hs)))
    (hcS hT2 (inv_mem hs'))

end TorusE6

section Components

open CFSG.ComponentClassification.CatalogueBFixedCentralQuotient

theorem pComponent_eq_of_quasisimple_normal {G : Type*} [Group G] [Finite G] (p : ℕ)
    (hp : p.Prime) (N : Subgroup G) [N.Normal] [Group.IsSolvable (G ⧸ N)]
    (hNq : CFSG.IsQuasisimple N) (L : Subgroup G) (hL : CFSG.IsPComponent p L) :
    L = N ∧ CFSG.IsQuasisimple L := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨hLN, hLN'⟩ := (p_components_solvable_quotient_invariance p hp N L).1 hL
  have hLsub : (L.subgroupOf N).IsSubnormal := hLN'.choose_spec.2.1
  have := CFSG.ComponentClassification.CatalogueBAlternating.pComponent_nontrivial hLN'
  have := CFSG.ComponentClassification.CatalogueBAlternating.pComponent_perfect hLN'
  rcases quasisimple_subnormal_subgroups hNq hLsub with h | h
  · have hLeq : L = N := by
      refine le_antisymm hLN fun g hg => ?_
      have hmem : (⟨g, hg⟩ : N) ∈ L.subgroupOf N := by
        rw [h]
        trivial
      exact hmem
    refine ⟨hLeq, ?_⟩
    rw [hLeq]
    exact hNq
  · exfalso
    refine Group.IsPerfect.not_isMulCommutative (L.subgroupOf N) ⟨⟨fun x y => Subtype.ext ?_⟩⟩
    exact (Subgroup.mem_center_iff.1 (h x.2) y).symm

end Components

end CFSG.LieType.AlgebraicGroups
