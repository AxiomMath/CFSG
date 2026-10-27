module

public import CFSG.LieType.Chevalley.E6GraphLeviRealization
public import CFSG.LieType.Chevalley.E6GraphInvertedRootRotation

public noncomputable section

namespace CFSG.LieType.Chevalley.E6GraphLevi

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley.E6GraphHighestRoot
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.Steinberg.Adjoint
open scoped commutatorElement Pointwise

variable {E : Type} [Field E]

variable (E) in
abbrev thetaSL2 :
    SL2 E →* ModGL TwistTag.E6.tag E :=
  rootSL2 TwistTag.E6.tag E e6HighestRoot

theorem thetaSL2_uSL
    (h2 : (2 : E) = 0) (c : E) :
    thetaSL2 E (uSL c) = pinnedX TwistTag.E6.tag E e6HighestRoot c := by
  rw [rootSL2_uSL_eq]
  congr 1
  rcases pinnedSign_eq TwistTag.E6.tag e6HighestRoot with h | h <;> rw [h]
  · exact one_zsmul c
  · rw [neg_zsmul, one_zsmul, neg_eq_self_of_two h2]

theorem thetaSL2_vSL
    (h2 : (2 : E) = 0) (c : E) :
    thetaSL2 E (vSL c) = pinnedX TwistTag.E6.tag E (-e6HighestRoot) c := by
  obtain ⟨ε, hε, h⟩ := exists_rootSL2_vSL_eq (K := E) isRoot_e6HighestRoot
  rw [h, eq_one_of_mul_self_eq_one_of_two_eq_zero h2 hε, one_mul]

theorem thetaSL2_injective
    (h2 : (2 : E) = 0) : Function.Injective (thetaSL2 E) := by
  rw [injective_iff_map_eq_one]
  intro B hB
  set W := pinnedWeyl TwistTag.E6.tag E e6HighestRoot
  have hB' :
      simpleRootSL2 TwistTag.E6.tag E (pinnedData TwistTag.E6.tag e6HighestRoot).1 B = 1 := by
    have h := hB
    rw [rootSL2_apply] at h
    calc simpleRootSL2 TwistTag.E6.tag E (pinnedData TwistTag.E6.tag e6HighestRoot).1 B =
          W⁻¹ * (W * simpleRootSL2 TwistTag.E6.tag E
            (pinnedData TwistTag.E6.tag e6HighestRoot).1 B * W⁻¹) * W := by group
      _ = 1 := by rw [h]; group
  obtain ⟨l, hl, hBl⟩ := (exceptional_ordinary_rank_one_central_image TwistTag.E6.tag E
    (pinnedData TwistTag.E6.tag e6HighestRoot).1).choose_spec.2.2.2.2.2.1 B
    (MonoidHom.mem_ker.2 hB')
  have hl1 : (l : E) = 1 := eq_one_of_mul_self_eq_one_of_two_eq_zero h2 (by rw [← sq]; exact hl)
  refine Subtype.ext ?_
  rw [hBl, hl1, one_smul, Matrix.SpecialLinearGroup.coe_one]

theorem range_thetaSL2
    (h2 : (2 : E) = 0) :
    (thetaSL2 E).range = Subgroup.closure
      (Set.range (pinnedX TwistTag.E6.tag E e6HighestRoot) ∪
        Set.range (pinnedX TwistTag.E6.tag E (-e6HighestRoot))) := by
  have e1 : (thetaSL2 E) '' Set.range (sl2Upper E) =
      Set.range (pinnedX TwistTag.E6.tag E e6HighestRoot) := by
    ext g
    constructor
    · rintro ⟨_, ⟨c, rfl⟩, rfl⟩
      exact ⟨c, (thetaSL2_uSL h2 c).symm⟩
    · rintro ⟨c, rfl⟩
      exact ⟨_, ⟨c, rfl⟩, thetaSL2_uSL h2 c⟩
  have e2 : (thetaSL2 E) '' Set.range (sl2Lower E) =
      Set.range (pinnedX TwistTag.E6.tag E (-e6HighestRoot)) := by
    ext g
    constructor
    · rintro ⟨_, ⟨c, rfl⟩, rfl⟩
      exact ⟨c, (thetaSL2_vSL h2 c).symm⟩
    · rintro ⟨c, rfl⟩
      exact ⟨_, ⟨c, rfl⟩, thetaSL2_vSL h2 c⟩
  rw [MonoidHom.range_eq_map, ← sl2_closure_upper_lower, MonoidHom.map_closure, Set.image_union,
    e1, e2]

theorem map_uSL {k : Type} [Field k] (ι : k →+* E) (c : k) :
    Matrix.SpecialLinearGroup.map ι (uSL c) = uSL (ι c) := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.map_apply_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [uSL]

theorem map_vSL {k : Type} [Field k] (ι : k →+* E) (c : k) :
    Matrix.SpecialLinearGroup.map ι (vSL c) = vSL (ι c) := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.map_apply_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [vSL]

theorem range_thetaSL2_comp_map
    {k : Type} [Field k] (ι : k →+* E) (h2 : (2 : E) = 0) :
    ((thetaSL2 E).comp (Matrix.SpecialLinearGroup.map ι)).range = Subgroup.closure
      (Set.range (fun c : k => pinnedX TwistTag.E6.tag E e6HighestRoot (ι c)) ∪
        Set.range (fun c : k => pinnedX TwistTag.E6.tag E (-e6HighestRoot) (ι c))) := by
  have e1 : ((thetaSL2 E).comp (Matrix.SpecialLinearGroup.map ι)) '' Set.range (sl2Upper k) =
      Set.range (fun c : k => pinnedX TwistTag.E6.tag E e6HighestRoot (ι c)) := by
    ext g
    constructor
    · rintro ⟨_, ⟨c, rfl⟩, rfl⟩
      refine ⟨c, ?_⟩
      change pinnedX TwistTag.E6.tag E e6HighestRoot (ι c) =
        thetaSL2 E (Matrix.SpecialLinearGroup.map ι (uSL c))
      rw [map_uSL, thetaSL2_uSL h2]
    · rintro ⟨c, rfl⟩
      refine ⟨_, ⟨c, rfl⟩, ?_⟩
      change thetaSL2 E (Matrix.SpecialLinearGroup.map ι (uSL c)) =
        pinnedX TwistTag.E6.tag E e6HighestRoot (ι c)
      rw [map_uSL, thetaSL2_uSL h2]
  have e2 : ((thetaSL2 E).comp (Matrix.SpecialLinearGroup.map ι)) '' Set.range (sl2Lower k) =
      Set.range (fun c : k => pinnedX TwistTag.E6.tag E (-e6HighestRoot) (ι c)) := by
    ext g
    constructor
    · rintro ⟨_, ⟨c, rfl⟩, rfl⟩
      refine ⟨c, ?_⟩
      change pinnedX TwistTag.E6.tag E (-e6HighestRoot) (ι c) =
        thetaSL2 E (Matrix.SpecialLinearGroup.map ι (vSL c))
      rw [map_vSL, thetaSL2_vSL h2]
    · rintro ⟨c, rfl⟩
      refine ⟨_, ⟨c, rfl⟩, ?_⟩
      change thetaSL2 E (Matrix.SpecialLinearGroup.map ι (vSL c)) =
        pinnedX TwistTag.E6.tag E (-e6HighestRoot) (ι c)
      rw [map_vSL, thetaSL2_vSL h2]
  rw [MonoidHom.range_eq_map, ← sl2_closure_upper_lower, MonoidHom.map_closure, Set.image_union,
    e1, e2]

theorem HSL_conj_uSL (a : Eˣ) (c : E) : HSL a * uSL c * (HSL a)⁻¹ = uSL ((a : E) ^ 2 * c) := by
  rw [mul_inv_eq_iff_eq_mul]
  ext i j
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
  fin_cases i <;> fin_cases j <;> simp [HSL, uSL, Matrix.mul_apply, Fin.sum_univ_two]
  field_simp

theorem HSL_conj_vSL (a : Eˣ) (c : E) :
    HSL a * vSL c * (HSL a)⁻¹ = vSL (((a⁻¹ : Eˣ) : E) ^ 2 * c) := by
  rw [mul_inv_eq_iff_eq_mul]
  ext i j
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
  fin_cases i <;> fin_cases j <;> simp [HSL, vSL, Matrix.mul_apply, Fin.sum_univ_two]
  field_simp

theorem rootTorusSL2_conj_pinnedX
    (h2 : (2 : E) = 0) (a : Eˣ) (c : E) :
    rootTorusSL2 TwistTag.E6.tag E e6HighestRoot a * pinnedX TwistTag.E6.tag E e6HighestRoot c *
        (rootTorusSL2 TwistTag.E6.tag E e6HighestRoot a)⁻¹ =
      pinnedX TwistTag.E6.tag E e6HighestRoot ((a : E) ^ 2 * c) := by
  rw [← thetaSL2_uSL h2, ← thetaSL2_uSL h2, rootTorusSL2, ← map_inv, ← map_mul, ← map_mul,
    HSL_conj_uSL]

theorem rootTorusSL2_conj_pinnedX_neg
    (h2 : (2 : E) = 0) (a : Eˣ) (c : E) :
    rootTorusSL2 TwistTag.E6.tag E e6HighestRoot a *
        pinnedX TwistTag.E6.tag E (-e6HighestRoot) c *
        (rootTorusSL2 TwistTag.E6.tag E e6HighestRoot a)⁻¹ =
      pinnedX TwistTag.E6.tag E (-e6HighestRoot) (((a⁻¹ : Eˣ) : E) ^ 2 * c) := by
  rw [← thetaSL2_vSL h2, ← thetaSL2_vSL h2, rootTorusSL2, ← map_inv, ← map_mul, ← map_mul,
    HSL_conj_vSL]

theorem rootTorusSL2_e6HighestRoot
    (a : Eˣ) :
    rootTorusSL2 TwistTag.E6.tag E e6HighestRoot a =
      rootDiagUnit TwistTag.E6.tag (Pi.mulSingle (e6Idx 1) a) := by
  obtain ⟨-, hdH, -, -, hv, hH, -, -⟩ :=
    exceptional_Lang_root_rank_one_torus_transport TwistTag.E6.tag E isRoot_e6HighestRoot
  obtain ⟨b, hb, -⟩ := hH _ (hdH a)
  rw [hb]
  congr 1
  funext j
  have h1 := (hv a).2 (Pi.single j 1) (isRoot_single _ j)
  rw [hb] at h1
  change rootDiag b (rootVec _ E _) = _ at h1
  rw [rootDiag_rootVec b (isRoot_single _ j)] at h1
  have hne : rootVec TwistTag.E6.tag E (Pi.single j 1 : Fin TwistTag.E6.tag.rank → ℤ) ≠ 0 := by
    rw [rootVec_eq_single (isRoot_single _ j)]
    exact Finsupp.single_ne_zero.2 one_ne_zero
  have h3 := smul_left_injective E hne h1
  have e : rootChar b (Pi.single j 1) = b j := by
    have := rootChar_nsmul_single b j 1
    rwa [one_nsmul, pow_one] at this
  have hexp : 2 * iform e6HighestRoot (Pi.single j 1) / iform e6HighestRoot e6HighestRoot =
      (Pi.single j 1 : Fin TwistTag.E6.tag.rank → ℤ) (e6Idx 1) := by
    rw [iform_e6HighestRoot, iform_e6HighestRoot, show e6HighestRoot (e6Idx 1) = 2 from rfl,
      Int.mul_ediv_cancel_left _ two_ne_zero]
  rw [e, hexp] at h3
  refine Units.ext ?_
  rw [h3]
  by_cases hj : j = e6Idx 1
  · subst hj
    simp
  · rw [Pi.single_eq_of_ne' hj, Pi.mulSingle_eq_of_ne hj, zpow_zero]

theorem single_theta_facts : ∀ i : Fin 6, e6Idx i ≠ e6Idx 1 → ∀ s t : Bool,
    let α : Fin TwistTag.E6.tag.rank → ℤ := if s then Pi.single (e6Idx i) 1 else
      -Pi.single (e6Idx i) 1
    let β : Fin TwistTag.E6.tag.rank → ℤ := if t then e6HighestRoot else -e6HighestRoot
    α ≠ β ∧ α ≠ -β ∧ α + β ∉ rootFinset TwistTag.E6.tag := by
  decide +kernel

theorem commute_pinnedX_of_not_isRoot
    {α β : Fin TwistTag.E6.tag.rank → ℤ}
    (hα : IsRoot TwistTag.E6.tag α) (hβ : IsRoot TwistTag.E6.tag β) (hne : α ≠ β)
    (hne' : α ≠ -β) (h : ¬IsRoot TwistTag.E6.tag (α + β)) (c d : E) :
    Commute (pinnedX TwistTag.E6.tag E α c) (pinnedX TwistTag.E6.tag E β d) :=
  (simply_laced_root_commutator_unit TwistTag.E6.tag (Or.inr (Or.inl rfl)) hα hβ hne hne').2 h E _
    (mem_rootSubgroup.2 ⟨c, rfl⟩) _ (mem_rootSubgroup.2 ⟨d, rfl⟩)

theorem commute_simple_theta
    {i : Fin TwistTag.E6.tag.rank} (hi : i ∈ setA) (s t : Bool)
    (c d : E) :
    Commute (pinnedX TwistTag.E6.tag E
        (if s then Pi.single i 1 else -Pi.single i 1) c)
      (pinnedX TwistTag.E6.tag E (if t then e6HighestRoot else -e6HighestRoot) d) := by
  obtain ⟨h1, h2, h3⟩ := single_theta_facts i hi s t
  have hα : IsRoot TwistTag.E6.tag (if s then Pi.single i 1 else -Pi.single i 1) := by
    cases s
    · exact isRoot_neg_single _ i
    · exact isRoot_single _ i
  have hβ : IsRoot TwistTag.E6.tag (if t then e6HighestRoot else -e6HighestRoot) := by
    cases t
    · exact IsRoot.neg isRoot_e6HighestRoot
    · exact isRoot_e6HighestRoot
  exact commute_pinnedX_of_not_isRoot hα hβ h1 h2 (fun h => h3 (mem_rootFinset.2 h)) c d

theorem subsystemGroup_le_centralizer_thetaSL2
    (h2 : (2 : E) = 0) :
    subsystemGroup TwistTag.E6.tag E setA ≤
      Subgroup.centralizer ((thetaSL2 E).range : Set (ModGL TwistTag.E6.tag E)) := by
  rw [Subgroup.le_centralizer_iff, range_thetaSL2 h2, Subgroup.closure_le]
  intro g hg
  have hle : subsystemGroup TwistTag.E6.tag E setA ≤ Subgroup.centralizer {g} := by
    rw [subsystemGroup, Subgroup.closure_le]
    rintro _ ⟨i, hi, c, rfl | rfl⟩ <;> rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
    · rw [← pinnedX_single]
      rcases hg with ⟨d, rfl⟩ | ⟨d, rfl⟩
      · exact (commute_simple_theta hi true true c d).eq
      · exact (commute_simple_theta hi true false c d).eq
    · rw [← pinnedX_neg_single]
      rcases hg with ⟨d, rfl⟩ | ⟨d, rfl⟩
      · exact (commute_simple_theta hi false true c d).eq
      · exact (commute_simple_theta hi false false c d).eq
  exact Subgroup.mem_centralizer_iff.2 fun h hh => Subgroup.mem_centralizer_singleton_iff.1 (hle hh)

theorem diagramMap_conj_pinnedX_theta
    (h2 : (2 : E) = 0) (t : Bool) (c : E) :
    diagramMap TwistTag.E6 E *
        pinnedX TwistTag.E6.tag E (if t then e6HighestRoot else -e6HighestRoot) c *
        (diagramMap TwistTag.E6 E)⁻¹ =
      pinnedX TwistTag.E6.tag E (if t then e6HighestRoot else -e6HighestRoot) c := by
  have hβ : IsRoot TwistTag.E6.tag (if t then e6HighestRoot else -e6HighestRoot) := by
    cases t
    · exact IsRoot.neg isRoot_e6HighestRoot
    · exact isRoot_e6HighestRoot
  rw [← twistHom_id_eq, twistHom_id_pinnedX h2 hβ]
  cases t
  · simp only [Bool.false_eq_true, ite_false]
    rw [permLattice_neg, permLattice_e6HighestRoot]
  · simp only [ite_true]
    rw [permLattice_e6HighestRoot]

theorem diagramMap_conj_thetaSL2
    (h2 : (2 : E) = 0) (B : SL2 E) :
    diagramMap TwistTag.E6 E * thetaSL2 E B * (diagramMap TwistTag.E6 E)⁻¹ = thetaSL2 E B := by
  have h := MonoidHom.eq_of_eqOn_dense sl2_closure_upper_lower
    (f := (MulAut.conj (diagramMap TwistTag.E6 E)).toMonoidHom.comp (thetaSL2 E))
    (g := thetaSL2 E) (by
      rintro _ (⟨c, rfl⟩ | ⟨c, rfl⟩)
      · change diagramMap TwistTag.E6 E * thetaSL2 E (uSL c) * (diagramMap TwistTag.E6 E)⁻¹ =
          thetaSL2 E (uSL c)
        rw [thetaSL2_uSL h2]
        exact diagramMap_conj_pinnedX_theta h2 true c
      · change diagramMap TwistTag.E6 E * thetaSL2 E (vSL c) * (diagramMap TwistTag.E6 E)⁻¹ =
          thetaSL2 E (vSL c)
        rw [thetaSL2_vSL h2]
        exact diagramMap_conj_pinnedX_theta h2 false c)
  exact DFunLike.congr_fun h B

theorem units_map_entrywiseHom_pinnedX'
    (σ : E →+* E) (α : Fin TwistTag.E6.tag.rank → ℤ) (c : E) :
    Units.map (entrywiseHom σ) (pinnedX TwistTag.E6.tag E α c) =
      pinnedX TwistTag.E6.tag E α (σ c) :=
  Units.ext (entrywise_pinnedX σ α c)

theorem twistHom_thetaSL2
    (h2 : (2 : E) = 0) (σ : E →+* E) (B : SL2 E) :
    twistHom TwistTag.E6 E σ (thetaSL2 E B) =
      thetaSL2 E (Matrix.SpecialLinearGroup.map σ B) := by
  have h := MonoidHom.eq_of_eqOn_dense sl2_closure_upper_lower
    (f := (twistHom TwistTag.E6 E σ).comp (thetaSL2 E))
    (g := (thetaSL2 E).comp (Matrix.SpecialLinearGroup.map σ)) (by
      rintro _ (⟨c, rfl⟩ | ⟨c, rfl⟩)
      · change twistHom TwistTag.E6 E σ (thetaSL2 E (uSL c)) =
          thetaSL2 E (Matrix.SpecialLinearGroup.map σ (uSL c))
        rw [map_uSL, thetaSL2_uSL h2, thetaSL2_uSL h2, twistHom_apply,
          units_map_entrywiseHom_pinnedX']
        exact diagramMap_conj_pinnedX_theta h2 true (σ c)
      · change twistHom TwistTag.E6 E σ (thetaSL2 E (vSL c)) =
          thetaSL2 E (Matrix.SpecialLinearGroup.map σ (vSL c))
        rw [map_vSL, thetaSL2_vSL h2, thetaSL2_vSL h2, twistHom_apply,
          units_map_entrywiseHom_pinnedX']
        exact diagramMap_conj_pinnedX_theta h2 false (σ c))
  exact DFunLike.congr_fun h B

variable (E) in
@[expose] def thetaTorusHom : Eˣ →* ModGL TwistTag.E6.tag E :=
  (rootDiagUnitHom TwistTag.E6.tag E).comp
    (MonoidHom.mulSingle (fun _ : Fin TwistTag.E6.tag.rank => Eˣ) (e6Idx 1))

theorem thetaTorusHom_apply
    (a : Eˣ) :
    thetaTorusHom E a = rootTorusSL2 TwistTag.E6.tag E e6HighestRoot a := by
  rw [rootTorusSL2_e6HighestRoot]
  rfl

theorem thetaTorusHom_eq_thetaSL2
    (a : Eˣ) : thetaTorusHom E a = thetaSL2 E (HSL a) :=
  thetaTorusHom_apply a

theorem thetaTorusHom_injective
    (h2 : (2 : E) = 0) : Function.Injective (thetaTorusHom E) := by
  intro a b h
  rw [thetaTorusHom_eq_thetaSL2, thetaTorusHom_eq_thetaSL2] at h
  have h' := congrArg (fun B : SL2 E => (B : Matrix (Fin 2) (Fin 2) E) 0 0)
    (thetaSL2_injective h2 h)
  exact Units.ext (by simpa [HSL] using h')

@[expose] def thetaTorus {k : Type} [Field k] (ι : k →+* E) : Subgroup (ModGL TwistTag.E6.tag E) :=
  ((thetaTorusHom E).comp (Units.map ι.toMonoidHom)).range

theorem mem_thetaTorus
    {k : Type} [Field k] (ι : k →+* E) {g : ModGL TwistTag.E6.tag E} :
    g ∈ thetaTorus ι ↔
      ∃ a : kˣ, rootTorusSL2 TwistTag.E6.tag E e6HighestRoot (Units.map ι.toMonoidHom a) = g := by
  simp only [thetaTorus, MonoidHom.mem_range, MonoidHom.comp_apply, thetaTorusHom_apply]

theorem thetaTorus_le_range_thetaSL2
    {k : Type} [Field k] (ι : k →+* E) :
    thetaTorus ι ≤ (thetaSL2 E).range := by
  rintro _ ⟨a, rfl⟩
  exact ⟨HSL _, (thetaTorusHom_eq_thetaSL2 _).symm⟩

theorem map_HSL {k : Type} [Field k] (ι : k →+* E) (a : kˣ) :
    Matrix.SpecialLinearGroup.map ι (HSL a) = HSL (Units.map ι.toMonoidHom a) := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.map_apply_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [HSL]

theorem thetaTorus_le_range_comp_map
    {k : Type} [Field k] (ι : k →+* E) :
    thetaTorus ι ≤ ((thetaSL2 E).comp (Matrix.SpecialLinearGroup.map ι)).range := by
  rintro _ ⟨a, rfl⟩
  refine ⟨HSL a, ?_⟩
  rw [MonoidHom.comp_apply, MonoidHom.comp_apply, thetaTorusHom_eq_thetaSL2, map_HSL]

theorem thetaTorus_le_torusGroup
    {k : Type} [Field k] (ι : k →+* E) :
    thetaTorus ι ≤ torusGroup TwistTag.E6.tag E := by
  rintro _ ⟨a, rfl⟩
  rw [MonoidHom.comp_apply, thetaTorusHom_apply]
  exact (exceptional_Lang_root_rank_one_torus_transport TwistTag.E6.tag E
    isRoot_e6HighestRoot).2.1 _

theorem list_prod_torusElt
    (c : Eˣ) (l : List (Fin TwistTag.E6.tag.rank × ℤ)) :
    (l.map fun p => torusElt TwistTag.E6.tag E p.1 (c ^ p.2)).prod =
      rootDiagUnit TwistTag.E6.tag
        (fun j => c ^ (l.map fun p => p.2 * TwistTag.E6.tag.cartan p.1 j).sum) := by
  induction l with
  | nil =>
    rw [List.map_nil, List.prod_nil]
    exact rootDiagUnit_one.symm.trans (congrArg _ (funext fun j => by simp))
  | cons p l ih =>
    rw [List.map_cons, List.prod_cons, ih, torusElt_eq_rootDiagUnit, ← rootDiagUnit_mul]
    congr 1
    funext j
    simp only [Pi.mul_apply, List.map_cons, List.sum_cons, zpow_add, zpow_mul]

@[expose] def thetaTail : List (Fin TwistTag.E6.tag.rank × ℤ) :=
  [(e6Idx 0, 1), (e6Idx 2, 2), (e6Idx 3, 3), (e6Idx 4, 2), (e6Idx 5, 1)]

theorem thetaCoroot_sum : ∀ j : Fin 6,
    (((e6Idx 1, 2) :: thetaTail).map fun p => p.2 * TwistTag.E6.tag.cartan p.1 (e6Idx j)).sum =
      (Pi.single (e6Idx 1) 1 : Fin TwistTag.E6.tag.rank → ℤ) (e6Idx j) := by
  decide

theorem thetaTail_mem_setA : ∀ p ∈ thetaTail, p.1 ∈ setA := by
  simp only [setA, Set.mem_ofPred_eq]
  decide

theorem rootTorusSL2_eq_torusElt_mul
    (c : Eˣ) :
    rootTorusSL2 TwistTag.E6.tag E e6HighestRoot c =
      torusElt TwistTag.E6.tag E (e6Idx 1) (c ^ 2) *
        (thetaTail.map fun p => torusElt TwistTag.E6.tag E p.1 (c ^ p.2)).prod := by
  have h := list_prod_torusElt c ((e6Idx 1, 2) :: thetaTail)
  rw [List.map_cons, List.prod_cons] at h
  rw [show c ^ 2 = c ^ (2 : ℤ) from (zpow_natCast c 2).symm, h, rootTorusSL2_e6HighestRoot]
  congr 1
  funext j
  rw [thetaCoroot_sum j]
  by_cases hj : j = e6Idx 1
  · subst hj
    simp
  · rw [Pi.single_eq_of_ne hj, Pi.mulSingle_eq_of_ne hj, zpow_zero]

theorem tail_mem_subsystemGroup
    (c : Eˣ) :
    (thetaTail.map fun p => torusElt TwistTag.E6.tag E p.1 (c ^ p.2)).prod ∈
      subsystemGroup TwistTag.E6.tag E setA := by
  refine Subgroup.list_prod_mem _ fun g hg => ?_
  obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hg
  exact subsystemTorus_le_subsystemGroup
    (torusElt_mem_subsystemTorus (thetaTail_mem_setA p hp) _)

theorem exists_sq_eq_of_two [Finite E] (h2 : (2 : E) = 0) (u : Eˣ) : ∃ c : Eˣ, c ^ 2 = u := by
  have hinj : Function.Injective fun c : Eˣ => c ^ 2 := by
    intro x y hxy
    have h : ((x : E) - y) ^ 2 = 0 := by
      have e := congrArg (fun z : Eˣ => (z : E)) hxy
      simp only [Units.val_pow_eq_pow_val] at e
      linear_combination e + ((y : E) ^ 2 - (x : E) * y) * h2
    exact Units.ext (sub_eq_zero.1 ((pow_eq_zero_iff two_ne_zero).1 h))
  exact Finite.surjective_of_injective hinj u

theorem commute_of_mem_thetaTorus
    (h2 : (2 : E) = 0) {k : Type} [Field k] (ι : k →+* E)
    {l h : ModGL TwistTag.E6.tag E} (hl : l ∈ subsystemGroup TwistTag.E6.tag E setA)
    (hh : h ∈ thetaTorus ι) : l * h = h * l :=
  (Subgroup.mem_centralizer_iff.1 (subsystemGroup_le_centralizer_thetaSL2 h2 hl) h
    (thetaTorus_le_range_thetaSL2 ι hh)).symm

theorem subsystemGroup_inf_thetaTorus
    (h2 : (2 : E) = 0) {k : Type} [Field k] (ι : k →+* E) :
    subsystemGroup TwistTag.E6.tag E setA ⊓ thetaTorus ι = ⊥ := by
  refine eq_bot_iff.2 fun g hg => ?_
  obtain ⟨hgL, hgH⟩ := Subgroup.mem_inf.1 hg
  obtain ⟨a, rfl⟩ := hgH
  have hc := Subgroup.mem_centralizer_iff.1 (subsystemGroup_le_centralizer_thetaSL2 h2 hgL)
    (pinnedX TwistTag.E6.tag E e6HighestRoot 1) ⟨uSL 1, thetaSL2_uSL h2 1⟩
  have h1 := rootTorusSL2_conj_pinnedX h2 (Units.map ι.toMonoidHom a) 1
  rw [← thetaTorusHom_apply] at h1
  rw [MonoidHom.comp_apply] at hc
  have h3 : pinnedX TwistTag.E6.tag E e6HighestRoot
      (((Units.map ι.toMonoidHom a : Eˣ) : E) ^ 2 * 1) =
        pinnedX TwistTag.E6.tag E e6HighestRoot 1 := by
    rw [← h1, ← hc, mul_inv_cancel_right]
  have h4 := pinnedX_injective (τ := TwistTag.E6.tag) (R := E) e6HighestRoot h3
  rw [mul_one] at h4
  have hb1 : Units.map ι.toMonoidHom a = 1 :=
    Units.ext (eq_one_of_mul_self_eq_one_of_two_eq_zero h2 (by rw [← sq]; exact h4))
  rw [Subgroup.mem_bot, MonoidHom.comp_apply, hb1, map_one]

theorem torusGroup_le_subsystemGroup_sup
    (hsq : ∀ u : Eˣ, ∃ c : Eˣ, c ^ 2 = u) :
    torusGroup TwistTag.E6.tag E ≤
      subsystemGroup TwistTag.E6.tag E setA ⊔ thetaTorus (RingHom.id E) := by
  rw [torusGroup, Subgroup.closure_le]
  rintro _ ⟨⟨i, u⟩, rfl⟩
  by_cases hi : i = e6Idx 1
  · subst hi
    obtain ⟨c, rfl⟩ := hsq u
    have e : torusElt TwistTag.E6.tag E (e6Idx 1) (c ^ 2) =
        thetaTorusHom E c *
          ((thetaTail.map fun p => torusElt TwistTag.E6.tag E p.1 (c ^ p.2)).prod)⁻¹ := by
      rw [thetaTorusHom_apply, rootTorusSL2_eq_torusElt_mul, mul_inv_cancel_right]
    change torusElt TwistTag.E6.tag E (e6Idx 1) (c ^ 2) ∈ _
    rw [e]
    exact mul_mem (Subgroup.mem_sup_right ⟨c, rfl⟩)
      (Subgroup.mem_sup_left (inv_mem (tail_mem_subsystemGroup c)))
  · exact Subgroup.mem_sup_left
      (subsystemTorus_le_subsystemGroup (torusElt_mem_subsystemTorus hi u))

theorem existsUnique_mul_of_commute {G : Type*} [Group G] {A B : Subgroup G} (hAB : A ⊓ B = ⊥)
    (hcomm : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) :
    ∀ g ∈ A ⊔ B, ∃! p : G × G, p.1 ∈ A ∧ p.2 ∈ B ∧ g = p.1 * p.2 := by
  have hBN : B ≤ Subgroup.normalizer (A : Set G) := fun b hb =>
    Subgroup.mem_normalizer_iff.2 fun a => by
      constructor
      · intro ha
        rw [← hcomm a ha b hb, mul_inv_cancel_right]
        exact ha
      · intro ha
        have e := hcomm _ ha b hb
        have : a = b * a * b⁻¹ := by
          calc a = b⁻¹ * (b * a * b⁻¹ * b) := by group
            _ = b⁻¹ * (b * (b * a * b⁻¹)) := by rw [e]
            _ = b * a * b⁻¹ := by group
        rw [this]
        exact ha
  intro g hg
  have hg' : g ∈ (A : Set G) * (B : Set G) := by
    rw [← Subgroup.coe_mul_of_right_le_normalizer_left _ _ hBN]
    exact hg
  obtain ⟨a, ha, b, hb, rfl⟩ := hg'
  refine ⟨(a, b), ⟨ha, hb, rfl⟩, ?_⟩
  rintro ⟨a', b'⟩ ⟨ha', hb', h⟩
  have hmem : a⁻¹ * a' ∈ A ⊓ B := by
    refine Subgroup.mem_inf.2 ⟨mul_mem (inv_mem ha) ha', ?_⟩
    have : a⁻¹ * a' = b * b'⁻¹ := by
      calc a⁻¹ * a' = a⁻¹ * (a' * b') * b'⁻¹ := by group
        _ = a⁻¹ * (a * b) * b'⁻¹ := by rw [← h]
        _ = b * b'⁻¹ := by group
    rw [this]
    exact mul_mem hb (inv_mem hb')
  rw [hAB, Subgroup.mem_bot, inv_mul_eq_one] at hmem
  subst hmem
  have : b = b' := mul_left_cancel h
  subst this
  rfl

theorem parabolicLevi_eq_subsystemGroup_sup
    (hsq : ∀ u : Eˣ, ∃ c : Eˣ, c ^ 2 = u) :
    parabolicLevi TwistTag.E6.tag E setA =
      subsystemGroup TwistTag.E6.tag E setA ⊔ thetaTorus (RingHom.id E) := by
  refine le_antisymm (sup_le (torusGroup_le_subsystemGroup_sup hsq) le_sup_left)
    (sup_le le_sup_right ((thetaTorus_le_torusGroup _).trans le_sup_left))

@[expose] def thetaRootGroup
    {k : Type} [Field k] (ι : k →+* E) :
    Subgroup (ModGL TwistTag.E6.tag E) :=
  Subgroup.closure (Set.range fun c : k => pinnedX TwistTag.E6.tag E e6HighestRoot (ι c))

@[expose] def thetaNegRootGroup
    {k : Type} [Field k] (ι : k →+* E) :
    Subgroup (ModGL TwistTag.E6.tag E) :=
  Subgroup.closure (Set.range fun c : k => pinnedX TwistTag.E6.tag E (-e6HighestRoot) (ι c))

@[expose] def thetaRankOneGroup
    {k : Type} [Field k] (ι : k →+* E) :
    Subgroup (ModGL TwistTag.E6.tag E) :=
  thetaRootGroup ι ⊔ thetaNegRootGroup ι

theorem mem_closure_range_pinnedX
    {k : Type} [Field k] (ι : k →+* E)
    (β : Fin TwistTag.E6.tag.rank → ℤ) {g : ModGL TwistTag.E6.tag E} :
    g ∈ Subgroup.closure (Set.range fun c : k => pinnedX TwistTag.E6.tag E β (ι c)) ↔
      ∃ c : k, pinnedX TwistTag.E6.tag E β (ι c) = g := by
  constructor
  · intro hg
    induction hg using Subgroup.closure_induction with
    | mem x hx => exact hx
    | one => exact ⟨0, by rw [map_zero, pinnedX_zero]⟩
    | mul x y _ _ hx hy =>
      obtain ⟨c, rfl⟩ := hx
      obtain ⟨d, rfl⟩ := hy
      exact ⟨c + d, by rw [map_add, pinnedX_add]⟩
    | inv x _ hx =>
      obtain ⟨c, rfl⟩ := hx
      exact ⟨-c, by rw [map_neg, ← pinnedX_neg]⟩
  · rintro ⟨c, rfl⟩
    exact Subgroup.subset_closure ⟨c, rfl⟩

theorem mem_thetaRootGroup
    {k : Type} [Field k] (ι : k →+* E) {g : ModGL TwistTag.E6.tag E} :
    g ∈ thetaRootGroup ι ↔ ∃ c : k, pinnedX TwistTag.E6.tag E e6HighestRoot (ι c) = g :=
  mem_closure_range_pinnedX ι _

theorem mem_thetaNegRootGroup
    {k : Type} [Field k] (ι : k →+* E) {g : ModGL TwistTag.E6.tag E} :
    g ∈ thetaNegRootGroup ι ↔ ∃ c : k, pinnedX TwistTag.E6.tag E (-e6HighestRoot) (ι c) = g :=
  mem_closure_range_pinnedX ι _

theorem thetaRankOneGroup_eq_range
    (h2 : (2 : E) = 0) {k : Type} [Field k] (ι : k →+* E) :
    thetaRankOneGroup ι = ((thetaSL2 E).comp (Matrix.SpecialLinearGroup.map ι)).range := by
  rw [range_thetaSL2_comp_map ι h2, thetaRankOneGroup, thetaRootGroup, thetaNegRootGroup,
    Subgroup.closure_union]

theorem injective_thetaSL2_comp_map
    (h2 : (2 : E) = 0) {k : Type} [Field k] (ι : k →+* E) :
    Function.Injective ((thetaSL2 E).comp (Matrix.SpecialLinearGroup.map ι)) := by
  refine (thetaSL2_injective h2).comp fun A B h => Subtype.ext ?_
  have h' := congrArg (fun C : SL2 E => (C : Matrix (Fin 2) (Fin 2) E)) h
  simp only [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply] at h'
  exact Matrix.map_injective ι.injective h'

theorem thetaSL2_comp_map_HSL
    {k : Type} [Field k] (ι : k →+* E) (a : kˣ) :
    (thetaSL2 E).comp (Matrix.SpecialLinearGroup.map ι) (HSL a) =
      rootTorusSL2 TwistTag.E6.tag E e6HighestRoot (Units.map ι.toMonoidHom a) := by
  rw [MonoidHom.comp_apply, map_HSL]
  rfl

theorem thetaTorus_le_thetaRankOneGroup
    (h2 : (2 : E) = 0) {k : Type} [Field k] (ι : k →+* E) :
    thetaTorus ι ≤ thetaRankOneGroup ι := by
  rw [thetaRankOneGroup_eq_range h2]
  exact thetaTorus_le_range_comp_map ι

theorem thetaRankOneGroup_le_range
    (h2 : (2 : E) = 0) {k : Type} [Field k] (ι : k →+* E) :
    thetaRankOneGroup ι ≤ (thetaSL2 E).range := by
  rw [thetaRankOneGroup_eq_range h2]
  rintro _ ⟨B, rfl⟩
  exact ⟨_, rfl⟩

end CFSG.LieType.Chevalley.E6GraphLevi
