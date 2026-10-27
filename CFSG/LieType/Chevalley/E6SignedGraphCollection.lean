module

public import CFSG.LieType.Chevalley.E6SignedGraphCollectionData

public noncomputable section

namespace CFSG.LieType.Chevalley.E6SignedGraph

open CFSG.Blueprint.Chevalley CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.Steinberg.Adjoint

variable (K : Type) [Field K]

@[expose] def posFixed
    : Subgroup (ModGL TwistTag.E6.tag K) :=
  posUnipotent TwistTag.E6.tag K ⊓ fixedGroup K

@[expose] def negFixed
    : Subgroup (ModGL TwistTag.E6.tag K) :=
  negUnipotent TwistTag.E6.tag K ⊓ fixedGroup K

@[expose] def rootGenerated
    : Subgroup (ModGL TwistTag.E6.tag K) :=
  posFixed K ⊔ negFixed K

@[expose] def torusFixed
    : Subgroup (ModGL TwistTag.E6.tag K) :=
  torusGroup TwistTag.E6.tag K ⊓ fixedGroup K

variable {K}

theorem finite_diagramRootOrbits
    : TwistTag.E6.diagramRootOrbits.Finite :=
  ((finite_setOf_isRoot TwistTag.E6.tag).image TwistTag.E6.diagramOrbit).subset
    fun _ ⟨α, hα, hαP⟩ => ⟨α, hα, hαP⟩

theorem fixed_orbit_list_prod
    (hK : ringChar K ≠ 2) {Φσ : Set E6Vec}
    {Uσ : Subgroup (ModGL TwistTag.E6.tag K)}
    (hU : ∀ P : Finset E6Vec, (P : Set E6Vec) ⊆ Φσ →
      rootSpan TwistTag.E6.tag K (P : Set E6Vec) ≤ Uσ)
    (hgrouped : ∀ {k : ℕ} (F : Fin k → Finset E6Vec), Function.Injective F →
      (∀ P, P ∈ Set.range F ↔ P ∈ TwistTag.E6.diagramRootOrbits ∧ (P : Set E6Vec) ⊆ Φσ) →
      (∀ u u' : Fin k → ModGL TwistTag.E6.tag K,
        (∀ j, u j ∈ rootSpan TwistTag.E6.tag K (F j : Set E6Vec)) →
        (∀ j, u' j ∈ rootSpan TwistTag.E6.tag K (F j : Set E6Vec)) →
        (List.ofFn u).prod = (List.ofFn u').prod → u = u') ∧
      ∀ g ∈ Uσ, ∃ u : Fin k → ModGL TwistTag.E6.tag K,
        (∀ j, u j ∈ rootSpan TwistTag.E6.tag K (F j : Set E6Vec)) ∧ (List.ofFn u).prod = g)
    {m : ℕ} (O : Fin m → Finset E6Vec) (hO : Function.Injective O)
    (hrange : Set.range O = {P | P ∈ orbits ∧ (P : Set E6Vec) ⊆ Φσ}) :
    Function.Injective (fun g : (i : Fin m) → ↥(orbitFixed K (O i)) =>
        (List.ofFn fun i => (g i : ModGL TwistTag.E6.tag K)).prod) ∧
      Set.range (fun g : (i : Fin m) → ↥(orbitFixed K (O i)) =>
        (List.ofFn fun i => (g i : ModGL TwistTag.E6.tag K)).prod) =
        ((Uσ ⊓ fixedGroup K : Subgroup (ModGL TwistTag.E6.tag K)) :
          Set (ModGL TwistTag.E6.tag K)) := by
  have hfin : {P : Finset E6Vec | P ∈ TwistTag.E6.diagramRootOrbits ∧ P ∉ orbits ∧
      (P : Set E6Vec) ⊆ Φσ}.Finite := finite_diagramRootOrbits.subset fun _ hP => hP.1
  obtain ⟨e, E, hE⟩ := hfin.fin_embedding
  have hEmem : ∀ j, E j ∈ TwistTag.E6.diagramRootOrbits ∧ E j ∉ orbits ∧
      (E j : Set E6Vec) ⊆ Φσ := fun j => by
    have h : E j ∈ Set.range E := Set.mem_range_self j
    rw [hE] at h
    exact h
  have hOmem : ∀ i, O i ∈ orbits ∧ (O i : Set E6Vec) ⊆ Φσ := fun i => by
    have h : O i ∈ Set.range O := Set.mem_range_self i
    rw [hrange] at h
    exact h
  set F := Fin.append O E with hFdef
  have hF : Function.Injective F := Fin.append_injective_iff.2
    ⟨hO, E.injective, fun i j h => (hEmem j).2.1 (h ▸ (hOmem i).1)⟩
  have hFmem : ∀ j, F j ∈ TwistTag.E6.diagramRootOrbits ∧ (F j : Set E6Vec) ⊆ Φσ := fun j => by
    induction j using Fin.addCases with
    | left i =>
      rw [hFdef, Fin.append_left]
      exact ⟨(hOmem i).1.1, (hOmem i).2⟩
    | right j =>
      rw [hFdef, Fin.append_right]
      exact ⟨(hEmem j).1, (hEmem j).2.2⟩
  have hFrange : ∀ P, P ∈ Set.range F ↔ P ∈ TwistTag.E6.diagramRootOrbits ∧
      (P : Set E6Vec) ⊆ Φσ := fun P => by
    refine ⟨fun ⟨j, hj⟩ => hj ▸ hFmem j, fun ⟨hP, hPσ⟩ => ?_⟩
    by_cases hΩ : P ∈ orbits
    · have h : P ∈ Set.range O := by
        rw [hrange]
        exact ⟨hΩ, hPσ⟩
      obtain ⟨i, rfl⟩ := h
      exact ⟨Fin.castAdd e i, by rw [hFdef, Fin.append_left]⟩
    · have h : P ∈ Set.range E := by
        rw [hE]
        exact ⟨hP, hΩ, hPσ⟩
      obtain ⟨j, rfl⟩ := h
      exact ⟨Fin.natAdd m j, by rw [hFdef, Fin.append_right]⟩
  obtain ⟨hinj, hsurj⟩ := hgrouped F hF hFrange
  exact fixed_list_prod (fun j => rootSpan TwistTag.E6.tag K (F j : Set E6Vec))
    (fun i => rootSpan TwistTag.E6.tag K (O i : Set E6Vec))
    (fun i => by simp only [hFdef, Fin.append_left]) Uσ
    (fun j => rootSpan_le_adjointGroup K _)
    (fun j x hx => twistA_conj_mem_rootSpan (hFmem j).1 hx) (fun j => hU _ (hFmem j).2)
    (fun j => by
      simp only [hFdef, Fin.append_right]
      exact orbitFixed_eq_bot_of_not_mem hK (hEmem j).1 (hEmem j).2.1)
    hinj hsurj

theorem posRoots_iff
    {O : Finset E6Vec} :
    O ∈ {P : Finset E6Vec | P ∈ orbits ∧ 0 < height (orbitVec P)} ↔
      O ∈ {P : Finset E6Vec | P ∈ orbits ∧
        (P : Set E6Vec) ⊆ {α | IsRoot TwistTag.E6.tag α ∧ 0 < height α}} :=
  ⟨fun ⟨hO, h⟩ => ⟨hO, (height_orbitVec_pos_iff hO).1 h⟩,
    fun ⟨hO, h⟩ => ⟨hO, (height_orbitVec_pos_iff hO).2 h⟩⟩

theorem negRoots_iff
    {O : Finset E6Vec} :
    O ∈ {P : Finset E6Vec | P ∈ orbits ∧ height (orbitVec P) < 0} ↔
      O ∈ {P : Finset E6Vec | P ∈ orbits ∧
        (P : Set E6Vec) ⊆ {α | IsRoot TwistTag.E6.tag α ∧ height α < 0}} :=
  ⟨fun ⟨hO, h⟩ => ⟨hO, (height_orbitVec_neg_iff hO).1 h⟩,
    fun ⟨hO, h⟩ => ⟨hO, (height_orbitVec_neg_iff hO).2 h⟩⟩

theorem posFixed_list_prod
    (hK : ringChar K ≠ 2) {m : ℕ} (O : Fin m → Finset E6Vec)
    (hO : Function.Injective O)
    (hrange : Set.range O = {P | P ∈ orbits ∧ 0 < height (orbitVec P)}) :
    Function.Injective (fun g : (i : Fin m) → ↥(orbitFixed K (O i)) =>
        (List.ofFn fun i => (g i : ModGL TwistTag.E6.tag K)).prod) ∧
      Set.range (fun g : (i : Fin m) → ↥(orbitFixed K (O i)) =>
        (List.ofFn fun i => (g i : ModGL TwistTag.E6.tag K)).prod) =
        (posFixed K : Set (ModGL TwistTag.E6.tag K)) :=
  fixed_orbit_list_prod hK (fun _ hP => rootSpan_le_posUnipotent hP)
    (fun F hF hrange => grouped_pos F hF hrange) O hO
    (by rw [hrange]; ext P; exact posRoots_iff)

theorem negFixed_list_prod
    (hK : ringChar K ≠ 2) {m : ℕ} (O : Fin m → Finset E6Vec)
    (hO : Function.Injective O)
    (hrange : Set.range O = {P | P ∈ orbits ∧ height (orbitVec P) < 0}) :
    Function.Injective (fun g : (i : Fin m) → ↥(orbitFixed K (O i)) =>
        (List.ofFn fun i => (g i : ModGL TwistTag.E6.tag K)).prod) ∧
      Set.range (fun g : (i : Fin m) → ↥(orbitFixed K (O i)) =>
        (List.ofFn fun i => (g i : ModGL TwistTag.E6.tag K)).prod) =
        (negFixed K : Set (ModGL TwistTag.E6.tag K)) :=
  fixed_orbit_list_prod hK (fun _ hP => rootSpan_le_negUnipotent hP)
    (fun F hF hrange => grouped_neg F hF hrange) O hO
    (by rw [hrange]; ext P; exact negRoots_iff)

theorem orbitFixed_le_rootGenerated
    {P : Finset E6Vec}
    (hP : (∀ α ∈ P, IsRoot TwistTag.E6.tag α ∧ 0 < height α) ∨
      ∀ α ∈ P, IsRoot TwistTag.E6.tag α ∧ height α < 0) :
    orbitFixed K P ≤ rootGenerated K := by
  rcases hP with hP | hP
  · exact le_sup_of_le_left (inf_le_inf_right _ (rootSpan_le_posUnipotent fun α hα => hP α hα))
  · exact le_sup_of_le_right (inf_le_inf_right _ (rootSpan_le_negUnipotent fun α hα => hP α hα))

theorem exists_ordering {X : Set (Finset E6Vec)} (hX : X.Finite) :
    ∃ (m : ℕ) (O : Fin m → Finset E6Vec), Function.Injective O ∧ Set.range O = X := by
  obtain ⟨m, O, hO⟩ := hX.fin_embedding
  exact ⟨m, O, O.injective, hO⟩

theorem rootGenerated_eq_iSup
    (hK : ringChar K ≠ 2) :
    rootGenerated K = ⨆ O ∈ orbits, orbitFixed K O := by
  have hgen : ∀ {m : ℕ} (O : Fin m → Finset E6Vec), (∀ i, O i ∈ orbits) →
      ∀ g : (i : Fin m) → ↥(orbitFixed K (O i)),
        (List.ofFn fun i => (g i : ModGL TwistTag.E6.tag K)).prod ∈
          ⨆ O ∈ orbits, orbitFixed K O := fun O hO g => by
    refine Subgroup.list_prod_mem _ fun y hy => ?_
    obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hy
    exact Subgroup.mem_iSup_of_mem (O i) (Subgroup.mem_iSup_of_mem (hO i) (g i).2)
  refine le_antisymm (sup_le (fun x hx => ?_) (fun x hx => ?_))
    (iSup₂_le fun O hO => orbitFixed_le_rootGenerated (diagramRootOrbits_sign hO.1))
  · obtain ⟨m, O, hO, hrange⟩ := exists_ordering (X := {P | P ∈ orbits ∧ 0 < height (orbitVec P)})
      (finite_diagramRootOrbits.subset fun _ hP => hP.1.1)
    have hx' : x ∈ Set.range (fun g : (i : Fin m) → ↥(orbitFixed K (O i)) =>
        (List.ofFn fun i => (g i : ModGL TwistTag.E6.tag K)).prod) := by
      rw [(posFixed_list_prod hK O hO hrange).2]
      exact hx
    obtain ⟨g, rfl⟩ := hx'
    refine hgen O (fun i => ?_) g
    have h : O i ∈ Set.range O := Set.mem_range_self i
    rw [hrange] at h
    exact h.1
  · obtain ⟨m, O, hO, hrange⟩ := exists_ordering (X := {P | P ∈ orbits ∧ height (orbitVec P) < 0})
      (finite_diagramRootOrbits.subset fun _ hP => hP.1.1)
    have hx' : x ∈ Set.range (fun g : (i : Fin m) → ↥(orbitFixed K (O i)) =>
        (List.ofFn fun i => (g i : ModGL TwistTag.E6.tag K)).prod) := by
      rw [(negFixed_list_prod hK O hO hrange).2]
      exact hx
    obtain ⟨g, rfl⟩ := hx'
    refine hgen O (fun i => ?_) g
    have h : O i ∈ Set.range O := Set.mem_range_self i
    rw [hrange] at h
    exact h.1

theorem range_orbitSL2_le_rootGenerated
    {w : WeylGroup TwistTag.E6.tag}
    (hw : w ∈ relWeylTwist TwistTag.E6) {a : Fin TwistTag.E6.foldedTag.rank}
    (hO : orbitImage w a ∈ orbits) : (orbitSL2 K w a).range ≤ rootGenerated K := by
  rw [range_orbitSL2 hw (orbitSign_eq_one_of_mem_orbits hO)]
  exact sup_le (orbitFixed_le_rootGenerated (orbitImage_sign hw a))
    (orbitFixed_le_rootGenerated (neg_orbitImage_sign hw a))

theorem isNilpotent_posFixed
    : Group.IsNilpotent (posFixed K) := by
  have := (positive_root_height_series TwistTag.E6.tag K).2.2.2.2.1
  have hle : posFixed K ≤ posUnipotent TwistTag.E6.tag K := fun x hx => (Subgroup.mem_inf.1 hx).1
  refine Subgroup.isNilpotent_of_ker_le_center (Subgroup.inclusion hle) ?_
  rw [(MonoidHom.ker_eq_bot_iff _).2 (Subgroup.inclusion_injective _)]
  exact bot_le

theorem isNilpotent_negFixed
    : Group.IsNilpotent (negFixed K) := by
  have := isNilpotent_negUnipotent (K := K)
  have hle : negFixed K ≤ negUnipotent TwistTag.E6.tag K := fun x hx => (Subgroup.mem_inf.1 hx).1
  refine Subgroup.isNilpotent_of_ker_le_center (Subgroup.inclusion hle) ?_
  rw [(MonoidHom.ker_eq_bot_iff _).2 (Subgroup.inclusion_injective _)]
  exact bot_le

theorem torusFixed_mul_comm
    {g g' : ModGL TwistTag.E6.tag K} (hg : g ∈ torusFixed K)
    (hg' : g' ∈ torusFixed K) : g * g' = g' * g :=
  (triangular_borel_structure.{0, 0} TwistTag.E6.tag K).1 g (Subgroup.mem_inf.1 hg).1 g'
    (Subgroup.mem_inf.1 hg').1

theorem torusFixed_le_normalizer_posFixed :
    torusFixed K ≤ Subgroup.normalizer (posFixed K : Set (ModGL TwistTag.E6.tag K)) := by
  intro h hh
  obtain ⟨hH, hΓ⟩ := Subgroup.mem_inf.1 hh
  have hN := Subgroup.mem_normalizer_iff.1 (torusGroup_le_normalizer_posUnipotent hH)
  refine Subgroup.mem_normalizer_iff.2 fun x => ?_
  rw [posFixed, Subgroup.mem_inf, Subgroup.mem_inf]
  exact (hN x).and (conj_mem_fixedGroup_iff hΓ x)

theorem torusFixed_le_normalizer_negFixed :
    torusFixed K ≤ Subgroup.normalizer (negFixed K : Set (ModGL TwistTag.E6.tag K)) := by
  intro h hh
  obtain ⟨hH, hΓ⟩ := Subgroup.mem_inf.1 hh
  have hN := Subgroup.mem_normalizer_iff.1 (torusGroup_le_normalizer_negUnipotent hH)
  refine Subgroup.mem_normalizer_iff.2 fun x => ?_
  rw [negFixed, Subgroup.mem_inf, Subgroup.mem_inf]
  exact (hN x).and (conj_mem_fixedGroup_iff hΓ x)

theorem torusFixed_le_normalizer_rootGenerated :
    torusFixed K ≤ Subgroup.normalizer (rootGenerated K : Set (ModGL TwistTag.E6.tag K)) :=
  fun _ hh => mem_normalizer_sup_of_mem (torusFixed_le_normalizer_posFixed hh)
    (torusFixed_le_normalizer_negFixed hh)

theorem torusFixed_inf_posFixed
    : torusFixed K ⊓ posFixed K = ⊥ :=
  eq_bot_iff.2 fun x hx => by
    have h : x ∈ torusGroup TwistTag.E6.tag K ⊓ posUnipotent TwistTag.E6.tag K :=
      Subgroup.mem_inf.2 ⟨(Subgroup.mem_inf.1 (Subgroup.mem_inf.1 hx).1).1,
        (Subgroup.mem_inf.1 (Subgroup.mem_inf.1 hx).2).1⟩
    rwa [torusGroup_inf_posUnipotent] at h

theorem torusFixed_inf_negFixed
    : torusFixed K ⊓ negFixed K = ⊥ :=
  eq_bot_iff.2 fun x hx => by
    have h : x ∈ borelGroup TwistTag.E6.tag K ⊓ negUnipotent TwistTag.E6.tag K :=
      Subgroup.mem_inf.2 ⟨torusGroup_le_borelGroup (Subgroup.mem_inf.1 (Subgroup.mem_inf.1 hx).1).1,
        (Subgroup.mem_inf.1 (Subgroup.mem_inf.1 hx).2).1⟩
    rwa [borelGroup_inf_negUnipotent] at h

theorem ncard_posOrbits
    : {P | P ∈ orbits ∧ 0 < height (orbitVec P)}.ncard = 16 := by
  rw [← Set.InjOn.ncard_image (injOn_orbitVec.mono fun _ hP => hP.1), ← ncard_posVecs]
  congr 1
  ext v
  constructor
  · rintro ⟨P, ⟨hP, hpos⟩, rfl⟩
    exact ⟨⟨P, hP, rfl⟩, hpos⟩
  · rintro ⟨⟨P, hP, rfl⟩, hpos⟩
    exact ⟨P, ⟨hP, hpos⟩, rfl⟩

theorem ncard_negOrbits
    : {P | P ∈ orbits ∧ height (orbitVec P) < 0}.ncard = 16 := by
  rw [← Set.InjOn.ncard_image (injOn_orbitVec.mono fun _ hP => hP.1)]
  have himg : orbitVec '' {P | P ∈ orbits ∧ height (orbitVec P) < 0} =
      (fun v => -v) '' posVecs := by
    ext v
    constructor
    · rintro ⟨P, ⟨hP, hneg⟩, rfl⟩
      refine ⟨-orbitVec P, ⟨neg_mem_vecs ⟨P, hP, rfl⟩, ?_⟩, neg_neg _⟩
      rw [height_neg]
      linarith
    · rintro ⟨u, ⟨hu, hpos⟩, rfl⟩
      obtain ⟨P, hP, hPv⟩ := neg_mem_vecs hu
      refine ⟨P, ⟨hP, ?_⟩, hPv⟩
      rw [hPv, height_neg]
      linarith
  rw [himg, Set.ncard_image_of_injective _ neg_injective, ncard_posVecs]

end CFSG.LieType.Chevalley.E6SignedGraph

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint.Chevalley CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.Steinberg.Adjoint
  E6SignedGraph

theorem E6_signed_graph_positive_orbit_collection
    (K : Type) [Field K] (hK : ringChar K ≠ 2) :
    {P | P ∈ orbits ∧ 0 < height (orbitVec P)}.ncard = 16 ∧
    {P | P ∈ orbits ∧ height (orbitVec P) < 0}.ncard = 16 ∧
    (∀ {m : ℕ} (O : Fin m → Finset E6Vec), Function.Injective O →
      Set.range O = {P | P ∈ orbits ∧ 0 < height (orbitVec P)} →
      Function.Injective (fun g : (i : Fin m) → ↥(orbitFixed K (O i)) =>
          (List.ofFn fun i => (g i : ModGL TwistTag.E6.tag K)).prod) ∧
        Set.range (fun g : (i : Fin m) → ↥(orbitFixed K (O i)) =>
          (List.ofFn fun i => (g i : ModGL TwistTag.E6.tag K)).prod) =
          (posFixed K : Set (ModGL TwistTag.E6.tag K))) ∧
    (∀ {m : ℕ} (O : Fin m → Finset E6Vec), Function.Injective O →
      Set.range O = {P | P ∈ orbits ∧ height (orbitVec P) < 0} →
      Function.Injective (fun g : (i : Fin m) → ↥(orbitFixed K (O i)) =>
          (List.ofFn fun i => (g i : ModGL TwistTag.E6.tag K)).prod) ∧
        Set.range (fun g : (i : Fin m) → ↥(orbitFixed K (O i)) =>
          (List.ofFn fun i => (g i : ModGL TwistTag.E6.tag K)).prod) =
          (negFixed K : Set (ModGL TwistTag.E6.tag K))) ∧
    rootGenerated K = ⨆ O ∈ orbits, orbitFixed K O ∧
    (∀ w ∈ relWeylTwist TwistTag.E6, ∀ a, orbitImage w a ∈ orbits →
      (orbitSL2 K w a).range ≤ rootGenerated K ∧
      ∀ t : Kˣ, orbitSL2 K w a (nSL t) ∈ rootGenerated K ∧
        orbitSL2 K w a (HSL t) ∈ rootGenerated K) ∧
    Group.IsNilpotent (posFixed K) ∧ Group.IsNilpotent (negFixed K) ∧
    (∀ g ∈ torusFixed K, ∀ g' ∈ torusFixed K, g * g' = g' * g) ∧
    torusFixed K ≤ Subgroup.normalizer (posFixed K : Set (ModGL TwistTag.E6.tag K)) ∧
    torusFixed K ≤ Subgroup.normalizer (negFixed K : Set (ModGL TwistTag.E6.tag K)) ∧
    torusFixed K ≤ Subgroup.normalizer (rootGenerated K : Set (ModGL TwistTag.E6.tag K)) ∧
    torusFixed K ⊓ posFixed K = ⊥ ∧ torusFixed K ⊓ negFixed K = ⊥ :=
  ⟨ncard_posOrbits, ncard_negOrbits, fun O hO hrange => posFixed_list_prod hK O hO hrange,
    fun O hO hrange => negFixed_list_prod hK O hO hrange, rootGenerated_eq_iSup hK,
    fun _ hw _ hO => ⟨range_orbitSL2_le_rootGenerated hw hO, fun _ =>
      ⟨range_orbitSL2_le_rootGenerated hw hO ⟨_, rfl⟩,
        range_orbitSL2_le_rootGenerated hw hO ⟨_, rfl⟩⟩⟩,
    isNilpotent_posFixed, isNilpotent_negFixed,
    fun _ hg _ hg' => torusFixed_mul_comm hg hg', torusFixed_le_normalizer_posFixed,
    torusFixed_le_normalizer_negFixed, torusFixed_le_normalizer_rootGenerated,
    torusFixed_inf_posFixed, torusFixed_inf_negFixed⟩

end CFSG.LieType.Chevalley
