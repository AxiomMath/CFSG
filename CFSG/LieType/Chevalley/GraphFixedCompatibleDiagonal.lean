module

public import CFSG.LieType.Chevalley.Braid
public import CFSG.LieType.Chevalley.GraphFixedRankOneScalar
public import CFSG.LieType.Chevalley.RootCharacterConjugation

public noncomputable section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

section Diagonal

variable {τ : Tag} {K : Type} [Field K]

theorem rootDiag_hVec (b : Fin τ.rank → Kˣ) (j : Fin τ.rank) :
    rootDiag b (hVec τ K j) = hVec τ K j :=
  rootDiag_single_inl b j

theorem rootDiag_rootVec
    (b : Fin τ.rank → Kˣ) {α : Fin τ.rank → ℤ} (hα : IsRoot τ α) :
    rootDiag b (rootVec τ K α) = ((rootChar b α : Kˣ) : K) • rootVec τ K α := by
  rw [rootVec_eq_single hα, rootDiag_single_inr]
  rfl

theorem rootChar_permLattice (b : Fin τ.rank → Kˣ) (π : Equiv.Perm (Fin τ.rank))
    (v : Fin τ.rank → ℤ) : rootChar b (permLattice π v) = rootChar (fun i => b (π i)) v :=
  (Fintype.prod_equiv π (fun i => b (π i) ^ v i) (fun j => b j ^ permLattice π v j) fun i => by
    simp [permLattice]).symm

theorem commute_torusElt
    (i j : Fin τ.rank) (s s' : Kˣ) :
    Commute (torusElt τ K i s) (torusElt τ K j s') := by
  refine Units.ext (rootModule_end_ext (fun l => ?_) fun α hα => ?_)
  · simp only [Units.val_mul, Module.End.mul_apply, torusElt_hVec]
  · simp only [Units.val_mul, Module.End.mul_apply, torusElt_rootVec _ _ hα, map_smul, smul_smul]
    rw [mul_comm]

end Diagonal

variable {t : TwistTag} {K : Type} [Field K] {σ : K →+* K}

theorem diagramMap_mul_rootDiag
    (b : Fin t.tag.rank → Kˣ) :
    (diagramMap t K : Module.End K (RootModule t.tag K)) * rootDiag b =
      rootDiag (fun i => b (t.perm.symm i)) *
        (diagramMap t K : Module.End K (RootModule t.tag K)) := by
  refine rootModule_end_ext (fun j => ?_) fun α hα => ?_
  · rw [Module.End.mul_apply, Module.End.mul_apply, rootDiag_hVec, diagramMap_hVec, rootDiag_hVec]
  · rw [Module.End.mul_apply, Module.End.mul_apply, rootDiag_rootVec b hα, map_smul,
      diagramMap_rootVec t K α hα, rootDiag_rootVec _ (hα.permLattice t.cartan_perm),
      rootChar_permLattice]
    simp only [Equiv.symm_apply_apply]

theorem twistHom_rootDiagUnit
    {b : Fin t.tag.rank → Kˣ}
    (hb : ∀ i, b (t.perm i) = Units.map σ.toMonoidHom (b i)) :
    twistHom t K σ (rootDiagUnit t.tag b) = rootDiagUnit t.tag b := by
  refine Units.ext ?_
  rw [coe_twistHom]
  change (diagramMap t K : Module.End K (RootModule t.tag K)) * entrywise σ (rootDiag b) *
    ((diagramMap t K)⁻¹ : ModGL t.tag K) = rootDiag b
  rw [entrywise_rootDiag, diagramMap_mul_rootDiag, mul_assoc, Units.mul_inv, mul_one]
  congr 1
  funext i
  rw [← hb, Equiv.apply_symm_apply]

theorem conj_rootDiagUnit_mem_twistedFixedGroup
    {b : Fin t.tag.rank → Kˣ}
    (hb : ∀ i, b (t.perm i) = Units.map σ.toMonoidHom (b i)) {g : ModGL t.tag K}
    (hg : g ∈ twistedFixedGroup t K σ) :
    rootDiagUnit t.tag b * g * (rootDiagUnit t.tag b)⁻¹ ∈ twistedFixedGroup t K σ := by
  obtain ⟨hgC, hgF⟩ := (mem_twistedFixedGroup_iff_twistHom t K σ).1 hg
  refine (mem_twistedFixedGroup_iff_twistHom t K σ).2
    ⟨conj_rootDiagUnit_mem_adjointGroup b hgC, ?_⟩
  rw [map_mul, map_mul, map_inv, twistHom_rootDiagUnit hb, hgF]

theorem rootDiagUnit_mem_normalizer_twistedFixedGroup
    {b : Fin t.tag.rank → Kˣ}
    (hb : ∀ i, b (t.perm i) = Units.map σ.toMonoidHom (b i)) :
    rootDiagUnit t.tag b ∈
      Subgroup.normalizer (twistedFixedGroup t K σ : Set (ModGL t.tag K)) := by
  refine Subgroup.mem_normalizer_iff.2 fun g =>
    ⟨conj_rootDiagUnit_mem_twistedFixedGroup hb, fun h => ?_⟩
  have hb' : ∀ i, b⁻¹ (t.perm i) = Units.map σ.toMonoidHom (b⁻¹ i) := fun i => by
    simp only [Pi.inv_apply, hb, map_inv]
  have h' := conj_rootDiagUnit_mem_twistedFixedGroup hb' h
  rwa [← rootDiagUnit_inv, inv_inv, show (rootDiagUnit t.tag b)⁻¹ *
    (rootDiagUnit t.tag b * g * (rootDiagUnit t.tag b)⁻¹) * rootDiagUnit t.tag b = g by group]
    at h'

theorem map_conj_rootDiagUnit_graphFixedPosUnipotent
    {b : Fin t.tag.rank → Kˣ}
    (hb : ∀ i, b (t.perm i) = Units.map σ.toMonoidHom (b i)) :
    (graphFixedPosUnipotent t K σ).map (MulAut.conj (rootDiagUnit t.tag b)).toMonoidHom =
      graphFixedPosUnipotent t K σ := by
  rw [graphFixedPosUnipotent, Subgroup.map_inf_eq _ _ _ (MulAut.conj _).injective,
    map_conj_eq_of_mem_normalizer (rootDiagUnit_mem_normalizer_twistedFixedGroup hb),
    ((chevalley_root_character_and_field_conjugation t.tag K).2.2.2.1 b).2.1]

theorem map_conj_rootDiagUnit_graphFixedNegUnipotent
    {b : Fin t.tag.rank → Kˣ}
    (hb : ∀ i, b (t.perm i) = Units.map σ.toMonoidHom (b i)) :
    (graphFixedNegUnipotent t K σ).map (MulAut.conj (rootDiagUnit t.tag b)).toMonoidHom =
      graphFixedNegUnipotent t K σ := by
  rw [graphFixedNegUnipotent, Subgroup.map_inf_eq _ _ _ (MulAut.conj _).injective,
    map_conj_eq_of_mem_normalizer (rootDiagUnit_mem_normalizer_twistedFixedGroup hb),
    ((chevalley_root_character_and_field_conjugation t.tag K).2.2.2.1 b).2.2]

theorem map_conj_rootDiagUnit_graphFixedRootGroup
    {b : Fin t.tag.rank → Kˣ}
    (hb : ∀ i, b (t.perm i) = Units.map σ.toMonoidHom (b i)) :
    (graphFixedRootGroup t K σ).map (MulAut.conj (rootDiagUnit t.tag b)).toMonoidHom =
      graphFixedRootGroup t K σ := by
  rw [graphFixedRootGroup, Subgroup.map_sup, map_conj_rootDiagUnit_graphFixedPosUnipotent hb,
    map_conj_rootDiagUnit_graphFixedNegUnipotent hb]

theorem rootDiagUnit_mem_normalizer_graphFixedRootGroup
    {b : Fin t.tag.rank → Kˣ}
    (hb : ∀ i, b (t.perm i) = Units.map σ.toMonoidHom (b i)) :
    rootDiagUnit t.tag b ∈
      Subgroup.normalizer (graphFixedRootGroup t K σ : Set (ModGL t.tag K)) := by
  have hb' : ∀ i, b⁻¹ (t.perm i) = Units.map σ.toMonoidHom (b⁻¹ i) := fun i => by
    simp only [Pi.inv_apply, hb, map_inv]
  refine Subgroup.mem_normalizer_iff.2 fun g => ⟨fun hg => ?_, fun hg => ?_⟩
  · rw [← map_conj_rootDiagUnit_graphFixedRootGroup hb]
    exact ⟨g, hg, rfl⟩
  · have h := map_conj_rootDiagUnit_graphFixedRootGroup (K := K) hb'
    rw [← h]
    refine ⟨_, hg, ?_⟩
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, ← rootDiagUnit_inv, inv_inv]
    group

variable (t σ) in
@[expose] def compatDiag (u : (a : Fin t.foldedTag.rank) → (orbitField t K σ a)ˣ) :
    Fin t.tag.rank → Kˣ :=
  fun i => orbitUnitParam t σ (t.orbitIndex i) (orbitFieldUnit t σ (u (t.orbitIndex i))) i

theorem compatDiag_pow (u : (a : Fin t.foldedTag.rank) → (orbitField t K σ a)ˣ)
    (a : Fin t.foldedTag.rank) {k : ℕ} (hk : k < (t.orbit a).card) :
    compatDiag t σ u ((t.perm ^ k) (t.orbitMin a)) =
      Units.map (σ ^ k).toMonoidHom (orbitFieldUnit t σ (u a)) := by
  have ha : t.orbitIndex ((t.perm ^ k) (t.orbitMin a)) = a :=
    (t.mem_orbit_iff).1 (t.perm_pow_mem_orbit (t.orbitMin_mem a) k)
  unfold compatDiag
  rw [ha]
  exact orbitUnitParam_pow t σ _ hk

theorem compatDiag_orbitMin (u : (a : Fin t.foldedTag.rank) → (orbitField t K σ a)ˣ)
    (a : Fin t.foldedTag.rank) : compatDiag t σ u (t.orbitMin a) = orbitFieldUnit t σ (u a) := by
  have h := compatDiag_pow u a (t.card_orbit_pos a)
  rw [pow_zero, Equiv.Perm.one_apply] at h
  rw [h]
  exact Units.ext rfl

theorem coe_compatDiag (u : (a : Fin t.foldedTag.rank) → (orbitField t K σ a)ˣ)
    (i : Fin t.tag.rank) :
    (compatDiag t σ u i : K) =
      orbitParam t σ (t.orbitIndex i)
        ((u (t.orbitIndex i) : orbitField t K σ (t.orbitIndex i)) : K) i :=
  coe_orbitUnitParam t σ _ (t.mem_orbit_orbitIndex i)

theorem compatDiag_perm (u : (a : Fin t.foldedTag.rank) → (orbitField t K σ a)ˣ)
    (i : Fin t.tag.rank) :
    compatDiag t σ u (t.perm i) = Units.map σ.toMonoidHom (compatDiag t σ u i) := by
  refine Units.ext ?_
  change ((compatDiag t σ u (t.perm i) : Kˣ) : K) = σ ((compatDiag t σ u i : Kˣ) : K)
  rw [coe_compatDiag, coe_compatDiag]
  have h := t.orbitIndex_perm i
  have key : ∀ a (v : (orbitField t K σ a)ˣ), t.orbitIndex i = a →
      orbitParam t σ a ((v : orbitField t K σ a) : K) (t.perm i) =
        σ (orbitParam t σ a ((v : orbitField t K σ a) : K) i) := fun a v ha =>
    orbitParam_perm ((mem_orbitField).1 (v : orbitField t K σ a).2) ((t.mem_orbit_iff).2 ha)
  rw [h]
  exact key _ _ rfl

theorem compatDiag_mul (u v : (a : Fin t.foldedTag.rank) → (orbitField t K σ a)ˣ) :
    compatDiag t σ (u * v) = compatDiag t σ u * compatDiag t σ v := by
  funext i
  obtain ⟨k, hk, hi⟩ := t.exists_eq_perm_pow_orbitMin (t.mem_orbit_orbitIndex i)
  rw [Pi.mul_apply, ← hi, compatDiag_pow _ _ hk, compatDiag_pow _ _ hk, compatDiag_pow _ _ hk,
    ← map_mul]
  congr 1

theorem compatDiag_one : compatDiag t σ (1 : (a : Fin t.foldedTag.rank) → (orbitField t K σ a)ˣ) =
    1 := by
  funext i
  obtain ⟨k, hk, hi⟩ := t.exists_eq_perm_pow_orbitMin (t.mem_orbit_orbitIndex i)
  rw [Pi.one_apply, ← hi, compatDiag_pow _ _ hk]
  have h1 : orbitFieldUnit t σ ((1 : (a : Fin t.foldedTag.rank) → (orbitField t K σ a)ˣ)
    (t.orbitIndex i)) = 1 := map_one _
  rw [h1, map_one]

theorem exists_compatDiag_eq {b : Fin t.tag.rank → Kˣ}
    (hb : ∀ i, b (t.perm i) = Units.map σ.toMonoidHom (b i)) :
    ∃ u : (a : Fin t.foldedTag.rank) → (orbitField t K σ a)ˣ, compatDiag t σ u = b := by
  have hpow : ∀ (k : ℕ) (i : Fin t.tag.rank),
      ((b ((t.perm ^ k) i) : Kˣ) : K) = (σ ^ k) ((b i : Kˣ) : K) := by
    intro k
    induction k with
    | zero => intro i; rfl
    | succ k ih =>
      intro i
      rw [pow_succ', Equiv.Perm.mul_apply, hb, pow_succ', RingHom.coe_mul, Function.comp_apply,
        ← ih]
      rfl
  have hmem : ∀ a, ((b (t.orbitMin a) : Kˣ) : K) ∈ orbitField t K σ a := fun a => by
    rw [mem_orbitField, ← hpow, t.perm_pow_card_orbitMin]
  refine ⟨fun a => Units.mk0 ⟨_, hmem a⟩ fun h => (b (t.orbitMin a)).ne_zero
    (congrArg Subtype.val h), ?_⟩
  funext i
  obtain ⟨k, hk, hi⟩ := t.exists_eq_perm_pow_orbitMin (t.mem_orbit_orbitIndex i)
  rw [← hi, compatDiag_pow _ _ hk]
  refine Units.ext ?_
  rw [hpow]
  rfl

theorem compatDiag_conj_orbitX
    (u : (a : Fin t.foldedTag.rank) → (orbitField t K σ a)ˣ)
    (a : Fin t.foldedTag.rank) (c : orbitField t K σ a) :
    rootDiagUnit t.tag (compatDiag t σ u) * orbitX t K σ a c *
        (rootDiagUnit t.tag (compatDiag t σ u))⁻¹ =
      orbitX t K σ a ((u a : orbitField t K σ a) * c) := by
  rw [coe_orbitX, coe_orbitX, ← MulAut.conj_apply, map_list_prod, List.map_map]
  refine congrArg List.prod (List.map_congr_left fun k hk => ?_)
  rw [Function.comp_apply, MulAut.conj_apply, (root_diagonal_conjugation t.tag K _).1,
    compatDiag_pow u a (List.mem_range.1 hk)]
  congr 1
  rw [Units.coe_map, coe_orbitFieldUnit, Subfield.coe_mul, map_mul]
  rfl

theorem compatDiag_conj_orbitY
    (u : (a : Fin t.foldedTag.rank) → (orbitField t K σ a)ˣ)
    (a : Fin t.foldedTag.rank) (c : orbitField t K σ a) :
    rootDiagUnit t.tag (compatDiag t σ u) * orbitY t K σ a c *
        (rootDiagUnit t.tag (compatDiag t σ u))⁻¹ =
      orbitY t K σ a (((u a)⁻¹ : (orbitField t K σ a)ˣ) * c) := by
  rw [coe_orbitY, coe_orbitY, ← MulAut.conj_apply, map_list_prod, List.map_map]
  refine congrArg List.prod (List.map_congr_left fun k hk => ?_)
  rw [Function.comp_apply, MulAut.conj_apply, (root_diagonal_conjugation t.tag K _).2.1,
    compatDiag_pow u a (List.mem_range.1 hk)]
  congr 1
  rw [Units.val_inv_eq_inv_val, Units.coe_map, coe_orbitFieldUnit, Units.val_inv_eq_inv_val,
    Subfield.coe_mul, Subfield.coe_inv, map_mul, map_inv₀]
  rfl

variable (t K σ) in
@[expose] def compatDiagHom :
    ((a : Fin t.foldedTag.rank) → (orbitField t K σ a)ˣ) →*
      Subgroup.normalizer (graphFixedRootGroup t K σ : Set (ModGL t.tag K)) where
  toFun u := ⟨rootDiagUnit t.tag (compatDiag t σ u),
    rootDiagUnit_mem_normalizer_graphFixedRootGroup (compatDiag_perm u)⟩
  map_one' := Subtype.ext (by
    change rootDiagUnit t.tag (compatDiag t σ 1) = 1
    rw [compatDiag_one, rootDiagUnit_one])
  map_mul' u v := Subtype.ext (by
    change rootDiagUnit t.tag (compatDiag t σ (u * v)) =
      rootDiagUnit t.tag (compatDiag t σ u) * rootDiagUnit t.tag (compatDiag t σ v)
    rw [compatDiag_mul, rootDiagUnit_mul])

variable (t K σ) in
@[expose] def compatDiagAutHom :
    ((a : Fin t.foldedTag.rank) → (orbitField t K σ a)ˣ) →* MulAut (graphFixedRootGroup t K σ) :=
  (graphFixedRootGroup t K σ).normalizerMonoidHom.comp (compatDiagHom t K σ)

theorem coe_compatDiagAutHom
    (u : (a : Fin t.foldedTag.rank) → (orbitField t K σ a)ˣ)
    (g : graphFixedRootGroup t K σ) :
    ((compatDiagAutHom t K σ u g : graphFixedRootGroup t K σ) : ModGL t.tag K) =
      rootDiagUnit t.tag (compatDiag t σ u) * g * (rootDiagUnit t.tag (compatDiag t σ u))⁻¹ :=
  Subgroup.normalizerMonoidHom_apply_apply_coe (graphFixedRootGroup t K σ) (compatDiagHom t K σ u) g

theorem compatDiagAutHom_injective
    : Function.Injective (compatDiagAutHom t K σ) := by
  intro u v h
  funext a
  have hx := congrArg (fun φ : MulAut (graphFixedRootGroup t K σ) =>
    ((φ ⟨_, graphFixedPosUnipotent_le_graphFixedRootGroup t K σ
      (orbitX_mem_graphFixedPosUnipotent t σ a 1)⟩ : graphFixedRootGroup t K σ) :
        ModGL t.tag K)) h
  simp only [coe_compatDiagAutHom, compatDiag_conj_orbitX, mul_one] at hx
  exact Units.ext (orbitX_injective σ a (Subtype.ext hx))

theorem map_compatDiagAutHom_subgroupOf
    {X : Subgroup (ModGL t.tag K)}
    (hXC : X ≤ graphFixedRootGroup t K σ)
    (u : (a : Fin t.foldedTag.rank) → (orbitField t K σ a)ˣ)
    (hX : X.map (MulAut.conj (rootDiagUnit t.tag (compatDiag t σ u))).toMonoidHom = X) :
    (X.subgroupOf (graphFixedRootGroup t K σ)).map (compatDiagAutHom t K σ u).toMonoidHom =
      X.subgroupOf (graphFixedRootGroup t K σ) := by
  refine le_antisymm ?_ fun x hx => ?_
  · rintro _ ⟨y, hy, rfl⟩
    rw [Subgroup.mem_subgroupOf, MulEquiv.coe_toMonoidHom, coe_compatDiagAutHom]
    rw [← hX]
    exact ⟨_, hy, rfl⟩
  · have hx' : (x : ModGL t.tag K) ∈ X.map
        (MulAut.conj (rootDiagUnit t.tag (compatDiag t σ u))).toMonoidHom := by
      rw [hX]
      exact hx
    obtain ⟨y, hy, hyx⟩ := hx'
    refine ⟨⟨y, hXC hy⟩, hy, Subtype.ext ?_⟩
    rw [MulEquiv.coe_toMonoidHom, coe_compatDiagAutHom]
    exact hyx

section FieldAut

variable {δ : K ≃+* K}

theorem units_map_entrywiseHom_symm_apply (δ : K ≃+* K) (g : ModGL t.tag K) :
    Units.map (entrywiseHom δ.toRingHom) (Units.map (entrywiseHom δ.symm.toRingHom) g) = g := by
  rw [units_map_entrywiseHom_comp]
  refine Units.ext ?_
  rw [Units.coe_map, RingEquiv.toRingHom_comp_symm_toRingHom]
  exact entrywise_id _

theorem units_map_entrywiseHom_apply_symm (δ : K ≃+* K) (g : ModGL t.tag K) :
    Units.map (entrywiseHom δ.symm.toRingHom) (Units.map (entrywiseHom δ.toRingHom) g) = g := by
  rw [units_map_entrywiseHom_comp]
  refine Units.ext ?_
  rw [Units.coe_map, RingEquiv.symm_toRingHom_comp_toRingHom]
  exact entrywise_id _

theorem twistHom_units_map_entrywiseHom (hδ : ∀ c, δ (σ c) = σ (δ c)) (g : ModGL t.tag K) :
    twistHom t K σ (Units.map (entrywiseHom δ.toRingHom) g) =
      Units.map (entrywiseHom δ.toRingHom) (twistHom t K σ g) := by
  have hcomm : σ.comp δ.toRingHom = δ.toRingHom.comp σ := RingHom.ext fun c => (hδ c).symm
  rw [twistHom_apply, twistHom_apply, map_mul, map_mul, map_inv,
    units_map_entrywiseHom_diagramMap, units_map_entrywiseHom_comp,
    units_map_entrywiseHom_comp, hcomm]

theorem symm_comm_of_comm (hδ : ∀ c, δ (σ c) = σ (δ c)) (c : K) :
    δ.symm (σ c) = σ (δ.symm c) := by
  apply δ.injective
  rw [RingEquiv.apply_symm_apply, hδ, RingEquiv.apply_symm_apply]

theorem units_map_entrywiseHom_mem_twistedFixedGroup
    (hδ : ∀ c, δ (σ c) = σ (δ c))
    {g : ModGL t.tag K} (hg : g ∈ twistedFixedGroup t K σ) :
    Units.map (entrywiseHom δ.toRingHom) g ∈ twistedFixedGroup t K σ := by
  obtain ⟨hgC, hgF⟩ := (mem_twistedFixedGroup_iff_twistHom t K σ).1 hg
  refine (mem_twistedFixedGroup_iff_twistHom t K σ).2 ⟨?_, ?_⟩
  · rw [← ((chevalley_root_character_and_field_conjugation t.tag K).2.2.2.2.1 δ).1]
    exact ⟨g, hgC, rfl⟩
  · rw [twistHom_units_map_entrywiseHom hδ, hgF]

theorem map_units_map_entrywiseHom_twistedFixedGroup
    (hδ : ∀ c, δ (σ c) = σ (δ c)) :
    (twistedFixedGroup t K σ).map (Units.map (entrywiseHom δ.toRingHom)) =
      twistedFixedGroup t K σ := by
  refine le_antisymm ?_ fun g hg => ?_
  · rintro _ ⟨g, hg, rfl⟩
    exact units_map_entrywiseHom_mem_twistedFixedGroup hδ hg
  · exact ⟨_, units_map_entrywiseHom_mem_twistedFixedGroup (δ := δ.symm)
      (symm_comm_of_comm hδ) hg, units_map_entrywiseHom_symm_apply δ g⟩

theorem units_map_entrywiseHom_injective
    (δ : K ≃+* K) :
    Function.Injective (Units.map (entrywiseHom δ.toRingHom) : ModGL t.tag K → ModGL t.tag K) :=
  fun _ _ hgh => Units.map_injective (f := entrywiseHom δ.toRingHom)
    (entrywise_injective δ.toRingHom) hgh

theorem map_units_map_entrywiseHom_graphFixedPosUnipotent
    (hδ : ∀ c, δ (σ c) = σ (δ c)) :
    (graphFixedPosUnipotent t K σ).map (Units.map (entrywiseHom δ.toRingHom)) =
      graphFixedPosUnipotent t K σ := by
  rw [graphFixedPosUnipotent, Subgroup.map_inf_eq _ _ _ (units_map_entrywiseHom_injective δ),
    map_units_map_entrywiseHom_twistedFixedGroup hδ,
    ((chevalley_root_character_and_field_conjugation t.tag K).2.2.2.2.1 δ).2.1]

theorem map_units_map_entrywiseHom_graphFixedNegUnipotent
    (hδ : ∀ c, δ (σ c) = σ (δ c)) :
    (graphFixedNegUnipotent t K σ).map (Units.map (entrywiseHom δ.toRingHom)) =
      graphFixedNegUnipotent t K σ := by
  rw [graphFixedNegUnipotent, Subgroup.map_inf_eq _ _ _ (units_map_entrywiseHom_injective δ),
    map_units_map_entrywiseHom_twistedFixedGroup hδ,
    ((chevalley_root_character_and_field_conjugation t.tag K).2.2.2.2.1 δ).2.2]

theorem map_units_map_entrywiseHom_graphFixedRootGroup
    (hδ : ∀ c, δ (σ c) = σ (δ c)) :
    (graphFixedRootGroup t K σ).map (Units.map (entrywiseHom δ.toRingHom)) =
      graphFixedRootGroup t K σ := by
  rw [graphFixedRootGroup, Subgroup.map_sup, map_units_map_entrywiseHom_graphFixedPosUnipotent hδ,
    map_units_map_entrywiseHom_graphFixedNegUnipotent hδ]

theorem units_map_entrywiseHom_mem_graphFixedRootGroup
    (hδ : ∀ c, δ (σ c) = σ (δ c))
    {g : ModGL t.tag K} (hg : g ∈ graphFixedRootGroup t K σ) :
    Units.map (entrywiseHom δ.toRingHom) g ∈ graphFixedRootGroup t K σ := by
  rw [← map_units_map_entrywiseHom_graphFixedRootGroup hδ]
  exact ⟨g, hg, rfl⟩

variable (σ) in
@[expose] def graphFixedEntrywiseAut
    (hδ : ∀ c, δ (σ c) = σ (δ c)) :
    MulAut (graphFixedRootGroup t K σ) where
  toFun g := ⟨Units.map (entrywiseHom δ.toRingHom) g,
    units_map_entrywiseHom_mem_graphFixedRootGroup hδ g.2⟩
  invFun g := ⟨Units.map (entrywiseHom δ.symm.toRingHom) g,
    units_map_entrywiseHom_mem_graphFixedRootGroup (δ := δ.symm) (symm_comm_of_comm hδ) g.2⟩
  left_inv g := Subtype.ext (units_map_entrywiseHom_apply_symm δ (g : ModGL t.tag K))
  right_inv g := Subtype.ext (units_map_entrywiseHom_symm_apply δ (g : ModGL t.tag K))
  map_mul' _ _ := Subtype.ext (map_mul _ _ _)

theorem coe_graphFixedEntrywiseAut
    (hδ : ∀ c, δ (σ c) = σ (δ c))
    (g : graphFixedRootGroup t K σ) :
    ((graphFixedEntrywiseAut σ hδ g : graphFixedRootGroup t K σ) : ModGL t.tag K) =
      Units.map (entrywiseHom δ.toRingHom) g :=
  rfl

theorem coe_graphFixedEntrywiseAut_symm
    (hδ : ∀ c, δ (σ c) = σ (δ c))
    (g : graphFixedRootGroup t K σ) :
    (((graphFixedEntrywiseAut σ hδ).symm g : graphFixedRootGroup t K σ) : ModGL t.tag K) =
      Units.map (entrywiseHom δ.symm.toRingHom) g :=
  rfl

theorem map_graphFixedEntrywiseAut_subgroupOf
    (hδ : ∀ c, δ (σ c) = σ (δ c))
    {X : Subgroup (ModGL t.tag K)} (hXC : X ≤ graphFixedRootGroup t K σ)
    (hX : X.map (Units.map (entrywiseHom δ.toRingHom)) = X) :
    (X.subgroupOf (graphFixedRootGroup t K σ)).map (graphFixedEntrywiseAut σ hδ).toMonoidHom =
      X.subgroupOf (graphFixedRootGroup t K σ) := by
  refine le_antisymm ?_ fun x hx => ?_
  · rintro _ ⟨y, hy, rfl⟩
    rw [Subgroup.mem_subgroupOf, MulEquiv.coe_toMonoidHom, coe_graphFixedEntrywiseAut, ← hX]
    exact ⟨_, hy, rfl⟩
  · have hx' : (x : ModGL t.tag K) ∈ X.map (Units.map (entrywiseHom δ.toRingHom)) := by
      rw [hX]
      exact hx
    obtain ⟨y, hy, hyx⟩ := hx'
    exact ⟨⟨y, hXC hy⟩, hy, Subtype.ext hyx⟩

theorem map_mem_orbitField (hδ : ∀ c, δ (σ c) = σ (δ c)) {a : Fin t.foldedTag.rank}
    {c : K} (hc : c ∈ orbitField t K σ a) : δ c ∈ orbitField t K σ a := by
  have hpow : ∀ (n : ℕ) (x : K), δ ((σ ^ n) x) = (σ ^ n) (δ x) := by
    intro n
    induction n with
    | zero => intro x; rfl
    | succ n ih =>
      intro x
      rw [pow_succ', RingHom.coe_mul, Function.comp_apply, Function.comp_apply, hδ, ih]
  rw [mem_orbitField] at hc ⊢
  rw [← hpow, hc]

variable (σ) in
@[expose] def orbitUnitsMap (hδ : ∀ c, δ (σ c) = σ (δ c))
    (u : (a : Fin t.foldedTag.rank) → (orbitField t K σ a)ˣ) :
    (a : Fin t.foldedTag.rank) → (orbitField t K σ a)ˣ :=
  fun a => Units.mk0 ⟨δ ((u a : orbitField t K σ a) : K), map_mem_orbitField hδ (u a).val.2⟩
    fun h => (u a).ne_zero (Subtype.ext (by
      have h' := congrArg Subtype.val h
      exact δ.injective (h'.trans (map_zero δ).symm)))

theorem coe_orbitUnitsMap (hδ : ∀ c, δ (σ c) = σ (δ c))
    (u : (a : Fin t.foldedTag.rank) → (orbitField t K σ a)ˣ) (a : Fin t.foldedTag.rank) :
    ((orbitUnitsMap σ hδ u a : orbitField t K σ a) : K) = δ ((u a : orbitField t K σ a) : K) :=
  rfl

theorem compatDiag_orbitUnitsMap (hδ : ∀ c, δ (σ c) = σ (δ c))
    (u : (a : Fin t.foldedTag.rank) → (orbitField t K σ a)ˣ) :
    compatDiag t σ (orbitUnitsMap σ hδ u) =
      fun i => Units.map δ.toRingHom.toMonoidHom (compatDiag t σ u i) := by
  have hpow : ∀ (n : ℕ) (x : K), δ ((σ ^ n) x) = (σ ^ n) (δ x) := by
    intro n
    induction n with
    | zero => intro x; rfl
    | succ n ih =>
      intro x
      rw [pow_succ', RingHom.coe_mul, Function.comp_apply, Function.comp_apply, hδ, ih]
  funext i
  obtain ⟨k, hk, hi⟩ := t.exists_eq_perm_pow_orbitMin (t.mem_orbit_orbitIndex i)
  rw [← hi, compatDiag_pow _ _ hk, compatDiag_pow _ _ hk]
  refine Units.ext ?_
  change (σ ^ k) (δ ((u (t.orbitIndex i) : orbitField t K σ (t.orbitIndex i)) : K)) =
    δ ((σ ^ k) ((u (t.orbitIndex i) : orbitField t K σ (t.orbitIndex i)) : K))
  exact (hpow k _).symm

theorem units_map_entrywiseHom_rootDiagUnit (δ : K →+* K) (b : Fin t.tag.rank → Kˣ) :
    Units.map (entrywiseHom δ) (rootDiagUnit t.tag b) =
      rootDiagUnit t.tag (fun i => Units.map δ.toMonoidHom (b i)) :=
  Units.ext (entrywise_rootDiag δ b)

theorem graphFixedEntrywiseAut_conj_compatDiagAutHom
    (hδ : ∀ c, δ (σ c) = σ (δ c))
    (u : (a : Fin t.foldedTag.rank) → (orbitField t K σ a)ˣ) :
    graphFixedEntrywiseAut σ hδ * compatDiagAutHom t K σ u * (graphFixedEntrywiseAut σ hδ)⁻¹ =
      compatDiagAutHom t K σ (orbitUnitsMap σ hδ u) := by
  refine MulEquiv.ext fun g => Subtype.ext ?_
  rw [MulAut.mul_apply, MulAut.mul_apply, coe_graphFixedEntrywiseAut, coe_compatDiagAutHom,
    MulAut.inv_apply, coe_graphFixedEntrywiseAut_symm, coe_compatDiagAutHom, map_mul, map_mul,
    map_inv, units_map_entrywiseHom_symm_apply, units_map_entrywiseHom_rootDiagUnit,
    compatDiag_orbitUnitsMap]

end FieldAut

theorem list_prod_orbitH
    (s : (a : Fin t.foldedTag.rank) → (orbitField t K σ a)ˣ) :
    ((List.finRange t.foldedTag.rank).map fun a => (orbitH t K σ a (s a) : ModGL t.tag K)).prod =
      ((List.finRange t.tag.rank).map fun j => torusElt t.tag K j (compatDiag t σ s j)).prod := by
  set F : Fin t.tag.rank → ModGL t.tag K := fun j => torusElt t.tag K j (compatDiag t σ s j)
  have h1 : ((List.finRange t.foldedTag.rank).map fun a =>
      (orbitH t K σ a (s a) : ModGL t.tag K)) =
        (List.finRange t.foldedTag.rank).map fun a => ((t.orbitWord a).map F).prod := by
    refine List.map_congr_left fun a _ => ?_
    rw [coe_orbitH_eq]
    refine congrArg List.prod (List.map_congr_left fun j hj => ?_)
    have ha : t.orbitIndex j = a := (t.mem_orbit_iff).1 ((t.mem_orbitWord).1 hj)
    subst ha
    rfl
  have hperm : List.Perm ((List.finRange t.foldedTag.rank).flatMap t.orbitWord)
      (List.finRange t.tag.rank) := by
    cases t <;> decide
  have h2 : ((List.finRange t.foldedTag.rank).map fun a => ((t.orbitWord a).map F).prod).prod =
      (((List.finRange t.foldedTag.rank).flatMap t.orbitWord).map F).prod := by
    rw [List.map_flatMap, List.flatMap_def, List.prod_flatten, List.map_map]
    rfl
  rw [h1, h2]
  exact (hperm.map F).prod_eq'
    (List.pairwise_map.2 (List.pairwise_of_forall fun i j => commute_torusElt i j _ _))

end CFSG.LieType.Chevalley
