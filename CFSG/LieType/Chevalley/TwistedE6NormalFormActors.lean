module

public import CFSG.LieType.Chevalley.GraphFixedE6CommonField

public noncomputable section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint CFSG.Blueprint.Chevalley

section Ext

variable {t : TwistTag} {K : Type} [Field K] {σ : K →+* K}

theorem graphFixedRootGroup_mulAut_ext
    (hσ : Function.Surjective σ)
    {β γ : MulAut (graphFixedRootGroup t K σ)}
    (hX : ∀ a c, β (fixedOrbitX t K σ a c) = γ (fixedOrbitX t K σ a c))
    (hY : ∀ a c, β (fixedOrbitY t K σ a c) = γ (fixedOrbitY t K σ a c)) : β = γ := by
  have hle : ⨆ a, (orbitRankOneHomFixed t K σ a).range ≤
      β.toMonoidHom.eqLocus γ.toMonoidHom := by
    refine iSup_le fun a => ?_
    rw [range_eq_sl2RootX_sup_sl2RootY]
    refine sup_le ?_ ?_
    · rintro _ ⟨c, rfl⟩
      change β _ = γ _
      dsimp only
      rw [orbitRankOneHomFixed_sl2Upper]
      exact hX a c
    · rintro _ ⟨c, rfl⟩
      change β _ = γ _
      dsimp only
      rw [orbitRankOneHomFixed_sl2Lower]
      exact hY a c
  rw [iSup_range_orbitRankOneHomFixed hσ] at hle
  exact MulEquiv.ext fun g => hle (Subgroup.mem_top g)

theorem compatDiagAutHom_fixedOrbitX
    (u : (a : Fin t.foldedTag.rank) → (orbitField t K σ a)ˣ)
    (a : Fin t.foldedTag.rank) (c : orbitField t K σ a) :
    compatDiagAutHom t K σ u (fixedOrbitX t K σ a c) =
      fixedOrbitX t K σ a ((u a : orbitField t K σ a) * c) :=
  Subtype.ext ((coe_compatDiagAutHom u _).trans (compatDiag_conj_orbitX u a c))

theorem compatDiagAutHom_fixedOrbitY
    (u : (a : Fin t.foldedTag.rank) → (orbitField t K σ a)ˣ)
    (a : Fin t.foldedTag.rank) (c : orbitField t K σ a) :
    compatDiagAutHom t K σ u (fixedOrbitY t K σ a c) =
      fixedOrbitY t K σ a (((u a)⁻¹ : (orbitField t K σ a)ˣ) * c) :=
  Subtype.ext ((coe_compatDiagAutHom u _).trans (compatDiag_conj_orbitY u a c))

theorem units_map_entrywiseHom_orbitX
    {δ : K ≃+* K} (hδ : ∀ c, δ (σ c) = σ (δ c))
    (a : Fin t.foldedTag.rank) (c : orbitField t K σ a) :
    Units.map (entrywiseHom δ.toRingHom) (orbitX t K σ a c : ModGL t.tag K) =
      orbitX t K σ a ⟨δ c, map_mem_orbitField hδ c.2⟩ := by
  rw [coe_orbitX, coe_orbitX, map_list_prod, List.map_map]
  refine congrArg List.prod (List.map_congr_left fun k _ => ?_)
  refine Units.ext ?_
  rw [Function.comp_apply, Units.coe_map]
  change entrywise δ.toRingHom (xOp t.tag K _ ((σ ^ k) (c : K))) =
    xOp t.tag K _ ((σ ^ k) (δ (c : K)))
  rw [entrywise_xOp]
  congr 1
  exact ringHom_pow_comm hδ k c

theorem units_map_entrywiseHom_orbitY
    {δ : K ≃+* K} (hδ : ∀ c, δ (σ c) = σ (δ c))
    (a : Fin t.foldedTag.rank) (c : orbitField t K σ a) :
    Units.map (entrywiseHom δ.toRingHom) (orbitY t K σ a c : ModGL t.tag K) =
      orbitY t K σ a ⟨δ c, map_mem_orbitField hδ c.2⟩ := by
  rw [coe_orbitY, coe_orbitY, map_list_prod, List.map_map]
  refine congrArg List.prod (List.map_congr_left fun k _ => ?_)
  refine Units.ext ?_
  rw [Function.comp_apply, Units.coe_map]
  change entrywise δ.toRingHom (yOp t.tag K _ ((σ ^ k) (c : K))) =
    yOp t.tag K _ ((σ ^ k) (δ (c : K)))
  rw [entrywise_yOp]
  congr 1
  exact ringHom_pow_comm hδ k c

end Ext

section Finite

variable {t : TwistTag} {K : Type} [Field K] [Finite K] (σ : K ≃+* K)

@[expose] def fieldActor
    (δ : K ≃+* K) : MulAut (graphFixedRootGroup t K σ.toRingHom) :=
  graphFixedEntrywiseAut σ.toRingHom (ringEquiv_comm_of_finite σ δ)

theorem coe_fieldActor
    (δ : K ≃+* K) (g : graphFixedRootGroup t K σ.toRingHom) :
    ((fieldActor σ δ g : graphFixedRootGroup t K σ.toRingHom) : ModGL t.tag K) =
      Units.map (entrywiseHom δ.toRingHom) g :=
  rfl

@[expose] def fieldActorHom
    : RingAut K →* MulAut (graphFixedRootGroup t K σ.toRingHom) where
  toFun δ := fieldActor σ δ
  map_one' := MulEquiv.ext fun _ => Subtype.ext (Units.ext (entrywise_id _))
  map_mul' δ ε := MulEquiv.ext fun _ => Subtype.ext (Units.ext
    (entrywise_entrywise δ.toRingHom ε.toRingHom _).symm)

theorem fieldActorHom_apply
    (δ : RingAut K) :
    fieldActorHom (t := t) σ δ = fieldActor σ δ := rfl

theorem fieldActor_one
    : fieldActor (t := t) σ (1 : RingAut K) = 1 :=
  map_one (fieldActorHom (t := t) σ)

theorem fieldActor_mul
    (δ ε : RingAut K) :
    fieldActor (t := t) σ (δ * ε) = fieldActor σ δ * fieldActor σ ε :=
  map_mul (fieldActorHom (t := t) σ) δ ε

theorem fieldActor_fixedOrbitX
    (δ : K ≃+* K) (a : Fin t.foldedTag.rank)
    (c : orbitField t K σ.toRingHom a) :
    fieldActor σ δ (fixedOrbitX t K σ.toRingHom a c) =
      fixedOrbitX t K σ.toRingHom a (orbitFieldRestrict t σ δ a c) :=
  Subtype.ext (units_map_entrywiseHom_orbitX (ringEquiv_comm_of_finite σ δ) a c)

theorem fieldActor_fixedOrbitY
    (δ : K ≃+* K) (a : Fin t.foldedTag.rank)
    (c : orbitField t K σ.toRingHom a) :
    fieldActor σ δ (fixedOrbitY t K σ.toRingHom a c) =
      fixedOrbitY t K σ.toRingHom a (orbitFieldRestrict t σ δ a c) :=
  Subtype.ext (units_map_entrywiseHom_orbitY (ringEquiv_comm_of_finite σ δ) a c)

theorem fieldActor_mul_compatDiagAutHom
    (δ : K ≃+* K)
    (v : (a : Fin t.foldedTag.rank) → (orbitField t K σ.toRingHom a)ˣ) :
    fieldActor σ δ * compatDiagAutHom t K σ.toRingHom v =
      compatDiagAutHom t K σ.toRingHom
        (orbitUnitsMap σ.toRingHom (ringEquiv_comm_of_finite σ δ) v) * fieldActor σ δ := by
  rw [← graphFixedEntrywiseAut_conj_compatDiagAutHom (ringEquiv_comm_of_finite σ δ) v]
  change _ = graphFixedEntrywiseAut _ _ * compatDiagAutHom t K σ.toRingHom v *
    (graphFixedEntrywiseAut _ _)⁻¹ * graphFixedEntrywiseAut _ _
  rw [inv_mul_cancel_right]
  rfl

@[expose] def normalActor
    (u : (a : Fin t.foldedTag.rank) → (orbitField t K σ.toRingHom a)ˣ)
    (δ : K ≃+* K) : MulAut (graphFixedRootGroup t K σ.toRingHom) :=
  compatDiagAutHom t K σ.toRingHom u * fieldActor σ δ

theorem normalActor_fixedOrbitX
    (u : (a : Fin t.foldedTag.rank) → (orbitField t K σ.toRingHom a)ˣ)
    (δ : K ≃+* K) (a : Fin t.foldedTag.rank) (c : orbitField t K σ.toRingHom a) :
    normalActor σ u δ (fixedOrbitX t K σ.toRingHom a c) =
      fixedOrbitX t K σ.toRingHom a ((u a : orbitField t K σ.toRingHom a) *
        orbitFieldRestrict t σ δ a c) := by
  rw [normalActor, MulAut.mul_apply, fieldActor_fixedOrbitX, compatDiagAutHom_fixedOrbitX]

theorem normalActor_fixedOrbitY
    (u : (a : Fin t.foldedTag.rank) → (orbitField t K σ.toRingHom a)ˣ)
    (δ : K ≃+* K) (a : Fin t.foldedTag.rank) (c : orbitField t K σ.toRingHom a) :
    normalActor σ u δ (fixedOrbitY t K σ.toRingHom a c) =
      fixedOrbitY t K σ.toRingHom a (((u a)⁻¹ : (orbitField t K σ.toRingHom a)ˣ) *
        orbitFieldRestrict t σ δ a c) := by
  rw [normalActor, MulAut.mul_apply, fieldActor_fixedOrbitY, compatDiagAutHom_fixedOrbitY]

theorem normalActor_mul
    (u v : (a : Fin t.foldedTag.rank) → (orbitField t K σ.toRingHom a)ˣ)
    (δ ε : K ≃+* K) :
    normalActor σ u δ * normalActor σ v ε = normalActor σ
      (u * orbitUnitsMap σ.toRingHom (ringEquiv_comm_of_finite σ δ) v) (δ * ε) := by
  rw [normalActor, normalActor, normalActor, fieldActor_mul, map_mul, mul_assoc,
    ← mul_assoc (fieldActor σ δ), fieldActor_mul_compatDiagAutHom]
  group

theorem normalActor_one_right
    (u : (a : Fin t.foldedTag.rank) → (orbitField t K σ.toRingHom a)ˣ) :
    normalActor σ u (1 : RingAut K) = compatDiagAutHom t K σ.toRingHom u := by
  rw [normalActor, fieldActor_one, mul_one]

theorem normalActor_one_left
    (δ : K ≃+* K) :
    normalActor (t := t) σ 1 δ = fieldActor σ δ := by
  rw [normalActor, map_one, one_mul]

theorem normalActor_mem
    (u : (a : Fin t.foldedTag.rank) → (orbitField t K σ.toRingHom a)ˣ)
    (δ : K ≃+* K) :
    normalActor σ u δ ∈ graphFixedUnipotentStabilizer t K σ.toRingHom := by
  have hUC := graphFixedPosUnipotent_le_graphFixedRootGroup t K σ.toRingHom
  have hVC := graphFixedNegUnipotent_le_graphFixedRootGroup t K σ.toRingHom
  have hδ := ringEquiv_comm_of_finite σ δ
  have hΔ : compatDiagAutHom t K σ.toRingHom u ∈ graphFixedUnipotentStabilizer t K σ.toRingHom :=
    ⟨map_compatDiagAutHom_subgroupOf hUC u
      (map_conj_rootDiagUnit_graphFixedPosUnipotent (compatDiag_perm u)),
      map_compatDiagAutHom_subgroupOf hVC u
        (map_conj_rootDiagUnit_graphFixedNegUnipotent (compatDiag_perm u))⟩
  have hF : fieldActor σ δ ∈ graphFixedUnipotentStabilizer t K σ.toRingHom :=
    ⟨map_graphFixedEntrywiseAut_subgroupOf hδ hUC
      (map_units_map_entrywiseHom_graphFixedPosUnipotent hδ),
      map_graphFixedEntrywiseAut_subgroupOf hδ hVC
        (map_units_map_entrywiseHom_graphFixedNegUnipotent hδ)⟩
  exact mul_mem hΔ hF

end Finite

section Inner

theorem mem_normalizer_of_map_conj_subgroupOf {G : Type*} [Group G] {C X : Subgroup G}
    (hXC : X ≤ C) {h : C}
    (hmap : (X.subgroupOf C).map (MulAut.conj h).toMonoidHom = X.subgroupOf C) :
    (h : G) ∈ Subgroup.normalizer (X : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    have hx' : (⟨x, hXC hx⟩ : C) ∈ X.subgroupOf C := hx
    have hm := Subgroup.mem_map_of_mem (MulAut.conj h).toMonoidHom hx'
    rw [hmap] at hm
    exact hm
  · intro hx
    have hmem : (⟨(h : G) * x * (h : G)⁻¹, hXC hx⟩ : C) ∈ X.subgroupOf C := hx
    rw [← hmap] at hmem
    obtain ⟨y, hy, hyx⟩ := hmem
    have h1 : (h : G) * y * (h : G)⁻¹ = (h : G) * x * (h : G)⁻¹ := congrArg Subtype.val hyx
    have h2 : (y : G) = x := mul_left_cancel (mul_right_cancel h1)
    rw [← h2]
    exact hy

variable {t : TwistTag} {K : Type} [Field K] {σ : K →+* K}

theorem exists_conj_eq_compatDiagAutHom
    (hσ : Function.Surjective σ)
    {h : graphFixedRootGroup t K σ}
    (hA : MulAut.conj h ∈ graphFixedUnipotentStabilizer t K σ) :
    ∃ u, MulAut.conj h = compatDiagAutHom t K σ u := by
  obtain ⟨hU, hV⟩ := hA
  have hNU := mem_normalizer_of_map_conj_subgroupOf
    (graphFixedPosUnipotent_le_graphFixedRootGroup t K σ) hU
  have hNV := mem_normalizer_of_map_conj_subgroupOf
    (graphFixedNegUnipotent_le_graphFixedRootGroup t K σ) hV
  have hB : (h : ModGL t.tag K) ∈ graphFixedRootBorel t K σ := by
    rw [← graphFixedRootGroup_inf_normalizer_graphFixedPosUnipotent hσ]
    exact Subgroup.mem_inf.2 ⟨h.2, hNU⟩
  obtain ⟨w₀, hw₀⟩ := Finite.exists_max (coxeterSystem t.tag).length
  have hn : canonicalRep (coxeterSystem t.tag) K w₀ ∈ graphFixedRootGroup t K σ :=
    canonicalRep_mem_graphFixedRootGroup (mem_relWeylTwist_of_forall_length_le hw₀)
  have hC : (graphFixedRootGroup t K σ).map
      (MulAut.conj (canonicalRep (coxeterSystem t.tag) K w₀)).toMonoidHom =
        graphFixedRootGroup t K σ :=
    map_conj_eq_of_mem_normalizer (Subgroup.le_normalizer hn)
  have e : graphFixedRootGroup t K σ ⊓
      Subgroup.normalizer (graphFixedNegUnipotent t K σ : Set (ModGL t.tag K)) =
        (graphFixedRootBorel t K σ).map
          (MulAut.conj (canonicalRep (coxeterSystem t.tag) K w₀)).toMonoidHom := by
    rw [← graphFixedRootGroup_inf_normalizer_graphFixedPosUnipotent hσ,
      Subgroup.map_inf_eq _ _ _ (MulAut.conj _).injective, hC, Subgroup.map_equiv_normalizer_eq,
      map_conj_graphFixedPosUnipotent hw₀]
  have hB' : (h : ModGL t.tag K) ∈ (graphFixedRootBorel t K σ).map
      (MulAut.conj (canonicalRep (coxeterSystem t.tag) K w₀)).toMonoidHom := by
    rw [← e]
    exact Subgroup.mem_inf.2 ⟨h.2, hNV⟩
  have hH : (h : ModGL t.tag K) ∈ graphFixedRootTorus t K σ := by
    rw [← graphFixedRootBorel_inf_map_conj hw₀]
    exact Subgroup.mem_inf.2 ⟨hB, hB'⟩
  have hT : (h : ModGL t.tag K) ∈ torusGroup t.tag K :=
    (Subgroup.mem_inf.1 (Subgroup.mem_inf.1 hH).1).1
  have hΓ : (h : ModGL t.tag K) ∈ twistedFixedGroup t K σ :=
    (Subgroup.mem_inf.1 (Subgroup.mem_inf.1 hH).1).2
  obtain ⟨b, hb⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hT
  have hF := ((mem_twistedFixedGroup_iff_twistHom t K σ).1 hΓ).2
  rw [hb, twistHom_rootDiagUnit_eq] at hF
  have hb' : ∀ i, b (t.perm i) = Units.map σ.toMonoidHom (b i) := by
    intro i
    have h1 := congrFun (rootDiagUnit_injective hF) (t.perm i)
    rw [Equiv.symm_apply_apply] at h1
    exact h1.symm
  obtain ⟨u, hu⟩ := exists_compatDiag_eq hb'
  refine ⟨u, MulEquiv.ext fun g => Subtype.ext ?_⟩
  rw [coe_compatDiagAutHom, hu, ← hb]
  rfl

end Inner

section E6

variable {K : Type} [Field K] [Finite K]

theorem exists_normalActor_eq_E6
    {p f : ℕ} (hp : p.Prime) (hf : 1 ≤ f)
    (hK : Nat.card K = (p ^ f) ^ 2) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (p ^ f))
    {β : MulAut (graphFixedRootGroup TwistTag.E6 K σ.toRingHom)}
    (hβ : β ∈ graphFixedUnipotentStabilizer TwistTag.E6 K σ.toRingHom) :
    ∃ u δ, β = normalActor σ u δ := by
  obtain ⟨-, -, -, -, h⟩ :=
    twisted_E6_all_characteristic_common_full_field_parameters hp hf K hK σ hσ
  obtain ⟨-, P, hP, -⟩ := h β hβ
  refine ⟨P.2, P.1, graphFixedRootGroup_mulAut_ext σ.surjective (fun a c => ?_) fun a c => ?_⟩
  · rw [normalActor_fixedOrbitX]
    exact (hP a).1 c
  · rw [normalActor_fixedOrbitY]
    exact (hP a).2.1 c

theorem eq_of_normalActor_eq_E6
    {σ : K ≃+* K}
    (h0 : orbitField TwistTag.E6 K σ.toRingHom ⟨0, by decide⟩ = ⊤)
    {u v : (a : Fin TwistTag.E6.foldedTag.rank) → (orbitField TwistTag.E6 K σ.toRingHom a)ˣ}
    {δ ε : K ≃+* K} (h : normalActor σ u δ = normalActor σ v ε) : δ = ε := by
  have key : ∀ c : K,
      ((u ⟨0, by decide⟩ : orbitField TwistTag.E6 K σ.toRingHom ⟨0, by decide⟩) : K) * δ c =
        ((v ⟨0, by decide⟩ : orbitField TwistTag.E6 K σ.toRingHom ⟨0, by decide⟩) : K) * ε c := by
    intro c
    have hc : c ∈ orbitField TwistTag.E6 K σ.toRingHom ⟨0, by decide⟩ := by
      rw [h0]
      trivial
    have e := congrArg (fun φ : MulAut (graphFixedRootGroup TwistTag.E6 K σ.toRingHom) =>
      φ (fixedOrbitX TwistTag.E6 K σ.toRingHom ⟨0, by decide⟩ ⟨c, hc⟩)) h
    simp only [normalActor_fixedOrbitX] at e
    exact congrArg Subtype.val (fixedOrbitX_injective _ e)
  have h1 := key 1
  rw [map_one, map_one, mul_one, mul_one] at h1
  refine RingEquiv.ext fun c => ?_
  have h2 := key c
  rw [h1] at h2
  refine mul_left_cancel₀ ?_ h2
  exact fun h3 => (v ⟨0, by decide⟩).ne_zero (Subtype.ext h3)

end E6

end CFSG.LieType.Chevalley
