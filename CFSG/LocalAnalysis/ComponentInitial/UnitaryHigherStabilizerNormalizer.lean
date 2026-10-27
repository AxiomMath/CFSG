module

public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms

public section

namespace CFSG.LocalAnalysis.ComponentInitial.StabilizerNormalizer

open MulAction CFSG.ComponentClassification.OuterAutomorphisms

variable {G Ω : Type*} [Group G] [MulAction G Ω]

theorem toPermHom_injective [FaithfulSMul G Ω] : Function.Injective (toPermHom G Ω) :=
  toPerm_injective

@[expose] noncomputable def stabPermFun (hinv : ∀ (α : MulAut G) (ω : Ω), ∃ ω' : Ω,
      (stabilizer G ω).map α.toMonoidHom = stabilizer G ω') (α : MulAut G) (ω : Ω) : Ω :=
  (hinv α ω).choose

variable (hinj : Function.Injective (stabilizer G : Ω → Subgroup G))
  (hinv : ∀ (α : MulAut G) (ω : Ω), ∃ ω' : Ω,
    (stabilizer G ω).map α.toMonoidHom = stabilizer G ω')

theorem map_stabilizer_stabPermFun (α : MulAut G) (ω : Ω) :
    (stabilizer G ω).map α.toMonoidHom = stabilizer G (stabPermFun hinv α ω) :=
  (hinv α ω).choose_spec

include hinj in
theorem stabPermFun_eq_iff {α : MulAut G} {ω ω' : Ω} :
    stabPermFun hinv α ω = ω' ↔ (stabilizer G ω).map α.toMonoidHom = stabilizer G ω' := by
  constructor
  · rintro rfl
    exact map_stabilizer_stabPermFun hinv α ω
  · intro h
    exact hinj ((map_stabilizer_stabPermFun hinv α ω).symm.trans h)

include hinj in
theorem stabPermFun_mul (α β : MulAut G) (ω : Ω) :
    stabPermFun hinv (α * β) ω = stabPermFun hinv α (stabPermFun hinv β ω) := by
  rw [stabPermFun_eq_iff hinj hinv, ← map_stabilizer_stabPermFun hinv α,
    ← map_stabilizer_stabPermFun hinv β, Subgroup.map_map]
  rfl

include hinj in
theorem stabPermFun_one (ω : Ω) : stabPermFun hinv 1 ω = ω := by
  rw [stabPermFun_eq_iff hinj hinv]
  ext x
  simp

@[expose] noncomputable def stabPerm : MulAut G →* Equiv.Perm Ω where
  toFun α :=
    { toFun := stabPermFun hinv α
      invFun := stabPermFun hinv α⁻¹
      left_inv := fun ω => by
        rw [← stabPermFun_mul hinj hinv, inv_mul_cancel, stabPermFun_one hinj hinv]
      right_inv := fun ω => by
        rw [← stabPermFun_mul hinj hinv, mul_inv_cancel, stabPermFun_one hinj hinv] }
  map_one' := Equiv.ext (stabPermFun_one hinj hinv)
  map_mul' α β := Equiv.ext (stabPermFun_mul hinj hinv α β)

theorem map_stabilizer_stabPerm (α : MulAut G) (ω : Ω) :
    (stabilizer G ω).map α.toMonoidHom = stabilizer G (stabPerm hinj hinv α ω) :=
  map_stabilizer_stabPermFun hinv α ω

theorem eq_stabPerm_iff (α : MulAut G) (π : Equiv.Perm Ω) :
    π = stabPerm hinj hinv α ↔
      ∀ ω, (stabilizer G ω).map α.toMonoidHom = stabilizer G (π ω) := by
  constructor
  · rintro rfl
    exact map_stabilizer_stabPerm hinj hinv α
  · intro h
    exact Equiv.ext fun ω => ((stabPermFun_eq_iff hinj hinv).mpr (h ω)).symm

theorem stabPerm_smul (α : MulAut G) (g : G) (ω : Ω) :
    stabPerm hinj hinv α (g • ω) = α g • stabPerm hinj hinv α ω := by
  apply hinj
  rw [← map_stabilizer_stabPerm, stabilizer_smul_eq_stabilizer_map_conj,
    stabilizer_smul_eq_stabilizer_map_conj, ← map_stabilizer_stabPerm, Subgroup.map_map,
    Subgroup.map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply]

theorem stabPerm_conj (α : MulAut G) (g : G) :
    stabPerm hinj hinv α * toPermHom G Ω g * (stabPerm hinj hinv α)⁻¹ =
      toPermHom G Ω (α g) := by
  refine Equiv.ext fun ω => ?_
  obtain ⟨ω', rfl⟩ := (stabPerm hinj hinv α).surjective ω
  rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, Equiv.Perm.inv_def, Equiv.symm_apply_apply,
    toPermHom_apply, toPermHom_apply, toPerm_apply, toPerm_apply, stabPerm_smul]

theorem stabPerm_conj_eq (g : G) : stabPerm hinj hinv (MulAut.conj g) = toPermHom G Ω g := by
  refine ((eq_stabPerm_iff hinj hinv _ _).mpr fun ω => ?_).symm
  rw [toPermHom_apply, toPerm_apply, stabilizer_smul_eq_stabilizer_map_conj]

theorem stabPerm_mem_normalizer (α : MulAut G) :
    stabPerm hinj hinv α ∈
      Subgroup.normalizer ((toPermHom G Ω).range : Set (Equiv.Perm Ω)) := by
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · rintro ⟨g, rfl⟩
    exact ⟨α g, (stabPerm_conj hinj hinv α g).symm⟩
  · rintro ⟨g, hg⟩
    refine ⟨α⁻¹ g, ?_⟩
    have := stabPerm_conj hinj hinv α⁻¹ g
    rw [map_inv, inv_inv, hg] at this
    rw [← this]
    group

theorem stabPerm_injective [FaithfulSMul G Ω] : Function.Injective (stabPerm hinj hinv) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro α hα
  rw [MonoidHom.mem_ker] at hα
  refine (Subgroup.mem_bot).mpr (MulEquiv.ext fun g => ?_)
  apply toPermHom_injective (G := G) (Ω := Ω)
  have := stabPerm_conj hinj hinv α g
  rw [hα, one_mul, inv_one, mul_one] at this
  exact this.symm

omit hinj hinv in
@[expose] noncomputable def normalizerAut [FaithfulSMul G Ω] (π : Equiv.Perm Ω)
    (hπ : π ∈ Subgroup.normalizer ((toPermHom G Ω).range : Set (Equiv.Perm Ω))) : MulAut G :=
  have hmap : (toPermHom G Ω).range.map (MulAut.conj π).toMonoidHom = (toPermHom G Ω).range := by
    ext x
    rw [Subgroup.mem_map_equiv, (Subgroup.mem_normalizer_iff.mp hπ) ((MulAut.conj π).symm x),
      MulAut.conj_symm_apply, show π * (π⁻¹ * x * π) * π⁻¹ = x by group]
  ((MonoidHom.ofInjective toPermHom_injective).trans
    (((MulAut.conj π).subgroupMap (toPermHom G Ω).range).trans
    (MulEquiv.subgroupCongr hmap))).trans (MonoidHom.ofInjective toPermHom_injective).symm

omit hinj hinv in
theorem toPermHom_normalizerAut [FaithfulSMul G Ω] (π : Equiv.Perm Ω)
    (hπ : π ∈ Subgroup.normalizer ((toPermHom G Ω).range : Set (Equiv.Perm Ω))) (g : G) :
    toPermHom G Ω (normalizerAut π hπ g) = π * toPermHom G Ω g * π⁻¹ := by
  rw [normalizerAut]
  simp only [MulEquiv.trans_apply]
  rw [MonoidHom.apply_ofInjective_symm]
  rfl

theorem range_stabPerm [FaithfulSMul G Ω] :
    (stabPerm hinj hinv).range =
      Subgroup.normalizer ((toPermHom G Ω).range : Set (Equiv.Perm Ω)) := by
  apply le_antisymm
  · rintro _ ⟨α, rfl⟩
    exact stabPerm_mem_normalizer hinj hinv α
  · intro π hπ
    refine ⟨normalizerAut π hπ, ((eq_stabPerm_iff hinj hinv _ π).mpr fun ω => ?_).symm⟩
    ext x
    rw [Subgroup.mem_map_equiv, mem_stabilizer_iff, mem_stabilizer_iff]
    have key := congrArg (fun σ : Equiv.Perm Ω => σ (π ω))
      (toPermHom_normalizerAut π hπ ((normalizerAut π hπ).symm x))
    simp only [MulEquiv.apply_symm_apply, Equiv.Perm.mul_apply, Equiv.Perm.inv_def,
      Equiv.symm_apply_apply, toPermHom_apply, toPerm_apply] at key
    constructor
    · intro hx
      rw [key, hx]
    · intro hx
      rw [hx] at key
      exact (π.injective key).symm

@[expose] noncomputable def stabPermEquiv [FaithfulSMul G Ω] :
    MulAut G ≃* Subgroup.normalizer ((toPermHom G Ω).range : Set (Equiv.Perm Ω)) :=
  (MonoidHom.ofInjective (stabPerm_injective hinj hinv)).trans
    (MulEquiv.subgroupCongr (range_stabPerm hinj hinv))

theorem coe_stabPermEquiv [FaithfulSMul G Ω] (α : MulAut G) :
    (stabPermEquiv hinj hinv α : Equiv.Perm Ω) = stabPerm hinj hinv α :=
  rfl

theorem map_inner_stabPerm : (inner G).map (stabPerm hinj hinv) = (toPermHom G Ω).range := by
  rw [CFSG.ComponentClassification.OuterAutomorphisms.inner, MonoidHom.map_range]
  congr 1
  exact MonoidHom.ext fun g => stabPerm_conj_eq hinj hinv g

theorem map_inner_stabPermEquiv [FaithfulSMul G Ω] :
    (inner G).map (stabPermEquiv hinj hinv : MulAut G →* _) =
      (toPermHom G Ω).range.subgroupOf
        (Subgroup.normalizer ((toPermHom G Ω).range : Set (Equiv.Perm Ω))) := by
  ext y
  rw [Subgroup.mem_subgroupOf]
  constructor
  · rintro ⟨α, hα, rfl⟩
    exact (map_inner_stabPerm hinj hinv).le ⟨α, hα, rfl⟩
  · intro hy
    obtain ⟨α, hα, hy'⟩ := (map_inner_stabPerm hinj hinv).ge hy
    exact ⟨α, hα, Subtype.ext hy'⟩

@[expose] noncomputable def stabPermOuterEquiv [FaithfulSMul G Ω] :
    Outer G ≃* Subgroup.normalizer ((toPermHom G Ω).range : Set (Equiv.Perm Ω)) ⧸
      (toPermHom G Ω).range.subgroupOf
        (Subgroup.normalizer ((toPermHom G Ω).range : Set (Equiv.Perm Ω))) :=
  QuotientGroup.congr (inner G) _ (stabPermEquiv hinj hinv) (map_inner_stabPermEquiv hinj hinv)

theorem stabPermOuterEquiv_mk [FaithfulSMul G Ω] (α : MulAut G) :
    stabPermOuterEquiv hinj hinv (α : Outer G) =
      ((stabPermEquiv hinj hinv α : Subgroup.normalizer
        ((toPermHom G Ω).range : Set (Equiv.Perm Ω))) : _ ⧸ _) :=
  QuotientGroup.congr_mk _ _ _ _ α

theorem faithful_stabilizer_permutation_normalizer [FaithfulSMul G Ω] :
    Function.Injective (toPermHom G Ω) ∧
    (∀ (α : MulAut G) (π : Equiv.Perm Ω), π = stabPerm hinj hinv α ↔
      ∀ ω, (stabilizer G ω).map α.toMonoidHom = stabilizer G (π ω)) ∧
    Function.Injective (stabPerm hinj hinv) ∧
    (stabPerm hinj hinv).range =
      Subgroup.normalizer ((toPermHom G Ω).range : Set (Equiv.Perm Ω)) ∧
    (∀ α : MulAut G, (stabPermEquiv hinj hinv α : Equiv.Perm Ω) = stabPerm hinj hinv α) ∧
    (∀ (α : MulAut G) (g : G), stabPerm hinj hinv α * toPermHom G Ω g *
      (stabPerm hinj hinv α)⁻¹ = toPermHom G Ω (α g)) ∧
    (inner G).map (stabPerm hinj hinv) = (toPermHom G Ω).range ∧
    ∀ α : MulAut G, stabPermOuterEquiv hinj hinv (α : Outer G) =
      ((stabPermEquiv hinj hinv α : Subgroup.normalizer
        ((toPermHom G Ω).range : Set (Equiv.Perm Ω))) : _ ⧸ _) :=
  ⟨toPermHom_injective, eq_stabPerm_iff hinj hinv, stabPerm_injective hinj hinv,
    range_stabPerm hinj hinv, coe_stabPermEquiv hinj hinv, stabPerm_conj hinj hinv,
    map_inner_stabPerm hinj hinv, stabPermOuterEquiv_mk hinj hinv⟩

end CFSG.LocalAnalysis.ComponentInitial.StabilizerNormalizer
