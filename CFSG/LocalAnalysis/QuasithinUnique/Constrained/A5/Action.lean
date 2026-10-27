module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.ActionAbs
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Basic245Single
public import CFSG.Adapters.ProjectiveSpecialLinear

public section

namespace CFSG.QuasithinUnique.A5

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.A5.Delta5
  CFSG.QuasithinUnique.A5.Action

variable {G : Type*} [Group G]

structure ModData (H L : Subgroup G) where
  α : ↥L →* Alt5
  β : ↥(blockU L) ≃* Multiplicative (evenWeight 5)
  π : ↥H →* Equiv.Perm (Fin 5)
  hα : Function.Surjective α
  hα_ker : α.ker = CFSG.pCore 2 L
  hLH : L ≤ H
  hβL : ∀ (ℓ : ↥L) (u u' : ↥(blockU L)), (u' : G) = (ℓ : G) * (u : G) * (ℓ : G)⁻¹ →
    Multiplicative.toAdd (β u') =
      vact ((α ℓ : Alt5) : Equiv.Perm (Fin 5)) (Multiplicative.toAdd (β u))
  hβ : ∀ (h : ↥H) (u u' : ↥(blockU L)), (u' : G) = (h : G) * (u : G) * (h : G)⁻¹ →
    Multiplicative.toAdd (β u') = vact (π h) (Multiplicative.toAdd (β u))
  hπL : ∀ (l : G) (hl : l ∈ L), π ⟨l, hLH hl⟩ = ((α ⟨l, hl⟩ : Alt5) : Equiv.Perm (Fin 5))
  hπψ : ∀ (h : ↥H) (l l' : ↥L), (l' : G) = (h : G) * (l : G) * (h : G)⁻¹ →
    ((α l' : Alt5) : Equiv.Perm (Fin 5)) = π h * α l * (π h)⁻¹


@[expose] def vactEquiv (σ : Equiv.Perm (Fin 5)) :
    Multiplicative (evenWeight 5) ≃* Multiplicative (evenWeight 5) where
  toFun w := Multiplicative.ofAdd (vact σ (Multiplicative.toAdd w))
  invFun w := Multiplicative.ofAdd (vact σ⁻¹ (Multiplicative.toAdd w))
  left_inv w := by
    show Multiplicative.ofAdd (vact σ⁻¹ (vact σ (Multiplicative.toAdd w))) = w
    rw [← vact_mul, inv_mul_cancel, vact_one]; rfl
  right_inv w := by
    show Multiplicative.ofAdd (vact σ (vact σ⁻¹ (Multiplicative.toAdd w))) = w
    rw [← vact_mul, mul_inv_cancel, vact_one]; rfl
  map_mul' x y := by
    show Multiplicative.ofAdd (vact σ (Multiplicative.toAdd (x * y))) =
      Multiplicative.ofAdd (vact σ (Multiplicative.toAdd x)) *
        Multiplicative.ofAdd (vact σ (Multiplicative.toAdd y))
    rw [toAdd_mul, vact_add]; rfl

theorem conjA5_apply (σ : Equiv.Perm (Fin 5)) (a : Alt5) :
    ((conjA5 σ a : Alt5) : Equiv.Perm (Fin 5)) = σ * a * σ⁻¹ := rfl

theorem conjA5_surjective (σ : Equiv.Perm (Fin 5)) : Function.Surjective (conjA5 σ) := by
  intro a
  refine ⟨conjA5 σ⁻¹ a, ?_⟩
  apply Subtype.ext
  rw [conjA5_apply, conjA5_apply]
  group

theorem conjA5_eq_one_iff (σ : Equiv.Perm (Fin 5)) (a : Alt5) : conjA5 σ a = 1 ↔ a = 1 := by
  constructor
  · intro h
    have h' := congrArg Subtype.val h
    rw [conjA5_apply] at h'
    apply Subtype.ext
    have : σ * (a : Equiv.Perm (Fin 5)) * σ⁻¹ = 1 := h'
    simpa using this
  · intro h
    rw [h, map_one]

@[expose] def ModData.conj {H L : Subgroup G} (D : ModData H L) (σ : Equiv.Perm (Fin 5)) :
    ModData H L where
  α := (conjA5 σ).comp D.α
  β := D.β.trans (vactEquiv σ)
  π := (MulAut.conj σ).toMonoidHom.comp D.π
  hα := (conjA5_surjective σ).comp D.hα
  hα_ker := by
    rw [← D.hα_ker]
    ext x
    simp only [MonoidHom.mem_ker, MonoidHom.comp_apply]
    exact conjA5_eq_one_iff σ _
  hLH := D.hLH
  hβL := by
    intro ℓ u u' h
    show vact σ (Multiplicative.toAdd (D.β u')) = _
    rw [D.hβL ℓ u u' h, ← vact_mul]
    show _ = vact (σ * (D.α ℓ : Equiv.Perm (Fin 5)) * σ⁻¹) (vact σ (Multiplicative.toAdd (D.β u)))
    rw [← vact_mul]
    congr 1
    group
  hβ := by
    intro h u u' hG
    show vact σ (Multiplicative.toAdd (D.β u')) = _
    rw [D.hβ h u u' hG, ← vact_mul]
    show _ = vact (σ * D.π h * σ⁻¹) (vact σ (Multiplicative.toAdd (D.β u)))
    rw [← vact_mul]
    congr 1
    group
  hπL := by
    intro l hl
    show σ * D.π ⟨l, D.hLH hl⟩ * σ⁻¹ = _
    rw [D.hπL l hl]
    rfl
  hπψ := by
    intro h l l' hG
    show σ * (D.α l' : Equiv.Perm (Fin 5)) * σ⁻¹ = (σ * D.π h * σ⁻¹) *
      (σ * (D.α l : Equiv.Perm (Fin 5)) * σ⁻¹) * (σ * D.π h * σ⁻¹)⁻¹
    rw [D.hπψ h l l' hG]
    group

section Glue

variable {G : Type} [Group G] [Finite G] {T M H S L : Subgroup G}

theorem blockU_le_L (hcs : ConstrainedSetting G T M H S L) : blockU L ≤ L :=
  (C1.blockU_le_blockQ (C56.isShort hcs)).trans (C1.blockQ_le L)

theorem exists_modData (hcs : ConstrainedSetting G T M H S L) (hj : conjJoin S L = L)
    (hQ : blockQ L = blockU L) (hZ : blockZ L = ⊥) (h5 : IsAltType L 5) :
    Nonempty (ModData H L) := by
  obtain ⟨α, hα, hker, β0, hβ0, hβ0ker, hβ0eq⟩ := h5
  have hLH : L ≤ H := C56.le_H hcs
  have hHL : H ≤ Subgroup.normalizer (L : Set G) := C56.H_le_normalizer hcs hj
  have hUH : blockU L ≤ H := (blockU_le_L hcs).trans hLH
  have hHU : H ≤ Subgroup.normalizer (blockU L : Set G) := fun h hh =>
    C1.mem_normalizer_blockU (hHL hh)
  have hLn : (L.subgroupOf H).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hLH).mpr hHL
  have hUn : ((blockU L).subgroupOf H).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hUH).mpr hHU
  let e1 : ↥(L.subgroupOf H) ≃* ↥L := Subgroup.subgroupOfEquivOfLe hLH
  let e2 : ↥((blockU L).subgroupOf H) ≃* ↥(blockU L) := Subgroup.subgroupOfEquivOfLe hUH
  let α' : ↥(L.subgroupOf H) →* Alt5 := α.comp e1.toMonoidHom
  have hα' : Function.Surjective α' := hα.comp e1.surjective
  have hinj : Function.Injective β0 := by
    rw [← MonoidHom.ker_eq_bot_iff, hβ0ker, hZ, Subgroup.bot_subgroupOf]
  let β0e : ↥(blockU L) ≃* Multiplicative (evenWeight 5) := MulEquiv.ofBijective β0 ⟨hinj, hβ0⟩
  let β' : ↥((blockU L).subgroupOf H) ≃* Multiplicative (evenWeight 5) := e2.trans β0e
  have hvact : ∀ (σ : Equiv.Perm (Fin 5)) (w : evenWeight 5) (i : Fin 5),
      ((vact σ w : evenWeight 5) : Fin 5 → ZMod 2) i = (w : Fin 5 → ZMod 2) (σ⁻¹ i) :=
    fun _ _ _ => rfl
  have hβLeq : ∀ (ℓ : ↥L) (u u' : ↥(blockU L)), (u' : G) = (ℓ : G) * (u : G) * (ℓ : G)⁻¹ →
      Multiplicative.toAdd (β0e u') =
        vact ((α ℓ : Alt5) : Equiv.Perm (Fin 5)) (Multiplicative.toAdd (β0e u)) := by
    intro ℓ u u' h
    apply Subtype.ext
    funext i
    rw [hvact]
    exact hβ0eq ℓ u u' h i
  have hmem : ∀ x : ↥L, x ∈ CFSG.pCore 2 L ↔ (x : G) ∈ blockU L := by
    intro x
    rw [← hQ]
    show x ∈ CFSG.pCore 2 L ↔ (x : G) ∈ pCoreOf 2 L
    unfold pCoreOf
    exact (Subgroup.mem_map_iff_mem L.subtype_injective).symm
  have hker' : ∀ ℓ : ↥(L.subgroupOf H), α' ℓ = 1 ↔ (ℓ : ↥H) ∈ (blockU L).subgroupOf H := by
    intro ℓ
    show α (e1 ℓ) = 1 ↔ _
    rw [← MonoidHom.mem_ker, hker, hmem, Subgroup.mem_subgroupOf]
    rfl
  have hβ' : ∀ (ℓ : ↥(L.subgroupOf H)) (u u' : ↥((blockU L).subgroupOf H)),
      (u' : ↥H) = (ℓ : ↥H) * (u : ↥H) * (ℓ : ↥H)⁻¹ →
      Multiplicative.toAdd (β' u') =
        vact ((α' ℓ : Alt5) : Equiv.Perm (Fin 5)) (Multiplicative.toAdd (β' u)) := by
    intro ℓ u u' h
    have hG : ((e2 u' : ↥(blockU L)) : G) =
        ((e1 ℓ : ↥L) : G) * ((e2 u : ↥(blockU L)) : G) * ((e1 ℓ : ↥L) : G)⁻¹ := by
      have := congrArg Subtype.val h
      simp only [Subgroup.coe_mul, Subgroup.coe_inv] at this
      exact this
    exact hβLeq (e1 ℓ) (e2 u) (e2 u') hG
  obtain ⟨π', hπ'c, hπ'α, hπ'ψ⟩ :=
    exists_pi (L.subgroupOf H) ((blockU L).subgroupOf H) α' hα' hker' β' hβ'
  refine ⟨{ α := α, β := β0e, π := π', hα := hα, hα_ker := hker, hLH := hLH,
            hβL := hβLeq, hβ := ?_, hπL := ?_, hπψ := ?_ }⟩
  · intro h u u' hG
    have h1 := hπ'c h (e2.symm u) (e2.symm u') (by
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      exact hG)
    have e3 : β' (e2.symm u) = β0e u := by
      show β0e (e2 (e2.symm u)) = _
      rw [MulEquiv.apply_symm_apply]
    have e4 : β' (e2.symm u') = β0e u' := by
      show β0e (e2 (e2.symm u')) = _
      rw [MulEquiv.apply_symm_apply]
    rw [e3, e4] at h1
    exact h1
  · intro l hl
    exact hπ'α ⟨⟨l, hLH hl⟩, Subgroup.mem_subgroupOf.mpr hl⟩
  · intro h l l' hG
    have h1 := hπ'ψ h (e1.symm l) (e1.symm l') (by
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      exact hG)
    have e3 : α' (e1.symm l) = α l := by
      show α (e1 (e1.symm l)) = _
      rw [MulEquiv.apply_symm_apply]
    have e4 : α' (e1.symm l') = α l' := by
      show α (e1 (e1.symm l')) = _
      rw [MulEquiv.apply_symm_apply]
    rw [e3, e4] at h1
    exact h1

end Glue

end CFSG.QuasithinUnique.A5
