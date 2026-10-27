module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4Real
public import CFSG.LocalAnalysis.ComponentClassification.Foote5AscInv

public section

namespace CFSG.ComponentClassification.Foote5.L34Real

open CFSG Subgroup CFSG.PSL3Four CFSG.ComponentClassification.PSL3Four

variable {Y₀ : Type} [Group Y₀]

theorem exists_frame
    (hm : Blueprint.LieModel (Y₀ ⧸ center Y₀) .PSL 3 2 2) :
    ∃ q : Y₀ →* Equiv.Perm (Fin 42), (∀ y, q y ∈ S) ∧ (∀ s ∈ S, ∃ y, q y = s) ∧
      q.ker = center Y₀ := by
  have hstated : Assembly.LowTwoRank.StatedClassicalModel (Y₀ ⧸ center Y₀) .PSL 3 2 2 := by
    rcases hm with ⟨-, h⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩
    · exact h
    all_goals exact absurd h (by norm_num)
  obtain ⟨e⟩ := nonempty_equiv_of_stated _ hstated
  refine ⟨S.subtype.comp (e.toMonoidHom.comp (QuotientGroup.mk' (center Y₀))),
    fun y => (e _).2, fun s hs => ?_, ?_⟩
  · obtain ⟨y, hy⟩ := QuotientGroup.mk'_surjective (center Y₀) (e.symm ⟨s, hs⟩)
    refine ⟨y, ?_⟩
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, Subgroup.coe_subtype, hy,
      MulEquiv.apply_symm_apply]
  · ext y
    simp only [MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      Subgroup.coe_subtype, QuotientGroup.mk'_apply]
    rw [OneMemClass.coe_eq_one, EmbeddingLike.map_eq_one_iff, QuotientGroup.eq_one_iff]

variable {q : Y₀ →* Equiv.Perm (Fin 42)}

theorem conj_frame (hqS : ∀ y, q y ∈ S)
    (hqsurj : ∀ s ∈ S, ∃ y, q y = s) (hqker : q.ker = center Y₀) {c : Equiv.Perm (Fin 42)}
    (hc : c ∈ R) :
    (∀ y, ((MulAut.conj c⁻¹).toMonoidHom.comp q) y ∈ S) ∧
      (∀ s ∈ S, ∃ y, ((MulAut.conj c⁻¹).toMonoidHom.comp q) y = s) ∧
      ((MulAut.conj c⁻¹).toMonoidHom.comp q).ker = center Y₀ := by
  refine ⟨fun y => ?_, fun s hs => ?_, ?_⟩
  · simpa [MulAut.conj_apply] using conj_mem_S (R.inv_mem hc) (hqS y)
  · obtain ⟨y, hy⟩ := hqsurj _ (conj_mem_S hc hs)
    refine ⟨y, ?_⟩
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, hy, inv_inv]
    group
  · rw [← hqker]
    ext y
    simp only [MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulAut.conj_apply, inv_inv]
    constructor
    · intro h
      calc q y = c * (c⁻¹ * q y * c) * c⁻¹ := by group
        _ = 1 := by rw [h]; group
    · intro h
      rw [h]
      group

theorem map_mem_center_iff (β : MulAut Y₀) (y : Y₀) : β y ∈ center Y₀ ↔ y ∈ center Y₀ := by
  rw [mem_center_iff, mem_center_iff]
  constructor
  · intro h k
    apply β.injective
    rw [map_mul, map_mul, h]
  · intro h k
    obtain ⟨k, rfl⟩ := β.surjective k
    rw [← map_mul, ← map_mul, h]

theorem exists_realHom (hqS : ∀ y, q y ∈ S)
    (hqsurj : ∀ s ∈ S, ∃ y, q y = s) (hqker : q.ker = center Y₀) :
    ∃ ψ : MulAut Y₀ →* Equiv.Perm (Fin 42), (∀ β, ψ β ∈ R) ∧
      ∀ β y, q (β y) = ψ β * q y * (ψ β)⁻¹ := by
  choose r hrR hr using fun β : MulAut Y₀ =>
    GrSLit.L34Facts.exists_realization q hqS hqsurj β fun e => by
      rw [hqker]
      exact map_mem_center_iff β e
  have hone : r 1 = 1 := GrSLit.GrS4.realization_unique hqsurj (hrR 1) R.one_mem (hr 1)
    fun e => by simp
  have hmul : ∀ β₁ β₂, r (β₁ * β₂) = r β₁ * r β₂ := fun β₁ β₂ =>
    GrSLit.GrS4.realization_unique hqsurj (hrR (β₁ * β₂)) (R.mul_mem (hrR β₁) (hrR β₂))
      (hr (β₁ * β₂)) fun e => by
        rw [MulAut.mul_apply, hr β₁, hr β₂]
        group
  exact ⟨{ toFun := r, map_one' := hone, map_mul' := hmul }, hrR, hr⟩

variable {ψ : MulAut Y₀ →* Equiv.Perm (Fin 42)}

theorem realHom_conj (hqS : ∀ y, q y ∈ S)
    (hqsurj : ∀ s ∈ S, ∃ y, q y = s) (hψR : ∀ β, ψ β ∈ R)
    (hψ : ∀ β y, q (β y) = ψ β * q y * (ψ β)⁻¹) (c : Y₀) : ψ (MulAut.conj c) = q c :=
  GrSLit.GrS4.realization_unique hqsurj (hψR _) (S_le_R (hqS c)) (hψ (MulAut.conj c))
    fun e => by simp [MulAut.conj_apply]

theorem eq_one_of_realHom_eq_one (hperf : commutator Y₀ = ⊤) (hqker : q.ker = center Y₀)
    (hψ : ∀ β y, q (β y) = ψ β * q y * (ψ β)⁻¹) {β : MulAut Y₀} (h1 : ψ β = 1) : β = 1 := by
  ext y
  refine eq_of_mk_eq_of_perfect hperf β.toMonoidHom (fun l => ?_) y
  rw [QuotientGroup.eq, ← hqker, MonoidHom.mem_ker, map_mul, map_inv, MulEquiv.coe_toMonoidHom,
    hψ, h1]
  group

theorem mem_center_of_commute (hqker : q.ker = center Y₀)
    (hψ : ∀ β y, q (β y) = ψ β * q y * (ψ β)⁻¹) {β₁ β₂ : MulAut Y₀}
    (h : ψ β₁ * ψ β₂ = ψ β₂ * ψ β₁) (y : Y₀) :
    (β₁ * β₂ * β₁⁻¹ * β₂⁻¹) y * y⁻¹ ∈ center Y₀ := by
  have h1 : ψ (β₁ * β₂ * β₁⁻¹ * β₂⁻¹) = 1 := by
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, h]
    group
  rw [← hqker, MonoidHom.mem_ker, map_mul, map_inv, hψ, h1]
  group

end CFSG.ComponentClassification.Foote5.L34Real
