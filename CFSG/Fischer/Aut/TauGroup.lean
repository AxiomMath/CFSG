module

public import CFSG.Fischer.Aut.Complete
public import CFSG.Fischer.Uniq.Graph

public section

namespace CFSG.Fischer

open CFSG.Blueprint.Fischer

variable {Y : Type} [Group Y] {F : Set Y}

@[expose] def tauGroup (hP : Pair Y F) : Subgroup (Equiv.Perm F) where
  carrier := {σ | ∀ x y, σ (tauE hP x y) = tauE hP (σ x) (σ y)}
  one_mem' _ _ := rfl
  mul_mem' {σ τ} hσ hτ x y := by
    show σ (τ (tauE hP x y)) = tauE hP (σ (τ x)) (σ (τ y))
    rw [hτ, hσ]
  inv_mem' {σ} hσ x y := by
    show σ⁻¹ (tauE hP x y) = tauE hP (σ⁻¹ x) (σ⁻¹ y)
    apply σ.injective
    rw [hσ]
    simp

theorem mem_tauGroup {hP : Pair Y F} {σ : Equiv.Perm F} :
    σ ∈ tauGroup hP ↔ ∀ x y, σ (tauE hP x y) = tauE hP (σ x) (σ y) := Iff.rfl

theorem conjPerm_mem_tauGroup (hP : Pair Y F) (g : Y) : Pair.conjPerm hP g ∈ tauGroup hP :=
  fun x y => Pair.conjPerm_tauE hP g x y

@[expose] noncomputable def innerTau (hP : Pair Y F) : Y →* tauGroup hP :=
  (Pair.conjPerm hP).codRestrict (tauGroup hP) (conjPerm_mem_tauGroup hP)

theorem innerTau_apply (hP : Pair Y F) (g : Y) (x : F) :
    ((innerTau hP g : Equiv.Perm F) x : Y) = g * x * g⁻¹ := rfl

theorem innerTau_mem_apply (hP : Pair Y F) (x y : F) :
    (innerTau hP x : Equiv.Perm F) y = tauE hP x y := conjPerm_eq_tau hP x y

theorem innerTau_injective (hP : Pair Y F) (hZ : Subgroup.center Y = ⊥) :
    Function.Injective (innerTau hP) := fun _ _ h =>
  Pair.conjPerm_injective hP hZ (congrArg Subtype.val h)

theorem conj_innerTau (hP : Pair Y F) (σ : tauGroup hP) (x : F) :
    σ * innerTau hP x * σ⁻¹ = innerTau hP (((σ : Equiv.Perm F) x : F) : Y) := by
  apply Subtype.ext
  ext y
  show (((σ : Equiv.Perm F) ((innerTau hP x : Equiv.Perm F) ((σ : Equiv.Perm F)⁻¹ y)) : F) : Y) =
    (((innerTau hP (((σ : Equiv.Perm F) x : F) : Y) : Equiv.Perm F) y : F) : Y)
  rw [innerTau_mem_apply, σ.2]
  have : (σ : Equiv.Perm F) ((σ : Equiv.Perm F)⁻¹ y) = y := by
    rw [← Equiv.Perm.mul_apply, mul_inv_cancel, Equiv.Perm.one_apply]
  rw [this, ← innerTau_mem_apply]

theorem eq_one_of_commute_innerTau (hP : Pair Y F) (hZ : Subgroup.center Y = ⊥)
    {σ : tauGroup hP} (h : ∀ x : F, σ * innerTau hP x = innerTau hP x * σ) : σ = 1 := by
  apply Subtype.ext
  ext x
  have h1 := conj_innerTau hP σ x
  rw [h x, mul_inv_cancel_right] at h1
  have h2 : Pair.conjPerm hP (((σ : Equiv.Perm F) x : F) : Y) = Pair.conjPerm hP (x : Y) :=
    congrArg Subtype.val h1.symm
  exact Pair.conjPerm_injective hP hZ h2

theorem tauGroup_complete (hP : Pair Y F) (hZ : Subgroup.center Y = ⊥)
    (hperf : commutator Y = ⊤) (huniq : ∀ E : Set Y, Pair Y E → E = F)
    (hidx : (innerTau hP).range.index = 2) :
    ∀ φ : MulAut (tauGroup hP), ∃ σ : tauGroup hP, φ = MulAut.conj σ := by
  intro φ
  set I := (innerTau hP).range with hIdef
  have hI : I = commutator (tauGroup hP) := by
    apply le_antisymm
    · rw [hIdef, MonoidHom.range_eq_map, ← hperf, commutator_def, Subgroup.map_commutator,
        commutator_def]
      exact Subgroup.commutator_mono le_top le_top
    · exact commutator_le_of_index_two hidx
  have hmap : I.map (φ : tauGroup hP →* tauGroup hP) = I := by
    rw [hI]
    exact (Subgroup.characteristic_iff_map_eq.1 inferInstance) φ
  have hinj : Function.Injective (innerTau hP) := fun a b h =>
    Pair.conjPerm_injective hP hZ (congrArg Subtype.val h)
  let ψ : Y ≃* I := MonoidHom.ofInjective hinj
  have hψ : ∀ y, ((ψ y : I) : tauGroup hP) = innerTau hP y := fun y => rfl
  let φI : I ≃* I := (φ.subgroupMap I).trans (MulEquiv.subgroupCongr hmap)
  have hφI : ∀ g : I, ((φI g : I) : tauGroup hP) = φ g := fun g => rfl
  let θ : Y ≃* Y := (ψ.trans φI).trans ψ.symm
  have key1 : ∀ y : Y, φ (innerTau hP y) = innerTau hP (θ y) := by
    intro y
    have e2 : ψ (θ y) = φI (ψ y) := by simp [θ]
    calc φ (innerTau hP y) = ((φI (ψ y) : I) : tauGroup hP) := rfl
      _ = ((ψ (θ y) : I) : tauGroup hP) := by rw [e2]
      _ = innerTau hP (θ y) := rfl
  have hθF : θ '' F = F := huniq _ (pair_map hP θ)
  have hθmem : ∀ x : F, θ x ∈ F := fun x => by
    have : θ x ∈ θ '' F := ⟨x, x.2, rfl⟩
    rwa [hθF] at this
  have hθsymm : ∀ x : F, θ.symm x ∈ F := by
    intro x
    have hx : (x : Y) ∈ θ '' F := by rw [hθF]; exact x.2
    obtain ⟨z, hz, hzx⟩ := hx
    rw [← hzx, MulEquiv.symm_apply_apply]
    exact hz
  let σ₀ : Equiv.Perm F :=
    { toFun := fun x => ⟨θ x, hθmem x⟩
      invFun := fun x => ⟨θ.symm x, hθsymm x⟩
      left_inv := fun x => Subtype.ext (by simp)
      right_inv := fun x => Subtype.ext (by simp) }
  have hσ₀ : σ₀ ∈ tauGroup hP := fun x y => Subtype.ext (by
    show θ ((x : Y) * y * x) = θ x * θ y * θ x
    rw [map_mul, map_mul])
  set σ : tauGroup hP := ⟨σ₀, hσ₀⟩
  refine ⟨σ, ?_⟩
  have hagree : (φ : tauGroup hP →* tauGroup hP).comp (innerTau hP) =
      (MulAut.conj σ : tauGroup hP →* tauGroup hP).comp (innerTau hP) := by
    apply MonoidHom.eq_of_eqOn_dense hP.2.2.2.2
    intro x hx
    show φ (innerTau hP x) = σ * innerTau hP x * σ⁻¹
    rw [key1, conj_innerTau hP σ ⟨x, hx⟩]
    rfl
  set ψ' := (MulAut.conj σ)⁻¹ * φ with hψ'
  have htriv : ∀ y : Y, ψ' (innerTau hP y) = innerTau hP y := by
    intro y
    have this : φ (innerTau hP y) = MulAut.conj σ (innerTau hP y) := by
      have := congrArg (fun f : Y →* tauGroup hP => f y) hagree
      simpa using this
    rw [hψ', MulAut.mul_apply, this, MulAut.inv_apply, MulEquiv.symm_apply_apply]
  have hψ'one : ψ' = 1 := by
    refine MulEquiv.ext fun g => ?_
    have hc : g⁻¹ * ψ' g = 1 := by
      apply eq_one_of_commute_innerTau hP hZ
      intro x
      have hmem : g * innerTau hP x * g⁻¹ ∈ I := by
        have := (Subgroup.normal_of_index_eq_two hidx).conj_mem _ ⟨(x : Y), rfl⟩ g
        exact this
      obtain ⟨y, hy⟩ := hmem
      have e := htriv y
      rw [hy, map_mul, map_mul, map_inv, htriv] at e
      calc g⁻¹ * ψ' g * innerTau hP x = g⁻¹ * (ψ' g * innerTau hP x * (ψ' g)⁻¹) * ψ' g := by
            group
        _ = g⁻¹ * (g * innerTau hP x * g⁻¹) * ψ' g := by rw [e]
        _ = innerTau hP x * (g⁻¹ * ψ' g) := by group
    rw [inv_mul_eq_one] at hc
    exact hc.symm
  rw [hψ'] at hψ'one
  exact (inv_mul_eq_one.1 hψ'one).symm



theorem complete_of_tauGroup (hP : Pair Y F) (huniq : ∀ E : Set Y, Pair Y E → E = F)
    (htau : ∀ σ : tauGroup hP, σ ∈ (innerTau hP).range) :
    ∀ φ : MulAut Y, ∃ g : Y, φ = MulAut.conj g := by
  intro φ
  have hφF : φ '' F = F := huniq _ (pair_map hP φ)
  have hmem : ∀ x : F, φ x ∈ F := fun x => by
    have : φ x ∈ φ '' F := ⟨x, x.2, rfl⟩
    rwa [hφF] at this
  have hmem' : ∀ x : F, φ.symm x ∈ F := by
    intro x
    have hx : (x : Y) ∈ φ '' F := by rw [hφF]; exact x.2
    obtain ⟨z, hz, hzx⟩ := hx
    rw [← hzx, MulEquiv.symm_apply_apply]
    exact hz
  let σ₀ : Equiv.Perm F :=
    { toFun := fun x => ⟨φ x, hmem x⟩
      invFun := fun x => ⟨φ.symm x, hmem' x⟩
      left_inv := fun x => Subtype.ext (by simp)
      right_inv := fun x => Subtype.ext (by simp) }
  have hσ₀ : σ₀ ∈ tauGroup hP := fun x y => Subtype.ext (by
    show φ ((x : Y) * y * x) = φ x * φ y * φ x
    rw [map_mul, map_mul])
  obtain ⟨g, hg⟩ := htau ⟨σ₀, hσ₀⟩
  refine ⟨g, ?_⟩
  have key : (φ : Y →* Y) = (MulAut.conj g : Y →* Y) := by
    apply MonoidHom.eq_of_eqOn_dense hP.2.2.2.2
    intro x hx
    have := congrArg (fun σ : tauGroup hP => (((σ : Equiv.Perm F) ⟨x, hx⟩ : F) : Y)) hg
    simp only at this
    rw [innerTau_apply] at this
    show φ x = g * x * g⁻¹
    exact this.symm
  exact MulEquiv.ext fun y => congrArg (fun f : Y →* Y => f y) key

end CFSG.Fischer
