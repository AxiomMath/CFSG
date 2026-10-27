module

public import CFSG.ClassicalInvolution.Q3.Q3ExcSmall
public import CFSG.ClassicalInvolution.Q3.Q3ExcToral
public import CFSG.ClassicalInvolution.Q3.Q3ExcMulti

public section

namespace CFSG.ClassicalInvolution.Q3

open CFSG.Open CFSG.ClassicalInvolution CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.Chevalley CFSG.LieType.Chevalley.OrthogonalSemilinearFixedRootDatum
open scoped MatrixGroups

section Class

variable {τ : Tag} {χ : Multiplicative (Fin τ.rank → ℤ) →* ℤˣ}

theorem exc3_iform_neg_left (x y : Fin τ.rank → ℤ) : iform (-x) y = -iform x y := by
  rw [← neg_one_smul ℤ x, iform_smul_left]
  ring

theorem exc3_iform_neg_right (x y : Fin τ.rank → ℤ) : iform x (-y) = -iform x y := by
  rw [← neg_one_smul ℤ y, iform_smul_right]
  ring

theorem exc3_class_of_isolated {β₀ : Fin τ.rank → ℤ} (hβ₀ : β₀ ∈ kernelRoots χ)
    (hiso : ∀ γ ∈ kernelRoots χ, iform β₀ γ ≠ 0 → γ = β₀ ∨ γ = -β₀) :
    ∀ γ ∈ componentRoots χ ⟦⟨β₀, hβ₀⟩⟧, γ = β₀ ∨ γ = -β₀ := by
  intro γ ⟨hγ, hcls⟩
  have hQ : ∀ a b : Fin τ.rank → ℤ, (b = β₀ ∨ b = -β₀) → iform a b ≠ 0 → iform β₀ a ≠ 0 := by
    intro a b hb h
    rcases hb with rfl | rfl
    · rwa [iform_comm]
    · rw [exc3_iform_neg_right, neg_ne_zero, iform_comm] at h
      exact h
  have hQ' : ∀ a b : Fin τ.rank → ℤ, (a = β₀ ∨ a = -β₀) → iform a b ≠ 0 → iform β₀ b ≠ 0 := by
    intro a b ha h
    rcases ha with rfl | rfl
    · exact h
    · rwa [exc3_iform_neg_left, neg_ne_zero] at h
  have hstep : ∀ a b : kernelRoots χ, iform (a : Fin τ.rank → ℤ) b ≠ 0 →
      (((a : Fin τ.rank → ℤ) = β₀ ∨ (a : Fin τ.rank → ℤ) = -β₀) ↔
        ((b : Fin τ.rank → ℤ) = β₀ ∨ (b : Fin τ.rank → ℤ) = -β₀)) := by
    intro a b hab
    exact ⟨fun ha => hiso b b.2 (hQ' _ _ ha hab), fun hb => hiso a a.2 (hQ _ _ hb hab)⟩
  have hEq : ∀ a b : kernelRoots χ, (kernelRootSetoid χ).r a b →
      (((a : Fin τ.rank → ℤ) = β₀ ∨ (a : Fin τ.rank → ℤ) = -β₀) ↔
        ((b : Fin τ.rank → ℤ) = β₀ ∨ (b : Fin τ.rank → ℤ) = -β₀)) := by
    intro a b h
    induction h with
    | rel x y hxy =>
      refine hstep x y ?_
      rwa [dotProduct_mulVec_eq_iform] at hxy
    | refl x => exact Iff.rfl
    | symm x y _ ih => exact ih.symm
    | trans x y z _ _ ih1 ih2 => exact ih1.trans ih2
  exact (hEq ⟨γ, hγ⟩ ⟨β₀, hβ₀⟩ (Quotient.exact hcls)).2 (Or.inl rfl)

end Class

section Datum

variable {τ : Tag} {p₀ : ℕ} [Fact p₀.Prime] {k : Type} [Field k] [CharP k p₀] [IsAlgClosed k]
  {D : OrthogonalSemilinearFixedRootDatum τ p₀ k}

omit [CharP k p₀] in
theorem exc3_mul_self_of_mem_center_sl2 {F : Type*} [Field F] {A : SL2 F}
    (h : A ∈ Subgroup.center (SL2 F)) : A * A = 1 := by
  rw [Matrix.SpecialLinearGroup.mem_center_iff] at h
  obtain ⟨r, hr, hrA⟩ := h
  rw [Fintype.card_fin] at hr
  ext i j
  have hA : (A : Matrix (Fin 2) (Fin 2) F) = Matrix.scalar (Fin 2) r := hrA.symm
  rw [Matrix.SpecialLinearGroup.coe_mul, hA, ← map_mul, Matrix.SpecialLinearGroup.coe_one]
  rw [← pow_two, hr]
  simp

theorem exc3_rootSpanJ_singleton {J : Set.range D.classOrbit} {i : KernelComponent D.χ}
    (hJ : (J : Set (KernelComponent D.χ)) = {i}) :
    (D.withOrbit J).rootSpanJ = componentRootSpan k D.χ i := by
  show unionRootSpan k D.χ (J : Set (KernelComponent D.χ)) = componentRootSpan k D.χ i
  unfold unionRootSpan componentRootSpan
  congr 1
  ext α
  rw [mem_unionRoots_iff]
  constructor
  · rintro ⟨j, hj, hα⟩
    rw [hJ, Set.mem_singleton_iff] at hj
    rw [← hj]
    exact hα
  · intro hα
    refine ⟨i, ?_, hα⟩
    rw [hJ]
    exact Set.mem_singleton i

theorem exc3_sq_of_small_orbit (hk2 : ringChar k ≠ 2) {J₀ J₁ : Set.range D.classOrbit}
    (hne : J₀ ≠ J₁) {i : KernelComponent D.χ} (hJ₀ : (J₀ : Set (KernelComponent D.χ)) = {i})
    (hi : ¬ 2 < (componentRoots D.χ i).ncard) :
    ∀ z ∈ (D.withOrbit J₀).rootSpanJ ⊓ (D.withOrbit J₁).rootSpanJ, z * z = 1 := by
  intro z hz
  have hS := exc3_rootSpanJ_singleton hJ₀
  obtain ⟨α, hα, -, -, -, ⟨e⟩⟩ := exc3_small_class (K := k) hk2 D.χ i hi
  have hzS : z ∈ componentRootSpan k D.χ i := hS ▸ hz.1
  have hcomm : ∀ y ∈ componentRootSpan k D.χ i, y * z = z * y := fun y hy =>
    (D.commute_of_ne hne (hS ▸ hy) hz.2).eq
  have hc : e.symm ⟨z, hzS⟩ ∈ Subgroup.center (SL2 k) := by
    rw [Subgroup.mem_center_iff]
    intro A
    apply e.injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
    exact Subtype.ext (hcomm _ (e A).2)
  have h1 := exc3_mul_self_of_mem_center_sl2 hc
  have h2 : (⟨z, hzS⟩ : componentRootSpan k D.χ i) * ⟨z, hzS⟩ = 1 := by
    apply e.symm.injective
    rw [map_mul, h1, map_one]
  exact congrArg Subtype.val h2

end Datum

section Main

variable {τ : Tag} {p₀ : ℕ} [Fact p₀.Prime] {k : Type} [Field k] [CharP k p₀] [IsAlgClosed k]
  {D : OrthogonalSemilinearFixedRootDatum τ p₀ k}

theorem exc3_two_orbit_data (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {c : ModGL τ k} (hc : Exc3Frob D c) (hq3 : p₀ ^ D.e = 3)
    {χ : Multiplicative (Fin τ.rank → ℤ) →* ℤˣ} (hχ : D.χ = χ)
    {β₀ γ₁ : Fin τ.rank → ℤ} (hβ₀ : β₀ ∈ kernelRoots χ) (hγ₁ : γ₁ ∈ kernelRoots χ)
    (hiso : ∀ γ ∈ kernelRoots χ, iform β₀ γ ≠ 0 → γ = β₀ ∨ γ = -β₀)
    (hθβ₀ : D.θ (toReal β₀) = toReal β₀) (hγ₁n : γ₁ ≠ β₀ ∧ γ₁ ≠ -β₀)
    (hrest : ∀ (γ : Fin τ.rank → ℤ) (hγ : γ ∈ kernelRoots χ), γ ≠ β₀ → γ ≠ -β₀ →
      ∃ (m : ℕ) (β : Fin τ.rank → ℤ) (hβ : β ∈ kernelRoots χ),
        (D.θ ^ m) (toReal γ₁) = toReal β ∧
          (⟦⟨β, hβ⟩⟧ : KernelComponent χ) = ⟦⟨γ, hγ⟩⟧)
    (hns : (∃ γ ∈ kernelRoots χ, ∃ γ' ∈ kernelRoots χ, γ ≠ β₀ ∧ γ ≠ -β₀ ∧
        iform γ γ' = 1) ∨
      ∃ (γ₂ : Fin τ.rank → ℤ) (h₂ : γ₂ ∈ kernelRoots χ), γ₂ ≠ β₀ ∧ γ₂ ≠ -β₀ ∧
        (⟦⟨γ₂, h₂⟩⟧ : KernelComponent χ) ≠ ⟦⟨γ₁, hγ₁⟩⟧) :
    ∃ J₀ J₁ : Set.range D.classOrbit, J₀ ≠ J₁ ∧ (∀ J', J' = J₀ ∨ J' = J₁) ∧
      (∀ z ∈ (D.withOrbit J₀).rootSpanJ ⊓ (D.withOrbit J₁).rootSpanJ, z * z = 1) ∧
      (∀ J₁' J₂' : Set.range D.classOrbit, Exc3Small (D.withOrbit J₁').orbitGroup →
        Exc3Small (D.withOrbit J₂').orbitGroup → J₁' = J₂') := by
  subst hχ
  classical
  have hk2 : ringChar k ≠ 2 := D.ringChar_ne_two
  have hcJ : ∀ J' : Set.range D.classOrbit, Exc3Frob (D.withOrbit J') c := fun J' =>
    ⟨hc.frob, hc.normalizes, hc.sq_mem⟩
  set i₀ : KernelComponent D.χ := ⟦⟨β₀, hβ₀⟩⟧ with hi₀
  set i₁ : KernelComponent D.χ := ⟦⟨γ₁, hγ₁⟩⟧ with hi₁
  have hΨ₀ := isRootComponent_componentRoots (χ := D.χ) i₀
  have hβ₀i : β₀ ∈ componentRoots D.χ i₀ := ⟨hβ₀, rfl⟩
  have hnβ₀i : -β₀ ∈ componentRoots D.χ i₀ := hΨ₀.neg_mem β₀ hβ₀i
  have hcls₀ : ∀ γ ∈ componentRoots D.χ i₀, γ = β₀ ∨ γ = -β₀ := exc3_class_of_isolated hβ₀ hiso
  have hθpow : ∀ m : ℕ, (D.θ ^ m) (toReal β₀) = toReal β₀ := fun m => by
    rw [Module.End.pow_apply]
    exact Function.iterate_fixed hθβ₀ m
  have hθpm : ∀ (m : ℕ) (α : Fin τ.rank → ℤ), (α = β₀ ∨ α = -β₀) →
      ∀ β : Fin τ.rank → ℤ, (D.θ ^ m) (toReal α) = toReal β → β = β₀ ∨ β = -β₀ := by
    intro m α hα β hαβ
    rcases hα with rfl | rfl
    · rw [hθpow] at hαβ
      exact Or.inl (toReal_injective hαβ).symm
    · rw [toReal_neg, map_neg, hθpow, ← toReal_neg] at hαβ
      exact Or.inr (toReal_injective hαβ).symm
  have hmem₀ : ∀ β : Fin τ.rank → ℤ, (β = β₀ ∨ β = -β₀) → β ∈ componentRoots D.χ i₀ := by
    rintro β (rfl | rfl)
    · exact hβ₀i
    · exact hnβ₀i
  have horb₀ : D.classOrbit i₀ = {i₀} := by
    ext i
    rw [Set.mem_singleton_iff]
    constructor
    · rintro ⟨m, α, hα, β, hβ, hθ⟩
      have hβ' := hθpm m α (hcls₀ α hα) β hθ
      exact exc3_class_eq_of_mem hβ (hmem₀ β hβ')
    · rintro rfl
      exact D.self_mem_classOrbit _
  set J₀ : Set.range D.classOrbit := ⟨D.classOrbit i₀, i₀, rfl⟩ with hJ₀
  set J₁ : Set.range D.classOrbit := ⟨D.classOrbit i₁, i₁, rfl⟩ with hJ₁
  have hJ₀set : (J₀ : Set (KernelComponent D.χ)) = {i₀} := horb₀
  have hrestorb : ∀ (γ : Fin τ.rank → ℤ) (hγ : γ ∈ kernelRoots D.χ), γ ≠ β₀ → γ ≠ -β₀ →
      (⟦⟨γ, hγ⟩⟧ : KernelComponent D.χ) ∈ D.classOrbit i₁ := by
    intro γ hγ h1 h2
    obtain ⟨m, β, hβ, hθ, hcl⟩ := hrest γ hγ h1 h2
    refine ⟨m, γ₁, ⟨hγ₁, rfl⟩, β, ⟨hβ, hcl⟩, hθ⟩
  have hne₁₀ : ¬ i₁ ∈ D.classOrbit i₀ := by
    intro h
    rw [horb₀, Set.mem_singleton_iff] at h
    have : γ₁ ∈ componentRoots D.χ i₀ := by
      rw [← h]
      exact ⟨hγ₁, rfl⟩
    rcases hcls₀ γ₁ this with h' | h'
    · exact hγ₁n.1 h'
    · exact hγ₁n.2 h'
  have hne : J₀ ≠ J₁ := by
    intro h
    have h' : D.classOrbit i₀ = D.classOrbit i₁ := congrArg Subtype.val h
    exact hne₁₀ (h' ▸ D.self_mem_classOrbit i₁)
  have hall : ∀ J' : Set.range D.classOrbit, J' = J₀ ∨ J' = J₁ := by
    rintro ⟨_, i, rfl⟩
    obtain ⟨⟨γ, hγ⟩, rfl⟩ := Quotient.exists_rep i
    by_cases h : γ = β₀ ∨ γ = -β₀
    · left
      have hi : (⟦⟨γ, hγ⟩⟧ : KernelComponent D.χ) = i₀ := exc3_class_eq_of_mem ⟨hγ, rfl⟩ (hmem₀ γ h)
      exact Subtype.ext (by rw [hi])
    · right
      have h' := not_or.1 h
      have hmem := hrestorb γ hγ h'.1 h'.2
      exact Subtype.ext (D.classOrbit_eq_of_mem hmem)
  have hJ₁ns : ¬ Exc3Small (D.withOrbit J₁).orbitGroup := by
    have hJmem : ∀ (γ : Fin τ.rank → ℤ) (hγ : γ ∈ kernelRoots D.χ), γ ≠ β₀ → γ ≠ -β₀ →
        (⟦⟨γ, hγ⟩⟧ : KernelComponent D.χ) ∈ (D.withOrbit J₁).J := fun γ hγ h1 h2 =>
      hrestorb γ hγ h1 h2
    rcases hns with ⟨γ, hγ, γ', hγ', h1, h2, h3⟩ | ⟨γ₂, h₂, h1, h2, h3⟩
    · refine exc3_not_small_of_pair hτ (hcJ J₁) hq3 (hJmem γ hγ h1 h2) (γ := γ) (γ' := γ')
        ⟨hγ, rfl⟩ ⟨hγ', ?_⟩ h3
      refine mk_eq_of_iform_ne_zero (α := ⟨γ', hγ'⟩) (β := ⟨γ, hγ⟩) ?_
      change iform γ' γ ≠ 0
      rw [iform_comm, h3]
      exact one_ne_zero
    · exact exc3_not_small_of_two_classes (hcJ J₁) hq3 (hJmem γ₂ h₂ h1 h2)
        (D.self_mem_classOrbit i₁) h3
  have hsmall : ∀ J' : Set.range D.classOrbit, Exc3Small (D.withOrbit J').orbitGroup → J' = J₀ := by
    intro J' hS
    rcases hall J' with h | h
    · exact h
    · exact absurd (h ▸ hS) hJ₁ns
  have hi₀ncard : ¬ 2 < (componentRoots D.χ i₀).ncard := by
    have hsub : componentRoots D.χ i₀ ⊆ {β₀, -β₀} := fun γ hγ => hcls₀ γ hγ
    have h1 := Set.ncard_le_ncard hsub (Set.toFinite _)
    have h2 : ({β₀, -β₀} : Set (Fin τ.rank → ℤ)).ncard ≤ 2 := by
      have := Set.ncard_insert_le β₀ ({-β₀} : Set (Fin τ.rank → ℤ))
      rw [Set.ncard_singleton] at this
      exact this
    omega
  exact ⟨J₀, J₁, hne, hall, exc3_sq_of_small_orbit hk2 hne hJ₀set hi₀ncard,
    fun J₁' J₂' h1 h2 => (hsmall J₁' h1).trans (hsmall J₂' h2).symm⟩

end Main

section Structure

variable {τ : Tag} {p₀ : ℕ} [Fact p₀.Prime] {k : Type} [Field k] [CharP k p₀] [IsAlgClosed k]
  {D : OrthogonalSemilinearFixedRootDatum τ p₀ k}

theorem exc3_two_orbit_structure (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {c : ModGL τ k} (hc : Exc3Frob D c) (hq3 : p₀ ^ D.e = 3)
    {χ : Multiplicative (Fin τ.rank → ℤ) →* ℤˣ} (hχ : D.χ = χ)
    {β₀ γ₁ : Fin τ.rank → ℤ} (hβ₀ : β₀ ∈ kernelRoots χ) (hγ₁ : γ₁ ∈ kernelRoots χ)
    (hiso : ∀ γ ∈ kernelRoots χ, iform β₀ γ ≠ 0 → γ = β₀ ∨ γ = -β₀)
    (hθβ₀ : D.θ (toReal β₀) = toReal β₀) (hγ₁n : γ₁ ≠ β₀ ∧ γ₁ ≠ -β₀)
    (hrest : ∀ (γ : Fin τ.rank → ℤ) (hγ : γ ∈ kernelRoots χ), γ ≠ β₀ → γ ≠ -β₀ →
      ∃ (m : ℕ) (β : Fin τ.rank → ℤ) (hβ : β ∈ kernelRoots χ),
        (D.θ ^ m) (toReal γ₁) = toReal β ∧
          (⟦⟨β, hβ⟩⟧ : KernelComponent χ) = ⟦⟨γ, hγ⟩⟧)
    (hns : (∃ γ ∈ kernelRoots χ, ∃ γ' ∈ kernelRoots χ, γ ≠ β₀ ∧ γ ≠ -β₀ ∧
        iform γ γ' = 1) ∨
      ∃ (γ₂ : Fin τ.rank → ℤ) (h₂ : γ₂ ∈ kernelRoots χ), γ₂ ≠ β₀ ∧ γ₂ ≠ -β₀ ∧
        (⟦⟨γ₂, h₂⟩⟧ : KernelComponent χ) ≠ ⟦⟨γ₁, hγ₁⟩⟧)
    {Y : Subgroup (ModGL τ k)} [Finite Y]
    (hCY : ∀ J' : Set.range D.classOrbit, (D.withOrbit J').orbitGroup ≤ Y)
    (hY2 : ∀ y ∈ Y, y ^ 2 ∈ D.totalFixedGroup.map (adjointGroup τ k).subtype)
    (hYn : ∀ y ∈ Y, ∀ v ∈ D.totalFixedGroup.map (adjointGroup τ k).subtype,
      y * v * y⁻¹ ∈ D.totalFixedGroup.map (adjointGroup τ k).subtype) :
    (∀ N : Subgroup (ModGL τ k), N ≤ Y → (∀ y ∈ Y, ∀ n ∈ N, y * n * y⁻¹ ∈ N) →
        Odd (Nat.card N) → N = ⊥) ∧
      (∀ L : Subgroup (ModGL τ k), L ≤ Y → Nonempty (SL(2, ZMod 3) ≃* L) → IsSubnormal L Y →
        ∃ J' : Set.range D.classOrbit, Exc3Small (D.withOrbit J').orbitGroup ∧
          L = (D.withOrbit J').orbitGroup) := by
  obtain ⟨J₀, J₁, hne, hall, hsq, hone⟩ := exc3_two_orbit_data hτ hc hq3 hχ hβ₀ hγ₁ hiso hθβ₀ hγ₁n
    hrest hns
  exact exc3_multi_structure hc hq3 hone (exc3_two_orbit_exp hc hq3 hne hall hsq) hCY hY2 hYn

theorem exc3_single_class_structure (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {c : ModGL τ k} (hc : Exc3Frob D c) (hq3 : p₀ ^ D.e = 3)
    {χ : Multiplicative (Fin τ.rank → ℤ) →* ℤˣ} (hχ : D.χ = χ)
    [Subsingleton (KernelComponent χ)]
    (hnon : ∀ β ∈ kernelRoots χ, ∃ γ ∈ kernelRoots χ, iform β γ = 1)
    {Y : Subgroup (ModGL τ k)} [Finite Y]
    (hCY : ∀ J' : Set.range D.classOrbit, (D.withOrbit J').orbitGroup ≤ Y)
    (hY2 : ∀ y ∈ Y, y ^ 2 ∈ D.totalFixedGroup.map (adjointGroup τ k).subtype)
    (hYn : ∀ y ∈ Y, ∀ v ∈ D.totalFixedGroup.map (adjointGroup τ k).subtype,
      y * v * y⁻¹ ∈ D.totalFixedGroup.map (adjointGroup τ k).subtype) :
    (∀ N : Subgroup (ModGL τ k), N ≤ Y → (∀ y ∈ Y, ∀ n ∈ N, y * n * y⁻¹ ∈ N) →
        Odd (Nat.card N) → N = ⊥) ∧
      (∀ L : Subgroup (ModGL τ k), L ≤ Y → Nonempty (SL(2, ZMod 3) ≃* L) → IsSubnormal L Y →
        False) := by
  classical
  subst hχ
  have hcJ : ∀ J' : Set.range D.classOrbit, Exc3Frob (D.withOrbit J') c := fun J' =>
    ⟨hc.frob, hc.normalizes, hc.sq_mem⟩
  have hsub : ∀ J' : Set.range D.classOrbit,
      Subsingleton (KernelComponent (D.withOrbit J').χ) := fun J' =>
    inferInstanceAs (Subsingleton (KernelComponent D.χ))
  have hone : ∀ J₁ J₂ : Set.range D.classOrbit, Exc3Small (D.withOrbit J₁).orbitGroup →
      Exc3Small (D.withOrbit J₂).orbitGroup → J₁ = J₂ := by
    rintro ⟨_, i, rfl⟩ ⟨_, i', rfl⟩ - -
    rw [Subsingleton.elim i i']
  obtain ⟨i₀, hJ⟩ := D.isThetaOrbit
  set J' : Set.range D.classOrbit := ⟨D.classOrbit i₀, i₀, rfl⟩ with hJ'
  have hexpX : ∀ x ∈ D.totalFixedGroup, ∃ m : ℕ, (x : ModGL τ k) ^ (2 ^ m) ∈
      ⨆ J' : Set.range D.classOrbit, (D.withOrbit J').orbitGroup := by
    intro x hx
    have h := (hcJ J').pow_pow_mem_orbitGroupC (D := D.withOrbit J') (x := x) hx
    change (x ^ ((p₀ ^ D.e) ^ 2 - 1)) ^ ((p₀ ^ D.e) ^ 2 - 1) ∈ _ at h
    rw [hq3] at h
    refine ⟨6, ?_⟩
    have h' := Subgroup.mem_subgroupOf.1 h
    refine Subgroup.mem_iSup_of_mem J' ?_
    have e : (x : ModGL τ k) ^ (2 ^ 6) =
        (((x ^ (3 ^ 2 - 1)) ^ (3 ^ 2 - 1) : adjointGroup τ k) : ModGL τ k) := by
      rw [← pow_mul]
      norm_num
    rw [e]
    exact h'
  obtain ⟨hA, hB⟩ := exc3_multi_structure hc hq3 hone hexpX hCY hY2 hYn
  refine ⟨hA, fun L hLY hL hLs => ?_⟩
  obtain ⟨J'', hS, -⟩ := hB L hLY hL hLs
  obtain ⟨_, i₁, rfl⟩ := J''
  obtain ⟨⟨α, hα⟩, hαi⟩ := Quotient.exists_rep i₁
  obtain ⟨γ, hγ, hform⟩ := hnon α hα
  refine exc3_not_small_of_pair hτ (hcJ _) hq3 (D.self_mem_classOrbit i₁) (γ := α) (γ' := γ)
    ⟨hα, hαi⟩ ⟨hγ, ?_⟩ hform hS
  exact Subsingleton.elim _ _

end Structure

end CFSG.ClassicalInvolution.Q3
