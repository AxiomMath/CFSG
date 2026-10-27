module

public import CFSG.HardMathSupport.Timmesfeld.LangTorus.TwoDHighType

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.LieComp

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.HardMathSupport.Timmesfeld.RootAut CFSG.HardMathSupport.Timmesfeld.LangTorus

namespace CompsPTwoDBase

variable {τ : Tag}
  {Ψ : Set (Fin τ.rank → ℤ)} {n : ℕ}

@[expose] def lift (b : Fin n → Fin τ.rank → ℤ) (x : Fin n → ℤ) : Fin τ.rank → ℤ :=
  ∑ j, x j • b j

theorem lift_single (b : Fin n → Fin τ.rank → ℤ) (i : Fin n) : lift b (Pi.single i 1) = b i := by
  simp [lift, Pi.single_apply]

theorem lift_neg (b : Fin n → Fin τ.rank → ℤ) (x : Fin n → ℤ) : lift b (-x) = -lift b x := by
  simp [lift, neg_smul, Finset.sum_neg_distrib]

theorem lift_sub (b : Fin n → Fin τ.rank → ℤ) (x y : Fin n → ℤ) :
    lift b (x - y) = lift b x - lift b y := by
  simp [lift, sub_smul, Finset.sum_sub_distrib]

theorem lift_smul (b : Fin n → Fin τ.rank → ℤ) (c : ℤ) (x : Fin n → ℤ) :
    lift b (c • x) = c • lift b x := by
  rw [lift, lift, Finset.smul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Pi.smul_apply, smul_eq_mul, smul_smul]

theorem rootLift_zero' (e : simpleRoots Ψ ≃ Fin n) : rootLift e 0 = 0 := by
  simp [rootLift, liftCoeff]

theorem rootLift_neg' (e : simpleRoots Ψ ≃ Fin n) (x : Fin n → ℤ) :
    rootLift e (-x) = -rootLift e x := by
  simp only [rootLift_eq_sum, neg_smul, Finset.sum_neg_distrib, Pi.neg_apply]

theorem iform_lift (b : Fin n → Fin τ.rank → ℤ) {M : Matrix (Fin n) (Fin n) ℤ}
    (hM : ∀ i j, iform (b i) (b j) = M i j) (x y : Fin n → ℤ) :
    iform (lift b x) (lift b y) = ∑ i, ∑ j, x i * M i j * y j := by
  rw [lift, lift, iform_sum_smul_left]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [iform_sum_smul_right, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hM]
  ring

theorem corootPair_eq_iform {u : Fin τ.rank → ℤ} (hu : IsRoot τ u) (h2 : iform u u = 2)
    (v : Fin τ.rank → ℤ) : corootPair u v = iform u v := by
  have h := corootPair_mul hu v
  rw [h2] at h
  omega

theorem lift_coordReflect (b : Fin n → Fin τ.rank → ℤ) {M : Matrix (Fin n) (Fin n) ℤ}
    (hM : ∀ i j, iform (b i) (b j) = M i j) (hroot : ∀ i, IsRoot τ (b i))
    (hdiag : ∀ i, M i i = 2) (i : Fin n) (x : Fin n → ℤ) :
    lift b (coordReflect M i x) = rootReflection (b i) • lift b x := by
  have h2 : iform (b i) (b i) = 2 := by rw [hM, hdiag]
  have hpair : corootPair (b i) (lift b x) = ∑ j, M i j * x j := by
    rw [corootPair_eq_iform (hroot i) h2, lift, iform_sum_smul_right]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hM]
    ring
  rw [rootReflection_smul (hroot i), hpair, coordReflect, lift_sub, lift_smul, lift_single]

theorem exists_weyl_base_transport (hΨ : IsRootComponent Ψ) (e : simpleRoots Ψ ≃ Fin n)
    (hsl : ∀ β ∈ Ψ, iform β β = 2) {M : Matrix (Fin n) (Fin n) ℤ}
    (he : ∀ β γ : simpleRoots Ψ, corootPair (β : Fin τ.rank → ℤ) γ = M (e β) (e γ))
    (hdiag : ∀ i, M i i = 2) (hoff : ∀ i j, i ≠ j → M i j ≠ 2)
    (b : Fin n → Fin τ.rank → ℤ) (hbΨ : ∀ i, b i ∈ Ψ) (hbM : ∀ i j, iform (b i) (b j) = M i j) :
    ∃ u ∈ componentWeylGroup Ψ, ∃ π : Equiv.Perm (Fin n), (∀ i j, M (π i) (π j) = M i j) ∧
      ∀ i, u • b i = (e.symm (π i) : Fin τ.rank → ℤ) := by
  classical
  have hsl' : ∀ β ∈ simpleRoots Ψ, iform β β = 2 := fun β hβ => hsl β (simpleRoots_subset hβ)
  have hfin : Ψ.Finite := (finite_setOf_isRoot τ).subset fun γ hγ => hΨ.isRoot γ hγ
  have hform := iform_rootLift hsl' e he
  have hbroot : ∀ i, IsRoot τ (b i) := fun i => hΨ.isRoot _ (hbΨ i)
  have hLinj : Function.Injective (lift b) := by
    intro x y hxy
    have h0 : iform (lift b (x - y)) (lift b (x - y)) = 0 := by
      rw [lift_sub, hxy, sub_self]
      exact iform_self_eq_zero_of_zero
    rw [iform_lift b hbM, ← hform] at h0
    have h1 := eq_zero_of_iform_self_eq_zero h0
    have hz : rootLift e (x - y) = rootLift e 0 := by rw [h1, rootLift_zero']
    exact sub_eq_zero.1 (rootLift_injective hΨ e hz)
  have hmemΨ : ∀ x, IsOrbitRoot M x → lift b x ∈ Ψ := by
    intro x hx
    induction hx with
    | single i =>
      rw [lift_single]
      exact hbΨ i
    | reflect i _ ih =>
      rw [lift_coordReflect b hbM hbroot hdiag]
      exact hΨ.reflection_mem _ ih _ (hbΨ i)
  have hSΨ : lift b '' {x | IsOrbitRoot M x} = Ψ := by
    refine Set.eq_of_subset_of_ncard_le ?_ ?_ hfin
    · rintro _ ⟨x, hx, rfl⟩
      exact hmemΨ x hx
    · rw [Set.ncard_image_of_injective _ hLinj, ← ncard_eq_ncard_orbit hΨ e he]
  have hcoord : ∀ γ ∈ Ψ, ∃ x, IsOrbitRoot M x ∧ lift b x = γ := by
    intro γ hγ
    rw [← hSΨ] at hγ
    obtain ⟨x, hx, rfl⟩ := hγ
    exact ⟨x, hx, rfl⟩
  let g : (Fin τ.rank → ℤ) → Fin τ.rank → ℤ := fun γ => rootLift e (Function.invFun (lift b) γ)
  have hg_lift : ∀ x, g (lift b x) = rootLift e x := fun x => by
    simp only [g, Function.leftInverse_invFun hLinj x]
  have hgmaps : ∀ γ ∈ Ψ, g γ ∈ Ψ := by
    intro γ hγ
    obtain ⟨x, hx, rfl⟩ := hcoord γ hγ
    rw [hg_lift]
    exact rootLift_mem hΨ e he hx
  have hginj : Set.InjOn g Ψ := by
    intro γ hγ γ' hγ' h
    obtain ⟨x, -, rfl⟩ := hcoord γ hγ
    obtain ⟨y, -, rfl⟩ := hcoord γ' hγ'
    rw [hg_lift, hg_lift] at h
    rw [rootLift_injective hΨ e h]
  have hiso : ∀ γ ∈ Ψ, ∀ γ' ∈ Ψ, iform (g γ) (g γ') = iform γ γ' := by
    intro γ hγ γ' hγ'
    obtain ⟨x, -, rfl⟩ := hcoord γ hγ
    obtain ⟨y, -, rfl⟩ := hcoord γ' hγ'
    rw [hg_lift, hg_lift, hform, iform_lift b hbM]
  have hgneg : ∀ γ ∈ Ψ, g (-γ) = -g γ := by
    intro γ hγ
    obtain ⟨x, -, rfl⟩ := hcoord γ hγ
    rw [← lift_neg, hg_lift, hg_lift, rootLift_neg']
  have hg : IsIsometry Ψ g :=
    ⟨(hfin.injOn_iff_bijOn_of_mapsTo hgmaps).1 hginj, hiso, hgneg⟩
  have hgb : ∀ i, g (b i) = (e.symm i : Fin τ.rank → ℤ) := fun i => by
    rw [← lift_single b i, hg_lift, rootLift_single]
  obtain ⟨w, hw, hpos⟩ := exists_mem_componentWeylGroup_posRoots hΨ hg
  have hg' := hg.comp_smul hΨ hw
  have hΔ : ∀ β ∈ simpleRoots Ψ, g (w • β) ∈ simpleRoots Ψ := fun β hβ =>
    hg'.apply_mem_simpleRoots hΨ hpos hβ
  have hΔbij : Set.BijOn (fun γ => g (w • γ)) (simpleRoots Ψ : Set (Fin τ.rank → ℤ))
      (simpleRoots Ψ : Set (Fin τ.rank → ℤ)) := by
    refine ((Finset.finite_toSet _).injOn_iff_bijOn_of_mapsTo (fun β hβ => hΔ β hβ)).1 ?_
    exact hg'.bijOn.injOn.mono (fun β hβ => simpleRoots_subset hβ)
  have hwinv : ∀ i, w⁻¹ • b i ∈ Ψ := fun i =>
    smul_mem_of_mem_componentWeylGroup hΨ (inv_mem hw) _ (hbΨ i)
  have hmemΔ : ∀ i, w⁻¹ • b i ∈ simpleRoots Ψ := by
    intro i
    obtain ⟨β, hβ, hβi⟩ := hΔbij.surjOn (show (e.symm i : Fin τ.rank → ℤ) ∈
      (simpleRoots Ψ : Set (Fin τ.rank → ℤ)) from (e.symm i).2)
    have h1 : g (w • (w⁻¹ • b i)) = (e.symm i : Fin τ.rank → ℤ) := by
      rw [smul_inv_smul, hgb]
    have h2 : w⁻¹ • b i = β :=
      hg'.bijOn.injOn (hwinv i) (simpleRoots_subset hβ) (h1.trans hβi.symm)
    rw [h2]
    exact hβ
  set π0 : Fin n → Fin n := fun i => e ⟨w⁻¹ • b i, hmemΔ i⟩ with hπ0
  have hπ0e : ∀ i, (e.symm (π0 i) : Fin τ.rank → ℤ) = w⁻¹ • b i := fun i => by
    simp only [hπ0, Equiv.symm_apply_apply]
  have hπ0M : ∀ i j, M (π0 i) (π0 j) = M i j := by
    intro i j
    have h1 := he (e.symm (π0 i)) (e.symm (π0 j))
    rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply] at h1
    rw [← h1, hπ0e, hπ0e, corootPair_eq_iform, iform_smul, hbM]
    · exact hΨ.isRoot _ (hwinv i)
    · rw [iform_smul, hbM, hdiag]
  have hπ0inj : Function.Injective π0 := by
    intro i j hij
    by_contra hne
    apply hoff i j hne
    rw [← hπ0M i j, hij, hdiag]
  refine ⟨w⁻¹, inv_mem hw, Equiv.ofBijective π0 (Finite.injective_iff_bijective.1 hπ0inj),
    hπ0M, fun i => ?_⟩
  simp only [Equiv.ofBijective_apply]
  rw [hπ0e]

end CompsPTwoDBase

end CFSG.HardMathSupport.Solomon.Coordinator.LieComp
