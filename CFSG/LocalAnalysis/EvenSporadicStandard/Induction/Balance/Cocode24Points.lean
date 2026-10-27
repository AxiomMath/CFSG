module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Balance.Cocode24Mask
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Balance.Cocode24Weight
public import CFSG.LocalAnalysis.EvenSporadicStandard.Wong77.ModuleRep

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.EvenSporadicStandard.Induction.Balance.Cocode24

open Equiv CFSG.EvenSporadicStandard.Wong77
open scoped IsMulCommutative

section

variable {Γ : Type*} [Group Γ] (E : Subgroup Γ) [E.Normal] [IsMulCommutative E]
  [Module (ZMod 2) (Additive E)]

noncomputable def theta (pt : Fin 24 → E) : Word →ₗ[ZMod 2] Additive E :=
  Fintype.linearCombination (ZMod 2) fun k => Additive.ofMul (pt k)

variable {E}

omit [E.Normal] in
theorem theta_apply (pt : Fin 24 → E) (v : Word) :
    theta E pt v = ∑ k, v k • Additive.ofMul (pt k) := by
  rw [theta, Fintype.linearCombination_apply]

omit [E.Normal] in
theorem theta_single (pt : Fin 24 → E) (k : Fin 24) :
    theta E pt (Pi.single k 1) = Additive.ofMul (pt k) := by
  rw [theta_apply]
  simp [Pi.single_apply]

omit [E.Normal] in
theorem add_self_additive (x : Additive E) : x + x = 0 := by
  rw [← two_smul (ZMod 2) x]
  have : (2 : ZMod 2) = 0 := by decide
  rw [this, zero_smul]

omit [E.Normal] in
theorem pt_injective {pt : Fin 24 → E} (hrel : ∀ v : Word, theta E pt v = 0 ↔ v ∈ golay) :
    Function.Injective pt := by
  intro k k' h
  have h0 : theta E pt (Pi.single k 1 + Pi.single k' 1) = 0 := by
    rw [map_add, theta_single, theta_single, h]
    exact add_self_additive _
  have h1 : synd (Pi.single k 1 + Pi.single k' 1) = 0 := (hrel _).1 h0
  rw [map_add, synd_single, synd_single] at h1
  have h2 : col k = col k' := by
    funext j
    have := congrFun h1 j
    simp only [Pi.add_apply, Pi.zero_apply] at this
    have key : ∀ a b : ZMod 2, a + b = 0 → a = b := by decide
    exact key _ _ this
  exact col_injective h2

theorem exists_psi_of_points (pt : Fin 24 → E)
    (hconj : ∀ (g : Γ) (k : Fin 24), ∃ j, MulAut.conjNormal g (pt k) = pt j)
    (hrel : ∀ v : Word, theta E pt v = 0 ↔ v ∈ golay) (hcard : Nat.card E = 2 ^ 12) :
    ∃ ψ : Additive E ≃+ Syn, ∀ g : Γ, ∃ σ ∈ aut, ∀ x : E,
      ψ (Additive.ofMul (MulAut.conjNormal g x)) = act σ (ψ (Additive.ofMul x)) := by
  have hker : LinearMap.ker (theta E pt) = golay := by
    ext v
    exact hrel v
  have hcardA : Nat.card (Additive E) = 2 ^ 12 :=
    (Nat.card_congr (Additive.ofMul : E ≃ Additive E)).symm.trans hcard
  have hfinE : Module.finrank (ZMod 2) (Additive E) = 12 :=
    finrank_zmod_two_eq_of_natCard hcardA
  have : Finite (Additive E) := Nat.finite_of_card_ne_zero (by rw [hcardA]; positivity)
  have hrange : (theta E pt).range = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    have h := LinearMap.finrank_range_add_finrank_ker (theta E pt)
    have hkd : Module.finrank (ZMod 2) (LinearMap.ker (theta E pt)) = 12 := by
      rw [hker]
      exact finrank_golay
    simp only [Module.finrank_pi, Fintype.card_fin] at h
    rw [hkd] at h
    rw [hfinE]
    omega
  obtain ⟨r, hr⟩ := LinearMap.exists_rightInverse_of_surjective (theta E pt) hrange
  have hθr : ∀ y, theta E pt (r y) = y := fun y => LinearMap.congr_fun hr y
  obtain ⟨ψ₀, hψ₀⟩ : ∃ ψ₀ : Additive E →ₗ[ZMod 2] Syn, ∀ y, ψ₀ y = synd (r y) :=
    ⟨synd ∘ₗ r, fun _ => rfl⟩
  have hψθ : ∀ v, ψ₀ (theta E pt v) = synd v := by
    intro v
    have h1 : theta E pt (r (theta E pt v) - v) = 0 := by
      rw [map_sub, hθr, sub_self]
    have h2 : r (theta E pt v) - v ∈ golay := (hrel _).1 h1
    rw [hψ₀]
    exact LinearMap.sub_mem_ker_iff.1 h2
  have hbij : Function.Bijective ψ₀ := by
    constructor
    · rw [injective_iff_map_eq_zero]
      intro x hx
      rw [hψ₀] at hx
      have h2 : r x ∈ golay := hx
      have h3 := (hrel _).2 h2
      rw [hθr] at h3
      exact h3
    · intro s
      obtain ⟨w, hw⟩ := synd_surjective s
      exact ⟨theta E pt w, by rw [hψθ, hw]⟩
  obtain ⟨ψ, hψ⟩ : ∃ ψ : Additive E ≃ₗ[ZMod 2] Syn, ∀ y, ψ y = ψ₀ y :=
    ⟨LinearEquiv.ofBijective ψ₀ hbij, fun _ => rfl⟩
  have hpt := pt_injective hrel
  refine ⟨ψ.toAddEquiv, fun g => ?_⟩
  choose f hf using hconj g
  have hfinj : Function.Injective f := by
    intro k k' h
    apply hpt
    apply (MulAut.conjNormal g).injective
    rw [hf, hf, h]
  obtain ⟨σ, hσf⟩ : ∃ σ : Perm (Fin 24), ∀ k, σ k = f k :=
    ⟨Equiv.ofBijective f (Finite.injective_iff_bijective.1 hfinj), fun _ => rfl⟩
  have hσ : ∀ k, pt (σ k) = MulAut.conjNormal g (pt k) := fun k => by rw [hσf, hf]
  have hkey : ∀ v, theta E pt (permW σ v) = linearAut E (MulAut.conjNormal g) (theta E pt v) := by
    intro v
    rw [theta_apply, theta_apply, map_sum]
    refine (Equiv.sum_comp σ (fun k => permW σ v k • Additive.ofMul (pt k))).symm.trans ?_
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [permW_apply, show σ⁻¹ (σ j) = j by simp, map_smul, linearAut_apply, hσ]
  have hσaut : σ ∈ aut := by
    intro v
    rw [← hrel, ← hrel, hkey]
    exact (linearAut E (MulAut.conjNormal g)).map_eq_zero_iff
  refine ⟨σ, hσaut, fun x => ?_⟩
  obtain ⟨v, hv⟩ : ∃ v, theta E pt v = Additive.ofMul x := by
    have : Additive.ofMul x ∈ (theta E pt).range := by rw [hrange]; trivial
    exact this
  have h1 : Additive.ofMul (MulAut.conjNormal g x) =
      linearAut E (MulAut.conjNormal g) (theta E pt v) := by
    rw [hv, linearAut_apply]
  change ψ (Additive.ofMul (MulAut.conjNormal g x)) = act σ (ψ (Additive.ofMul x))
  rw [hψ, hψ, h1, ← hv, ← hkey, hψθ, hψθ]
  exact synd_permW σ (act_col hσaut) v

end

end CFSG.EvenSporadicStandard.Induction.Balance.Cocode24
