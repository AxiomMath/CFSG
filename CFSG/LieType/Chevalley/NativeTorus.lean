module

public import CFSG.LieType.Chevalley.NativeMonomial
public import Certificates.Certificate113
public import Certificates.Certificate114

public section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint.Chevalley

variable {τ : Tag} {K : Type} [Field K]

theorem xUnit_inv (i : Fin τ.rank) (c : K) : (xUnit τ K i c)⁻¹ = xUnit τ K i (-c) :=
  Units.ext (coe_xUnit_inv i c)

theorem weylElt_eq_torusElt_mul (i : Fin τ.rank) (t : Kˣ) :
    weylElt τ K i t = torusElt τ K i t * weylElt τ K i 1 := by
  have h2 : weylElt τ K i (-1) * weylElt τ K i 1 = 1 := by
    have := weylElt_inv (R := K) i (-1)
    rw [neg_neg] at this
    rw [← this, mul_inv_cancel]
  unfold torusElt
  rw [mul_assoc, h2, mul_one]

theorem yUnit_eq_mul_weylElt (i : Fin τ.rank) (u : Kˣ) :
    yUnit τ K i u = xUnit τ K i ↑u⁻¹ * torusElt τ K i (-u⁻¹) * weylElt τ K i 1 *
      xUnit τ K i ↑u⁻¹ := by
  have h1 := weylElt_eq_xUnit_mul (R := K) i (-u⁻¹)
  have h2 : (-(((-u⁻¹)⁻¹ : Kˣ) : K)) = (u : K) := by simp
  rw [h2] at h1
  rw [mul_assoc (xUnit τ K i _) (torusElt τ K i _) (weylElt τ K i 1),
    ← weylElt_eq_torusElt_mul, h1]
  have h3 : ((-u⁻¹ : Kˣ) : K) = -((u⁻¹ : Kˣ) : K) := by simp
  rw [h3]
  have h4 : xUnit τ K i ((u⁻¹ : Kˣ) : K) * xUnit τ K i (-((u⁻¹ : Kˣ) : K)) = 1 := by
    rw [← xUnit_inv, mul_inv_cancel]
  calc yUnit τ K i u
      = (xUnit τ K i ((u⁻¹ : Kˣ) : K) * xUnit τ K i (-((u⁻¹ : Kˣ) : K))) * yUnit τ K i u *
          (xUnit τ K i (-((u⁻¹ : Kˣ) : K)) * xUnit τ K i ((u⁻¹ : Kˣ) : K)) := by
        rw [h4, one_mul, ← xUnit_inv, inv_mul_cancel, mul_one]
    _ = _ := by group

theorem xOp_rootVec_neg_single' (i : Fin τ.rank) (c : K) :
    xOp τ K i c (rootVec τ K (-Pi.single i 1)) =
      rootVec τ K (-Pi.single i 1) + c • hVec τ K i + c ^ 2 • rootVec τ K (Pi.single i 1) := by
  have hne : (Pi.single i 1 : Fin τ.rank → ℤ) ≠ -Pi.single i 1 := fun h => by
    simpa using congrFun h i
  rw [rootVec_eq_single (isRoot_neg_single τ i), xOp, Finsupp.linearCombination_single,
    one_smul]
  exact (ite_eq_right hne.symm).trans (ite_eq_left rfl)

@[expose] def PreservesWeights (h : Module.End K (RootModule τ K)) : Prop :=
  ∀ a b, h (Finsupp.single b 1) a ≠ 0 → labelWt τ a = labelWt τ b

theorem PreservesWeights.apply_hVec_inr {h : Module.End K (RootModule τ K)}
    (hh : PreservesWeights h) (j : Fin τ.rank) (α : {v : Fin τ.rank → ℤ // IsRoot τ v}) :
    h (hVec τ K j) (Sum.inr α) = 0 := by
  by_contra hne
  have := hh _ _ hne
  simp only [labelWt] at this
  exact α.2.ne_zero this

theorem PreservesWeights.apply_rootVec {h : Module.End K (RootModule τ K)}
    (hh : PreservesWeights h) {α : Fin τ.rank → ℤ} (hα : IsRoot τ α) :
    h (rootVec τ K α) = h (rootVec τ K α) (Sum.inr ⟨α, hα⟩) • rootVec τ K α := by
  classical
  rw [rootVec_eq_single hα]
  ext a
  rw [Finsupp.smul_apply, Finsupp.single_apply]
  split_ifs with ha
  · subst ha
    simp
  · rw [smul_zero]
    by_contra hne
    have h1 := hh _ _ hne
    rcases a with k | ⟨β, hβ⟩
    · simp only [labelWt] at h1
      exact hα.ne_zero h1.symm
    · simp only [labelWt] at h1
      exact ha (by subst h1; rfl)

theorem exists_apply_hVec_eq_smul {h : Module.End K (RootModule τ K)} (hh : PreservesWeights h)
    (i : Fin τ.rank) {c : K} (hc : h * xOp τ K i 1 = xOp τ K i c * h) :
    ∃ μ : K, h (hVec τ K i) = μ • hVec τ K i := by
  classical
  have hr0 : rootVec τ K (-Pi.single i 1) (Sum.inr ⟨_, isRoot_neg_single τ i⟩) = 1 := by
    rw [rootVec_eq_single (isRoot_neg_single τ i)]
    simp
  have h1 := hh.apply_rootVec (isRoot_neg_single τ i)
  have h2 := hh.apply_rootVec (isRoot_single τ i)
  have key := congrArg (fun f : Module.End K (RootModule τ K) => f (rootVec τ K (-Pi.single i 1)))
    hc
  simp only [Module.End.mul_apply] at key
  rw [xOp_rootVec_neg_single', h1, map_smul, xOp_rootVec_neg_single', map_add, map_add,
    map_smul, map_smul, h1, h2, one_smul, one_pow, one_smul] at key
  refine ⟨h (rootVec τ K (-Pi.single i 1)) (Sum.inr ⟨_, isRoot_neg_single τ i⟩) * c, ?_⟩
  ext a
  have hk := congrArg (fun x : RootModule τ K => x a) key
  simp only [Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul] at hk
  rcases a with k | ⟨β, hβ⟩
  · have hr1 : rootVec τ K (-Pi.single i 1) (Sum.inl k) = 0 := by
      rw [rootVec_eq_single (isRoot_neg_single τ i)]; simp
    have hr2 : rootVec τ K (Pi.single i 1) (Sum.inl k) = 0 := by
      rw [rootVec_eq_single (isRoot_single τ i)]; simp
    simp only [hr0, hr1, hr2, mul_zero, add_zero, zero_add, mul_one] at hk
    rw [Finsupp.smul_apply, smul_eq_mul, hk]
    ring
  · rw [hh.apply_hVec_inr, Finsupp.smul_apply, hVec_eq_single]
    simp

theorem pow_card_sub_one_eq_one_of_diagonal [Finite K] {ι : Type*}
    (h : (Module.End K (ι →₀ K))ˣ)
    (hdiag : ∀ b : ι, ∃ μ : K, (h : Module.End K (ι →₀ K)) (Finsupp.single b 1) =
      μ • Finsupp.single b 1) :
    h ^ (Nat.card K - 1) = 1 := by
  classical
  have := Fintype.ofFinite K
  refine Units.ext (Finsupp.lhom_ext' fun b => LinearMap.ext_ring ?_)
  obtain ⟨μ, hμ⟩ := hdiag b
  have hμ0 : μ ≠ 0 := by
    rintro rfl
    have := congrArg (fun x => ((h⁻¹ : (Module.End K (ι →₀ K))ˣ) : Module.End K (ι →₀ K)) x) hμ
    simp only [zero_smul, map_zero] at this
    rw [← Module.End.mul_apply, Units.inv_mul, Module.End.one_apply] at this
    exact Finsupp.single_ne_zero.mpr one_ne_zero this
  have hpow : ∀ m : ℕ, ((h ^ m : (Module.End K (ι →₀ K))ˣ) : Module.End K (ι →₀ K))
      (Finsupp.single b 1) = μ ^ m • Finsupp.single b 1 := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [pow_succ, Units.val_mul, Module.End.mul_apply, hμ, map_smul, ih, smul_smul, pow_succ,
        mul_comm]
  simp only [LinearMap.comp_apply, Finsupp.lsingle_apply, Units.val_one, Module.End.one_apply]
  rw [hpow, Nat.card_eq_fintype_card, FiniteField.pow_card_sub_one_eq_one μ hμ0, one_smul]

end CFSG.LieType.Chevalley
