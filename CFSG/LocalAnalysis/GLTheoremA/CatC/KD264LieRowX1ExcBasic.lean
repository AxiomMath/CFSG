module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowX2E6TTrans

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie.X1Exc

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
open CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.LieType.AlgebraicGroups
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.LocalAnalysis.GLTheoremA.KD264Lie.X2E6.T
open CFSG.HardMathSupport.Lang.E6Descent
open scoped Matrix

section Theta

variable {Ω : Type} [Field Ω]

theorem theta_zero' (ζ : Ωˣ) : DiagTorus.theta ζ 0 = 1 := by
  simp [DiagTorus.theta]

theorem theta_add' {ζ : Ωˣ} (hζ : ζ ^ 3 = 1) (a b : ZMod 3) :
    DiagTorus.theta ζ (a + b) = DiagTorus.theta ζ a * DiagTorus.theta ζ b := by
  unfold DiagTorus.theta
  rw [ZMod.val_add, ← pow_add]
  exact (pow_eq_pow_mod _ hζ).symm

theorem theta_zpow' {ζ : Ωˣ} (hζ : ζ ^ 3 = 1) (a : ZMod 3) (n : ℤ) :
    DiagTorus.theta ζ a ^ n = DiagTorus.theta ζ ((n : ZMod 3) * a) := by
  let θ : Multiplicative (ZMod 3) →* Ωˣ :=
    { toFun := fun a => DiagTorus.theta ζ (Multiplicative.toAdd a)
      map_one' := theta_zero' ζ
      map_mul' := fun _ _ => theta_add' hζ _ _ }
  have h := map_zpow θ (Multiplicative.ofAdd a) n
  rw [← ofAdd_zsmul, zsmul_eq_mul] at h
  exact h.symm

theorem theta_sum' {ζ : Ωˣ} (hζ : ζ ^ 3 = 1) {ι : Type*} (s : Finset ι) (f : ι → ZMod 3) :
    DiagTorus.theta ζ (∑ i ∈ s, f i) = ∏ i ∈ s, DiagTorus.theta ζ (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [theta_zero']
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, theta_add' hζ, ih]

theorem theta_injective' {ζ : Ωˣ} (hζ : orderOf ζ = 3) :
    Function.Injective (DiagTorus.theta ζ) := by
  intro a b h
  unfold DiagTorus.theta at h
  rw [pow_inj_mod, hζ, Nat.mod_eq_of_lt (ZMod.val_lt a), Nat.mod_eq_of_lt (ZMod.val_lt b)] at h
  exact ZMod.val_injective 3 h

end Theta

section Character

variable {τ : Tag} {Ω : Type} [Field Ω]

@[expose] def dotT (u : Fin τ.rank → ZMod 3) (x : Fin τ.rank → ℤ) : ZMod 3 :=
  ∑ i, (x i : ZMod 3) * u i

@[expose] def thetaTupleG (τ : Tag) (ζ : Ωˣ) (u : Fin τ.rank → ZMod 3) : Fin τ.rank → Ωˣ :=
  fun i => DiagTorus.theta ζ (u i)

theorem rootChar_thetaTupleG {ζ : Ωˣ} (hζ : ζ ^ 3 = 1) (u : Fin τ.rank → ZMod 3)
    (x : Fin τ.rank → ℤ) :
    rootChar (thetaTupleG τ ζ u) x = DiagTorus.theta ζ (dotT u x) := by
  unfold rootChar dotT thetaTupleG
  rw [theta_sum' hζ]
  exact Finset.prod_congr rfl fun i _ => theta_zpow' hζ _ _

theorem rootChar_thetaTupleG_eq_one_iff {ζ : Ωˣ} (hζ : ζ ^ 3 = 1) (hζ' : orderOf ζ = 3)
    (u : Fin τ.rank → ZMod 3) (γ : Fin τ.rank → ℤ) :
    rootChar (thetaTupleG τ ζ u) γ = 1 ↔ dotT u γ = 0 := by
  rw [rootChar_thetaTupleG hζ, ← theta_zero' ζ, (theta_injective' hζ').eq_iff]

theorem thetaTupleG_pow_three {ζ : Ωˣ} (hζ : ζ ^ 3 = 1) (u : Fin τ.rank → ZMod 3)
    (i : Fin τ.rank) : thetaTupleG τ ζ u i ^ 3 = 1 := by
  show (DiagTorus.theta ζ (u i)) ^ 3 = 1
  unfold DiagTorus.theta
  rw [← pow_mul, mul_comm, pow_mul, hζ, one_pow]

theorem mem_kernelRoots_thetaTupleG_iff {ζ : Ωˣ} (hζ : ζ ^ 3 = 1) (hζ' : orderOf ζ = 3)
    (u : Fin τ.rank → ZMod 3) (γ : Fin τ.rank → ℤ) :
    γ ∈ kernelRoots (rootCharHom (thetaTupleG τ ζ u)) ↔ IsRoot τ γ ∧ dotT u γ = 0 := by
  rw [kernelRoots_rootCharHom]
  exact and_congr Iff.rfl (rootChar_thetaTupleG_eq_one_iff hζ hζ' u γ)

end Character

section Connected

theorem reflTransGen_of_ordering {α : Type*} [Inhabited α] (r : α → α → Prop) [Std.Symm r]
    (l : List α)
    (h : ∀ j : ℕ, 0 < j → j < l.length →
      ∃ i : ℕ, i < j ∧ r (l.getD i default) (l.getD j default)) :
    ∀ x ∈ l, ∀ y ∈ l, Relation.ReflTransGen r x y := by
  have hl0 : ∀ j, j < l.length →
      Relation.ReflTransGen r (l.getD 0 default) (l.getD j default) := by
    intro j
    induction j using Nat.strong_induction_on with
    | _ j ih =>
      intro hj
      rcases Nat.eq_zero_or_pos j with rfl | hjpos
      · exact Relation.ReflTransGen.refl
      · obtain ⟨i, hij, hr⟩ := h j hjpos hj
        exact (ih i hij (by omega)).tail hr
  intro x hx y hy
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hx
  obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.1 hy
  have hi' := hl0 i hi
  have hj' := hl0 j hj
  rw [List.getD_eq_getElem _ _ hi] at hi'
  rw [List.getD_eq_getElem _ _ hj] at hj'
  exact (Std.Symm.symm _ _ hi').trans hj'

end Connected

section Component

variable
  {τ : Tag} {M : Type*} [CommGroup M]

theorem componentRoots_eq_of_closed (χ : Multiplicative (Fin τ.rank → ℤ) →* M)
    (P : Set (Fin τ.rank → ℤ)) (hP : P ⊆ kernelRoots χ)
    (hconn : ∀ x ∈ P, ∀ y ∈ P, Relation.ReflTransGen (KerAdj χ) x y)
    (hclosed : ∀ x ∈ P, ∀ y ∈ kernelRoots χ, iform x y ≠ 0 → y ∈ P)
    {x₀ : Fin τ.rank → ℤ} (hx₀ : x₀ ∈ P) :
    componentRoots χ (⟦⟨x₀, hP hx₀⟩⟧ : KernelComponent χ) = P := by
  ext y
  rw [mem_componentRoots_iff χ ⟨x₀, hP hx₀⟩ y]
  constructor
  · rintro ⟨hy, hr⟩
    have key : ∀ z, Relation.ReflTransGen (KerAdj χ) x₀ z → z ∈ P := by
      intro z hz
      induction hz with
      | refl => exact hx₀
      | tail _ hstep ih => exact hclosed _ ih _ hstep.2.1 hstep.2.2
    exact key y hr
  · intro hy
    exact ⟨hP hy, hconn x₀ hx₀ y hy⟩

end Component

section Rank

variable {τ : Tag}

theorem le_compRank_of_cert {Ψ : Set (Fin τ.rank → ℤ)} {k : ℕ} (B P : Fin k → Fin τ.rank → ℤ)
    (N : ℤ) (hN : N ≠ 0) (hB : ∀ j, B j ∈ Ψ)
    (hP : ∀ i j, ∑ l, P i l * B j l = if i = j then N else 0) : k ≤ compRank Ψ := by
  classical
  set v : Fin k → (Fin τ.rank → ℚ) := fun j l => (B j l : ℚ) with hv
  have hli : LinearIndependent ℚ v := by
    rw [Fintype.linearIndependent_iff]
    intro c hc i
    have h1 := congrArg (fun x : Fin τ.rank → ℚ => ∑ l, (P i l : ℚ) * x l) hc
    have h2 : ∑ l, (P i l : ℚ) * (∑ j, c j • v j) l = (c i) * (N : ℚ) := by
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hv]
      calc ∑ l, (P i l : ℚ) * ∑ j, c j * (B j l : ℚ)
          = ∑ j, c j * ∑ l, (P i l : ℚ) * (B j l : ℚ) := by
            simp only [Finset.mul_sum]
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => by ring
        _ = ∑ j, c j * (if i = j then (N : ℚ) else 0) := by
            refine Finset.sum_congr rfl fun j _ => ?_
            congr 1
            have := hP i j
            have h3 : ((∑ l, P i l * B j l : ℤ) : ℚ) = ((if i = j then N else 0 : ℤ) : ℚ) :=
              congrArg _ this
            push_cast at h3
            by_cases hij : i = j <;> simp [hij] at h3 ⊢ <;> exact h3
        _ = c i * N := by simp
    simp only [Pi.zero_apply, mul_zero, Finset.sum_const_zero] at h1
    rw [h2] at h1
    have hN' : (N : ℚ) ≠ 0 := by exact_mod_cast hN
    exact (mul_eq_zero.1 h1).resolve_right hN'
  have hspan : Module.finrank ℚ (Submodule.span ℚ (Set.range v)) = k := by
    rw [finrank_span_eq_card hli, Fintype.card_fin]
  have hle : Submodule.span ℚ (Set.range v) ≤ Submodule.span ℚ
      ((fun γ (i : Fin τ.rank) => (γ i : ℚ)) '' Ψ) := by
    refine Submodule.span_mono ?_
    rintro _ ⟨j, rfl⟩
    exact ⟨B j, hB j, rfl⟩
  calc k = Module.finrank ℚ (Submodule.span ℚ (Set.range v)) := hspan.symm
    _ ≤ compRank Ψ := Submodule.finrank_mono hle

theorem compRank_succ_le_of_relation {Ψ : Set (Fin τ.rank → ℤ)} (ℓ : Fin τ.rank → ℤ)
    (hℓ : ℓ ≠ 0) (h : ∀ γ ∈ Ψ, ∑ l, ℓ l * γ l = 0) : compRank Ψ + 1 ≤ τ.rank := by
  classical
  let f : (Fin τ.rank → ℚ) →ₗ[ℚ] ℚ := ∑ l, (ℓ l : ℚ) • LinearMap.proj l
  have hf : ∀ x, f x = ∑ l, (ℓ l : ℚ) * x l := by
    intro x
    simp [f]
  have hfne : f ≠ 0 := by
    intro h0
    apply hℓ
    funext l
    have := congrArg (fun g : (Fin τ.rank → ℚ) →ₗ[ℚ] ℚ => g (Pi.single l 1)) h0
    simp only [hf, LinearMap.zero_apply] at this
    rw [Finset.sum_eq_single l (fun b _ hb => by simp [Pi.single_apply, hb])
      (fun hl => absurd (Finset.mem_univ l) hl)] at this
    simpa using this
  have hle : Submodule.span ℚ ((fun γ (i : Fin τ.rank) => (γ i : ℚ)) '' Ψ) ≤ LinearMap.ker f := by
    rw [Submodule.span_le]
    rintro _ ⟨γ, hγ, rfl⟩
    show f _ = 0
    rw [hf]
    have := h γ hγ
    have h' : ((∑ l, ℓ l * γ l : ℤ) : ℚ) = 0 := by rw [this]; rfl
    push_cast at h'
    simpa using h'
  have hrange : Module.finrank ℚ (LinearMap.range f) = 1 := by
    have h1 : Module.finrank ℚ (LinearMap.range f) ≤ 1 := by
      calc _ ≤ Module.finrank ℚ ℚ := Submodule.finrank_le _
        _ = 1 := Module.finrank_self ℚ
    have h2 : LinearMap.range f ≠ ⊥ := by
      intro hb
      exact hfne (LinearMap.range_eq_bot.1 hb)
    have h3 : 1 ≤ Module.finrank ℚ (LinearMap.range f) := Submodule.one_le_finrank_iff.2 h2
    omega
  have hnull := LinearMap.finrank_range_add_finrank_ker f
  have hdim : Module.finrank ℚ (Fin τ.rank → ℚ) = τ.rank := Module.finrank_fin_fun ℚ
  have := Submodule.finrank_mono hle
  unfold compRank
  omega

end Rank

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie.X1Exc

end
