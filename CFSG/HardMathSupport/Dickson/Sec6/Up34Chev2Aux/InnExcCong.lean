module

public import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.InnExcRDDefs
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.ExcToralityFive
public import CFSG.HardMathSupport.Timmesfeld.RootAut.Linear
public import Certificates.Data.ExceptionalSL3

public section

namespace CFSG.HardMathSupport.Dickson.Sec6

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Adjoint CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Solomon.UniquenessMaximal CFSG.LocalAnalysis.GLTheoremB
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.RootAut
  CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple

namespace Up34Exc

namespace InnExcCong

section Linear

set_option linter.unusedSectionVars false

variable {τ : Tag}

theorem eq_sum_single_smul (v : Fin τ.rank → ℤ) :
    v = ∑ j, v j • (Pi.single j 1 : Fin τ.rank → ℤ) := by
  ext k
  simp [Finset.sum_apply, Pi.single_apply]

theorem corootPair_eq_sum {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ) (v : Fin τ.rank → ℤ) :
    corootPair γ v = ∑ j, v j * corootPair γ (Pi.single j 1 : Fin τ.rank → ℤ) := by
  have hpos := iform_self_pos_of_isRoot hγ
  refine mul_right_cancel₀ hpos.ne' ?_
  rw [corootPair_mul hγ, Finset.sum_mul]
  have h1 : ∀ j, v j * corootPair γ (Pi.single j 1 : Fin τ.rank → ℤ) * iform γ γ =
      v j * (2 * iform γ (Pi.single j 1 : Fin τ.rank → ℤ)) := fun j => by
    rw [mul_assoc, corootPair_mul hγ]
  simp_rw [h1]
  have h2 : iform γ v = ∑ j, v j * iform γ (Pi.single j 1 : Fin τ.rank → ℤ) := by
    conv_lhs => rw [eq_sum_single_smul v]
    rw [iform_finset_sum_right]
    exact Finset.sum_congr rfl fun j _ => by rw [iform_smul_right]
  rw [h2, Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring

theorem dot_a2Exp {γ₁ γ₂ : Fin τ.rank → ℤ} (h₁ : IsRoot τ γ₁) (h₂ : IsRoot τ γ₂) (ε : ℤ)
    (v : Fin τ.rank → ℤ) :
    (fun j => ε * a2Exp τ γ₁ γ₂ j) ⬝ᵥ v =
      ε * (corootPair γ₁ v + 2 * corootPair γ₂ v) := by
  rw [corootPair_eq_sum h₁ v, corootPair_eq_sum h₂ v, dotProduct]
  have h : ∀ j, ε * a2Exp τ γ₁ γ₂ j * v j =
      ε * (v j * corootPair γ₁ (Pi.single j 1 : Fin τ.rank → ℤ) +
        2 * (v j * corootPair γ₂ (Pi.single j 1 : Fin τ.rank → ℤ))) := fun j => by
    change ε * (corootPair γ₁ (Pi.single j 1 : Fin τ.rank → ℤ) +
      2 * corootPair γ₂ (Pi.single j 1 : Fin τ.rank → ℤ)) * v j = _
    ring
  simp_rw [h]
  rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum]

theorem dot_rootReflection_smul {β : Fin τ.rank → ℤ} (hβ : IsRoot τ β) (x v : Fin τ.rank → ℤ) :
    x ⬝ᵥ (rootReflection β • v) = x ⬝ᵥ v - corootPair β v * (x ⬝ᵥ β) := by
  rw [rootReflection_smul hβ, dotProduct_sub, dotProduct_smul, smul_eq_mul]

theorem three_dvd_dot_smul {Ψ : Set (Fin τ.rank → ℤ)} {x : Fin τ.rank → ℤ}
    (hΨ : ∀ γ ∈ Ψ, IsRoot τ γ ∧ (3 : ℤ) ∣ x ⬝ᵥ γ) {w : WeylGroup τ}
    (hw : w ∈ Subgroup.closure {s : WeylGroup τ | ∃ γ ∈ Ψ, s = rootReflection γ}) :
    ∀ v : Fin τ.rank → ℤ, (3 : ℤ) ∣ x ⬝ᵥ (w • v) - x ⬝ᵥ v := by
  induction hw using Subgroup.closure_induction with
  | mem y hy =>
    obtain ⟨γ, hγ, rfl⟩ := hy
    intro v
    obtain ⟨hr, h3⟩ := hΨ γ hγ
    rw [dot_rootReflection_smul hr]
    have e : x ⬝ᵥ v - corootPair γ v * (x ⬝ᵥ γ) - x ⬝ᵥ v = -(corootPair γ v * (x ⬝ᵥ γ)) := by
      ring
    rw [e]
    exact (dvd_mul_of_dvd_right h3 _).neg_right
  | one => intro v; simp
  | mul y z _ _ hy hz =>
    intro v
    rw [mul_smul]
    have e : x ⬝ᵥ (y • z • v) - x ⬝ᵥ v =
        (x ⬝ᵥ (y • z • v) - x ⬝ᵥ (z • v)) + (x ⬝ᵥ (z • v) - x ⬝ᵥ v) := by ring
    rw [e]
    exact dvd_add (hy (z • v)) (hz v)
  | inv y _ hy =>
    intro v
    have h1 := hy (y⁻¹ • v)
    rw [smul_inv_smul] at h1
    have e : x ⬝ᵥ (y⁻¹ • v) - x ⬝ᵥ v = -(x ⬝ᵥ v - x ⬝ᵥ (y⁻¹ • v)) := by ring
    rw [e]
    exact h1.neg_right

theorem zpow_eq_zpow_iff_three_dvd {G : Type*} [Group G] {ω : G} (hord : orderOf ω = 3) {m n : ℤ} :
    ω ^ m = ω ^ n ↔ (3 : ℤ) ∣ m - n := by
  rw [← mul_inv_eq_one, ← zpow_sub, ← orderOf_dvd_iff_zpow_eq_one, hord]
  norm_cast

theorem rootChar_zpow_dot {L : Type} [Field L] (ζ : Lˣ) (x v : Fin τ.rank → ℤ) :
    rootChar (fun k => ζ ^ x k) v = ζ ^ (x ⬝ᵥ v) := by
  simp only [rootChar, dotProduct, ← zpow_mul]
  have key : ∀ s : Finset (Fin τ.rank), ∏ i ∈ s, ζ ^ (x i * v i) = ζ ^ (∑ i ∈ s, x i * v i) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih => rw [Finset.prod_insert ha, Finset.sum_insert ha, ih, zpow_add]
  exact key _

end Linear

section Frob

set_option linter.unusedSectionVars false

variable {τ : Tag} {L : Type}
  [Field L] [IsAlgClosed L] {p₀ : ℕ} (S : LangSetup τ L p₀)

theorem iterate_isRoot (n : ℕ) {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ) :
    IsRoot τ ((S.ρ : (Fin τ.rank → ℤ) → _)^[n] γ) := by
  induction n with
  | zero => exact hγ
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact (S.frob.isRoot_iff _).2 ih

theorem iform_iterate (n : ℕ) (y z : Fin τ.rank → ℤ) :
    iform ((S.ρ : (Fin τ.rank → ℤ) → _)^[n] y) ((S.ρ : (Fin τ.rank → ℤ) → _)^[n] z) =
      iform y z := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', S.frob.iform_eq, ih]

variable {a : Fin τ.rank → Lˣ}

theorem three_dvd_dot_iterate (hT : rootDiagUnit τ a ∈ S.D.torus) {ω : Lˣ} (hord : orderOf ω = 3)
    {x : Fin τ.rank → ℤ} (hχ : ∀ v, rootChar a v = ω ^ (x ⬝ᵥ v)) (n : ℕ)
    {δ : Fin τ.rank → ℤ} (hδ : IsRoot τ δ) :
    (3 : ℤ) ∣ x ⬝ᵥ (S.ρ : (Fin τ.rank → ℤ) → _)^[n] δ - (S.D.q : ℤ) ^ n * (x ⬝ᵥ δ) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    have hr := iterate_isRoot S n hδ
    have h1 := S.frob.rootChar_eq a hT _ hr
    rw [hχ, hχ, ← zpow_natCast, ← zpow_mul, zpow_eq_zpow_iff_three_dvd hord] at h1
    have e : x ⬝ᵥ S.ρ ((S.ρ : (Fin τ.rank → ℤ) → _)^[n] δ) - (S.D.q : ℤ) ^ (n + 1) * (x ⬝ᵥ δ) =
        (x ⬝ᵥ S.ρ ((S.ρ : (Fin τ.rank → ℤ) → _)^[n] δ) -
          x ⬝ᵥ (S.ρ : (Fin τ.rank → ℤ) → _)^[n] δ * (S.D.q : ℤ)) +
        (S.D.q : ℤ) * (x ⬝ᵥ (S.ρ : (Fin τ.rank → ℤ) → _)^[n] δ - (S.D.q : ℤ) ^ n * (x ⬝ᵥ δ)) := by
      ring
    rw [e]
    exact dvd_add h1 (dvd_mul_of_dvd_right ih _)

theorem q_pow_mod_three_aux (hT : rootDiagUnit τ a ∈ S.D.torus)
    (i : KernelComponent (rootCharHom a)) {s : ℕ}
    (hinner : twistInner (componentRoots (rootCharHom a) i)
      ((S.ρ : (Fin τ.rank → ℤ) → _)^[s]))
    {γ₁ γ₂ : Fin τ.rank → ℤ} (hm₁ : γ₁ ∈ componentRoots (rootCharHom a) i)
    (hm₂ : γ₂ ∈ componentRoots (rootCharHom a) i)
    {ω : Lˣ} (hord : orderOf ω = 3) {x : Fin τ.rank → ℤ}
    (hχ : ∀ v, rootChar a v = ω ^ (x ⬝ᵥ v)) {c₁ c₂ : ℤ}
    (hdot : ∀ v, x ⬝ᵥ v = c₁ * corootPair γ₁ v + c₂ * corootPair γ₂ v)
    (j : Fin τ.rank) (hj : ¬ (3 : ℤ) ∣ x j) :
    (S.D.q ^ s) % 3 = 1 := by
  classical
  have hΨ3 : ∀ γ ∈ componentRoots (rootCharHom a) i, IsRoot τ γ ∧ (3 : ℤ) ∣ x ⬝ᵥ γ := by
    intro γ hγ
    obtain ⟨hk, -⟩ := hγ
    refine ⟨hk.1, ?_⟩
    have h1 : rootChar a γ = 1 := hk.2
    rw [hχ] at h1
    have h2 := orderOf_dvd_iff_zpow_eq_one.2 h1
    rw [hord] at h2
    exact_mod_cast h2
  obtain ⟨w, hw, hwγ⟩ := hinner
  have hcop : ∀ γ ∈ componentRoots (rootCharHom a) i, ∀ v : Fin τ.rank → ℤ,
      corootPair γ (w⁻¹ • (S.ρ : (Fin τ.rank → ℤ) → _)^[s] v) = corootPair γ v := by
    intro γ hγ v
    have h1 : w⁻¹ • (S.ρ : (Fin τ.rank → ℤ) → _)^[s] γ = γ := by
      rw [hwγ γ hγ, inv_smul_smul]
    have h2 : iform γ (w⁻¹ • (S.ρ : (Fin τ.rank → ℤ) → _)^[s] v) = iform γ v :=
      calc iform γ (w⁻¹ • (S.ρ : (Fin τ.rank → ℤ) → _)^[s] v)
          = iform (w⁻¹ • (S.ρ : (Fin τ.rank → ℤ) → _)^[s] γ)
              (w⁻¹ • (S.ρ : (Fin τ.rank → ℤ) → _)^[s] v) := by rw [h1]
        _ = iform γ v := by rw [iform_smul, iform_iterate S]
    unfold corootPair
    rw [h2]
  have hu : ∀ v : Fin τ.rank → ℤ,
      x ⬝ᵥ (w⁻¹ • (S.ρ : (Fin τ.rank → ℤ) → _)^[s] v) = x ⬝ᵥ v := by
    intro v
    rw [hdot, hdot, hcop γ₁ hm₁, hcop γ₂ hm₂]
  have hδ : IsRoot τ (Pi.single j 1 : Fin τ.rank → ℤ) := isRoot_single τ j
  have hxδ : x ⬝ᵥ (Pi.single j 1 : Fin τ.rank → ℤ) = x j := dotProduct_single_one x j
  have hA := three_dvd_dot_smul hΨ3 hw
    (w⁻¹ • (S.ρ : (Fin τ.rank → ℤ) → _)^[s] (Pi.single j 1 : Fin τ.rank → ℤ))
  rw [smul_inv_smul, hu] at hA
  have hB := three_dvd_dot_iterate S hT hord hχ s hδ
  have hC : (3 : ℤ) ∣ ((S.D.q : ℤ) ^ s - 1) * x j := by
    have h := dvd_sub hA hB
    rw [hxδ] at h
    have e : x ⬝ᵥ (S.ρ : (Fin τ.rank → ℤ) → _)^[s] (Pi.single j 1 : Fin τ.rank → ℤ) - x j -
        (x ⬝ᵥ (S.ρ : (Fin τ.rank → ℤ) → _)^[s] (Pi.single j 1 : Fin τ.rank → ℤ) -
          (S.D.q : ℤ) ^ s * x j) = ((S.D.q : ℤ) ^ s - 1) * x j := by ring
    rwa [e] at h
  have hq : (3 : ℤ) ∣ (S.D.q : ℤ) ^ s - 1 := (Int.prime_three.dvd_or_dvd hC).resolve_right hj
  have hq' : (3 : ℤ) ∣ ((S.D.q ^ s : ℕ) : ℤ) - 1 := by
    push_cast
    exact hq
  generalize S.D.q ^ s = N at hq'
  omega

end Frob

end InnExcCong

section Spec

set_option linter.unusedSectionVars false


variable {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ} (S : LangSetup τ L p₀)
  {a : Fin τ.rank → Lˣ}

theorem q_pow_mod_three_of_inner_a2 (hT : rootDiagUnit τ a ∈ S.D.torus)
    (i : KernelComponent (rootCharHom a)) {s : ℕ}
    (hinner : twistInner (componentRoots (rootCharHom a) i)
      ((S.ρ : (Fin τ.rank → ℤ) → _)^[s]))
    {γ₁ γ₂ : Fin τ.rank → ℤ} (hP : IsA2Pair τ γ₁ γ₂)
    (hΨ : componentRoots (rootCharHom a) i = {γ₁, γ₂, γ₁ + γ₂, -γ₁, -γ₂, -(γ₁ + γ₂)})
    {ω : Lˣ} (hω3 : ω ^ 3 = 1) (hω1 : ω ≠ 1) {ε : ℤ} (hε : ε = 1 ∨ ε = -1)
    (hglue : ∀ j, a j = ω ^ (ε * a2Exp τ γ₁ γ₂ j)) (ha1 : ∃ j, a j ≠ 1) :
    (S.D.q ^ s) % 3 = 1 := by
  obtain ⟨hγ₁, hγ₂, -, -⟩ := hP
  have hord : orderOf ω = 3 := orderOf_eq_prime hω3 hω1
  have hχ : ∀ v, rootChar a v = ω ^ ((fun j => ε * a2Exp τ γ₁ γ₂ j) ⬝ᵥ v) := fun v => by
    have ha : a = fun k => ω ^ (ε * a2Exp τ γ₁ γ₂ k) := funext hglue
    rw [ha]
    exact InnExcCong.rootChar_zpow_dot ω (fun j => ε * a2Exp τ γ₁ γ₂ j) v
  obtain ⟨j, hj⟩ := ha1
  have hj3 : ¬ (3 : ℤ) ∣ ε * a2Exp τ γ₁ γ₂ j := by
    intro h3
    apply hj
    have h1 : ω ^ (ε * a2Exp τ γ₁ γ₂ j) = 1 := by
      rw [← orderOf_dvd_iff_zpow_eq_one, hord]
      exact_mod_cast h3
    rw [hglue j]
    exact h1
  have hm₁ : γ₁ ∈ componentRoots (rootCharHom a) i := by rw [hΨ]; simp
  have hm₂ : γ₂ ∈ componentRoots (rootCharHom a) i := by rw [hΨ]; simp
  refine InnExcCong.q_pow_mod_three_aux S hT i hinner hm₁ hm₂ hord hχ (c₁ := ε) (c₂ := 2 * ε)
    (fun v => ?_) j hj3
  rw [InnExcCong.dot_a2Exp hγ₁ hγ₂ ε v]
  ring

end Spec

end Up34Exc

end CFSG.HardMathSupport.Dickson.Sec6
