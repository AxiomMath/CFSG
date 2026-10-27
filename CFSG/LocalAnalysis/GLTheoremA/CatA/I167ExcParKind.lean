module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I167ExcParKindLin
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I167ExcParKindDet
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I167ExcParKindPerm

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I167

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.HardMathSupport.Timmesfeld
  CFSG.HardMathSupport.Timmesfeld.LangTorus


theorem exc_component_finite {τ : Tag} {Ψ : Set (Fin τ.rank → ℤ)} (hΨ : IsRootComponent Ψ) :
    Ψ.Finite :=
  (finite_setOf_isRoot τ).subset fun α hα => hΨ.isRoot α hα

private theorem exc_reflection_perm_exists {τ : Tag} {Ψ : Set (Fin τ.rank → ℤ)}
    (hΨ : IsRootComponent Ψ) {γ : Fin τ.rank → ℤ} (hγ : γ ∈ Ψ) :
    ∃ π : Equiv.Perm ↥Ψ, ∀ x : ↥Ψ,
      (π x : Fin τ.rank → ℤ) = rootReflection γ • (x : Fin τ.rank → ℤ) := by
  have hinv : ∀ x : ↥Ψ, rootReflection γ • rootReflection γ • (x : Fin τ.rank → ℤ) = x := by
    intro x
    rw [← mul_smul, rootReflection_mul_self (hΨ.isRoot γ hγ), one_smul]
  refine ⟨⟨fun x => ⟨rootReflection γ • (x : Fin τ.rank → ℤ), hΨ.reflection_mem x x.2 γ hγ⟩,
    fun x => ⟨rootReflection γ • (x : Fin τ.rank → ℤ), hΨ.reflection_mem x x.2 γ hγ⟩, ?_, ?_⟩,
    fun x => rfl⟩
  · intro x
    exact Subtype.ext (hinv x)
  · intro x
    exact Subtype.ext (hinv x)

theorem exc_neg_perm_sign {τ : Tag} {Ψ : Set (Fin τ.rank → ℤ)} [Fintype ↥Ψ] [DecidableEq ↥Ψ]
    (hΨ : IsRootComponent Ψ) (π : Equiv.Perm ↥Ψ)
    (hπ : ∀ x : ↥Ψ, (π x : Fin τ.rank → ℤ) = -(x : Fin τ.rank → ℤ)) :
    Equiv.Perm.sign π = (-1) ^ (Ψ.ncard / 2) := by
  have h2 : π ^ 2 = 1 := by
    refine Equiv.ext fun x => Subtype.ext ?_
    simp only [pow_two, Equiv.Perm.mul_apply, Equiv.Perm.one_apply]
    rw [hπ, hπ, neg_neg]
  have hfix : Fintype.card (Function.fixedPoints π) = 0 := by
    rw [Fintype.card_eq_zero_iff]
    refine ⟨fun ⟨x, hx⟩ => ?_⟩
    have h1 : (π x : Fin τ.rank → ℤ) = x := congrArg Subtype.val hx
    rw [hπ] at h1
    have h0 : (x : Fin τ.rank → ℤ) = 0 := by
      funext i
      have := congrFun h1 i
      simp only [Pi.neg_apply] at this
      simp only [Pi.zero_apply]
      omega
    exact (hΨ.isRoot x x.2).ne_zero h0
  have hcard : Fintype.card ↥Ψ = Ψ.ncard := by
    rw [← Nat.card_coe_set_eq, Nat.card_eq_fintype_card]
  rw [Equiv.Perm.sign_of_pow_two_eq_one h2, hfix, hcard, Nat.sub_zero]

private theorem exc_det_eq_sign {τ : Tag} {Ψ : Set (Fin τ.rank → ℤ)} [Fintype ↥Ψ]
    [DecidableEq ↥Ψ] (hΨ : IsRootComponent Ψ) {w : WeylGroup τ}
    (hw : w ∈ Subgroup.closure {s : WeylGroup τ | ∃ γ ∈ Ψ, s = rootReflection γ}) :
    ∃ (L : (Fin τ.rank → ℚ) →ₗ[ℚ] (Fin τ.rank → ℚ)) (π : Equiv.Perm ↥Ψ),
      (∀ x : Fin τ.rank → ℤ, L (excToQ x) = excToQ (w • x)) ∧
      (∀ x : ↥Ψ, (π x : Fin τ.rank → ℤ) = w • (x : Fin τ.rank → ℤ)) ∧
      LinearMap.det L = (((Equiv.Perm.sign π : ℤˣ) : ℤ) : ℚ) := by
  have hS : {s : WeylGroup τ | ∃ γ ∈ Ψ, s = rootReflection γ}⁻¹ =
      {s : WeylGroup τ | ∃ γ ∈ Ψ, s = rootReflection γ} := by
    ext s
    constructor
    · rintro ⟨γ, hγ, hs⟩
      refine ⟨γ, hγ, ?_⟩
      rw [← inv_inv s, hs, rootReflection_inv (hΨ.isRoot γ hγ)]
    · rintro ⟨γ, hγ, hs⟩
      refine ⟨γ, hγ, ?_⟩
      rw [hs, rootReflection_inv (hΨ.isRoot γ hγ)]
  have hw' : w ∈ Submonoid.closure {s : WeylGroup τ | ∃ γ ∈ Ψ, s = rootReflection γ} := by
    have := hw
    rw [← Subgroup.mem_toSubmonoid, Subgroup.closure_toSubmonoid, hS, Set.union_self] at this
    exact this
  clear hw
  induction hw' using Submonoid.closure_induction with
  | mem s hs =>
    obtain ⟨γ, hγ, rfl⟩ := hs
    obtain ⟨L, hL⟩ := exc_exists_linearExt (rootReflection γ)
    obtain ⟨π, hπ⟩ := exc_reflection_perm_exists hΨ hγ
    refine ⟨L, π, hL, hπ, ?_⟩
    rw [exc_reflection_det (hΨ.isRoot γ hγ) L hL, exc_reflection_perm_sign hΨ hγ π hπ]
    simp
  | one =>
    exact ⟨LinearMap.id, 1, fun x => by simp, fun x => by simp, by simp⟩
  | mul a b _ _ iha ihb =>
    obtain ⟨L₁, π₁, h1L, h1π, h1d⟩ := iha
    obtain ⟨L₂, π₂, h2L, h2π, h2d⟩ := ihb
    refine ⟨L₁ ∘ₗ L₂, π₁ * π₂, ?_, ?_, ?_⟩
    · intro x
      simp only [LinearMap.comp_apply]
      rw [h2L, h1L, mul_smul]
    · intro x
      rw [Equiv.Perm.mul_apply, h1π, h2π, mul_smul]
    · rw [LinearMap.det_comp, h1d, h2d, map_mul]
      push_cast
      ring

theorem exc_neg_parity {τ : Tag} {Ψ : Set (Fin τ.rank → ℤ)} (hΨ : IsRootComponent Ψ)
    {v : WeylGroup τ}
    (hv : v ∈ Subgroup.closure {s : WeylGroup τ | ∃ γ ∈ Ψ, s = rootReflection γ})
    (hneg : ∀ γ ∈ Ψ, v • γ = -γ) : Even (compRank Ψ + Ψ.ncard / 2) := by
  classical
  haveI : Fintype ↥Ψ := (exc_component_finite hΨ).fintype
  obtain ⟨L, π, hL, hπ, hd⟩ := exc_det_eq_sign hΨ hv
  have h1 := exc_det_neg_element hΨ hv hneg L hL
  have h2 : Equiv.Perm.sign π = (-1) ^ (Ψ.ncard / 2) :=
    exc_neg_perm_sign hΨ π fun x => by rw [hπ x, hneg x x.2]
  rw [h1, h2] at hd
  simp only [Units.val_pow_eq_pow_val, Units.val_neg, Units.val_one, Int.cast_pow, Int.cast_neg,
    Int.cast_one] at hd
  rcases Nat.even_or_odd (compRank Ψ) with ha | ha <;>
    rcases Nat.even_or_odd (Ψ.ncard / 2) with hb | hb
  · exact ha.add hb
  · rw [ha.neg_one_pow, hb.neg_one_pow] at hd
    norm_num at hd
  · rw [ha.neg_one_pow, hb.neg_one_pow] at hd
    norm_num at hd
  · exact ha.add_odd hb

theorem exc_not_twistInner_of_odd {τ : Tag} {Ψ : Set (Fin τ.rank → ℤ)} (hΨ : IsRootComponent Ψ)
    {σ : (Fin τ.rank → ℤ) → (Fin τ.rank → ℤ)} {u : WeylGroup τ}
    (hu : u ∈ Subgroup.closure {s : WeylGroup τ | ∃ γ ∈ Ψ, s = rootReflection γ})
    (hσ : ∀ γ ∈ Ψ, σ γ = -(u • γ)) (hodd : Odd (compRank Ψ + Ψ.ncard / 2)) :
    ¬ twistInner Ψ σ := by
  rintro ⟨w, hw, hwσ⟩
  have hv : u⁻¹ * w ∈ Subgroup.closure {s : WeylGroup τ | ∃ γ ∈ Ψ, s = rootReflection γ} :=
    mul_mem (inv_mem hu) hw
  have hneg : ∀ γ ∈ Ψ, (u⁻¹ * w) • γ = -γ := by
    intro γ hγ
    rw [mul_smul, ← hwσ γ hγ, hσ γ hγ, smul_neg, inv_smul_smul]
  exact (Nat.not_even_iff_odd.2 hodd) (exc_neg_parity hΨ hv hneg)

end CFSG.LocalAnalysis.GLTheoremA.I167

end
