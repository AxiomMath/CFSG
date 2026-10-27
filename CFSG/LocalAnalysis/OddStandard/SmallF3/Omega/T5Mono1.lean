module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.T5Frame
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.TypesOmega

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open CFSG.ClassicalInvolution

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V} {ι : Type} [Fintype ι] [DecidableEq ι] {c : ZMod 3}

private theorem mul_self_eq_one_prod
    (a : (ZMod 3)ˣ × Multiplicative (TauCeti.SquareClassGroup (ZMod 3))) : a * a = 1 := by
  obtain ⟨u, b⟩ := a
  refine Prod.ext ?_ ?_
  · show u * u = 1
    rcases aux_units_zmod3 u with h | h <;> rw [h] <;> decide
  · show b * b = 1
    apply Multiplicative.toAdd.injective
    rw [toAdd_mul, toAdd_one]
    have h : (2 : ℕ) • Multiplicative.toAdd b = 0 := by
      rw [← Nat.cast_smul_eq_nsmul (ZMod 2) 2 (Multiplicative.toAdd b),
        CharP.cast_eq_zero (ZMod 2) 2, zero_smul]
    simpa [two_nsmul] using h

theorem NFrame.exists_permOrth (fr : NFrame Q ι c) (σ : Equiv.Perm ι) :
    ∃ g : OGroup Q, ∀ i, (g : V ≃ₗ[ZMod 3] V) (fr.b i) = fr.b (σ i) := by
  let e : V ≃ₗ[ZMod 3] V := fr.b.equiv fr.b σ
  have he : ∀ i, e (fr.b i) = fr.b (σ i) := fun i => by simp [e]
  have hcoord : ∀ x i, fr.b.repr (e x) (σ i) = fr.b.repr x i := by
    intro x i
    let F : V →ₗ[ZMod 3] (ι → ZMod 3) :=
      { toFun := fun x i => fr.b.repr (e x) (σ i)
        map_add' := by intro x y; funext i; simp
        map_smul' := by intro a x; funext i; simp }
    let G : V →ₗ[ZMod 3] (ι → ZMod 3) :=
      { toFun := fun x i => fr.b.repr x i
        map_add' := by intro x y; funext i; simp
        map_smul' := by intro a x; funext i; simp }
    have hFG : F = G := by
      apply fr.b.ext
      intro j
      funext i
      change fr.b.repr (e (fr.b j)) (σ i) = fr.b.repr (fr.b j) i
      rw [he j, Module.Basis.repr_self, Module.Basis.repr_self]
      by_cases hji : j = i
      · subst hji
        simp
      · have hne : σ j ≠ σ i := fun h => hji (σ.injective h)
        rw [Finsupp.single_eq_of_ne' hne, Finsupp.single_eq_of_ne' hji]
    exact congrFun (congrArg (fun H : V →ₗ[ZMod 3] (ι → ZMod 3) => H x) hFG) i
  have hmem : e ∈ TauCeti.QuadraticMap.orthogonalGroup Q := by
    rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
    intro x
    have hsum : (∑ i, (fr.b.repr (e x) i) ^ 2) = ∑ i, (fr.b.repr x i) ^ 2 := by
      rw [← Equiv.sum_comp σ (fun i => (fr.b.repr (e x) i) ^ 2)]
      exact Finset.sum_congr rfl fun i _ => by rw [hcoord x i]
    rw [fr.map_eq (e x), fr.map_eq x, hsum]
  exact ⟨⟨e, hmem⟩, he⟩

noncomputable def NFrame.permOrth (fr : NFrame Q ι c) (σ : Equiv.Perm ι) : OGroup Q :=
  Classical.choose (fr.exists_permOrth σ)

theorem NFrame.permOrth_basis (fr : NFrame Q ι c) (σ : Equiv.Perm ι) (i : ι) :
    ((fr.permOrth σ : OGroup Q) : V ≃ₗ[ZMod 3] V) (fr.b i) = fr.b (σ i) :=
  Classical.choose_spec (fr.exists_permOrth σ) i

theorem NFrame.permOrth_mul (fr : NFrame Q ι c) (σ τ : Equiv.Perm ι) :
    fr.permOrth (σ * τ) = fr.permOrth σ * fr.permOrth τ := by
  apply Subtype.ext
  apply fr.b.ext'
  intro i
  rw [Submonoid.coe_mul, LinearEquiv.mul_apply, fr.permOrth_basis (σ * τ) i,
    fr.permOrth_basis τ i, fr.permOrth_basis σ (τ i)]
  rfl

theorem NFrame.permOrth_one (fr : NFrame Q ι c) : fr.permOrth 1 = 1 := by
  apply Subtype.ext
  apply fr.b.ext'
  intro i
  rw [fr.permOrth_basis 1 i]
  simp

theorem NFrame.permOrth_mul_signChange (fr : NFrame Q ι c) (σ : Equiv.Perm ι) (J : Finset ι) :
    fr.permOrth σ * fr.signChange J = fr.signChange (J.map σ.toEmbedding) * fr.permOrth σ := by
  apply Subtype.ext
  apply fr.b.ext'
  intro i
  rw [Submonoid.coe_mul, Submonoid.coe_mul, LinearEquiv.mul_apply, LinearEquiv.mul_apply,
    fr.signChange_basis J i]
  by_cases hi : i ∈ J
  · have hmem : σ i ∈ J.map σ.toEmbedding := by
      rw [Finset.mem_map]
      exact ⟨i, hi, rfl⟩
    rw [if_pos hi, map_neg, fr.permOrth_basis σ i,
      fr.signChange_basis (J.map σ.toEmbedding) (σ i), if_pos hmem]
  · have hmem : σ i ∉ J.map σ.toEmbedding := by
      rw [Finset.mem_map]
      rintro ⟨j, hj, hji⟩
      exact hi (σ.injective hji ▸ hj)
    rw [if_neg hi, fr.permOrth_basis σ i,
      fr.signChange_basis (J.map σ.toEmbedding) (σ i), if_neg hmem]

theorem NFrame.permOrth_mem_omegaGroup (hQ : Q.Nondegenerate) (fr : NFrame Q ι c)
    {σ : Equiv.Perm ι} (hσ : σ ∈ alternatingGroup ι) : fr.permOrth σ ∈ omegaGroup hQ := by
  have hsq : ∀ g : OGroup Q, g * g ∈ omegaGroup hQ := by
    intro g
    rw [mem_omegaGroup_iff hQ, map_mul]
    exact mul_self_eq_one_prod (detSpinorNorm hQ g)
  let p : Equiv.Perm ι →* OGroup Q :=
    { toFun := fr.permOrth
      map_one' := fr.permOrth_one
      map_mul' := fr.permOrth_mul }
  have h3 : ∀ τ : Equiv.Perm ι, Equiv.Perm.IsThreeCycle τ → p τ ∈ omegaGroup hQ := by
    intro τ hτ
    have hτ3 : τ ^ 3 = 1 := by
      rw [← hτ.orderOf]
      exact pow_orderOf_eq_one τ
    have h4 : τ ^ 4 = τ := by
      rw [show (4 : ℕ) = 3 + 1 from rfl, pow_add, hτ3, one_mul, pow_one]
    have hgg : (τ * τ) * (τ * τ) = τ := by
      rw [← pow_two τ, ← pow_add, show (2 : ℕ) + 2 = 4 from rfl, h4]
    have hmem : p (τ * τ) * p (τ * τ) ∈ omegaGroup hQ := hsq (p (τ * τ))
    rwa [← map_mul, hgg] at hmem
  have hle : Subgroup.closure {τ : Equiv.Perm ι | Equiv.Perm.IsThreeCycle τ} ≤
      (omegaGroup hQ).comap p := by
    rw [Subgroup.closure_le]
    exact fun τ hτ => h3 τ hτ
  have halt : alternatingGroup ι ≤ (omegaGroup hQ).comap p := by
    rwa [Equiv.Perm.closure_three_cycles_eq_alternating] at hle
  exact halt hσ

theorem NFrame.signChange_injective (fr : NFrame Q ι c) : Function.Injective fr.signChange := by
  intro J K h
  apply Finset.ext
  intro i
  have hb := congrArg (fun g : OGroup Q => ((g : V ≃ₗ[ZMod 3] V) (fr.b i))) h
  rw [fr.signChange_basis J i, fr.signChange_basis K i] at hb
  by_cases hJ : i ∈ J <;> by_cases hK : i ∈ K
  · exact iff_of_true hJ hK
  · exfalso
    have hneg : -fr.b i = fr.b i := by simpa [hJ, hK] using hb
    have hx : fr.b i = -fr.b i := hneg.symm
    have hsum : fr.b i + fr.b i = 0 := by
      nth_rewrite 1 [hx]
      exact neg_add_cancel _
    have hsmul : (2 : ZMod 3) • fr.b i = 0 := by rw [two_smul]; exact hsum
    rcases (fr.b.smul_eq_zero (c := (2 : ZMod 3)) (x := fr.b i)).mp hsmul with h2 | hx0
    · exact absurd h2 (by decide)
    · exact fr.b.ne_zero i hx0
  · exfalso
    have hneg : fr.b i = -fr.b i := by simpa [hJ, hK] using hb
    have hsum : fr.b i + fr.b i = 0 := by
      nth_rewrite 1 [hneg]
      exact neg_add_cancel _
    have hsmul : (2 : ZMod 3) • fr.b i = 0 := by rw [two_smul]; exact hsum
    rcases (fr.b.smul_eq_zero (c := (2 : ZMod 3)) (x := fr.b i)).mp hsmul with h2 | hx0
    · exact absurd h2 (by decide)
    · exact fr.b.ne_zero i hx0
  · exact iff_of_false hJ hK

end CFSG.OddStandard.SmallF3.Omega
