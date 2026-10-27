module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FF6PFrame
public import CFSG.ClassicalInvolution.Models.OrthogonalPairs.Frame

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open CFSG.ClassicalInvolution

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V} {ι : Type} [Fintype ι] [DecidableEq ι] {c : ι → ZMod 3}

@[expose] def ffC : Option (Fin 5) → ZMod 3
  | none => -1
  | some _ => 1

theorem ffC_optionCongr (σ : Equiv.Perm (Fin 5)) (i : Option (Fin 5)) :
    ffC (Equiv.optionCongr σ i) = ffC i := by
  cases i <;> simp [ffC]

theorem PFrame.exists_pOrth (fr : PFrame Q (Option (Fin 5)) ffC) (σ : Equiv.Perm (Fin 5)) :
    ∃ g : OGroup Q, ∀ i, (g : V ≃ₗ[ZMod 3] V) (fr.b i) = fr.b (Equiv.optionCongr σ i) := by
  let τ : Equiv.Perm (Option (Fin 5)) := Equiv.optionCongr σ
  let e : V ≃ₗ[ZMod 3] V := fr.b.equiv fr.b τ
  have he : ∀ i, e (fr.b i) = fr.b (τ i) := fun i => by simp [e]
  have hcoord : ∀ x i, fr.b.repr (e x) (τ i) = fr.b.repr x i := by
    intro x i
    let F : V →ₗ[ZMod 3] (Option (Fin 5) → ZMod 3) :=
      { toFun := fun x i => fr.b.repr (e x) (τ i)
        map_add' := by intro x y; funext i; simp
        map_smul' := by intro a x; funext i; simp }
    let G : V →ₗ[ZMod 3] (Option (Fin 5) → ZMod 3) :=
      { toFun := fun x i => fr.b.repr x i
        map_add' := by intro x y; funext i; simp
        map_smul' := by intro a x; funext i; simp }
    have hFG : F = G := by
      apply fr.b.ext
      intro j
      funext i
      change fr.b.repr (e (fr.b j)) (τ i) = fr.b.repr (fr.b j) i
      rw [he j, Module.Basis.repr_self, Module.Basis.repr_self]
      by_cases hji : j = i
      · subst hji
        simp
      · have hne : τ j ≠ τ i := fun h => hji (τ.injective h)
        rw [Finsupp.single_eq_of_ne' hne, Finsupp.single_eq_of_ne' hji]
    exact congrFun (congrArg (fun H : V →ₗ[ZMod 3] (Option (Fin 5) → ZMod 3) => H x) hFG) i
  have hmem : e ∈ TauCeti.QuadraticMap.orthogonalGroup Q := by
    rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
    intro x
    have hsum : (∑ i, ffC i * (fr.b.repr (e x) i) ^ 2) = ∑ i, ffC i * (fr.b.repr x i) ^ 2 := by
      rw [← Equiv.sum_comp τ (fun i => ffC i * (fr.b.repr (e x) i) ^ 2)]
      exact Finset.sum_congr rfl fun i _ => by rw [ffC_optionCongr σ i, hcoord x i]
    rw [fr.map_eq (e x), fr.map_eq x, hsum]
  exact ⟨⟨e, hmem⟩, he⟩

noncomputable def PFrame.pOrth (fr : PFrame Q (Option (Fin 5)) ffC) (σ : Equiv.Perm (Fin 5)) :
    OGroup Q :=
  Classical.choose (fr.exists_pOrth σ)

theorem PFrame.pOrth_basis (fr : PFrame Q (Option (Fin 5)) ffC) (σ : Equiv.Perm (Fin 5))
    (i : Option (Fin 5)) :
    ((fr.pOrth σ : OGroup Q) : V ≃ₗ[ZMod 3] V) (fr.b i) = fr.b (Equiv.optionCongr σ i) :=
  Classical.choose_spec (fr.exists_pOrth σ) i

theorem PFrame.pOrth_mul (fr : PFrame Q (Option (Fin 5)) ffC) (σ τ : Equiv.Perm (Fin 5)) :
    fr.pOrth (σ * τ) = fr.pOrth σ * fr.pOrth τ := by
  apply Subtype.ext
  apply fr.b.ext'
  intro i
  rw [Submonoid.coe_mul, LinearEquiv.mul_apply, fr.pOrth_basis (σ * τ) i,
    fr.pOrth_basis τ i, fr.pOrth_basis σ (Equiv.optionCongr τ i)]
  cases i <;> rfl

theorem PFrame.pOrth_one (fr : PFrame Q (Option (Fin 5)) ffC) : fr.pOrth 1 = 1 := by
  apply Subtype.ext
  apply fr.b.ext'
  intro i
  rw [fr.pOrth_basis 1 i]
  cases i <;> rfl

theorem PFrame.pOrth_mul_signChange (fr : PFrame Q (Option (Fin 5)) ffC)
    (σ : Equiv.Perm (Fin 5)) (J : Finset (Option (Fin 5))) :
    fr.pOrth σ * fr.signChange J =
      fr.signChange (J.map (Equiv.optionCongr σ).toEmbedding) * fr.pOrth σ := by
  apply Subtype.ext
  apply fr.b.ext'
  intro i
  rw [Submonoid.coe_mul, Submonoid.coe_mul, LinearEquiv.mul_apply, LinearEquiv.mul_apply,
    fr.signChange_basis J i]
  by_cases hi : i ∈ J
  · have hmem : Equiv.optionCongr σ i ∈ J.map (Equiv.optionCongr σ).toEmbedding := by
      rw [Finset.mem_map]
      exact ⟨i, hi, rfl⟩
    rw [if_pos hi, map_neg, fr.pOrth_basis σ i,
      fr.signChange_basis (J.map (Equiv.optionCongr σ).toEmbedding) (Equiv.optionCongr σ i),
      if_pos hmem]
  · have hmem : Equiv.optionCongr σ i ∉ J.map (Equiv.optionCongr σ).toEmbedding := by
      rw [Finset.mem_map]
      rintro ⟨j, hj, hji⟩
      exact hi ((Equiv.optionCongr σ).injective hji ▸ hj)
    rw [if_neg hi, fr.pOrth_basis σ i,
      fr.signChange_basis (J.map (Equiv.optionCongr σ).toEmbedding) (Equiv.optionCongr σ i),
      if_neg hmem]

theorem PFrame.signChange_injective (fr : PFrame Q ι c) : Function.Injective fr.signChange := by
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
