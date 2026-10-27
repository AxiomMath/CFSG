module

public import CFSG.CGT.Stroth77.L4Sylow.Embed

public section

namespace CFSG.CGT.Stroth77.L4Sylow

open Matrix CFSG.Open

variable {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι]

theorem diagonal_mul_permMatrix_eq_diagonal_iff {x : ι → K} (hx : ∀ i, x i ≠ 0)
    (σ : Equiv.Perm ι) (u : K) :
    diagonal x * σ.permMatrix K = diagonal (fun _ => u) ↔ σ = 1 ∧ ∀ i, x i = u := by
  have happ : ∀ i j, (diagonal x * σ.permMatrix K) i j = if σ i = j then x i else 0 := by
    intro i j
    rw [diagonal_mul]
    simp [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply]
  constructor
  · intro h
    have hσ : σ = 1 := by
      ext i
      by_contra hne
      have hne' : i ≠ σ i := fun h' => hne (by rw [Equiv.Perm.one_apply, ← h'])
      have h1 := congrFun (congrFun h i) (σ i)
      rw [happ, if_pos rfl, diagonal_apply_ne _ hne'] at h1
      exact hx i h1
    refine ⟨hσ, fun i => ?_⟩
    have h1 := congrFun (congrFun h i) i
    rw [happ, hσ, Equiv.Perm.one_apply, if_pos rfl, diagonal_apply_eq] at h1
    exact h1
  · rintro ⟨rfl, hu⟩
    rw [permMatrix_one, mul_one]
    exact congrArg diagonal (funext hu)

theorem mem_statedScalars_iff_of_coe_eq_diagonal_mul_permMatrix [Nonempty ι] {g : GL ι K}
    {x : ι → K} (hx : ∀ i, x i ≠ 0) {σ : Equiv.Perm ι}
    (hg : (g : Matrix ι ι K) = diagonal x * σ.permMatrix K) :
    g ∈ StatedScalars ι K ↔ σ = 1 ∧ ∀ i j, x i = x j := by
  constructor
  · rintro ⟨u, hu⟩
    have h : diagonal x * σ.permMatrix K = diagonal (fun _ => (u : K)) := by
      rw [← hg, ← hu, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply]
    obtain ⟨hσ, hxu⟩ := (diagonal_mul_permMatrix_eq_diagonal_iff hx σ u).1 h
    exact ⟨hσ, fun i j => (hxu i).trans (hxu j).symm⟩
  · rintro ⟨rfl, hxc⟩
    obtain ⟨i₀⟩ := ‹Nonempty ι›
    refine ⟨Units.mk0 (x i₀) (hx i₀), Units.ext ?_⟩
    rw [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, hg, permMatrix_one, mul_one,
      Units.val_mk0]
    exact congrArg diagonal (funext fun i => hxc i₀ i)

namespace L4Data

variable {n : ℕ} (D : L4Data K n)

theorem pow_val_eq_pow_val_iff {x y : ZMod (2 ^ n)} :
    (D.ζ : K) ^ x.val = (D.ζ : K) ^ y.val ↔ x = y := by
  haveI : NeZero (2 ^ n) := ⟨by positivity⟩
  refine ⟨fun h => ?_, by rintro rfl; rfl⟩
  have h' : D.ζ ^ x.val = D.ζ ^ y.val :=
    Units.ext (by rw [Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, h])
  rw [pow_eq_pow_iff_modEq, D.orderOf_ζ] at h'
  apply ZMod.val_injective
  unfold Nat.ModEq at h'
  rwa [Nat.mod_eq_of_lt (ZMod.val_lt x), Nat.mod_eq_of_lt (ZMod.val_lt y)] at h'

theorem embed_mem_statedScalars_iff (a : L4Hat n) :
    D.embed a ∈ StatedScalars (Fin 4) K ↔ a.right = 1 ∧
      ∀ i j, Multiplicative.toAdd a.left i = Multiplicative.toAdd a.left j := by
  rw [mem_statedScalars_iff_of_coe_eq_diagonal_mul_permMatrix
    (fun i => pow_ne_zero _ D.ζ.ne_zero) (D.coe_embed a)]
  refine and_congr ?_ (forall_congr' fun i => forall_congr' fun j => D.pow_val_eq_pow_val_iff)
  rw [inv_eq_one, OneMemClass.coe_eq_one]

@[expose] def toProj (hn : 1 ≤ n) : L4P n →* StatedProj (StatedSL 4 K) :=
  (QuotientGroup.mk' _).comp (D.toSL hn)

theorem ker_toProj (hn1 : 1 ≤ n) (hn : 2 ≤ n) :
    (D.toProj hn1).ker = Subgroup.zpowers (cL4 n) := by
  ext a
  rw [toProj, MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
    QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf, coe_toSL,
    D.embed_mem_statedScalars_iff, mem_zpowers_cL4 hn]

end L4Data

end CFSG.CGT.Stroth77.L4Sylow
