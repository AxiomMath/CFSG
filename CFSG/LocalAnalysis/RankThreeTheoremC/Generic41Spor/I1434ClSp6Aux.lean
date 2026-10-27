module

public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.GroupTheory.Sylow
public import Mathlib.FieldTheory.Finiteness

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.I1434.Cl

open Matrix

theorem survivor_mul_comm_three {G : Type*} [Group G] {a0 a1 a2 b0 b1 b2 : G}
    (h10 : Commute a1 b0) (h20 : Commute a2 b0) (h21 : Commute a2 b1) :
    a0 * a1 * a2 * (b0 * b1 * b2) = a0 * b0 * (a1 * b1) * (a2 * b2) := by
  calc a0 * a1 * a2 * (b0 * b1 * b2) = a0 * (a1 * (a2 * b0) * b1 * b2) := by simp only [mul_assoc]
    _ = a0 * (a1 * (b0 * a2) * b1 * b2) := by rw [h20.eq]
    _ = a0 * (a1 * b0 * (a2 * b1) * b2) := by simp only [mul_assoc]
    _ = a0 * (b0 * a1 * (b1 * a2) * b2) := by rw [h10.eq, h21.eq]
    _ = a0 * b0 * (a1 * b1) * (a2 * b2) := by simp only [mul_assoc]

theorem survivor_conj_mul_three {G : Type*} [Group G] (c x y z : G) :
    c * (x * y * z) * c⁻¹ = (c * x * c⁻¹) * (c * y * c⁻¹) * (c * z * c⁻¹) := by group

theorem survivor_rev_three {G : Type*} [Group G] {x y z : G} (hxy : Commute x y)
    (hyz : Commute y z) (hxz : Commute x z) : x * y * z = z * y * x := by
  calc x * y * z = x * (y * z) := by rw [mul_assoc]
    _ = x * (z * y) := by rw [hyz.eq]
    _ = (x * z) * y := by rw [mul_assoc]
    _ = (z * x) * y := by rw [hxz.eq]
    _ = z * (x * y) := by rw [mul_assoc]
    _ = z * (y * x) := by rw [hxy.eq]
    _ = z * y * x := by rw [mul_assoc]

theorem survivor_le_ncard_lines {G : Type*} [Group G] [Finite G] (A : G) (Q : Subgroup G) {n : ℕ}
    (h : Fin n → G) (hmem : ∀ i, h i * A * (h i)⁻¹ ∈ Q)
    (hinj : ∀ i j, Subgroup.zpowers (h i * A * (h i)⁻¹) = Subgroup.zpowers (h j * A * (h j)⁻¹) →
      i = j) :
    n ≤ Set.ncard {B : Subgroup G | ∃ g : G,
      B = (Subgroup.zpowers A).map (MulAut.conj g).toMonoidHom ∧ B ≤ Q} := by
  have : Finite (Subgroup G) :=
    Finite.of_injective (fun H : Subgroup G => (H : Set G)) SetLike.coe_injective
  let c : Fin n → Subgroup G := fun i => (Subgroup.zpowers A).map (MulAut.conj (h i)).toMonoidHom
  have hci : ∀ i, c i = Subgroup.zpowers (h i * A * (h i)⁻¹) := by
    intro i
    simp only [c]
    rw [MonoidHom.map_zpowers]
    rfl
  have hinjc : Function.Injective c := fun i j hij => hinj i j (by rw [← hci, ← hci]; exact hij)
  calc n = (Set.range c).ncard := by rw [Set.ncard_range_of_injective hinjc, Nat.card_fin]
    _ ≤ _ := Set.ncard_le_ncard (by
        rintro _ ⟨i, rfl⟩
        exact ⟨h i, rfl, by rw [hci, Subgroup.zpowers_le]; exact hmem i⟩) (Set.toFinite _)

theorem survivor_finrank_ker_add_rank {F ι : Type*} [Field F] [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι F) :
    Module.finrank F (LinearMap.ker (Matrix.toLin' M)) + M.rank = Fintype.card ι := by
  have := LinearMap.finrank_range_add_finrank_ker (Matrix.toLin' M)
  rw [Module.finrank_fintype_fun_eq_card] at this
  rw [Matrix.rank, ← Matrix.toLin'_apply']
  omega

theorem survivor_card_le_finrank_ker {K ι κ : Type*} [Field K] [Fintype ι] [DecidableEq ι]
    [Fintype κ] (A P Q : Matrix ι ι K) (hQP : Q * P = 1) (x : κ → ι) (hx : Function.Injective x)
    (hmem : ∀ s, A *ᵥ (P *ᵥ (Pi.single (x s) (1 : K) : ι → K)) = 0) :
    Fintype.card κ ≤ Module.finrank K (LinearMap.ker (Matrix.toLin' A)) := by
  let f : κ → LinearMap.ker (Matrix.toLin' A) := fun s =>
    ⟨P *ᵥ (Pi.single (x s) (1 : K) : ι → K), by
      rw [LinearMap.mem_ker, Matrix.toLin'_apply]
      exact hmem s⟩
  have hli : LinearIndependent K f := by
    apply LinearIndependent.of_comp (Submodule.subtype _)
    have h1 : LinearIndependent K (fun s => (Pi.single (x s) (1 : K) : ι → K)) := by
      have := (Pi.basisFun K ι).linearIndependent.comp x hx
      convert this using 1
      funext s
      simp [Pi.basisFun_apply]
    have hker : LinearMap.ker (Matrix.mulVecLin P) = ⊥ := by
      rw [LinearMap.ker_eq_bot']
      intro w hw
      have hw' : P *ᵥ w = 0 := hw
      calc w = Q *ᵥ (P *ᵥ w) := by rw [Matrix.mulVec_mulVec, hQP, Matrix.one_mulVec]
        _ = 0 := by rw [hw', Matrix.mulVec_zero]
    exact h1.map' (Matrix.mulVecLin P) hker
  exact hli.fintype_card_le_finrank

theorem survivor_finrank_ker_map {K K' ι : Type*} [Field K] [Field K'] [Fintype K] [Fintype K']
    [Fintype ι] [DecidableEq ι] (ψ : K ≃+* K') (M : Matrix ι ι K) :
    Module.finrank K' (LinearMap.ker (Matrix.toLin' (M.map ψ))) =
      Module.finrank K (LinearMap.ker (Matrix.toLin' M)) := by
  have hcard : Nat.card (LinearMap.ker (Matrix.toLin' M)) =
      Nat.card (LinearMap.ker (Matrix.toLin' (M.map ψ))) := by
    refine Nat.card_congr (Equiv.subtypeEquiv (Equiv.arrowCongr (Equiv.refl ι) ψ.toEquiv) ?_)
    intro v
    simp only [LinearMap.mem_ker, Matrix.toLin'_apply]
    constructor
    · intro h
      funext i
      have h1 : ψ ((M *ᵥ v) i) = (M.map ψ *ᵥ (ψ ∘ v)) i := ψ.toRingHom.map_mulVec M v i
      rw [h] at h1
      simp only [Pi.zero_apply, map_zero] at h1
      exact h1.symm
    · intro h
      funext i
      have h1 : ψ ((M *ᵥ v) i) = (M.map ψ *ᵥ (ψ ∘ v)) i := ψ.toRingHom.map_mulVec M v i
      have h2 := congrFun h i
      simp only [Pi.zero_apply] at h2 ⊢
      apply ψ.injective
      rw [map_zero, h1]
      exact h2
  have h1 := Module.natCard_eq_pow_finrank (K := K') (V := LinearMap.ker (Matrix.toLin' (M.map ψ)))
  have h2 := Module.natCard_eq_pow_finrank (K := K) (V := LinearMap.ker (Matrix.toLin' M))
  have hK : Nat.card K = Nat.card K' := Nat.card_congr ψ.toEquiv
  rw [← hK, ← hcard] at h1
  have hpos : 1 < Nat.card K := by
    rw [Nat.card_eq_fintype_card]
    exact Fintype.one_lt_card
  exact Nat.pow_right_injective (Nat.succ_le_of_lt hpos) (h1.symm.trans h2)

theorem survivor_finrank_ker_conj {F ι : Type*} [Field F] [Fintype ι] [DecidableEq ι]
    (U : GL ι F) (M : Matrix ι ι F) :
    Module.finrank F (LinearMap.ker (Matrix.toLin'
        (((U⁻¹ : GL ι F) : Matrix ι ι F) * M * (U : Matrix ι ι F)))) =
      Module.finrank F (LinearMap.ker (Matrix.toLin' M)) := by
  have h1 := survivor_finrank_ker_add_rank
    (((U⁻¹ : GL ι F) : Matrix ι ι F) * M * (U : Matrix ι ι F))
  have h2 := survivor_finrank_ker_add_rank M
  have hU : IsUnit (U : Matrix ι ι F).det := (Matrix.isUnit_iff_isUnit_det _).1 U.isUnit
  have hUi : IsUnit ((U⁻¹ : GL ι F) : Matrix ι ι F).det :=
    (Matrix.isUnit_iff_isUnit_det _).1 (U⁻¹).isUnit
  rw [Matrix.rank_mul_eq_left_of_isUnit_det _ _ hU,
    Matrix.rank_mul_eq_right_of_isUnit_det _ _ hUi] at h1
  omega

theorem survivor_exists_conj_torus {G : Type*} [Group G] [Finite G]
    (τ : Multiplicative (Fin 3 → ZMod 5) →* G) (hτ : Function.Injective τ)
    (hG : (Nat.card G).factorization 5 = 3) (Q : Sylow 5 G) {A : G} (hA : A ∈ (Q : Subgroup G)) :
    ∃ (g : G) (v : Fin 3 → ZMod 5), A = g * τ (Multiplicative.ofAdd v) * g⁻¹ ∧
      (Q : Subgroup G) = τ.range.map (MulAut.conj g).toMonoidHom := by
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hcard : Nat.card τ.range = 5 ^ (Nat.card G).factorization 5 := by
    rw [hG, ← Nat.card_congr (MonoidHom.ofInjective hτ).toEquiv, Nat.card_eq_fintype_card]
    decide +kernel
  let T : Sylow 5 G := Sylow.ofCard τ.range hcard
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G T Q
  have hQ : (Q : Subgroup G) = τ.range.map (MulAut.conj g).toMonoidHom := by
    rw [← hg]
    ext x
    rw [Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists, Subgroup.mem_map]
    rfl
  refine ⟨g, ?_⟩
  rw [hQ] at hA
  obtain ⟨y, ⟨u, rfl⟩, rfl⟩ := Subgroup.mem_map.1 hA
  exact ⟨Multiplicative.toAdd u, rfl, hQ⟩

theorem survivor_torus_zpow {G : Type*} [Group G] (τ : Multiplicative (Fin 3 → ZMod 5) →* G)
    (v : Fin 3 → ZMod 5) (k : ℤ) :
    τ (Multiplicative.ofAdd v) ^ k =
      τ (Multiplicative.ofAdd (fun j => (k : ZMod 5) * v j)) := by
  rw [← map_zpow, ← ofAdd_zsmul]
  congr 2
  funext j
  simp [zsmul_eq_mul]

theorem survivor_exists_smul_of_zpowers_eq {G : Type*} [Group G]
    (τ : Multiplicative (Fin 3 → ZMod 5) →* G) (hτ : Function.Injective τ) (g : G)
    (v w : Fin 3 → ZMod 5)
    (h : Subgroup.zpowers (g * τ (Multiplicative.ofAdd v) * g⁻¹) =
      Subgroup.zpowers (g * τ (Multiplicative.ofAdd w) * g⁻¹)) :
    ∃ n : ZMod 5, (fun j => n * v j) = w := by
  have hmem : g * τ (Multiplicative.ofAdd w) * g⁻¹ ∈
      Subgroup.zpowers (g * τ (Multiplicative.ofAdd v) * g⁻¹) := by
    rw [h]
    exact Subgroup.mem_zpowers _
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hmem
  have h1 : g * (τ (Multiplicative.ofAdd v) ^ k) * g⁻¹ =
      g * τ (Multiplicative.ofAdd w) * g⁻¹ := by
    rw [← hk]
    have := map_zpow (MulAut.conj g) (τ (Multiplicative.ofAdd v)) k
    rw [MulAut.conj_apply, MulAut.conj_apply] at this
    exact this
  have h2 : τ (Multiplicative.ofAdd v) ^ k = τ (Multiplicative.ofAdd w) := by
    simpa using h1
  rw [survivor_torus_zpow] at h2
  exact ⟨k, Multiplicative.ofAdd.injective (hτ h2)⟩

theorem survivor_lines_torus {G : Type*} [Group G] [Finite G]
    (τ : Multiplicative (Fin 3 → ZMod 5) →* G) (hτ : Function.Injective τ) (g : G)
    (v : Fin 3 → ZMod 5) {n : ℕ} (c : Fin n → G) (w : Fin n → Fin 3 → ZMod 5)
    (hc : ∀ i, c i * τ (Multiplicative.ofAdd v) * (c i)⁻¹ = τ (Multiplicative.ofAdd (w i)))
    (hw : ∀ (i j : Fin n) (m : ZMod 5), (fun k => m * w i k) = w j → i = j) :
    n ≤ Set.ncard {B : Subgroup G | ∃ g' : G,
      B = (Subgroup.zpowers (g * τ (Multiplicative.ofAdd v) * g⁻¹)).map
          (MulAut.conj g').toMonoidHom ∧
        B ≤ τ.range.map (MulAut.conj g).toMonoidHom} := by
  have key : ∀ i : Fin n, (g * c i * g⁻¹) * (g * τ (Multiplicative.ofAdd v) * g⁻¹) *
      (g * c i * g⁻¹)⁻¹ = g * τ (Multiplicative.ofAdd (w i)) * g⁻¹ := by
    intro i
    rw [← hc i]
    group
  refine survivor_le_ncard_lines (g * τ (Multiplicative.ofAdd v) * g⁻¹) _
    (fun i => g * c i * g⁻¹) ?_ ?_
  · intro i
    rw [key]
    exact Subgroup.mem_map.2 ⟨τ (Multiplicative.ofAdd (w i)), ⟨_, rfl⟩, rfl⟩
  · intro i j hij
    simp only [key] at hij
    obtain ⟨m, hm⟩ := survivor_exists_smul_of_zpowers_eq τ hτ g _ _ hij
    exact hw i j m hm

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.I1434.Cl
