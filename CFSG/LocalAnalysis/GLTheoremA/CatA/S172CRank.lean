module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S172XDefs
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S172CRankBound
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S172CRankFrame
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S172CRankInv
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S172CRankSiegel
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S172CRankTorus
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S172CRankWitt

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S172C

open QuadraticMap Module CFSG.Open CFSG.ClassicalGroups.Orthogonal CFSG.GroupTheory.WeirSylow
  CFSG.RankThree.Classical2 CFSG.LocalAnalysis.GLTheoremA.S172C.Rank

private theorem liftableRank_orthDerived_minus_aux1 {F : Type} [Field F] [CharP F 2] {V : Type}
    [AddCommGroup V] [Module F V] {Q : QuadraticForm F V} {n : ℕ} {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {x y : Fin (n - 1) → V} {u v : V}
    (hrot : ∀ i, Q (x i) ≠ 0 ∧ Q (y i) ≠ 0 ∧ orderOf (reflect Q (x i) * reflect Q (y i)) = p)
    (hporth : ∀ i, polar Q u (x i) = 0 ∧ polar Q u (y i) = 0 ∧ polar Q v (x i) = 0 ∧
      polar Q v (y i) = 0)
    (hu : Q u = 0) (hv : Q v = 0) (huv : polar Q u v = 1) :
    Q (u + v) ≠ 0 ∧ (∀ i, polar Q (u + v) (x i) = 0) ∧ (∀ i, polar Q (u + v) (y i) = 0) ∧
      (∀ i, polar Q (x i) (u + v) = 0) ∧ (∀ i, polar Q (y i) (u + v) = 0) ∧
      (∀ i, polar Q (x i) u = 0) ∧ (∀ i, polar Q (y i) u = 0) ∧
      (∀ i, polar Q (x i) (y i) ≠ 0) := by
  have hQc : Q (u + v) ≠ 0 := by
    rw [QuadraticMap.map_add Q, hu, hv, huv]
    simp
  have hcx : ∀ i, polar Q (u + v) (x i) = 0 := fun i => by
    rw [polar_add_left, (hporth i).1, (hporth i).2.2.1, add_zero]
  have hcy : ∀ i, polar Q (u + v) (y i) = 0 := fun i => by
    rw [polar_add_left, (hporth i).2.1, (hporth i).2.2.2, add_zero]
  have hxc : ∀ i, polar Q (x i) (u + v) = 0 := fun i => by rw [polar_comm, hcx]
  have hyc : ∀ i, polar Q (y i) (u + v) = 0 := fun i => by rw [polar_comm, hcy]
  have hxu : ∀ i, polar Q (x i) u = 0 := fun i => by rw [polar_comm]; exact (hporth i).1
  have hyu : ∀ i, polar Q (y i) u = 0 := fun i => by rw [polar_comm]; exact (hporth i).2.1
  have hxy : ∀ i, polar Q (x i) (y i) ≠ 0 := fun i =>
    polar_ne_zero_of_orderOf_reflect_mul_reflect hp hp2 (hrot i).2.2
  exact ⟨hQc, hcx, hcy, hxc, hyc, hxu, hyu, hxy⟩

private theorem liftableRank_orthDerived_minus_aux2 {F : Type} [Field F] [Finite F] [CharP F 2] {V : Type}
    [AddCommGroup V] [Module F V] [FiniteDimensional F V] {Q : QuadraticForm F V} {n : ℕ} {p : ℕ}
    (hQ : (polarBilin Q).Nondegenerate) (hp : p.Prime) (hp2 : p ≠ 2) {x y : Fin (n - 1) → V}
    (hrot : ∀ i, Q (x i) ≠ 0 ∧ Q (y i) ≠ 0 ∧ orderOf (reflect Q (x i) * reflect Q (y i)) = p)
    (hperp : ∀ i j, i ≠ j → polar Q (x i) (x j) = 0 ∧ polar Q (x i) (y j) = 0 ∧
      polar Q (y i) (x j) = 0 ∧ polar Q (y i) (y j) = 0) :
    ∃ ρ : Fin (n - 1) → ↥(orthDerived Q),
      (∀ i, (ρ i : V ≃ₗ[F] V) = reflect Q (x i) * reflect Q (y i)) ∧
      IsElemAbelian p (Subgroup.closure (Set.range ρ)) ∧
      Nat.card (Subgroup.closure (Set.range ρ)) = p ^ (n - 1) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hxy : ∀ i, polar Q (x i) (y i) ≠ 0 := fun i =>
    polar_ne_zero_of_orderOf_reflect_mul_reflect hp hp2 (hrot i).2.2
  let ρ : Fin (n - 1) → ↥(orthDerived Q) := fun i =>
    ⟨reflect Q (x i) * reflect Q (y i),
      reflect_mul_reflect_mem_orthDerived hQ (hrot i).1 (hrot i).2.1⟩
  refine ⟨ρ, fun i => rfl, ?_⟩
  have hcomm : ∀ i j, Commute (ρ i) (ρ j) := by
    intro i j
    by_cases hij : i = j
    · subst hij
      exact Commute.refl _
    · obtain ⟨h1, h2, h3, h4⟩ := hperp i j hij
      exact Subtype.ext (commute_reflect_mul_reflect_rot h1 h2 h3 h4).eq
  have hord : ∀ i, orderOf (ρ i) = p := fun i => by
    show orderOf (⟨_, _⟩ : ↥(orthDerived Q)) = p
    rw [Subgroup.orderOf_mk]
    exact (hrot i).2.2
  have hindep : ∀ i, ρ i ∉ Subgroup.closure (ρ '' {j | j ≠ i}) := by
    refine not_mem_closure_image_of_smul_ne (orthDerived Q).subtype ρ x (fun i => ?_)
      (fun i j hij => ?_)
    · exact reflect_mul_reflect_apply_ne (hrot i).1 (hrot i).2.1 (hxy i)
    · obtain ⟨h1, -, h3, -⟩ := hperp j i (Ne.symm hij)
      exact reflect_mul_reflect_apply_of_polar_eq_zero h1 h3
  exact isElemAbelian_card_closure_range ρ hcomm hord hindep

private theorem liftableRank_orthDerived_minus_aux3 {F : Type} [Field F] [Finite F] [CharP F 2] {V : Type}
    [AddCommGroup V] [Module F V] [FiniteDimensional F V] {Q : QuadraticForm F V} {n : ℕ} {p : ℕ}
    {x y : Fin (n - 1) → V}
    {u v : V} (hQ : (polarBilin Q).Nondegenerate)
    (hrot : ∀ i, Q (x i) ≠ 0 ∧ Q (y i) ≠ 0 ∧ orderOf (reflect Q (x i) * reflect Q (y i)) = p)
    (hperp : ∀ i j, i ≠ j → polar Q (x i) (x j) = 0 ∧ polar Q (x i) (y j) = 0 ∧
      polar Q (y i) (x j) = 0 ∧ polar Q (y i) (y j) = 0)
    (hQc : Q (u + v) ≠ 0) (hxc : ∀ i, polar Q (x i) (u + v) = 0)
    (hyc : ∀ i, polar Q (y i) (u + v) = 0) (hcx : ∀ i, polar Q (u + v) (x i) = 0)
    (hcy : ∀ i, polar Q (u + v) (y i) = 0) {ρ : Fin (n - 1) → ↥(orthDerived Q)}
    (hρ : ∀ i, (ρ i : V ≃ₗ[F] V) = reflect Q (x i) * reflect Q (y i)) :
    ∃ τ : Fin (n - 1) → ↥(orthDerived Q),
      (∀ i, τ i ^ 2 = 1 ∧ τ i * ρ i * (τ i)⁻¹ = (ρ i)⁻¹) ∧
      (∀ i j, i ≠ j → τ i * ρ j = ρ j * τ i) := by
  let τ : Fin (n - 1) → ↥(orthDerived Q) := fun i =>
    ⟨reflect Q (x i) * reflect Q (u + v), reflect_mul_reflect_mem_orthDerived hQ (hrot i).1 hQc⟩
  refine ⟨τ, fun i => ⟨?_, ?_⟩, fun i j hij => ?_⟩
  · exact Subtype.ext (sq_reflect_mul_reflect (hxc i))
  · refine Subtype.ext ?_
    change (reflect Q (x i) * reflect Q (u + v)) * (ρ i : V ≃ₗ[F] V) *
      (reflect Q (x i) * reflect Q (u + v))⁻¹ = (ρ i : V ≃ₗ[F] V)⁻¹
    rw [hρ i]
    exact reflect_mul_reflect_conj_rot (hxc i) (hyc i)
  · obtain ⟨h1, h2, -, -⟩ := hperp i j hij
    refine Subtype.ext ?_
    change (reflect Q (x i) * reflect Q (u + v)) * (ρ j : V ≃ₗ[F] V) =
      (ρ j : V ≃ₗ[F] V) * (reflect Q (x i) * reflect Q (u + v))
    rw [hρ j]
    exact (commute_reflect_mul_reflect_rot h1 h2 (hcx j) (hcy j)).eq

private theorem liftableRank_orthDerived_minus_aux4 {F : Type} [Field F] [CharP F 2] {V : Type}
    [AddCommGroup V] [Module F V] {Q : QuadraticForm F V} {n : ℕ} {p : ℕ} {x y : Fin (n - 1) → V}
    {u v : V} (hn : 2 ≤ n)
    (hrot : ∀ i, Q (x i) ≠ 0 ∧ Q (y i) ≠ 0 ∧ orderOf (reflect Q (x i) * reflect Q (y i)) = p)
    (hporth : ∀ i, polar Q u (x i) = 0 ∧ polar Q u (y i) = 0 ∧ polar Q v (x i) = 0 ∧
      polar Q v (y i) = 0)
    (hu : Q u = 0) (huv : polar Q u v = 1) (hxu : ∀ i, polar Q (x i) u = 0)
    (hyu : ∀ i, polar Q (y i) u = 0) (hxy : ∀ i, polar Q (x i) (y i) ≠ 0)
    {ρ : Fin (n - 1) → ↥(orthDerived Q)}
    (hρ : ∀ i, (ρ i : V ≃ₗ[F] V) = reflect Q (x i) * reflect Q (y i)) :
    (rootGroup Q u).subgroupOf (orthDerived Q) ≠ ⊥ ∧
      Subgroup.closure (Set.range ρ) ≤
        Subgroup.normalizer ((rootGroup Q u).subgroupOf (orthDerived Q) : Set ↥(orthDerived Q)) := by
  have i0 : 0 < n - 1 := by omega
  constructor
  · have hB := hxy ⟨0, i0⟩
    refine subgroupOf_rootGroup_ne_bot (a := x ⟨0, i0⟩) (w := (Q (x ⟨0, i0⟩) / polar Q (x ⟨0, i0⟩)
      (y ⟨0, i0⟩)) • y ⟨0, i0⟩) (f := v) hu (hrot ⟨0, i0⟩).1 (hporth ⟨0, i0⟩).1 ?_ ?_ ?_ ?_
    · rw [polar_smul_right_eq, (hporth ⟨0, i0⟩).2.1, mul_zero]
    · rw [polar_smul_right_eq, div_mul_cancel₀ _ hB]
    · rw [polar_comm, huv]
    · exact (hporth ⟨0, i0⟩).2.2.1
  · rw [Subgroup.closure_le]
    rintro _ ⟨i, rfl⟩
    exact mem_normalizer_subgroupOf_rootGroup
      (by rw [hρ i]; exact reflect_mul_reflect_apply_of_polar_eq_zero (hxu i) (hyu i))

theorem liftableRank_orthDerived_minus {F : Type} [Field F] [Finite F] [CharP F 2] {V : Type}
    [AddCommGroup V] [Module F V] [FiniteDimensional F V] {Q : QuadraticForm F V}
    (hQ : (polarBilin Q).Nondegenerate) {n : ℕ} (hdim : finrank F V = 2 * n)
    (hminus : ¬ IsPlusType Q) (hn : 2 ≤ n) (heven : Even n) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ Nat.card F + 1) :
    S172X.LiftableRank p ↥(orthDerived Q) (n - 1) := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨x, y, u, v, hrot, hperp, hu, hv, huv, hporth⟩ :=
    exists_rotationFrame hQ hdim hminus hn heven hp hp2 hpq
  refine ⟨fun E hE => card_le_pow_pred_of_isElemAbelian_orthDerived hQ hdim hminus (by omega) heven hp
    hp2 hpq E hE, ?_⟩
  obtain ⟨hQc, hcx, hcy, hxc, hyc, hxu, hyu, hxy⟩ :=
    liftableRank_orthDerived_minus_aux1 hp hp2 hrot hporth hu hv huv
  obtain ⟨ρ, hρ, hEA, hcard⟩ := liftableRank_orthDerived_minus_aux2 hQ hp hp2 hrot hperp
  obtain ⟨τ, hτ⟩ :=
    liftableRank_orthDerived_minus_aux3 hQ hrot hperp hQc hxc hyc hcx hcy hρ
  obtain ⟨hTne, hTnorm⟩ :=
    liftableRank_orthDerived_minus_aux4 hn hrot hporth hu huv hxu hyu hxy hρ
  exact ⟨ρ, τ, (rootGroup Q u).subgroupOf (orthDerived Q), hEA, hcard, hτ.1, hτ.2,
    isPGroup_two_subgroupOf_rootGroup u, hTne, hTnorm⟩

end CFSG.LocalAnalysis.GLTheoremA.S172C

end
