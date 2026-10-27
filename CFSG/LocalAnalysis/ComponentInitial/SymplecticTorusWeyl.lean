module

public import CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeylQuotient

public section

namespace CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl

open Matrix CFSG.Assembly.LowTwoRank CFSG.LieType.CentralExt

variable {r : ℕ} {k : Type} [Field k] {E : Type*} [Group E] [Finite k] [Finite E]
  {π : E →* StatedSp r k}

noncomputable def torusEquiv : (Fin r → kˣ) ≃* torus r k :=
  MonoidHom.ofInjective (torusHom_injective (r := r) (k := k))

omit [Finite k] in
theorem coe_torusEquiv (t : Fin r → kˣ) :
    ((torusEquiv t : torus r k) : StatedSp r k) = torusHom t :=
  MonoidHom.ofInjective_apply _

noncomputable def liftTorusEquiv (hS : Hyp π) : (Fin r → kˣ) ≃* liftTorus π :=
  (MonoidHom.ofInjective (thetaHom_injective hS)).trans (MulEquiv.subgroupCongr (range_thetaHom hS))

theorem coe_liftTorusEquiv (hS : Hyp π) (t : Fin r → kˣ) :
    ((liftTorusEquiv hS t : liftTorus π) : E) = thetaHom hS t := by
  rw [liftTorusEquiv, MulEquiv.trans_apply, MulEquiv.subgroupCongr_apply,
    MonoidHom.ofInjective_apply]

noncomputable def thetaEquiv (hS : Hyp π) : torus r k ≃* liftTorus π :=
  (torusEquiv (r := r) (k := k)).symm.trans (liftTorusEquiv hS)

theorem thetaEquiv_torusHom (hS : Hyp π) (t : Fin r → kˣ) :
    (thetaEquiv hS ⟨torusHom t, torusHom_mem_torus t⟩ : E) = thetaHom hS t := by
  have h : (⟨torusHom t, torusHom_mem_torus t⟩ : torus r k) = torusEquiv t :=
    Subtype.ext (coe_torusEquiv t).symm
  rw [h, thetaEquiv, MulEquiv.trans_apply, MulEquiv.symm_apply_apply, coe_liftTorusEquiv]

theorem pi_thetaEquiv (hS : Hyp π) (x : torus r k) : π (thetaEquiv hS x) = x := by
  obtain ⟨_, ⟨t, rfl⟩⟩ := x
  rw [thetaEquiv_torusHom, ← MonoidHom.comp_apply π, comp_thetaHom hS]

@[expose] noncomputable def weylQuotientEquiv (hS : Hyp π)
    [((liftTorus π).subgroupOf (liftWeyl π)).Normal] :
    liftWeyl π ⧸ (liftTorus π).subgroupOf (liftWeyl π) ≃* signedPermGroup r :=
  (QuotientGroup.quotientMulEquivOfEq (ker_weylHom hS).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective (weylHom hS) (weylHom_surjective hS))

theorem weylQuotientEquiv_mk (hS : Hyp π) [((liftTorus π).subgroupOf (liftWeyl π)).Normal]
    (n : liftWeyl π) : weylQuotientEquiv hS n = weylHom hS n :=
  rfl

theorem sLift_sq_mem (hS : Hyp π) (i : Fin r) : sLift π i ^ 2 ∈ liftTorus π := by
  rw [sq]
  by_cases h : i.val + 1 < r
  · rw [sLift_of_lt h, vLiftRho_mul_self]
    exact hLiftRho_mem hS _ _
  · rw [sLift_of_not_lt h, vLift_mul_self]
    exact hLift_mem _ _

theorem odd_symplectic_lifted_torus_and_weyl {k : Type} [Field k] [Finite k]
    (hk : ringChar k ≠ 2) {r : ℕ} (_hr : 1 ≤ r) {E : Type*} [Group E] [Finite E]
    {π : E →* StatedSp r k} (hπ : Function.Surjective π) (hcen : π.ker ≤ Subgroup.center E)
    (h2 : IsPGroup 2 π.ker) :
    IsMulCommutative (liftTorus π) ∧
    (∀ (i j : Fin r) (hij : i ≠ j) (a : kˣ),
      hLiftRho π i j hij a = hLift π i a * (hLift π j a)⁻¹) ∧
    (∃ θ : torus r k ≃* liftTorus π,
      (∀ t : Fin r → kˣ, (θ ⟨torusHom t, torusHom_mem_torus t⟩ : E) =
        (List.ofFn fun i => hLift π i (t i)).prod) ∧
      ∀ x : torus r k, π (θ x) = x) ∧
    liftTorus π ≤ liftWeyl π ∧
    liftWeyl π ≤ Subgroup.normalizer (liftTorus π : Set E) ∧
    (∀ i : Fin r, vLift π i ∈ liftWeyl π) ∧
    (∃ φ : liftWeyl π →* signedPermGroup r,
      (∀ (n : liftWeyl π) (x y : Fin r ⊕ Fin r),
        (((π n : StatedSp r k) : GL (Fin r ⊕ Fin r) k) :
          Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) k) y x ≠ 0 ↔
          y = (φ n : Equiv.Perm (Fin r ⊕ Fin r)) x) ∧
      Function.Surjective φ ∧ φ.ker = (liftTorus π).subgroupOf (liftWeyl π) ∧
      ∃ _ : ((liftTorus π).subgroupOf (liftWeyl π)).Normal,
        ∃ e : liftWeyl π ⧸ (liftTorus π).subgroupOf (liftWeyl π) ≃* signedPermGroup r,
          ∀ n : liftWeyl π, e n = φ n) ∧
    Function.Injective (π.comp (liftWeyl π).subtype) ∧
    ∀ i : Fin r, sLift π i ^ 2 ∈ liftTorus π := by
  have hS : Hyp π := ⟨hk, hπ, hcen, h2⟩
  have hN := normal_liftTorus_subgroupOf hS
  refine ⟨⟨⟨fun x y => Subtype.ext (liftTorus_commute hS x.2 y.2).eq⟩⟩,
    fun i j hij a => hLiftRho_eq hS hij a,
    ⟨thetaEquiv hS, fun t => by rw [thetaEquiv_torusHom, thetaHom_apply], pi_thetaEquiv hS⟩,
    liftTorus_le_liftWeyl, liftWeyl_le_normalizer hS, vLift_mem hS,
    ⟨weylHom hS, fun n x y => isLinePerm_weylHom hS n x y, weylHom_surjective hS,
      ker_weylHom hS, hN, weylQuotientEquiv hS, weylQuotientEquiv_mk hS⟩,
    injective_pi_comp hS, sLift_sq_mem hS⟩

end CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl
