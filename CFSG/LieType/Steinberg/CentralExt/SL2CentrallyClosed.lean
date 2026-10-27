module

public import CFSG.LieType.Steinberg.CentralExt.TorusLift
public import CFSG.LocalAnalysis.SectionRank.EvenCover.SLTwo
public import CFSG.LinearAlgebra.LinearGroups.Perfect
public import CFSG.RankThree.PerfectCover.HopfCentralCoversSetup

public section

open Matrix CFSG.LieType.Steinberg CFSG.SectionRank.EvenCover
open scoped commutatorElement

namespace CFSG.LieType.Steinberg.CentralExt.SL2Closed

variable {k : Type} [Field k] [Finite k]

omit [Field k] in
theorem exists_four_of_five_le (hk : 5 ≤ Nat.card k) : ∃ s : Finset k, s.card = 4 := by
  have : Fintype k := Fintype.ofFinite k
  obtain ⟨s, hs⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset k)) (n := 4)
    (by rw [Finset.card_univ, Fintype.card_eq_nat_card]; omega)
  exact ⟨s, hs.2⟩

theorem exists_sq_ne_one (hk : 5 ≤ Nat.card k) : ∃ u : k, u ≠ 0 ∧ u ^ 2 ≠ 1 := by
  obtain ⟨l, hl⟩ := LinearGroups.field_scalar_with_nontrivial_square (exists_four_of_five_le hk)
  refine ⟨l, l.ne_zero, fun h => hl (Units.ext ?_)⟩
  simpa using h

omit [Finite k] in
theorem sl2_cells_one : ∀ a t : k, t ≠ 0 → (sl2Rels k).x a * (sl2Rels k).h t = 1 →
    a = 0 ∧ t = 1 := by
  intro a t ht h
  have h' := congrArg (fun M : SpecialLinearGroup (Fin 2) k => (M : Matrix (Fin 2) (Fin 2) k)) h
  simp only [Matrix.SpecialLinearGroup.coe_mul, sl2Rels_x, coe_sl2Upper, coe_sl2Rels_h ht,
    Matrix.SpecialLinearGroup.coe_one] at h'
  have h00 := congrFun (congrFun h' 0) 0
  have h01 := congrFun (congrFun h' 0) 1
  simp [Matrix.mul_apply, Fin.sum_univ_two] at h00 h01
  subst h00
  simpa using h01

omit [Finite k] in
theorem sl2_cells_two : ∀ a b t : k, t ≠ 0 →
    (sl2Rels k).x a * (sl2Rels k).w 1 * (sl2Rels k).x b * (sl2Rels k).h t ≠ 1 := by
  intro a b t ht h
  have h' := congrArg (fun M : SpecialLinearGroup (Fin 2) k => (M : Matrix (Fin 2) (Fin 2) k)) h
  simp only [Matrix.SpecialLinearGroup.coe_mul, sl2Rels_x, coe_sl2Upper, coe_sl2Rels_h ht,
    coe_sl2Rels_w one_ne_zero, Matrix.SpecialLinearGroup.coe_one] at h'
  have h10 := congrFun (congrFun h' 1) 0
  simp [Matrix.mul_apply, Fin.sum_univ_two] at h10
  exact ht h10

theorem sl2_exists_section_of_central
    (hk : 5 ≤ Nat.card k) (hk9 : Nat.card k ≠ 9) {E : Type*} [Group E]
    {π : E →* SpecialLinearGroup (Fin 2) k} (hπ : Function.Surjective π)
    (hcen : π.ker ≤ Subgroup.center E) :
    ∃ σ : SpecialLinearGroup (Fin 2) k →* E, ∀ g, π (σ g) = g := by
  obtain ⟨u, hu0, hu1⟩ := exists_sq_ne_one hk
  obtain ⟨φ, hφ⟩ := (sl2Rels k).exists_section_of_central (by omega) hk9 hu0 hu1 sl2_cells_one
    sl2_cells_two hπ hcen
  let e : SpecialLinearGroup (Fin 2) k ≃* (sl2Rels k).sub :=
    Subgroup.topEquiv.symm.trans (MulEquiv.subgroupCongr sl2Rels_sub.symm)
  exact ⟨φ.comp e.toMonoidHom, fun g => hφ (e g)⟩

section Hopf

open CFSG.RankThree.PerfectCover

theorem ker_eq_bot_of_section {U E : Type*} [Group U] [Group E] [Group.IsPerfect U]
    (f : U →* E) (hker : f.ker ≤ Subgroup.center U) (σ : E →* U) (hσ : ∀ e, f (σ e) = e) :
    f.ker = ⊥ := by
  have hz : ∀ u : U, (σ (f u))⁻¹ * u ∈ f.ker := fun u => by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hσ, inv_mul_cancel]
  have hdec : ∀ u : U, u = σ (f u) * ((σ (f u))⁻¹ * u) := fun u => by group
  have hcomm : ∀ u v : U, ⁅u, v⁆ ∈ σ.range := fun u v => by
    have e1 : ⁅u, v⁆ = ⁅σ (f u), σ (f v)⁆ := by
      conv_lhs => rw [hdec u, hdec v]
      rw [TorusLift.commutatorElement_mul_central_left (hker (hz u)),
        TorusLift.commutatorElement_mul_central_right (hker (hz v))]
    rw [e1, ← map_commutatorElement]
    exact ⟨_, rfl⟩
  have hrange : σ.range = ⊤ := by
    rw [eq_top_iff, ← Group.IsPerfect.commutator_eq_top (G := U), _root_.commutator_def,
      Subgroup.commutator_le]
    intro u _ v _
    exact hcomm u v
  rw [eq_bot_iff]
  intro u hu
  obtain ⟨e, rfl⟩ : u ∈ σ.range := hrange ▸ Subgroup.mem_top u
  rw [MonoidHom.mem_ker, hσ] at hu
  rw [hu, map_one]
  exact Subgroup.one_mem _

theorem hopfMultiplierToKer_bijective {E X : Type*} [Group E] [Group X] [Group.IsPerfect X]
    [Group.IsPerfect E] (q : E →* X) (hq : Function.Surjective q)
    (hker : q.ker ≤ Subgroup.center E)
    (hsplit : ∀ (π : HopfCover X →* E), Function.Surjective π →
      π.ker ≤ Subgroup.center (HopfCover X) → ∃ σ : E →* HopfCover X, ∀ e, π (σ e) = e) :
    Function.Bijective (hopfMultiplierToKer q hq hker) := by
  refine ⟨?_, hopfMultiplierToKer_surjective q hq hker⟩
  have hker' : (hopfLift q hq hker).ker ≤ Subgroup.center (HopfCover X) := by
    intro u hu
    apply hopfMultiplier_le_center
    rw [MonoidHom.mem_ker] at hu ⊢
    rw [← comp_hopfLift q hq hker, MonoidHom.comp_apply, hu, map_one]
  have : Group.IsPerfect (HopfCover X) := hopfCover_isPerfect
  obtain ⟨σ, hσ⟩ := hsplit _ (hopfLift_surjective q hq hker) hker'
  have hbot := ker_eq_bot_of_section _ hker' σ hσ
  rw [← MonoidHom.ker_eq_bot_iff, hopfMultiplierToKer_ker, hbot, Subgroup.bot_subgroupOf]

end Hopf

theorem sl2_hopfMultiplier_mulEquiv_ker
    (hk : 5 ≤ Nat.card k) (hk9 : Nat.card k ≠ 9) {X : Type} [Group X]
    (q : SpecialLinearGroup (Fin 2) k →* X) (hq : Function.Surjective q)
    (hker : q.ker ≤ Subgroup.center (SpecialLinearGroup (Fin 2) k)) :
    Nonempty (CFSG.RankThree.PerfectCover.hopfMultiplier X ≃* q.ker) := by
  have : Group.IsPerfect (SpecialLinearGroup (Fin 2) k) :=
    LinearGroups.special_linear_dimension_two_perfect (exists_four_of_five_le hk)
  have : Group.IsPerfect X := Group.IsPerfect.ofSurjective hq
  exact ⟨MulEquiv.ofBijective _ (hopfMultiplierToKer_bijective q hq hker fun π hπ hcen =>
    sl2_exists_section_of_central hk hk9 hπ hcen)⟩

end CFSG.LieType.Steinberg.CentralExt.SL2Closed

