module

public import CFSG.ClassicalInvolution.Q3.Q3TCCtx

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3TY

open CFSG.Open hiding StatedLieTag StatedLieAdmissible
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD
  CFSG.Assembly.LowTwoRank CFSG.LieType.Universal CFSG.LieType.Universal.Spin
  CFSG.LieType.Universal.Spin.Twisted CFSG.LieType.CurtisTits CFSG.ClassicalInvolution.Q3.Q3W
  CFSG.ClassicalInvolution.Q3.Q3TC
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)


theorem yData3_minus {m : ℕ} (hm : 4 ≤ m) (hadm : StatedLieAdmissible .POmegaMinus m 3 1) :
    YData3 .POmegaMinus m := by
  have hp : Nat.Prime 3 := Nat.prime_three
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  have : Fact (Nat.Prime 3) := ⟨hp⟩
  have hirr := minusCoeffs_irr 3 1
  have h2 : (2 : GaloisField 3 1) ≠ 0 := Q3W.two_ne_zero_gf3
  have hsc : FundamentalSingleClass .POmegaMinus (modelUniv .POmegaMinus m 3 1 hp).D :=
    ModelFacts.fundamentalSingleClass .POmegaMinus m 3 1 hp trivial hadm (by decide) (by decide)
  have hk0 : (⟨0, by omega⟩ : Fin (m - 1)).val + 1 < m - 1 := by simp only; omega
  have hk1 : (⟨1, by omega⟩ : Fin (m - 1)).val + 1 < m - 1 := by simp only; omega
  have hR₀ := rankOne_mem_fund_minus hirr hk0
  have hR₁ := rankOne_mem_fund_minus hirr hk1
  obtain ⟨W₁, hW₁⟩ := WeakCT.linearBlockStandardPair_minusDatum hirr h2 hm
    (i := ⟨0, by omega⟩) (j := ⟨1, by omega⟩) rfl (by simp only; omega)
  have hfin : Finite (modelUniv .POmegaMinus m 3 1 hp).K :=
    finite_spinGroup_quadMinus m (minusCoeffs 3 1).1 (minusCoeffs 3 1).2
  refine ⟨hsc, perfectK_of_admissible hp trivial hadm,
    Q3W.pow3_of_mem_fundamental hsc hR₀ (Q3W.pow3_of_stdPair Q3W.card_gf3 hW₁).1,
    central_of_stdPair hsc hR₀ hW₁, std_of_stdPair hsc hR₀ hR₁ hW₁, ?_⟩
  intro w hw h3
  have hfac := (ModelFacts.OrthAut.minus_center_facts (p := 3) hirr hp2 hm).1
  have hord : orderOf w ≠ 0 := (orderOf_pos w).ne'
  have h1 : orderOf (w ^ (orderOf w / 3)) = 3 := orderOf_pow_orderOf_div hord h3
  have hζ : (w ^ (orderOf w / 3)) ^ 3 = 1 := by
    have := pow_orderOf_eq_one (w ^ (orderOf w / 3))
    rwa [h1] at this
  have hcen : w ^ (orderOf w / 3) ∈ Subgroup.center _ := Subgroup.pow_mem _ hw _
  have h0 := hfac _ hcen hζ
  have h0' : w ^ (orderOf w / 3) = (1 : (modelUniv .POmegaMinus m 3 1 hp).K) := h0
  rw [h0', orderOf_one] at h1
  omega


theorem nonempty_fund_minus3 {m : ℕ} (hm : 4 ≤ m) :
    (fundamentalSubgroups .POmegaMinus (modelUniv .POmegaMinus m 3 1 Nat.prime_three).D).Nonempty :=
  ⟨_, rankOne_mem_fund_minus (minusCoeffs_irr 3 1) (k := (⟨0, by omega⟩ : Fin (m - 1)))
    (by simp only; omega)⟩

end CFSG.ClassicalInvolution.Q3.Q3TY

namespace CFSG.ClassicalInvolution.Q3.Q3TC.TCtx3

open CFSG.Open hiding StatedLieTag StatedLieAdmissible
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD
  CFSG.Assembly.LowTwoRank CFSG.LieType.Universal CFSG.LieType.Universal.Spin
  CFSG.LieType.Universal.Spin.Twisted CFSG.LieType.CurtisTits CFSG.ClassicalInvolution.Q3.Q3W
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)


variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {z : G} {tY : StatedLieTag}
  {nY : ℕ} {K : Subgroup G}

theorem exists_nodes_gen3 (c : TCtx3 tY nY Ω K z) {r : ℕ}
    (R : Fin r → Subgroup (modelUniv tY nY 3 1 Nat.prime_three).K)
    (hR : ∀ a, R a ∈ fundamentalSubgroups tY (modelUniv tY nY 3 1 Nat.prime_three).D)
    (adj : Fin r → Fin r → Prop)
    (hcomm : ∀ a b, a ≠ b → ¬ adj a b → ¬ adj b a → Commutes (R a) (R b))
    (hstd : ∀ a b, adj a b → ∃ W : Subgroup (modelUniv tY nY 3 1 Nat.prime_three).K,
      LinearBlockStandardPair (GaloisField 3 1) W (R a) (R b)) :
    ∃ j : Fin r → Subgroup G, (∀ a, j a ∈ centralizingMembers Ω {z} ∧ j a ≠ K ∧
        ¬ locImg Ω z (j a) ≤ c.d.Q₁ ∧ locImg Ω z (j a) = (R a).map c.d.ψ) ∧
      (∀ a b, a ≠ b → ¬ adj a b → ¬ adj b a → Commutes (j a) (j b)) ∧
      (∀ a b, adj a b → ∃ W : Subgroup G,
        LinearBlockStandardPair (GaloisField 3 1) W (j a) (j b)) ∧
      (∀ a, Commutes K (j a)) := by
  choose j hj using fun a => c.exists_member_of_fund (hR a)
  refine ⟨j, fun a => ⟨(hj a).1, (hj a).2.1, (hj a).2.2.1, (hj a).2.2.2⟩, ?_, ?_, ?_⟩
  · intro a b hab h1 h2
    exact (c.commutes_iff_fund (hj a).1 (hj b).1 (hR a) (hj a).2.2.2 (hj b).2.2.2).mpr
      (hcomm a b hab h1 h2)
  · intro a b hadj
    obtain ⟨W, hW⟩ := hstd a b hadj
    exact c.stdPair_of_fund (hj a).1 (hj b).1 hW (hj a).2.2.2 (hj b).2.2.2
  · intro a
    exact c.commutes_K_of_ne (hj a).1 (hj a).2.1

theorem exists_nodes_minus3 {m : ℕ} (hm : 4 ≤ m) (c : TCtx3 .POmegaMinus m Ω K z) :
    ∃ j : Fin (m - 2) → Subgroup G, (∀ a, j a ∈ centralizingMembers Ω {z} ∧ j a ≠ K ∧
        ¬ locImg Ω z (j a) ≤ c.d.Q₁) ∧
      (∀ a b : Fin (m - 2), a.val + 1 < b.val → Commutes (j a) (j b)) ∧
      (∀ a b : Fin (m - 2), a.val + 1 = b.val → ∃ W : Subgroup G,
        LinearBlockStandardPair (GaloisField 3 1) W (j a) (j b)) ∧
      (∀ a, Commutes K (j a)) ∧
      (∀ a : Fin (m - 2), locImg Ω z (j a) =
        (rankOne (minusDatum m (minusCoeffs_irr 3 1)).rootGroup
          (⟨a.val, by have := a.2; omega⟩ : Fin (m - 1))).map c.d.ψ) := by
  have hirr := minusCoeffs_irr 3 1
  let nd : Fin (m - 2) → Fin (m - 1) := fun a => ⟨a.val, by have := a.2; omega⟩
  have hlong : ∀ a : Fin (m - 2), (nd a).val + 1 < m - 1 := fun a => by
    have := a.2
    simp only [nd]
    omega
  obtain ⟨j, hj, hjc, hjp, hjK⟩ := c.exists_nodes_gen3
    (fun a : Fin (m - 2) => rankOne (minusDatum m hirr).rootGroup (nd a))
    (fun a => rankOne_mem_fund_minus hirr (hlong a))
    (fun a b => a.val + 1 = b.val)
    (fun a b hab h1 h2 => by
      rcases lt_or_gt_of_ne (fun h => hab (Fin.ext h) : a.val ≠ b.val) with hlt | hgt
      · exact fun x hx y hy => CFSG.ClassicalInvolution.WeakCT.commute_rankOne_minusDatum hirr
          (nd a) (nd b) (by simp only [nd]; omega) x hx y hy
      · exact fun x hx y hy => (CFSG.ClassicalInvolution.WeakCT.commute_rankOne_minusDatum hirr
          (nd b) (nd a) (by simp only [nd]; omega) y hy x hx).symm)
    (fun a b hab => CFSG.ClassicalInvolution.WeakCT.linearBlockStandardPair_minusDatum hirr
      Q3W.two_ne_zero_gf3 hm (i := nd a) (j := nd b) hab (hlong b))
  refine ⟨j, fun a => ⟨(hj a).1, (hj a).2.1, (hj a).2.2.1⟩, fun a b hab => ?_, hjp, hjK,
    fun a => (hj a).2.2.2⟩
  exact hjc a b (Fin.ne_of_val_ne (by omega)) (by show ¬ (a.val + 1 = b.val); omega)
    (by show ¬ (b.val + 1 = a.val); omega)

end CFSG.ClassicalInvolution.Q3.Q3TC.TCtx3
