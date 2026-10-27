module

public import CFSG.HardMathSupport.Dickson.BMRows.M13B
public import CFSG.HardMathSupport.Dickson.BMRows.RowsM
public import CFSG.HardMathSupport.Dickson.Sec6.I1431SporAux.ThirteenGmat
public import CFSG.HardMathSupport.Dickson.Sec6.I1431SporAux.ThirteenGraphMonster
public import CFSG.Sporadic.Bridge.MonsterModelsGriess

public section

set_option linter.unusedSectionVars false

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.HardMathSupport.Dickson.BMRows

open Subgroup CFSG.Blueprint CFSG.Monster CFSG.Monster.Generated CFSG.Monster.Existence
  CFSG.AGLEmbedding.Norton.MON5_7 CFSG.AGLEmbedding.Norton.GenD13 CFSG.AGLEmbedding.Norton.MON11_13
  CFSG.HardMathSupport.Timmesfeld.Proving CFSG.Open CFSG.Yardstones.Md0ec50421ce4
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterThirteenLocal
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterThirteenB
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterThirteen
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThreeBNF
  CFSG.HardMathSupport.Dickson.Sec6.I1431
open CFSG.Blueprint.NativeSporadic (Carrier)
open CFSG.LocalAnalysis.GLTheoremA

section Generic

theorem card_centralizer_le_mul {G : Type*} [Group G] [Finite G] {x u : G} (hu : u ∈ invComm x)
    {A B : ℕ} (hA : (invComm x).ncard ≤ A)
    (hB : Nat.card ↥(Subgroup.centralizer ({u} : Set G) ⊓ Subgroup.centralizer ({x} : Set G)) ≤ B) :
    Nat.card ↥(Subgroup.centralizer ({x} : Set G)) ≤ A * B := by
  have hxC : u ∈ Subgroup.centralizer ({x} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.2 hu.2.2
  let t : ↥(Subgroup.centralizer ({x} : Set G)) := ⟨u, hxC⟩
  have hclass := card_isConj_mul_card_centralizer t
  have hcent : Nat.card ↥(Subgroup.centralizer ({t} : Set ↥(Subgroup.centralizer ({x} : Set G)))) =
      Nat.card ↥(Subgroup.centralizer ({u} : Set G) ⊓ Subgroup.centralizer ({x} : Set G)) :=
    card_centralizer_subtype_eq hxC
  have hcls : Nat.card {h : ↥(Subgroup.centralizer ({x} : Set G)) // IsConj t h} ≤
      (invComm x).ncard := by
    rw [← Nat.card_coe_set_eq]
    refine Nat.card_le_card_of_injective (fun h => ⟨(h.1 : G), ?_⟩) ?_
    · obtain ⟨c, hc⟩ := isConj_iff.1 h.2
      have hh : (h.1 : G) = (c : G) * u * (c : G)⁻¹ := by
        rw [← hc]
        rfl
      rw [hh]
      exact conj_mem_invComm (Subgroup.mem_centralizer_singleton_iff.1 c.2) hu
    · intro h h' hh
      have h1 := congrArg Subtype.val hh
      exact Subtype.ext (Subtype.ext h1)
  calc Nat.card ↥(Subgroup.centralizer ({x} : Set G))
      = Nat.card {h : ↥(Subgroup.centralizer ({x} : Set G)) // IsConj t h} *
          Nat.card ↥(Subgroup.centralizer ({t} : Set ↥(Subgroup.centralizer ({x} : Set G)))) :=
        hclass.symm
    _ ≤ A * B := Nat.mul_le_mul (hcls.trans hA) (hcent ▸ hB)

theorem card_centralizer_le_of_graph {G : Type} [Group G] [Finite G] {B : Type} [Group B]
    [Finite B] {P : B → Prop} {a : G} {c : Fin 9 → G} (D : ThirteenGraphData P a c) {x : G}
    (hx : orderOf x = 13)
    (hA1 : ∀ u : G, u * u = 1 → u ≠ 1 → u * x = x * u → IsConj a u) {u : G} (hu2 : u * u = 1)
    (hu1 : u ≠ 1) (hux : u * x = x * u) :
    Nat.card ↥(Subgroup.centralizer ({x} : Set G)) ≤ 451 * 936 :=
  card_centralizer_le_mul ⟨hu2, hu1, hux⟩ (ncard_invComm_le D hx hA1)
    (card_cent_inf_le D hx hA1 hu2 hu1 hux)

end Generic

section Order


theorem card_centralizer_xE_le (φ : Gmat ≃* MGriess) :
    Nat.card ↥(Subgroup.centralizer ({gw thirteenX} : Set Gmat)) ≤ 451 * 936 := by
  obtain ⟨⟨hfin, -, -, -⟩, a, z, ha, hz, hnc, hcls, hA, hBz, hgraph⟩ :=
    CFSG.Milestones.cl_lit_monster_existence_griess_conway
  haveI : Finite MGriess := hfin
  have ht2 : orderOf (φ tGmat) = 2 := by
    rw [MulEquiv.orderOf_eq]
    exact CFSG.Monster.Tri.orderOf_tGmat
  have haconj : IsConj a (φ tGmat) := by
    rcases hcls _ ht2 with h | h
    · exact h
    · exfalso
      obtain ⟨-, -, -, -, -, h17⟩ := hBz _ h
      apply h17
      show 17 ∣ Nat.card (Subgroup.centralizer ({φ tGmat} : Set MGriess))
      rw [CFSG.HardMathSupport.Timmesfeld.SporadicBalance.card_centralizer_mulEquiv_apply φ tGmat,
        CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterFiveGmat.natCard_centralizer_tGmat]
      norm_num [monsterBabyOrder]
  have hx : orderOf (φ (gw thirteenX)) = 13 := by
    rw [MulEquiv.orderOf_eq]
    exact orderOf_xE
  have hA1 : ∀ u : MGriess, u * u = 1 → u ≠ 1 → u * φ (gw thirteenX) = φ (gw thirteenX) * u →
      IsConj a u := by
    intro u hu2 hu1 hux
    have hv2 : φ.symm u * φ.symm u = 1 := by rw [← map_mul, hu2, map_one]
    have hv1 : φ.symm u ≠ 1 := fun h1 => hu1 (by simpa using congrArg φ h1)
    have hvx : φ.symm u * gw thirteenX = gw thirteenX * φ.symm u := by
      apply φ.injective
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
      exact hux
    have hvc : IsConj tGmat (φ.symm u) := isConj_tGmat_of_commute_xE hv2 hv1 hvx
    have hc : IsConj (φ tGmat) u := by
      have := (φ : Gmat →* MGriess).map_isConj hvc
      simpa using this
    exact haconj.trans hc
  obtain ⟨c, D⟩ := thirteenGraphData_of_existence ha hA hgraph
  obtain ⟨hj2, -, -, hj1x, -, -, -, -, hj1, -, -, -⟩ := thirteen_a_facts
  have key := card_centralizer_le_of_graph D hx hA1 (u := φ (gw j1W))
    (by rw [← map_mul, hj2, map_one])
    (fun h1 => hj1 (φ.injective (by rw [h1, map_one])))
    (by rw [← map_mul, ← map_mul, hj1x])
  rwa [CFSG.HardMathSupport.Timmesfeld.SporadicBalance.card_centralizer_mulEquiv_apply φ] at key

theorem card_centralizer_conj_xE_le (φ : Gmat ≃* MGriess) {s m : Gmat} {k : ℕ} (hk : k % 13 ≠ 0)
    (h : m * s * m⁻¹ = gw thirteenX ^ k) :
    Nat.card ↥(Subgroup.centralizer ({s} : Set Gmat)) ≤ 451 * 936 := by
  haveI : Finite Gmat := generated_rational_group_finite_simple.2.2
  haveI : Fact (Nat.Prime 13) := ⟨by norm_num⟩
  have hk1 : gw thirteenX ^ k ≠ 1 := by
    intro h1
    have := orderOf_dvd_of_pow_eq_one h1
    rw [orderOf_xE] at this
    exact hk (Nat.mod_eq_zero_of_dvd this)
  rw [← CFSG.HardMathSupport.Timmesfeld.SporadicBalance.card_centralizer_conj_eq m, h,
    CFSG.HardMathSupport.Timmesfeld.SporadicBalance.centralizer_pow_eq_of_prime orderOf_xE hk1]
  exact card_centralizer_xE_le φ

theorem acompOK_conj_xE (φ : Gmat ≃* MGriess) {s m : Gmat} {k : ℕ} (hs : orderOf s = 13)
    (hk : k % 13 ≠ 0) (h : m * s * m⁻¹ = gw thirteenX ^ k) :
    I1415Rows.ACompOK 13 s := by
  haveI : Finite Gmat := generated_rational_group_finite_simple.2.2
  refine I1415Rows.acompOK_of_not_dvd_card (by norm_num) hs fun hdvd => ?_
  have h1 := Nat.le_of_dvd Nat.card_pos hdvd
  have h2 := card_centralizer_conj_xE_le φ hk h
  omega

end Order

section Rows


theorem acompOK_gmat_thirteen (φ : Gmat ≃* MGriess) {s : Gmat} (hs : orderOf s = 13) :
    I1415Rows.ACompOK 13 s := by
  obtain ⟨m, k, hk, h | h⟩ := census_thirteen s hs
  · exact acompOK_conj_c13 hk h
  · exact acompOK_conj_xE φ hs hk h

theorem acompOK_M_thirteen :
    ∀ k : Carrier .M, orderOf k = 13 → I1415Rows.ACompOK 13 k := by
  obtain ⟨e₀⟩ := CFSG.Blueprint.NativeSporadic.MonsterModel.iso_griess_y443Derived
  let e : CFSG.Monster.Existence.MGriess ≃* Carrier .M := e₀
  have φ := CFSG.YGroups.Y443.griessEquivGmat CFSG.YGroups.Y443.Gmat_eq_AutO_of_stroth
  let eG : Gmat ≃* Carrier .M := φ.symm.trans e
  haveI : Finite Gmat := CFSG.Monster.Generated.finite_Gmat
  haveI : Finite (Carrier .M) := Finite.of_equiv Gmat eG.toEquiv
  intro k hk
  have hs : orderOf (eG.symm k) = 13 := by
    rw [MulEquiv.orderOf_eq]
    exact hk
  have h := I1415Rows.ACompOK.of_mulEquiv (by norm_num : Nat.Prime 13) eG
    (acompOK_gmat_thirteen φ.symm hs)
  rwa [MulEquiv.apply_symm_apply] at h

theorem i1415Row_M_thirteen : I1415Rows.I1415Row .M 13 := by
  obtain ⟨_, _, ⟨b⟩, hnc⟩ := model_M
  exact I1415Rows.arow_of_model sporadicOuterLeTwo_holds b hnc acompOK_M_thirteen

end Rows

end CFSG.HardMathSupport.Dickson.BMRows
