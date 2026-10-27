module

public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterTwoAPure
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.FixedFreeRank
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterFiveGmat
public import CFSG.Milestones.CL_LIT_Monster_existence_Griess_Conway
public import CFSG.YGroups.Y443.Tri.AssemblyLit

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterTwoBGmat

theorem exists_isConj_of_mulEquiv {K K' : Type*} [Group K] [Group K'] (e : K ≃* K') {z : K}
    (h : ∀ A : Subgroup K, (∀ a ∈ A, ∀ b ∈ A, a * b = b * a) → (∀ a ∈ A, a ^ 2 = 1) →
      8 ≤ Nat.card A → ∃ u ∈ A, IsConj z u)
    (A : Subgroup K') (hAc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) (hAe : ∀ a ∈ A, a ^ 2 = 1)
    (h8 : 8 ≤ Nat.card A) : ∃ u ∈ A, IsConj (e z) u := by
  obtain ⟨_, ⟨u, hu, rfl⟩, hzu⟩ := h (A.map e.symm.toMonoidHom)
    (by
      rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
      simp only [MulEquiv.coe_toMonoidHom, ← map_mul, hAc x hx y hy])
    (by
      rintro _ ⟨x, hx, rfl⟩
      simp only [MulEquiv.coe_toMonoidHom, ← map_pow, hAe x hx, map_one])
    (by rw [Subgroup.card_map_of_injective e.symm.injective]; exact h8)
  refine ⟨u, hu, isConj_iff.2 ?_⟩
  obtain ⟨g, hg⟩ := isConj_iff.1 hzu
  simp only [MulEquiv.coe_toMonoidHom] at hg
  exact ⟨e g, by rw [← map_inv, ← map_mul, ← map_mul, hg, MulEquiv.apply_symm_apply]⟩

end CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterTwoBGmat


namespace CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterTwoBGmat

open CFSG.Open CFSG.Monster CFSG.Monster.Generated CFSG.Monster.Existence CFSG.Monster.Griess
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance

theorem nineteen_dvd_of_lieModel (X : Type) [Group X]
    (h : CFSG.Blueprint.LieModel X .twistedE6 0 2 1) : 19 ∣ Nat.card X := by
  obtain ⟨e⟩ := CFSG.LieType.Chevalley.C2E6Std.MatrixModel.nonempty_mulEquiv_stdGroup_of_lieModel h
  rw [Nat.card_congr e.toEquiv, CFSG.LieType.Chevalley.C2E6Std.card_stdGroup]
  norm_num

theorem isConj_xGmat_of_twoB (φ : MGriess ≃* Gmat) {z : MGriess} (hz : orderOf z = 2)
    (hB : IsTwoBCentralizer z) : IsConj xGmat (φ z) := by
  have hz' : orderOf (φ z) = 2 := by rw [MulEquiv.orderOf_eq]; exact hz
  rcases CFSG.Monster.Existence.Census.generated_group_two_involution_classes (φ z) hz' with h | h
  · exact h
  · exfalso
    obtain ⟨c, hc⟩ := isConj_iff.1 h
    have h1 := card_centralizer_mulEquiv_apply φ z
    rw [← hc, card_centralizer_conj_eq, MonsterFiveGmat.natCard_centralizer_tGmat] at h1
    have h2 : Nat.card (Subgroup.centralizer ({z} : Set MGriess)) = twoBCentralizerOrder :=
      hB.2.2.2.2.1
    rw [h2] at h1
    norm_num [monsterBabyOrder, twoBCentralizerOrder] at h1

theorem exists_twoB_Gmat (A : Subgroup Gmat) (hAc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
    (hAe : ∀ a ∈ A, a ^ 2 = 1) (h8 : 8 ≤ Nat.card A) : ∃ u ∈ A, IsConj xGmat u := by
  obtain ⟨⟨hfin, -, -, -⟩, a, z, ha, hz, -, hcls, hA, hB, hgraph⟩ :=
    CFSG.Milestones.cl_lit_monster_existence_griess_conway
  obtain ⟨-, c, -, -, hc1, -, -, -, -, hshape, -⟩ := hgraph
  let φ := CFSG.YGroups.Y443.griessEquivGmat CFSG.YGroups.Y443.Gmat_eq_AutO_of_stroth
  obtain ⟨u, hu, hzu⟩ := exists_isConj_of_mulEquiv φ (z := z)
    (exists_twoB_of_elemAbelian babyTableIII babyTableIV nineteen_dvd_of_lieModel ha hA hc1 hshape
      hcls) A hAc hAe h8
  exact ⟨u, hu, (isConj_xGmat_of_twoB φ hz (hB z (IsConj.refl z))).trans hzu⟩

end CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterTwoBGmat
