module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2PerfectEight
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2PositionBHigh

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup Matrix Equiv CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_injective mat_elt elt E)
open CFSG.Quasithin (perfectCore perfectCore_le le_perfectCore_of_perfect perfectCore_perfect)
open CFSG.SeitzReduction.E6Pilot (IsAutConjIn)

variable {K : Type} [Field K]

section OrderThree

@[expose] noncomputable def sp4YLong : StatedSp 2 K :=
  elt (.positiveLong 1) 1 * elt (.negativeLong 1) 1

@[expose] noncomputable def sp4YShort : StatedSp 2 K :=
  elt (.difference 0 1 (by decide)) 1 * elt (.difference 1 0 (by decide)) 1

theorem exists_conj_eq_yLong_or_yShort (hK : Nat.card K = 2) {y : StatedSp 2 K}
    (hy : orderOf y = 3) :
    ∃ g : StatedSp 2 K, g * sp4YLong * g⁻¹ = y ∨ g * sp4YShort * g⁻¹ = y := by
  have : Finite K := Nat.finite_of_card_ne_zero (by omega)
  set E := F4Pilot.sp4EquivPerm hK with hE
  have hEy : orderOf (E y) = 3 := by rw [MulEquiv.orderOf_eq]; exact hy
  have key : ∀ {x : StatedSp 2 K}, IsConj (E x) (E y) →
      ∃ g : StatedSp 2 K, g * x * g⁻¹ = y := by
    intro x hc
    obtain ⟨c, hc⟩ := isConj_iff.1 hc
    refine ⟨E.symm c, E.injective ?_⟩
    rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply, hc]
  rcases F4Pilot.isConj_finSix_of_orderOf_eq_three hEy with h | h
  · obtain ⟨g, hg⟩ := key (x := sp4YLong) (by
      rwa [sp4YLong, map_mul, hE, F4Pilot.sp4EquivPerm_elt_long, F4Pilot.sp4EquivPerm_elt_long_neg])
    exact ⟨g, Or.inl hg⟩
  · obtain ⟨g, hg⟩ := key (x := sp4YShort) (by
      rwa [sp4YShort, map_mul, hE, F4Pilot.sp4EquivPerm_elt_short,
        F4Pilot.sp4EquivPerm_elt_short_neg])
    exact ⟨g, Or.inr hg⟩

theorem eq_zero_of_vecMul_yShort [CharP K 2] {v : Fin 2 ⊕ Fin 2 → K}
    (h : Matrix.vecMul v (mat 2 K sp4YShort) = v) : v = 0 := by
  rw [sp4YShort, map_mul, mat_elt, mat_elt, one_smul, one_smul, ← Matrix.vecMul_vecMul] at h
  have a1 := congrFun h (Sum.inl 0)
  have a2 := congrFun h (Sum.inl 1)
  have a3 := congrFun h (Sum.inr 0)
  have a4 := congrFun h (Sum.inr 1)
  simp [Matrix.vecMul, dotProduct, E, Matrix.single_apply, Matrix.add_apply, Matrix.sub_apply,
    Matrix.one_apply, Fintype.sum_sum_type, Fin.sum_univ_two] at a1 a2 a3 a4
  funext x
  rcases x with x | x <;> fin_cases x
  · simpa using a2
  · simp only [Fin.mk_one, Fin.isValue, Pi.zero_apply]
    linear_combination a1 - a2
  · simp only [Fin.zero_eta, Fin.isValue, Pi.zero_apply]
    linear_combination a3 - a4
  · simpa using a3

end OrderThree

section F5

variable [Finite K] [CharP K 2]

omit [Finite K] [CharP K 2] in
theorem coe_symm_mem_wCenter_of_compat {M : Subgroup (StatedSp (1 + 3) K)}
    (β : (wRadical K (1 : Fin (1 + 3)) 2 ⊔ M : Subgroup (StatedSp (1 + 3) K)) ≃*
      (wRadical K (1 : Fin (1 + 3)) 2 ⊔ M : Subgroup (StatedSp (1 + 3) K)))
    (hβ : ∀ y : (wRadical K (1 : Fin (1 + 3)) 2 ⊔ M : Subgroup (StatedSp (1 + 3) K)),
      ((β y : StatedSp (1 + 3) K) ∈ wRadical K (1 : Fin (1 + 3)) 2 ↔
        (y : StatedSp (1 + 3) K) ∈ wRadical K (1 : Fin (1 + 3)) 2))
    (x : (wRadical K (1 : Fin (1 + 3)) 2 ⊔ M : Subgroup (StatedSp (1 + 3) K)))
    (hx : (x : StatedSp (1 + 3) K) ∈ wCenter K 1) :
    (β.symm x : StatedSp (1 + 3) K) ∈ wCenter K 1 := by
  rw [mem_wCenter_iff] at hx ⊢
  obtain ⟨hxQ, hxc⟩ := hx
  refine ⟨(hβ (β.symm x)).1 (by rw [MulEquiv.apply_symm_apply]; exact hxQ), fun y hy => ?_⟩
  set yy : (wRadical K (1 : Fin (1 + 3)) 2 ⊔ M : Subgroup (StatedSp (1 + 3) K)) :=
    ⟨y, mem_sup_left hy⟩ with hyy
  have hβy : (β yy : StatedSp (1 + 3) K) ∈ wRadical K (1 : Fin (1 + 3)) 2 := (hβ yy).2 hy
  have h1 : x * β yy = β yy * x := Subtype.ext (hxc _ hβy)
  have h2 : β (β.symm x * yy) = β (yy * β.symm x) := by
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply, h1]
  have h3 := congrArg Subtype.val (β.injective h2)
  simpa [hyy] using h3

theorem planes12_one_one : planes12 1 1 = 3 := by decide

theorem nonempty_perfectCore_centralizer_of_compat_eight (hK : Nat.card K = 2)
    {M : Subgroup (StatedSp (1 + 3) K)} (hMS : M ≤ spCompl12 K 1)
    (hXM : nsTorusSp K (0 : Fin (1 + 3)) ≤ M)
    (β : (wRadical K (1 : Fin (1 + 3)) 2 ⊔ M : Subgroup (StatedSp (1 + 3) K)) ≃*
      (wRadical K (1 : Fin (1 + 3)) 2 ⊔ M : Subgroup (StatedSp (1 + 3) K)))
    (hβ : ∀ y : (wRadical K (1 : Fin (1 + 3)) 2 ⊔ M : Subgroup (StatedSp (1 + 3) K)),
      ((β y : StatedSp (1 + 3) K) ∈ wRadical K (1 : Fin (1 + 3)) 2 ↔
        (y : StatedSp (1 + 3) K) ∈ wRadical K (1 : Fin (1 + 3)) 2))
    (ι : M ≃* M)
    (hι : ∀ m : M, ((ι m : StatedSp (1 + 3) K))⁻¹ * (β (inclusion le_sup_right m) :
      StatedSp (1 + 3) K) ∈ wRadical K (1 : Fin (1 + 3)) 2) :
    Nonempty (perfectCore (centralizer
      ((((nsTorusSp K (0 : Fin (1 + 3))).subgroupOf M).map ι.toMonoidHom).map M.subtype :
          Set (StatedSp (1 + 3) K))) ≃* complSp K (0 : Fin (1 + 3))) := by
  classical
  have : Finite (StatedSp (1 + 3) K) := by
    have : Finite (GL (Fin (1 + 3) ⊕ Fin (1 + 3)) K) := inferInstance
    exact Subtype.finite
  have hx0M : nsElt (K := K) (0 : Fin (1 + 3)) ∈ M := hXM (nsElt_mem_nsTorusSp 0)
  set m₀ : M := ⟨nsElt 0, hx0M⟩ with hm₀
  set y : StatedSp (1 + 3) K := (ι m₀ : StatedSp (1 + 3) K) with hydef
  have hX : (((nsTorusSp K (0 : Fin (1 + 3))).subgroupOf M).map ι.toMonoidHom).map M.subtype =
      zpowers y := by
    have h1 : (nsTorusSp K (0 : Fin (1 + 3))).subgroupOf M = zpowers m₀ := by
      ext x
      rw [mem_subgroupOf, nsTorusSp, mem_zpowers_iff, mem_zpowers_iff]
      constructor
      · rintro ⟨k, hk⟩
        exact ⟨k, Subtype.ext (by rw [SubgroupClass.coe_zpow]; exact hk)⟩
      · rintro ⟨k, rfl⟩
        exact ⟨k, by rw [SubgroupClass.coe_zpow]⟩
    rw [h1, MonoidHom.map_zpowers, MonoidHom.map_zpowers]
    rfl
  rw [hX]
  have hyS : y ∈ spCompl12 K 1 := hMS (ι m₀).2
  have hy3 : orderOf y = 3 := by
    rw [hydef, Subgroup.orderOf_coe, MulEquiv.orderOf_eq, Subgroup.orderOf_mk, orderOf_nsElt]
  obtain ⟨g, hg⟩ : ∃ g : StatedSp 2 K, (spCompl12Equiv K 1 g : StatedSp (1 + 3) K) = y :=
    ⟨(spCompl12Equiv K 1).symm ⟨y, hyS⟩, by simp⟩
  have hg3 : orderOf g = 3 := by
    rw [← hy3, ← hg, Subgroup.orderOf_coe, MulEquiv.orderOf_eq]
  set E' : StatedSp 2 K →* StatedSp (1 + 3) K :=
    (spCompl12 K 1).subtype.comp (spCompl12Equiv K 1).toMonoidHom with hE'
  have hE'g : E' g = y := hg
  have hE'ns : E' (nsElt (K := K) (1 : Fin 2)) = nsElt (K := K) (3 : Fin (1 + 3)) := by
    change spEmbed (planes12 1) (planes12_injective 1) (longBlock K 2 1 zThreeSL) = _
    rw [spEmbed_longBlock, planes12_one_one]
    rfl
  obtain ⟨h, hL | hSh⟩ := exists_conj_eq_yLong_or_yShort hK hg3
  ·
    have hyL3 : orderOf (sp4YLong (K := K)) = 3 := by
      rw [← hg3, ← hL, ← MulAut.conj_apply, MulEquiv.orderOf_eq]
    have hyLJ : sp4YLong (K := K) ∈ longRootSp2 K 2 1 :=
      mul_mem (elt_positiveLong_mem_longRootSp2 1 1) (elt_negativeLong_mem_longRootSp2 1 1)
    obtain ⟨k, hk⟩ := mem_zpowers_iff.1 (mem_nsTorusSp_of_mem_longRootSp2 hK hyLJ hyL3)
    set c : StatedSp (1 + 3) K := E' h with hc
    have hyc : y = c * nsElt (K := K) (3 : Fin (1 + 3)) ^ k * c⁻¹ := by
      rw [← hE'g, ← hL, ← hk, map_mul, map_mul, map_inv, map_zpow, hE'ns]
    have hle : zpowers y ≤ (nsTorusSp K (3 : Fin (1 + 3))).map (MulAut.conj c).toMonoidHom := by
      rw [zpowers_le, hyc]
      exact ⟨_, ⟨k, rfl⟩, by simp [MulAut.conj_apply]⟩
    have heq : zpowers y = (nsTorusSp K (3 : Fin (1 + 3))).map (MulAut.conj c).toMonoidHom := by
      refine Subgroup.eq_of_le_of_card_ge hle ?_
      rw [Subgroup.card_map_of_injective (MulAut.conj c).injective, card_nsTorusSp,
        Nat.card_zpowers, hy3]
    rw [heq]
    obtain ⟨e1⟩ := F4Pilot.nonempty_perfectCore_centralizer_map_mulAut (MulAut.conj c)
      (nsTorusSp K (3 : Fin (1 + 3)))
    rw [perfectCore_centralizer_nsTorusSp hK (m := 3) le_rfl (3 : Fin (3 + 1))] at e1
    exact ⟨e1.trans ((complSpEquiv (K := K) (m := 3) (3 : Fin (3 + 1))).symm.trans
      (complSpEquiv (K := K) (m := 3) (0 : Fin (3 + 1))))⟩
  ·
    exfalso
    have hq₀Q : siegPair K (1 : Fin (1 + 3)) 3 1 ∈ wRadical K (1 : Fin (1 + 3)) 2 :=
      siegPair_one_three_mem_wRadical
    obtain ⟨qq, hqq⟩ : ∃ qq : (wRadical K (1 : Fin (1 + 3)) 2 ⊔ M :
        Subgroup (StatedSp (1 + 3) K)),
        (qq : StatedSp (1 + 3) K) = siegPair K (1 : Fin (1 + 3)) 3 1 :=
      ⟨⟨_, mem_sup_left hq₀Q⟩, rfl⟩
    obtain ⟨X, hX⟩ : ∃ X : StatedSp (1 + 3) K, X = (β qq : StatedSp (1 + 3) K) := ⟨_, rfl⟩
    have hXQ : X ∈ wRadical K (1 : Fin (1 + 3)) 2 := by
      rw [hX]
      exact (hβ qq).2 (by rw [hqq]; exact hq₀Q)
    obtain ⟨B, hB⟩ : ∃ B : StatedSp (1 + 3) K,
        B = (β (inclusion le_sup_right m₀) : StatedSp (1 + 3) K) := ⟨_, rfl⟩
    have hβc : B * X = X * B := by
      have hcomm : inclusion le_sup_right m₀ * qq = qq * inclusion le_sup_right m₀ := by
        apply Subtype.ext
        rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inclusion, hqq]
        exact commute_siegPair_one_three (nsTorusSp_le_longRootSp2 0 (nsElt_mem_nsTorusSp 0))
      have h' : β (inclusion le_sup_right m₀ * qq) = β (qq * inclusion le_sup_right m₀) := by
        rw [hcomm]
      rw [map_mul, map_mul] at h'
      have h'' := congrArg Subtype.val h'
      rw [hB, hX]
      exact h''
    have hdQ : y⁻¹ * B ∈ wRadical K (1 : Fin (1 + 3)) 2 := by
      rw [hB, hydef]
      exact hι m₀
    have hrel : y * ((y⁻¹ * B) * X * (y⁻¹ * B)⁻¹) = X * y := by
      calc y * ((y⁻¹ * B) * X * (y⁻¹ * B)⁻¹) = (B * X) * B⁻¹ * y := by group
        _ = X * y := by rw [hβc]; group
    have key : ∀ i : Fin (1 + 3), (i = 1 ∨ i = 2) →
        wRowT 1 i X = Matrix.vecMul (wRowT 1 i X) (mat 2 K g) := by
      intro i hi
      have h1 := wRowT_mul_left hyS ((y⁻¹ * B) * X * (y⁻¹ * B)⁻¹) hi
      have h2 := wRowT_conj hdQ hXQ hi
      have h3 : wRowT 1 i (X * y) = Matrix.vecMul (wRowT 1 i X) (mat 2 K g) := by
        rw [← hg, coe_spCompl12Equiv_apply]
        exact wRowT_mul_spEmbed X g i
      calc wRowT 1 i X = wRowT 1 i ((y⁻¹ * B) * X * (y⁻¹ * B)⁻¹) := h2.symm
        _ = wRowT 1 i (y * ((y⁻¹ * B) * X * (y⁻¹ * B)⁻¹)) := h1.symm
        _ = wRowT 1 i (X * y) := by rw [hrel]
        _ = Matrix.vecMul (wRowT 1 i X) (mat 2 K g) := h3
    have hfix : ∀ i : Fin (1 + 3), (i = 1 ∨ i = 2) → wRowT 1 i X = 0 := by
      intro i hi
      have hk := key i hi
      rw [← hSh] at hk
      have hw0 := eq_zero_of_vecMul_yShort (vecMul_mat_conj hk)
      have hs2 : mat 2 K h * mat 2 K h⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
      calc wRowT 1 i X = Matrix.vecMul (wRowT 1 i X) (mat 2 K h * mat 2 K h⁻¹) := by
            rw [hs2, Matrix.vecMul_one]
        _ = Matrix.vecMul (Matrix.vecMul (wRowT 1 i X) (mat 2 K h)) (mat 2 K h⁻¹) := by
            rw [Matrix.vecMul_vecMul]
        _ = 0 := by rw [hw0, Matrix.zero_vecMul]
    have hXY : X ∈ wCenter K 1 :=
      mem_wCenter_of_wRowT_eq_zero hXQ (hfix 1 (Or.inl rfl)) (hfix 2 (Or.inr rfl))
    rw [hX] at hXY
    have hq₀Y := coe_symm_mem_wCenter_of_compat β hβ (β qq) hXY
    rw [MulEquiv.symm_apply_apply, hqq] at hq₀Y
    exact siegPair_one_three_not_mem_wCenter hq₀Y

end F5

section Eight

variable [Finite K] [CharP K 2]

theorem spTwoLemmaBFacts_one (hK : Nat.card K = 2) : SpTwoLemmaBFacts K 1 := by
  have h10 : (1 : Fin (1 + 3)) ≠ 0 := one_ne_zero_fin3
  have hJ1 : longRootSp2 K (1 + 3) 0 ≤ complSp K (1 : Fin (1 + 3)) := longRootSp2_le_complSp h10
  have hA1 : IsAutConjIn (complSp K (1 : Fin (1 + 3))) (longRootSp2 K (1 + 3) 0) :=
    isAutConjIn_complSp_longRootSp2 le_rfl
  have hXM : nsTorusSp K (0 : Fin (1 + 3)) ≤ ⁅spCompl12 K 1, spCompl12 K 1⁆ :=
    nsTorusSp_le_commutator_spCompl12
  have hMS : ⁅spCompl12 K 1, spCompl12 K 1⁆ ≤ spCompl12 K 1 := Subgroup.commutator_le_self _
  have hO2 : ∀ N : Subgroup (⁅spCompl12 K 1, spCompl12 K 1⁆ : Subgroup (StatedSp (1 + 3) K)),
      N.Normal → IsPGroup 2 N → N = ⊥ := by
    intro N hN h2
    have : IsSimpleGroup (⁅spCompl12 K 1, spCompl12 K 1⁆ : Subgroup (StatedSp (1 + 3) K)) :=
      isSimpleGroup_commutator_spCompl12_one hK
    have hy : orderOf (⟨nsElt 0, hXM (nsElt_mem_nsTorusSp 0)⟩ :
        (⁅spCompl12 K 1, spCompl12 K 1⁆ : Subgroup (StatedSp (1 + 3) K))) = 3 := by
      rw [Subgroup.orderOf_mk, orderOf_nsElt]
    exact eq_bot_of_normal_of_isPGroup_of_orderOf_three hy N hN h2
  refine ⟨fun κ => ?_, fun κ => ?_, fun κ => ?_, fun κ κ' β hβ ι hι => ?_⟩
  · cases κ
    · exact perfectCore_centralizer_spRep_b1_two hK le_rfl
    · rw [spRep_a2_eq]
      exact perfectCore_centralizer_twoCentralElt_one_two hK (Or.inl rfl)
    · rw [spRep_c2_eq]
      exact perfectCore_centralizer_twoCentralElt_one_two hK (Or.inr rfl)
  · cases κ
    · exact forall_normal_isPGroup_complSp_one_two hK le_rfl
    · exact hO2
    · exact hO2
  · cases κ
    · exact (nsTorusSp_le_longRootSp2 0).trans hJ1
    · exact hXM
    · exact hXM
  · cases κ <;> cases κ'
    · exact nonempty_perfectCore_centralizer_of_isAutConjIn hK le_rfl hA1 hJ1 ι
    · exact ((isEmpty_mulEquiv_complSp_spCoreLeviTwo (K := K) (n := 1) (κ := .a2)
        SpTwoCentral.noConfusion).false ι).elim
    · exact ((isEmpty_mulEquiv_complSp_spCoreLeviTwo (K := K) (n := 1) (κ := .c2)
        SpTwoCentral.noConfusion).false ι).elim
    · exact ((isEmpty_mulEquiv_spCoreLeviTwo_complSp (K := K) (n := 1) (κ := .a2)
        SpTwoCentral.noConfusion).false ι).elim
    · exact nonempty_perfectCore_centralizer_of_compat_eight (M := ⁅spCompl12 K 1, spCompl12 K 1⁆)
        hK hMS hXM β hβ ι hι
    · exact nonempty_perfectCore_centralizer_of_compat_eight (M := ⁅spCompl12 K 1, spCompl12 K 1⁆)
        hK hMS hXM β hβ ι hι
    · exact ((isEmpty_mulEquiv_spCoreLeviTwo_complSp (K := K) (n := 1) (κ := .c2)
        SpTwoCentral.noConfusion).false ι).elim
    · exact nonempty_perfectCore_centralizer_of_compat_eight (M := ⁅spCompl12 K 1, spCompl12 K 1⁆)
        hK hMS hXM β hβ ι hι
    · exact nonempty_perfectCore_centralizer_of_compat_eight (M := ⁅spCompl12 K 1, spCompl12 K 1⁆)
        hK hMS hXM β hβ ι hι

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

end Eight

theorem spEightTwoLemmaBFacts : SpEightTwoLemmaBFacts := fun _ _ _ _ hK => spTwoLemmaBFacts_one hK

theorem spTwoPositionInput_holds : SpTwoPositionInput :=
  spTwoPositionInput_of_eight spEightTwoLemmaBFacts

theorem spTwoInput_of_catalogue_rows (hcat : ∀ m : ℕ, 3 ≤ m → Sp2mCatalogueClausesAt m)
    (hrows : ∀ κ : Sp2mKind, SpTwoRowInput κ) : SpTwoInput :=
  spTwoInput_of_rows hcat spTwoPositionInput_holds hrows

end CFSG.SeitzReduction.SymplecticPilot
