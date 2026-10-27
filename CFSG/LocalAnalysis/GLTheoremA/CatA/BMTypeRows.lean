module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.BMTypeM
public import CFSG.LocalAnalysis.GLTheoremA.CatA.K14SporRows2
public import CFSG.HardMathSupport.Dickson.BMRows.RowsB
public import CFSG.Sporadic.Bridge.MonsterModelsGriess

public section

namespace CFSG.LocalAnalysis.GLTheoremA.BMType

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.Blueprint.NativeSporadic (Carrier)

@[expose] def TypeRow (P : TauCeti.CFSGIndex → Prop) (s : TauCeti.SporadicName) : Prop :=
  ∀ (S : Type) [Group S] [Finite S], Nonempty (S ≃* (TauCeti.CFSGIndex.sporadic s).Group) →
    ∀ β : MulAut S, β ^ 3 = 1 → β ≠ 1 → ∀ J : Subgroup S,
      GLAPComponent 3 (CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup β) J →
      catalogIs (PSimple 3 J) P → False

theorem typeRow_of_model {P : TauCeti.CFSGIndex → Prop} {s : TauCeti.SporadicName} {Q : Type}
    [Group Q] [Finite Q] [IsSimpleGroup Q]
    (hOut : CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicOuterLeTwo)
    (b : Q ≃* (TauCeti.CFSGIndex.sporadic s).Group) (hnc : ∃ a c : Q, a * c ≠ c * a)
    (h : ∀ k : Q, orderOf k = 3 → ∀ J : Subgroup Q,
      GLAPComponent 3 (Subgroup.centralizer ({k} : Set Q)) J → catalogIs (PSimple 3 J) P → False) :
    TypeRow P s := by
  intro S _ _ ⟨e⟩ β hβ hβ1 J hJ hT
  let φ : S ≃* Q := e.trans b.symm
  haveI : IsSimpleGroup S := (MulEquiv.isSimpleGroup_congr φ).2 inferInstance
  have hncS : ∃ a c : S, a * c ≠ c * a := by
    obtain ⟨a, c, hac⟩ := hnc
    refine ⟨φ.symm a, φ.symm c, fun h' => hac ?_⟩
    have := congrArg φ h'
    simpa using this
  have hcen : Subgroup.center S = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center S) with h' | h'
    · exact h'
    · obtain ⟨a, c, hac⟩ := hncS
      exact absurd ((Subgroup.mem_center_iff.1 (h' ▸ Subgroup.mem_top c)) a) hac
  have hout := hOut S inferInstance hncS s ⟨e⟩
  obtain ⟨x, rfl, hxp⟩ :=
    CFSG.HardMathSupport.Solomon.Coordinator.exists_conj_of_pow Nat.prime_three (by norm_num)
      hcen hout β hβ
  have hx1 : x ≠ 1 := by
    rintro rfl
    exact hβ1 (map_one MulAut.conj)
  have hxo : orderOf x = 3 := orderOf_eq_prime hxp hx1
  rw [KDSpor.fixSubgroup_conj_eq] at hJ
  have hk : orderOf (φ x) = 3 := by rw [MulEquiv.orderOf_eq, hxo]
  obtain ⟨hJ', hT'⟩ := glaPComponent_map_type φ hJ hT
  exact h _ hk _ hJ' hT'

theorem typeHyp_u5two
    : TypeHyp S9.isU5two 13685760 where
  card _ _ _ h := K14Spor.card_u5two h
  out _ _ h := CFSG.LocalAnalysis.GLTheoremA.CatB.not_three_dvd_outer_u5two h
  big := by norm_num
  thirteen := by norm_num
  pow_six := by norm_num
  nine := by norm_num

theorem typeHyp_sp6two
    : TypeHyp S9.isSp6two 1451520 where
  card _ _ _ h := K14Spor.card_sp6two h
  out _ _ h := CFSG.LocalAnalysis.GLTheoremA.CatB.not_three_dvd_outer_sp6two h
  big := by norm_num
  thirteen := by norm_num
  pow_six := by norm_num
  nine := by norm_num

theorem typeRow_B
    {P : TauCeti.CFSGIndex → Prop} {n : ℕ} (hP : TypeHyp P n) : TypeRow P .B := by
  obtain ⟨hfin, hs, ⟨b⟩, hnc⟩ := CFSG.HardMathSupport.Dickson.BMRows.model_B
  exact @typeRow_of_model P .B (Carrier .B) _ hfin hs
    CFSG.HardMathSupport.Timmesfeld.Proving.sporadicOuterLeTwo_holds b hnc
    fun k hk J hJ hT => false_of_type_B hP (s := k) hk hJ hT

theorem typeRow_M
    {P : TauCeti.CFSGIndex → Prop} {n : ℕ} (hP : TypeHyp P n) : TypeRow P .M := by
  obtain ⟨-, hs, hfin⟩ := CFSG.Monster.Generated.generated_rational_group_finite_simple
  obtain ⟨b⟩ := CFSG.Blueprint.NativeSporadic.MonsterModel.iso_gmat_tauCeti
  have hnc : ∃ a c : CFSG.Monster.Generated.Gmat, a * c ≠ c * a :=
    CFSG.LocalAnalysis.GLTheoremA.S8.HNRows.exists_noncomm_of_simple (by
      rw [CFSG.YGroups.Y443.natCard_Gmat_eq_monsterOrder, CFSG.Open.monsterOrder]
      norm_num)
  exact @typeRow_of_model P .M CFSG.Monster.Generated.Gmat _ hfin hs
    CFSG.HardMathSupport.Timmesfeld.Proving.sporadicOuterLeTwo_holds b hnc
    fun k hk J hJ hT => false_of_type_gmat hP (s := k) hk hJ hT

theorem k14Row_B
    : K14Spor.K14Row .B := by
  intro S _ _ e β hβ hβ1 J hJ hT
  rcases hT with hT | hT
  · exact typeRow_B typeHyp_u5two S e β hβ hβ1 J hJ hT
  · exact typeRow_B typeHyp_sp6two S e β hβ hβ1 J hJ hT

theorem k14Row_M
    : K14Spor.K14Row .M := by
  intro S _ _ e β hβ hβ1 J hJ hT
  rcases hT with hT | hT
  · exact typeRow_M typeHyp_u5two S e β hβ hβ1 J hJ hT
  · exact typeRow_M typeHyp_sp6two S e β hβ hβ1 J hJ hT

theorem k14SporU_holds
    : K14SporU :=
  K14Spor.k14SporU_of_BM k14Row_B k14Row_M

end CFSG.LocalAnalysis.GLTheoremA.BMType

end
