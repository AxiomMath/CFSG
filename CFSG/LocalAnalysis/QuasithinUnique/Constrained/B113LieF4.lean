module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.B113LieEngine
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsLieF4

public section

namespace CFSG.QuasithinUnique.B113Lie.LargeRee

open CFSG.LieType.Chevalley CFSG.LieType.Ree CFSG.LieType.Ree.ReeTag CFSG.Blueprint
  CFSG.Blueprint.Chevalley CFSG.Assembly.LowTwoRank
open CFSG.QuasithinUnique.Setup.X6

variable {a : ℕ} {K : Type} [Field K] [Finite K] [CharP K F4.prime]

theorem overgroup_le_parabolic
    (hK : Nat.card K = 2 ^ (2 * a + 1))
    {M : Subgroup (ModGL F4.tag K)} (hUM : F4.reeFixedPosUnipotent K a ≤ M)
    (hMΓ : M ≤ F4.reeGamma K a) (hMne : M ≠ F4.reeGamma K a) :
    M ≤ F4.reeLocalParabolic K a ⟨0, by decide⟩ ∨ M ≤ F4.reeLocalParabolic K a ⟨1, by decide⟩ := by
  obtain ⟨J, hJ, hMJ, -⟩ :=
    (large_Ree_positive_root_overgroup_parabolic_containment hK hMΓ hUM).2.2 hMne
  obtain ⟨j, hj⟩ : ∃ j, j ∉ J := by
    by_contra h
    exact hJ (Set.eq_univ_of_forall fun j => not_not.1 fun hj => h ⟨j, hj⟩)
  have hcases : ∀ j : Fin F4.fixedOrbitCount, j = ⟨0, by decide⟩ ∨ j = ⟨1, by decide⟩ := by
    decide
  rcases hcases j with rfl | rfl
  · right
    refine hMJ.trans (reeParabolic_le_reeGamma_inf (J := J) (i := ⟨1, by decide⟩) ?_)
    intro k hk
    rcases hcases k with rfl | rfl
    · exact absurd hk hj
    · exact Set.mem_singleton _
  · left
    refine hMJ.trans (reeParabolic_le_reeGamma_inf (J := J) (i := ⟨0, by decide⟩) ?_)
    intro k hk
    rcases hcases k with rfl | rfl
    · exact Set.mem_singleton _
    · exact absurd hk hj

theorem parabolicData
    (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    ParabolicData ↥(F4.reeGamma K a)
      ((F4.reeFixedPosUnipotent K a).subgroupOf (F4.reeGamma K a))
      {(F4.reeLocalParabolic K a ⟨0, by decide⟩).subgroupOf (F4.reeGamma K a),
        (F4.reeLocalParabolic K a ⟨1, by decide⟩).subgroupOf (F4.reeGamma K a)} := by
  classical
  have : Finite (ModGL F4.tag K) := finite_modGL
  obtain ⟨hU, hcov, hn₀, hn₁, hgen, hi₀, hi₁⟩ :=
    CFSG.QuasithinUnique.Vol2Native.L239.Lie.F4.largeRee_named_covers a K hK
  obtain ⟨hF₀, hF₁⟩ :=
    CFSG.QuasithinUnique.Vol2Native.L239.Lie.F4.largeReeParabolicFacts a K ha hK
  have hq : 2 ≤ Nat.card K := by
    rw [hK]
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (2 * a + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hne : Nat.card K + 1 ≠ Nat.card K ^ 2 + 1 := by
    intro h
    have h1 : Nat.card K = Nat.card K ^ 2 := Nat.add_right_cancel h
    nlinarith
  have hinv := CFSG.QuasithinUnique.Vol2Native.L239.Lie.D4.invariant_of_unequal_covers hcov
    (by rw [hi₀, hi₁]; exact hne)
  set Γ := F4.reeGamma K a with hΓ
  have hP₀Γ : F4.reeLocalParabolic K a ⟨0, by decide⟩ ≤ Γ := inf_le_left
  have hP₁Γ : F4.reeLocalParabolic K a ⟨1, by decide⟩ ≤ Γ := inf_le_left
  have hQ₀Γ : F4.reeFixedOrbitComplementUnipotent K a ⟨0, by decide⟩ ≤ Γ := inf_le_right
  have hQ₁Γ : F4.reeFixedOrbitComplementUnipotent K a ⟨1, by decide⟩ ≤ Γ := inf_le_right
  have hUΓ : F4.reeFixedPosUnipotent K a ≤ Γ := reeFixedPosUnipotent_le_reeGamma
  have hUP : ∀ P : Subgroup ↥Γ,
      (P = (F4.reeLocalParabolic K a ⟨0, by decide⟩).subgroupOf Γ ∨
        P = (F4.reeLocalParabolic K a ⟨1, by decide⟩).subgroupOf Γ) →
      (F4.reeFixedPosUnipotent K a).subgroupOf Γ ≤ P := by
    intro P hP
    exact (Subgroup.le_normalizer).trans ((hcov P).2 hP).le
  refine ParabolicData.of_pair hU (hUP _ (Or.inl rfl)) (hUP _ (Or.inr rfl)) hn₀ hn₁ hgen
    (cover_subgroupOf hUΓ fun A hUA hAΓ hAne => overgroup_le_parabolic hK hUA hAΓ hAne) ?_ ?_
    hinv
  · refine (CFSG.QuasithinUnique.Vol2Native.L239.Lie.ParabolicFacts.of_map
      (Q := (F4.reeFixedOrbitComplementUnipotent K a ⟨0, by decide⟩).subgroupOf Γ)
      Γ.subtype Γ.subtype_injective ?_).charTwo
    rw [Subgroup.map_subgroupOf_eq_of_le hP₀Γ, Subgroup.map_subgroupOf_eq_of_le hQ₀Γ]
    exact hF₀
  · refine (CFSG.QuasithinUnique.Vol2Native.L239.Lie.ParabolicFacts.of_map
      (Q := (F4.reeFixedOrbitComplementUnipotent K a ⟨1, by decide⟩).subgroupOf Γ)
      Γ.subtype Γ.subtype_injective ?_).charTwo
    rw [Subgroup.map_subgroupOf_eq_of_le hP₁Γ, Subgroup.map_subgroupOf_eq_of_le hQ₁Γ]
    exact hF₁

end CFSG.QuasithinUnique.B113Lie.LargeRee

namespace CFSG.QuasithinUnique.B113Lie

open CFSG.Blueprint CFSG.LieType.Ree CFSG.LieType.Ree.ReeTag

theorem f4_sylowFacts
    {S : Type} [Group S] [Finite S] {f : ℕ} (_hodd : Odd f) (_hf : 3 ≤ f)
    (h : ReeTitsModel S .twistedF4 2 f) {T : Subgroup S} (hT : IsSylowTwoOf T ⊤) :
    SylowFacts S T := by
  obtain ⟨a, K, hKF, hKFin, hcp, ha, hfa, hK, ⟨e⟩⟩ :=
    CFSG.QuasithinUnique.Setup.X6.exists_mulEquiv_largeRee_model h
  have hK' : Nat.card K = 2 ^ (2 * a + 1) := by rw [hK, hfa]
  have : Finite (CFSG.Blueprint.Chevalley.ModGL F4.tag K) :=
    CFSG.LieType.Chevalley.finite_modGL
  exact SylowFacts.of_mulEquiv_isSylow e (LargeRee.parabolicData ha hK').sylowFacts hT

end CFSG.QuasithinUnique.B113Lie
