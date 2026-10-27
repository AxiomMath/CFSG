module

public import CFSG.LieType.SeitzGeneration.ExcHigh.TwE6SU6Members
public import CFSG.LieType.SeitzGeneration.ExcHigh.TwE6TwoFrame
public import CFSG.RankThree.Lattice.SteinbergBIListMatrix

public noncomputable section

namespace CFSG.LieType.SeitzGeneration.ExcHigh.TwSU6

open CFSG.LieType.Chevalley.E6GraphLevi CFSG.Timmesfeld Matrix CFSG.LieType.Chevalley
  CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.SeitzGeneration.ExcHigh
open scoped MatrixGroups


variable {K : Type} [Field K] [Finite K]

structure IsPsiTw (σ : K →+* K) (ε : K) (Ψ : SL(6, K) →* ModGL TwistTag.E6.tag K) : Prop where
  scalar_of_eq_one : ∀ B, Ψ B = 1 →
    ∃ r : K, r ^ 6 = 1 ∧ (B : Matrix (Fin 6) (Fin 6) K) = Matrix.scalar (Fin 6) r
  range_le : Ψ.range ≤ Subgroup.closure (a5Gens K)
  twist : ∀ B, twistHom TwistTag.E6 K σ (Ψ B) = Ψ (unitaryTwist σ B)
  upper : ∀ (t : Fin 5) (c : K),
    Ψ (tv t.castSucc t.succ c) = xUnit TwistTag.E6.tag K (a5Node t) (eTw ε t * c)
  lower : ∀ (t : Fin 5) (c : K),
    Ψ (tv t.succ t.castSucc c) = yUnit TwistTag.E6.tag K (a5Node t) ((eTw ε t)⁻¹ * c)

theorem exists_isPsiTw (σ : K →+* K) (hσσ : ∀ c, σ (σ c) = c) {ε : K} (hε0 : ε ≠ 0)
    (hε : σ ε = -ε) {p f : ℕ} (hp : p.Prime) (hf : 1 ≤ f) (hK : Nat.card K = p ^ f) :
    ∃ Ψ : SL(6, K) →* ModGL TwistTag.E6.tag K, IsPsiTw σ ε Ψ := by
  obtain ⟨Ψ, h1, h2, h3, h4⟩ := exists_psiTw σ hσσ hε0 hε hp hf hK
  exact ⟨Ψ, ⟨h1, h2, h3, fun t c => (h4 t c).1, fun t c => (h4 t c).2⟩⟩

variable {σ : K →+* K} {ε : K} {Ψ : SL(6, K) →* ModGL TwistTag.E6.tag K}

omit
  [Finite K] in
theorem map_unitarySL_le_graphFixedRootGroup (hΨ : IsPsiTw σ ε Ψ) (hsurj : Function.Surjective σ)
    (hperf : Group.IsPerfect (unitarySL σ)) :
    (unitarySL σ).map Ψ ≤ graphFixedRootGroup TwistTag.E6 K σ := by
  have hadj : Subgroup.closure (a5Gens K) ≤ adjointGroup TwistTag.E6.tag K := by
    rw [Subgroup.closure_le]
    intro g hg
    simp only [a5Gens, Set.mem_iUnion, Set.mem_union, Set.mem_range] at hg
    obtain ⟨k, ⟨c, rfl⟩ | ⟨c, rfl⟩⟩ := hg
    · exact xUnit_mem_adjointGroup _ c
    · exact yUnit_mem_adjointGroup _ c
  have hΓ : (unitarySL σ).map Ψ ≤ twistedFixedGroup TwistTag.E6 K σ := by
    rintro _ ⟨B, hB, rfl⟩
    refine (mem_twistedFixedGroup_iff_twistHom TwistTag.E6 K σ).2
      ⟨hadj (hΨ.range_le ⟨B, rfl⟩), ?_⟩
    rw [hΨ.twist, mem_unitarySL_iff_unitaryTwist.1 hB]
  calc (unitarySL σ).map Ψ = (⁅unitarySL σ, unitarySL σ⁆).map Ψ := by
        rw [Subgroup.commutator_eq_self]
    _ = ⁅(unitarySL σ).map Ψ, (unitarySL σ).map Ψ⁆ := Subgroup.map_commutator _ _ _
    _ ≤ ⁅twistedFixedGroup TwistTag.E6 K σ, twistedFixedGroup TwistTag.E6 K σ⁆ :=
        Subgroup.commutator_mono hΓ hΓ
    _ ≤ graphFixedRootGroup TwistTag.E6 K σ := commutator_twistedFixedGroup_le hsurj

omit
  [Finite K] in
theorem coe_orbitX_two (a : Fin TwistTag.E6.foldedTag.rank)
    (ha : (TwistTag.E6.orbit a).card = 2) (c : orbitField TwistTag.E6 K σ a) :
    (orbitX TwistTag.E6 K σ a c : ModGL TwistTag.E6.tag K) =
      xUnit TwistTag.E6.tag K (TwistTag.E6.orbitMin a) (c : K) *
        xUnit TwistTag.E6.tag K (TwistTag.E6.perm (TwistTag.E6.orbitMin a)) (σ (c : K)) := by
  rw [coe_orbitX, ha]
  simp [List.range_succ]

omit
  [Finite K] in
theorem coe_orbitY_two (a : Fin TwistTag.E6.foldedTag.rank)
    (ha : (TwistTag.E6.orbit a).card = 2) (c : orbitField TwistTag.E6 K σ a) :
    (orbitY TwistTag.E6 K σ a c : ModGL TwistTag.E6.tag K) =
      yUnit TwistTag.E6.tag K (TwistTag.E6.orbitMin a) (c : K) *
        yUnit TwistTag.E6.tag K (TwistTag.E6.perm (TwistTag.E6.orbitMin a)) (σ (c : K)) := by
  rw [coe_orbitY, ha]
  simp [List.range_succ]

omit
  [Finite K] in
theorem coe_orbitX_one (a : Fin TwistTag.E6.foldedTag.rank)
    (ha : (TwistTag.E6.orbit a).card = 1) (c : orbitField TwistTag.E6 K σ a) :
    (orbitX TwistTag.E6 K σ a c : ModGL TwistTag.E6.tag K) =
      xUnit TwistTag.E6.tag K (TwistTag.E6.orbitMin a) (c : K) := by
  rw [coe_orbitX, ha]
  simp

omit
  [Finite K] in
theorem coe_orbitY_one (a : Fin TwistTag.E6.foldedTag.rank)
    (ha : (TwistTag.E6.orbit a).card = 1) (c : orbitField TwistTag.E6 K σ a) :
    (orbitY TwistTag.E6 K σ a c : ModGL TwistTag.E6.tag K) =
      yUnit TwistTag.E6.tag K (TwistTag.E6.orbitMin a) (c : K) := by
  rw [coe_orbitY, ha]
  simp

section Orbits

variable (hΨ : IsPsiTw σ ε Ψ) (hσσ : ∀ c, σ (σ c) = c)

include hΨ hσσ in
omit
  [Finite K] in
theorem xUnit_pair_mem_map (t : Fin 5) (ht : t ≠ Fin.rev t) (x : K) :
    xUnit TwistTag.E6.tag K (a5Node t) (eTw ε t * x) *
      xUnit TwistTag.E6.tag K (a5Node (Fin.rev t)) (eTw ε (Fin.rev t) * (-σ x)) ∈
        (unitarySL σ).map Ψ := by
  refine ⟨_, mem_unitarySL_upper_pair σ hσσ t ht x, ?_⟩
  rw [map_mul, hΨ.upper, hΨ.upper]

include hΨ hσσ in
omit
  [Finite K] in
theorem yUnit_pair_mem_map (t : Fin 5) (ht : t ≠ Fin.rev t) (x : K) :
    yUnit TwistTag.E6.tag K (a5Node t) ((eTw ε t)⁻¹ * x) *
      yUnit TwistTag.E6.tag K (a5Node (Fin.rev t)) ((eTw ε (Fin.rev t))⁻¹ * (-σ x)) ∈
        (unitarySL σ).map Ψ := by
  refine ⟨_, mem_unitarySL_lower_pair σ hσσ t ht x, ?_⟩
  rw [map_mul, hΨ.lower, hΨ.lower]

include hΨ in
omit
  [Finite K] in
theorem xUnit_mid_mem_map (hε0 : ε ≠ 0) (hε : σ ε = -ε) (c : K) (hc : σ c = c) :
    xUnit TwistTag.E6.tag K (a5Node 2) c ∈ (unitarySL σ).map Ψ := by
  have hx : σ (ε⁻¹ * c) = -(ε⁻¹ * c) := by
    rw [map_mul, map_inv₀, hε, hc, inv_neg, neg_mul]
  refine ⟨_, mem_unitarySL_upper_mid σ (ε⁻¹ * c) hx, ?_⟩
  rw [hΨ.upper]
  have h2 : eTw ε (2 : Fin 5) = ε := rfl
  rw [h2]
  congr 1
  field_simp

include hΨ in
omit
  [Finite K] in
theorem yUnit_mid_mem_map (hε0 : ε ≠ 0) (hε : σ ε = -ε) (c : K) (hc : σ c = c) :
    yUnit TwistTag.E6.tag K (a5Node 2) c ∈ (unitarySL σ).map Ψ := by
  have hx : σ (ε * c) = -(ε * c) := by
    rw [map_mul, hε, hc, neg_mul]
  refine ⟨_, mem_unitarySL_lower_mid σ (ε * c) hx, ?_⟩
  rw [hΨ.lower]
  have h2 : eTw ε (2 : Fin 5) = ε := rfl
  rw [h2]
  congr 1
  field_simp

end Orbits

section OrbitMembers

variable (hΨ : IsPsiTw σ ε Ψ) (hσσ : ∀ c, σ (σ c) = c)

theorem orbLeaf_min : TwistTag.E6.orbitMin orbLeaf = (⟨3, by decide⟩ : Fin TwistTag.E6.tag.rank) :=
  by decide

include hΨ hσσ in
omit
  [Finite K] in
theorem orbitX_orb0_mem (c : orbitField TwistTag.E6 K σ orb0) :
    (orbitX TwistTag.E6 K σ orb0 c : ModGL TwistTag.E6.tag K) ∈ (unitarySL σ).map Ψ := by
  rw [coe_orbitX_two _ orb0_card, orb0_perm, orb0_min]
  have h := xUnit_pair_mem_map hΨ hσσ 0 (by decide) (-(c : K))
  have e1 : a5Node (0 : Fin 5) = nd0 := rfl
  have e2 : a5Node (Fin.rev (0 : Fin 5)) = nd5 := by decide
  have e3 : eTw ε (0 : Fin 5) * (-(c : K)) = c := by simp [eTw]
  have e4 : eTw ε (Fin.rev (0 : Fin 5)) * (-σ (-(c : K))) = σ c := by
    have : Fin.rev (0 : Fin 5) = 4 := by decide
    rw [this]
    simp [eTw, hσσ]
  rw [e1, e2, e3, e4] at h
  exact h

include hΨ hσσ in
omit
  [Finite K] in
theorem orbitX_orb1_mem (c : orbitField TwistTag.E6 K σ orb1) :
    (orbitX TwistTag.E6 K σ orb1 c : ModGL TwistTag.E6.tag K) ∈ (unitarySL σ).map Ψ := by
  rw [coe_orbitX_two _ orb1_card, orb1_perm, orb1_min]
  have h := xUnit_pair_mem_map hΨ hσσ 1 (by decide) (-(c : K))
  have e1 : a5Node (1 : Fin 5) = nd2 := rfl
  have e2 : a5Node (Fin.rev (1 : Fin 5)) = nd4 := by decide
  have e3 : eTw ε (1 : Fin 5) * (-(c : K)) = c := by simp [eTw]
  have e4 : eTw ε (Fin.rev (1 : Fin 5)) * (-σ (-(c : K))) = σ c := by
    have : Fin.rev (1 : Fin 5) = 3 := by decide
    rw [this]
    simp [eTw, hσσ]
  rw [e1, e2, e3, e4] at h
  exact h

include hΨ hσσ in
omit
  [Finite K] in
theorem orbitY_orb0_mem (c : orbitField TwistTag.E6 K σ orb0) :
    (orbitY TwistTag.E6 K σ orb0 c : ModGL TwistTag.E6.tag K) ∈ (unitarySL σ).map Ψ := by
  rw [coe_orbitY_two _ orb0_card, orb0_perm, orb0_min]
  have h := yUnit_pair_mem_map hΨ hσσ 0 (by decide) (-(c : K))
  have e1 : a5Node (0 : Fin 5) = nd0 := rfl
  have e2 : a5Node (Fin.rev (0 : Fin 5)) = nd5 := by decide
  have e3 : (eTw ε (0 : Fin 5))⁻¹ * (-(c : K)) = c := by simp [eTw]
  have e4 : (eTw ε (Fin.rev (0 : Fin 5)))⁻¹ * (-σ (-(c : K))) = σ c := by
    have : Fin.rev (0 : Fin 5) = 4 := by decide
    rw [this]
    simp [eTw, hσσ]
  rw [e1, e2, e3, e4] at h
  exact h

include hΨ hσσ in
omit
  [Finite K] in
theorem orbitY_orb1_mem (c : orbitField TwistTag.E6 K σ orb1) :
    (orbitY TwistTag.E6 K σ orb1 c : ModGL TwistTag.E6.tag K) ∈ (unitarySL σ).map Ψ := by
  rw [coe_orbitY_two _ orb1_card, orb1_perm, orb1_min]
  have h := yUnit_pair_mem_map hΨ hσσ 1 (by decide) (-(c : K))
  have e1 : a5Node (1 : Fin 5) = nd2 := rfl
  have e2 : a5Node (Fin.rev (1 : Fin 5)) = nd4 := by decide
  have e3 : (eTw ε (1 : Fin 5))⁻¹ * (-(c : K)) = c := by simp [eTw]
  have e4 : (eTw ε (Fin.rev (1 : Fin 5)))⁻¹ * (-σ (-(c : K))) = σ c := by
    have : Fin.rev (1 : Fin 5) = 3 := by decide
    rw [this]
    simp [eTw, hσσ]
  rw [e1, e2, e3, e4] at h
  exact h

include hΨ in
omit
  [Finite K] in
theorem orbitX_leaf_mem (hε0 : ε ≠ 0) (hε : σ ε = -ε) (c : orbitField TwistTag.E6 K σ orbLeaf) :
    (orbitX TwistTag.E6 K σ orbLeaf c : ModGL TwistTag.E6.tag K) ∈ (unitarySL σ).map Ψ := by
  have hc : σ (c : K) = c := by
    have := mem_orbitField.1 c.2
    rwa [orbLeaf_card, pow_one] at this
  rw [coe_orbitX_one _ orbLeaf_card, orbLeaf_min]
  exact xUnit_mid_mem_map hΨ hε0 hε c hc

include hΨ in
omit
  [Finite K] in
theorem orbitY_leaf_mem (hε0 : ε ≠ 0) (hε : σ ε = -ε) (c : orbitField TwistTag.E6 K σ orbLeaf) :
    (orbitY TwistTag.E6 K σ orbLeaf c : ModGL TwistTag.E6.tag K) ∈ (unitarySL σ).map Ψ := by
  have hc : σ (c : K) = c := by
    have := mem_orbitField.1 c.2
    rwa [orbLeaf_card, pow_one] at this
  rw [coe_orbitY_one _ orbLeaf_card, orbLeaf_min]
  exact yUnit_mid_mem_map hΨ hε0 hε c hc

include hΨ hσσ in
omit
  [Finite K] in
theorem orbitRankOneGroup_le_map (hε0 : ε ≠ 0) (hε : σ ε = -ε)
    (a : Fin TwistTag.E6.foldedTag.rank) (ha : a.val ≤ 2) :
    orbitRankOneGroup TwistTag.E6 K σ a ≤ (unitarySL σ).map Ψ := by
  have key : ∀ b : Fin TwistTag.E6.foldedTag.rank,
      (∀ c : orbitField TwistTag.E6 K σ b,
        (orbitX TwistTag.E6 K σ b c : ModGL TwistTag.E6.tag K) ∈ (unitarySL σ).map Ψ) →
      (∀ c : orbitField TwistTag.E6 K σ b,
        (orbitY TwistTag.E6 K σ b c : ModGL TwistTag.E6.tag K) ∈ (unitarySL σ).map Ψ) →
      orbitRankOneGroup TwistTag.E6 K σ b ≤ (unitarySL σ).map Ψ := fun b hx hy => by
    rw [orbitRankOneGroup, Subgroup.closure_le]
    rintro _ (⟨c, rfl⟩ | ⟨c, rfl⟩)
    · exact hx c
    · exact hy c
  fin_cases a
  · exact key _ (orbitX_orb0_mem hΨ hσσ) (orbitY_orb0_mem hΨ hσσ)
  · exact key _ (orbitX_orb1_mem hΨ hσσ) (orbitY_orb1_mem hΨ hσσ)
  · exact key _ (orbitX_leaf_mem hΨ hε0 hε) (orbitY_leaf_mem hΨ hε0 hε)
  · exact absurd ha (by decide)

end OrbitMembers

end CFSG.LieType.SeitzGeneration.ExcHigh.TwSU6
