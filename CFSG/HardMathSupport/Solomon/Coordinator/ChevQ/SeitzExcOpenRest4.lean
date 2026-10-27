module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.SeitzExcOpenRest3
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.SeitzExcOpenRest4Twist
public import CFSG.LieType.SeitzGeneration.ExcHighThree.KillsRootF4

public noncomputable section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.SeitzExcOpenRest4

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.SeitzGeneration
  CFSG.LieType.SeitzGeneration.ExcHigh CFSG.LieType.SeitzGeneration.ExcHighThree TauCeti
  CFSG.LieType.Seitz CFSG.AGLEmbedding CFSG.HardMathSupport.Solomon.Coordinator.ChevQ
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.SeitzExcOpenRest4Twist

set_option linter.unusedSectionVars false

section E8One

@[expose] def E8OneFiveCubeRest4 : Prop :=
  ∀ (K : Type) [Field K] [Finite K], orderOf ((Nat.card K : ℕ) : ZMod 5) = 1 →
    ∀ E₀ : Subgroup (adjointGroup .E8 K), IsElemAbelian 5 E₀ → Nat.card E₀ = 5 ^ 3 →
      ¬ NormalizesRGroup (ringChar K) E₀ →
      (∀ (ζ : K) (hζ : IsPrimitiveRoot ζ 5) (a : Fin Tag.E8.rank → Kˣ) (g : adjointGroup .E8 K),
        E₀ ≠ (griessCubeT hζ a).map (MulAut.conj g).toMonoidHom) →
      HyperGen 5 ⊤ E₀

end E8One

section ThreeDefs

@[expose] def SeitzGoodInnerExcThreeF4 : Prop :=
  SeitzHyperLie fun d p E₀ => IsF4Index d.1 ∧ ¬ NormalizesRSub d E₀ ∧ SeitzGoodIndex p d.1 ∧
    p = 3

@[expose] def SeitzGoodInnerExcThreeE6 : Prop :=
  SeitzHyperLie fun d p E₀ => IsE6Index d.1 ∧ ¬ NormalizesRSub d E₀ ∧ SeitzGoodIndex p d.1 ∧
    p = 3

@[expose] def SeitzGoodInnerExcThreeTwE6 : Prop :=
  SeitzHyperLie fun d p E₀ => IsTwistedE6Index d.1 ∧ ¬ NormalizesRSub d E₀ ∧
    SeitzGoodIndex p d.1 ∧ p = 3

@[expose] def SeitzGoodInnerExcThreeE7 : Prop :=
  SeitzHyperLie fun d p E₀ => IsE7Index d.1 ∧ ¬ NormalizesRSub d E₀ ∧ SeitzGoodIndex p d.1 ∧
    p = 3

@[expose] def SeitzGoodInnerExcThreeE8 : Prop :=
  SeitzHyperLie fun d p E₀ => IsE8Index d.1 ∧ ¬ NormalizesRSub d E₀ ∧ SeitzGoodIndex p d.1 ∧
    p = 3

@[expose] def ThreeScope (c : PrimePower → LieTypeIndex) (K : Type) : Prop :=
  ∃ (q : PrimePower) (hv : (c q).Valid), Nat.card K = q.card ∧ SeitzGoodIndex 3 (c q) ∧
    ¬ P1ThreeLieList 3 ⟨c q, hv⟩

@[expose] def ThreeToralCubeRest (τ : Tag) (c : PrimePower → LieTypeIndex) : Prop :=
  ∀ (K : Type) [Field K] [Finite K], ¬ 3 ∣ Nat.card K → ThreeScope c K →
    ∀ E₀ : Subgroup (adjointGroup τ K), IsElemAbelian 3 E₀ → Nat.card E₀ = 3 ^ 3 →
      ¬ NormalizesRGroup (ringChar K) E₀ → ∀ D : LangPlaneData τ K E₀,
        (∀ α : Fin τ.rank → ℤ, IsRoot τ α → ¬ D.Kills α) → HyperGen 3 ⊤ E₀

@[expose] def ThreeNonToralCubeRest (τ : Tag) (c : PrimePower → LieTypeIndex) : Prop :=
  ∀ (K : Type) [Field K] [Finite K], ¬ 3 ∣ Nat.card K → ThreeScope c K →
    ∀ E₀ : Subgroup (adjointGroup τ K), IsElemAbelian 3 E₀ → Nat.card E₀ = 3 ^ 3 →
      ¬ NormalizesRGroup (ringChar K) E₀ → IsEmpty (LangPlaneData τ K E₀) → HyperGen 3 ⊤ E₀

@[expose] def SeitzThreeResidual4 : Prop :=
  (ThreeToralCubeRest .F4 LieTypeIndex.F4 ∧ ThreeNonToralCubeRest .F4 LieTypeIndex.F4) ∧
    SeitzGoodInnerExcThreeE6 ∧ SeitzGoodInnerExcThreeTwE6 ∧
    (ThreeToralCubeRest .E7 LieTypeIndex.E7 ∧ ThreeNonToralCubeRest .E7 LieTypeIndex.E7) ∧
    (ThreeToralCubeRest .E8 LieTypeIndex.E8 ∧ ThreeNonToralCubeRest .E8 LieTypeIndex.E8)

end ThreeDefs

section Residual

@[expose] def SeitzExcOpenResidual4 : Prop :=
  SeitzThreeResidual4 ∧ E8OneFiveCubeRest4 ∧ SeitzExcOpenRest3.E8TwoFiveCubeRest ∧
    SeitzExcOpenRest3.E8FourFiveCubeRest

end Residual

section Generic

variable {G : Type*} [Group G]

theorem normalizesRGroup_of_commute {r : ℕ} {E₀ : Subgroup G} {u : G} (hu : u ≠ 1)
    (hur : ∃ n : ℕ, u ^ (r ^ n) = 1) (hc : ∀ x ∈ E₀, Commute u x) : NormalizesRGroup r E₀ := by
  obtain ⟨n, hn⟩ := hur
  refine ⟨Subgroup.zpowers u, fun h => hu ?_, fun g => ⟨n, ?_⟩, fun x hx => ?_⟩
  · have hmem : u ∈ Subgroup.zpowers u := Subgroup.mem_zpowers u
    rw [h] at hmem
    exact Subgroup.mem_bot.1 hmem
  · obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.1 g.2
    apply Subtype.ext
    rw [SubgroupClass.coe_pow, OneMemClass.coe_one, ← hm, ← zpow_natCast, ← zpow_mul, mul_comm,
      zpow_mul, zpow_natCast, hn, one_zpow]
  · rw [MonoidHom.map_zpowers]
    congr 1
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [← (hc x hx).eq, mul_inv_cancel_right]

end Generic

section Proofs

theorem e8OneFiveCubeRest_of_rest4 (h : E8OneFiveCubeRest4) :
    SeitzExcOpenRest3.E8OneFiveCubeRest := by
  intro K _ _ he E₀ hE₀ hc hN
  by_cases hG : ∃ (ζ : K) (hζ : IsPrimitiveRoot ζ 5) (a : Fin Tag.E8.rank → Kˣ)
      (g : adjointGroup .E8 K), E₀ = (griessCubeT hζ a).map (MulAut.conj g).toMonoidHom
  · obtain ⟨ζ, hζ, a, g, rfl⟩ := hG
    exact hyperGen_conj_griessCubeT hζ a g
  · exact h K he E₀ hE₀ hc hN fun ζ hζ a g hEq => hG ⟨ζ, hζ, a, g, hEq⟩

theorem seitzGoodInnerExcThree_of_types (hF4 : SeitzGoodInnerExcThreeF4)
    (hE6 : SeitzGoodInnerExcThreeE6) (hTw : SeitzGoodInnerExcThreeTwE6)
    (hE7 : SeitzGoodInnerExcThreeE7) (hE8 : SeitzGoodInnerExcThreeE8) :
    SeitzExcOpenRest3.SeitzGoodInnerExcThree := by
  intro d p hp hp2 hpd hlist E₀ hE₀ hcard ⟨htop, hN, hgood, h3⟩
  rcases htop with h | h | h | h | h
  · exact hF4 d p hp hp2 hpd hlist E₀ hE₀ hcard ⟨h, hN, hgood, h3⟩
  · exact hE6 d p hp hp2 hpd hlist E₀ hE₀ hcard ⟨h, hN, hgood, h3⟩
  · exact hE7 d p hp hp2 hpd hlist E₀ hE₀ hcard ⟨h, hN, hgood, h3⟩
  · exact hE8 d p hp hp2 hpd hlist E₀ hE₀ hcard ⟨h, hN, hgood, h3⟩
  · exact hTw d p hp hp2 hpd hlist E₀ hE₀ hcard ⟨h, hN, hgood, h3⟩

theorem hyperGen_three_of_toral_nonToral {τ : Tag} {c : PrimePower → LieTypeIndex}
    (hkill : LangPlaneKillsRoot τ) (ht : ThreeToralCubeRest τ c) (hn : ThreeNonToralCubeRest τ c)
    (K : Type) [Field K] [Finite K] (hK : ¬ 3 ∣ Nat.card K) (hs : ThreeScope c K)
    (E₀ : Subgroup (adjointGroup τ K)) (hE₀ : IsElemAbelian 3 E₀) (hc : Nat.card E₀ = 3 ^ 3)
    (hN : ¬ NormalizesRGroup (ringChar K) E₀) : HyperGen 3 ⊤ E₀ := by
  rcases isEmpty_or_nonempty (LangPlaneData τ K E₀) with h | h
  · exact hn K hK hs E₀ hE₀ hc hN h
  · obtain ⟨D⟩ := h
    refine ht K hK hs E₀ hE₀ hc hN D fun α hα hk => hN ?_
    obtain ⟨u, hu1, hur, hcomm⟩ := hkill K E₀ D α hα hk
    exact normalizesRGroup_of_commute hu1 hur hcomm

theorem seitzHyperLie_three_of_rest {τ : Tag} {c : PrimePower → LieTypeIndex}
    (hB : CFSG.TauCetiBridge.Even.UntwistedBridgeAll τ c)
    (hc : ∀ q : PrimePower, (c q).characteristic = q.p) (hkill : LangPlaneKillsRoot τ)
    (ht : ThreeToralCubeRest τ c) (hn : ThreeNonToralCubeRest τ c) :
    SeitzHyperLie fun d p E₀ => (∃ q : PrimePower, d.1 = c q) ∧ ¬ NormalizesRSub d E₀ ∧
      SeitzGoodIndex p d.1 ∧ p = 3 := by
  rintro ⟨d, hv⟩ p hp hp2 hpd hlist E₀ hE₀ hcard ⟨⟨q, hq⟩, hN, hgood, rfl⟩
  simp only at hq
  subst hq
  obtain ⟨K, _, _, hKq, hchar, ⟨e⟩⟩ := exists_catEquiv_adjointGroup hB q hv
  have hrc : ringChar K = q.p := ringChar.eq K q.p
  have hK3 : ¬ 3 ∣ Nat.card K := by
    rw [hKq]
    refine not_dvd_card_of_ne Nat.prime_three fun h3 => hpd ?_
    show 3 = (c q).characteristic
    rw [hc q]
    exact h3
  refine SeitzExcOpenCubes.hyperGen_of_mulEquiv e ?_
  refine hyperGen_three_of_toral_nonToral hkill ht hn K hK3 ⟨q, hv, hKq, hgood, hlist⟩ _
    (CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_map 3 hE₀ _)
    (by rw [Subgroup.card_map_of_injective e.injective, hcard]) fun hN' => hN ?_
  have h1 := SeitzExcOpenRest2.normalizesRGroup_of_map_mulEquiv e hN'
  rw [hrc, ← hc q] at h1
  exact h1

theorem seitzGoodInnerExcThreeF4_of_rest (ht : ThreeToralCubeRest .F4 LieTypeIndex.F4)
    (hn : ThreeNonToralCubeRest .F4 LieTypeIndex.F4) : SeitzGoodInnerExcThreeF4 :=
  seitzHyperLie_three_of_rest CFSG.TauCetiBridge.Even.chevalleyBridgesAll.f4
    LieTypeIndex.characteristic_F4 langPlaneKillsRoot_F4 ht hn

theorem seitzGoodInnerExcThreeE7_of_rest (ht : ThreeToralCubeRest .E7 LieTypeIndex.E7)
    (hn : ThreeNonToralCubeRest .E7 LieTypeIndex.E7) : SeitzGoodInnerExcThreeE7 :=
  seitzHyperLie_three_of_rest CFSG.TauCetiBridge.Even.chevalleyBridgesAll.e7
    LieTypeIndex.characteristic_E7 langPlaneKillsRoot_E7 ht hn

theorem seitzGoodInnerExcThreeE8_of_rest (ht : ThreeToralCubeRest .E8 LieTypeIndex.E8)
    (hn : ThreeNonToralCubeRest .E8 LieTypeIndex.E8) : SeitzGoodInnerExcThreeE8 :=
  seitzHyperLie_three_of_rest CFSG.TauCetiBridge.Even.chevalleyBridgesAll.e8
    LieTypeIndex.characteristic_E8 langPlaneKillsRoot_E8 ht hn

theorem seitzGoodInnerExcThree_of_residual4 (h : SeitzThreeResidual4) :
    SeitzExcOpenRest3.SeitzGoodInnerExcThree := by
  obtain ⟨⟨hF4t, hF4n⟩, hE6, hTw, ⟨hE7t, hE7n⟩, ⟨hE8t, hE8n⟩⟩ := h
  exact seitzGoodInnerExcThree_of_types (seitzGoodInnerExcThreeF4_of_rest hF4t hF4n) hE6 hTw
    (seitzGoodInnerExcThreeE7_of_rest hE7t hE7n) (seitzGoodInnerExcThreeE8_of_rest hE8t hE8n)

theorem seitzExcOpenResidual3_of_residual4 (h : SeitzExcOpenResidual4) :
    SeitzExcOpenRest3.SeitzExcOpenResidual3 :=
  ⟨seitzGoodInnerExcThree_of_residual4 h.1, e8OneFiveCubeRest_of_rest4 h.2.1, h.2.2.1, h.2.2.2⟩

end Proofs

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.SeitzExcOpenRest4

end
