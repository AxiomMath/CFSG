module

public import CFSG.ClassicalInvolution.Basic
public import CFSG.Blueprint.Catalog
public import CFSG.Open.GeneralizedFittingSelfCentralizingMilestoneDefs

public section

namespace CFSG.ClassicalInvolution

open CFSG.Open CFSG.Blueprint

section Configuration

variable {G : Type*} [Group G]

@[expose] def conjugateSet (J : Subgroup G) : Set (Subgroup G) :=
  {A | ∃ g : G, A = J.map (MulAut.conj g⁻¹).toMonoidHom}

@[expose] def commutingAdj (J A B : Subgroup G) : Prop :=
  A ∈ conjugateSet J ∧ B ∈ conjugateSet J ∧ A ≠ B ∧ ∀ a ∈ A, ∀ b ∈ B, a * b = b * a

@[expose] def DeltaConnected (J : Subgroup G) : Prop :=
  ∀ A ∈ conjugateSet J, ∀ B ∈ conjugateSet J, Relation.ReflTransGen (commutingAdj J) A B

@[expose] def DistinctCentralTriple (z : G) (J : Subgroup G) : Prop :=
  ∃ g : Fin 3 → G, (∀ i j, i ≠ j → ∀ a ∈ J.map (MulAut.conj (g i)⁻¹).toMonoidHom,
      ∀ b ∈ J.map (MulAut.conj (g j)⁻¹).toMonoidHom, a * b = b * a) ∧
    Function.Injective fun i => (g i)⁻¹ * z * g i

theorem case_partition (z : G) (J : Subgroup G) :
    Group.IsSolvable J ∨ (¬ Group.IsSolvable J ∧ ¬ DeltaConnected J) ∨
      (¬ Group.IsSolvable J ∧ DeltaConnected J ∧ ¬ DistinctCentralTriple z J) ∨
      (¬ Group.IsSolvable J ∧ DeltaConnected J ∧ DistinctCentralTriple z J) := by
  by_cases hs : Group.IsSolvable J
  · exact Or.inl hs
  by_cases hc : DeltaConnected J
  · by_cases ht : DistinctCentralTriple z J
    · exact Or.inr (Or.inr (Or.inr ⟨hs, hc, ht⟩))
    · exact Or.inr (Or.inr (Or.inl ⟨hs, hc, ht⟩))
  · exact Or.inr (Or.inl ⟨hs, hc⟩)

end Configuration

abbrev PartOneConclusion (G : Type) [Group G] : Prop :=
  OddLieType (genFittingFStar G) ∨ NativeSporadic.IsSporadic (genFittingFStar G) .M11

abbrev PartTwoConclusion (G : Type) [Group G] : Prop :=
  OddLieType (genFittingFStar G) ∨ NativeSporadic.IsSporadic (genFittingFStar G) .M11 ∨
    NativeSporadic.IsSporadic (genFittingFStar G) .M12

@[expose] def PartOneUnder (P : ∀ {G : Type} [Group G], G → Subgroup G → Prop) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup (genFittingFStar G)],
    (∃ a b : genFittingFStar G, a * b ≠ b * a) →
    ∀ (z : G), orderOf z = 2 → ∀ (J : Subgroup G), z ∈ J →
    IsSubnormal J (Subgroup.centralizer ({z} : Set G)) →
    ∀ (S : Sylow 2 J),
    (∃ r : ℕ, 3 ≤ r ∧ Nonempty ((S : Subgroup J) ≃* QuaternionGroup (2 ^ (r - 2)))) →
    classicalInvolutionWitness J → P z J → PartOneConclusion G

abbrev PartOneSolvable : Prop :=
  PartOneUnder fun _ J => Group.IsSolvable J

abbrev PartOneDisconnected : Prop :=
  PartOneUnder fun _ J => ¬ Group.IsSolvable J ∧ ¬ DeltaConnected J

abbrev PartOneConnectedNoTriple : Prop :=
  PartOneUnder fun z J => ¬ Group.IsSolvable J ∧ DeltaConnected J ∧ ¬ DistinctCentralTriple z J

abbrev PartOneConnectedTriple : Prop :=
  PartOneUnder fun z J => ¬ Group.IsSolvable J ∧ DeltaConnected J ∧ DistinctCentralTriple z J

abbrev PartOne : Prop :=
  PartOneUnder fun _ _ => True

theorem partOne_of_cases (hs : PartOneSolvable) (hd : PartOneDisconnected)
    (hn : PartOneConnectedNoTriple) (ht : PartOneConnectedTriple) : PartOne := by
  intro G _ _ _ hnab z hz J hzJ hJ S hS hw _
  rcases case_partition z J with h | h | h | h
  · exact hs G hnab z hz J hzJ hJ S hS hw h
  · exact hd G hnab z hz J hzJ hJ S hS hw h
  · exact hn G hnab z hz J hzJ hJ S hS hw h
  · exact ht G hnab z hz J hzJ hJ S hS hw h

@[expose] def NormalOddByQuaternionUnder
    (P : ∀ {G : Type} [Group G] [Finite G], Subgroup G → Prop) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup (genFittingFStar G)],
    (∃ a b : genFittingFStar G, a * b ≠ b * a) →
    ∀ (R : Subgroup G) (S : Sylow 2 R),
    (∃ r : ℕ, 3 ≤ r ∧ Nonempty ((S : Subgroup R) ≃* QuaternionGroup (2 ^ (r - 2)))) →
    ∀ t : G, t ∈ (S : Subgroup R).map R.subtype → orderOf t = 2 →
    R ≤ Subgroup.centralizer ({t} : Set G) →
    (R.subgroupOf (Subgroup.centralizer ({t} : Set G))).Normal →
    IsPGroup 2 (R ⧸ classicalInvolutionOddCore R) →
    P ((S : Subgroup R).map R.subtype) → PartTwoConclusion G

@[expose] def NormalizerHasSylow {G : Type} [Group G] [Finite G] (S : Subgroup G) : Prop :=
  ∃ T : Sylow 2 G, (T : Subgroup G) ≤ Subgroup.normalizer (S : Set G)

abbrev NormalOddByQuaternionAmbient : Prop :=
  NormalOddByQuaternionUnder fun S => NormalizerHasSylow S

abbrev NormalOddByQuaternionNonambient : Prop :=
  NormalOddByQuaternionUnder fun S => ¬ NormalizerHasSylow S

abbrev NormalOddByQuaternion : Prop :=
  NormalOddByQuaternionUnder fun _ => True

theorem normalOddByQuaternion_of_cases (ha : NormalOddByQuaternionAmbient)
    (hn : NormalOddByQuaternionNonambient) : NormalOddByQuaternion := by
  intro G _ _ _ hnab R S hS t ht hto hRC hRn h2 _
  by_cases hamb : NormalizerHasSylow ((S : Subgroup R).map R.subtype)
  · exact ha G hnab R S hS t ht hto hRC hRn h2 hamb
  · exact hn G hnab R S hS t ht hto hRC hRn h2 hamb

@[expose] def WitnessOfNotTwoGroup : Prop :=
  ∀ {G : Type} [Group G] [Finite G] (J : Subgroup G) (S : Sylow 2 J),
    (∃ r : ℕ, 3 ≤ r ∧ Nonempty ((S : Subgroup J) ≃* QuaternionGroup (2 ^ (r - 2)))) →
    ¬ IsPGroup 2 (J ⧸ classicalInvolutionOddCore J) →
    ∃ J' : Subgroup G, J' ≤ J ∧ (J'.subgroupOf J).Normal ∧ classicalInvolutionWitness J' ∧
      ∃ S' : Sylow 2 J', ∃ r : ℕ, 3 ≤ r ∧
        Nonempty ((S' : Subgroup J') ≃* QuaternionGroup (2 ^ (r - 2)))

section Helpers

variable {G : Type} [Group G]

theorem sylow_map_isPGroup_ne_bot {J : Subgroup G} (S : Sylow 2 J)
    (hS : ∃ r : ℕ, 3 ≤ r ∧ Nonempty ((S : Subgroup J) ≃* QuaternionGroup (2 ^ (r - 2)))) :
    IsPGroup 2 ((S : Subgroup J).map J.subtype) ∧ (S : Subgroup J).map J.subtype ≠ ⊥ := by
  refine ⟨S.isPGroup'.map J.subtype, ?_⟩
  obtain ⟨r, -, ⟨e⟩⟩ := hS
  intro hbot
  have hS1 : (S : Subgroup J) = ⊥ :=
    (Subgroup.map_eq_bot_iff_of_injective _ J.subtype_injective).mp hbot
  have hcard : Nat.card (S : Subgroup J) = 4 * 2 ^ (r - 2) := by
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]
  rw [hS1, Subgroup.card_bot] at hcard
  have : 0 < 2 ^ (r - 2) := Nat.pow_pos (by norm_num)
  omega

end Helpers

theorem models_of_partOne_of_normalOddByQuaternion (h1 : PartOne)
    (h2 : NormalOddByQuaternion) (hw : WitnessOfNotTwoGroup)
    (G : Type) [Group G] [Finite G]
    [IsSimpleGroup (genFittingFStar G)]
    (hFnonab : ∃ a b : genFittingFStar G, a * b ≠ b * a)
    (z : G) (hz : orderOf z = 2)
    (J : Subgroup G) (hzJ : z ∈ J) (hJ : IsSubnormal J (Subgroup.centralizer ({z} : Set G)))
    (S : Sylow 2 J)
    (hS : ∃ r : ℕ, 3 ≤ r ∧ Nonempty ((S : Subgroup J) ≃* QuaternionGroup (2 ^ (r - 2)))) :
    (classicalInvolutionWitness J → Blueprint.OddLieType (genFittingFStar G) ∨
      Blueprint.NativeSporadic.IsSporadic (genFittingFStar G) .M11) ∧
    (classicalInvolutionTightlyEmbedded J → Blueprint.OddLieType (genFittingFStar G) ∨
      Blueprint.NativeSporadic.IsSporadic (genFittingFStar G) .M11 ∨
      Blueprint.NativeSporadic.IsSporadic (genFittingFStar G) .M12) := by
  have hcent : J ≤ Subgroup.centralizer ({z} : Set G) := isSubnormal_le hJ
  have hU := (unique_involution_of_quaternion_sylow hzJ hz hcent S hS).2
  refine ⟨fun hw' => h1 G hFnonab z hz J hzJ hJ S hS hw' trivial, fun hTE => ?_⟩
  have hCN : Subgroup.centralizer ({z} : Set G) ≤ Subgroup.normalizer (J : Set G) :=
    (tightlyEmbedded_iff_centralizer_le_normalizer hzJ hz hcent S hS).mp hTE
  have hJn : (J.subgroupOf (Subgroup.centralizer ({z} : Set G))).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hcent).mpr hCN
  by_cases h2grp : IsPGroup 2 (J ⧸ classicalInvolutionOddCore J)
  · obtain ⟨hSp, hSne⟩ := sylow_map_isPGroup_ne_bot S hS
    have hzS : z ∈ (S : Subgroup J).map J.subtype :=
      hU _ (Subgroup.map_subtype_le _) hSp hSne
    exact h2 G hFnonab J S hS z hzS hz hcent hJn h2grp trivial
  · obtain ⟨J', hJ'J, hJ'n, hw', S', hS'⟩ := hw J S hS h2grp
    obtain ⟨hSp', hSne'⟩ := sylow_map_isPGroup_ne_bot S' hS'
    have hzJ' : z ∈ J' := by
      have := hU _ ((Subgroup.map_subtype_le _).trans hJ'J) hSp' hSne'
      exact Subgroup.map_subtype_le _ this
    have hJ'sub : IsSubnormal J' (Subgroup.centralizer ({z} : Set G)) :=
      isSubnormal_trans (isSubnormal_of_normal_subgroupOf hJ'J hJ'n)
        (isSubnormal_of_normal_subgroupOf hcent hJn)
    rcases h1 G hFnonab z hz J' hzJ' hJ'sub S' hS' hw' trivial with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)

end CFSG.ClassicalInvolution
