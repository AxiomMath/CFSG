module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.LieOver.Tags
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.B113LieEngine
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X6Containment
public import CFSG.LieType.Chevalley.ParabolicRadicalSelfCentralizing
public import CFSG.LieType.Chevalley.ParabolicRadicalNormalizer
public import CFSG.LieType.Chevalley.ExceptionalG2F4ModelSchreier

public section

namespace CFSG.Quasithin.LieOver

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Blueprint.Chevalley
open CFSG.LieType.Chevalley CFSG.QuasithinUnique.Setup.X6 CFSG.QuasithinUnique.B113Lie

theorem lb_charTwo {G : Type*} [Group G] {P Q : Subgroup G} (hQP : Q ≤ P)
    (hPN : P ≤ Subgroup.normalizer (Q : Set G)) (hQ2 : IsPGroup 2 Q)
    (hsc : P ⊓ Subgroup.centralizer (Q : Set G) ≤ Q) : CharTwo P := by
  have hQle : Q ≤ pCoreOf 2 P :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hQP hPN hQ2
  intro x hx
  have hxC : x ∈ Subgroup.centralizer (Q : Set G) :=
    Subgroup.centralizer_le (SetLike.coe_subset_coe.2 hQle) hx.2
  exact hQle (hsc ⟨hx.1, hxC⟩)

section Chevalley

variable (τ : Tag) (K : Type) [Field K]


theorem lb_weyl_not_mem (i : Fin τ.rank) :
    weylElt τ K i 1 ∉ parabolicSubgroup τ K {j | j ≠ i} := by
  rw [weylElt_mem_parabolicSubgroup_iff]
  simp

theorem lb_ne_univ (i : Fin τ.rank) : ({j | j ≠ i} : Set (Fin τ.rank)) ≠ Set.univ := by
  intro h
  have hi : i ∈ ({j | j ≠ i} : Set (Fin τ.rank)) := by
    rw [h]
    exact Set.mem_univ i
  exact (show i ≠ i from hi) rfl

theorem lb_subgroupOf_ne_top (i : Fin τ.rank) :
    (parabolicSubgroup τ K {j | j ≠ i}).subgroupOf (adjointGroup τ K) ≠ ⊤ := by
  intro h
  apply lb_weyl_not_mem τ K i
  have hx : (⟨weylElt τ K i 1, weylElt_mem_adjointGroup i 1⟩ : ↥(adjointGroup τ K)) ∈
      (parabolicSubgroup τ K {j | j ≠ i}).subgroupOf (adjointGroup τ K) := by
    rw [h]
    exact Subgroup.mem_top _
  exact Subgroup.mem_subgroupOf.1 hx

theorem lb_U_le_C : posUnipotent τ K ≤ adjointGroup τ K :=
  (posUnipotent_le_parabolicSubgroup (τ := τ) (K := K) Set.univ).trans
    (parabolicSubgroup_le_adjointGroup τ K Set.univ)

theorem lb_Q_le_U (J : Set (Fin τ.rank)) : parabolicRadical τ K J ≤ posUnipotent τ K :=
  parabolicRadical_le_posUnipotent (τ := τ) (K := K) J

theorem lb_Q_le_C (J : Set (Fin τ.rank)) : parabolicRadical τ K J ≤ adjointGroup τ K :=
  (lb_Q_le_U τ K J).trans (lb_U_le_C τ K)

theorem lb_Q_le_P (J : Set (Fin τ.rank)) : parabolicRadical τ K J ≤ parabolicSubgroup τ K J :=
  (lb_Q_le_U τ K J).trans (posUnipotent_le_parabolicSubgroup (τ := τ) (K := K) J)

theorem lb_sylow [Finite K] [CharP K 2] :
    IsSylowTwoOf ((posUnipotent τ K).subgroupOf (adjointGroup τ K)) ⊤ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Finite (ModGL τ K) := finite_modGL (τ := τ) (K := K)
  exact CFSG.QuasithinUnique.Setup.X6.isSylowTwoOf_subgroupOf_top
    (CFSG.QuasithinUnique.Setup.X6.isSylowTwoOf_iff_isSylowOf.2
      (unique_Chevalley_positive_Sylow (τ := τ) (K := K) 2).1)

theorem lb_U_le_coatom (i : Fin τ.rank) :
    (posUnipotent τ K).subgroupOf (adjointGroup τ K) ≤
      (parabolicSubgroup τ K {j | j ≠ i}).subgroupOf (adjointGroup τ K) :=
  Subgroup.subgroupOf_mono _ (posUnipotent_le_parabolicSubgroup (τ := τ) (K := K) _)

theorem lb_cover : ∀ A : Subgroup ↥(adjointGroup τ K),
    (posUnipotent τ K).subgroupOf (adjointGroup τ K) ≤ A → A ≠ ⊤ →
      ∃ P ∈ (Set.range fun i : Fin τ.rank =>
        (parabolicSubgroup τ K {j | j ≠ i}).subgroupOf (adjointGroup τ K)), A ≤ P := by
  intro A hUA hA
  have hAM_le : A.map (adjointGroup τ K).subtype ≤ adjointGroup τ K := by
    rintro _ ⟨x, -, rfl⟩
    exact x.2
  have hUAM : posUnipotent τ K ≤ A.map (adjointGroup τ K).subtype := by
    rw [← Subgroup.map_subgroupOf_eq_of_le (lb_U_le_C τ K)]
    exact Subgroup.map_mono hUA
  have hAM_ne : A.map (adjointGroup τ K).subtype ≠ adjointGroup τ K := by
    intro h
    apply hA
    apply Subgroup.map_injective (adjointGroup τ K).subtype_injective
    rw [h, Subgroup.map_top, Subgroup.range_subtype]
  obtain ⟨J, hJ, hAJ, -⟩ :=
    (chevalley_positive_root_overgroup_parabolic_containment (τ := τ) (K := K) hAM_le hUAM).2.2
      hAM_ne
  obtain ⟨i, hi⟩ : ∃ i, i ∉ J := by
    by_contra h
    exact hJ (Set.eq_univ_of_forall fun i => not_not.1 fun hi => h ⟨i, hi⟩)
  refine ⟨(parabolicSubgroup τ K {j | j ≠ i}).subgroupOf (adjointGroup τ K), ⟨i, rfl⟩, ?_⟩
  intro x hx
  apply Subgroup.mem_subgroupOf.2
  have hPJ : parabolicSubgroup τ K J ≤ parabolicSubgroup τ K {j | j ≠ i} :=
    (parabolicSubgroup_le_parabolicSubgroup_iff (τ := τ) (K := K)).2
      (fun j hj => show j ≠ i from fun hji => hi (hji ▸ hj))
  exact hPJ (hAJ ⟨x, hx, rfl⟩)

theorem lb_charTwo_coatom [Finite K] [CharP K 2] (i : Fin τ.rank) :
    CharTwo ((parabolicSubgroup τ K {j | j ≠ i}).subgroupOf (adjointGroup τ K)) := by
  have hJ : ({j | j ≠ i} : Set (Fin τ.rank)) ≠ Set.univ := lb_ne_univ τ i
  have hQC : parabolicRadical τ K {j | j ≠ i} ≤ adjointGroup τ K := lb_Q_le_C τ K _
  have hQ2 : IsPGroup 2 ((parabolicRadical τ K {j | j ≠ i}).subgroupOf (adjointGroup τ K)) :=
    IsPGroup.to_le (lb_sylow τ K).2.1 (Subgroup.subgroupOf_mono _ (lb_Q_le_U τ K _))
  have hQP : (parabolicRadical τ K {j | j ≠ i}).subgroupOf (adjointGroup τ K) ≤
      (parabolicSubgroup τ K {j | j ≠ i}).subgroupOf (adjointGroup τ K) :=
    Subgroup.subgroupOf_mono _ (lb_Q_le_P τ K _)
  refine lb_charTwo hQP ?_ hQ2 ?_
  · exact le_of_eq (by
      rw [CFSG.QuasithinUnique.Setup.X6.normalizer_subgroupOf_eq' hQC,
        adjointGroup_inf_normalizer_parabolicRadical])
  · rintro x ⟨hxP, hxC⟩
    have hxP' : (x : ModGL τ K) ∈ parabolicSubgroup τ K {j | j ≠ i} :=
      Subgroup.mem_subgroupOf.1 hxP
    have hcomm : ∀ q ∈ parabolicRadical τ K {j | j ≠ i},
        q * (x : ModGL τ K) = (x : ModGL τ K) * q := by
      intro q hq
      have hq' : (⟨q, hQC hq⟩ : ↥(adjointGroup τ K)) ∈
          (parabolicRadical τ K {j | j ≠ i}).subgroupOf (adjointGroup τ K) :=
        Subgroup.mem_subgroupOf.2 hq
      exact congrArg Subtype.val (Subgroup.mem_centralizer_iff.1 hxC _ hq')
    have hxQ : (x : ModGL τ K) ∈ parabolicRadical τ K {j | j ≠ i} :=
      (Chevalley_proper_parabolic_root_radical_self_centralizing τ K hJ).2
        (Subgroup.mem_inf.2 ⟨hxP', Subgroup.mem_centralizer_iff.2 hcomm⟩)
    exact Subgroup.mem_subgroupOf.2 hxQ

theorem lb_gen (hτ : 2 ≤ τ.rank) :
    sSup (Set.range fun i : Fin τ.rank =>
      (parabolicSubgroup τ K {j | j ≠ i}).subgroupOf (adjointGroup τ K)) = ⊤ := by
  set H := sSup (Set.range fun i : Fin τ.rank =>
    (parabolicSubgroup τ K {j | j ≠ i}).subgroupOf (adjointGroup τ K)) with hH
  have hPle : ∀ i : Fin τ.rank,
      (parabolicSubgroup τ K {j | j ≠ i}).subgroupOf (adjointGroup τ K) ≤ H :=
    fun i => le_sSup ⟨i, rfl⟩
  have hPmap : ∀ i : Fin τ.rank,
      parabolicSubgroup τ K {j | j ≠ i} ≤ H.map (adjointGroup τ K).subtype := by
    intro i
    calc parabolicSubgroup τ K {j | j ≠ i}
        = ((parabolicSubgroup τ K {j | j ≠ i}).subgroupOf (adjointGroup τ K)).map
            (adjointGroup τ K).subtype :=
          (Subgroup.map_subgroupOf_eq_of_le (parabolicSubgroup_le_adjointGroup τ K _)).symm
      _ ≤ H.map (adjointGroup τ K).subtype := Subgroup.map_mono (hPle i)
  have hpos : 0 < τ.rank := by omega
  have hBle : borelGroup τ K ≤ H.map (adjointGroup τ K).subtype := by
    have hB := borelGroup_le_parabolicSubgroup (τ := τ) (K := K)
      {j | j ≠ (⟨0, hpos⟩ : Fin τ.rank)}
    exact hB.trans (hPmap ⟨0, hpos⟩)
  have hweyl : ∀ i : Fin τ.rank, weylElt τ K i 1 ∈ H.map (adjointGroup τ K).subtype := by
    intro i
    obtain ⟨k, hk⟩ := Fintype.exists_ne_of_one_lt_card (by rw [Fintype.card_fin]; omega) i
    exact hPmap k ((weylElt_mem_parabolicSubgroup_iff (τ := τ) (K := K)).2 hk.symm)
  have hAMle : H.map (adjointGroup τ K).subtype ≤ adjointGroup τ K := by
    rintro _ ⟨x, -, rfl⟩
    exact x.2
  have hAM : H.map (adjointGroup τ K).subtype = adjointGroup τ K := by
    have hcl := (borel_overgroup_classification (τ := τ) (K := K)).1 _ hBle hAMle
    have hI : {i : Fin τ.rank | weylElt τ K i 1 ∈ H.map (adjointGroup τ K).subtype} =
        Set.univ := Set.eq_univ_of_forall hweyl
    rw [hI, (standard_parabolic_cells τ K).2.2.2.2.2.1] at hcl
    exact hcl
  apply eq_top_iff.2
  intro x _
  have hx : (x : ModGL τ K) ∈ H.map (adjointGroup τ K).subtype := by
    rw [hAM]
    exact x.2
  obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.1 hx
  have hxy : y = x := Subtype.ext hyx
  rw [← hxy]
  exact hy

theorem lb_inv (i : Fin τ.rank) (α : MulAut ↥(adjointGroup τ K))
    (hα : ∀ u ∈ (posUnipotent τ K).subgroupOf (adjointGroup τ K), α u = u) :
    ((parabolicSubgroup τ K {j | j ≠ i}).subgroupOf (adjointGroup τ K)).map α.toMonoidHom =
      (parabolicSubgroup τ K {j | j ≠ i}).subgroupOf (adjointGroup τ K) := by
  have hQU : (parabolicRadical τ K {j | j ≠ i}).subgroupOf (adjointGroup τ K) ≤
      (posUnipotent τ K).subgroupOf (adjointGroup τ K) :=
    Subgroup.subgroupOf_mono _ (lb_Q_le_U τ K _)
  have hQfix : ∀ q ∈ (parabolicRadical τ K {j | j ≠ i}).subgroupOf (adjointGroup τ K),
      α q = q :=
    fun q hq => hα q (hQU hq)
  have hQmap := map_eq_of_fixes hQfix
  have hN : Subgroup.normalizer
      (((parabolicRadical τ K {j | j ≠ i}).subgroupOf (adjointGroup τ K) :
        Subgroup ↥(adjointGroup τ K)) : Set ↥(adjointGroup τ K)) =
      (parabolicSubgroup τ K {j | j ≠ i}).subgroupOf (adjointGroup τ K) := by
    rw [CFSG.QuasithinUnique.Setup.X6.normalizer_subgroupOf_eq' (lb_Q_le_C τ K _),
      adjointGroup_inf_normalizer_parabolicRadical]
  rw [← hN, Subgroup.map_equiv_normalizer_eq, hQmap]

theorem lb_parabolicData [Finite K] [CharP K 2] (hτ : 2 ≤ τ.rank) :
    CFSG.QuasithinUnique.B113Lie.ParabolicData ↥(adjointGroup τ K)
      ((posUnipotent τ K).subgroupOf (adjointGroup τ K))
      (Set.range fun i : Fin τ.rank =>
        (parabolicSubgroup τ K {j | j ≠ i}).subgroupOf (adjointGroup τ K)) where
  sylow := lb_sylow τ K
  le := by
    rintro _ ⟨i, rfl⟩
    exact ⟨lb_U_le_coatom τ K i, lb_subgroupOf_ne_top τ K i⟩
  cover := lb_cover τ K
  charTwo := by
    rintro _ ⟨i, rfl⟩
    exact lb_charTwo_coatom τ K i
  gen := lb_gen τ K hτ
  inv := by
    intro α hα _ P hP
    obtain ⟨i, rfl⟩ := hP
    exact lb_inv τ K i α hα

theorem lb_sylowFacts (hτ : 2 ≤ τ.rank) {S : Type} [Group S] [Finite S] {f : ℕ}
    (h : CFSG.Blueprint.UntwistedChevalleyModel S τ (2 ^ f)) {T : Subgroup S}
    (hT : IsSylowTwoOf T ⊤) : CFSG.QuasithinUnique.B113Lie.SylowFacts S T := by
  obtain ⟨Kf, hFf, hFin, hK, ⟨e⟩⟩ := CFSG.LieType.Chevalley.nonempty_mulEquiv_adjointGroup τ h
  have hf : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with h0 | h0
    · have h1 : 1 < Nat.card Kf := Finite.one_lt_card
      rw [hK, h0, pow_zero] at h1
      exact absurd h1 (lt_irrefl 1)
    · exact h0
  have hcp : CharP Kf 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two hf hK
  haveI : Finite (ModGL τ Kf) := finite_modGL (τ := τ) (K := Kf)
  exact CFSG.QuasithinUnique.B113Lie.SylowFacts.of_mulEquiv_isSylow e
    (lb_parabolicData τ Kf hτ).sylowFacts hT

theorem lb_sylowProps (hτ : 2 ≤ τ.rank) {X : Type} [Group X] [Finite X] {f : ℕ}
    (h : CFSG.Blueprint.UntwistedChevalleyModel X τ (2 ^ f)) : SylowProps X := by
  have hsyl : ∀ T : Subgroup X, IsSylowTwoOf T ⊤ →
      CFSG.QuasithinUnique.B113Lie.SylowFacts X T :=
    fun _ hT => lb_sylowFacts τ hτ h hT
  unfold SylowProps
  exact ⟨CFSG.QuasithinUnique.B113Lie.overgroups_of_forall_sylowFacts hsyl,
    CFSG.QuasithinUnique.B113Lie.oddAut_of_forall_sylowFacts hsyl⟩

end Chevalley

theorem asLieTwoAt_f4 :
    AsLieTwoAt .F4 := by
  intro n f X _ _ _ _ hmod
  exact lb_sylowProps Tag.F4 (by decide) (hmod.chevalleyExceptionalModel (by decide)).2

theorem asLieTwoAt_e6 :
    AsLieTwoAt .E6 := by
  intro n f X _ _ _ _ hmod
  exact lb_sylowProps Tag.E6 (by decide) (hmod.chevalleyExceptionalModel (by decide)).2

theorem asLieTwoAt_e7 :
    AsLieTwoAt .E7 := by
  intro n f X _ _ _ _ hmod
  exact lb_sylowProps Tag.E7 (by decide) (hmod.chevalleyExceptionalModel (by decide)).2

theorem asLieTwoAt_e8 :
    AsLieTwoAt .E8 := by
  intro n f X _ _ _ _ hmod
  exact lb_sylowProps Tag.E8 (by decide) (hmod.chevalleyExceptionalModel (by decide)).2

end CFSG.Quasithin.LieOver
