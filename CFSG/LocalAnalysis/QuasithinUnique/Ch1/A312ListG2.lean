module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListLevi
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListFamilies
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X6ResidualG2
public import CFSG.LieType.Chevalley.ParabolicRadicalLevi
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListRank2

public section

namespace CFSG.QuasithinUnique.Vol2Native.A312L

open CFSG.LieType.Chevalley CFSG.Blueprint CFSG.Blueprint.Chevalley
open CFSG.QuasithinUnique.Setup.X6
open CFSG.Quasithin hiding lemma_1_2_1_one lemma_1_2_1_two lemma_1_2_4_exists lemma_1_2_4_unique
  lemma_1_2_4_existsUnique normal_conjClosure_of_pCoreOf_ne_bot

section Ordinary

variable {τ : Tag} {K : Type} [Field K] [Finite K] [CharP K 2]

omit [Finite K] in
theorem exists_rankOne_injective
    (i : Fin τ.rank) :
    ∃ ρ : SL2 K →* ModGL τ K, Function.Injective ρ ∧
      ρ.range = Subgroup.closure (Set.range (xUnit τ K i) ∪ Set.range (yUnit τ K i)) := by
  obtain ⟨ρ, -, -, -, -, hrange, hker, -, -⟩ := exceptional_ordinary_rank_one_central_image τ K i
  refine ⟨ρ, ?_, hrange⟩
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro g hg
  obtain ⟨l, hl, hgl⟩ := hker g hg
  have hl1 : (l : K) = 1 := by
    have h2 : ((l : K) - 1) ^ 2 = 0 := by
      linear_combination hl + (1 - (l : K)) * (CharTwo.two_eq_zero : (2 : K) = 0)
    exact sub_eq_zero.mp ((pow_eq_zero_iff two_ne_zero).mp h2)
  rw [Subgroup.mem_bot]
  refine Subtype.ext ?_
  rw [hgl, hl1, one_smul]
  rfl

omit [Finite K] in
theorem levi_data
    (hK4 : ∃ s : Finset K, s.card = 4) (i : Fin τ.rank) :
    ∃ ρ : SL2 K →* ModGL τ K, Function.Injective ρ ∧ ρ.range ≤ parabolicLevi τ K {i} ∧
      ⁅ρ.range, ρ.range⁆ = ρ.range ∧ perfectCore (parabolicLevi τ K {i}) ≤ ρ.range := by
  obtain ⟨ρ, hρ, hrange⟩ := exists_rankOne_injective (K := K) (τ := τ) i
  have hLM : ρ.range ≤ parabolicLevi τ K {i} := by
    rw [hrange]
    refine (Subgroup.closure_le _).2 ?_
    rintro _ (⟨c, rfl⟩ | ⟨c, rfl⟩)
    · exact xUnit_mem_parabolicLevi (Set.mem_singleton i) c
    · exact yUnit_mem_parabolicLevi (Set.mem_singleton i) c
  have hL : ⁅ρ.range, ρ.range⁆ = ρ.range := by
    have := CFSG.LinearGroups.special_linear_dimension_two_perfect (K := K) hK4
    exact Subgroup.isPerfect_iff.mp (Group.IsPerfect.range ρ)
  have hcl : Subgroup.closure
      {g | ∃ j ∈ ({i} : Set (Fin τ.rank)), ∃ c : K, g = xUnit τ K j c ∨ g = yUnit τ K j c} =
      ρ.range := by
    rw [hrange]
    congr 1
    ext g
    constructor
    · rintro ⟨j, hj, c, rfl | rfl⟩
      · rw [Set.mem_singleton_iff] at hj
        subst hj
        exact Or.inl ⟨c, rfl⟩
      · rw [Set.mem_singleton_iff] at hj
        subst hj
        exact Or.inr ⟨c, rfl⟩
    · rintro (⟨c, rfl⟩ | ⟨c, rfl⟩)
      · exact ⟨i, rfl, c, Or.inl rfl⟩
      · exact ⟨i, rfl, c, Or.inr rfl⟩
  have hMeq : parabolicLevi τ K {i} = ρ.range ⊔ torusGroup τ K := by
    rw [parabolicLevi, hcl, sup_comm]
  have hLspan : ρ.range = rootSpan τ K {Pi.single i 1, -Pi.single i 1} := by
    rw [hrange]
    apply le_antisymm
    · refine (Subgroup.closure_le _).2 ?_
      rintro _ (⟨c, rfl⟩ | ⟨c, rfl⟩)
      · rw [← pinnedX_single]
        exact pinnedX_mem_rootSpan (Set.mem_insert _ _) c
      · rw [← pinnedX_neg_single]
        exact pinnedX_mem_rootSpan (Set.mem_insert_of_mem _ (Set.mem_singleton _)) c
    · refine iSup₂_le fun α hα => ?_
      refine (Subgroup.closure_le _).2 ?_
      rintro _ ⟨c, rfl⟩
      rcases hα with rfl | hα
      · rw [pinnedX_single]
        exact Subgroup.subset_closure (Or.inl ⟨c, rfl⟩)
      · rw [Set.mem_singleton_iff] at hα
        subst hα
        rw [pinnedX_neg_single]
        exact Subgroup.subset_closure (Or.inr ⟨c, rfl⟩)
  have hHnorm : torusGroup τ K ≤ Subgroup.normalizer (ρ.range : Set (ModGL τ K)) := by
    rw [hLspan]
    refine torusGroup_le_normalizer_rootSpan ?_
    intro α hα
    rcases hα with rfl | hα
    · exact isRoot_single τ i
    · rw [Set.mem_singleton_iff] at hα
      subst hα
      exact isRoot_neg_single τ i
  refine ⟨ρ, hρ, hLM, hL, ?_⟩
  refine perfectCore_le_of_sup_solvable hLM ?_ hMeq ?_
  · rw [Subgroup.normal_subgroupOf_iff_le_normalizer hLM, hMeq]
    exact sup_le Subgroup.le_normalizer hHnorm
  · have : IsMulCommutative ↥(torusGroup τ K) :=
      ⟨⟨fun a b => Subtype.ext (mul_comm_of_mem_diagonalGroup
        (torusGroup_le_diagonalGroup a.2) (torusGroup_le_diagonalGroup b.2))⟩⟩
    infer_instance

theorem exists_levi_hom_adjoint
    {f : ℕ} (hK : Nat.card K = 2 ^ f) (hf2 : 2 ≤ f)
    (i : Fin τ.rank) :
    ∃ g : ↥(perfectCore ((parabolicSubgroup τ K {i}).subgroupOf (adjointGroup τ K))) →*
        SL2 K, Function.Surjective g ∧ IsPGroup 2 g.ker := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hK4 : ∃ s : Finset K, s.card = 4 := by
    refine exists_finset_card_four ?_
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf2
  obtain ⟨ρ, hρ, hLM, hL, hMinf⟩ := levi_data hK4 i
  have : Finite (ModGL τ K) := finite_modGL
  have hQP : parabolicRadical τ K {i} ≤ parabolicSubgroup τ K {i} :=
    (parabolicRadical_le_posUnipotent {i}).trans (posUnipotent_le_parabolicSubgroup {i})
  obtain ⟨g, hg, hk⟩ := exists_levi_hom_subgroupOf (C := adjointGroup τ K)
    (parabolicSubgroup_le_adjointGroup τ K {i}) hQP
    (parabolicSubgroup_le_normalizer_parabolicRadical {i}) (parabolicRadical_inf_parabolicLevi {i})
    (parabolicRadical_sup_parabolicLevi {i}) hLM hL hMinf
  have hQp : IsPGroup 2 ↥(parabolicRadical τ K {i}) := by
    refine IsPGroup.of_card (n := f * (parabolicRadicalRoots τ {i}).ncard) ?_
    rw [card_parabolicRadical, hK, ← pow_mul]
  let e : ↥ρ.range ≃* SL2 K := (MonoidHom.ofInjective hρ).symm
  refine ⟨e.toMonoidHom.comp g, e.surjective.comp hg, ?_⟩
  refine isPGroup_ker_of_levi hQp _ ?_
  intro x hx
  exact hk x ((MulEquiv.map_eq_one_iff e).mp hx)

end Ordinary

section G2

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem a312For_G2
    {f : ℕ} (hK : Nat.card K = 2 ^ f) (hf2 : 2 ≤ f)
    (hq : CFSG.IsQuasisimple ↥(adjointGroup Tag.G2 K))
    (hR : IsRank2LieChar2 ↥(adjointGroup Tag.G2 K)) : A312For ↥(adjointGroup Tag.G2 K) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (ModGL Tag.G2 K) := finite_modGL
  have hUC : posUnipotent Tag.G2 K ≤ adjointGroup Tag.G2 K := posUnipotent_le_adjointGroup
  have hU₀ : CFSG.QuasithinUnique.IsSylowTwoOf
      ((posUnipotent Tag.G2 K).subgroupOf (adjointGroup Tag.G2 K)) ⊤ :=
    isSylowTwoOf_subgroupOf_top (isSylowTwoOf_iff_isSylowOf.2
      (unique_Chevalley_positive_Sylow (τ := Tag.G2) (K := K) 2).1)
  choose g hg hker using fun j : Fin 2 =>
    exists_levi_hom_adjoint (τ := Tag.G2) (K := K) hK hf2 (g2Index j)
  refine a312For_of_rank2_levi hq hU₀ G2_residualOvergroupsAt ?_ hR hK hf2 g hg hker
  intro j c hc
  have hc' : (c : ModGL Tag.G2 K) ∈
      Subgroup.normalizer (posUnipotent Tag.G2 K : Set (ModGL Tag.G2 K)) := by
    have key : ∀ v : ↥(adjointGroup Tag.G2 K), (v : ModGL Tag.G2 K) ∈ posUnipotent Tag.G2 K ↔
        ((c * v * c⁻¹ : ↥(adjointGroup Tag.G2 K)) : ModGL Tag.G2 K) ∈ posUnipotent Tag.G2 K :=
      fun v => Subgroup.mem_normalizer_iff.1 hc v
    rw [Subgroup.mem_normalizer_iff]
    intro u
    constructor
    · intro hu
      exact (key ⟨u, hUC hu⟩).1 hu
    · intro hcu
      have huC : u ∈ adjointGroup Tag.G2 K := by
        have : u = (c : ModGL Tag.G2 K)⁻¹ * ((c : ModGL Tag.G2 K) * u * (c : ModGL Tag.G2 K)⁻¹) *
            (c : ModGL Tag.G2 K) := by group
        rw [this]
        exact mul_mem (mul_mem (inv_mem c.2) (hUC hcu)) c.2
      exact (key ⟨u, huC⟩).2 hcu
  have hB : (c : ModGL Tag.G2 K) ∈ borelGroup Tag.G2 K := by
    rw [← (borel_self_normalizers Tag.G2 K).1]
    exact ⟨c.2, hc'⟩
  exact borelGroup_le_parabolicSubgroup _ hB

end G2

theorem g2
    : FamG2 := by
  intro X _ _ f hq hf hX
  obtain ⟨-, K, hF, hFin, hcp, hK, ⟨e⟩⟩ := exists_mulEquiv_G2_model hX
  have hR : IsRank2LieChar2 X := Or.inl ⟨f, Or.inr (Or.inr (Or.inr (Or.inl ⟨hf, hX⟩)))⟩
  exact A312For.of_mulEquiv e (a312For_G2 hK hf (CFSG.LocalCores.isQuasisimple_of_mulEquiv e hq)
    (IsRank2LieChar2.of_mulEquiv e hR))

end CFSG.QuasithinUnique.Vol2Native.A312L
