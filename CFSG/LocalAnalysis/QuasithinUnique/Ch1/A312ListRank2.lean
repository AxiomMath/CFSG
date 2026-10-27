module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListCore
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X6Residual
public import CFSG.LinearAlgebra.LinearGroups.ProjectiveSimple
public import CFSG.Walter.PSL2Facts.Even
public import CFSG.Assembly.GL83LieDefs

public section

namespace CFSG.QuasithinUnique.Vol2Native.A312L

open CFSG.QuasithinUnique.Setup.X6
open CFSG.Quasithin hiding lemma_1_2_1_one lemma_1_2_1_two lemma_1_2_4_exists lemma_1_2_4_unique
  lemma_1_2_4_existsUnique normal_conjClosure_of_pCoreOf_ne_bot

theorem dInf_eq_perfectCore {G : Type} [Group G] [Finite G] (M : Subgroup G) :
    dInf M = perfectCore M :=
  le_antisymm
    (le_perfectCore_of_perfect (dInf_le M) (Subgroup.isPerfect_iff.mp (dInf_isPerfect M)))
    (le_dInf_of_perfect (Subgroup.isPerfect_iff.mpr (perfectCore_perfect M)) (perfectCore_le M))

theorem lFamily_eq_of_perfectCore_eq {X : Type} [Group X] [Finite X] {T B N : Subgroup X}
    (hB : B ∈ lFamily T) (hN : perfectCore (B ⊔ T) = N) {S : Type} [Group S] [IsSimpleGroup S]
    (hS : ∃ a b : S, a * b ≠ b * a) (f : ↥N →* S) (hf : Function.Surjective f)
    (hker : Group.IsSolvable f.ker) : B = N := by
  subst hN
  exact lFamily_eq_perfectCore hB hS f hf hker

theorem isMaxParabolic2_of_residual {S : Type} [Group S] [Finite S] {U : Subgroup S}
    (hU : CFSG.QuasithinUnique.IsSylowTwoOf U ⊤) {P : Fin 2 → Subgroup S}
    (hP : ResidualOvergroupsAt S U P) (hN : ∀ j, Subgroup.normalizer (U : Set S) ≤ P j)
    (j : Fin 2) : IsMaxParabolic2 (⊤ : Subgroup S) (P j) := by
  have hc : P j ⋖ ⊤ := (hP.2.2.1 (P j) (hP.2.1 j)).2 ⟨j, rfl⟩
  refine ⟨⟨le_top, U, hU, fun g hg => hN j hg.2⟩, hc.lt.ne, ?_⟩
  intro Q _ hQtop hPQ
  by_contra hne
  exact hc.2 (lt_of_le_of_ne hPQ (Ne.symm hne)) (lt_top_iff_ne_top.mpr hQtop)

theorem rank2_eq_perfectCore {S : Type} [Group S] [Finite S] (hq : CFSG.IsQuasisimple S)
    {U : Subgroup S} {P : Fin 2 → Subgroup S} (hP : ResidualOvergroupsAt S U P)
    (hsimple : ∀ j, ∃ (T : Type) (_ : Group T) (_ : IsSimpleGroup T),
      (∃ a b : T, a * b ≠ b * a) ∧ ∃ f : ↥(perfectCore (P j)) →* T,
        Function.Surjective f ∧ Group.IsSolvable f.ker)
    {B : Subgroup S} (hB : B ∈ lFamily U) (hBtop : B ≠ ⊤) : ∃ j, B = perfectCore (P j) := by
  have hB' : B ∈ cComp (B ⊔ U) := hB
  have hne : B ⊔ U ≠ ⊤ := by
    intro htop
    rw [htop] at hB'
    exact hBtop (A321.cComp_eq_top_of_quasisimple hq hB')
  have hns : ¬ Group.IsSolvable ↥(B ⊔ U) := fun hs =>
    not_isSolvable_of_mem_cComp hB'
      (Group.isSolvable_of_isSolvable_injective
        (f := Subgroup.inclusion (le_of_mem_cComp hB' : B ≤ B ⊔ U))
        (Subgroup.inclusion_injective _))
  obtain ⟨j, -, hd⟩ := hP.2.2.2.2.1 (B ⊔ U) le_sup_right hne hns
  have hN : perfectCore (B ⊔ U) = perfectCore (P j) := by
    rw [← dInf_eq_perfectCore, ← dInf_eq_perfectCore, hd]
  obtain ⟨T, _, _, hT, f, hf, hker⟩ := hsimple j
  exact ⟨j, lFamily_eq_of_perfectCore_eq hB hN hT f hf hker⟩

theorem a312For_of_rank2 {S : Type} [Group S] [Finite S] (hq : CFSG.IsQuasisimple S)
    {U : Subgroup S} {P : Fin 2 → Subgroup S} (hU : CFSG.QuasithinUnique.IsSylowTwoOf U ⊤)
    (hP : ResidualOvergroupsAt S U P) (hN : ∀ j, Subgroup.normalizer (U : Set S) ≤ P j)
    (hR : IsRank2LieChar2 S) (hmod : ∀ j, ∃ n, IsPSL 2 2 n (ModO2 (perfectCore (P j))))
    (hsimple : ∀ j, ∃ (T : Type) (_ : Group T) (_ : IsSimpleGroup T),
      (∃ a b : T, a * b ≠ b * a) ∧ ∃ f : ↥(perfectCore (P j)) →* T,
        Function.Surjective f ∧ Group.IsSolvable f.ker) : A312For S := by
  refine A312For.of_sylow U hU fun B hB hBtop => ?_
  obtain ⟨j, rfl⟩ := rank2_eq_perfectCore hq hP hsimple hB hBtop
  exact Or.inl ⟨hmod j, IsRank2LieChar2.of_mulEquiv Subgroup.topEquiv.symm hR, P j,
    isMaxParabolic2_of_residual hU hP hN j, rfl⟩

theorem a312For_of_rank2_solvable {S : Type} [Group S] [Finite S] (hq : CFSG.IsQuasisimple S)
    {U : Subgroup S} {P : Fin 2 → Subgroup S} (hU : CFSG.QuasithinUnique.IsSylowTwoOf U ⊤)
    (hP : ResidualOvergroupsAt S U P) (hsolv : ∀ j, perfectCore (P j) = ⊥) : A312For S := by
  refine A312For.of_solvable_overgroups hq U hU fun M hUM hMtop => ?_
  by_contra hns
  obtain ⟨j, -, hd⟩ := hP.2.2.2.2.1 M hUM hMtop hns
  apply hns
  rw [isSolvable_iff_perfectCore_eq_bot, ← dInf_eq_perfectCore, hd, dInf_eq_perfectCore]
  exact hsolv j

theorem pCore_two_eq_ker {G S : Type*} [Group G] [Group S] [Finite S] [IsSimpleGroup S]
    (hS : ∃ a b : S, a * b ≠ b * a) (g : G →* S) (hg : Function.Surjective g)
    (hker : IsPGroup 2 g.ker) : CFSG.pCore 2 G = g.ker := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine le_antisymm ?_ (le_sSup ⟨inferInstance, hker⟩)
  have hP : IsPGroup 2 (CFSG.pCore 2 G) := CFSG.pCore_isPGroup
  have hN : ((CFSG.pCore 2 G).map g).Normal := Subgroup.Normal.map inferInstance g hg
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((CFSG.pCore 2 G).map g) with h | h
  · intro x hx
    have : g x ∈ (CFSG.pCore 2 G).map g := ⟨x, hx, rfl⟩
    rw [h] at this
    exact this
  · exfalso
    have h2 : IsPGroup 2 S := by
      have := hP.map g
      rw [h] at this
      exact IsPGroup.of_equiv this Subgroup.topEquiv
    have := h2.isNilpotent
    obtain ⟨a, b, hab⟩ := hS
    exact hab (IsSimpleGroup.comm_iff_isSolvable.mpr inferInstance a b)

noncomputable def modO2EquivOfHom {X : Type} [Group X] {B : Subgroup X} {S : Type} [Group S]
    [Finite S] [IsSimpleGroup S] (hS : ∃ a b : S, a * b ≠ b * a) (g : ↥B →* S)
    (hg : Function.Surjective g) (hker : IsPGroup 2 g.ker) : ModO2 B ≃* S :=
  (QuotientGroup.quotientMulEquivOfEq (pCore_two_eq_ker hS g hg hker)).trans
    (QuotientGroup.quotientKerEquivOfSurjective g hg)

section Levi

open Matrix CFSG.Assembly.LowTwoRank

variable {K : Type} [Field K]

omit [Field K] in
theorem exists_finset_card_four [Finite K] (h4 : 4 ≤ Nat.card K) :
    ∃ s : Finset K, s.card = 4 := by
  have := Fintype.ofFinite K
  have hle : 4 ≤ (Finset.univ : Finset K).card := by
    rw [Finset.card_univ, ← Nat.card_eq_fintype_card]
    exact h4
  obtain ⟨s, -, hs⟩ := Finset.exists_subset_card_eq hle
  exact ⟨s, hs⟩

theorem sl2_isSimple [CharP K 2] (hK4 : ∃ s : Finset K, s.card = 4) :
    IsSimpleGroup (SpecialLinearGroup (Fin 2) K) := by
  obtain ⟨-, hsimple, -⟩ :=
    CFSG.LinearGroups.linear_projective_simple (K := K) (n := 2) le_rfl (Or.inr hK4)
  exact (CFSG.Walter.psl2MulEquivSL2OfCharTwo (K := K)).symm.isSimpleGroup

theorem sl2_nonabelian [CharP K 2] (hK4 : ∃ s : Finset K, s.card = 4) :
    ∃ a b : SpecialLinearGroup (Fin 2) K, a * b ≠ b * a := by
  have := sl2_isSimple hK4
  by_contra h
  push Not at h
  have hsolv : Group.IsSolvable (SpecialLinearGroup (Fin 2) K) :=
    IsSimpleGroup.comm_iff_isSolvable.mp h
  have hperf := CFSG.LinearGroups.special_linear_dimension_two_perfect (K := K) hK4
  exact (Group.IsSolvable.commutator_lt_top_of_nontrivial (G := SpecialLinearGroup (Fin 2) K)).ne
    (Group.isPerfect_def.mp hperf)

noncomputable def sl2EquivStatedProj [CharP K 2] :
    SpecialLinearGroup (Fin 2) K ≃* StatedProj (StatedSL 2 K) :=
  (CFSG.Walter.psl2MulEquivSL2OfCharTwo (K := K)).symm.trans
    (projectiveSpecialLinearGroupEquivStatedProj 2 K)

theorem a312For_of_rank2_levi {S : Type} [Group S] [Finite S] (hq : CFSG.IsQuasisimple S)
    {U : Subgroup S} {P : Fin 2 → Subgroup S} (hU : CFSG.QuasithinUnique.IsSylowTwoOf U ⊤)
    (hP : ResidualOvergroupsAt S U P) (hN : ∀ j, Subgroup.normalizer (U : Set S) ≤ P j)
    (hR : IsRank2LieChar2 S) [Finite K] [CharP K 2] {f : ℕ} (hf : Nat.card K = 2 ^ f)
    (hf2 : 2 ≤ f) (g : ∀ j, ↥(perfectCore (P j)) →* SpecialLinearGroup (Fin 2) K)
    (hg : ∀ j, Function.Surjective (g j)) (hker : ∀ j, IsPGroup 2 (g j).ker) :
    A312For S := by
  have hK4 : ∃ s : Finset K, s.card = 4 := by
    refine exists_finset_card_four ?_
    rw [hf]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf2
  have hsimple := sl2_isSimple hK4
  have hnab := sl2_nonabelian hK4
  have hsolvker : ∀ j, Group.IsSolvable (g j).ker := by
    intro j
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have := (hker j).isNilpotent
    infer_instance
  refine a312For_of_rank2 hq hU hP hN hR (fun j => ?_)
    (fun j => ⟨SpecialLinearGroup (Fin 2) K, inferInstance, hsimple, hnab, g j, hg j, hsolvker j⟩)
  have h2f : 2 ^ 2 ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf2
  refine ⟨f, ⟨Nat.prime_two, by omega, le_rfl, ?_, ?_⟩, K, inferInstance, inferInstance, hf,
    ⟨(modO2EquivOfHom hnab (g j) (hg j) (hker j)).trans sl2EquivStatedProj⟩⟩
  · intro h
    have := congrArg Prod.snd h
    simp only at this
    omega
  · intro h
    have := congrArg Prod.snd h
    simp only at this
    omega

end Levi

end CFSG.QuasithinUnique.Vol2Native.A312L
