module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListRank2b
public import CFSG.LieType.Ree.SuzukiSimple

public section

namespace CFSG.QuasithinUnique.Vol2Native.A312L

open CFSG.QuasithinUnique.Setup.X6
open CFSG.Quasithin hiding lemma_1_2_1_one lemma_1_2_1_two lemma_1_2_4_exists lemma_1_2_4_unique
  lemma_1_2_4_existsUnique normal_conjClosure_of_pCoreOf_ne_bot

@[expose] def LeviDataSz (f : ℕ) {S : Type} [Group S] (P : Subgroup S) : Prop :=
  ∃ (a : ℕ) (K : Type) (_ : Field K) (_ : Finite K), 1 ≤ a ∧ f = 2 * a + 1 ∧
    Nat.card K = 2 ^ f ∧
    ∃ g : ↥(perfectCore P) →* CFSG.Blueprint.suzukiGroup a K,
      Function.Surjective g ∧ IsPGroup 2 g.ker

theorem a312For_of_rank2_ree
    {S : Type} [Group S] [Finite S] (hq : CFSG.IsQuasisimple S)
    {U : Subgroup S} {P : Fin 2 → Subgroup S} (hU : CFSG.QuasithinUnique.IsSylowTwoOf U ⊤)
    (hP : ResidualOvergroupsAt S U P) (hN : ∀ j, Subgroup.normalizer (U : Set S) ≤ P j) {f : ℕ}
    (hf : Odd f) (hf3 : 3 ≤ f) (h2F4 : Is2F4 f S)
    (hLevi : ∀ j, LeviData (P j) ∨ LeviDataSz f (P j)) : A312For S := by
  refine A312For.of_sylow U hU fun B hB hBtop => ?_
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
  have hN' : perfectCore (B ⊔ U) = perfectCore (P j) := by
    rw [← dInf_eq_perfectCore, ← dInf_eq_perfectCore, hd]
  have hnb : perfectCore (P j) ≠ ⊥ := fun h =>
    hns ((isSolvable_iff_perfectCore_eq_bot _).mpr (hN'.trans h))
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rcases hLevi j with h0 | h1
  ·
    rcases h0 with h | ⟨K, _, _, _, n, hn, hn2, g, hg, hker⟩
    · exact absurd h hnb
    · have hK4 : ∃ s : Finset K, s.card = 4 := by
        refine exists_finset_card_four ?_
        rw [hn]
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn2
      have hsimple := sl2_isSimple hK4
      have hnab := sl2_nonabelian hK4
      have hsolv : Group.IsSolvable g.ker := by
        have := hker.isNilpotent
        infer_instance
      have hBeq : B = perfectCore (P j) := lFamily_eq_of_perfectCore_eq hB hN' hnab g hg hsolv
      rw [hBeq]
      have hR : IsRank2LieChar2 S :=
        Or.inl ⟨f, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨hf, hf3, h2F4⟩))))⟩
      refine Or.inl ⟨?_, IsRank2LieChar2.of_mulEquiv Subgroup.topEquiv.symm hR, P j,
        isMaxParabolic2_of_residual hU hP hN j, rfl⟩
      have h2n : 2 ^ 2 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn2
      refine ⟨n, ⟨Nat.prime_two, by omega, le_rfl, ?_, ?_⟩, K, inferInstance, inferInstance, hn,
        ⟨(modO2EquivOfHom hnab g hg hker).trans sl2EquivStatedProj⟩⟩
      · intro h
        have := congrArg Prod.snd h
        simp only at this
        omega
      · intro h
        have := congrArg Prod.snd h
        simp only at this
        omega
  ·
    obtain ⟨a, K, _, _, ha, hfa, hK, g, hg, hker⟩ := h1
    have hK' : Nat.card K = 2 ^ (2 * a + 1) := by rw [← hfa]; exact hK
    obtain ⟨hfin, hnt, hsimple⟩ := CFSG.LieType.Ree.suzuki_simple ha hK'
    have hnab : ∃ x y : CFSG.Blueprint.suzukiGroup a K, x * y ≠ y * x := by
      by_contra hcon
      push Not at hcon
      have : IsMulCommutative (CFSG.Blueprint.suzukiGroup a K) := ⟨⟨hcon⟩⟩
      have : Group.IsPerfect (CFSG.Blueprint.suzukiGroup a K) :=
        (CFSG.LieType.Ree.suzuki_perfect ha hK').2
      exact Group.IsPerfect.not_isMulCommutative (CFSG.Blueprint.suzukiGroup a K) ‹_›
    have hsolv : Group.IsSolvable g.ker := by
      have := hker.isNilpotent
      infer_instance
    have hBeq : B = perfectCore (P j) := lFamily_eq_of_perfectCore_eq hB hN' hnab g hg hsolv
    rw [hBeq]
    refine Or.inr (Or.inl ⟨f, ⟨rfl, a, ha, K, inferInstance, inferInstance, hfa, hK,
      ⟨modO2EquivOfHom hnab g hg hker⟩⟩, Is2F4.of_mulEquiv Subgroup.topEquiv.symm h2F4, P j,
      (isMaxParabolic2_of_residual hU hP hN j).1, rfl⟩)

end CFSG.QuasithinUnique.Vol2Native.A312L
