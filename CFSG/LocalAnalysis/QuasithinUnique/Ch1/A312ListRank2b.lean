module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListRank2

public section

namespace CFSG.QuasithinUnique.Vol2Native.A312L

open CFSG.QuasithinUnique.Setup.X6
open CFSG.Quasithin hiding lemma_1_2_1_one lemma_1_2_1_two lemma_1_2_4_exists lemma_1_2_4_unique
  lemma_1_2_4_existsUnique normal_conjClosure_of_pCoreOf_ne_bot

@[expose] def LeviData {S : Type} [Group S] (P : Subgroup S) : Prop :=
  perfectCore P = ⊥ ∨ ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2) (n : ℕ),
    Nat.card K = 2 ^ n ∧ 2 ≤ n ∧
      ∃ g : ↥(perfectCore P) →* Matrix.SpecialLinearGroup (Fin 2) K,
        Function.Surjective g ∧ IsPGroup 2 g.ker

theorem a312For_of_rank2_levi_gen {S : Type} [Group S] [Finite S] (hq : CFSG.IsQuasisimple S)
    {U : Subgroup S} {P : Fin 2 → Subgroup S} (hU : CFSG.QuasithinUnique.IsSylowTwoOf U ⊤)
    (hP : ResidualOvergroupsAt S U P) (hN : ∀ j, Subgroup.normalizer (U : Set S) ≤ P j)
    (hR : IsRank2LieChar2 S) (hLevi : ∀ j, LeviData (P j)) : A312For S := by
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
  rcases hLevi j with h | ⟨K, _, _, _, n, hn, hn2, g, hg, hker⟩
  · exact absurd h hnb
  · have hK4 : ∃ s : Finset K, s.card = 4 := by
      refine exists_finset_card_four ?_
      rw [hn]
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn2
    have hsimple := sl2_isSimple hK4
    have hnab := sl2_nonabelian hK4
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hsolv : Group.IsSolvable g.ker := by
      have := hker.isNilpotent
      infer_instance
    have hBeq : B = perfectCore (P j) := lFamily_eq_of_perfectCore_eq hB hN' hnab g hg hsolv
    rw [hBeq]
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

end CFSG.QuasithinUnique.Vol2Native.A312L
