module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.Inputs
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdStep2
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdGen
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.Claim1Basic

public section

namespace CFSG.QuasithinUnique.DoubleA3

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique Subgroup

theorem center_eq_bot_of_equiv_alt6 {K : Type*} [Group K] (e₀ : K ≃* alternatingGroup (Fin 6)) :
    Subgroup.center K = ⊥ := by
  rw [eq_bot_iff]
  intro z hz
  have hcenter : Subgroup.center (alternatingGroup (Fin 6)) = ⊥ :=
    alternatingGroup.center_eq_bot (by simp)
  have hmem : e₀ z ∈ Subgroup.center (alternatingGroup (Fin 6)) := by
    rw [Subgroup.mem_center_iff]
    intro y
    have h1 := Subgroup.mem_center_iff.mp hz (e₀.symm y)
    have h2 := congrArg e₀ h1
    simpa using h2
  rw [hcenter, Subgroup.mem_bot] at hmem
  rw [Subgroup.mem_bot]
  exact e₀.injective (hmem.trans (map_one e₀).symm)

variable {G : Type} [Group G] [Finite G] {T M H S L K : Subgroup G} {s x z₁ z₂ : G}

theorem A3A3K.balance
    (hI : Inputs2436) (h34 : Lemma2_4_34_used)
    (hK : A3A3K T M H S L s x z₁ z₂ K) {r : G} (hrC : r ∈ Subgroup.centralizer (K : Set G))
    (hr2 : r * r = 1) (hr1 : r ≠ 1) (hrz : r * z₂ = z₂ * r) :
    centralizerElem r ≤ normalizer (K : Set G) ∨
      ∃ J : Subgroup G, IsComponentIn J (centralizerElem r) ∧ K ≤ J ∧ K ≠ J ∧
        centralizerElem r ≤ normalizer (J : Set G) ∧ z₂ ∈ normalizer (J : Set G) := by
  have hcs := hK.cs
  have hsimple := hcs.setting.simple
  have hnonab := hcs.setting.nonabelian
  have hq := hcs.setting.qtke
  obtain ⟨e₀⟩ := hK.nonempty_alt6 h34
  have hr2' : r ^ 2 = 1 := by rw [pow_two]; exact hr2
  have hz₂1 : z₂ ≠ 1 := hK.toA3A3x.z₂_ne
  have hz₂2' : z₂ ^ 2 = 1 := hK.toA3A3x.sq₂
  have hKC : K ≤ centralizerElem r := fun κ hκ =>
    Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_iff.mp hrC κ hκ)
  have hKz : K ≤ centralizerElem z₂ := hK.K_comp.1
  have hX : IsComponentIn K
      (Subgroup.centralizer ({r} : Set G) ⊓ Subgroup.centralizer ({z₂} : Set G)) :=
    BenderBranch.isComponentIn_of_le hK.K_comp (le_inf hKC hKz) inf_le_right
  have hKcard : Nat.card ↥K = 360 := (Nat.card_congr e₀.toEquiv).trans card_alt6'
  have hXe : 2 ∣ Nat.card K := by rw [hKcard]; norm_num
  have hX4 : ∃ E : Subgroup G, E ≤ K ∧ IsElemAbelian 2 E ∧ Nat.card E = 4 :=
    ⟨blockU L, hK.isA4.le.trans hK.L_le_K, hK.isA4.isElemAbelian_U, hK.isA4.card_U⟩
  obtain ⟨hXY, hcases⟩ := Id2519.step2 hI.i32 hI.p121_3 hI.p121_5 hsimple hnonab hq hr1 hr2' hz₂1
    hz₂2' hrz hX hXe hX4
  have hpc : pCoreOf 2 (Subgroup.centralizer ({r} : Set G)) ≠ ⊥ :=
    Id2519.pCoreOf_centralizer_ne_bot hr1 hr2
  have hz₂C : z₂ ∈ centralizerElem r := Subgroup.mem_centralizer_singleton_iff.mpr hrz.symm
  rcases hcases with ⟨J, hJ, hYJ, hz₂N⟩ | ⟨J, hJ, hJne, hYJ, -, hiso⟩
  ·
    have hKJ : K ≤ J := hYJ ▸ hXY
    have hJq : CFSG.IsQuasisimple ↥J := BenderBranch.isQuasisimple_of_isComponentIn hJ
    have hJc : J ∈ cComp (Subgroup.centralizer ({r} : Set G)) :=
      Id2519.mem_cComp_of_isComponentIn hJ
    have hJN : centralizerElem r ≤ normalizer (J : Set G) := by
      rcases hI.p121_3 G hsimple hnonab hq _ hpc J hJc with hnorm | ⟨-, hlist⟩
      · exact hnorm
      · exfalso
        have hpcen := Id2519.pCore_eq_center_of_simple_quotient hJq hlist.1 hlist.2.1
        obtain ⟨E, hEK, hE, hEc⟩ := exists_isElemAbelian_nine_le e₀
        have hEJ : Id2519.HasElemAb 3 9 ↥J := Id2519.HasElemAb.of_subgroup (hEK.trans hKJ) hE hEc
        have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
        have hN2 : IsPGroup 2 ↥(Subgroup.center ↥J) := by
          rw [← hpcen]
          exact CFSG.pCore_isPGroup
        have hE9 : Id2519.HasElemAb 3 9 (↥J ⧸ Subgroup.center ↥J) :=
          Id2519.HasElemAb.quotient_two (Subgroup.center ↥J) hN2 hEJ
        exact Id2519.false_of_isList_of_hasE9 hI.threeRank hJq hE9 hlist
    by_cases hJK : K = J
    · left
      rw [hJK]
      exact hJN
    · right
      exact ⟨J, hJ, hKJ, hJK, hJN, hz₂N⟩
  ·
    exfalso
    have hJq : CFSG.IsQuasisimple ↥J := BenderBranch.isQuasisimple_of_isComponentIn hJ
    have hJc : J ∈ cComp (Subgroup.centralizer ({r} : Set G)) :=
      Id2519.mem_cComp_of_isComponentIn hJ
    rcases hI.p121_3 G hsimple hnonab hq _ hpc J hJc with hnorm | ⟨-, hlist⟩
    · exact hJne ((BenderBranch.conjugate_eq_iff_mem_normalizer.mpr (hnorm hz₂C)).symm)
    · obtain ⟨iso⟩ := hiso
      obtain ⟨E, hEK, hE, hEc⟩ := exists_isElemAbelian_nine_le e₀
      have hEK' : Id2519.HasElemAb 3 9 ↥K := Id2519.HasElemAb.of_subgroup hEK hE hEc
      have hcen : Subgroup.center ↥K = ⊥ := center_eq_bot_of_equiv_alt6 e₀
      let eKq : (↥K ⧸ Subgroup.center ↥K) ≃* ↥K :=
        (QuotientGroup.quotientMulEquivOfEq hcen).trans QuotientGroup.quotientBot
      have hE9 : Id2519.HasElemAb 3 9 (↥J ⧸ Subgroup.center ↥J) :=
        Id2519.HasElemAb.of_mulEquiv iso.symm (Id2519.HasElemAb.of_mulEquiv eKq.symm hEK')
      exact Id2519.false_of_isList_of_hasE9 hI.threeRank hJq hE9 hlist

end CFSG.QuasithinUnique.DoubleA3
