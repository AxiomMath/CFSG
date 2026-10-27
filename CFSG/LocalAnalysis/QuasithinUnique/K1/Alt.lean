module

public import CFSG.LocalAnalysis.QuasithinUnique.K1.AltGroup
import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.DicksonClassification
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.II.theorem_6_14

public section

namespace CFSG.QuasithinUnique.K1

open scoped MatrixGroups

namespace Alt

private theorem card_psl_two_four : Nat.card PSL(2, GaloisField 2 2) = 60 := by
  have hK : Nat.card (GaloisField 2 2) = 4 := by
    rw [GaloisField.card 2 2 (by norm_num)]
    norm_num
  have : CharP (GaloisField 2 2) 2 := inferInstance
  have hcenter := CFSG.BenderSuzuki.External.huppert614_card_center_of_neg_one_eq_one
    (K := GaloisField 2 2) (CharTwo.neg_eq 1)
  have hcard := CFSG.BenderSuzuki.External.huppert614_card_psl_mul_center
    (K := GaloisField 2 2)
  rw [hK, hcenter] at hcard
  norm_num at hcard
  exact hcard

private theorem nonempty_mulEquiv_alternatingGroup_five_of_card_sixty {G : Type} [Group G]
    [Finite G] [IsSimpleGroup G] (hG : Nat.card G = 60) :
    Nonempty (G ≃* alternatingGroup (Fin 5)) := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨P⟩ : Nonempty (Sylow 5 G) := inferInstance
  have hP : Nat.card P = 5 := by
    rw [Sylow.card_eq_multiplicity, hG, show (60 : ℕ) = 5 * 12 by rfl,
      Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
      Nat.Prime.factorization_self (by norm_num),
      Nat.factorization_eq_zero_of_not_dvd (by norm_num)]
    norm_num
  have hnot_normal : ¬ (P : Subgroup G).Normal := fun hN => by
    rcases hN.eq_bot_or_eq_top with h | h
    · rw [h, Subgroup.card_bot] at hP
      omega
    · rw [h, Subgroup.card_top, hG] at hP
      omega
  have hcard : Nat.card (Sylow 5 G) = 6 := by
    have hmod := card_sylow_modEq_one 5 G
    have hdvd : Nat.card (Sylow 5 G) ∣ 12 := by
      have h := P.card_dvd_index
      rwa [(P : Subgroup G).index_eq_card, show Nat.card (G ⧸ (P : Subgroup G)) = 12 by
        have := (P : Subgroup G).card_mul_index
        rw [hP, hG, (P : Subgroup G).index_eq_card] at this
        omega] at h
    have hpos : 0 < Nat.card (Sylow 5 G) := Nat.card_pos
    have hle := Nat.le_of_dvd (by norm_num) hdvd
    have hne1 : Nat.card (Sylow 5 G) ≠ 1 := fun h1 => by
      have : Subsingleton (Sylow 5 G) := (Nat.card_eq_one_iff_unique.mp h1).1
      exact hnot_normal (Sylow.normal_of_subsingleton P)
    unfold Nat.ModEq at hmod
    interval_cases h : Nat.card (Sylow 5 G) <;> simp_all
  have hfaithful : FaithfulSMul G (Sylow 5 G) := by
    let φ := MulAction.toPermHom G (Sylow 5 G)
    rcases (MonoidHom.normal_ker φ).eq_bot_or_eq_top with hk | hk
    · refine ⟨fun {g h} hgh => ?_⟩
      have : φ g = φ h := Equiv.ext hgh
      exact (MonoidHom.ker_eq_bot_iff φ).mp hk this
    · refine absurd ?_ hnot_normal
      rw [← Subgroup.normalizer_eq_top_iff, eq_top_iff]
      intro g _
      have hg : g ∈ φ.ker := hk ▸ Subgroup.mem_top g
      exact Sylow.smul_eq_iff_mem_normalizer.mp
        (congrArg (fun σ : Equiv.Perm (Sylow 5 G) => σ P) hg)
  exact Glauberman.Dickson.huppert_II_8_25_transitive_degree_six_order_sixty
    (Ω := Sylow 5 G) inferInstance hcard hG

theorem alternating_five_isBender {X : Type} [Group X]
    (e : X ≃* alternatingGroup (Fin 5)) : CFSG.Open.fusionIsBenderGroup X := by
  have hPSLsimple : IsSimpleGroup PSL(2, GaloisField 2 2) :=
    Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by
      rw [GaloisField.card 2 2 (by norm_num)]
      norm_num)
  have hfin : Finite PSL(2, GaloisField 2 2) :=
    Nat.finite_of_card_ne_zero (by rw [card_psl_two_four]; norm_num)
  obtain ⟨e5⟩ := nonempty_mulEquiv_alternatingGroup_five_of_card_sixty
    (G := PSL(2, GaloisField 2 2)) card_psl_two_four
  exact Or.inl ⟨2, le_rfl, ⟨e.trans e5.symm⟩⟩

end Alt

theorem k1_alt : K1FamilyRecognition AltFamily := by
  intro G _ _ H S U L hD hP w hwU hwS hwL _hchar
  obtain ⟨n, hn5, hn8, ⟨φ⟩⟩ := hP
  by_cases h5 : n = 5
  · subst h5
    exact Alt.alternating_five_isBender φ
  · exfalso
    rcases (show n = 6 ∨ n = 7 ∨ n = 8 by omega) with rfl | rfl | rfl
    · exact Alt.false_of_qlevel hD Alt.R6_isPGroup Alt.qlevelFalse_six φ hwU hwS hwL
    · exact Alt.false_of_qlevel hD Alt.R7_isPGroup Alt.qlevelFalse_seven φ hwU hwS hwL
    · exact Alt.false_of_qlevel hD Alt.R8_isPGroup Alt.qlevelFalse_eight φ hwU hwS hwL

end CFSG.QuasithinUnique.K1
