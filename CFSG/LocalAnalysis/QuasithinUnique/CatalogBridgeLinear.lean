module

public import CFSG.Assembly.InCatalog
import CFSG.Adapters.LinearCatalog
import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.DicksonClassification
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.II.theorem_6_14

public section

namespace CFSG.QuasithinUnique

open scoped MatrixGroups

open TauCeti

theorem inCatalog_of_mulEquiv_psl_zmod {X : Type} [Group X] {r p : ℕ} (hp : p.Prime)
    (hv : (LieTypeIndex.A r ⟨p, 1, hp, Nat.one_pos⟩).Valid) (e : X ≃* PSL(r + 1, ZMod p)) :
    CFSG.Assembly.InCatalog X := by
  have : Fact p.Prime := ⟨hp⟩
  let q : PrimePower := ⟨p, 1, hp, Nat.one_pos⟩
  let eF : ZMod p ≃+* GaloisField p 1 :=
    CFSG.ClassicalModels.finiteFieldEquivGaloisField (ZMod p) p 1 Nat.one_pos
      (by rw [Nat.card_zmod, pow_one])
  exact ⟨.lie ⟨_, hv⟩,
    ⟨(e.trans (CFSG.ClassicalModels.projectiveSpecialLinearFieldEquiv eF (Fin (r + 1)))).trans
      (CFSG.ClassicalModels.linearCatalogCandidateEquivPSL r q hv).symm⟩⟩

theorem inCatalog_of_mulEquiv_psl_two_zmod {X : Type} [Group X] {p : ℕ} (hp : p.Prime)
    (hp7 : 7 < p) (e : X ≃* PSL(2, ZMod p)) : CFSG.Assembly.InCatalog X := by
  have hp9 : p ≠ 9 := by
    rintro rfl
    norm_num at hp
  refine inCatalog_of_mulEquiv_psl_zmod (r := 1) hp ?_ e
  rw [LieTypeIndex.valid_iff, LieTypeIndex.inStandardRange_iff,
    LieTypeIndex.isDuplicateRepresentative_iff]
  simp only [PrimePower.card_def, pow_one]
  omega

theorem inCatalog_of_mulEquiv_psl_three_zmod_three {X : Type} [Group X]
    (e : X ≃* PSL(3, ZMod 3)) : CFSG.Assembly.InCatalog X := by
  refine inCatalog_of_mulEquiv_psl_zmod (r := 2) Nat.prime_three ?_ e
  rw [LieTypeIndex.valid_iff, LieTypeIndex.inStandardRange_iff,
    LieTypeIndex.isDuplicateRepresentative_iff]
  simp only [PrimePower.card_def, pow_one]
  omega

theorem nonempty_mulEquiv_alternatingGroup_five_of_card_sixty {G : Type*} [Group G] [Finite G]
    [IsSimpleGroup G] (hG : Nat.card G = 60) : Nonempty (G ≃* alternatingGroup (Fin 5)) := by
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

private theorem card_psl_two_galoisField_two : Nat.card PSL(2, GaloisField 2 2) = 60 := by
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

theorem inCatalog_of_mulEquiv_psl_two_galoisField_two {X : Type} [Group X] [Finite X]
    [IsSimpleGroup X] {f : ℕ} (hf : 2 ≤ f) (e : X ≃* PSL(2, GaloisField 2 f)) :
    CFSG.Assembly.InCatalog X := by
  rcases (show f = 2 ∨ 3 ≤ f by omega) with rfl | hf3
  · have hcard : Nat.card X = 60 := by
      rw [Nat.card_congr e.toEquiv]
      exact card_psl_two_galoisField_two
    obtain ⟨e5⟩ := nonempty_mulEquiv_alternatingGroup_five_of_card_sixty hcard
    exact ⟨.alternating 5 le_rfl, ⟨e5⟩⟩
  · let q : PrimePower := ⟨2, f, Nat.prime_two, by omega⟩
    have h8 : 8 ≤ 2 ^ f := le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) hf3)
    have h9 : 2 ^ f ≠ 9 := fun h => by
      obtain ⟨k, rfl⟩ : ∃ k, f = k + 1 := ⟨f - 1, by omega⟩
      rw [pow_succ] at h
      omega
    have hv : (LieTypeIndex.A 1 q).Valid := by
      rw [LieTypeIndex.valid_iff, LieTypeIndex.inStandardRange_iff,
        LieTypeIndex.isDuplicateRepresentative_iff]
      simp only [q, PrimePower.card_def]
      generalize 2 ^ f = N at *
      omega
    exact ⟨.lie ⟨_, hv⟩,
      ⟨e.trans (CFSG.ClassicalModels.linearCatalogCandidateEquivPSL 1 q hv).symm⟩⟩

end CFSG.QuasithinUnique
