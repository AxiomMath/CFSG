module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ReeId
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.Unitary
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.UnitaryModel
import CFSG.Quasithin.Background.F6ResL28
import Certificates.Data.ExceptionalSL3

public section

namespace CFSG.AGLEmbedding

theorem exists_orderOf_eq_nine_of_isCaseTwoGroup_three {L : Type} [Group L]
    (hL : IsCaseTwoGroup 3 L) : ∃ x : L, orderOf x = 9 := by
  obtain ⟨⟨i, hi⟩, hd, ⟨e⟩⟩ := hL
  rcases hd with ⟨-, ⟨p, f, hp, hf⟩, hqp, hqe, hi1⟩ | ⟨h35, -⟩
  · subst hi1
    simp only at hqp hqe
    subst hqp hqe
    have : Fact (Nat.Prime 2) := ⟨hp⟩
    have hK : Nat.card (GaloisField 2 3) = 8 := by
      rw [GaloisField.card 2 3 (by norm_num)]
      norm_num
    obtain ⟨e₂⟩ := CFSG.Quasithin.F6.L28Res.nonempty_equiv (GaloisField 2 3) hK
    let e₃ : L ≃* CFSG.Quasithin.F6.L28Res.G8 :=
      (e.trans (CFSG.ClassicalModels.linearCatalogCandidateEquivPSL 1 _ hi)).trans
        ((CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 _).trans e₂)
    refine ⟨e₃.symm CFSG.Quasithin.F6.L28Res.g9, ?_⟩
    rw [MulEquiv.orderOf_eq]
    obtain ⟨-, -, h93, h99⟩ := CFSG.Quasithin.F6.L28Res.gen_facts_prod
    have := orderOf_eq_prime_pow (n := 1) (p := 3) (x := CFSG.Quasithin.F6.L28Res.g9)
      (by simpa using h93) (by simpa using h99)
    simpa using this
  · omega

theorem not_surjective_of_no_orderOf_nine {G L : Type} [Group G] [Finite G] [Group L]
    (hG : ∀ g : G, orderOf g ≠ 9) (A : Subgroup G) (f : A →* L) (hf : Function.Surjective f)
    (hL : ∃ x : L, orderOf x = 9) : False := by
  obtain ⟨x, hx⟩ := hL
  obtain ⟨a, rfl⟩ := hf x
  have hdvd : 9 ∣ orderOf a := hx ▸ orderOf_map_dvd f a
  obtain ⟨k, hk⟩ := hdvd
  have hpos : 0 < orderOf a := orderOf_pos a
  have hk0 : k ≠ 0 := by
    rintro rfl
    omega
  have hkdvd : k ∣ orderOf a := ⟨9, by rw [hk, mul_comm]⟩
  have hord : orderOf (a ^ k) = 9 := by
    rw [orderOf_pow_of_dvd hk0 hkdvd, hk, mul_comm]
    exact Nat.mul_div_cancel_left 9 (Nat.pos_of_ne_zero hk0)
  exact hG ((a ^ k : A) : G) (by rw [Subgroup.orderOf_coe, hord])

theorem no_orderOf_nine_psl2GF (n : ℕ) (hn : 1 ≤ n) (g : PSL2GF 3 n) : orderOf g ≠ 9 := by
  intro hg
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hp : IsPGroup 3 (Subgroup.zpowers g) :=
    IsPGroup.of_card (n := 2) (by rw [Nat.card_zpowers, hg]; norm_num)
  obtain ⟨T, hT⟩ := hp.exists_le_sylow
  have hgT : g ∈ (T : Subgroup (PSL2GF 3 n)) := hT (Subgroup.mem_zpowers g)
  have h3 : g ^ 3 = 1 := (psl2GF_sylow 3 n hn T).1.2 g hgT
  have := orderOf_dvd_of_pow_eq_one h3
  rw [hg] at this
  omega

theorem no_orderOf_nine_unitary {d : TauCeti.ValidLieTypeIndex} (hd : IsUnitaryIndex 3 d)
    [Finite (CatGroup d)] (g : CatGroup d) : orderOf g ≠ 9 := by
  intro hg
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hp : IsPGroup 3 (Subgroup.zpowers g) :=
    IsPGroup.of_card (n := 2) (by rw [Nat.card_zpowers, hg]; norm_num)
  obtain ⟨T, hT⟩ := hp.exists_le_sylow
  have hgT : g ∈ (T : Subgroup (CatGroup d)) := hT (Subgroup.mem_zpowers g)
  have h3 : g ^ 3 = 1 :=
    (kFactUnitarySylowStructure (CatGroup d) 3 d (by norm_num) hd ⟨MulEquiv.refl _⟩ T).2.2.1 g hgT
  have := orderOf_dvd_of_pow_eq_one h3
  rw [hg] at this
  omega

theorem linTwo_not_surjective_caseTwo : ∀ (d : TauCeti.ValidLieTypeIndex) (n : ℕ), 3 ≤ n →
    IsLinTwoIndex 3 n d → ∀ (A : Subgroup (CatGroup d)) (L : Type) [Group L],
      IsCaseTwoGroup 3 L → ∀ f : A →* L, ¬ Function.Surjective f := by
  intro d n hn hd A L _ hL f hf
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨e⟩ := nonempty_mulEquiv_psl2GF_of_isLinTwoIndex hd
  have : Finite (CatGroup d) := Finite.of_equiv _ e.symm.toEquiv
  refine not_surjective_of_no_orderOf_nine (G := CatGroup d) (fun g hg => ?_) A f hf
    (exists_orderOf_eq_nine_of_isCaseTwoGroup_three hL)
  exact no_orderOf_nine_psl2GF n (by omega) (e g) (by rw [MulEquiv.orderOf_eq]; exact hg)

theorem unitary_not_surjective_caseTwo : ∀ d : TauCeti.ValidLieTypeIndex, IsUnitaryIndex 3 d →
    2 ≤ d.1.fieldExponent → ∀ (A : Subgroup (CatGroup d)) (L : Type) [Group L],
      IsCaseTwoGroup 3 L → ∀ f : A →* L, ¬ Function.Surjective f := by
  intro d hd h2 A L _ hL f hf
  obtain ⟨-, -, -, K, _, _, J, -, -, -, ⟨e⟩⟩ :=
    UnitaryModel.exists_equiv_psu
      (UnitaryModel.statedClassicalModel hd ⟨MulEquiv.refl (CatGroup d)⟩)
  have : Finite (CatGroup d) := Finite.of_equiv _ e.symm.toEquiv
  exact not_surjective_of_no_orderOf_nine (G := CatGroup d) (no_orderOf_nine_unitary hd) A f hf
    (exists_orderOf_eq_nine_of_isCaseTwoGroup_three hL)

theorem kFactCaseTwoReeId_of_oneLieIdent (hId : KFactOneLieIdent) : KFactCaseTwoReeId :=
  kFactCaseTwoReeId_of_ident hId linTwo_not_surjective_caseTwo unitary_not_surjective_caseTwo

end CFSG.AGLEmbedding
