module

public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoDefs
import CFSG.RankThree.PartOne.K159.AutSzIso
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.UnitaryModel
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.Unitary

public section

namespace CFSG.AGLEmbedding

theorem exists_orderOf_eq_of_surjective {G L : Type*} [Group G] [Finite G] [Group L]
    (A : Subgroup G) (f : A →* L) (hf : Function.Surjective f) {n : ℕ} {x : L}
    (hx : orderOf x = n) : ∃ g : G, orderOf g = n := by
  obtain ⟨a, rfl⟩ := hf x
  have hdvd : n ∣ orderOf a := hx ▸ orderOf_map_dvd f a
  obtain ⟨k, hk⟩ := hdvd
  have hpos : 0 < orderOf a := orderOf_pos a
  have hk0 : k ≠ 0 := by
    rintro rfl
    omega
  have hkdvd : k ∣ orderOf a := ⟨n, by rw [hk, mul_comm]⟩
  have hord : orderOf (a ^ k) = n := by
    rw [orderOf_pow_of_dvd hk0 hkdvd, hk]
    exact Nat.mul_div_cancel n (Nat.pos_of_ne_zero hk0)
  exact ⟨((a ^ k : A) : G), by rw [Subgroup.orderOf_coe, hord]⟩

theorem exists_orderOf_eq_twentyFive_of_isCaseTwoGroup_five
    {L : Type} [Group L]
    (hL : IsCaseTwoGroup 5 L) : ∃ x : L, orderOf x = 25 := by
  obtain ⟨⟨x, hv⟩, hd, ⟨e⟩⟩ := hL
  rcases hd with ⟨h53, -⟩ | ⟨-, hs⟩
  · omega
  · obtain rfl : x = TauCeti.LieTypeIndex.suzuki 2 := hs
    have hS := CFSG.RankThree.PartOne.K159.SzAbs.szSylow_of_isoLie (S := L) ⟨hv, ⟨e⟩⟩
    have hfin : Finite L := Nat.finite_of_card_ne_zero (by rw [hS.card]; norm_num)
    have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
    obtain ⟨T⟩ : Nonempty (Sylow 5 L) := inferInstance
    have hT : Nat.card T = 25 := by
      rw [Sylow.card_eq_multiplicity, hS.card, CFSG.RankThree.PartOne.K159.SzAbs.factorization_five]
      norm_num
    have hcyc : IsCyclic T := hS.cyclic T
    obtain ⟨g, hg⟩ := hcyc.exists_generator
    refine ⟨(g : L), ?_⟩
    rw [Subgroup.orderOf_coe, orderOf_eq_card_of_forall_mem_zpowers hg, hT]

theorem no_orderOf_twentyFive_psl2GF [Fact (Nat.Prime 5)] (n : ℕ) (hn : 1 ≤ n)
    (g : PSL2GF 5 n) : orderOf g ≠ 25 := by
  intro hg
  have hp : IsPGroup 5 (Subgroup.zpowers g) :=
    IsPGroup.of_card (n := 2) (by rw [Nat.card_zpowers, hg]; norm_num)
  obtain ⟨T, hT⟩ := hp.exists_le_sylow
  have hgT : g ∈ (T : Subgroup (PSL2GF 5 n)) := hT (Subgroup.mem_zpowers g)
  have h5 : g ^ 5 = 1 := (psl2GF_sylow 5 n hn T).1.2 g hgT
  have := orderOf_dvd_of_pow_eq_one h5
  rw [hg] at this
  omega

theorem no_orderOf_twentyFive_unitary {d : TauCeti.ValidLieTypeIndex} (hd : IsUnitaryIndex 5 d)
    [Finite (CatGroup d)] (g : CatGroup d) : orderOf g ≠ 25 := by
  intro hg
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hp : IsPGroup 5 (Subgroup.zpowers g) :=
    IsPGroup.of_card (n := 2) (by rw [Nat.card_zpowers, hg]; norm_num)
  obtain ⟨T, hT⟩ := hp.exists_le_sylow
  have hgT : g ∈ (T : Subgroup (CatGroup d)) := hT (Subgroup.mem_zpowers g)
  have h5 : g ^ 5 = 1 :=
    (kFactUnitarySylowStructure (CatGroup d) 5 d (by norm_num) hd ⟨MulEquiv.refl _⟩ T).2.2.1 g hgT
  have := orderOf_dvd_of_pow_eq_one h5
  rw [hg] at this
  omega

theorem linTwo_not_surjective_caseTwo_five :
    ∀ (d : TauCeti.ValidLieTypeIndex) (n : ℕ), 3 ≤ n → IsLinTwoIndex 5 n d →
      ∀ (A : Subgroup (CatGroup d)) (L : Type) [Group L], IsCaseTwoGroup 5 L →
        ∀ f : A →* L, ¬ Function.Surjective f := by
  intro d n hn hd A L _ hL f hf
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨e⟩ := nonempty_mulEquiv_psl2GF_of_isLinTwoIndex hd
  have : Finite (CatGroup d) := Finite.of_equiv _ e.symm.toEquiv
  obtain ⟨x, hx⟩ := exists_orderOf_eq_twentyFive_of_isCaseTwoGroup_five hL
  obtain ⟨g, hg⟩ := exists_orderOf_eq_of_surjective A f hf hx
  exact no_orderOf_twentyFive_psl2GF n (by omega) (e g) (by rw [MulEquiv.orderOf_eq]; exact hg)

theorem unitary_not_surjective_caseTwo_five :
    ∀ d : TauCeti.ValidLieTypeIndex, IsUnitaryIndex 5 d → 2 ≤ d.1.fieldExponent →
      ∀ (A : Subgroup (CatGroup d)) (L : Type) [Group L], IsCaseTwoGroup 5 L →
        ∀ f : A →* L, ¬ Function.Surjective f := by
  intro d hd h2 A L _ hL f hf
  obtain ⟨-, -, -, K, _, _, J, -, -, -, ⟨e⟩⟩ :=
    UnitaryModel.exists_equiv_psu
      (UnitaryModel.statedClassicalModel hd ⟨MulEquiv.refl (CatGroup d)⟩)
  have : Finite (CatGroup d) := Finite.of_equiv _ e.symm.toEquiv
  obtain ⟨x, hx⟩ := exists_orderOf_eq_twentyFive_of_isCaseTwoGroup_five hL
  obtain ⟨g, hg⟩ := exists_orderOf_eq_of_surjective A f hf hx
  exact no_orderOf_twentyFive_unitary hd g hg

end CFSG.AGLEmbedding
