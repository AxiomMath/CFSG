module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureTwoCoreGrowthTransfer
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CardSupOfDisjointNormalizer

public section

namespace CFSG.ProperTwoGeneratedCore.HighRankPair

open scoped Pointwise

variable {G : Type*} [Group G]

theorem sup_of_le_normalizer_of_inf_eq_bot {V P : Subgroup G}
    (hPV : P ≤ Subgroup.normalizer (V : Set G)) (hVP : V ⊓ P = ⊥) :
    ((V ⊔ P : Subgroup G) : Set G) = (V : Set G) * (P : Set G) ∧
      Nat.card (V ⊔ P : Subgroup G) = Nat.card V * Nat.card P ∧
      ∃ _ : (V.subgroupOf (V ⊔ P)).Normal,
        Nonempty (↥(V ⊔ P) ⧸ V.subgroupOf (V ⊔ P) ≃* P) := by
  have hdisj : Disjoint V P := disjoint_iff.mpr hVP
  refine ⟨Subgroup.coe_mul_of_right_le_normalizer_left V P hPV,
    CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer V P hPV hdisj, ?_⟩
  have key : ∃ _ : (V.subgroupOf (P ⊔ V)).Normal,
      Nonempty (↥(P ⊔ V) ⧸ V.subgroupOf (P ⊔ V) ≃* P) := by
    have hn : (V.subgroupOf (P ⊔ V)).Normal := Subgroup.normal_subgroupOf_sup_of_le_normalizer hPV
    refine ⟨hn, ⟨?_⟩⟩
    have : (V.subgroupOf P).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hPV
    have hbot : V.subgroupOf P = ⊥ := Subgroup.subgroupOf_eq_bot.mpr hdisj
    exact (QuotientGroup.quotientInfEquivProdNormalizerQuotient P V hPV).symm.trans
      ((QuotientGroup.quotientMulEquivOfEq hbot).trans QuotientGroup.quotientBot)
  rw [sup_comm] at key
  exact key

theorem card_sup_mul_card_inf_of_le_normalizer [Finite G] {A C : Subgroup G}
    (hC : C ≤ Subgroup.normalizer (A : Set G)) :
    Nat.card (C ⊔ A : Subgroup G) * Nat.card (A ⊓ C : Subgroup G) = Nat.card A * Nat.card C := by
  have := Subgroup.normal_subgroupOf_of_le_normalizer hC
  have := Subgroup.normal_subgroupOf_sup_of_le_normalizer hC
  have e := QuotientGroup.quotientInfEquivProdNormalizerQuotient C A hC
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (A.subgroupOf C)
  have h2 := Subgroup.card_eq_card_quotient_mul_card_subgroup (A.subgroupOf (C ⊔ A))
  have h3 : Nat.card (A.subgroupOf (C ⊔ A)) = Nat.card A :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_sup_right).toEquiv
  have h4 : Nat.card (A.subgroupOf C) = Nat.card (A ⊓ C : Subgroup G) := by
    rw [← Subgroup.inf_subgroupOf_right]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv
  have h5 := Nat.card_congr e.toEquiv
  rw [h2, h3, ← h5, ← h4, mul_comm (Nat.card _) (Nat.card A), mul_assoc, ← h1]

theorem exists_sylow_of_le_of_card_eq [Finite G] {N S : Subgroup G}
    (hlift : ∀ T : Sylow 2 N, ∃ T' : Sylow 2 G,
      (T' : Subgroup G) = (T : Subgroup N).map N.subtype)
    (hSN : S ≤ N) (hcard : Nat.card S = 2 ^ (Nat.card N).factorization 2) :
    ∃ S' : Sylow 2 G, (S' : Subgroup G) = S := by
  have hcard' : Nat.card (S.subgroupOf N) = 2 ^ (Nat.card N).factorization 2 := by
    rw [← hcard]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSN).toEquiv
  obtain ⟨T', hT'⟩ := hlift (Sylow.ofCard _ hcard')
  refine ⟨T', ?_⟩
  rw [hT', Sylow.coe_ofCard, Subgroup.map_subgroupOf_eq_of_le hSN]

theorem exists_conj_mem_of_isCyclic_sylow_quotient [Finite G] (hsimple : IsSimpleGroup G)
    (hnonab : ∃ a b : G, a * b ≠ b * a) (S : Sylow 2 G) {V : Subgroup G}
    [(V.subgroupOf S).Normal] [IsCyclic (↥(S : Subgroup G) ⧸ V.subgroupOf S)]
    {u : G} (huS : u ∈ (S : Subgroup G)) (huV : u ∉ V) (hu : orderOf u = 2) :
    ∃ g : G, g⁻¹ * u * g ∈ V := by
  by_contra hcon
  push Not at hcon
  have hx : (⟨u, huS⟩ : (S : Subgroup G)) ∉ V.subgroupOf S := fun h =>
    huV (Subgroup.mem_subgroupOf.mp h)
  have hxorder : orderOf (⟨u, huS⟩ : (S : Subgroup G)) = 2 := by
    rw [← Subgroup.orderOf_coe]
    exact hu
  obtain ⟨-, -, -, -, -, -, D, hDn, hDi⟩ :=
    CFSG.ShultStronglyClosedTI.TwoCoreGrowth.thompson_cyclic_two_quotient_transfer S
      (V.subgroupOf S) ⟨u, huS⟩ hx hxorder fun g hmem h => hcon g (Subgroup.mem_subgroupOf.mp h)
  have := hsimple
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal D with rfl | rfl
  · rw [Subgroup.index_bot] at hDi
    let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have : IsCyclic G := isCyclic_of_prime_card hDi
    obtain ⟨a, b, hab⟩ := hnonab
    exact hab (mul_comm' a b)
  · rw [Subgroup.index_top] at hDi
    exact absurd hDi (by norm_num)

theorem mem_sylow_of_central_involution [Finite G] {A : Subgroup G} {u : G} (huA : u ∈ A)
    (hAu : A ≤ Subgroup.centralizer ({u} : Set G)) (hu : orderOf u = 2) (P : Sylow 2 A) :
    u ∈ (P : Subgroup A).map A.subtype := by
  have hnormal : (Subgroup.zpowers (⟨u, huA⟩ : A)).Normal := by
    constructor
    intro x hx g
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    have hg : g * ⟨u, huA⟩ = ⟨u, huA⟩ * g :=
      Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp (hAu g.2))
    rw [((show Commute g ⟨u, huA⟩ from hg).zpow_right k).eq, mul_inv_cancel_right]
    exact Subgroup.zpow_mem_zpowers _ k
  have hp : IsPGroup 2 (Subgroup.zpowers (⟨u, huA⟩ : A)) := by
    apply IsPGroup.of_card (n := 1)
    rw [Nat.card_zpowers, pow_one, ← Subgroup.orderOf_coe]
    exact hu
  have hle := hp.le_sylow_of_normal P
  exact ⟨⟨u, huA⟩, hle (Subgroup.mem_zpowers _), rfl⟩

end CFSG.ProperTwoGeneratedCore.HighRankPair
