module

public import CFSG.LocalAnalysis.ComponentClassification.GSYard02Basic
public import CFSG.GH74.Filter.Final
public import CFSG.LocalAnalysis.ComponentClassification.CTUSol76SigGoodJoin

public section

namespace CFSG.ComponentClassification.Sol76.Sig.GSYard02

open CFSG Subgroup

@[expose] def SimpleCase : Prop :=
  ∀ (X : Type) [Group X] [Finite X], IsSimpleGroup X → (∃ a b : X, a * b ≠ b * a) →
    3 ≤ Open.twoRank X → GH74.Gen4 X → GH74.GH74Conclusion X → SylowFourJoined X

@[expose] def CoverCase : Prop :=
  ∀ (Q : Type) [Group Q] [Finite Q], IsQuasisimple Q → center Q ≠ ⊥ →
    IsPGroup 2 (center Q) → IsCyclic (center Q) → 3 ≤ CFSG.pRank 2 Q → GH74.Gen4 Q →
    Blueprint.Catalog (Q ⧸ center Q) → SylowFourJoined Q

theorem center_isPGroup_two_of_pPrimeCore_eq_bot {Q : Type} [Group Q] [Finite Q]
    (hO : pPrimeCore 2 Q = ⊥) : IsPGroup 2 (center Q) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [IsPGroup.iff_card]
  refine ⟨_, Nat.eq_prime_pow_of_unique_prime_dvd Nat.card_pos.ne' fun {d} hd hdvd => ?_⟩
  by_contra hd2
  have : Fact d.Prime := ⟨hd⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := center Q) d hdvd
  have hK : zpowers (x : Q) ≤ center Q := by
    rw [zpowers_le]
    exact x.2
  have hKn : (zpowers (x : Q)).Normal := normal_of_le_center hK
  have hcard : Nat.card (zpowers (x : Q)) = d := by
    rw [Nat.card_zpowers, Subgroup.orderOf_coe, hx]
  have hcop : Nat.Coprime 2 (Nat.card (zpowers (x : Q))) := by
    rw [hcard]
    exact (Nat.coprime_primes Nat.prime_two hd).mpr (Ne.symm hd2)
  have hbot : zpowers (x : Q) = ⊥ := pPrimeCore_eq_bot_iff.mp hO _ hKn hcop
  have hx1 : (x : Q) = 1 := by
    rwa [zpowers_eq_bot] at hbot
  have hx1' : x = 1 := Subtype.ext hx1
  rw [hx1', orderOf_one] at hx
  exact hd.one_lt.ne hx

theorem center_isCyclic_of_no_kleinFour {Q : Type} [Group Q] [Finite Q]
    (h2 : IsPGroup 2 (center Q)) (hZ : ∀ Z : Subgroup Q, Z ≤ center Q → ¬ IsKleinFour Z) :
    IsCyclic (center Q) := by
  letI : CommGroup (center Q) :=
    { (inferInstance : Group (center Q)) with
      mul_comm := fun a b => Subtype.ext (mem_center_iff.mp b.2 a) }
  refine DisconnectedInvolutionGraph.Helpers.rank_one_abelian_two_group_cyclic (center Q) h2 ?_
  rintro ⟨a, ha⟩ ⟨b, hb⟩ -
  by_contra hne
  have hne' : (a : Q) ≠ (b : Q) := fun h => hne (Subtype.ext (Subtype.ext h))
  have hinv : ∀ c : center Q, orderOf c = 2 → BenderSuzuki.PFAppendixIII.IsInvolution (c : Q) :=
    fun c hc => by
      have h1 : orderOf (c : Q) = 2 := by rw [Subgroup.orderOf_coe]; exact hc
      exact ⟨(orderOf_eq_prime_iff.mp h1).2, (orderOf_eq_prime_iff.mp h1).1⟩
  obtain ⟨V, hVc, hV, -, -⟩ := GorensteinWalter.exists_kleinFour_of_commuting_involutions_le
    (center Q) (a : Q) (b : Q) (hinv a ha) (hinv b hb) hne'
    (mem_center_iff.mp b.2 (a : Q)) a.2 b.2
  exact hZ V hVc hV

theorem quasisimpleSylowFourJoinedSCN_of_cases
    (hS : SimpleCase) (hC : CoverCase) : QuasisimpleSylowFourJoinedSCN := by
  intro Q _ _ hQ hO hcat hr hZ S _ hgen E F hE hES hF hFS
  have hgen4 : GH74.Gen4 Q := hgen
  have h2 : IsPGroup 2 (center Q) := center_isPGroup_two_of_pPrimeCore_eq_bot hO
  by_cases hz : center Q = ⊥
  · obtain ⟨-, hsimp, hnonab⟩ := hQ
    let e : Q ≃* Q ⧸ center Q :=
      QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq hz.symm)
    have hsimpQ : IsSimpleGroup Q := (MulEquiv.isSimpleGroup_congr e).mpr hsimp
    have hnonabQ : ∃ a b : Q, a * b ≠ b * a := by
      obtain ⟨a, b, hab⟩ := hnonab
      obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
      obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
      exact ⟨a, b, fun h => hab (by rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, h])⟩
    have hr3 : 3 ≤ Open.twoRank Q := by
      show 3 ≤ Open.pRank 2 (⊤ : Subgroup Q)
      rw [← SectionRank.pRank_eq_open_pRank_top]
      exact hr
    have hGH : GH74.GH74Conclusion Q :=
      GH74.Filter.filter Q (SectionRank.catalog_of_mulEquiv e hcat) hnonabQ hr3 hgen4
    exact hS Q hsimpQ hnonabQ hr3 hgen4 hGH S E F hE hES hF hFS
  · exact hC Q hQ hz h2 (center_isCyclic_of_no_kleinFour h2 hZ) hr hgen4 hcat S E F hE hES hF hFS

end CFSG.ComponentClassification.Sol76.Sig.GSYard02
