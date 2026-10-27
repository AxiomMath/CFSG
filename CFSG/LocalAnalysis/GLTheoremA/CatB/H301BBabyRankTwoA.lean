module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.BabyCoverProved
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1016M3TwE6Rank
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1016M5AssemblyInv

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H301B

open CFSG.Open CFSG.Blueprint CFSG.Monster.GMS CFSG.Monster.B.TwoA.Amalgam
  CFSG.LieType.Chevalley.C2E6Std Subgroup

attribute [local irreducible] Matrix.instHMulOfFintypeOfMulOfAddCommMonoid


theorem card_le_of_babyInv_zero {u : NativeSporadic.B} (hu : BabyInv 0 u)
    (E : Subgroup NativeSporadic.B) (hEu : E ≤ centralizer ({u} : Set NativeSporadic.B))
    (hE : IsElemAbelian 3 E) : Nat.card E ≤ 3 ^ 5 := by
  obtain ⟨Ψ⟩ := CFSG.EvenSporadicStandard.Induction.Hyp.babyCover_centralizerEquiv_native hu.1
    (by rw [hu.2]; unfold ordTwistedE6; norm_num [babyCentOrder])
  obtain ⟨hidx, -, -, -, hc2, ⟨e⟩, -⟩ := short_F4_derived_standard_perfect_cover
  have hE₁ : IsElemAbelian 3 ((E.subgroupOf (centralizer ({u} : Set NativeSporadic.B))).map
      Ψ.toMonoidHom) := (hE.subgroupOf _).map _
  have hE₁D : (E.subgroupOf (centralizer ({u} : Set NativeSporadic.B))).map Ψ.toMonoidHom ≤
      commutator ↥Eam := by
    intro x hx
    have h4 : (x ^ 2) ^ 2 = x := by
      rw [← pow_mul, show 2 * 2 = 3 + 1 from rfl, pow_succ, hE₁.2 x hx, one_mul]
    rw [← h4]
    exact (commutator ↥Eam).pow_mem (sq_mem_of_index_two hidx x) 2
  have hc : IsPGroup 2 (zpowers cE') := IsPGroup.of_card (n := 1) (by rw [hc2, pow_one])
  have hK : ∀ F : Subgroup ↥stdGroup, IsElemAbelian 3 F → Nat.card F ≤ 3 ^ 5 := fun F hF =>
    H1017.H1016M3.card_le_of_lieModel_twistedE6_two
      ((CFSG.EvenSmallLie.TwoE6.lieModel_twistedE6_two_iff _).2 ⟨MulEquiv.refl _⟩) F hF
  have h := H1017.H1016M5.card_le_of_le_quot Nat.prime_three (by norm_num) hc.comap_subtype hK e
    hE₁D hE₁
  rwa [card_map_of_injective Ψ.injective, Nat.card_congr (subgroupOfEquivOfLe hEu).toEquiv] at h

end CFSG.LocalAnalysis.GLTheoremA.H301B
