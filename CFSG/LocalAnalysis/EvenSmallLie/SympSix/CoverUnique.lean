module

public import CFSG.LocalAnalysis.EvenSmallLie.SympSix.CoverUniqueBound
public import CFSG.Sporadic.Schreier.Co3First

public section

namespace CFSG.EvenSmallLie.SympSix

open Subgroup CFSG.RankThree.PerfectCover CFSG.Sporadic.Schreier.Co3 CFSG.EvenSmallLie.Sp6

@[expose] noncomputable def co3MQuotHom
    {X : Type} [Group X] (e : X ≃* co3X36) : co3M →* X :=
  (co3MQuotEquiv.trans e.symm).toMonoidHom.comp (QuotientGroup.mk' (center co3M))

theorem co3MQuotHom_surjective
    {X : Type} [Group X] (e : X ≃* co3X36) :
    Function.Surjective (co3MQuotHom e) :=
  (co3MQuotEquiv.trans e.symm).surjective.comp (QuotientGroup.mk'_surjective _)

theorem co3MQuotHom_ker
    {X : Type} [Group X] (e : X ≃* co3X36) :
    (co3MQuotHom e).ker = center co3M := by
  ext x
  rw [MonoidHom.mem_ker, co3MQuotHom, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    MulEquiv.map_eq_one_iff, ← MonoidHom.mem_ker, QuotientGroup.ker_mk']

theorem nonempty_mulEquiv_co3M
    {X : Type} [Group X] (hX : CFSG.Blueprint.LieModel X .PSp 3 2 1)
    {E : Type*} [Group E] [Group.IsPerfect E] (q : E →* X) (hq : Function.Surjective q)
    (hker : q.ker ≤ center E) (h2 : Nat.card q.ker = 2) : Nonempty (co3M ≃* E) := by
  obtain ⟨e⟩ := nonempty_mulEquiv_co3X36 hX
  have hM := hopfLift_bijective hX (co3MQuotHom e) (co3MQuotHom_surjective e)
    (co3MQuotHom_ker e).le (by rw [co3MQuotHom_ker, card_co3M_center])
  exact ⟨(MulEquiv.ofBijective _ hM).symm.trans
    (MulEquiv.ofBijective _ (hopfLift_bijective hX q hq hker h2))⟩

theorem center_eq_zpowers_of_mulEquiv {G H : Type*} [Group G] [Group H] (θ : G ≃* H) {z : G}
    (hz : center G = zpowers z) : center H = zpowers (θ z) := by
  rw [← map_center_eq θ, hz]
  exact MonoidHom.map_zpowers θ.toMonoidHom z

theorem sp62_double_cover_unique
    (L : Type) [Group L] (hL : commutator L = ⊤)
    (hZ : Nat.card (center L) = 2) (hX : CFSG.Blueprint.LieModel (L ⧸ center L) .PSp 3 2 1) :
    ∃ θ : co3M ≃* L, center L = zpowers (θ co3ZM) := by
  have : Group.IsPerfect L := ⟨hL⟩
  obtain ⟨θ⟩ := nonempty_mulEquiv_co3M hX (QuotientGroup.mk' (center L))
    (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _).le
    (by rw [QuotientGroup.ker_mk', hZ])
  exact ⟨θ, center_eq_zpowers_of_mulEquiv θ co3M_center⟩

theorem sp62_double_cover_unique_of_mem_center
    (L : Type) [Group L] (hL : commutator L = ⊤)
    (hZ : Nat.card (center L) = 2) (hX : CFSG.Blueprint.LieModel (L ⧸ center L) .PSp 3 2 1)
    {t : L} (ht : t ∈ center L) (ht1 : t ≠ 1) : ∃ θ : co3M ≃* L, θ co3ZM = t := by
  obtain ⟨θ, hθ⟩ := sp62_double_cover_unique L hL hZ hX
  refine ⟨θ, ?_⟩
  have hord : orderOf (θ co3ZM) = 2 := by rw [MulEquiv.orderOf_eq, orderOf_co3ZM]
  rw [hθ] at ht
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 ht
  rw [← zpow_mod_orderOf, hord] at ht1 ⊢
  rcases Int.emod_two_eq_zero_or_one k with h | h
  · rw [Nat.cast_ofNat, h, zpow_zero] at ht1
    exact absurd rfl ht1
  · rw [Nat.cast_ofNat, h, zpow_one]

theorem multiplier_PSp_three_two_one
    (X : Type) [Group X]
    (hX : CFSG.Blueprint.LieModel X .PSp 3 2 1) :
    commutator X = ⊤ ∧ Nonempty (CFSG.Open.griessHopfMultiplier X ≃* Multiplicative (ZMod 2)) := by
  obtain ⟨hperf, -, -⟩ := perfect_and_hopfCover_card_le hX
  obtain ⟨e⟩ := nonempty_mulEquiv_co3X36 hX
  have hb := hopfLift_bijective hX (co3MQuotHom e) (co3MQuotHom_surjective e)
    (co3MQuotHom_ker e).le (by rw [co3MQuotHom_ker, card_co3M_center])
  have hU : Nat.card (HopfCover X) = 2903040 := by
    rw [Nat.card_congr (Equiv.ofBijective _ hb), card_co3M]
  have hM : Nat.card (hopfMultiplier X) = 2 := by
    have h1 := (hopfMultiplier X).card_eq_card_quotient_mul_card_subgroup
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective _
      hopfCoverMap_surjective).toEquiv, hU, card_of_lieModel hX] at h1
    omega
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact ⟨hperf.commutator_eq_top, ⟨(hopfMultiplierEquivGriess X).trans
    (mulEquivOfPrimeCardEq hM (by simp [Nat.card_eq_fintype_card]))⟩⟩

end CFSG.EvenSmallLie.SympSix
