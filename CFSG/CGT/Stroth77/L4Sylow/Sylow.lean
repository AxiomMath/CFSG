module

public import CFSG.CGT.Stroth77.L4Sylow.Arith
public import CFSG.CGT.Stroth77.L4Sylow.Center
public import CFSG.Blueprint.Catalog

public section

namespace CFSG.CGT.Stroth77.L4Sylow

theorem exists_sylow_quotient_eq_range {p : ℕ} [Fact p.Prime] {G H : Type*} [Group G]
    [Group H] [Finite G] (N : Subgroup G) [N.Normal] (φ : H →* G) (hφ : Function.Injective φ)
    (hH : Nat.card H = p ^ (Nat.card G).factorization p) :
    ∃ Q : Sylow p (G ⧸ N), (Q : Subgroup (G ⧸ N)) = ((QuotientGroup.mk' N).comp φ).range := by
  have hR : Nat.card φ.range = p ^ (Nat.card G).factorization p := by
    rw [← hH]
    exact Nat.card_congr (MonoidHom.ofInjective hφ).toEquiv.symm
  refine ⟨(Sylow.ofCard φ.range hR).mapSurjective (QuotientGroup.mk'_surjective N), ?_⟩
  change φ.range.map (QuotientGroup.mk' N) = _
  rw [MonoidHom.map_range]

theorem nonempty_sylow_quotient_mulEquiv {p : ℕ} [Fact p.Prime] {G H : Type*} [Group G]
    [Group H] [Finite G] {N : Subgroup G} [N.Normal] (φ : H →* G) (hφ : Function.Injective φ)
    (hH : Nat.card H = p ^ (Nat.card G).factorization p) {Z : Subgroup H} [Z.Normal]
    (hZ : ((QuotientGroup.mk' N).comp φ).ker = Z) (P : Sylow p (G ⧸ N)) :
    Nonempty (↥(P : Subgroup (G ⧸ N)) ≃* H ⧸ Z) := by
  obtain ⟨Q, hQ⟩ := exists_sylow_quotient_eq_range N φ hφ hH
  exact ⟨(Sylow.equiv P Q).trans ((MulEquiv.subgroupCongr hQ).trans
    ((QuotientGroup.quotientKerEquivRange _).symm.trans
      (QuotientGroup.quotientMulEquivOfEq hZ)))⟩

open CFSG.Open

theorem nonempty_mulEquiv_l4Model {K : Type} [Field K] [Finite K] (hq : Nat.card K % 4 = 1)
    (P : Sylow 2 (StatedProj (StatedSL 4 K))) :
    Nonempty (↥(P : Subgroup (StatedProj (StatedSL 4 K))) ≃*
      L4Model ((Nat.card K - 1).factorization 2)) := by
  obtain ⟨-, -, -, hn2⟩ := exists_odd_q_sub_one Finite.one_lt_card hq
  obtain ⟨D⟩ := exists_l4Data_of_dvd (K := K) (Nat.ordProj_dvd (Nat.card K - 1) 2)
  exact nonempty_sylow_quotient_mulEquiv (D.toSL (by omega)) (D.toSL_injective _)
    (by rw [card_L4P, factorization_card_statedSL_four K hq]) (D.ker_toProj (by omega) hn2) P

theorem nonempty_mulEquiv_l4Model_of_lieModel {L : Type} [Group L] {p f : ℕ}
    (hq : p ^ f % 4 = 1) (hL : CFSG.Blueprint.LieModel L .PSL 4 p f) (P : Sylow 2 L) :
    Nonempty (↥(P : Subgroup L) ≃* L4Model ((p ^ f - 1).factorization 2)) := by
  obtain ⟨-, K, _, _, hK, ⟨eL⟩⟩ := hL.statedClassicalModel_of_ne_zero (by norm_num)
  have hqK : Nat.card K % 4 = 1 := by rw [hK]; exact hq
  have : Finite L := Finite.of_equiv _ eL.symm.toEquiv
  let P' : Sylow 2 (StatedProj (StatedSL 4 K)) :=
    P.mapSurjective (f := eL.toMonoidHom) eL.surjective
  have eP : ↥(P : Subgroup L) ≃* ↥(P' : Subgroup (StatedProj (StatedSL 4 K))) :=
    ((P : Subgroup L).equivMapOfInjective eL.toMonoidHom eL.injective).trans
      (MulEquiv.subgroupCongr (Sylow.coe_mapSurjective _ _).symm)
  obtain ⟨eM⟩ := nonempty_mulEquiv_l4Model hqK P'
  rw [← hK]
  exact ⟨eP.trans eM⟩

end CFSG.CGT.Stroth77.L4Sylow
