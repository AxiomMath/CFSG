module

public import CFSG.CGT.Foote81L6.Bridge.Embed
public import CFSG.Blueprint.Catalog

public section

namespace CFSG.CGT.Foote81L6.Bridge

open CFSG.Open

theorem nonempty_mulEquiv_sModel {K : Type} [Field K] [Finite K] (hq : Nat.card K % 4 = 3)
    (P : Sylow 2 (StatedProj (StatedSL 6 K))) :
    Nonempty (↥(P : Subgroup (StatedProj (StatedSL 6 K))) ≃*
      SModel ((Nat.card K ^ 2 - 1).factorization 2)) := by
  obtain ⟨-, -, -, hn3⟩ := exists_odd_q_add_one hq
  obtain ⟨D⟩ := exists_gl2Data hq
  have hcard : Nat.card D.toSL.range = 2 ^ (Nat.card (StatedSL 6 K)).factorization 2 := by
    rw [← Nat.card_congr (MonoidHom.ofInjective D.toSL_injective).toEquiv, card_P,
      factorization_card_statedSL_six K hq]
  let Q₀ : Sylow 2 (StatedSL 6 K) := Sylow.ofCard _ hcard
  let Q : Sylow 2 (StatedProj (StatedSL 6 K)) :=
    Q₀.mapSurjective (QuotientGroup.mk'_surjective _)
  have hQ : (Q : Subgroup (StatedProj (StatedSL 6 K))) = D.toProj.range := by
    change D.toSL.range.map (QuotientGroup.mk' _) = _
    rw [MonoidHom.map_range]
    rfl
  exact ⟨(Sylow.equiv P Q).trans ((MulEquiv.subgroupCongr hQ).trans
    ((QuotientGroup.quotientKerEquivRange D.toProj).symm.trans
      (QuotientGroup.quotientMulEquivOfEq (D.ker_toProj hn3))))⟩

theorem exists_mulEquiv_sModel {H : Type} [Group H] (S : Sylow 2 H)
    (hS : ∃ (p f : ℕ) (L : Type) (_ : Group L), p.Prime ∧ 0 < f ∧ p ^ f % 4 = 3 ∧
      CFSG.Blueprint.LieModel L .PSL 6 p f ∧ ∃ P : Sylow 2 L, Nonempty (↥S ≃* ↥P)) :
    ∃ n : ℕ, 3 ≤ n ∧ Nonempty (↥(S : Subgroup H) ≃* SModel n) := by
  obtain ⟨p, f, L, _, -, -, hq, hL, P, ⟨eSP⟩⟩ := hS
  obtain ⟨-, K, _, _, hK, ⟨eL⟩⟩ := hL.statedClassicalModel_of_ne_zero (by norm_num)
  have hqK : Nat.card K % 4 = 3 := by rw [hK]; exact hq
  obtain ⟨-, -, -, hn3⟩ := exists_odd_q_add_one hqK
  have : Finite L := Finite.of_equiv _ eL.symm.toEquiv
  let P' : Sylow 2 (StatedProj (StatedSL 6 K)) :=
    P.mapSurjective (f := eL.toMonoidHom) eL.surjective
  have eP : ↥(P : Subgroup L) ≃* ↥(P' : Subgroup (StatedProj (StatedSL 6 K))) :=
    ((P : Subgroup L).equivMapOfInjective eL.toMonoidHom eL.injective).trans
      (MulEquiv.subgroupCongr (Sylow.coe_mapSurjective _ _).symm)
  obtain ⟨eM⟩ := nonempty_mulEquiv_sModel hqK P'
  exact ⟨_, hn3, ⟨(eSP.trans eP).trans eM⟩⟩

end CFSG.CGT.Foote81L6.Bridge
