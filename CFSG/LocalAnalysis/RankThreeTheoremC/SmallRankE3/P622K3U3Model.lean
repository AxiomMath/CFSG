module

public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.UnitaryTauCeti
public import CFSG.RankThree.SubgroupLists.UnitaryThreeFamily
public import CFSG.LieType.Steinberg.CentralExt.UnitaryField
public import CFSG.GroupTheory.ABGLocalTools.PStabilityQSL2

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3

open scoped MatrixGroups

theorem exists_sl2_embedding_of_twistedA2 {X : Type} [Group X] {q : TauCeti.PrimePower}
    (hv : (TauCeti.LieTypeIndex.twistedA 2 q).Valid)
    (e : X ≃* TauCeti.ValidLieTypeIndex.Group ⟨TauCeti.LieTypeIndex.twistedA 2 q, hv⟩) :
    ∃ (F₀ : Type) (_ : Field F₀) (_ : Finite F₀), Nat.card F₀ = q.p ^ q.exponent ∧
      ∃ ι : SL(2, F₀) →* X, Function.Injective ι := by
  have hmodel := CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA 2 q hv e
  unfold CFSG.Open.StatedClassicalModel at hmodel
  obtain ⟨-, K, hKf, hKfin, hK, ⟨φ⟩⟩ := hmodel
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  have hchar : CharP K q.p :=
    CFSG.ABGLocalTools.SL2Facts.charP_of_card_eq_prime_pow (n := q.exponent * 2) q.prime_p
      (by rw [hK, ← pow_mul])
  obtain ⟨ψ⟩ := CFSG.RankThree.SubgroupLists.nonempty_sl2_mulEquiv_statedSU_two
    (K := K) (r := q.p) (f := q.exponent) hK
  obtain ⟨χ⟩ := CFSG.RankThree.SubgroupLists.nonempty_mulEquiv_leviPSU3 (K := K)
    (q.p ^ q.exponent) (Nat.one_le_pow _ _ q.prime_p.pos)
  have hcard : Nat.card (CFSG.LieType.Steinberg.fixedSubfield K q.p q.exponent) =
      q.p ^ q.exponent :=
    CFSG.LieType.Steinberg.card_fixedSubfield hK
  refine ⟨CFSG.LieType.Steinberg.fixedSubfield K q.p q.exponent, inferInstance, inferInstance,
    hcard, ?_⟩
  let L := CFSG.RankThree.SubgroupLists.leviPSU3 (K := K) (q.p ^ q.exponent)
  have hL : Function.Injective (φ.symm.toMonoidHom.comp L.subtype) :=
    φ.symm.injective.comp Subtype.val_injective
  have hψχ : Function.Injective (χ.toMonoidHom.comp ψ.toMonoidHom) :=
    χ.injective.comp ψ.injective
  exact ⟨(φ.symm.toMonoidHom.comp L.subtype).comp (χ.toMonoidHom.comp ψ.toMonoidHom),
    hL.comp hψχ⟩

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3
