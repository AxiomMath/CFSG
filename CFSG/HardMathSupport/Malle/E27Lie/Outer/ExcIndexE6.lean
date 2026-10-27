module

public import CFSG.HardMathSupport.Malle.E27Lie.Outer.ExcIndex
public import CFSG.HardMathSupport.Lang.E27.E6Field
public import CFSG.HardMathSupport.Lang.E27.TwistedE6Field

public section

namespace CFSG.HardMathSupport.Malle.E27Lie

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley TauCeti
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.OuterAutomorphisms (inner)

section


theorem e27LieOuterAutAt_E6 (hdiag : CFSG.HardMathSupport.Lang.E27.E6InnerDiagLowerBound) :
    E27LieOuterAutAt (fun i => ∃ q, i = .E6 q) := by
  rintro K _ _ d hd ⟨e⟩ - u hu3 hout - hQ -
  obtain ⟨i, hv⟩ := d
  obtain ⟨q, rfl⟩ := hd
  have hm := untwistedModel_of_bridgeAll
    (CFSG.TauCetiBridge.Even.chevalleyBridgesAll).e6 q hv e
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  refine false_of_dvd_twentySeven u hQ (twentySeven_dvd_fixedSubgroup_of_untwistedModel ?_ hm u hu3
    hout)
  intro F _ hF α h3' hα
  exact CFSG.HardMathSupport.Lang.E27.twentySeven_dvd_fixedSubgroup_E6_of_innerDiag hdiag
    q.exponent_pos F hF α h3' hα

theorem e27LieOuterAutAt_twistedE6
    (hdiag : CFSG.HardMathSupport.Lang.E27.TwistedE6InnerDiagLowerBound) :
    E27LieOuterAutAt (fun i => ∃ q, i = .twistedE6 q) := by
  rintro K _ _ d hd ⟨e⟩ - u hu3 hout - hQ -
  obtain ⟨i, hv⟩ := d
  obtain ⟨q, rfl⟩ := hd
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  have hcard : Nat.card (GaloisField q.p (q.exponent * 2)) = q.card ^ 2 := by
    rw [GaloisField.card q.p (q.exponent * 2) (by have := q.exponent_pos; omega),
      TauCeti.PrimePower.card_def, pow_mul]
  have hinj := RingHom.injective (iterateFrobenius (GaloisField q.p (q.exponent * 2)) q.p
    q.exponent)
  let σ : GaloisField q.p (q.exponent * 2) ≃+* GaloisField q.p (q.exponent * 2) :=
    RingEquiv.ofBijective (iterateFrobenius (GaloisField q.p (q.exponent * 2)) q.p q.exponent)
      ⟨hinj, Finite.surjective_of_injective hinj⟩
  have hσ : ∀ c, σ c = c ^ q.card := fun c => by
    show iterateFrobenius (GaloisField q.p (q.exponent * 2)) q.p q.exponent c = _
    rw [iterateFrobenius_def, TauCeti.PrimePower.card_def]
  obtain ⟨br⟩ := (CFSG.TauCetiBridge.Even.chevalleyBridgesAll).twistedE6 q hv
    (GaloisField q.p (q.exponent * 2)) hcard σ.toRingHom hσ
  have hK : Nat.card (GaloisField q.p (q.exponent * 2)) =
      (q.p ^ q.exponent) ^ TwistTag.E6.order := by
    rw [hcard, TauCeti.PrimePower.card_def]
    rfl
  have hσ' : ∀ c, σ.toRingHom c = c ^ (q.p ^ q.exponent) := fun c => by
    rw [← TauCeti.PrimePower.card_def]; exact hσ c
  have hcl := (finite_fixed_root_group_perfect TwistTag.E6 q.prime_p q.exponent_pos
    (GaloisField q.p (q.exponent * 2)) hK σ.toRingHom hσ').2.2.1
  have hZD : Subgroup.center ↥⁅twistedFixedGroup TwistTag.E6 (GaloisField q.p (q.exponent * 2))
      σ.toRingHom, twistedFixedGroup TwistTag.E6 (GaloisField q.p (q.exponent * 2))
        σ.toRingHom⁆ = ⊥ := by
    rw [hcl]
    exact center_graphFixedRootGroup_eq_bot σ.surjective
  let θ : K ≃* twistedE6RootGroup (GaloisField q.p (q.exponent * 2)) σ :=
    (e.trans br.symm).trans (((MulEquiv.subgroupCongr hcl).symm.trans
      ((QuotientGroup.quotientMulEquivOfEq hZD).trans QuotientGroup.quotientBot).symm).symm)
  refine false_of_dvd_twentySeven u hQ ?_
  rw [← CFSG.HardMathSupport.Lang.Coordinator.card_fixedSubgroup_congr θ u]
  have hK2 : Nat.card (GaloisField q.p (q.exponent * 2)) = (q.p ^ q.exponent) ^ 2 := by
    rw [hcard, TauCeti.PrimePower.card_def]
  refine CFSG.HardMathSupport.Lang.E27.twentySeven_dvd_fixedSubgroup_twistedE6_of_innerDiag hdiag
    q.prime_p q.exponent_pos _ hK2 σ (fun c => hσ' c) (MulAut.congr θ u)
    (by rw [← map_pow, hu3, map_one]) fun hin => ?_
  obtain ⟨k, hk⟩ := (CFSG.HardMathSupport.Lang.Coordinator.congr_mem_inner_iff θ u).1 hin
  exact hout k hk.symm

end

end CFSG.HardMathSupport.Malle.E27Lie
