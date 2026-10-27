module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1420CoreDefs
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1420SporArith
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1420SporGrp
public import CFSG.HardMathSupport.Solomon.Coordinator.B3SporGen

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H1420

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.HardMathSupport.Timmesfeld.Coordinator CFSG.ComponentClassification.OuterAutomorphisms

private theorem prime_mul_dvd_sporOrd {S : Type} [Group S] [Finite S]
    (hOrd : SporadicOrdersTable) (hOut : SporadicOuterLeTwo) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {t : TauCeti.SporadicName} (e : S ≃* (TauCeti.CFSGIndex.sporadic t).Group)
    (hS : IsSimpleGroup S) (hnab : ∃ a b : S, a * b ≠ b * a) {β : MulAut S} (hβp : β ^ p = 1)
    (hβ1 : β ≠ 1) {J : Subgroup S} (hJ : J ≤ fixSubgroup β) :
    p * Nat.card (PSimple p J) ∣ sporOrd t := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hcen : Subgroup.center S = ⊥ := center_eq_bot_of_isSimpleGroup hnab
  have hout : Nat.card (Outer S) ≤ 2 := hOut S hS hnab t ⟨e⟩
  obtain ⟨x, rfl, hxp⟩ := exists_conj_of_pow hp hp2 hcen hout β hβp
  have hx1 : x ≠ 1 := fun h => hβ1 (by rw [h, map_one])
  have hxo : orderOf x = p := orderOf_eq_prime hxp hx1
  have hJc : J ≤ Subgroup.centralizer {x} := fun a ha => by
    have := hJ ha
    rwa [fixSubgroup_conj] at this
  have h := prime_mul_card_pSimple_dvd hp hxo hJc
  rwa [Nat.card_congr e.toEquiv, hOrd t] at h

theorem i1420Spor_holds (hOrd : SporadicOrdersTable) (hOut : SporadicOuterLeTwo) :
    I1420Spor := by
  intro p z s ht S _ _ t e β J hcore
  obtain ⟨hS, hnab, hβp, hβ1, -, hJ, ⟨eT⟩, -⟩ := hcore
  have hcardT : Nat.card (PSimple p J) = sporOrd s :=
    (Nat.card_congr eT.toEquiv).trans (hOrd s)
  rcases ht with ⟨rfl, -, rfl⟩ | ⟨rfl, -, rfl⟩
  · have h := prime_mul_dvd_sporOrd hOrd hOut Nat.prime_three (by norm_num) e hS hnab hβp hβ1 hJ.1
    rw [hcardT] at h
    exact eq_M_of_three_mul_fi24_dvd t h
  · have h := prime_mul_dvd_sporOrd hOrd hOut Nat.prime_five (by norm_num) e hS hnab hβp hβ1 hJ.1
    rw [hcardT] at h
    exact eq_M_of_five_mul_hn_dvd t h

end CFSG.LocalAnalysis.GLTheoremA.H1420
