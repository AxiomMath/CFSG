module

public import CFSG.LocalAnalysis.SectionRank.QTK.Insp443.RankThreeConcl
public import CFSG.LocalAnalysis.SectionRank.QTK.Insp443.CentralKerOf
public import CFSG.RankThree.PartOne.S11c.G2Plane

public section

namespace CFSG.SectionRank.QTK.Insp443

open Subgroup CFSG.Open CFSG.Quasithin CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.LieType.Chevalley CFSG.RankThree.PartOne

theorem card_le_eight_of_chevalleyExceptionalModel_G2
    {S : Type} [Group S] [Finite S]
    {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hm : ChevalleyExceptionalModel S .G2 p f)
    {E : Subgroup S} (hE : IsElemAbelian 2 E) : Nat.card E ≤ 8 := by
  obtain ⟨F, _, _, hcard, ⟨e₀⟩⟩ := hm.2
  let e : S ≃* adjointGroup .G2 F :=
    e₀.trans ((QuotientGroup.quotientMulEquivOfEq center_adjointGroup_eq_bot).trans
      QuotientGroup.quotientBot)
  have hodd : Odd (Nat.card F) := by
    rw [hcard]
    exact (hp.odd_of_ne_two hp2).pow
  let ψ : S →* ModGL .G2 F := (adjointGroup .G2 F).subtype.comp e.toMonoidHom
  have hψ : Function.Injective ψ := fun a b h => e.injective (Subtype.ext h)
  have hR : E.map ψ ≤ adjointGroup .G2 F := by
    rintro _ ⟨x, -, rfl⟩
    exact (e x).2
  let eR : E ≃* E.map ψ := E.equivMapOfInjective ψ hψ
  have : Finite (E.map ψ) := Finite.of_equiv E eR.toEquiv
  have : CFSG.IsElementaryAbelian 2 (E.map ψ) := (hE.map ψ).isElementaryAbelian
  have hle := (g2_elementary_two hodd hR).1
  rwa [← Nat.card_congr eR.toEquiv] at hle

theorem KConf.card_le_eight_of_G2
    {K : Type} [Group K] [Finite K] {L V MK : Subgroup K}
    (h : KConf K L V MK) {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hm : ChevalleyExceptionalModel (K ⧸ Subgroup.center K) .G2 p f) : Nat.card V ≤ 8 := by
  let π : K →* K ⧸ Subgroup.center K := QuotientGroup.mk' (Subgroup.center K)
  have hinj : Function.Injective (π.comp V.subtype) := by
    rw [injective_iff_map_eq_one]
    intro v hv
    have hvZ : (v : K) ∈ Subgroup.center K := (QuotientGroup.eq_one_iff _).1 hv
    have hodd : Odd (orderOf (v : K)) :=
      h.odd_card_center.of_dvd_nat (Subgroup.orderOf_dvd_natCard _ hvZ)
    have hdvd : orderOf (v : K) ∣ 2 := orderOf_dvd_of_pow_eq_one (h.elemAbelian.2 v v.2)
    have h1 : orderOf (v : K) = 1 := by
      rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h1 | h2
      · exact h1
      · rw [h2] at hodd
        exact absurd hodd (by decide)
    exact Subtype.ext (orderOf_eq_one_iff.1 h1)
  have hE : IsElemAbelian 2 (π.comp V.subtype).range := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
    exact h.elemAbelian.map π
  have hle := card_le_eight_of_chevalleyExceptionalModel_G2 hp hp2 hm hE
  rwa [← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv] at hle

theorem forKF_G2odd :
    ForKF (fun S _ => ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ ChevalleyExceptionalModel S .G2 p 1) := by
  intro K _ _ L V MK hK hC ⟨p, hp, hp2, hm⟩
  exact hK.kConfig.conclK_of_card_le_eight hC (hK.card_le_eight_of_G2 hp hp2 hm)

theorem for_G2odd
    (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK) :
    For (fun S _ => ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ ChevalleyExceptionalModel S .G2 p 1) :=
  For.of_forKF h37 h38 h39 forKF_G2odd

end CFSG.SectionRank.QTK.Insp443
