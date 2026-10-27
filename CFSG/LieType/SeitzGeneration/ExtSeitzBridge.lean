module

public import CFSG.LieType.SeitzGeneration.OuterModel
public import CFSG.LieType.SeitzGeneration.ExcParabolicModel
public import CFSG.RankThree.PartOne.CTP.SeitzFineDefs

public section

namespace CFSG.LieType.SeitzGeneration

open CFSG.Open CFSG.AGLEmbeddingD2 CFSG.RankThree.PartOne.CTP CFSG.PreuniquenessRankFour.Helpers

theorem exists_noncommuting_of_isElementaryAbelian_aut {K : Type} [Group K] [Finite K]
    [IsSimpleGroup K] {p : ℕ} [Fact p.Prime] {E : Subgroup (MulAut K)}
    (hE : IsElementaryAbelian p ↥E) (hc : Nat.card E = p ^ 2) : ∃ a b : K, a * b ≠ b * a := by
  by_contra hnc
  have hcomm : ∀ a b : K, a * b = b * a := fun a b => by_contra fun hne => hnc ⟨a, b, hne⟩
  let _ : CommGroup K := { ‹Group K› with mul_comm := hcomm }
  have hprime : (Nat.card K).Prime := IsSimpleGroup.prime_card (α := K)
  have : Fact (Nat.card K).Prime := ⟨hprime⟩
  have : IsCyclic K := isCyclic_of_prime_card (p := Nat.card K) rfl
  have : IsCyclic (ZMod (Nat.card K))ˣ := inferInstance
  have : IsCyclic (MulAut K) :=
    isCyclic_of_surjective (IsCyclic.mulAutMulEquiv K).symm.toMonoidHom
      (IsCyclic.mulAutMulEquiv K).symm.surjective
  have : Finite E := Nat.finite_of_card_ne_zero (by rw [hc]; exact pow_ne_zero 2 (NeZero.ne p))
  exact IsElementaryAbelian.not_isCyclic_of_card_eq_prime_sq hc (Subgroup.isCyclic E)

theorem planeGen_of_extSeitzAtInnerFor {d : TauCeti.ValidLieTypeIndex} [Finite (Cat d)]
    [IsSimpleGroup (Cat d)] {P : ℕ → Prop} (h : ExtSeitzAtInnerFor d.1 P) {p : ℕ} (hp : p.Prime)
    (hp5 : 5 ≤ p) (hpd : p ≠ d.1.characteristic) (hex : ¬ IsD2SeitzException p d.1) (hP : P p)
    {E : Subgroup (MulAut (Cat d))} (hE : IsElemAbelian p E) (hc : Nat.card E = p ^ 2)
    (hin : InnerPlane d p E) : PlaneGen E := by
  have : Fact p.Prime := ⟨hp⟩
  have hel : IsElementaryAbelian p ↥E := isElementaryAbelian_of_isElemAbelian hE
  rw [planeGen_iff_closure_fixUnion]
  rcases h (Cat d) (exists_noncommuting_of_isElementaryAbelian_aut hel hc)
      ⟨d.2, ⟨MulEquiv.refl _⟩⟩ p hp hp5 hpd hP E hel hc
      (fun φ hφ => (hin hφ).imp fun g hg => hg.symm) with h' | h'
  · exact h'
  · exact absurd (Or.inr h') hex

theorem planeGen_of_extSeitzAtOuterFor {d : TauCeti.ValidLieTypeIndex} [Finite (Cat d)]
    [IsSimpleGroup (Cat d)] {P : ℕ → Prop} (h : ExtSeitzAtOuterFor d.1 P) {p : ℕ} (hp : p.Prime)
    (hp5 : 5 ≤ p) (hpd : p ≠ d.1.characteristic) (hex : ¬ IsD2SeitzException p d.1) (hP : P p)
    {E : Subgroup (MulAut (Cat d))} (hE : IsElemAbelian p E) (hc : Nat.card E = p ^ 2)
    (hout : ¬ InnerPlane d p E) : PlaneGen E := by
  have : Fact p.Prime := ⟨hp⟩
  have hel : IsElementaryAbelian p ↥E := isElementaryAbelian_of_isElemAbelian hE
  rw [planeGen_iff_closure_fixUnion]
  rcases h (Cat d) (exists_noncommuting_of_isElementaryAbelian_aut hel hc)
      ⟨d.2, ⟨MulEquiv.refl _⟩⟩ p hp hp5 hpd hP E hel hc
      (fun hall => hout fun φ hφ => (hall φ hφ).elim fun g hg => ⟨g, hg.symm⟩) with h' | h'
  · exact h'
  · exact absurd (Or.inr h') hex

theorem seitzPlanes_inner_of_extSeitz {F : TauCeti.LieTypeIndex → Prop}
    {R : TauCeti.LieTypeIndex → ℕ → Prop}
    (hfs : ∀ d : TauCeti.ValidLieTypeIndex, F d.1 → Finite (Cat d) ∧ IsSimpleGroup (Cat d))
    (h : ∀ d : TauCeti.ValidLieTypeIndex, F d.1 → ExtSeitzAtInnerFor d.1 (R d.1)) :
    SeitzPlanes fun d p E => InnerPlane d p E ∧ F d.1 ∧ 5 ≤ p ∧ R d.1 p := by
  rintro d p hp hp2 hpd hex E hE hc ⟨hin, hF, hp5, hR⟩
  obtain ⟨hfin, hsimple⟩ := hfs d hF
  exact planeGen_of_extSeitzAtInnerFor (h d hF) hp hp5 hpd hex hR hE hc hin

theorem seitzPlanes_outer_of_extSeitz {F : TauCeti.LieTypeIndex → Prop}
    {R : TauCeti.LieTypeIndex → ℕ → Prop}
    (hfs : ∀ d : TauCeti.ValidLieTypeIndex, F d.1 → Finite (Cat d) ∧ IsSimpleGroup (Cat d))
    (h : ∀ d : TauCeti.ValidLieTypeIndex, F d.1 → ExtSeitzAtOuterFor d.1 (R d.1)) :
    SeitzPlanes fun d p E => ¬ InnerPlane d p E ∧ F d.1 ∧ 5 ≤ p ∧ R d.1 p := by
  rintro d p hp hp2 hpd hex E hE hc ⟨hout, hF, hp5, hR⟩
  obtain ⟨hfin, hsimple⟩ := hfs d hF
  exact planeGen_of_extSeitzAtOuterFor (h d hF) hp hp5 hpd hex hR hE hc hout

end CFSG.LieType.SeitzGeneration
