module

public import CFSG.LieType.SeitzGeneration.OuterSUData
public import CFSG.LieType.SeitzGeneration.OuterModel
public import CFSG.LieType.SeitzGeneration.RankVacuity

public section

namespace CFSG.LieType.SeitzGeneration

open Matrix CFSG.Open CFSG.AGLEmbeddingD2 CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
  CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KCUnitaryModel CFSG.RankThree.PartOne.CTP

private theorem planeGen_outer_su_model_of_fieldAutData {d : TauCeti.ValidLieTypeIndex}
    {n ℓ f p : ℕ} {K : Type} [Field K] (h : UnitaryFieldData ℓ f K)
    (e : Cat d ≃* primeFormP h (idGram K n)) (hn3 : 3 ≤ n) (hne : ¬(n = 3 ∧ ℓ ^ f = 2))
    (hp : p.Prime) (hd : FieldAutData (primeFormP h (idGram K n)) p)
    {E : Subgroup (MulAut (Cat d))} (hE : IsElemAbelian p E) (hc : Nat.card E = p ^ 2)
    (hout : ¬ InnerPlane d p E) : PlaneGen E := by
  have : Fact p.Prime := ⟨hp⟩
  have : IsSimpleGroup (primeFormP h (idGram K n)) :=
    CFSG.RankThree.Classical.isSimpleGroup_primeFormP_one h hn3 hne
  have hnab : ∃ a b : primeFormP h (idGram K n), a * b ≠ b * a := by
    have hnc := CFSG.RankThree.Classical.not_commute_primeFormP_one h hn3 hne
    push Not at hnc
    exact hnc
  have hEi : CFSG.IsElementaryAbelian p (E.map (MulAut.congr e).toMonoidHom) :=
    (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian p _).mpr (isElemAbelian_map_congr e hE)
  have hc' : Nat.card (E.map (MulAut.congr e).toMonoidHom) = p ^ 2 := by
    rw [card_map_congr, hc]
  have hout' : ¬ ∀ φ ∈ E.map (MulAut.congr e).toMonoidHom, ∃ g, φ = MulAut.conj g := by
    intro h'
    exact not_le_range_conj_map_congr e hout fun φ hφ => (h' φ hφ).imp fun g hg => hg.symm
  have hclos := closure_fixUnion_eq_top_of_fieldAutData hnab hp hd
    (E.map (MulAut.congr e).toMonoidHom) hc' hout'
  exact planeGen_of_outer_model e ((planeGen_iff_closure_fixUnion _).mpr hclos)

theorem planeGen_outer_su_model (hpair : SubfieldPairSUOdd) {d : TauCeti.ValidLieTypeIndex}
    {n ℓ f p : ℕ} {K : Type} [Field K] (h : UnitaryFieldData ℓ f K)
    (e : Cat d ≃* primeFormP h (idGram K n)) (hn3 : 3 ≤ n) (hne : ¬(n = 3 ∧ ℓ ^ f = 2))
    (hp : p.Prime) (hp2 : p ≠ 2) (hpℓ : p ≠ ℓ) (hg : ¬ p ∣ Nat.gcd n (ℓ ^ f + 1))
    {E : Subgroup (MulAut (Cat d))} (hE : IsElemAbelian p E) (hc : Nat.card E = p ^ 2)
    (hout : ¬ InnerPlane d p E) : PlaneGen E :=
  planeGen_outer_su_model_of_fieldAutData h e hn3 hne hp
    (fieldAutData_primeFormP_odd hpair hn3 h hne hp hp2 hpℓ hg) hE hc hout

theorem planeGen_outer_twistedA (hpair : SubfieldPairSUOdd) {m : ℕ} {q : TauCeti.PrimePower}
    (hv : (TauCeti.LieTypeIndex.twistedA m q).Valid) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ≠ q.p) (hlift : ¬ (p ∣ q.card + 1 ∧ p ∣ m + 1))
    {E : Subgroup (MulAut (Cat ⟨.twistedA m q, hv⟩))} (hE : IsElemAbelian p E)
    (hc : Nat.card E = p ^ 2) (hout : ¬ InnerPlane ⟨.twistedA m q, hv⟩ p E) : PlaneGen E := by
  obtain ⟨hℓ, hf, hn3, hne, F, _, hU, ⟨θ⟩⟩ :=
    CFSG.RankThree.PartOne.exists_primeFormP_of_statedClassicalModel_PSU
      (CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA m q hv
        (MulEquiv.refl (Cat ⟨.twistedA m q, hv⟩)))
  refine planeGen_outer_su_model hpair hU θ hn3 hne hp hp2 hpq ?_ hE hc hout
  intro hd
  apply hlift
  rw [TauCeti.PrimePower.card_def]
  exact ⟨hd.trans (Nat.gcd_dvd_right _ _), hd.trans (Nat.gcd_dvd_left _ _)⟩

theorem seitzOuter_unitary_centralPrimeFree (hpair : SubfieldPairSUOdd) :
    SeitzPlanes fun d p E => ¬ InnerPlane d p E ∧ IsUnitaryIndex' d.1 ∧ CentralPrimeFree p d.1 := by
  rintro ⟨d, hv⟩ p hp hp2 hpd hex E hE hc ⟨hout, ⟨m, q, hd⟩, hlift⟩
  subst hd
  exact planeGen_outer_twistedA hpair hv hp hp2 (by simpa using hpd) hlift hE hc hout

theorem seitzOuter_unitary (hpair : SubfieldPairSUOdd) :
    SeitzPlanes fun d p E => ¬ InnerPlane d p E ∧ RankLE2 p (Cat d) ∧ IsUnitaryIndex' d.1 ∧
      ¬ (p = 3 ∧ ∃ q, d.1 = .twistedA 2 q ∧ 3 ∣ q.card + 1) := by
  rintro ⟨d, hv⟩ p hp hp2 hpd hex E hE hc ⟨hout, hrk, ⟨m, q, hd⟩, hexc⟩
  subst hd
  have hrange := (TauCeti.LieTypeIndex.inStandardRange_iff _).1
    ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1
  have hm2 : 2 ≤ m := hrange.1
  have hpq : p ≠ q.p := by simpa using hpd
  by_cases hlift : p ∣ q.card + 1 ∧ p ∣ m + 1
  · exfalso
    rcases (by omega : m = 2 ∨ m = 3 ∨ 4 ≤ m) with rfl | rfl | hm4
    · have hp3 : p = 3 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp hlift.2
      exact hexc ⟨hp3, q, rfl, hp3 ▸ hlift.1⟩
    · exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp
        (hp.dvd_of_dvd_pow (show p ∣ 2 ^ 2 from hlift.2)))
    · exact not_rankLE2_unitary hv hp hlift.1 hm4 hrk
  · exact planeGen_outer_twistedA hpair hv hp hp2 hpq hlift hE hc hout

end CFSG.LieType.SeitzGeneration
