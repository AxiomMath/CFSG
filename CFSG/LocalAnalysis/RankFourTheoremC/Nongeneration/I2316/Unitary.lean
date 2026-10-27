module

public import CFSG.LocalAnalysis.RankFourTheoremC.Nongeneration.I2316.Defs
public import CFSG.LocalAnalysis.RankFourTheoremC.Nongeneration.I2316.UnitaryField
public import CFSG.LocalAnalysis.AGLEmbedding.GenericTargetFacts

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.Nongeneration.I2316

open CFSG.AGLEmbedding CFSG.Open CFSG.LieType.SeitzGeneration CFSG.RankThree.PartOne
  CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.RankThree.PartOne.KCUnitaryModel

theorem planesGenerate_of_isUnitaryIndex {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {d : TauCeti.ValidLieTypeIndex} (hd : IsUnitaryIndex p d) :
    PlanesGenerate p (CatGroup d) := by
  intro E hE hEc hnot
  obtain ⟨q, hqp, hdq⟩ := hd
  obtain ⟨d, hv⟩ := d
  simp only at hdq
  subst hdq
  subst hqp
  obtain ⟨hℓ, hf, hn3, hne, F, _, hU, ⟨θ⟩⟩ :=
    exists_primeFormP_of_statedClassicalModel_PSU
      (CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA 2 q hv
        (MulEquiv.refl (CatGroup ⟨.twistedA 2 q, hv⟩)))
  set E' := E.map (MulAut.congr θ).toMonoidHom
  have hE' : IsElemAbelian q.p E' := isElemAbelian_map_congr θ hE
  have hc' : Nat.card E' = q.p ^ 2 := (card_map_congr θ E).trans hEc
  have hg : ¬ q.p ∣ Nat.gcd (2 + 1) (q.p ^ q.exponent + 1) := by
    intro h1
    have h2 : q.p ∣ q.p ^ q.exponent + 1 := h1.trans (Nat.gcd_dvd_right _ _)
    have h3 : q.p ∣ q.p ^ q.exponent := dvd_pow_self q.p (by omega)
    have h4 := (Nat.dvd_add_right h3).1 h2
    exact hp.one_lt.ne' (Nat.dvd_one.1 h4)
  have hout : ¬ E' ≤ primeFormD hU (idGram F (2 + 1)) := by
    intro hle
    apply not_le_range_conj_map_congr θ hnot
    intro e he
    exact pElement_mem_inner_of_not_dvd_gcd hU hn3 hne hp hg (hle he) (hE'.2 e he)
  have hexc : 2 + 1 = 3 → q.p ^ (q.exponent / q.p) = 2 → q.p ∣ q.exponent →
      CFSG.LieType.SeitzGeneration.PlaneGen E' := by
    intro _ h2 _
    exact absurd ((Nat.Prime.pow_eq_iff Nat.prime_two).1 h2).1 hp2
  exact planeGen_of_outer_model θ
    (planeGen_outer_su_field' hU hn3 hne hp hp2 hE' hc' hout hexc)

end CFSG.LocalAnalysis.RankFourTheoremC.Nongeneration.I2316
