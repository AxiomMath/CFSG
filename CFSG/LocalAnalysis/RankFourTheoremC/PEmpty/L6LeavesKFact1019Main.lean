module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFact1019Reduce
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFact1019PSp
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.TypeCCarrier

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.Fact1019

open CFSG.Open

theorem involution_typeA4 : InvolutionAt FamA4 := by
  intro K _ _ d hd ⟨e⟩ p hp hp2 hchar
  obtain ⟨r, q, hr, hdq⟩ := hd
  obtain ⟨dd, hv⟩ := d
  have hdq' : dd = TauCeti.LieTypeIndex.A r q := hdq
  subst hdq'
  have hchar' : p = q.p := by simpa using hchar
  subst hchar'
  haveI : Fact q.p.Prime := ⟨hp⟩
  let e' := e.trans (CFSG.ClassicalModels.linearCatalogCandidateEquivPSL r q hv)
  obtain ⟨t, ht, E, hEc, hE, hcard⟩ :=
    exists_involution_pslProj (F := GaloisField q.p q.exponent) q.p hp2 (show 5 ≤ r + 1 by omega)
  obtain ⟨t', ht', E', hEc', hE', hcard'⟩ := exists_involution_transport e' hEc hE hcard
  exact ⟨t', ht'.trans ht, E', hEc', hE', hcard'⟩

theorem involution_typeC3 : InvolutionAt FamC3 := by
  intro K _ _ d hd ⟨e⟩ p hp hp2 hchar
  obtain ⟨r, q, hr, hdq⟩ := hd
  obtain ⟨dd, hv⟩ := d
  have hdq' : dd = TauCeti.LieTypeIndex.C r q := hdq
  subst hdq'
  have hchar' : p = q.p := by simpa using hchar
  subst hchar'
  haveI : Fact q.p.Prime := ⟨hp⟩
  obtain ⟨-, F, hF, hFfin, hcard, ⟨e'⟩⟩ := CFSG.QuasithinUnique.SQTK.statedClassicalModel_typeC
    r q hv e
  haveI : Fintype F := Fintype.ofFinite F
  haveI : CharP F q.p :=
    charP_of_card_eq_prime_pow (f := q.exponent)
      (by rw [← Nat.card_eq_fintype_card]; exact hcard)
  obtain ⟨t, ht, E, hEc, hE, hcard'⟩ :=
    exists_involution_statedSp (F := F) (n := r) q.p hp2 (by omega)
  obtain ⟨t', ht', E', hEc', hE', hcard''⟩ := exists_involution_transport e' hEc hE hcard'
  exact ⟨t', ht'.trans ht, E', hEc', hE', hcard''⟩

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.Fact1019
