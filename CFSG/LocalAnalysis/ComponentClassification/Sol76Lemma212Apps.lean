module

public import CFSG.LocalAnalysis.ComponentClassification.Sol76Lemma212Proof
public import CFSG.LocalAnalysis.ComponentClassification.Sol78MaxAlt

public section

namespace CFSG.ComponentClassification

theorem Sol78.maximalAltComponent_of_thm13_of_maximality (h13 : Sol76T13.SolomonThm13Simple)
    (hmax : Sol78.MaximalityLemmaInput) (hS : SolAltLit.SchurAlternatingMultiplierInput) :
    SolAltLit.MaximalAltComponentInput :=
  Sol78.maximalAltComponent_of_thm13 h13 Sol76.lemma212Input hmax hS

end CFSG.ComponentClassification
