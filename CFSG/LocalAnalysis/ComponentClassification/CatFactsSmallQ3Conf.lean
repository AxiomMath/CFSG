module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSmallConfA8
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSmallConfP45
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSmallQ3
public import Certificates.Certificate2007
public import Certificates.Certificate2008
public import Certificates.Certificate2009
public import Certificates.Certificate2012
public import Certificates.Certificate2013
public import Certificates.Certificate2014
public import Certificates.Certificate2015

public section

namespace CFSG.ComponentClassification.CatFactsSmall

open CFSG.ComponentClassification.GSThmB

theorem cfQ3Conf : CFQ3Conf := by
  intro K₀ _ _ hK c
  rcases hK with hL | ⟨-, -, ⟨e⟩⟩
  · obtain ⟨e⟩ := PSp43.equiv_of_lieModel hL
    exact props_of_confData (PSp43.cfConfData e) c
  · exact props_of_confData (A8.cfConfData e) c

end CFSG.ComponentClassification.CatFactsSmall
