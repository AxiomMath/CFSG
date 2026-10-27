module

public import Certificates.Certificate12041

public section

namespace CFSG.EvenSmallLie.OmegaEight.Cover

theorem relator_sq_check :
    (rels.all fun r => decide (rhoWord r * rhoWord r = 1)) = true :=
  Certificates.certificate12041

end CFSG.EvenSmallLie.OmegaEight.Cover
