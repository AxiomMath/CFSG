module

public import Certificates.Data.Kernel.LocalQT.CovH
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.HSCoverCheck

public section

namespace CFSG.KC.LQT.Cov.H

open CFSG.KC.LQT.Cov CFSG.QuasithinUnique.Ch1.HSCover

@[expose] def ofCH (d : CH) : CovData :=
  { xw0 := d.xw.getD 0 [], xw1 := d.xw.getD 1 [], xw2 := d.xw.getD 2 [], nV := d.nV,
    words := d.words.toArray, tgtA := d.tgt.toArray, backA := d.back.toArray,
    pairs := d.pairs.map fun p => { gw := p.1, a := p.2.1, b := p.2.2 },
    anchors := d.anchors.map fun p => { gw := p.1, a := 0, b := p.2 } }

end CFSG.KC.LQT.Cov.H

end
