module

public import CFSG.GH74.QTGen4.DSGen4.MainAmal
public import CFSG.GH74.QTGen4.DSGen4.Leaf.Bruhat
public import CFSG.GH74.QTGen4.DSGen4.Leaf.ChiefOfA5
public import CFSG.GH74.QTGen4.DSGen4.Leaf.SylowS
public import CFSG.GH74.QTGen4.DSGen4.Leaf.DSANoField
public import CFSG.GH74.QTGen4.DSGen4.Leaf.ZiStructure
public import CFSG.GH74.QTGen4.DSGen4.Leaf.ZiChief
public import CFSG.GH74.QTGen4.DSGen4.Leaf.M3
public import CFSG.GH74.QTGen4.DSGen4.Leaf.M4
public import CFSG.GH74.QTGen4.DSGen4.Leaf.DSACaseIOffender
public import CFSG.GH74.QTGen4.DSGen4.Leaf.DSACaseIFrattini
public import CFSG.GH74.QTGen4.DSGen4.Leaf.DSACaseIStep4
public import CFSG.GH74.QTGen4.DSGen4.Leaf.DSAA6
public import CFSG.GH74.QTGen4.DSGen4.Leaf.DSACaseIIOmega
public import CFSG.GH74.QTGen4.DSGen4.Leaf.M5
public import CFSG.GH74.QTGen4.DSGen4.Leaf.DSACaseIIQQ
public import CFSG.GH74.QTGen4.DSGen4.Leaf.DSACaseIIStep3
public import CFSG.GH74.QTGen4.DSGen4.Leaf.DSACaseIIStep4
public import CFSG.GH74.QTGen4.DSGen4.Leaf.Short2OfA5
public import CFSG.GH74.QTGen4.DSGen4.Leaf.DSAVertex
public import CFSG.GH74.QTGen4.DSGen4.Leaf.S3Module
public import CFSG.GH74.QTGen4.DSGen4.Leaf.DSBJZ2
public import CFSG.GH74.QTGen4.DSGen4.Leaf.DSBJV1
public import CFSG.GH74.QTGen4.DSGen4.Leaf.M8a
public import CFSG.GH74.QTGen4.DSGen4.Leaf.M8b
public import CFSG.GH74.QTGen4.DSGen4.Leaf.DSBJQ1
public import CFSG.GH74.QTGen4.DSGen4.Leaf.DSBJQ2
public import CFSG.GH74.QTGen4.DSGen4.Leaf.DSBReduce
public import CFSG.GH74.QTGen4.DSGen4.Leaf.DSBUQQ
public import CFSG.GH74.QTGen4.DSGen4.Leaf.DSBUQ1
public import CFSG.GH74.QTGen4.DSGen4.Leaf.DSBUQ2
public import CFSG.GH74.QTGen4.DSGen4.Leaf.DSBZSJ
public import CFSG.GH74.QTGen4.DSGen4.Leaf.DSBZSU
public import CFSG.GH74.QTGen4.DSGen4.Leaf.L34Glue
public import CFSG.GH74.QTGen4.DSGen4.Leaf.L34Local
public import CFSG.GH74.QTGen4.DSGen4.Leaf.L34Model
public import CFSG.GH74.QTGen4.DSGen4.Leaf.UAmalCoordsPlain
public import CFSG.GH74.QTGen4.DSGen4.Leaf.UAmalExtA5
public import CFSG.GH74.QTGen4.DSGen4.Leaf.M2
public import CFSG.GH74.QTGen4.DSGen4.Leaf.M6
public import CFSG.GH74.QTGen4.DSGen4.Leaf.M7
public import CFSG.GH74.QTGen4.DSGen4.Leaf.Lin2OfNatural
public import CFSG.GH74.QTGen4.DSGen4.Leaf.Alt5OfOrth
public import CFSG.GH74.QTGen4.DSGen4.Leaf.Omega4MinusOfOrth
public import CFSG.GH74.QTGen4.DSGen4.Leaf.L34DC

public section

namespace CFSG.GH74.QTGen4.DSGen4

instance : DSLeaf LeafBruhat := ⟨leafBruhat⟩
instance : DSLeaf LeafFaithfulA5 := ⟨leafFaithfulA5⟩
instance : DSLeaf LeafChiefOfA5 := ⟨leafChiefOfA5⟩
instance : DSLeaf LeafSylowS := ⟨leafSylowS⟩
instance : DSLeaf LeafRankBounds := ⟨leafRankBounds⟩
instance : DSLeaf LeafFrattiniFaithful := ⟨leafFrattiniFaithful⟩
instance : DSLeaf LeafM7 := ⟨leafM7⟩
instance : DSLeaf LeafFrattiniChief := ⟨leafFrattiniChief⟩
instance : DSLeaf LeafM2 := ⟨leafM2⟩
instance : DSLeaf LeafDSANoField := ⟨leafDSANoField⟩
instance : DSLeaf LeafZiStructure := ⟨leafZiStructure⟩
instance : DSLeaf LeafZiChief := ⟨leafZiChief⟩
instance : DSLeaf LeafM3 := ⟨leafM3⟩
instance : DSLeaf LeafM4 := ⟨leafM4⟩
instance : DSLeaf LeafDSACaseIOffender := ⟨leafDSACaseIOffender⟩
instance : DSLeaf LeafDSACaseIFrattini := ⟨leafDSACaseIFrattini⟩
instance : DSLeaf LeafDSACaseIStep4 := ⟨leafDSACaseIStep4⟩
instance : DSLeaf LeafDSAA6 := ⟨leafDSAA6⟩
instance : DSLeaf LeafDSACaseIIOmega := ⟨leafDSACaseIIOmega⟩
instance : DSLeaf LeafM5 := ⟨leafM5⟩
instance : DSLeaf LeafDSACaseIIQQ := ⟨leafDSACaseIIQQ⟩
instance : DSLeaf LeafDSACaseIIStep3 := ⟨leafDSACaseIIStep3⟩
instance : DSLeaf LeafDSACaseIIStep4 := ⟨leafDSACaseIIStep4⟩
instance : DSLeaf LeafShort2OfA5 := ⟨leafShort2OfA5⟩
instance : DSLeaf LeafLin2OfNatural := ⟨leafLin2OfNatural⟩
instance : DSLeaf LeafDSAVertex := ⟨leafDSAVertex⟩
instance : DSLeaf LeafDSBA5Vertex := ⟨leafDSBA5Vertex⟩
instance : DSLeaf LeafDSBS3Vertex := ⟨leafDSBS3Vertex⟩
instance : DSLeaf LeafS3Module := ⟨leafS3Module⟩
instance : DSLeaf LeafDSBJZ2 := ⟨leafDSBJZ2⟩
instance : DSLeaf LeafDSBJV1 := ⟨leafDSBJV1⟩
instance : DSLeaf LeafM8a := ⟨leafM8a⟩
instance : DSLeaf LeafM8b := ⟨leafM8b⟩
instance : DSLeaf LeafM6 := ⟨leafM6⟩
instance : DSLeaf LeafDSBJQ1 := ⟨leafDSBJQ1⟩
instance : DSLeaf LeafDSBJQ2 := ⟨leafDSBJQ2⟩
instance : DSLeaf LeafDSBReduce := ⟨leafDSBReduce⟩
instance : DSLeaf LeafDSBUQQ := ⟨leafDSBUQQ⟩
instance : DSLeaf LeafDSBUQ1 := ⟨leafDSBUQ1⟩
instance : DSLeaf LeafDSBUQ2 := ⟨leafDSBUQ2⟩
instance : DSLeaf LeafDSBZSJ := ⟨leafDSBZSJ⟩
instance : DSLeaf LeafDSBZSU := ⟨leafDSBZSU⟩
instance : DSLeaf LeafL34DC := ⟨leafL34DC⟩
instance : DSLeaf LeafL34Glue := ⟨leafL34Glue⟩
instance : DSLeaf LeafL34Local := ⟨leafL34Local⟩
instance : DSLeaf LeafL34Model := ⟨leafL34Model⟩
instance : DSLeaf LeafAlt5OfOrth := ⟨leafAlt5OfOrth⟩
instance : DSLeaf LeafUAmalCoordsPlain := ⟨leafUAmalCoordsPlain⟩
instance : DSLeaf LeafUAmalExtA5 := ⟨leafUAmalExtA5⟩
instance : DSLeaf LeafOmega4MinusOfOrth := ⟨leafOmega4MinusOfOrth⟩

theorem dsALoc_F4_holds : DSALoc_F4 :=
  dsALoc_F4_of_leaves leafDSANoField leafZiStructure leafDSACaseIIStep3 leafDSACaseIIStep4 leafDSAVertex

theorem dsAAmal_F4_holds : DSAAmal_F4 :=
  dsAAmal_F4_of_leaves leafDSANoField leafZiStructure leafDSACaseIIStep3 leafDSACaseIIStep4
    leafDSACaseIStep4 leafL34Model leafL34Local leafL34Glue

theorem dsBLoc_F4_holds : DSBLoc_F4 :=
  dsBLoc_F4_of_leaves leafDSBReduce leafDSBJQ1 leafDSBJQ2 leafDSBUQ1 leafDSBUQ2 leafShort2OfA5
    (DSLeaf.holds (L := LeafAlt5OfOrth)) (DSLeaf.holds (L := LeafOmega4MinusOfOrth)) leafDSBZSU leafDSBZSJ

end CFSG.GH74.QTGen4.DSGen4
