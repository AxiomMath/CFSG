module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicWitData
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicM11Tests
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicCheckW
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicM24Tests

public section

namespace CFSG.ComponentClassification.RankTwoSporadic.M11

open CFSG.ComponentClassification.RankTwoSporadic.Cert
open CFSG.RankThree.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native

@[expose] def m11TreeD : ℕ :=
  0x2519120120e6505032a48601c2250821080c921d4040c22294683814448446100220a0c7190aa48122518e12a08300422080a341c0a22422314243994810d201000000000300060000004080190e5321220a82030000000000180000010219243a80818445080000000000005000050408a110e02a0291982030000000c500000014102146838144484460800000000014050000004085090e6520434802701000000031002000000824a838864500c128487329021a402

@[expose] def m11WitD : ℕ :=
  0x420084200842008401004120040108021080200802008401006c1080200840100420081e0084010802008420084300840100401084010802180021004010802008401798000000001c200802108420080210014a420e629063108200018b229c93202f7b80d6b16550d27408e6290601042041d222194518064394c84882a114874850a300660a0e5010491a92021c23418aa100483a8c408d251a9070a48530046490ea020611154221c0540523308c838c240154928d0702889088c1510e3120a03246621c49401450a4a838864500c128487329021a40a4a0e62906208050

@[expose] def m11CheckW (dt dw : ℕ) : Bool :=
  let d := rdCensus (natTokens 5 295 dt) 11
  let w := rdWitData (natTokens 5 359 dw) 11
  let inX := inWords 11 m11Gens w.words
  (allLt m11Gens.size fun k => validK 11 m11Gens[k]!) &&
    censusOKW 11 m11PS inX M24.allA true false false d.sGens d.roots d.nodes w.cS w.wcs &&
    (allLt d.sGens.size fun k => inX d.sGens[k]!) && w.cS.pts.size == 16

end CFSG.ComponentClassification.RankTwoSporadic.M11
