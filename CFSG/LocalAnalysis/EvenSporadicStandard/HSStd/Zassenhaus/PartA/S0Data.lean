module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.SpecialData
public import CFSG.RankThree.Native.ChainCentralizer

public section

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA.S0

open CFSG.Monster.B.Co2.Native CFSG.Monster.B.Fischer CFSG.Certificates.Native
  CFSG.RankThree.Native CFSG.EvenSporadicStandard.HSStd CFSG.EvenSporadicStandard.HSStd.Zassenhaus

@[expose] def hexData : String :=
  "00F01905800204501A00601505C01002204306004701401603001100E00501204B00003603704401303F05205B\
  02C02A02005604802802401D00B01705702104E05D02E02D01E05000905500C00803404602705905A04F00D01B\
  02F01C00403B04004105102600103E06103A00A02B04C00706203901F04D03C06303D05305405F029023003018\
  05E02503304903803103203504A04200400301900100004901103C02E04A02803B04F04202704504C00603605D\
  01702F03E01405F00202B04302A03505C03D05303805704805406103F00E00A05E01C01A033040008015062037\
  03902C04101D01203102103206300B00701F01602602D03400D01B05800F05B05102300500905001006005200C\
  04B04704E02002405905A02204405505604601E01302901804D02503003A00404C05503100004301106103C018\
  05701305100E00D04503700603A00B04703503E04F00906202601F02B01E01D01B02D05A02302204002E01A039\
  04803803F01C05B02002505C05900304205004101504D01002902701204E00804901602A02403403200504A00F\
  04B01402803D04404600103603B01703300C05D05405300205E00A05F03002102C02F052056058063007019060\
  00502701400E04900001102104603A02805204F01000301A00D00605801600205601301905F01700F01F02602C\
  02501B02400705704802001E01C00100A04B03F04501D04105B05A04703703903504003304403103C03200904E\
  03804305D02A03402D04C03D03602B00803002300406302904206003B00C05E06200B054053059015022012055\
  02F02E06103E05001804D05C05104A00402A05201C00001803403C06104302903004F00E00D04502604103A059\
  04702F03E05100504E03704A00301E01D04402402202105A02002E01004205E00A00103105B04002501500B02B\
  03904600605C06301A05703201206200705801604C02D01102700901F00F03301405605F01B05003F06001900C\
  04B01700205405305D04803803D01302302C03505502804904D00803B03603401700E014041040006025008044\
  02204E03103000200F04701106301300305A01600101802701A02003F05E02102401B01E00A02301F00702A019\
  05703502602B05004902E05600D00C05504B00002903A04F05C05903605206105403E01C005004062053009045\
  04601004802D05803305104D00B03702C04C03B04303D03202F02804A03901505B03805D01D05F06003C042012\
  00004E01C05200400600504B05E04402501004502704204F00B04905401305101503904703402A01A03D00201D\
  01E04306304603305603600A03000D06102E01902B05702D02902F02603103E02201803502403705B01605304C\
  05001B03206204005F00E01F00900C02101705A01105800703B04D00100F03C01400303A01205502302C04A059\
  04803805C05D00804106002803F02004F01003D04C00C00501A01504800B05E00900405305400F00102B063013\
  05100704D04701801F00606203F02202101904201E01D02E02705A02A02402902802601102C02D02303C043041\
  03203303705703A03405C03903604A02F00206001C04003102003004E04504601700804903B04B003016044000\
  05001405800D00E05506103505205902505B03805D00A05F03E05601B01200002006205300400C045025008044\
  04B01200502704201105400F00B06004305C01601B01803001A01703F01D02F05100105603304604C00702A00D\
  05002902602B05703702E01E01904003202203403503B02D05A03905203606104703E01C03104100E014009006\
  02303D05B04F05800A02405D06304902801F03A00301005502102C04A05903804801504D05E05F01303C00204E\
  00001005304C00403203E02204804402504E00C03D04300F00101602601305101D01104701802006002703A015\
  01E04201902100702E06200A01201B06105606304D05005902303505403100504B03402F03F03703804901C052\
  05700D00603605504101F00E00904504601700803905803300302B00B04F02C01403B00203004002903C04A02D\
  05E05B05C05D05A05F01A02802402A00700202401903C01E05605902B03D04D03B02C00304C00A03005A036050\
  00904F01D04A05E05402E03F01701604001C00E04504904104200004701006005F01400803102201A00C05302F\
  02303705B03E01201500F04803A00B05502A03505105704600102604302803204403405C01F01106203804E033\
  00605805202700D06101300501B02505D03902D04B018029021004020063"

@[expose] def tab (k : ℕ) : Array ℕ := hexTable3 100 (100 * k) hexData

@[expose] def y0 : Array ℕ := tab 0

@[expose] def xGens : Array (Array ℕ) := #[tab 1, tab 2, tab 3, tab 4]

@[expose] def u0 : Array ℕ := tab 1

@[expose] def rGens : Array (Array ℕ) := #[tab 5, tab 6, tab 7, tab 8, tab 9]

@[expose] def pEl : Array ℕ := tab 10

@[expose] def z0 : Array ℕ := s5Z

@[expose] def pGens : Array (Array ℕ) := #[hs100Arr 0, hs100Arr 1]

@[expose] def keys : List ℕ := [0, 1, 2, 3, 4]

@[expose] def pw (x : Array ℕ) : ℕ → Array ℕ
  | 0 => idA 100
  | k + 1 => compA 100 x (pw x k)

@[expose] def cyGens : Array (Array ℕ) := #[y0, tab 1, tab 2, tab 3, tab 4]

@[expose] def aGens : Array (Array ℕ) := #[tab 5, tab 6, tab 7, tab 8, tab 9, tab 10]

@[expose] def cuGens : Array (Array ℕ) := #[u0, tab 5, tab 6, tab 7, tab 8, tab 9, tab 10]

@[expose] def jGens : Array (Array ℕ) :=
  Array.ofFn (n := 4) fun i => compA 100 (tab (5 + i.1)) (tab (6 + i.1))

@[expose] def classAct (k : ℕ) (a : Array ℕ) : Array ℕ := conjA 100 pGens[k]! a

@[expose] def classOrbit (x : Array ℕ) (fuel : ℕ) : ArrCert :=
  arrBfs classAct pGens.size (keyA 100 keys) x fuel

@[expose] def zOrbit : ArrCert := classOrbit z0 20000

@[expose] def uOrbit : ArrCert := classOrbit u0 40000

@[expose] def yOrbit : ArrCert := classOrbit y0 400000

@[expose] def kCert : ArrCert := enumBfs 100 xGens keys 400

@[expose] def cyCert : ArrCert := enumBfs 100 cyGens keys 800

@[expose] def aCert : ArrCert := enumBfs 100 aGens keys 4000

@[expose] def cuCert : ArrCert := enumBfs 100 cuGens keys 8000

@[expose] def jCert : ArrCert := enumBfs 100 jGens keys 800

@[expose] def fixCnt (a : Array ℕ) : ℕ :=
  (Finset.univ.filter fun i : Fin 100 => a[i.1]! = i.1).card

@[expose] def coxOK (s : Array (Array ℕ)) (m : ℕ) : Bool :=
  allLt m (fun i => eqA 100 (compA 100 s[i]! s[i]!) (idA 100)) &&
    allLt (m - 1) (fun i => eqA 100 (compA 100 (compA 100 s[i]! s[i + 1]!) s[i]!)
      (compA 100 (compA 100 s[i + 1]! s[i]!) s[i + 1]!)) &&
    allLt m (fun i => allLt m (fun j => decide (j < i + 2) ||
      eqA 100 (compA 100 s[i]! s[j]!) (compA 100 s[j]! s[i]!)))

@[expose] def classOK (x : Array ℕ) (c : ArrCert) (N : ℕ) : Bool :=
  arrCertOK classAct pGens.size (validA 100) (keyA 100 keys) x c && c.pts.size == N

@[noinline, expose] def basicOK : Bool :=
  allLt pGens.size (fun k => validA 100 pGens[k]!) &&
    validA 100 z0 && s5InP z0 && eqA 100 (compA 100 z0 z0) (idA 100) && !eqA 100 z0 (idA 100) &&
    validA 100 y0 && s5InP y0 && !eqA 100 u0 (idA 100) &&
    allLt xGens.size (fun k => validA 100 xGens[k]! && s5InP xGens[k]!) &&
    allLt rGens.size (fun k => validA 100 rGens[k]! && s5InP rGens[k]!) &&
    validA 100 pEl && s5InP pEl

@[noinline, expose] def classesOK : Bool :=
  classOK z0 zOrbit 5775 && classOK u0 uOrbit 15400 && classOK y0 yOrbit 123200 &&
    fixCnt z0 == 20 && fixCnt u0 == 0

@[expose] def eCommCount : ℕ :=
  (Finset.univ.filter fun i : Fin zasE0Cert.pts.size =>
    commA 100 y0 zasE0Cert.pts[i.1]! = true).card

@[noinline, expose] def yOK : Bool :=
  eqA 100 (pw y0 3) (idA 100) && !eqA 100 y0 (idA 100) && commA 100 y0 z0 &&
    enumOK 100 zasE0Gens zasEKeys zasE0Cert && zasE0Cert.pts.size == 16 &&
    allLt zasE0Gens.size (fun k =>
      zasE0Cert.pts.toList.any (eqA 100 (conjA 100 y0 zasE0Gens[k]!))) &&
    zasE0Cert.pts.toList.any (eqA 100 z0) && eCommCount == 4

@[noinline, expose] def kOK : Bool :=
  coxOK xGens 4 && !eqA 100 (compA 100 xGens[0]! xGens[1]!) (idA 100) &&
    enumOK 100 xGens keys kCert && kCert.pts.size == 120 &&
    allLt xGens.size (fun k => commA 100 y0 xGens[k]!) &&
    enumOK 100 cyGens keys cyCert && cyCert.pts.size == 360 &&
    !kCert.pts.toList.any (eqA 100 y0)

@[expose] def ord3J : List (Array ℕ) :=
  jCert.pts.toList.filter fun b => eqA 100 (pw b 3) (idA 100) && !eqA 100 b (idA 100)

@[noinline, expose] def aOK : Bool :=
  coxOK rGens 5 && !eqA 100 (compA 100 rGens[0]! rGens[1]!) (idA 100) &&
    allLt aGens.size (fun k => commA 100 u0 aGens[k]!) &&
    enumOK 100 aGens keys aCert && aCert.pts.size == 1440 &&
    !aCert.pts.toList.any (eqA 100 u0) &&
    enumOK 100 cuGens keys cuCert && cuCert.pts.size == 2880 &&
    enumOK 100 jGens keys jCert && jCert.pts.size == 360 &&
    jCert.pts.toList.any (eqA 100 y0) &&
    allLt aGens.size (fun g => allLt jGens.size (fun k =>
      jCert.pts.toList.any (eqA 100 (conjA 100 aGens[g]! jGens[k]!)))) &&
    cyCert.pts.toList.all (fun c =>
      !(allLt jGens.size (fun k => commA 100 c jGens[k]!)) ||
        eqA 100 c (idA 100) || eqA 100 c u0)

@[expose] def tableOne (x : Array ℕ) : Bool :=
  !(eqA 100 (compA 100 x x) (idA 100) && !eqA 100 x (idA 100)) ||
    ((!(jCert.pts.toList.any (eqA 100 x)) ||
        (fixCnt x == 20 && fixCnt (compA 100 u0 x) == 0)) &&
      ((jCert.pts.toList.any (eqA 100 x)) || !(ord3J.any (fun b => commA 100 x b)) ||
        (fixCnt x == 20 && fixCnt (compA 100 u0 x) == 0) ||
        (fixCnt x == 0 && fixCnt (compA 100 u0 x) == 20)) &&
      ((jCert.pts.toList.any (eqA 100 x)) || (ord3J.any (fun b => commA 100 x b)) ||
        (fixCnt x == 0 && fixCnt (compA 100 u0 x) == 0)))

@[noinline, expose] def tableOK : Bool := aCert.pts.toList.all tableOne

@[noinline, expose] def s0OK : Bool := basicOK && classesOK && yOK && kOK && aOK && tableOK

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA.S0
