module

public import Certificates.Data.Kernel.HeModelK
public import CFSG.Certificates.Kernel.BfsPinBaseSound
public import CFSG.Certificates.Kernel.HeAutKLoops
public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec4HeModelsTests
import CFSG.Certificates.Kernel.HeModelKGlue
import CFSG.Certificates.Kernel.BfsPinSetSound

public section

namespace CFSG.KC.HeModelK

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw CFSG.KC.BfsPin CFSG.KC.HexaK CFSG.KC.HeAutK
open CFSG.Monster.B.Co2.Native CFSG.RankThree.Native CFSG.Monster.B.Fischer
open CFSG.ComponentClassification.AS81.HeSylow CFSG.ComponentClassification.AS81.Hexa
open CFSG.ComponentClassification.AS81.HeTri
open CFSG.KLie.CT (anyN andB orB notB)

structure HD where
  tG : List (Array ℕ)
  mG : List (Array ℕ)
  cG : List (Array ℕ)
  b0G : List (Array ℕ)
  f0G : List (Array ℕ)
  p23G : List (Array ℕ)
  pcG : List (Array ℕ)
  bcG : List (Array ℕ)
  p12cG : List (Array ℕ)
  p13cG : List (Array ℕ)
  ecG : List (Array ℕ)
  fcG : List (Array ℕ)
  zeta : Array ℕ
  t0 : Array ℕ
  tc : Array ℕ

@[expose] def heModelCheckG (h : HD) : Bool :=
  let TL := eltsK 64 base64 h.tG 64
  let ML := eltsK 64 base64 h.mG 2160
  let P12L := eltsK 64 base64 (h.tG ++ h.cG) 3072
  let BL := eltsK 64 base64 h.b0G 1024
  let FL := eltsK 64 base64 h.f0G 64
  let CL := eltsK 32 base32 h.pcG 21504
  let BCL := eltsK 32 base32 h.bcG 1024
  let P0L := eltsK 32 base32 h.p12cG 3072
  let P1L := eltsK 32 base32 h.p13cG 3072
  let U0L := eltsK 32 base32 h.ecG 64
  let U1L := eltsK 32 base32 h.fcG 64
  (enumCheckK 64 base64 h.tG 64 && enumCheckK 64 base64 h.mG 2160 &&
    enumCheckK 64 base64 (h.tG ++ h.cG) 3072 && enumCheckK 64 base64 h.b0G 1024 &&
    enumCheckK 64 base64 h.f0G 64 && enumCheckK 64 base64 h.p23G 9216 &&
    enumCheckK 32 base32 h.pcG 21504 && enumCheckK 32 base32 h.bcG 1024 &&
    enumCheckK 32 base32 h.p12cG 3072 && enumCheckK 32 base32 h.p13cG 3072 &&
    enumCheckK 32 base32 h.ecG 64 && enumCheckK 32 base32 h.fcG 64 &&
    validA 64 h.zeta && validA 64 h.t0 && validA 32 h.tc) &&
  (TL.all (fun t => !(inLN 64 ML t) || eqA 64 t (idA 64)) &&
    inLN 64 ML h.zeta && eqA 64 (powN 64 h.zeta 3) (idA 64) &&
    !(eqA 64 h.zeta (idA 64)) &&
    TL.all (fun t => !(commN 64 h.zeta t) || eqA 64 t (idA 64)) &&
    ML.all fun m => eqA 64 (conjA 64 m h.zeta) h.zeta ||
      eqA 64 (conjA 64 m h.zeta) (powN 64 h.zeta 2)) &&
  (TL.all fun t => eqA 64 t (idA 64) || ML.any (fun m => eqA 64 (conjA 64 m t) h.t0) ||
    ML.any fun m => commN 64 m t && eqA 64 (powN 64 m 5) (idA 64) && !(eqA 64 m (idA 64))) &&
  (h.tG.all (fun a => h.tG.all (commN 64 a)) && inLN 64 TL h.t0 &&
    h.cG.all (inLN 64 ML) && h.cG.all (fun g => commN 64 g h.t0) &&
    h.b0G.all (inLN 64 P12L) && h.tG.all (inLN 64 BL) &&
    h.f0G.all (inLN 64 BL) && FL.all (fun x => eqA 64 (mulN 64 x x) (idA 64)) &&
    FL.any (fun x => !(inLN 64 TL x)) && h.b0G.all (normsN 64 FL h.f0G) &&
    uniqEN 64 BL TL FL) &&
  (h.p23G.all (fun g => TL.any fun t => inLN 64 ML (compA 64 (invCand 64 t) g)) &&
    h.p23G.all (normsN 64 FL h.f0G) &&
    h.p23G.all (fun g => eqA 64 (powN 64 g 8) (idA 64)) &&
    (ML.filter (normsN 64 FL h.f0G)).length == 144) &&
  (inLN 32 CL h.tc &&
    CL.all (fun x => !(h.pcG.all (commN 32 x)) || eqA 32 x (idA 32) || eqA 32 x h.tc) &&
    h.bcG.all (inLN 32 P0L) && h.bcG.all (inLN 32 P1L) &&
    h.p12cG.all (inLN 32 CL) && h.p13cG.all (inLN 32 CL) &&
    h.ecG.all (inLN 32 P0L) && h.fcG.all (inLN 32 P1L) &&
    h.ecG.all (inLN 32 BCL) && h.fcG.all (inLN 32 BCL) &&
    U0L.all (fun x => eqA 32 (mulN 32 x x) (idA 32)) &&
    U1L.all (fun x => eqA 32 (mulN 32 x x) (idA 32)) &&
    inLN 32 U0L h.tc && inLN 32 U1L h.tc &&
    uniqEN 32 BCL U0L U1L &&
    h.p12cG.any (fun g => h.fcG.any fun f => !(inLN 32 U1L (conjA 32 g f))) &&
    h.p13cG.any (fun g => h.ecG.any fun f => !(inLN 32 U0L (conjA 32 g f))) &&
    CL.all (fun x => !(h.ecG.all (commN 32 x)) || inLN 32 U0L x) &&
    CL.all (fun x => !(h.fcG.all (commN 32 x)) || inLN 32 U1L x) &&
    h.p12cG.all (normsN 32 U0L h.ecG) && h.p13cG.all (normsN 32 U1L h.fcG)) &&
  ((CL.filter (stabW 2)).length == 3072 && (CL.filter (stabW 3)).length == 3072 &&
    P0L.all (stabW 2) && P1L.all (stabW 3) && (P0L.filter (stabW 3)).length == 1024 &&
    (CL.filter (unipW 2)).length == 64 && (CL.filter (unipW 3)).length == 64 &&
    U0L.all (unipW 2) && U1L.all (unipW 3) &&
    (CL.filter fun x => h.ecG.all fun f => unipW 2 (conjA 32 x f)).length == 3072 &&
    (CL.filter fun x => h.fcG.all fun f => unipW 3 (conjA 32 x f)).length == 3072)

@[expose] def heD : HD :=
  ⟨hexaTGens, hexaMGens, hexaCGens, heB0Gens, heF0Gens, heP23Gens, hePCGens, heBCGens, heP12CGens,
    heP13CGens, heECGens, heFCGens, heZetaArr, hexaT0, heTCArr⟩

structure PinB (n w : Nat) (ps : List Nat) (gs : List (Array Nat)) (g : Nat) (G : Nat → Nat) (N : Nat)
    (T E S : Nat → Nat) (SK : List Nat) : Prop where
  size : gs.toArray.size = g
  bind : ∀ k < g, gs.toArray[k]! = unpack n w (G k)
  perm : ∀ k < g, permOK n w (mask w) (n * w) (G k) (pinvS n w (mask w) (G k)) = true
  ok : bfsK n w g G N T E S = true
  keys : keysSK n w ps N T SK = true

structure HK where
  d64 : D64
  d32 : D32
  NP23 : Nat
  Z : Nat

theorem heModelCheck_eq : heModelCheck = heModelCheckG heD := rfl

namespace PinB

variable {n w : Nat} {ps : List Nat} {gs : List (Array Nat)} {g : Nat} {G : Nat → Nat} {N : Nat}
  {T E S : Nat → Nat} {SK : List Nat}

private theorem gen (p : PinB n w ps gs g G N T E S SK) : ∀ k < g, PP n w (G k) := PP_gen p.ok p.perm

private theorem pts (p : PinB n w ps gs g G N T E S SK) : ∀ i < N, PP n w (T i) := PP_pts p.ok p.perm

theorem gens (p : PinB n w ps gs g G N T E S SK) :
    gs = (List.range g).map fun k => unpack n w (G k) :=
  gens_eq p.size p.bind

theorem elts (p : PinB n w ps gs g G N T E S SK) (hps : ∀ q ∈ ps, q < n) {m : Nat} (hm : N = m) :
    eltsK n ps gs m = (List.range N).map fun i => unpack n w (T i) := by
  unfold eltsK certK
  rw [enumBfs_pts_base p.size p.bind p.ok hps p.keys (by omega)]
  exact pts_toList fun i => unpack n w (T i)

theorem check (p : PinB n w ps gs g G N T E S SK) (hps : ∀ q ∈ ps, q < n) {m : Nat}
    (hm : N = m) : enumCheckK n ps gs m = true := by
  subst hm
  unfold enumCheckK certK
  rw [enumOK_of_bfsK_base p.size p.bind p.perm p.ok hps p.keys (Nat.le_succ _),
    enumBfs_pts_base p.size p.bind p.ok hps p.keys (Nat.le_succ _), Bool.true_and,
    Array.size_ofFn]
  exact beq_self_eq_true N

end PinB

theorem cntRange_succ (d : D32) (lo k : Nat) :
    cntRange d lo (k + 1) = cntRange d lo k + cntAt d (lo + k) := by
  have h : ∀ y c, strictN y (fun a => Nat.add a c) = y + c := fun y c => by cases y <;> rfl
  exact h _ _

theorem cntRange_eq (d : D32) : ∀ N, cntRange d 0 N =
    ((List.range N).filter fun i => stabWK 6 2 (d.TC i)).length +
    65536 * ((List.range N).filter fun i => stabWK 6 3 (d.TC i)).length +
    4294967296 * ((List.range N).filter fun i => unipWK 6 2 (d.TC i)).length +
    281474976710656 * ((List.range N).filter fun i => unipWK 6 3 (d.TC i)).length +
    18446744073709551616 * ((List.range N).filter fun i =>
      allN d.gE fun j => unipWK 6 2 (conj 32 6 (d.TC i) (d.GE j))).length +
    1208925819614629174706176 * ((List.range N).filter fun i =>
      allN d.gF fun j => unipWK 6 3 (conj 32 6 (d.TC i) (d.GF j))).length
  | 0 => rfl
  | N + 1 => by
    rw [cntRange_succ, cntRange_eq d N, Nat.zero_add]
    simp only [length_filter_range_succ]
    unfold cntAt CFSG.KC.Q47K.bn
    simp only [strictN_eq', Nat.add_eq, Nat.mul_eq]
    omega

theorem cnt_decode {a b c d e f : Nat} (ha : a ≤ 21504) (hb : b ≤ 21504) (hc : c ≤ 21504)
    (hd : d ≤ 21504) (he : e ≤ 21504)
    (h : a + 65536 * b + 4294967296 * c + 281474976710656 * d + 18446744073709551616 * e +
      1208925819614629174706176 * f =
      3072 + 65536 * 3072 + 4294967296 * 64 + 281474976710656 * 64 +
        18446744073709551616 * 3072 + 1208925819614629174706176 * 3072) :
    a = 3072 ∧ b = 3072 ∧ c = 64 ∧ d = 64 ∧ e = 3072 ∧ f = 3072 := by
  omega

theorem heModelK_sound {h : HD} {k : HK}
    {cT cM cP cB cF cP23 cC cBC cP0 cP1 cU0 cU1 : Nat}
    {GT GM GP GB GF GP23 GC GBC GP0 GP1 GU0 GU1 : Nat → Nat}
    {ET EM EP EB EF EP23 EC EBC EP0 EP1 EU0 EU1 : Nat → Nat}
    {ST SM SP SB SF SP23 SC SBC SP0 SP1 SU0 SU1 : Nat → Nat}
    {KT KM KP KB KF KP23 KC KBC KP0 KP1 KU0 KU1 : List Nat} {TP23 : Nat → Nat}
    (pT : PinB 64 7 base64 h.tG cT GT k.d64.NT k.d64.TT ET ST KT)
    (pM : PinB 64 7 base64 h.mG cM GM k.d64.NM k.d64.TM EM SM KM)
    (pP : PinB 64 7 base64 (h.tG ++ h.cG) cP GP k.d64.NP k.d64.TP EP SP KP)
    (pB : PinB 64 7 base64 h.b0G cB GB k.d64.NB k.d64.TB EB SB KB)
    (pF : PinB 64 7 base64 h.f0G cF GF k.d64.NF k.d64.TF EF SF KF)
    (pP23 : PinB 64 7 base64 h.p23G cP23 GP23 k.NP23 TP23 EP23 SP23 KP23)
    (pC : PinB 32 6 base32 h.pcG cC GC k.d32.NC k.d32.TC EC SC KC)
    (pBC : PinB 32 6 base32 h.bcG cBC GBC k.d32.NBC k.d32.TBC EBC SBC KBC)
    (pP0 : PinB 32 6 base32 h.p12cG cP0 GP0 k.d32.N0 k.d32.T0 EP0 SP0 KP0)
    (pP1 : PinB 32 6 base32 h.p13cG cP1 GP1 k.d32.N1 k.d32.T1 EP1 SP1 KP1)
    (pU0 : PinB 32 6 base32 h.ecG cU0 GU0 k.d32.NU0 k.d32.TU0 EU0 SU0 KU0)
    (pU1 : PinB 32 6 base32 h.fcG cU1 GU1 k.d32.NU1 k.d32.TU1 EU1 SU1 KU1)
    (hsz : k.d64.NT = 64 ∧ k.d64.NM = 2160 ∧ k.d64.NP = 3072 ∧ k.d64.NB = 1024 ∧ k.d64.NF = 64 ∧
      k.NP23 = 9216 ∧ k.d32.NC = 21504 ∧ k.d32.NBC = 1024 ∧ k.d32.N0 = 3072 ∧ k.d32.N1 = 3072 ∧
      k.d32.NU0 = 64 ∧ k.d32.NU1 = 64)
    (hgen : k.d64.gT = cT ∧ k.d64.GT = GT ∧ h.cG.toArray.size = k.d64.gC ∧
      (∀ i < k.d64.gC, h.cG.toArray[i]! = unpack 64 7 (k.d64.GC i)) ∧ k.d64.gB = cB ∧ k.d64.GB = GB ∧
      k.d64.gF = cF ∧ k.d64.GF = GF ∧ k.d64.gP23 = cP23 ∧ k.d64.GP23 = GP23 ∧ k.d32.gPC = cC ∧
      k.d32.GPC = GC ∧ k.d32.gBC = cBC ∧ k.d32.GBC = GBC ∧ k.d32.g12 = cP0 ∧ k.d32.G12 = GP0 ∧
      k.d32.g13 = cP1 ∧ k.d32.G13 = GP1 ∧ k.d32.gE = cU0 ∧ k.d32.GE = GU0 ∧ k.d32.gF = cU1 ∧
      k.d32.GF = GU1)
    (hpC : ∀ i < k.d64.gC,
      permOK 64 7 (mask 7) (64 * 7) (k.d64.GC i) (pinvS 64 7 (mask 7) (k.d64.GC i)) = true)
    (hz : h.zeta = unpack 64 7 k.Z ∧ permOK 64 7 (mask 7) (64 * 7) k.Z (pinvS 64 7 (mask 7) k.Z) = true)
    (ht0 : h.t0 = unpack 64 7 k.d64.t0 ∧
      permOK 64 7 (mask 7) (64 * 7) k.d64.t0 (pinvS 64 7 (mask 7) k.d64.t0) = true)
    (htc : h.tc = unpack 32 6 k.d32.TCa ∧
      permOK 32 6 (mask 6) (32 * 6) k.d32.TCa (pinvS 32 6 (mask 6) k.d32.TCa) = true)
    (hZ : zetaK 7 k.d64.NT k.d64.TT k.d64.NM k.d64.TM k.Z = true)
    {WO : List Nat} (hO : ∀ i < k.d64.NT, orbAt 7 k.d64.TT k.d64.NM k.d64.TM k.d64.t0 WO i = true)
    (hB0 : b0K k.d64 = true)
    (hFB : flagsK 64 7 k.d64.NB k.d64.TB (pidn 64 7) k.d64.FB k.d64.FB = true)
    (hUB : allR (ueAt 64 7 k.d64.NB k.d64.TB k.d64.NT k.d64.TT k.d64.NF k.d64.TF k.d64.FB) 0
      k.d64.NB = true)
    (hC : cK k.d32 = true)
    (hCA : allR (cAt k.d32) 0 k.d32.NC = true)
    (hFBC : flagsK 32 6 k.d32.NBC k.d32.TBC (pidn 32 6) k.d32.FBC k.d32.FBC = true)
    (hUBC : allR (ueAt 32 6 k.d32.NBC k.d32.TBC k.d32.NU0 k.d32.TU0 k.d32.NU1 k.d32.TU1 k.d32.FBC) 0
      k.d32.NBC = true)
    (hCnt : cntRange k.d32 0 k.d32.NC =
      3072 + 65536 * 3072 + 4294967296 * 64 + 281474976710656 * 64 +
        18446744073709551616 * 3072 + 1208925819614629174706176 * 3072)
    (hCount : countK k.d32 = true) :
    heModelCheckG h = true := by
  obtain ⟨hNT, hNM, hNP, hNB, hNF, hNP23, hNC, hNBC, hN0, hN1, hNU0, hNU1⟩ := hsz
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18, e19,
    e20, e21, e22⟩ := hgen
  subst e1 e2 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22
  have hps64 : ∀ p ∈ base64, p < 64 := by decide
  have hps32 : ∀ p ∈ base32, p < 32 := by decide
  have sT := pT.pts
  have sM := pM.pts
  have sP := pP.pts
  have sB := pB.pts
  have sF := pF.pts
  have sC := pC.pts
  have sBC := pBC.pts
  have sP0 := pP0.pts
  have sP1 := pP1.pts
  have sU0 := pU0.pts
  have sU1 := pU1.pts
  have qT := pT.gen
  have qB := pB.gen
  have qF := pF.gen
  have qP23 := pP23.gen
  have qC := pC.gen
  have qBC := pBC.gen
  have qP0 := pP0.gen
  have qP1 := pP1.gen
  have qU0 := pU0.gen
  have qU1 := pU1.gen
  have h64 : szOK 64 7 = true := (sT 0 (by omega)).sz
  have h32 : szOK 32 6 = true := (sC 0 (by omega)).sz
  have pz : PP 64 7 k.Z := PP_of_permOK h64 hz.2
  have p0 : PP 64 7 k.d64.t0 := PP_of_permOK h64 ht0.2
  have ptc : PP 32 6 k.d32.TCa := PP_of_permOK h32 htc.2
  have qCg : ∀ i < k.d64.gC, PP 64 7 (k.d64.GC i) := fun i hi => PP_of_permOK h64 (hpC i hi)
  have cT := pT.check hps64 hNT
  have cM := pM.check hps64 hNM
  have cP := pP.check hps64 hNP
  have cB := pB.check hps64 hNB
  have cF := pF.check hps64 hNF
  have cP23 := pP23.check hps64 hNP23
  have cC := pC.check hps32 hNC
  have cBC := pBC.check hps32 hNBC
  have cP0 := pP0.check hps32 hN0
  have cP1 := pP1.check hps32 hN1
  have cU0 := pU0.check hps32 hNU0
  have cU1 := pU1.check hps32 hNU1
  have eT := pT.elts hps64 hNT
  have eM := pM.elts hps64 hNM
  have eP := pP.elts hps64 hNP
  have eB := pB.elts hps64 hNB
  have eF := pF.elts hps64 hNF
  have eC := pC.elts hps32 hNC
  have eBC := pBC.elts hps32 hNBC
  have eP0 := pP0.elts hps32 hN0
  have eP1 := pP1.elts hps32 hN1
  have eU0 := pU0.elts hps32 hNU0
  have eU1 := pU1.elts hps32 hNU1
  have gT := pT.gens
  have gM := pM.gens
  have gC : h.cG = (List.range k.d64.gC).map fun i => unpack 64 7 (k.d64.GC i) := gens_eq e3 e4
  have gB := pB.gens
  have gF := pF.gens
  have gP23 := pP23.gens
  have gPC := pC.gens
  have gBC := pBC.gens
  have gP0 := pP0.gens
  have gP1 := pP1.gens
  have gU0 := pU0.gens
  have gU1 := pU1.gens
  rw [gT] at cT
  rw [gM] at cM
  rw [gT, gC] at cP
  rw [gB] at cB
  rw [gF] at cF
  rw [gP23] at cP23
  rw [gPC] at cC
  rw [gBC] at cBC
  rw [gP0] at cP0
  rw [gP1] at cP1
  rw [gU0] at cU0
  rw [gU1] at cU1
  unfold zetaK at hZ
  simp only [andB_eq, Bool.and_eq_true] at hZ
  obtain ⟨z1, z2, z3, z4, z5, z6⟩ := hZ
  unfold b0K at hB0
  simp only [andB_eq, Bool.and_eq_true] at hB0
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14⟩ := hB0
  unfold cK at hC
  simp only [andB_eq, Bool.and_eq_true] at hC
  obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14⟩ := hC
  unfold countK at hCount
  simp only [andB_eq, Bool.and_eq_true] at hCount
  obtain ⟨k1, k2, k3, k4, k5⟩ := hCount
  have cA : ∀ i < k.d32.NC,
      CFSG.KLie.CT.orB (CFSG.KLie.CT.notB (allN k.d32.gPC fun j => comm 32 6 (k.d32.TC i) (k.d32.GPC j)))
          (CFSG.KLie.CT.orB (Nat.beq (k.d32.TC i) (pidn 32 6)) (Nat.beq (k.d32.TC i) k.d32.TCa)) = true ∧
        CFSG.KLie.CT.orB (CFSG.KLie.CT.notB (allN k.d32.gE fun j => comm 32 6 (k.d32.TC i) (k.d32.GE j)))
          (inL k.d32.NU0 k.d32.TU0 (k.d32.TC i)) = true ∧
        CFSG.KLie.CT.orB (CFSG.KLie.CT.notB (allN k.d32.gF fun j => comm 32 6 (k.d32.TC i) (k.d32.GF j)))
          (inL k.d32.NU1 k.d32.TU1 (k.d32.TC i)) = true := by
    intro i hi
    have c := allR_spec hCA i hi
    rw [Nat.zero_add] at c
    unfold cAt at c
    simp only [strictB_eq', andB_eq, Bool.and_eq_true] at c
    exact c
  have hle : ∀ p : Nat → Bool, ((List.range k.d32.NC).filter p).length ≤ 21504 := fun p => by
    have := List.length_filter_le p (List.range k.d32.NC)
    rw [List.length_range] at this
    omega
  obtain ⟨n1, n2, n3, n4, n5, n6⟩ := cnt_decode (hle _) (hle _) (hle _) (hle _) (hle _)
    ((cntRange_eq k.d32 k.d32.NC).symm.trans hCnt)
  unfold heModelCheckG
  dsimp only
  rw [eT, eM, eP, eB, eF, eC, eBC, eP0, eP1, eU0, eU1]
  rw [gT, gM, gC, gB, gF, gP23, gPC, gBC, gP0, gP1, gU0, gU1, hz.1, ht0.1, htc.1]
  simp only [Bool.and_eq_true]
  and_intros
  · exact cT
  · exact cM
  · exact cP
  · exact cB
  · exact cF
  · exact cP23
  · exact cC
  · exact cBC
  · exact cP0
  · exact cP1
  · exact cU0
  · exact cU1
  · exact validA_unpack hz.2
  · exact validA_unpack ht0.2
  · exact validA_unpack htc.2
  · exact all_map_allN (fun i hi => by
      rw [inLN_eq (sT i hi) sM, eqA_id_PP (sT i hi), strictB_eq', orB_eq, notB_eq]) z1
  · rw [inLN_eq pz sM]
    exact z2
  · rw [powN_PP pz, eqA_id_PP (pz.pwK 3)]
    exact z3
  · rw [eqA_id_PP pz]
    rw [notB_eq] at z4
    exact z4
  · exact all_map_allN (fun i hi => by
      rw [commN_PP pz (sT i hi), eqA_id_PP (sT i hi), strictB_eq', orB_eq, notB_eq]) z5
  · exact all_map_allN (fun i hi => by
      rw [conjA_PP (sM i hi) pz, eqA_PP ((sM i hi).conjK pz) pz, powN_PP pz,
        eqA_PP ((sM i hi).conjK pz) (pz.pwK 2), strictB_eq', orB_eq]) z6
  · refine all_map_intro fun i hi => ?_
    have o := hO i hi
    unfold orbAt at o
    rw [strictB_eq', orB_eq, Bool.or_eq_true] at o
    rw [eqA_id_PP (sT i hi)]
    simp only [Bool.or_eq_true]
    rcases o with o | o
    · exact Or.inl (Or.inl o)
    · rw [strictB_eq', strictB_eq', andB_eq, Bool.and_eq_true] at o
      obtain ⟨hj, o⟩ := o
      have hj' := Nat.blt_eq.mp hj
      rw [strictB_eq'] at o
      have pm := sM _ hj'
      cases hb : Nat.beq (Nat.land (WO.getD i 0) 1) 1
      · rw [hb] at o
        refine Or.inl (Or.inr (any_map_intro hj' ?_))
        rw [conjA_PP pm (sT i hi), eqA_PP (pm.conjK (sT i hi)) p0]
        exact o
      · rw [hb] at o
        simp only [andB_eq, notB_eq] at o
        refine Or.inr (any_map_intro hj' ?_)
        rw [commN_PP pm (sT i hi), powN_PP pm, eqA_id_PP (pm.pwK 5), eqA_id_PP pm, Bool.and_assoc]
        exact o
  · refine all_map_allN (fun a ha => ?_) b1
    rw [allN_eq']
    exact all_map_congr fun b hb => commN_PP (qT a ha) (qT b (List.mem_range.1 hb))
  · rw [inLN_eq p0 sT]
    exact b2
  · exact all_map_allN (fun j hj => inLN_eq (qCg j hj) sM) b3
  · exact all_map_allN (fun j hj => commN_PP (qCg j hj) p0) b4
  · exact all_map_allN (fun j hj => inLN_eq (qB j hj) sP) b5
  · exact all_map_allN (fun j hj => inLN_eq (qT j hj) sB) b6
  · exact all_map_allN (fun j hj => inLN_eq (qF j hj) sB) b7
  · exact all_map_allN (fun i hi => by
      rw [mulN_PP (sF i hi) (sF i hi), eqA_id_PP ((sF i hi).mul (sF i hi)), strictB_eq',
        mul_eq']) b8
  · exact any_map_anyN (fun i hi => by rw [inLN_eq (sF i hi) sT, notB_eq]) b9
  · exact all_map_allN (fun j hj => normsN_eq sF qF (qB j hj)) b10
  · exact uniqEN_of sB sT sF hFB hUB
  · refine all_map_allN (fun j hj => ?_) b11
    rw [strictB_eq', anyN_eq]
    refine any_map_congr fun i hi => ?_
    have pi := sT i (List.mem_range.1 hi)
    rw [invCand_PP pi, compA_PP pi.inv (qP23 j hj), inLN_eq (pi.inv.mul (qP23 j hj)) sM, mul_eq',
      inv_eq']
  · exact all_map_allN (fun j hj => normsN_eq sF qF (qP23 j hj)) b12
  · exact all_map_allN (fun j hj => by
      rw [powN_PP (qP23 j hj), eqA_id_PP ((qP23 j hj).pwK 8)]) b13
  · refine beq_iff_eq.2 ((filter_map_length ?_).trans
      ((cntR_zero _ _).symm.trans (Nat.eq_of_beq_eq_true b14)))
    exact fun i hi => normsN_eq sF qF (sM i hi)
  · rw [inLN_eq ptc sC]
    exact c1
  · refine all_map_intro fun i hi => ?_
    rw [all_commN_eq (sC i hi) qC, eqA_id_PP (sC i hi), eqA_PP (sC i hi) ptc, Bool.or_assoc]
    simpa only [orB_eq, notB_eq] using (cA i hi).1
  · exact all_map_allN (fun j hj => inLN_eq (qBC j hj) sP0) (allN_and c2).1
  · exact all_map_allN (fun j hj => inLN_eq (qBC j hj) sP1) (allN_and c2).2
  · exact all_map_allN (fun j hj => inLN_eq (qP0 j hj) sC) c3
  · exact all_map_allN (fun j hj => inLN_eq (qP1 j hj) sC) c4
  · exact all_map_allN (fun j hj => inLN_eq (qU0 j hj) sP0) (allN_and c5).1
  · exact all_map_allN (fun j hj => inLN_eq (qU1 j hj) sP1) (allN_and c6).1
  · exact all_map_allN (fun j hj => inLN_eq (qU0 j hj) sBC) (allN_and c5).2
  · exact all_map_allN (fun j hj => inLN_eq (qU1 j hj) sBC) (allN_and c6).2
  · exact all_map_allN (fun i hi => by
      rw [mulN_PP (sU0 i hi) (sU0 i hi), eqA_id_PP ((sU0 i hi).mul (sU0 i hi)), strictB_eq',
        mul_eq']) c7
  · exact all_map_allN (fun i hi => by
      rw [mulN_PP (sU1 i hi) (sU1 i hi), eqA_id_PP ((sU1 i hi).mul (sU1 i hi)), strictB_eq',
        mul_eq']) c8
  · rw [inLN_eq ptc sU0]
    exact c9
  · rw [inLN_eq ptc sU1]
    exact c10
  · exact uniqEN_of sBC sU0 sU1 hFBC hUBC
  · refine any_map_anyN (fun j hj => ?_) c11
    rw [anyN_eq]
    refine any_map_congr fun f hf => ?_
    have pf := qU1 f (List.mem_range.1 hf)
    rw [conjA_PP (qP0 j hj) pf, inLN_eq ((qP0 j hj).conjK pf) sU1, notB_eq]
  · refine any_map_anyN (fun j hj => ?_) c12
    rw [anyN_eq]
    refine any_map_congr fun f hf => ?_
    have pf := qU0 f (List.mem_range.1 hf)
    rw [conjA_PP (qP1 j hj) pf, inLN_eq ((qP1 j hj).conjK pf) sU0, notB_eq]
  · refine all_map_intro fun i hi => ?_
    rw [all_commN_eq (sC i hi) qU0, inLN_eq (sC i hi) sU0]
    simpa only [orB_eq, notB_eq] using (cA i hi).2.1
  · refine all_map_intro fun i hi => ?_
    rw [all_commN_eq (sC i hi) qU1, inLN_eq (sC i hi) sU1]
    simpa only [orB_eq, notB_eq] using (cA i hi).2.2
  · exact all_map_allN (fun j hj => normsN_eq sU0 qU0 (qP0 j hj)) c13
  · exact all_map_allN (fun j hj => normsN_eq sU1 qU1 (qP1 j hj)) c14
  · refine beq_iff_eq.2 ((filter_map_length ?_).trans n1)
    exact fun i _ => stabW_eq (by decide) _
  · refine beq_iff_eq.2 ((filter_map_length ?_).trans n2)
    exact fun i _ => stabW_eq (by decide) _
  · exact all_map_allN (fun i _ => stabW_eq (by decide) _) k1
  · exact all_map_allN (fun i _ => stabW_eq (by decide) _) k2
  · refine beq_iff_eq.2 ((filter_map_length ?_).trans
      ((cntR_zero _ _).symm.trans (Nat.eq_of_beq_eq_true k3)))
    exact fun i _ => stabW_eq (by decide) _
  · refine beq_iff_eq.2 ((filter_map_length ?_).trans n3)
    exact fun i _ => unipW_eq (by decide) _
  · refine beq_iff_eq.2 ((filter_map_length ?_).trans n4)
    exact fun i _ => unipW_eq (by decide) _
  · exact all_map_allN (fun i _ => unipW_eq (by decide) _) k4
  · exact all_map_allN (fun i _ => unipW_eq (by decide) _) k5
  · refine beq_iff_eq.2 ((filter_map_length ?_).trans n5)
    intro i hi
    rw [allN_eq']
    exact all_map_congr fun j hj => by
      have pj := qU0 j (List.mem_range.1 hj)
      rw [conjA_PP (sC i hi) pj, unipW_eq (by decide)]
  · refine beq_iff_eq.2 ((filter_map_length ?_).trans n6)
    intro i hi
    rw [allN_eq']
    exact all_map_congr fun j hj => by
      have pj := qU1 j (List.mem_range.1 hj)
      rw [conjA_PP (sC i hi) pj, unipW_eq (by decide)]

theorem allR_blocks (f : Nat → Bool) (k : Nat) :
    ∀ m, (∀ s < m, allR f (k * s) k = true) → allR f 0 (k * m) = true
  | 0, _ => rfl
  | m + 1, h => by
    rw [Nat.mul_succ, allR_add, Nat.zero_add, allR_blocks f k m (fun s hs => h s (by omega)),
      Bool.true_and]
    exact h m (by omega)

theorem cntRange_add (d : D32) (lo a b : Nat) :
    cntRange d lo (a + b) = cntRange d lo a + cntRange d (lo + a) b := by
  induction b with
  | zero => rfl
  | succ b ih =>
    rw [← Nat.add_assoc, cntRange_succ, ih, cntRange_succ, Nat.add_assoc, Nat.add_assoc lo a b]

end CFSG.KC.HeModelK

end
