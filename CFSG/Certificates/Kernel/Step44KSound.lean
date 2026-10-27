module

public import Certificates.Data.Kernel.Step44K
public import CFSG.Certificates.Kernel.HexaKSound
public import CFSG.Certificates.Kernel.HexaKGlue
import CFSG.Certificates.Kernel.HeSylKSound
import CFSG.Certificates.Kernel.HexaStabKGlue
import CFSG.Certificates.Kernel.BfsPinBaseSound
import CFSG.Certificates.Kernel.BfsPinSetSound

public section

namespace CFSG.KC.Step44K

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw CFSG.KC.BfsPin CFSG.KC.HexaK
open CFSG.Monster.B.Co2.Native CFSG.RankThree.Native CFSG.ComponentClassification.AS81.HeSylow
open CFSG.ComponentClassification.AS81.Hexa

@[expose] def v0AG (V : List (Array ℕ)) (i : ℕ) : Array ℕ := V[i]!

@[expose] def inV0AG (V : List (Array ℕ)) (x : Array ℕ) : Bool :=
  (List.range 4).any fun i => eqA 64 x (v0AG V i)

@[expose] def normV0AG (V : List (Array ℕ)) (m : Array ℕ) : Bool :=
  (List.range 4).all fun i => inV0AG V (conjA 64 m (v0AG V i))

@[expose] def sixTrivAG (V : List (Array ℕ)) (m : Array ℕ) : Bool :=
  [1, 2, 3].all (fun u => m[16 * u]! / 16 == u) &&
    (List.range 4).all fun j => eqA 64 (conjA 64 m (v0AG V j)) (v0AG V j)

@[expose] def v0CheckG (V : List (Array ℕ)) (om mu muPi : Array ℕ) (mG nG : List (Array ℕ)) :
    Bool :=
  let M := eltsN 64 mG
  let K := eltsN 64 (V ++ [om, mu])
  let W := eltsN 64 [om, mu]
  V.length == 4 && eqA 64 (v0AG V 0) (idA 64) &&
    (List.range 4).all (fun i => i == 0 || !(eqA 64 (v0AG V i) (idA 64))) &&
    (List.range 4).all (fun i => (List.range 4).all fun j =>
      eqA 64 (mulN 64 (v0AG V i) (v0AG V j)) (v0AG V (i ^^^ j))) &&
    (List.range 4).all (fun i => validA 64 (v0AG V i) && inLN 64 M (v0AG V i) &&
      fix16A (v0AG V i)) &&
    M.all (fun m => !(fix16A m) || inV0AG V m) &&
    validA 64 om && inLN 64 M om &&
    (List.range 64).all (fun v => v == 0 || om[v]! != v) &&
    eqA 64 (powN 64 om 3) (idA 64) &&
    (List.range 4).all (fun i => commN 64 om (v0AG V i)) &&
    validA 64 mu && inLN 64 M mu && eqA 64 (powN 64 mu 3) (idA 64) &&
    commN 64 mu om &&
    muPi.size == 4 && (List.range 4).all (fun i => decide (muPi[i]! < 4) &&
      eqA 64 (conjA 64 mu (v0AG V i)) (v0AG V muPi[i]!)) &&
    enumCheckN 64 (V ++ [om, mu]) 36 && enumCheckN 64 [om, mu] 9 &&
    K.all (fun k => (List.range 4).any fun i => inLN 64 W (mulN 64 (v0AG V i) k)) &&
    K.all (fun k => inV0AG V (powN 64 k 9)) &&
    M.all (fun m => !(normV0AG V m && inV0AG V (powN 64 m 9)) || inLN 64 K m) &&
    (M.filter (normV0AG V)).length == 144 && enumCheckN 64 nG 144 &&
    nG.all (fun m => inLN 64 M m && normV0AG V m) &&
    M.all (fun m => !(normV0AG V m) || (List.range 16).all fun v => decide (m[v]! < 16)) &&
    M.all (fun m => !(normV0AG V m && sixTrivAG V m) || inV0AG V m)

@[expose] def smStarG (V : List (Array ℕ)) (i j : ℕ) : ℕ :=
  ((i % 64) ^^^ (v0AG V (i / 64))[j % 64]!) + 64 * ((i / 64) ^^^ (j / 64))

@[expose] def omuAG (om mu : Array ℕ) (a b : ℕ) : Array ℕ :=
  mulN 64 (powN 64 om (a % 3)) (powN 64 mu (b % 3))

@[expose] def muPiNG (muPi : Array ℕ) : ℕ → ℕ → ℕ
  | 0, m => m
  | b + 1, m => muPi[muPiNG muPi b m]!

@[expose] def smTauG (om mu muPi : Array ℕ) (a b i : ℕ) : ℕ :=
  (omuAG om mu a b)[i % 64]! + 64 * muPiNG muPi (b % 3) (i / 64)

@[expose] def smCompG (om mu muPi : Array ℕ) (s1 s2 d : ℕ × ℕ) (y code : ℕ) : ℕ :=
  if code = 0 then 0 else
    smTauG om mu muPi (sigN s1 s2 ((code - 1) * d.1, (code - 1) * d.2)).1
      (sigN s1 s2 ((code - 1) * d.1, (code - 1) * d.2)).2 y

@[expose] def smCandAtG (V : List (Array ℕ)) (om mu muPi NF : Array ℕ) (s1 s2 : ℕ × ℕ)
    (y0 y1 y2 y3 i : ℕ) : ℕ :=
  smStarG V (smStarG V (smStarG V (smCompG om mu muPi s1 s2 (0, 1) y0 NF[4 * i]!)
    (smCompG om mu muPi s1 s2 (1, 0) y1 NF[4 * i + 1]!))
      (smCompG om mu muPi s1 s2 (0, 1) y2 NF[4 * i + 2]!))
    (smCompG om mu muPi s1 s2 (0, 1) y3 NF[4 * i + 3]!)

@[expose] def smCandG (V : List (Array ℕ)) (om mu muPi NF : Array ℕ) (s1 s2 : ℕ × ℕ)
    (y0 y1 y2 y3 : ℕ) : Array ℕ :=
  Array.ofFn fun i : Fin 256 => smCandAtG V om mu muPi NF s1 s2 y0 y1 y2 y3 i.val

@[expose] def smFixG (om mu muPi : Array ℕ) (s1 s2 k : ℕ × ℕ) : List ℕ :=
  (List.range 256).filter fun i =>
    i != 0 && smTauG om mu muPi (sigN s1 s2 k).1 (sigN s1 s2 k).2 i == i

@[expose] def smHomAG (V : List (Array ℕ)) (f : Array ℕ) : Bool :=
  (List.range 256).all fun i => (List.range 256).all fun j =>
    f[smStarG V i j]! == smStarG V f[i]! f[j]!

@[expose] def smAutNG (V : List (Array ℕ)) (om mu muPi NF : Array ℕ) (N : List (Array ℕ)) : Bool :=
  smSigmas.all fun s => (smFixG om mu muPi s.1 s.2 (1, 0)).all fun y0 =>
    (smFixG om mu muPi s.1 s.2 (0, 1)).all fun y1 =>
    (smFixG om mu muPi s.1 s.2 (1, 1)).all fun y2 => (smFixG om mu muPi s.1 s.2 (1, 2)).all fun y3 =>
      !(smHomAG V (smCandG V om mu muPi NF s.1 s.2 y0 y1 y2 y3)) ||
        inLN 256 N (smCandG V om mu muPi NF s.1 s.2 y0 y1 y2 y3)

@[expose] def smLamAG (V : List (Array ℕ)) (x : ℕ) : Array ℕ :=
  Array.ofFn fun i : Fin 256 => smStarG V x i.val

@[expose] def smLamGensG (V : List (Array ℕ)) : List (Array ℕ) :=
  [1, 2, 4, 8, 16, 32, 64, 128].map (smLamAG V)

@[expose] def smCheckG (V : List (Array ℕ)) (om mu muPi NF : Array ℕ)
    (NG NEG PG PEG Ab Aa y32 x16 : List (Array ℕ)) : Bool :=
  let N := eltsN 256 NG
  let NE := eltsN 256 NEG
  f3Pairs.all (fun c => f3Pairs.all fun c' => (List.range 256).all fun i =>
      smTauG om mu muPi c.1 c.2 (smTauG om mu muPi c'.1 c'.2 i) ==
        smTauG om mu muPi (c.1 + c'.1) (c.2 + c'.2) i) &&
    f3Pairs.all (fun c => c == (0, 0) || (List.range 256).any fun i => smTauG om mu muPi c.1 c.2 i != i) &&
    smTauG om mu muPi 1 0 64 == 64 && smTauG om mu muPi 0 1 30 == 30 &&
    smTauG om mu muPi 1 1 4 == 4 && smTauG om mu muPi 1 2 1 == 1 &&
    eqA 256 (smCandG V om mu muPi NF (1, 0) (0, 1) 64 30 4 1) (idA 256) &&
    enumCheckN 256 NG 72 && NG.all (smHomAG V) && smAutNG V om mu muPi NF N &&
    enumCheckN 256 NEG 36 && NEG.all (inLN 256 N) &&
    N.all (fun f => !(presTA f) || inLN 256 NE f) &&
    enumCheckN 256 PG 8 && PG.all (inLN 256 N) &&
    enumCheckN 256 PEG 4 && PEG.all (inLN 256 NE) &&
    enumCheckN 256 (smLamGensG V) 256 &&
    enumCheckN 256 (smLamGensG V ++ PG) 2048 &&
    enumCheckN 288 (List.zipWith (pairA 256) (smLamGensG V ++ PG) Ab) 2048 &&
    Ab.length == 10 && (smLamGensG V ++ PG).all (·.size == 256) &&
    Ab.all (·.size == 32) && enumCheckN 32 Ab 2048 &&
    enumCheckN 32 y32 2048 && y32.all (inLN 32 (eltsN 32 Ab)) &&
    enumCheckN 256 (smLamGensG V ++ PEG) 1024 &&
    enumCheckN 272 (List.zipWith (pairA 256) (smLamGensG V ++ PEG) Aa) 1024 &&
    Aa.length == 10 && (smLamGensG V ++ PEG).all (·.size == 256) &&
    Aa.all (·.size == 16) && enumCheckN 16 Aa 1024 &&
    enumCheckN 16 x16 1024 && x16.all (inLN 16 (eltsN 16 Aa))

@[expose] def step44CheckG (V : List (Array ℕ)) (om mu muPi : Array ℕ) (mG nG : List (Array ℕ))
    (NF : Array ℕ) (NG NEG PG PEG Ab Aa y32 x16 : List (Array ℕ)) : Bool :=
  v0CheckG V om mu muPi mG nG && smCheckG V om mu muPi NF NG NEG PG PEG Ab Aa y32 x16

theorem v0Check_eq : v0Check = v0CheckG hexaV0 hexaOmega hexaMu hexaMuPi hexaMGens
    hexaNormGens := rfl

theorem muPiN_eq : ∀ b m, muPiN b m = muPiNG hexaMuPi b m
  | 0, _ => rfl
  | b + 1, m => by rw [muPiN, muPiNG, muPiN_eq b m]

theorem smTau_eq (a b i : ℕ) : smTau a b i = smTauG hexaOmega hexaMu hexaMuPi a b i := by
  rw [smTau, smTauG, muPiN_eq]
  rfl

theorem smStar_eq (i j : ℕ) : smStar i j = smStarG hexaV0 i j := rfl

theorem smComp_eq (s1 s2 d : ℕ × ℕ) (y code : ℕ) :
    smComp s1 s2 d y code = smCompG hexaOmega hexaMu hexaMuPi s1 s2 d y code := by
  rw [smComp, smCompG, smTau_eq]

theorem smCand_eq (s1 s2 : ℕ × ℕ) (y0 y1 y2 y3 : ℕ) :
    smCand s1 s2 y0 y1 y2 y3 = smCandG hexaV0 hexaOmega hexaMu hexaMuPi hexaNF s1 s2 y0 y1 y2 y3 := by
  simp only [smCand, smCandG, smCandAt, smCandAtG, smComp_eq, smStar_eq]

theorem smFix_eq (s1 s2 k : ℕ × ℕ) : smFix s1 s2 k = smFixG hexaOmega hexaMu hexaMuPi s1 s2 k := by
  simp only [smFix, smFixG, smTau_eq]

theorem smHomA_eq (f : Array ℕ) : smHomA f = smHomAG hexaV0 f := by
  simp only [smHomA, smHomAG, smStar_eq]

theorem smAutN_eq (N : List (Array ℕ)) :
    smAutN N = smAutNG hexaV0 hexaOmega hexaMu hexaMuPi hexaNF N := by
  simp only [smAutN, smAutNG, smFix_eq, smCand_eq, smHomA_eq]

theorem smLamGens_eq : smLamGens = smLamGensG hexaV0 := by
  unfold smLamGens smLamGensG
  congr 1

theorem smCheck_eq : smCheck = smCheckG hexaV0 hexaOmega hexaMu hexaMuPi hexaNF hexaNGens
    hexaNEGens hexaPGens hexaPEGens hexaAbImgs hexaAaImgs
    CFSG.ComponentClassification.GrSLit.HeldFix.hfT0Tabs32.toList heSyl16 := by
  have h : smHomA = smHomAG hexaV0 := funext smHomA_eq
  simp only [smCheck, smCheckG, smTau_eq, smCand_eq, h, smAutN_eq, smLamGens_eq]

theorem step44Check_eq : step44Check = step44CheckG hexaV0 hexaOmega hexaMu hexaMuPi hexaMGens
    hexaNormGens hexaNF hexaNGens hexaNEGens hexaPGens hexaPEGens hexaAbImgs hexaAaImgs
    CFSG.ComponentClassification.GrSLit.HeldFix.hfT0Tabs32.toList heSyl16 := by
  rw [step44Check, step44CheckG, v0Check_eq, smCheck_eq]

@[expose] noncomputable def pairK (n m w wb a b : Nat) : Nat :=
  pmk (Nat.add n m) w fun i => nIf(Nat.blt i n, pg w (mask w) a i,
    Nat.add n (pg wb (mask wb) b (Nat.sub i n)))

structure LamPin (PV : Nat → Nat) (g : Nat) (GP : Nat → Nat) (G : Nat → Nat) (N : Nat)
    (T E S : Nat → Nat) : Prop where
  lam : ∀ k < 8, G k = pmk 256 9 (starK PV (2 ^ k))
  gens : ∀ k < g, G (8 + k) = GP k
  perm : ∀ k < 8 + g, permOK 256 9 (mask 9) (256 * 9) (G k) (pinvS 256 9 (mask 9) (G k)) = true
  ok : bfsK 256 9 (8 + g) G N T E S = true
  fuel : N ≤ 4000

structure PairPin (m : Nat) (GB GA : Nat → Nat) (wa : Nat) (G : Nat → Nat) (N : Nat)
    (T E S : Nat → Nat) : Prop where
  pair : ∀ k < 10, G k = pairK 256 m 9 wa (GB k) (GA k)
  perm : ∀ k < 10, permOK (256 + m) 9 (mask 9) ((256 + m) * 9) (G k)
    (pinvS (256 + m) 9 (mask 9) (G k)) = true
  ok : bfsK (256 + m) 9 10 G N T E S = true
  fuel : N ≤ 4000

open CFSG.KC.HeAutK (powN_PP pw_PP)
open CFSG.KLie.CT (anyN sumN andB orB notB)

theorem andB_true {a b : Bool} : CFSG.KLie.CT.andB a b = true ↔ a = true ∧ b = true := by
  rw [andB_eq, Bool.and_eq_true]

theorem all_pts {n w N : Nat} {T : Nat → Nat} {Q : Array Nat → Bool} {P : Nat → Bool}
    (hT : ∀ i < N, PP n w (T i)) (hQ : ∀ m, PP n w m → Q (unpack n w m) = P m)
    (h : allN N (fun k => strictB (T k) P) = true) :
    ((List.range N).map fun i => unpack n w (T i)).all Q = true := by
  rw [allN_eq'] at h
  refine (all_map_congr (q := fun k => strictB (T k) P) fun i hi => ?_).trans h
  rw [strictB_eq']
  exact hQ _ (hT i (List.mem_range.1 hi))

theorem all_gens {n w g : Nat} {G : Nat → Nat} {Q : Array Nat → Bool} {P : Nat → Bool}
    (hG : ∀ k < g, PP n w (G k)) (hQ : ∀ m, PP n w m → Q (unpack n w m) = P m)
    (h : allN g (fun k => P (G k)) = true) :
    ((List.range g).map fun k => unpack n w (G k)).all Q = true := by
  rw [allN_eq'] at h
  refine (all_map_congr (q := fun k => P (G k)) fun i hi => ?_).trans h
  exact hQ _ (hG i (List.mem_range.1 hi))

section V0

variable {V : List (Array ℕ)} {PV : Nat → Nat}

theorem V_eq (hV : V.length = 4 ∧ ∀ i < 4, V[i]! = unpack 64 7 (PV i) ∧
    permOK 64 7 (mask 7) (64 * 7) (PV i) (pinvS 64 7 (mask 7) (PV i)) = true) :
    V = (List.range 4).map fun i => unpack 64 7 (PV i) := by
  apply List.ext_getElem (by simp [hV.1])
  intro k h1 _
  have e := (hV.2 k (hV.1 ▸ h1)).1
  rw [getElem!_pos V k h1] at e
  rw [e, List.getElem_map, List.getElem_range]

theorem v0AG_eq (hV : V = (List.range 4).map fun i => unpack 64 7 (PV i)) {i : Nat} (hi : i < 4) :
    v0AG V i = unpack 64 7 (PV i) := by
  unfold v0AG
  rw [hV, getElem!_map_range _ hi]

variable (hV : V = (List.range 4).map fun i => unpack 64 7 (PV i)) (hPV : ∀ i < 4, PP 64 7 (PV i))
include hV hPV

theorem inV0AG_eq {m : Nat} (hm : PP 64 7 m) : inV0AG V (unpack 64 7 m) = inV0 PV m := by
  unfold inV0AG inV0
  rw [strictB_eq', anyN_eq]
  refine any_congr_mem fun i hi => ?_
  have hi' := List.mem_range.1 hi
  rw [v0AG_eq hV hi', eqA_PP hm (hPV i hi')]

theorem normV0AG_eq {m : Nat} (hm : PP 64 7 m) : normV0AG V (unpack 64 7 m) = normV0 PV m := by
  unfold normV0AG normV0
  rw [allN_eq']
  refine all_congr_mem fun i hi => ?_
  have hi' := List.mem_range.1 hi
  rw [v0AG_eq hV hi', conjA_PP hm (hPV i hi'), inV0AG_eq hV hPV (hm.conjK (hPV i hi'))]

theorem sixTrivAG_eq {m : Nat} (hm : PP 64 7 m) : sixTrivAG V (unpack 64 7 m) = sixTriv PV m := by
  unfold sixTrivAG sixTriv
  rw [andB_eq, allN_eq', allN_eq']
  have e1 : ([1, 2, 3].all fun u => (unpack 64 7 m)[16 * u]! / 16 == u) =
      (List.range 3).all fun u =>
        Nat.beq (Nat.div (pg 7 (mask 7) m (Nat.mul 16 (Nat.succ u))) 16) (Nat.succ u) := by
    have e : List.range 3 = [0, 1, 2] := rfl
    rw [e]
    simp only [List.all_cons, List.all_nil, Bool.and_true, unpack_getElem!, beq_nat]
    rfl
  have e2 : ((List.range 4).all fun j =>
      eqA 64 (conjA 64 (unpack 64 7 m) (v0AG V j)) (v0AG V j)) =
      (List.range 4).all fun j => Nat.beq (conj 64 7 m (PV j)) (PV j) := by
    refine all_congr_mem fun j hj => ?_
    have hj' := List.mem_range.1 hj
    rw [v0AG_eq hV hj', conjA_PP hm (hPV j hj'), eqA_PP (hm.conjK (hPV j hj')) (hPV j hj')]
  rw [e1, e2]

omit hV hPV in
theorem fix16A_eq (m : Nat) : fix16A (unpack 64 7 m) = fix16 m := by
  unfold fix16A fix16
  rw [allN_eq']
  refine all_congr_mem fun v hv => ?_
  have hv' : v < 64 := by have := List.mem_range.1 hv; omega
  rw [unpack_getElem!, ite_eq_left hv', beq_nat]

end V0

theorem v0CheckG_of {V : List (Array ℕ)} {om mu muPi : Array ℕ} {mG nG : List (Array ℕ)}
    {PV : Nat → Nat} {Om Mu : Nat} {MP : Nat → Nat}
    {cM NM cK NK cW NW cH NH : Nat}
    {GM TM EM SM GK TK EK SK GW TW EW SW GH TH EH SH : Nat → Nat}
    (hV : V.length = 4 ∧ ∀ i < 4, V[i]! = unpack 64 7 (PV i) ∧
      permOK 64 7 (mask 7) (64 * 7) (PV i) (pinvS 64 7 (mask 7) (PV i)) = true)
    (hom : om = unpack 64 7 Om) (hmu : mu = unpack 64 7 Mu)
    (hpo : permOK 64 7 (mask 7) (64 * 7) Om (pinvS 64 7 (mask 7) Om) = true)
    (hpm : permOK 64 7 (mask 7) (64 * 7) Mu (pinvS 64 7 (mask 7) Mu) = true)
    (hmp : muPi.size = 4 ∧ ∀ i < 4, muPi[i]! = MP i)
    (pM : Pin 64 7 mG cM GM NM TM EM SM) (pK : Pin 64 7 (V ++ [om, mu]) cK GK NK TK EK SK)
    (pW : Pin 64 7 [om, mu] cW GW NW TW EW SW) (pH : Pin 64 7 nG cH GH NH TH EH SH)
    (hNK : NK = 36) (hNW : NW = 9) (hNH : NH = 144)
    (hv0 : v0K PV Om Mu MP NM TM NK TK NW TW cH GH = true) :
    v0CheckG V om mu muPi mG nG = true := by
  have hsz : szOK 64 7 = true := by
    have h := pM.ok
    unfold bfsK at h
    simp only [bAnd_iff] at h
    exact h.1
  have hV' := V_eq hV
  have hPV : ∀ i < 4, PP 64 7 (PV i) := fun i hi => PP_of_permOK hsz (hV.2 i hi).2
  have po : PP 64 7 Om := PP_of_permOK hsz hpo
  have pm : PP 64 7 Mu := PP_of_permOK hsz hpm
  have sM := PP_pts pM.ok pM.perm
  have sK := PP_pts pK.ok pK.perm
  have sW := PP_pts pW.ok pW.perm
  have qH := PP_gen pH.ok pH.perm
  have hid : PP 64 7 (pidn 64 7) := PP.id hsz
  have cK := enumCheckN_of pK.size pK.bind pK.perm pK.ok pK.fuel
  have cW := enumCheckN_of pW.size pW.bind pW.perm pW.ok pW.fuel
  have cH := enumCheckN_of pH.size pH.bind pH.perm pH.ok pH.fuel
  rw [hNK] at cK
  rw [hNW] at cW
  rw [hNH] at cH
  have eM := eltsN_eq pM.size pM.bind pM.ok pM.fuel
  have eK := eltsN_eq pK.size pK.bind pK.ok pK.fuel
  have eW := eltsN_eq pW.size pW.bind pW.ok pW.fuel
  have gH := gens_eq pH.size pH.bind
  have v0 := fun {i : Nat} (hi : i < 4) => v0AG_eq hV' hi
  unfold v0K at hv0
  simp only [andB_eq, Bool.and_eq_true] at hv0
  obtain ⟨k1, k2, k3, k4, k5, k6, k7, k8, k9, k10, k11, k12, k13, k14, k15, k16, k17, k18, k19,
    k20⟩ := hv0
  subst hom hmu
  unfold v0CheckG
  rw [eM, eK, eW]
  simp only [Bool.and_eq_true, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, validA_unpack hpo, ?_, ?_, ?_, ?_, validA_unpack hpm, ?_, ?_, ?_,
    ?_, ?_, cK, cW, ?_, ?_, ?_, ?_, cH, ?_, ?_, ?_⟩
  · rw [hV.1]
    rfl
  · rw [v0 (by decide), eqA_id_PP (hPV 0 (by decide))]
    exact k1
  · rw [allN_eq'] at k2
    refine (all_congr_mem fun i hi => ?_).trans k2
    have hi' := List.mem_range.1 hi
    rw [v0 hi', eqA_id_PP (hPV i hi'), orB_eq, notB_eq, beq_nat]
  · rw [allN_eq'] at k3
    refine (all_congr_mem fun i hi => ?_).trans k3
    have hi' := List.mem_range.1 hi
    rw [allN_eq']
    refine all_congr_mem fun j hj => ?_
    have hj' := List.mem_range.1 hj
    have hx : i ^^^ j < 4 := Nat.xor_lt_two_pow (n := 2) hi' hj'
    rw [v0 hi', v0 hj', v0 hx, mulN_PP (hPV i hi') (hPV j hj'),
      eqA_PP ((hPV i hi').mul (hPV j hj')) (hPV _ hx)]
    rfl
  · refine List.all_eq_true.2 fun i hi => ?_
    have hi' := List.mem_range.1 hi
    have h := allN_spec k4 i hi'
    rw [v0 hi', validA_unpack (hV.2 i hi').2, inLN_eq (hPV i hi') sM, fix16A_eq, Bool.true_and]
    exact h
  · exact all_pts sM (fun m hm => by rw [fix16A_eq, inV0AG_eq hV' hPV hm, orB_eq, notB_eq]) k5
  · rw [inLN_eq po sM]
    exact k6
  · rw [allN_eq'] at k7
    refine (all_congr_mem fun v hv => ?_).trans k7
    rw [unpack_getElem!, ite_eq_left (List.mem_range.1 hv)]
    simp only [bne, beq_nat, orB_eq, notB_eq]
  · rw [powN_PP po 3, eqA_id_PP (pw_PP po 3)]
    exact k8
  · rw [allN_eq'] at k9
    refine (all_congr_mem fun i hi => ?_).trans k9
    have hi' := List.mem_range.1 hi
    rw [v0 hi', commN_PP po (hPV i hi')]
  · rw [inLN_eq pm sM]
    exact k10
  · rw [powN_PP pm 3, eqA_id_PP (pw_PP pm 3)]
    exact k11
  · rw [commN_PP pm po]
    exact k12
  · rw [hmp.1]
    rfl
  · refine List.all_eq_true.2 fun i hi => ?_
    have hi' := List.mem_range.1 hi
    have h := allN_spec k13 i hi'
    rw [Bool.and_eq_true] at h
    have hlt := Nat.blt_eq.mp h.1
    rw [hmp.2 i hi', v0 hi', v0 hlt, conjA_PP pm (hPV i hi'),
      eqA_PP (pm.conjK (hPV i hi')) (hPV _ hlt), decide_eq_true hlt, Bool.true_and]
    exact h.2
  · refine all_pts sK (fun m hm => ?_) k14
    rw [anyN_eq]
    refine any_congr_mem fun i hi => ?_
    have hi' := List.mem_range.1 hi
    rw [v0 hi', mulN_PP (hPV i hi') hm, inLN_eq ((hPV i hi').mul hm) sW]
    rfl
  · exact all_gens sK (fun m hm => by rw [powN_PP hm 9, inV0AG_eq hV' hPV (pw_PP hm 9)]) k15
  · exact all_pts sM (fun m hm => by
      rw [normV0AG_eq hV' hPV hm, powN_PP hm 9, inV0AG_eq hV' hPV (pw_PP hm 9), inLN_eq hm sK,
        orB_eq, notB_eq]) k16
  · unfold normCount at k17
    rw [sumN_count] at k17
    rw [List.filter_map, List.length_map, beq_iff_eq, ← Nat.eq_of_beq_eq_true k17]
    exact congrArg List.length (List.filter_congr fun j hj => by
      rw [Function.comp_apply, normV0AG_eq hV' hPV (sM j (List.mem_range.1 hj))])
  · rw [gH]
    exact all_gens qH (fun m hm => by rw [inLN_eq hm sM, normV0AG_eq hV' hPV hm]) k18
  · refine all_pts sM (fun m hm => ?_) k19
    have e : ((List.range 16).all fun v => decide ((unpack 64 7 m)[v]! < 16)) =
        (List.range 16).all fun v => Nat.blt (pg 7 (mask 7) m v) 16 := by
      refine all_congr_mem fun v hv => ?_
      have hv' : v < 64 := by have := List.mem_range.1 hv; omega
      rw [unpack_getElem!, ite_eq_left hv', blt_eq_decide]
    rw [normV0AG_eq hV' hPV hm, orB_eq, notB_eq, allN_eq', e]
  · exact all_pts sM (fun m hm => by
      rw [normV0AG_eq hV' hPV hm, sixTrivAG_eq hV' hPV hm, inV0AG_eq hV' hPV hm, orB_eq,
        notB_eq]) k20

theorem canonK_pmk {n w : Nat} {f : Nat → Nat} (hn : n < 16777216) (hw : n + 1 < 2 ^ w)
    (hf : ∀ x < n, f x < n) : canonK n w (mask w) (n * w) (pmk n w f) = true := by
  have hf' : ∀ x < n, f x < 2 ^ w := fun x hx => by have := hf x hx; omega
  unfold canonK szOK
  rw [bAnd_iff, bAnd_iff, bAnd_iff, Nat.blt_eq, Nat.blt_eq, Nat.beq_eq]
  refine ⟨⟨hn, ?_⟩, ?_, allN_intro fun i hi => Nat.blt_eq.mpr ?_⟩
  · change n + 1 < 1 <<< w
    rw [Nat.shiftLeft_eq, Nat.one_mul]
    exact hw
  · exact PF.shr_zero_of_fld (PF.w_pos hw) (CFSG.KC.HexaStabK.fld_pmk hn hf') fun i hi => by
      have : ¬ i < n := by omega
      simp [this]
  · rw [CFSG.KC.HexaStabK.pg_pmk hn hf' hi]
    exact hf i hi

theorem inLN_canon {n w N x : Nat} {T : Nat → Nat} (hx : canonK n w (mask w) (n * w) x = true)
    (hT : ∀ i < N, PP n w (T i)) :
    inLN n ((List.range N).map fun i => unpack n w (T i)) (unpack n w x) = HexaK.inL N T x := by
  unfold inLN HexaK.inL
  rw [strictB_eq', anyN_eq, List.any_map]
  refine any_congr_mem fun j hj => ?_
  rw [Function.comp_apply, eqA_unpack hx (hT j (List.mem_range.1 hj)).1]

theorem unpack_get {n w P x : Nat} (hx : x < n) : (unpack n w P)[x]! = pg w (mask w) P x := by
  rw [unpack_getElem!, ite_eq_left hx]

theorem muPiK_lt {MP : Nat → Nat} (hMP : ∀ i < 4, MP i < 4) {m : Nat} (hm : m < 4) :
    ∀ k, muPiK MP k m < 4
  | 0 => hm
  | k + 1 => hMP _ (muPiK_lt hMP hm k)

theorem muPi_eq {muPi : Array ℕ} {MP : Nat → Nat} (hmp : ∀ i < 4, muPi[i]! = MP i)
    (hMP : ∀ i < 4, MP i < 4) {m : Nat} (hm : m < 4) : ∀ k, muPiNG muPi k m = muPiK MP k m
  | 0 => rfl
  | k + 1 => by
    have e1 : muPiK MP (k + 1) m = MP (muPiK MP k m) := rfl
    rw [muPiNG, e1, muPi_eq hmp hMP hm k, hmp _ (muPiK_lt hMP hm k)]

theorem filt_rec (f : Nat → Bool) : ∀ M acc,
    Nat.rec (motive := fun _ => List Nat → List Nat) (fun acc => acc)
      (fun r ih acc => Bool.rec (motive := fun _ => List Nat) (ih acc) (ih (r :: acc)) (f r)) M acc =
      (List.range M).filter f ++ acc
  | 0, acc => rfl
  | M + 1, acc => by
    change Bool.rec (motive := fun _ => List Nat) _ _ (f M) = _
    rw [List.range_succ, List.filter_append]
    cases h : f M
    · change Nat.rec (motive := fun _ => List Nat → List Nat) _ _ M acc = _
      rw [filt_rec f M acc]
      simp [h]
    · change Nat.rec (motive := fun _ => List Nat → List Nat) _ _ M (M :: acc) = _
      rw [filt_rec f M (M :: acc)]
      simp [h]

theorem strictL_eq (y : Nat) (k : Nat → List Nat) : strictL y k = k y := by cases y <;> rfl

theorem fixRec (MP : Nat → Nat) (o b M : Nat) :
    Nat.rec (motive := fun _ => List Nat → List Nat) (fun acc => acc)
      (fun r ih acc => Bool.rec (motive := fun _ => List Nat) (ih acc) (ih (r :: acc))
        (CFSG.KLie.CT.andB (CFSG.KLie.CT.notB (Nat.beq r 0)) (Nat.beq (tauO MP o b r) r))) M [] =
      (List.range M).filter fun r => CFSG.KLie.CT.andB (CFSG.KLie.CT.notB (Nat.beq r 0)) (Nat.beq (tauO MP o b r) r) :=
  (filt_rec _ M []).trans (List.append_nil _)

section SM

variable {V : List (Array ℕ)} {PV : Nat → Nat} {Om Mu : Nat} {MP : Nat → Nat} {muPi : Array ℕ}

theorem omuK_PP (po : PP 64 7 Om) (pm : PP 64 7 Mu) (a b : Nat) : PP 64 7 (omuK Om Mu a b) :=
  (pw_PP po _).mul (pw_PP pm _)

theorem omuAG_eq (po : PP 64 7 Om) (pm : PP 64 7 Mu) (a b : Nat) :
    omuAG (unpack 64 7 Om) (unpack 64 7 Mu) a b = unpack 64 7 (omuK Om Mu a b) := by
  unfold omuAG
  rw [powN_PP po, powN_PP pm, mulN_PP (pw_PP po _) (pw_PP pm _)]
  rfl

theorem tau_eq (po : PP 64 7 Om) (pm : PP 64 7 Mu) (hmp : ∀ i < 4, muPi[i]! = MP i)
    (hMP : ∀ i < 4, MP i < 4) {i : Nat} (hi : i < 256) (a b : Nat) :
    smTauG (unpack 64 7 Om) (unpack 64 7 Mu) muPi a b i = tauK Om Mu MP a b i := by
  unfold smTauG
  rw [omuAG_eq po pm, unpack_get (Nat.mod_lt i (by decide)),
    muPi_eq hmp hMP (by omega : i / 64 < 4) (b % 3)]
  rfl

theorem tau_lt (po : PP 64 7 Om) (pm : PP 64 7 Mu) (hMP : ∀ i < 4, MP i < 4) {i : Nat}
    (hi : i < 256) (a b : Nat) : tauK Om Mu MP a b i < 256 := by
  have h1 : pg 7 (mask 7) (omuK Om Mu a b) (i % 64) < 64 :=
    (omuK_PP po pm a b).2.1 _ (Nat.mod_lt i (by decide))
  have h2 := muPiK_lt hMP (by omega : i / 64 < 4) (b % 3)
  change pg 7 (mask 7) (omuK Om Mu a b) (i % 64) + 64 * muPiK MP (b % 3) (i / 64) < 256
  omega

theorem star_eq (hV : V = (List.range 4).map fun i => unpack 64 7 (PV i)) {i : Nat} (hi : i < 256)
    (j : Nat) : smStarG V i j = starK PV i j := by
  unfold smStarG starK
  rw [v0AG_eq hV (by omega : i / 64 < 4), unpack_get (Nat.mod_lt j (by decide))]
  rfl

theorem starK_lt (hPV : ∀ i < 4, PP 64 7 (PV i)) {i j : Nat} (hi : i < 256) (hj : j < 256) :
    starK PV i j < 256 := by
  have h1 : Nat.xor (i % 64) (pg 7 (mask 7) (PV (i / 64)) (j % 64)) < 64 :=
    Nat.xor_lt_two_pow (n := 6) (Nat.mod_lt i (by decide))
      ((hPV _ (by omega)).2.1 _ (Nat.mod_lt j (by decide)))
  have h2 : Nat.xor (i / 64) (j / 64) < 4 := Nat.xor_lt_two_pow (n := 2) (by omega) (by omega)
  change Nat.xor (i % 64) (pg 7 (mask 7) (PV (i / 64)) (j % 64)) +
    64 * Nat.xor (i / 64) (j / 64) < 256
  omega

theorem comp_eq (po : PP 64 7 Om) (pm : PP 64 7 Mu) (hmp : ∀ i < 4, muPi[i]! = MP i)
    (hMP : ∀ i < 4, MP i < 4) {y : Nat} (hy : y < 256) (s1 s2 d : ℕ × ℕ) (code : ℕ) :
    smCompG (unpack 64 7 Om) (unpack 64 7 Mu) muPi s1 s2 d y code = compK Om Mu MP s1 s2 d y code := by
  unfold smCompG compK
  rw [nIf_ite, tau_eq po pm hmp hMP hy]
  by_cases h : code = 0
  · subst h
    rfl
  · have e : Nat.beq code 0 = false := by
      cases e : Nat.beq code 0
      · rfl
      · exact absurd (Nat.eq_of_beq_eq_true e) h
    simp [h, e]

theorem comp_lt (po : PP 64 7 Om) (pm : PP 64 7 Mu) (hMP : ∀ i < 4, MP i < 4) {y : Nat}
    (hy : y < 256) (s1 s2 d : ℕ × ℕ) (code : ℕ) : compK Om Mu MP s1 s2 d y code < 256 := by
  unfold compK
  rw [nIf_ite]
  split
  · decide
  · exact tau_lt po pm hMP hy _ _

variable (hV : V = (List.range 4).map fun i => unpack 64 7 (PV i)) (hPV : ∀ i < 4, PP 64 7 (PV i))
  (po : PP 64 7 Om) (pm : PP 64 7 Mu) (hmp : ∀ i < 4, muPi[i]! = MP i) (hMP : ∀ i < 4, MP i < 4)
include hV hPV po pm hmp hMP

theorem candAt_eq {NFP : Nat} (s1 s2 : ℕ × ℕ) {y0 y1 y2 y3 i : Nat} (hi : i < 256)
    (hy0 : y0 < 256) (hy1 : y1 < 256) (hy2 : y2 < 256) (hy3 : y3 < 256) :
    smCandAtG V (unpack 64 7 Om) (unpack 64 7 Mu) muPi (unpack 1024 2 NFP) s1 s2 y0 y1 y2 y3 i =
      candAtK PV Om Mu MP NFP s1 s2 y0 y1 y2 y3 i ∧
    candAtK PV Om Mu MP NFP s1 s2 y0 y1 y2 y3 i < 256 := by
  have c0 := comp_lt po pm hMP hy0 s1 s2 (0, 1) (pg 2 (mask 2) NFP (4 * i))
  have c1 := comp_lt po pm hMP hy1 s1 s2 (1, 0) (pg 2 (mask 2) NFP (4 * i + 1))
  have c2 := comp_lt po pm hMP hy2 s1 s2 (0, 1) (pg 2 (mask 2) NFP (4 * i + 2))
  have c3 := comp_lt po pm hMP hy3 s1 s2 (0, 1) (pg 2 (mask 2) NFP (4 * i + 3))
  have d01 := starK_lt hPV c0 c1
  have d012 := starK_lt hPV d01 c2
  unfold smCandAtG
  rw [unpack_get (by omega : 4 * i < 1024), unpack_get (by omega : 4 * i + 1 < 1024),
    unpack_get (by omega : 4 * i + 2 < 1024), unpack_get (by omega : 4 * i + 3 < 1024),
    comp_eq po pm hmp hMP hy0, comp_eq po pm hmp hMP hy1, comp_eq po pm hmp hMP hy2,
    comp_eq po pm hmp hMP hy3, star_eq hV c0, star_eq hV d01, star_eq hV d012]
  exact ⟨rfl, starK_lt hPV d012 c3⟩

theorem canonK_candK {NFP : Nat} (s1 s2 : ℕ × ℕ) {y0 y1 y2 y3 : Nat} (hy0 : y0 < 256)
    (hy1 : y1 < 256) (hy2 : y2 < 256) (hy3 : y3 < 256) :
    canonK 256 9 (mask 9) (256 * 9) (candK PV Om Mu MP NFP s1 s2 y0 y1 y2 y3) = true :=
  canonK_pmk (by norm_num) (by norm_num) fun _ hx =>
    (candAt_eq hV hPV po pm hmp hMP s1 s2 hx hy0 hy1 hy2 hy3).2

theorem cand_eq {NFP : Nat} (s1 s2 : ℕ × ℕ) {y0 y1 y2 y3 : Nat} (hy0 : y0 < 256)
    (hy1 : y1 < 256) (hy2 : y2 < 256) (hy3 : y3 < 256) :
    smCandG V (unpack 64 7 Om) (unpack 64 7 Mu) muPi (unpack 1024 2 NFP) s1 s2 y0 y1 y2 y3 =
      unpack 256 9 (candK PV Om Mu MP NFP s1 s2 y0 y1 y2 y3) := by
  unfold smCandG candK
  rw [CFSG.KC.HexaStabK.unpack_pmk (by norm_num) fun _ hx => Nat.lt_trans
    (candAt_eq hV hPV po pm hmp hMP s1 s2 hx hy0 hy1 hy2 hy3).2 (by norm_num)]
  exact congrArg (Array.ofFn (n := 256)) (funext fun x =>
    (candAt_eq hV hPV po pm hmp hMP s1 s2 x.2 hy0 hy1 hy2 hy3).1)

omit hV hPV in
theorem fixK_eq (s1 s2 k : ℕ × ℕ) :
    fixK Om Mu MP s1 s2 k = smFixG (unpack 64 7 Om) (unpack 64 7 Mu) muPi s1 s2 k := by
  unfold fixK smFixG
  rw [strictL_eq, fixRec]
  refine List.filter_congr fun i hi => ?_
  rw [tau_eq po pm hmp hMP (List.mem_range.1 hi), andB_eq, notB_eq]
  simp only [bne, beq_nat]
  rfl

omit hV hPV po pm hmp hMP in
theorem lt_of_mem_smFixG {om mu : Array ℕ} {s1 s2 k : ℕ × ℕ} {y : Nat}
    (h : y ∈ smFixG om mu muPi s1 s2 k) : y < 256 := by
  unfold smFixG at h
  exact List.mem_range.1 (List.mem_filter.1 h).1

omit po pm hmp hMP in
theorem homA_eq {F : Nat} (hF : canonK 256 9 (mask 9) (256 * 9) F = true) :
    smHomAG V (unpack 256 9 F) = homK PV F := by
  obtain ⟨-, -, -, hlt⟩ := PF.canon_facts hF
  unfold smHomAG homK
  rw [allN_eq']
  refine all_congr_mem fun i hi => ?_
  have hi' := List.mem_range.1 hi
  rw [allN_eq']
  refine all_congr_mem fun j hj => ?_
  have hj' := List.mem_range.1 hj
  rw [unpack_get hi', unpack_get hj', star_eq hV hi', unpack_get (starK_lt hPV hi' hj'),
    star_eq hV (hlt i hi'), beq_nat]

end SM

theorem presTA_eq (F : Nat) : presTA (unpack 256 9 F) = presT F := by
  unfold presTA presT
  rw [allN_eq']
  refine all_congr_mem fun i hi => ?_
  have hi' : i < 256 := by have := List.mem_range.1 hi; omega
  rw [unpack_get hi', blt_eq_decide]

theorem pin_of_eq {n w : Nat} {gs : List (Array Nat)} {g N : Nat} {G T E S : Nat → Nat}
    (hgs : gs = (List.range g).map fun k => unpack n w (G k))
    (hp : ∀ k < g, permOK n w (mask w) (n * w) (G k) (pinvS n w (mask w) (G k)) = true)
    (hk : bfsK n w g G N T E S = true) (hf : N ≤ 4000) : Pin n w gs g G N T E S := by
  subst hgs
  refine ⟨by simp, fun k hk => ?_, hp, hk, hf⟩
  rw [getElem!_pos _ k (by simpa using hk), List.getElem_toArray, List.getElem_map,
    List.getElem_range]

theorem lamA_eq {V : List (Array ℕ)} {PV : Nat → Nat}
    (hV : V = (List.range 4).map fun i => unpack 64 7 (PV i)) (hPV : ∀ i < 4, PP 64 7 (PV i))
    {x : Nat} (hx : x < 256) : smLamAG V x = unpack 256 9 (pmk 256 9 (starK PV x)) := by
  unfold smLamAG
  rw [CFSG.KC.HexaStabK.unpack_pmk (by norm_num) fun _ hy => Nat.lt_trans (starK_lt hPV hx hy)
    (by norm_num)]
  exact congrArg (Array.ofFn (n := 256)) (funext fun y => star_eq hV hx y)

theorem lam_list {V : List (Array ℕ)} {PV : Nat → Nat} {PG : List (Array ℕ)} {g N : Nat}
    {GP G T E S : Nat → Nat}
    (hV : V = (List.range 4).map fun i => unpack 64 7 (PV i)) (hPV : ∀ i < 4, PP 64 7 (PV i))
    (pl : LamPin PV g GP G N T E S) (hPG : PG = (List.range g).map fun k => unpack 256 9 (GP k)) :
    smLamGensG V ++ PG = (List.range (8 + g)).map fun k => unpack 256 9 (G k) := by
  have e0 : ([1, 2, 4, 8, 16, 32, 64, 128] : List ℕ) = (List.range 8).map (2 ^ ·) := by
    simp [List.range_succ]
  have e : smLamGensG V = (List.range 8).map fun k => smLamAG V (2 ^ k) := by
    unfold smLamGensG
    rw [e0, List.map_map]
    exact List.map_congr_left fun k _ => Function.comp_apply
  rw [e, hPG, List.range_add, List.map_append, List.map_map]
  refine congrArg₂ (· ++ ·) ?_ ?_
  · refine List.map_congr_left fun k hk => ?_
    have hk' := List.mem_range.1 hk
    have h2 : 2 ^ k < 256 := by interval_cases k <;> decide
    rw [lamA_eq hV hPV h2, pl.lam k hk']
  · refine List.map_congr_left fun k hk => ?_
    rw [Function.comp_apply, pl.gens k (List.mem_range.1 hk)]

theorem pin_lam {V : List (Array ℕ)} {PV : Nat → Nat} {PG : List (Array ℕ)} {g N : Nat}
    {GP G T E S : Nat → Nat}
    (hV : V = (List.range 4).map fun i => unpack 64 7 (PV i)) (hPV : ∀ i < 4, PP 64 7 (PV i))
    (pl : LamPin PV g GP G N T E S) (hPG : PG = (List.range g).map fun k => unpack 256 9 (GP k)) :
    Pin 256 9 (smLamGensG V ++ PG) (8 + g) G N T E S :=
  pin_of_eq (lam_list hV hPV pl hPG) pl.perm pl.ok pl.fuel

theorem pairA_eq {m wa a b : Nat} (hm : m < 256) (ha : PP 256 9 a) (hb : PP m wa b) :
    pairA 256 (unpack 256 9 a) (unpack m wa b) = unpack (256 + m) 9 (pairK 256 m 9 wa a b) := by
  have hf : ∀ x < 256 + m, (if x < 256 then pg 9 (mask 9) a x
      else 256 + pg wa (mask wa) b (x - 256)) < 2 ^ 9 := fun x hx => by
    split
    · next h => exact Nat.lt_trans (ha.2.1 x h) (by norm_num)
    · next h =>
      have := hb.2.1 (x - 256) (by omega)
      have h9 : (2 : Nat) ^ 9 = 512 := by norm_num
      omega
  have e : pairK 256 m 9 wa a b = pmk (256 + m) 9 fun x =>
      if x < 256 then pg 9 (mask 9) a x else 256 + pg wa (mask wa) b (x - 256) := by
    unfold pairK
    congr 1
    funext x
    rw [nIf_ite, blt_eq_decide]
    simp only [decide_eq_true_eq]
    rfl
  rw [e, CFSG.KC.HexaStabK.unpack_pmk (by omega) hf]
  unfold pairA unpack
  apply Array.ext
  · simp
  · intro i h1 h2
    simp only [Array.getElem_append, Array.getElem_map, Array.getElem_ofFn, Array.size_ofFn]
    split
    · rfl
    · exact Nat.add_comm _ _

theorem pin_pair {n wa m g N NB : Nat} {LB LA : List (Array Nat)}
    {GB GA G T E S TB EB SB TA EA SA : Nat → Nat} {gA : Nat}
    (hm : m < 256) (hg : g = 10) (hgA : gA = 10)
    (pB : Pin 256 9 LB g GB NB TB EB SB) (pA : Pin m wa LA gA GA n TA EA SA)
    (pp : PairPin m GB GA wa G N T E S) :
    Pin (256 + m) 9 (List.zipWith (pairA 256) LB LA) 10 G N T E S := by
  subst hg hgA
  have qB := PP_gen pB.ok pB.perm
  have qA := PP_gen pA.ok pA.perm
  refine pin_of_eq ?_ pp.perm pp.ok pp.fuel
  rw [gens_eq pB.size pB.bind, gens_eq pA.size pA.bind, List.zipWith_map, List.zipWith_self]
  refine List.map_congr_left fun k hk => ?_
  have hk' := List.mem_range.1 hk
  rw [pairA_eq hm (qB k hk') (qA k hk'), pp.pair k hk']

theorem chk {n w : Nat} {gs : List (Array Nat)} {g N m : Nat} {G T E S : Nat → Nat}
    (p : Pin n w gs g G N T E S) (h : N = m) : enumCheckN n gs m = true := by
  subst h
  exact enumCheckN_of p.size p.bind p.perm p.ok p.fuel

theorem szOK_pin {n w : Nat} {gs : List (Array Nat)} {g N : Nat} {G T E S : Nat → Nat}
    (p : Pin n w gs g G N T E S) : szOK n w = true := by
  have h := p.ok
  unfold bfsK at h
  simp only [bAnd_iff] at h
  exact h.1

theorem mp_lt {PV : Nat → Nat} {Om Mu : Nat} {MP : Nat → Nat} {NM NK NW gH : Nat}
    {TM TK TW GH : Nat → Nat} (h : v0K PV Om Mu MP NM TM NK TK NW TW gH GH = true) :
    ∀ i < 4, MP i < 4 := by
  unfold v0K at h
  simp only [andB_eq, Bool.and_eq_true] at h
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, k13, -⟩ := h
  intro i hi
  have h1 := allN_spec k13 i hi
  rw [Bool.and_eq_true] at h1
  exact Nat.blt_eq.mp h1.1

theorem prod_beq_zero (c : ℕ × ℕ) : (c == (0, 0)) = (Nat.beq c.1 0 && Nat.beq c.2 0) := by
  apply Bool.eq_iff_iff.2
  rw [Bool.and_eq_true, beq_iff_eq, Nat.beq_eq, Nat.beq_eq, Prod.ext_iff]

theorem lt_of_mem_fixK {Om Mu : Nat} {MP : Nat → Nat} {muPi : Array ℕ} (po : PP 64 7 Om)
    (pm : PP 64 7 Mu) (hmp : ∀ i < 4, muPi[i]! = MP i) (hMP : ∀ i < 4, MP i < 4)
    {s1 s2 k : ℕ × ℕ} {y : Nat} (h : y ∈ fixK Om Mu MP s1 s2 k) : y < 256 := by
  rw [fixK_eq po pm hmp hMP] at h
  exact lt_of_mem_smFixG h

theorem size_all {n w : Nat} (g : Nat) (G : Nat → Nat) :
    ((List.range g).map fun k => unpack n w (G k)).all (·.size == n) = true :=
  List.all_eq_true.2 fun a ha => by
    obtain ⟨k, -, rfl⟩ := List.mem_map.1 ha
    simp [unpack]

theorem step44K_sound {V : List (Array ℕ)} {om mu muPi NF : Array ℕ}
    {mG nG NG NEG PG PEG Ab Aa y32 x16 : List (Array ℕ)}
    {PV : Nat → Nat} {Om Mu NFP : Nat} {MP : Nat → Nat}
    {cM NM cK NK cW NW cH NH cN NN cE NE cP NP cQ NQ NL NLP NLQ NPP NPQ cAb NAb cY NY cAa NAa
      cX NX : Nat}
    {GM TM EM SM GK TK EK SK GW TW EW SW GH TH EH SH GN TN EN SN GE TE EE SE GP TP EP SP
      GQ TQ EQ SQ GLa TL EL SL GLP TLP ELP SLP GLQ TLQ ELQ SLQ GPP TPP EPP SPP GPQ TPQ EPQ SPQ
      GAb TAb EAb SAb GY TY EY SY GAa TAa EAa SAa GX TX EX SX : Nat → Nat}
    (hV : V.length = 4 ∧ ∀ i < 4, V[i]! = unpack 64 7 (PV i) ∧
      permOK 64 7 (mask 7) (64 * 7) (PV i) (pinvS 64 7 (mask 7) (PV i)) = true)
    (hom : om = unpack 64 7 Om) (hmu : mu = unpack 64 7 Mu)
    (hpo : permOK 64 7 (mask 7) (64 * 7) Om (pinvS 64 7 (mask 7) Om) = true)
    (hpm : permOK 64 7 (mask 7) (64 * 7) Mu (pinvS 64 7 (mask 7) Mu) = true)
    (hmp : muPi.size = 4 ∧ ∀ i < 4, muPi[i]! = MP i) (hnf : NF = unpack 1024 2 NFP)
    (pM : Pin 64 7 mG cM GM NM TM EM SM) (pK : Pin 64 7 (V ++ [om, mu]) cK GK NK TK EK SK)
    (pW : Pin 64 7 [om, mu] cW GW NW TW EW SW) (pH : Pin 64 7 nG cH GH NH TH EH SH)
    (pN : Pin 256 9 NG cN GN NN TN EN SN) (pE : Pin 256 9 NEG cE GE NE TE EE SE)
    (pP : Pin 256 9 PG cP GP NP TP EP SP) (pQ : Pin 256 9 PEG cQ GQ NQ TQ EQ SQ)
    (pL : LamPin PV 0 GP GLa NL TL EL SL) (pLP : LamPin PV cP GP GLP NLP TLP ELP SLP)
    (pLQ : LamPin PV cQ GQ GLQ NLQ TLQ ELQ SLQ)
    (pAb : Pin 32 6 Ab cAb GAb NAb TAb EAb SAb) (pY : Pin 32 6 y32 cY GY NY TY EY SY)
    (pAa : Pin 16 5 Aa cAa GAa NAa TAa EAa SAa) (pX : Pin 16 5 x16 cX GX NX TX EX SX)
    (pPP : PairPin 32 GLP GAb 6 GPP NPP TPP EPP SPP) (pPQ : PairPin 16 GLQ GAa 5 GPQ NPQ TPQ EPQ SPQ)
    (hsz : NK = 36 ∧ NW = 9 ∧ NH = 144 ∧ NN = 72 ∧ NE = 36 ∧ NP = 8 ∧ NQ = 4 ∧ NL = 256 ∧
      NLP = 2048 ∧ NPP = 2048 ∧ NAb = 2048 ∧ NY = 2048 ∧ NLQ = 1024 ∧ NPQ = 1024 ∧ NAa = 1024 ∧
      NX = 1024 ∧ cAb = 10 ∧ cAa = 10 ∧ cP = 2 ∧ cQ = 2)
    (hv0 : v0K PV Om Mu MP NM TM NK TK NW TW cH GH = true)
    (htau : tauChk PV Om Mu MP NFP = true)
    (haut : autK PV Om Mu MP NFP NN TN 0 48 = true)
    (hsm : smK PV cN GN NN TN cE GE NE TE cP GP cQ GQ cY GY NAb TAb cX GX NAa TAa = true) :
    step44CheckG V om mu muPi mG nG NF NG NEG PG PEG Ab Aa y32 x16 = true := by
  obtain ⟨hNK, hNW, hNH, hNN, hNE, hNP, hNQ, hNL, hNLP, hNPP, hNAb, hNY, hNLQ, hNPQ, hNAa, hNX,
    hcAb, hcAa, hcP, hcQ⟩ := hsz
  have hsz : szOK 64 7 = true := szOK_pin pM
  have hsz2 : szOK 256 9 = true := szOK_pin pN
  have hV' := V_eq hV
  have hPV : ∀ i < 4, PP 64 7 (PV i) := fun i hi => PP_of_permOK hsz (hV.2 i hi).2
  have po : PP 64 7 Om := PP_of_permOK hsz hpo
  have pm : PP 64 7 Mu := PP_of_permOK hsz hpm
  have hMP := mp_lt hv0
  have hmp' := hmp.2
  have h0 := v0CheckG_of hV hom hmu hpo hpm hmp pM pK pW pH hNK hNW hNH hv0
  unfold step44CheckG
  rw [Bool.and_eq_true]
  refine ⟨h0, ?_⟩
  rw [hom, hmu, hnf]
  have sN := PP_pts pN.ok pN.perm
  have sE := PP_pts pE.ok pE.perm
  have sAb := PP_pts pAb.ok pAb.perm
  have sAa := PP_pts pAa.ok pAa.perm
  have qN := PP_gen pN.ok pN.perm
  have qE := PP_gen pE.ok pE.perm
  have qP := PP_gen pP.ok pP.perm
  have qQ := PP_gen pQ.ok pQ.perm
  have qY := PP_gen pY.ok pY.perm
  have qX := PP_gen pX.ok pX.perm
  have gP := gens_eq pP.size pP.bind
  have gQ := gens_eq pQ.size pQ.bind
  have bL := pin_lam (PG := []) hV' hPV pL rfl
  rw [List.append_nil] at bL
  have bLP := pin_lam hV' hPV pLP gP
  have bLQ := pin_lam hV' hPV pLQ gQ
  have bPP := pin_pair (by norm_num) (by omega) hcAb bLP pAb pPP
  have bPQ := pin_pair (by norm_num) (by omega) hcAa bLQ pAa pPQ
  have c256 := PP.id hsz2
  unfold tauChk at htau
  simp only [andB_eq, Bool.and_eq_true] at htau
  obtain ⟨t1, t2, t3, t4, t5, t6, t7⟩ := htau
  unfold smK at hsm
  simp only [andB_eq, Bool.and_eq_true] at hsm
  obtain ⟨m1, m2, m3, m4, m5, m6, m7⟩ := hsm
  have tq := fun {i : Nat} (hi : i < 256) (a b : Nat) => tau_eq (muPi := muPi) po pm hmp' hMP hi a b
  unfold smCheckG
  rw [eltsN_eq pN.size pN.bind pN.ok pN.fuel, eltsN_eq pE.size pE.bind pE.ok pE.fuel,
    eltsN_eq pAb.size pAb.bind pAb.ok pAb.fuel, eltsN_eq pAa.size pAa.bind pAa.ok pAa.fuel]
  simp only [Bool.and_eq_true, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, chk pN hNN, ?_, ?_, chk pE hNE, ?_, ?_, chk pP hNP,
    ?_, chk pQ hNQ, ?_, chk bL hNL, chk bLP hNLP, chk bPP hNPP, ?_, ?_, ?_,
    chk pAb hNAb, chk pY hNY, ?_, chk bLQ hNLQ, chk bPQ hNPQ, ?_, ?_, ?_, chk pAa hNAa,
    chk pX hNX, ?_⟩
  ·
    refine (all_congr_mem fun c _ => all_congr_mem fun c' _ => ?_).trans t1
    rw [strictB_eq', strictB_eq', strictB_eq', allN_eq']
    refine all_congr_mem fun i hi => ?_
    have hi' := List.mem_range.1 hi
    rw [tq hi', tq (tau_lt po pm hMP hi' _ _), tq hi', beq_nat]
    rfl
  ·
    refine (all_congr_mem fun c _ => ?_).trans t2
    rw [orB_eq, strictB_eq', anyN_eq, prod_beq_zero]
    refine congrArg (fun x => (Nat.beq c.1 0 && Nat.beq c.2 0) || x)
      (any_congr_mem fun i hi => ?_)
    rw [tq (List.mem_range.1 hi), notB_eq]
    simp only [bne, beq_nat]
    rfl
  · rw [tq (by norm_num), beq_nat]
    exact t3
  · rw [tq (by norm_num), beq_nat]
    exact t4
  · rw [tq (by norm_num), beq_nat]
    exact t5
  · rw [tq (by norm_num), beq_nat]
    exact t6
  · rw [cand_eq hV' hPV po pm hmp' hMP _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num),
      idA_eq hsz2, eqA_unpack (canonK_candK hV' hPV po pm hmp' hMP _ _ (by norm_num) (by norm_num)
        (by norm_num) (by norm_num)) c256.1]
    exact t7
  · rw [gens_eq pN.size pN.bind]
    exact all_gens qN (fun f hf => homA_eq hV' hPV hf.1) m1
  ·
    unfold smAutNG
    refine List.all_eq_true.2 fun s hs => ?_
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hs
    have hk48 : k < 48 := by
      have e : smSigmas.length = 48 := by decide
      omega
    have h := HeAutK.allR_spec haut k hk48
    rw [Nat.zero_add, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk,
      Option.getD_some] at h
    simp only [← fixK_eq po pm hmp' hMP] at h ⊢
    refine (all_congr_mem fun y0 hy0 => all_congr_mem fun y1 hy1 => all_congr_mem fun y2 hy2 =>
      all_congr_mem fun y3 hy3 => ?_).trans h
    have l0 := lt_of_mem_fixK po pm hmp' hMP hy0
    have l1 := lt_of_mem_fixK po pm hmp' hMP hy1
    have l2 := lt_of_mem_fixK po pm hmp' hMP hy2
    have l3 := lt_of_mem_fixK po pm hmp' hMP hy3
    rw [strictB_eq', cand_eq hV' hPV po pm hmp' hMP _ _ l0 l1 l2 l3,
      homA_eq hV' hPV (canonK_candK hV' hPV po pm hmp' hMP _ _ l0 l1 l2 l3),
      inLN_canon (canonK_candK hV' hPV po pm hmp' hMP _ _ l0 l1 l2 l3) sN, orB_eq, notB_eq]
  · rw [gens_eq pE.size pE.bind]
    exact all_gens qE (fun f hf => inLN_eq hf sN) m2
  · exact all_pts sN (fun f hf => by rw [presTA_eq, inLN_eq hf sE, orB_eq, notB_eq]) m3
  · rw [gP]
    exact all_gens qP (fun f hf => inLN_eq hf sN) m4
  · rw [gQ]
    exact all_gens qQ (fun f hf => inLN_eq hf sE) m5
  · rw [← List.size_toArray, pAb.size, hcAb]
    rfl
  · rw [lam_list hV' hPV pLP gP]
    exact size_all _ _
  · rw [gens_eq pAb.size pAb.bind]
    exact size_all _ _
  · rw [gens_eq pY.size pY.bind]
    exact all_gens qY (fun f hf => inLN_eq hf sAb) m6
  · rw [← List.size_toArray, pAa.size, hcAa]
    rfl
  · rw [lam_list hV' hPV pLQ gQ]
    exact size_all _ _
  · rw [gens_eq pAa.size pAa.bind]
    exact size_all _ _
  · rw [gens_eq pX.size pX.bind]
    exact all_gens qX (fun f hf => inLN_eq hf sAa) m7

end CFSG.KC.Step44K

end
