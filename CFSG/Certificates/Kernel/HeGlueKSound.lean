module

public import CFSG.Certificates.Kernel.HeModelKSound
public import CFSG.Certificates.Kernel.HeGlueKGlue

public section

namespace CFSG.KC.HeGlueK

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw CFSG.KC.BfsPin CFSG.KC.HexaK CFSG.KC.HeAutK
open CFSG.KC.HeModelK
open CFSG.Monster.B.Co2.Native CFSG.RankThree.Native
open CFSG.ComponentClassification.AS81.HeSylow CFSG.ComponentClassification.AS81.Hexa
open CFSG.ComponentClassification.AS81.HeTri CFSG.ComponentClassification.AS81.HePres.Native
open CFSG.KLie.CT (anyN andB orB notB)

theorem bindArrsK_eq {gs : List (Array Nat)} {n w g : Nat} {G : Nat → Nat}
    (h : bindArrsK gs n w g G = true) : gs = (List.range g).map fun k => unpack n w (G k) := by
  unfold bindArrsK at h
  rw [andB_eq, Bool.and_eq_true] at h
  exact gens_eq (Nat.eq_of_beq_eq_true h.1)
    fun k hk => unpack_eq_of_bindArrK (allN_spec h.2 k hk)

theorem pinB_of {n w : Nat} {ps : List Nat} {gs : List (Array Nat)} {g N : Nat}
    {G T E S : Nat → Nat} {SK : List Nat} (hb : bindArrsK gs n w g G = true)
    (hp : allN g (fun k => permOK n w (mask w) (n * w) (G k) (pinvS n w (mask w) (G k))) = true)
    (hk : bfsK n w g G N T E S = true) (hK : keysSK n w ps N T SK = true) :
    PinB n w ps gs g G N T E S SK := by
  unfold bindArrsK at hb
  rw [andB_eq, Bool.and_eq_true] at hb
  exact ⟨Nat.eq_of_beq_eq_true hb.1, fun k hk => unpack_eq_of_bindArrK (allN_spec hb.2 k hk),
    allN_spec hp, hk, hK⟩

theorem allR_chunks {f : Nat → Bool} {K L : Nat} (h : ∀ s < K, allR f (s * L) L = true) :
    ∀ j < K * L, f j = true := by
  intro j hj
  have hL : 0 < L := Nat.pos_of_ne_zero fun e => by simp [e] at hj
  have hs : j / L < K := (Nat.div_lt_iff_lt_mul hL).2 hj
  have e := HeModelK.allR_spec (h (j / L) hs) (j % L) (Nat.mod_lt j hL)
  rwa [Nat.div_add_mod'] at e

structure HG where
  p12c : List (Array ℕ)
  p13c : List (Array ℕ)
  relsP : List (List ℕ)
  repE : List (Array ℕ)
  repF : List (Array ℕ)
  sigmaF : List ℕ
  conjF : List (Array ℕ)
  p12G : List (Array ℕ)
  b0G : List (Array ℕ)
  p23G : List (Array ℕ)
  wE : List (List ℕ)
  wF : List (List ℕ)
  wBE : List (List ℕ)
  wBF : List (List ℕ)
  wit : List (List ℕ)
  witE : List Bool
  piE : Array (Array ℕ)
  piF : Array (Array ℕ)
  piC : Bool → Array (Array ℕ)
  bcG : List (Array ℕ)
  t0 : Array ℕ
  rels23 : List (List ℕ)
  r23 : List (List ℕ)
  tc : Array ℕ
  gC0 : List (List ℕ)
  gC1 : List (List ℕ)
  gT : List (List ℕ)
  gM : List (List ℕ)
  gR : List (List ℕ)
  pcG : List (Array ℕ)
  tG : List (Array ℕ)
  mG : List (Array ℕ)
  rG : List (Array ℕ)

section G

variable (h : HG)

@[expose] def lP12 : List (Array ℕ) := eltsK 64 base64 h.p12G 3072
@[expose] def lB : List (Array ℕ) := eltsK 64 base64 h.b0G 1024
@[expose] def lP23 : List (Array ℕ) := eltsK 64 base64 h.p23G 9216
@[expose] def lP0 : List (Array ℕ) := eltsK 32 base32 h.p12c 3072
@[expose] def lP1 : List (Array ℕ) := eltsK 32 base32 h.p13c 3072
@[expose] def lBC : List (Array ℕ) := eltsK 32 base32 h.bcG 1024

@[expose] def rEG (i k : ℕ) : Array ℕ := h.repE.getD (2 * i + k) #[]
@[expose] def rFG (i k : ℕ) : Array ℕ := h.repF.getD (2 * i + k) #[]
@[expose] def pEG (i : ℕ) : List (Array ℕ) := [rEG h i 0, rEG h i 1]
@[expose] def pFG (i : ℕ) : List (Array ℕ) := [rFG h i 0, rFG h i 1]

@[expose] def srcG : Bool :=
  relsOK 32 h.p12c h.relsP && relsOK 32 h.p13c h.relsP &&
    isOrd12 32 (h.p12c.getD 1 #[]) && isOrd12 32 (h.p13c.getD 1 #[]) &&
    ((lP0 h).filter (commN 32 (h.p12c.getD 1 #[]))).length == 12 &&
    ((lP1 h).filter (commN 32 (h.p13c.getD 1 #[]))).length == 12 &&
    h.repE.all (inLN 64 (lP12 h)) && h.repF.all (inLN 64 (lP12 h))

@[expose] def classBG : Bool :=
  (lP12 h).all fun x => !(isOrd12 64 x && ((lP12 h).filter (commN 64 x)).length == 12) ||
    (List.range 4).any fun i => (lP12 h).any fun p => eqA 64 (conjA 64 p (rEG h i 1)) x

@[expose] def classCG : Bool :=
  (List.range 4).all fun i => (lP12 h).all fun x => !(relsOK 64 [x, rEG h i 1] h.relsP) ||
    (List.range 4).any fun i' => (lP12 h).any fun c =>
      eqA 64 (conjA 64 c (rEG h i' 0)) x && eqA 64 (conjA 64 c (rEG h i' 1)) (rEG h i 1)

@[expose] def repFG : Bool :=
  (List.range 4).all fun j => decide (h.sigmaF.getD j 0 < 4) &&
    inLN 64 (lP12 h) (h.conjF.getD j #[]) &&
    eqA 64 (conjA 64 (h.conjF.getD j #[]) (rEG h (h.sigmaF.getD j 0) 0)) (rFG h j 0) &&
    eqA 64 (conjA 64 (h.conjF.getD j #[]) (rEG h (h.sigmaF.getD j 0) 1)) (rFG h j 1)

@[expose] def normBG : Bool :=
  ((lP12 h).filter (normsN 64 (lB h) h.b0G)).length == 1024 &&
    (List.range 4).all fun i => (h.wBE ++ h.wBF).all fun w =>
      inLN 64 (lB h) (evalW 64 (pEG h i) w) && inLN 64 (lB h) (evalW 64 (pFG h i) w)

@[expose] def conjG (x y : Array ℕ) : Bool := (lP23 h).any fun q => eqA 64 (conjA 64 q x) y

@[expose] def fusG (k : ℕ) : Bool :=
  let i := (heWitIdx.getD k (0, 0)).1
  let j := (heWitIdx.getD k (0, 0)).2
  let wE1 := h.wit.getD (4 * k) []
  let wF1 := h.wit.getD (4 * k + 1) []
  let wE2 := h.wit.getD (4 * k + 2) []
  let wF2 := h.wit.getD (4 * k + 3) []
  let x1 := evalW 64 (pEG h i) wE1
  let x2 := evalW 64 (pEG h i) wE2
  let y1 := evalW 64 (pFG h j) wF1
  let y2 := evalW 64 (pFG h j) wF2
  eqA 32 (evalW 32 h.p12c wE1) (evalW 32 h.p13c wF1) &&
    eqA 32 (evalW 32 h.p12c wE2) (evalW 32 h.p13c wF2) &&
    eqA 32 (evalW 32 h.p13c wE1) (evalW 32 h.p12c wF1) &&
    eqA 32 (evalW 32 h.p13c wE2) (evalW 32 h.p12c wF2) &&
    if h.witE.getD k true then conjG h x1 x2 && !(conjG h y1 y2)
    else conjG h y1 y2 && !(conjG h x1 x2)

@[expose] def piG : Bool :=
  (List.range 5).all (fun k =>
    eqA 64 (evalW 64 (pEG h 0) (h.wE.getD k [])) (h.piE.getD (piIdx 4 k) #[]) &&
      eqA 64 (evalW 64 (pFG h 0) (h.wF.getD k [])) (h.piF.getD (piIdx 5 k) #[]) &&
      eqA 32 (evalW 32 h.p12c (h.wE.getD k [])) ((h.piC false).getD (piIdx 4 k) #[]) &&
      eqA 32 (evalW 32 h.p13c (h.wF.getD k [])) ((h.piC false).getD (piIdx 5 k) #[]) &&
      eqA 32 (evalW 32 h.p13c (h.wE.getD k [])) ((h.piC true).getD (piIdx 4 k) #[]) &&
      eqA 32 (evalW 32 h.p12c (h.wF.getD k [])) ((h.piC true).getD (piIdx 5 k) #[])) &&
    (List.range 4).all fun k =>
      eqA 32 (evalW 32 h.p12c (h.wBE.getD k [])) (h.bcG.getD k #[]) &&
        eqA 32 (evalW 32 h.p13c (h.wBF.getD k [])) (h.bcG.getD k #[])

@[expose] def t8G (hx hy : Array ℕ) : List (Array ℕ) :=
  (h.piF.toList.take 4) ++ [idA 64, idA 64, hx, hy]

@[expose] def relsXG : List (List ℕ) := h.r23.filter fun r => r.all fun l => l / 2 < 4 || l / 2 == 6

@[expose] def relsYG : List (List ℕ) := h.r23.filter fun r => r.all fun l => l / 2 < 4 || l / 2 == 7

@[expose] def kerG : Bool :=
  let xF := h.piF.getD 6 #[]
  let yF := h.piF.getD 7 #[]
  let xF' := conjA 64 h.t0 xF
  let yF' := conjA 64 h.t0 yF
  relsOK 64 h.piE.toList h.rels23 &&
    (lP23 h).all (fun hy => !(relsOK 64 (t8G h (idA 64) hy) (relsYG h)) || eqA 64 hy yF ||
      eqA 64 hy yF') &&
    (lP23 h).all fun hx => !(relsOK 64 (t8G h hx (idA 64)) (relsXG h)) ||
      ((!(relsOK 64 (t8G h hx yF) h.r23) || eqA 64 hx xF) &&
        (!(relsOK 64 (t8G h hx yF') h.r23) || eqA 64 hx xF'))

@[expose] def validG : Bool :=
  (h.repE ++ h.repF ++ h.conjF ++ h.piE.toList ++ h.piF.toList).all (validA 64) &&
    ((h.piC false).toList ++ (h.piC true).toList).all (validA 32) && validA 64 (idA 64) &&
    validA 64 h.t0 && validA 64 (conjA 64 h.t0 (h.piF.getD 6 #[])) &&
    validA 64 (conjA 64 h.t0 (h.piF.getD 7 #[])) && h.repE.length == 8 &&
    h.repF.length == 8 && h.conjF.length == 4 &&
    h.piE.size == 8 && h.piF.size == 8 && (h.piC false).size == 8 &&
    (h.piC true).size == 8

@[expose] def rangeG : Bool :=
  (h.relsP ++ h.wE ++ h.wF ++ h.wBE ++ h.wBF ++ h.wit).all (·.all (· < 4)) &&
    h.rels23.all (·.all fun l => l < 8 || l / 2 == 6 || l / 2 == 7) &&
    (h.gC0 ++ h.gC1).all (·.all (· < 12)) &&
    (h.gT ++ h.gM ++ h.gR).all
      (·.all fun l => l < 10 || l / 2 == 6 || l / 2 == 7)

@[expose] def memG : Bool :=
  (List.range 4).all (fun k => inLN 64 (lB h) (h.piE.getD k #[]) &&
      inLN 64 (lB h) (h.piF.getD k #[]) && inLN 32 (lBC h) ((h.piC false).getD k #[]) &&
      inLN 32 (lBC h) ((h.piC true).getD k #[])) &&
    inLN 64 (lP12 h) (h.piE.getD 4 #[]) && inLN 64 (lP12 h) (h.piF.getD 5 #[]) &&
    inLN 32 (lP0 h) ((h.piC false).getD 4 #[]) && inLN 32 (lP1 h) ((h.piC false).getD 5 #[]) &&
    inLN 32 (lP1 h) ((h.piC true).getD 4 #[]) && inLN 32 (lP0 h) ((h.piC true).getD 5 #[]) &&
    [6, 7].all fun k =>
      inLN 64 (lP23 h) (h.piE.getD k #[]) && inLN 64 (lP23 h) (h.piF.getD k #[])

@[expose] def zG : Bool :=
  eqA 32 (evalW 32 (h.piC false).toList [2, 4, 2, 4]) h.tc &&
    eqA 32 (evalW 32 (h.piC true).toList [2, 4, 2, 4]) h.tc

@[expose] def genG : Bool :=
  h.gC0.length == h.pcG.length && h.gC1.length == h.pcG.length &&
    h.gT.length == h.tG.length && h.gM.length == h.mG.length &&
    (List.range h.pcG.length).all (fun k =>
      eqA 32 (evalW 32 (h.piC false).toList (h.gC0.getD k [])) (h.pcG.getD k #[]) &&
        eqA 32 (evalW 32 (h.piC true).toList (h.gC1.getD k [])) (h.pcG.getD k #[])) &&
    (List.range h.tG.length).all (fun k =>
      eqA 64 (evalW 64 h.piE.toList (h.gT.getD k [])) (h.tG.getD k #[])) &&
    (List.range h.mG.length).all (fun k =>
      eqA 64 (evalW 64 h.piE.toList (h.gM.getD k [])) (h.mG.getD k #[])) &&
    h.gR.length == h.rG.length &&
    (List.range h.rG.length).all fun k =>
      eqA 64 (evalW 64 h.piE.toList (h.gR.getD k [])) (h.rG.getD k #[])

@[expose] def heGlueCheckG : Bool :=
  validG h && rangeG h && srcG h && classBG h && classCG h && repFG h &&
    normBG h && (List.range 15).all (fusG h) && piG h && kerG h && memG h && zG h &&
    genG h

end G

@[expose] def heG : HG :=
  ⟨heP12CGens, heP13CGens, heRelsP, heRepE, heRepF, heSigmaF, heConjF, heP12Gens, heB0Gens,
    heP23Gens, heWordsE, heWordsF, heWordsBE, heWordsBF, heWit, heWitE, hePiEArrs, hePiFArrs,
    hePiCArrs, heBCGens, hexaT0, hePiRels23Codes, hePiR23Codes, heTCArr, heGenWordsC0,
    heGenWordsC1, heGenWordsT, heGenWordsM, heGenWordsR, hePCGens, hexaTGens, hexaMGens,
    hexaR0Gens⟩

theorem heGlueCheck_eq : heGlueCheck = heGlueCheckG heG := rfl

theorem invOK_facts {n w a b : Nat} (hsz : szOK n w = true) (h : invOK n w a b = true) :
    PP n w a ∧ b = pinvS n w (mask w) a :=
  ⟨PP_of_invOK hsz h, inv_of_invOK (PP_of_invOK hsz h) h⟩

theorem vA {n w p : Nat} (hp : PP n w p) : validA n (unpack n w p) = true :=
  validA_unpack (CFSG.KS.PinvS.permOK_pinvS hp.1 hp.2)

theorem eqA_of_beq {n w a b : Nat} (h : Nat.beq a b = true) :
    eqA n (unpack n w a) (unpack n w b) = true := by
  rw [Nat.eq_of_beq_eq_true h]
  unfold eqA
  rw [CFSG.Monster.B.Co2.allLt_iff]
  intro i _
  exact beq_self_eq_true _

theorem arr_getD {α : Type} (A : Array α) (i : Nat) (d : α) : A.getD i d = A.toList.getD i d := by
  rw [Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD, Array.getElem?_toList]

theorem lgetD_unpack {l : List (Array Nat)} {n w g : Nat} {G : Nat → Nat}
    (hl : l = (List.range g).map fun k => unpack n w (G k)) {i : Nat} (hi : i < g) :
    l.getD i #[] = unpack n w (G i) := by
  rw [hl, getD_map_range, ite_eq_left hi]

theorem getD_unpack {A : Array (Array Nat)} {n w g : Nat} {G : Nat → Nat}
    (hA : A.toList = (List.range g).map fun k => unpack n w (G k)) {i : Nat} (hi : i < g) :
    A.getD i #[] = unpack n w (G i) := by
  rw [arr_getD, lgetD_unpack hA hi]

theorem inLN_of {n w N x : Nat} {L : List (Array Nat)} {T : Nat → Nat}
    (hl : L = (List.range N).map fun i => unpack n w (T i)) (hT : ∀ i < N, PP n w (T i))
    (hx : PP n w x) (h : inL N T x = true) : inLN n L (unpack n w x) = true := by
  rw [hl, inLN_eq hx hT]
  exact h

theorem not_any_of {l : List Nat} {p : Nat → Bool} (h : ∀ x ∈ l, p x ≠ true) :
    (!l.any p) = true := by
  rw [List.any_eq_false.2 h]
  rfl

theorem WG_pair {n w a b ai bi : Nat} (hsz : szOK n w = true) (ha : PP n w a) (hb : PP n w b)
    (hai : ai = pinvS n w (mask w) a) (hbi : bi = pinvS n w (mask w) b) :
    WG n w [unpack n w a, unpack n w b] 2 (pairG a b) (pairG ai bi) := by
  refine ⟨hsz, rfl, fun k hk => ?_, fun k hk => ?_⟩
  · rcases (by omega : k = 0 ∨ k = 1) with rfl | rfl
    · exact ha
    · exact hb
  · rcases (by omega : k = 0 ∨ k = 1) with rfl | rfl
    · exact hai
    · exact hbi

theorem Wt8 {h : HG} {d : GK}
    (hPF : h.piF.toList = (List.range 8).map fun k => unpack 64 7 (d.PF k))
    (fPF : ∀ k < 8, PP 64 7 (d.PF k) ∧ d.PFI k = pinvS 64 7 (mask 7) (d.PF k))
    {hx hy hxi hyi : Nat} (px : PP 64 7 hx) (py : PP 64 7 hy)
    (vx : hxi = pinvS 64 7 (mask 7) hx) (vy : hyi = pinvS 64 7 (mask 7) hy) :
    WG 64 7 (t8G h (unpack 64 7 hx) (unpack 64 7 hy)) 8 (t8 d hx hy) (t8I d hxi hyi) := by
  have h64 : szOK 64 7 = true := rfl
  refine ⟨h64, ?_, fun k hk => ?_, fun k hk => ?_⟩
  · unfold t8G
    rw [hPF, idA_eq h64]
    rfl
  · rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [(fPF 0 (by omega)).1, (fPF 1 (by omega)).1, (fPF 2 (by omega)).1,
      (fPF 3 (by omega)).1, PP.id h64, PP.id h64, px, py]
  · rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [(fPF 0 (by omega)).2, (fPF 1 (by omega)).2, (fPF 2 (by omega)).2,
      (fPF 3 (by omega)).2, (pinvS_pidn h64).symm, (pinvS_pidn h64).symm, vx, vy]

theorem conjP_spec {d : GK} (sP : ∀ i < d.NP, PP 64 7 (d.TP i)) {p x y : Nat}
    (h : conjP d p x y = true) : p < d.NP ∧ conj 64 7 (d.TP p) x = y := by
  unfold conjP at h
  rw [strictB_eq', strictB_eq'] at h
  simp only [andB_eq, Bool.and_eq_true] at h
  obtain ⟨h1, -, h3, h4⟩ := h
  have hp := Nat.blt_eq.mp h1
  rw [inv_of_invOK (sP _ hp) h3, conjW_eq] at h4
  exact ⟨hp, Nat.eq_of_beq_eq_true h4⟩

theorem conj23_spec {d : GK} (s23 : ∀ i < d.N23, PP 64 7 (d.T23 i)) {q x y : Nat}
    (h : conj23 d q x y = true) : q < d.N23 ∧ conj 64 7 (d.T23 q) x = y := by
  unfold conj23 at h
  rw [strictB_eq', strictB_eq'] at h
  simp only [andB_eq, Bool.and_eq_true] at h
  obtain ⟨h1, -, h3, h4⟩ := h
  have hq := Nat.blt_eq.mp h1
  rw [inv_of_invOK (s23 _ hq) h3, conjW_eq] at h4
  exact ⟨hq, Nat.eq_of_beq_eq_true h4⟩

theorem rec2_all {f g : List Nat → Bool} (ws : List (List Nat)) :
    List.rec (motive := fun _ => Bool) true (fun w _ ih => CFSG.KLie.CT.andB (f w) (CFSG.KLie.CT.andB (g w) ih)) ws =
      ws.all fun w => f w && g w := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
    change CFSG.KLie.CT.andB (f w) (CFSG.KLie.CT.andB (g w) (List.rec (motive := fun _ => Bool) true
      (fun w _ ih => CFSG.KLie.CT.andB (f w) (CFSG.KLie.CT.andB (g w) ih)) ws)) = _
    rw [ih, andB_eq, andB_eq, List.all_cons, Bool.and_assoc]

theorem conjG_eq {h : HG} {N : Nat} {T : Nat → Nat}
    (hl : lP23 h = (List.range N).map fun i => unpack 64 7 (T i)) (hT : ∀ i < N, PP 64 7 (T i))
    {a b : Nat} (ha : PP 64 7 a) (hb : PP 64 7 b) :
    conjG h (unpack 64 7 a) (unpack 64 7 b) =
      (List.range N).any fun q => Nat.beq (conj 64 7 (T q) a) b := by
  unfold conjG
  rw [hl, List.any_map]
  refine any_congr_mem fun q hq => ?_
  have pq := hT q (List.mem_range.1 hq)
  simp only [Function.comp_apply]
  rw [conjA_PP pq ha, eqA_PP (pq.conjK ha) hb]

theorem piIdx_eq (c k : Nat) : piIdx c k = Bool.rec (motive := fun _ => Nat) c k (Nat.blt k 4) := by
  unfold piIdx
  cases h : Nat.blt k 4
  · rw [ite_eq_right fun h' => by rw [Nat.blt_eq.mpr h'] at h; cases h]
  · rw [ite_eq_left (Nat.blt_eq.mp h)]

theorem piIdx_lt {c k : Nat} (hc : c < 8) (hk : k < 5) : piIdx c k < 8 := by
  unfold piIdx
  split <;> omega

theorem heGlueK_sound {h : HG} {d : GK} {WB WR WC WF WM KY FX FX1 FX2 : Nat → Nat}
    {WX : Nat → Nat → Nat}
    {gP : Nat} {GP EP EB E23 E0 E1 EBC SP S23 S0 S1 SBC : Nat → Nat}
    {KP KB K23 K0 K1 KBC : List Nat}
    (pP : PinB 64 7 base64 h.p12G gP GP d.NP d.TP EP SP KP)
    (pB : PinB 64 7 base64 h.b0G d.gB d.GB d.NB d.TB EB d.SB KB)
    (p23 : PinB 64 7 base64 h.p23G d.g23 d.G23 d.N23 d.T23 E23 S23 K23)
    (p0 : PinB 32 6 base32 h.p12c 2 d.G12 d.N0 d.T0 E0 S0 K0)
    (p1 : PinB 32 6 base32 h.p13c 2 d.G13 d.N1 d.T1 E1 S1 K1)
    (pBC : PinB 32 6 base32 h.bcG d.gBC d.GBC d.NBC d.TBC EBC SBC KBC)
    (hsz : d.NP = 3072 ∧ d.NB = 1024 ∧ d.N23 = 9216 ∧ d.N0 = 3072 ∧ d.N1 = 3072 ∧ d.NBC = 1024)
    (hbind : bindArrsK h.repE 64 7 8 d.RE = true ∧ bindArrsK h.repF 64 7 8 d.RF = true ∧
      bindArrsK h.conjF 64 7 4 d.CF = true ∧ bindArrsK h.piE.toList 64 7 8 d.PE = true ∧
      bindArrsK h.piF.toList 64 7 8 d.PF = true ∧
      bindArrsK (h.piC false).toList 32 6 8 d.PC0 = true ∧
      bindArrsK (h.piC true).toList 32 6 8 d.PC1 = true ∧
      bindArrsK h.tG 64 7 d.gT d.GT = true ∧ bindArrsK h.mG 64 7 d.gM d.GM = true ∧
      bindArrsK h.rG 64 7 d.gR d.GR = true ∧ bindArrsK h.pcG 32 6 d.gC d.GC = true ∧
      bindArrK h.t0 64 7 d.t0 = true ∧ bindArrK h.tc 32 6 d.tc = true)
    (hinv : invsK d = true)
    (_hperm : permsK d = true)
    (hsrc : srcK d h.relsP = true)
    (hcB : ∀ j < d.NP, classBAt d WB j = true)
    (hcC : ∀ i < 4, ∀ j < d.NP, classCAt d h.relsP WR WC i j = true)
    (hrepF : repFK d = true)
    (hnorm : normCnt d 0 3072 = 1024)
    (hwB : wordsBK d (h.wBE ++ h.wBF) = true)
    (hfus : ∀ k < 15, fusK d (h.wit.getD (4 * k) []) (h.wit.getD (4 * k + 1) [])
      (h.wit.getD (4 * k + 2) []) (h.wit.getD (4 * k + 3) []) (h.witE.getD k true) k
      (WF k) (WM k) (WX k) = true)
    (hpi : piK d h.wE h.wF h.wBE h.wBF = true)
    (hkerE : relsK 64 7 8 d.PE d.PEI h.rels23 = true)
    (hkerY : ∀ j < d.N23, kerYAt d (relsYG h) (KY j) j = true)
    (hkerX : ∀ j < d.N23, kerXAt d (relsXG h) h.r23 (FX j) (FX1 j) (FX2 j) j = true)
    (hmem : memK d = true)
    (hgen : genK d h.gC0 h.gC1 h.gT h.gM h.gR = true)
    (_hid : permOK 64 7 (mask 7) (64 * 7) (pidn 64 7) (pidn 64 7) = true ∧
      permOK 32 6 (mask 6) (32 * 6) (pidn 32 6) (pidn 32 6) = true)
    (hsig : h.sigmaF = [0, 1, 2, 3]) (hrange : rangeG h = true) :
    heGlueCheckG h = true := by
  obtain ⟨hNP, hNB, hN23, hN0, hN1, hNBC⟩ := hsz
  obtain ⟨bRE, bRF, bCF, bPE, bPF, bPC0, bPC1, bT, bM, bR, bC, bt0, btc⟩ := hbind
  have h64 : szOK 64 7 = true := rfl
  have h32 : szOK 32 6 = true := rfl
  have hps64 : ∀ p ∈ base64, p < 64 := by decide
  have hps32 : ∀ p ∈ base32, p < 32 := by decide
  have sP := PP_pts pP.ok pP.perm
  have sB := PP_pts pB.ok pB.perm
  have s23 := PP_pts p23.ok p23.perm
  have s0 := PP_pts p0.ok p0.perm
  have s1 := PP_pts p1.ok p1.perm
  have sBC := PP_pts pBC.ok pBC.perm
  have qB := PP_gen pB.ok pB.perm
  have q23 := PP_gen p23.ok p23.perm
  have q0 := PP_gen p0.ok p0.perm
  have q1 := PP_gen p1.ok p1.perm
  have eP : lP12 h = (List.range d.NP).map fun i => unpack 64 7 (d.TP i) := pP.elts hps64 hNP
  have eB : lB h = (List.range d.NB).map fun i => unpack 64 7 (d.TB i) := pB.elts hps64 hNB
  have e23 : lP23 h = (List.range d.N23).map fun i => unpack 64 7 (d.T23 i) :=
    p23.elts hps64 hN23
  have e0 : lP0 h = (List.range d.N0).map fun i => unpack 32 6 (d.T0 i) := p0.elts hps32 hN0
  have e1 : lP1 h = (List.range d.N1).map fun i => unpack 32 6 (d.T1 i) := p1.elts hps32 hN1
  have eBC : lBC h = (List.range d.NBC).map fun i => unpack 32 6 (d.TBC i) :=
    pBC.elts hps32 hNBC
  have hdB : distinctK d.NB d.TB d.SB = true := by
    have hk := pB.ok
    unfold bfsK at hk
    simp only [bAnd_iff] at hk
    exact hk.2.2.2.2.1
  have inB_eq : ∀ x, inB d x = inL d.NB d.TB x := fun x => memS_eq hdB
  have lRE := bindArrsK_eq bRE
  have lRF := bindArrsK_eq bRF
  have lCF := bindArrsK_eq bCF
  have lPE := bindArrsK_eq bPE
  have lPF := bindArrsK_eq bPF
  have lPC0 := bindArrsK_eq bPC0
  have lPC1 := bindArrsK_eq bPC1
  have lT := bindArrsK_eq bT
  have lM := bindArrsK_eq bM
  have lR := bindArrsK_eq bR
  have lC := bindArrsK_eq bC
  have et0 := unpack_eq_of_bindArrK bt0
  have etc := unpack_eq_of_bindArrK btc
  unfold invsK at hinv
  simp only [andB_eq, Bool.and_eq_true] at hinv
  obtain ⟨i8, i4, i2, i23, it0, iyT⟩ := hinv
  have I8 : ∀ k < 8, invOK 64 7 (d.RE k) (d.REI k) = true ∧ invOK 64 7 (d.RF k) (d.RFI k) = true ∧
      invOK 64 7 (d.PE k) (d.PEI k) = true ∧ invOK 64 7 (d.PF k) (d.PFI k) = true ∧
      invOK 32 6 (d.PC0 k) (d.PC0I k) = true ∧ invOK 32 6 (d.PC1 k) (d.PC1I k) = true :=
    fun k hk => by
      have e := allN_spec i8 k hk
      simp only [Bool.and_eq_true] at e
      exact e
  have fRE := fun k (hk : k < 8) => invOK_facts h64 (I8 k hk).1
  have fRF := fun k (hk : k < 8) => invOK_facts h64 (I8 k hk).2.1
  have fPE := fun k (hk : k < 8) => invOK_facts h64 (I8 k hk).2.2.1
  have fPF := fun k (hk : k < 8) => invOK_facts h64 (I8 k hk).2.2.2.1
  have fPC0 := fun k (hk : k < 8) => invOK_facts h32 (I8 k hk).2.2.2.2.1
  have fPC1 := fun k (hk : k < 8) => invOK_facts h32 (I8 k hk).2.2.2.2.2
  have fCF := fun k (hk : k < 4) => invOK_facts h64 (allN_spec i4 k hk)
  have I2 : ∀ k < 2, invOK 32 6 (d.G12 k) (d.G12I k) = true ∧
      invOK 32 6 (d.G13 k) (d.G13I k) = true := fun k hk => by
    have e := allN_spec i2 k hk
    simp only [Bool.and_eq_true] at e
    exact e
  have fG23 : ∀ k < d.g23, d.G23I k = pinvS 64 7 (mask 7) (d.G23 k) :=
    fun k hk => (invOK_facts h64 (allN_spec i23 k hk)).2
  have ft0 := invOK_facts h64 it0
  have pyT := PP_of_invOK h64 iyT
  have vyT := inv_of_invOK pyT iyT
  have hyT : yT d = conj 64 7 d.t0 (d.PF 7) := by
    unfold yT
    rw [ft0.2, conjW_eq]
  have hxT : xT d = conj 64 7 d.t0 (d.PF 6) := by
    unfold xT
    rw [ft0.2, conjW_eq]
  have W12 : WG 32 6 h.p12c 2 d.G12 d.G12I :=
    ⟨h32, p0.gens, q0, fun k hk => (invOK_facts h32 (I2 k hk).1).2⟩
  have W13 : WG 32 6 h.p13c 2 d.G13 d.G13I :=
    ⟨h32, p1.gens, q1, fun k hk => (invOK_facts h32 (I2 k hk).2).2⟩
  have WPE : WG 64 7 h.piE.toList 8 d.PE d.PEI :=
    ⟨h64, lPE, fun k hk => (fPE k hk).1, fun k hk => (fPE k hk).2⟩
  have WPC0 : WG 32 6 (h.piC false).toList 8 d.PC0 d.PC0I :=
    ⟨h32, lPC0, fun k hk => (fPC0 k hk).1, fun k hk => (fPC0 k hk).2⟩
  have WPC1 : WG 32 6 (h.piC true).toList 8 d.PC1 d.PC1I :=
    ⟨h32, lPC1, fun k hk => (fPC1 k hk).1, fun k hk => (fPC1 k hk).2⟩
  have rE : ∀ i < 4, ∀ k < 2, rEG h i k = unpack 64 7 (d.RE (2 * i + k)) := fun i hi k hk => by
    unfold rEG
    rw [lgetD_unpack lRE (by omega)]
  have rF : ∀ i < 4, ∀ k < 2, rFG h i k = unpack 64 7 (d.RF (2 * i + k)) := fun i hi k hk => by
    unfold rFG
    rw [lgetD_unpack lRF (by omega)]
  have WE : ∀ i < 4, WG 64 7 (pEG h i) 2 (pE d i) (pEI d i) := fun i hi => by
    have e : pEG h i = [unpack 64 7 (d.RE (2 * i)), unpack 64 7 (d.RE (2 * i + 1))] := by
      unfold pEG
      rw [rE i hi 0 (by omega), rE i hi 1 (by omega)]
      rfl
    rw [e]
    exact WG_pair h64 (fRE (2 * i) (by omega)).1 (fRE (2 * i + 1) (by omega)).1
      (fRE (2 * i) (by omega)).2 (fRE (2 * i + 1) (by omega)).2
  have WF : ∀ i < 4, WG 64 7 (pFG h i) 2 (pF d i) (pFI d i) := fun i hi => by
    have e : pFG h i = [unpack 64 7 (d.RF (2 * i)), unpack 64 7 (d.RF (2 * i + 1))] := by
      unfold pFG
      rw [rF i hi 0 (by omega), rF i hi 1 (by omega)]
      rfl
    rw [e]
    exact WG_pair h64 (fRF (2 * i) (by omega)).1 (fRF (2 * i + 1) (by omega)).1
      (fRF (2 * i) (by omega)).2 (fRF (2 * i + 1) (by omega)).2
  unfold heGlueCheckG
  simp only [Bool.and_eq_true]
  refine ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨?_, hrange⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · have szE : h.piE.size = 8 := by
      rw [← Array.length_toList, lPE, List.length_map, List.length_range]
    have szF : h.piF.size = 8 := by
      rw [← Array.length_toList, lPF, List.length_map, List.length_range]
    have szC0 : (h.piC false).size = 8 := by
      rw [← Array.length_toList, lPC0, List.length_map, List.length_range]
    have szC1 : (h.piC true).size = 8 := by
      rw [← Array.length_toList, lPC1, List.length_map, List.length_range]
    unfold validG
    rw [getD_unpack lPF (by omega : 6 < 8), getD_unpack lPF (by omega : 7 < 8), et0, idA_eq h64,
      conjA_PP ft0.1 (fPF 6 (by omega)).1, conjA_PP ft0.1 (fPF 7 (by omega)).1, szE, szF, szC0,
      szC1, lRE, lRF, lCF, lPE, lPF, lPC0, lPC1]
    simp only [List.all_append, Bool.and_eq_true, List.length_map, List.length_range]
    and_intros
    · exact all_map_intro fun k hk => vA (fRE k hk).1
    · exact all_map_intro fun k hk => vA (fRF k hk).1
    · exact all_map_intro fun k hk => vA (fCF k hk).1
    · exact all_map_intro fun k hk => vA (fPE k hk).1
    · exact all_map_intro fun k hk => vA (fPF k hk).1
    · exact all_map_intro fun k hk => vA (fPC0 k hk).1
    · exact all_map_intro fun k hk => vA (fPC1 k hk).1
    · exact vA (PP.id h64)
    · exact vA ft0.1
    · exact vA (ft0.1.conjK (fPF 6 (by omega)).1)
    · exact vA (ft0.1.conjK (fPF 7 (by omega)).1)
    all_goals rfl
  · unfold srcK at hsrc
    simp only [andB_eq, Bool.and_eq_true] at hsrc
    obtain ⟨r1, r2, o1, o2, c1, c2, m1, m2⟩ := hsrc
    unfold srcG
    simp only [Bool.and_eq_true]
    rw [relsOK_eq W12, relsOK_eq W13, lgetD_unpack p0.gens (by omega : 1 < 2),
      lgetD_unpack p1.gens (by omega : 1 < 2), ord12_eq (q0 1 (by omega)),
      ord12_eq (q1 1 (by omega)), e0, e1, eP, lRE, lRF,
      filter_map_length (q := fun i => comm 32 6 (d.G12 1) (d.T0 i))
        (fun i hi => commN_PP (q0 1 (by omega)) (s0 i hi)),
      filter_map_length (q := fun i => comm 32 6 (d.G13 1) (d.T1 i))
        (fun i hi => commN_PP (q1 1 (by omega)) (s1 i hi)),
      ← HeModelK.cntR_zero, ← HeModelK.cntR_zero, Nat.eq_of_beq_eq_true c1,
      Nat.eq_of_beq_eq_true c2]
    exact ⟨⟨⟨⟨⟨⟨⟨r1, r2⟩, o1⟩, o2⟩, rfl⟩, rfl⟩,
      all_map_allN (fun k hk => inLN_eq (fRE k hk).1 sP) m1⟩,
      all_map_allN (fun k hk => inLN_eq (fRF k hk).1 sP) m2⟩
  · unfold classBG
    rw [eP]
    refine all_map_intro fun j hj => ?_
    have c := hcB j hj
    unfold classBAt at c
    rw [strictB_eq', strictB_eq', orB_eq, Bool.or_eq_true, notB_eq] at c
    rw [ord12_eq (sP j hj), Bool.or_eq_true]
    cases ho : ord12K 64 7 (d.TP j)
    · exact Or.inl rfl
    · rw [ho] at c
      rcases c with c | c
      · exact absurd c (by decide)
      · right
        obtain ⟨hp, e⟩ := conjP_spec sP c
        have hl3 : Nat.land (WB j) 3 < 4 := lt_of_le_of_lt Nat.and_le_right (by omega)
        have pr := (fRE (2 * Nat.land (WB j) 3 + 1) (by omega)).1
        have e' : conj 64 7 (d.TP (Nat.shiftRight (WB j) 2)) (d.RE (2 * Nat.land (WB j) 3 + 1)) =
            d.TP j := e
        refine List.any_eq_true.2 ⟨Nat.land (WB j) 3, List.mem_range.2 hl3, any_map_intro hp ?_⟩
        rw [rE _ hl3 1 (by omega), conjA_PP (sP _ hp) pr, e']
        exact eqA_of_beq (Nat.beq_refl _)
  · unfold classCG
    rw [List.all_eq_true]
    intro i hi
    have hi4 := List.mem_range.1 hi
    rw [eP]
    refine all_map_intro fun j hj => ?_
    have c := hcC i hi4 j hj
    unfold classCAt at c
    simp only [strictB_eq', andB_eq, orB_eq, notB_eq, Bool.and_eq_true, Bool.or_eq_true] at c
    obtain ⟨-, c2, c3⟩ := c
    have vj := inv_of_invOK (sP j hj) c2
    have pr := fRE (2 * i + 1) (by omega)
    have W : WG 64 7 [unpack 64 7 (d.TP j), rEG h i 1] 2
        (pairG (d.TP j) (d.RE (Nat.add (Nat.mul 2 i) 1)))
        (pairG (d.TP (d.IP j)) (d.REI (Nat.add (Nat.mul 2 i) 1))) := by
      rw [rE i hi4 1 (by omega)]
      exact WG_pair h64 (sP j hj) pr.1 vj pr.2
    rw [relsOK_eq W, Bool.or_eq_true]
    rcases c3 with c3 | ⟨c3, c4⟩
    · rw [relsW_eq] at c3
      exact Or.inl c3
    · right
      obtain ⟨hp, e1⟩ := conjP_spec sP c3
      obtain ⟨-, e2⟩ := conjP_spec sP c4
      have hl3 : Nat.land (WC (Nat.add (Nat.mul i d.NP) j)) 3 < 4 :=
        lt_of_le_of_lt Nat.and_le_right (by omega)
      have p0' := (fRE (2 * Nat.land (WC (Nat.add (Nat.mul i d.NP) j)) 3 + 0) (by omega)).1
      have p1' := (fRE (2 * Nat.land (WC (Nat.add (Nat.mul i d.NP) j)) 3 + 1) (by omega)).1
      refine List.any_eq_true.2 ⟨_, List.mem_range.2 hl3, any_map_intro hp ?_⟩
      rw [rE _ hl3 0 (by omega), rE _ hl3 1 (by omega), rE i hi4 1 (by omega),
        conjA_PP (sP _ hp) p0', conjA_PP (sP _ hp) p1', Bool.and_eq_true]
      exact ⟨eqA_of_beq (by rw [Nat.beq_eq]; exact e1), eqA_of_beq (by rw [Nat.beq_eq]; exact e2)⟩
  · unfold repFG
    rw [List.all_eq_true]
    intro j hj
    have hj4 := List.mem_range.1 hj
    have r := allN_spec hrepF j hj4
    simp only [strictB_eq', andB_eq, Bool.and_eq_true] at r
    obtain ⟨r1, r2, r3⟩ := r
    have fc := fCF j hj4
    rw [fc.2, conjW_eq] at r2 r3
    have hs : h.sigmaF.getD j 0 = j := by
      rw [hsig]
      exact (by decide : ∀ j < 4, [0, 1, 2, 3].getD j 0 = j) j hj4
    rw [hs, lgetD_unpack lCF hj4, rE j hj4 0 (by omega), rE j hj4 1 (by omega),
      rF j hj4 0 (by omega), rF j hj4 1 (by omega), conjA_PP fc.1 (fRE (2 * j + 0) (by omega)).1,
      conjA_PP fc.1 (fRE (2 * j + 1) (by omega)).1]
    simp only [Bool.and_eq_true]
    exact ⟨⟨⟨decide_eq_true hj4, inLN_of eP sP fc.1 r1⟩, eqA_of_beq r2⟩, eqA_of_beq r3⟩
  · unfold normBG
    simp only [Bool.and_eq_true]
    refine ⟨?_, ?_⟩
    · have hn : ∀ j < 3072, normAt d j = normsK 64 7 d.NB d.TB d.gB d.GB (d.TP j) := by
        intro j hj
        have c := hcC 0 (by omega) j (by omega)
        unfold classCAt at c
        simp only [strictB_eq', andB_eq, Bool.and_eq_true] at c
        obtain ⟨c1, c2, -⟩ := c
        unfold normAt normsK
        simp only [strictB_eq', andB_eq]
        rw [c1, c2, Bool.true_and, Bool.true_and, inv_of_invOK (sP j (by omega)) c2]
        simp only [inB, conjW_eq, memS_eq hdB]
      have e := hnorm
      unfold normCnt at e
      rw [HeModelK.cntR_zero] at e
      rw [eP, eB, pB.gens,
        filter_map_length (q := fun j => normsK 64 7 d.NB d.TB d.gB d.GB (d.TP j))
          (fun j hj => normsN_eq sB qB (sP j hj)), hNP,
        ← List.filter_congr (p := normAt d)
          (q := fun j => normsK 64 7 d.NB d.TB d.gB d.GB (d.TP j))
          fun j hj => hn j (List.mem_range.1 hj), e]
      rfl
    · rw [List.all_eq_true]
      intro i hi
      have hi4 := List.mem_range.1 hi
      have c := allN_spec hwB i hi4
      rw [rec2_all, List.all_eq_true] at c
      rw [List.all_eq_true]
      intro wd hw
      have c' := c wd hw
      rw [Bool.and_eq_true, inB_eq, inB_eq] at c'
      obtain ⟨ex, px⟩ := evalW_eq (WE i hi4) wd
      obtain ⟨ey, py⟩ := evalW_eq (WF i hi4) wd
      rw [Bool.and_eq_true, ex, ey]
      exact ⟨inLN_of eB sB px c'.1, inLN_of eB sB py c'.2⟩
  · rw [List.all_eq_true]
    intro k hk
    have hk15 := List.mem_range.1 hk
    have hf := hfus k hk15
    have hidx : heWitIdx.getD k (0, 0) = ((k + 1) / 4, (k + 1) % 4) :=
      (by decide : ∀ k < 15, heWitIdx.getD k (0, 0) = ((k + 1) / 4, (k + 1) % 4)) k hk15
    have hi : (k + 1) / 4 < 4 := by omega
    have hj : (k + 1) % 4 < 4 := Nat.mod_lt _ (by omega)
    unfold fusK at hf
    simp only [strictB_eq', andB_eq, Bool.and_eq_true] at hf
    obtain ⟨f1, f2, f3, f4, f5⟩ := hf
    have eW : ∀ u v, eqA 32 (evalW 32 h.p12c u) (evalW 32 h.p13c v) =
        Nat.beq (evalK 32 6 2 d.G12 d.G12I u) (evalK 32 6 2 d.G13 d.G13I v) := fun u v => by
      rw [(evalW_eq W12 u).1, (evalW_eq W13 v).1, eqA_PP (evalW_eq W12 u).2 (evalW_eq W13 v).2]
    have eW' : ∀ u v, eqA 32 (evalW 32 h.p13c u) (evalW 32 h.p12c v) =
        Nat.beq (evalK 32 6 2 d.G13 d.G13I u) (evalK 32 6 2 d.G12 d.G12I v) := fun u v => by
      rw [(evalW_eq W13 u).1, (evalW_eq W12 v).1, eqA_PP (evalW_eq W13 u).2 (evalW_eq W12 v).2]
    unfold fusG
    simp only [hidx]
    obtain ⟨x1e, x1p⟩ := evalW_eq (WE _ hi) (h.wit.getD (4 * k) [])
    obtain ⟨x2e, x2p⟩ := evalW_eq (WE _ hi) (h.wit.getD (4 * k + 2) [])
    obtain ⟨y1e, y1p⟩ := evalW_eq (WF _ hj) (h.wit.getD (4 * k + 1) [])
    obtain ⟨y2e, y2p⟩ := evalW_eq (WF _ hj) (h.wit.getD (4 * k + 3) [])
    rw [eW, eW, eW', eW', x1e, x2e, y1e, y2e, conjG_eq e23 s23 x1p x2p, conjG_eq e23 s23 y1p y2p]
    simp only [Bool.and_eq_true]
    refine ⟨⟨⟨⟨f1, f2⟩, f3⟩, f4⟩, ?_⟩
    have cls := fun {m a b : Nat} {X : Nat → Nat} (hc : classOK d m X a b = true) =>
      classOK_sound p23.ok q23 fG23 s23 hc
    cases he : h.witE.getD k true
    · simp only [he, Bool.and_eq_true] at f5
      simp only [Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true]
      obtain ⟨hq, eq⟩ := conj23_spec s23 f5.1
      refine ⟨List.any_eq_true.2 ⟨_, List.mem_range.2 hq, by rw [Nat.beq_eq]; exact eq⟩, ?_⟩
      exact not_any_of fun q hq e => cls f5.2 q (List.mem_range.1 hq) (Nat.eq_of_beq_eq_true e)
    · simp only [he, Bool.and_eq_true] at f5
      simp only [↓reduceIte, Bool.and_eq_true]
      obtain ⟨hq, eq⟩ := conj23_spec s23 f5.1
      refine ⟨List.any_eq_true.2 ⟨_, List.mem_range.2 hq, by rw [Nat.beq_eq]; exact eq⟩, ?_⟩
      exact not_any_of fun q hq e => cls f5.2 q (List.mem_range.1 hq) (Nat.eq_of_beq_eq_true e)
  · unfold piK at hpi
    simp only [andB_eq, Bool.and_eq_true] at hpi
    obtain ⟨p1', p2', p3'⟩ := hpi
    have hgBC : d.gBC = 4 := Nat.eq_of_beq_eq_true p2'
    unfold piG
    simp only [Bool.and_eq_true]
    refine ⟨?_, ?_⟩
    · rw [List.all_eq_true]
      intro k hk
      have hk5 := List.mem_range.1 hk
      have c := allN_spec p1' k hk5
      simp only [strictB_eq', Bool.and_eq_true] at c
      rw [← piIdx_eq 4 k, ← piIdx_eq 5 k] at c
      obtain ⟨c1, c2, c3, c4, c5, c6⟩ := c
      have i4 := piIdx_lt (by omega : 4 < 8) hk5
      have i5 := piIdx_lt (by omega : 5 < 8) hk5
      rw [(evalW_eq (WE 0 (by omega)) _).1, (evalW_eq (WF 0 (by omega)) _).1,
        (evalW_eq W12 _).1, (evalW_eq W13 _).1, (evalW_eq W13 _).1, (evalW_eq W12 _).1,
        getD_unpack lPE i4, getD_unpack lPF i5, getD_unpack lPC0 i4, getD_unpack lPC0 i5,
        getD_unpack lPC1 i4, getD_unpack lPC1 i5]
      simp only [Bool.and_eq_true]
      exact ⟨⟨⟨⟨⟨eqA_of_beq c1, eqA_of_beq c2⟩, eqA_of_beq c3⟩, eqA_of_beq c4⟩, eqA_of_beq c5⟩,
        eqA_of_beq c6⟩
    · rw [List.all_eq_true]
      intro k hk
      have hk4 := List.mem_range.1 hk
      have c := allN_spec p3' k hk4
      simp only [Bool.and_eq_true] at c
      rw [(evalW_eq W12 _).1, (evalW_eq W13 _).1, lgetD_unpack pBC.gens (by omega),
        Bool.and_eq_true]
      exact ⟨eqA_of_beq c.1, eqA_of_beq c.2⟩
  · unfold kerG
    dsimp only
    rw [getD_unpack lPF (by omega : 6 < 8), getD_unpack lPF (by omega : 7 < 8), et0,
      conjA_PP ft0.1 (fPF 6 (by omega)).1, conjA_PP ft0.1 (fPF 7 (by omega)).1, ← hxT, ← hyT,
      idA_eq h64]
    simp only [Bool.and_eq_true]
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [relsOK_eq WPE]
      exact hkerE
    · rw [e23]
      refine all_map_intro fun j hj => ?_
      have c := hkerY j hj
      unfold kerYAt at c
      simp only [strictB_eq', andB_eq, orB_eq, notB_eq, Bool.and_eq_true, Bool.or_eq_true] at c
      obtain ⟨-, c2, c3⟩ := c
      have vj := inv_of_invOK (s23 j hj) c2
      have Wy := Wt8 lPF fPF (PP.id h64) (s23 j hj) (pinvS_pidn h64).symm vj
      rw [relsOK_eq Wy, Bool.or_eq_true, Bool.or_eq_true]
      rcases c3 with c3 | c3 | c3
      · rw [relsW_eq] at c3
        exact Or.inl (Or.inl c3)
      · exact Or.inl (Or.inr (eqA_of_beq c3))
      · exact Or.inr (eqA_of_beq c3)
    · rw [e23]
      refine all_map_intro fun j hj => ?_
      have c := hkerX j hj
      unfold kerXAt at c
      simp only [strictB_eq', andB_eq, orB_eq, notB_eq, Bool.and_eq_true, Bool.or_eq_true] at c
      obtain ⟨-, c2, c3⟩ := c
      have vj := inv_of_invOK (s23 j hj) c2
      have px := s23 j hj
      have W0 := Wt8 lPF fPF px (PP.id h64) vj (pinvS_pidn h64).symm
      have W1 := Wt8 lPF fPF px (fPF 7 (by omega)).1 vj (fPF 7 (by omega)).2
      have W2 := Wt8 lPF fPF px pyT vj vyT
      rw [relsOK_eq W0, relsOK_eq W1, relsOK_eq W2, Bool.or_eq_true, Bool.and_eq_true,
        Bool.or_eq_true, Bool.or_eq_true]
      rcases c3 with c3 | ⟨c3, c4⟩
      · rw [relsW_eq] at c3
        exact Or.inl c3
      · refine Or.inr ⟨?_, ?_⟩
        · rcases c3 with c3 | c3
          · rw [relsW_eq] at c3
            exact Or.inl c3
          · exact Or.inr (eqA_of_beq c3)
        · rcases c4 with c4 | c4
          · rw [relsW_eq] at c4
            exact Or.inl c4
          · exact Or.inr (eqA_of_beq c4)
  · unfold memK at hmem
    simp only [andB_eq, Bool.and_eq_true] at hmem
    obtain ⟨m0, m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, -, -⟩ := hmem
    unfold memG
    simp only [Bool.and_eq_true, List.all_cons, List.all_nil, Bool.and_true]
    refine ⟨⟨⟨⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ⟨?_, ?_⟩, ?_, ?_⟩
    · rw [List.all_eq_true]
      intro k hk
      have hk4 := List.mem_range.1 hk
      have c := allN_spec m0 k hk4
      simp only [Bool.and_eq_true, inB_eq] at c
      rw [getD_unpack lPE (by omega), getD_unpack lPF (by omega), getD_unpack lPC0 (by omega),
        getD_unpack lPC1 (by omega)]
      simp only [Bool.and_eq_true]
      exact ⟨⟨⟨inLN_of eB sB (fPE k (by omega)).1 c.1, inLN_of eB sB (fPF k (by omega)).1 c.2.1⟩,
        inLN_of eBC sBC (fPC0 k (by omega)).1 c.2.2.1⟩,
        inLN_of eBC sBC (fPC1 k (by omega)).1 c.2.2.2⟩
    · rw [getD_unpack lPE (by omega)]
      exact inLN_of eP sP (fPE 4 (by omega)).1 m1
    · rw [getD_unpack lPF (by omega)]
      exact inLN_of eP sP (fPF 5 (by omega)).1 m2
    · rw [getD_unpack lPC0 (by omega)]
      exact inLN_of e0 s0 (fPC0 4 (by omega)).1 m3
    · rw [getD_unpack lPC0 (by omega)]
      exact inLN_of e1 s1 (fPC0 5 (by omega)).1 m4
    · rw [getD_unpack lPC1 (by omega)]
      exact inLN_of e1 s1 (fPC1 4 (by omega)).1 m5
    · rw [getD_unpack lPC1 (by omega)]
      exact inLN_of e0 s0 (fPC1 5 (by omega)).1 m6
    · rw [getD_unpack lPE (by omega)]
      exact inLN_of e23 s23 (fPE 6 (by omega)).1 m7
    · rw [getD_unpack lPF (by omega)]
      exact inLN_of e23 s23 (fPF 6 (by omega)).1 m8
    · rw [getD_unpack lPE (by omega)]
      exact inLN_of e23 s23 (fPE 7 (by omega)).1 m9
    · rw [getD_unpack lPF (by omega)]
      exact inLN_of e23 s23 (fPF 7 (by omega)).1 m10
  · unfold memK at hmem
    simp only [andB_eq, Bool.and_eq_true] at hmem
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, z1, z2⟩ := hmem
    unfold zG
    rw [(evalW_eq WPC0 _).1, (evalW_eq WPC1 _).1, etc, Bool.and_eq_true]
    exact ⟨eqA_of_beq z1, eqA_of_beq z2⟩
  · unfold genK wordsEqK at hgen
    simp only [andB_eq, Bool.and_eq_true] at hgen
    obtain ⟨⟨l0, a0⟩, ⟨l1, a1⟩, ⟨lT', aT⟩, ⟨lM', aM⟩, ⟨lR', aR⟩⟩ := hgen
    unfold genG
    rw [lC, lT, lM, lR]
    simp only [Bool.and_eq_true, List.length_map, List.length_range]
    refine ⟨⟨⟨⟨⟨⟨⟨⟨beq_iff_eq.2 (Nat.eq_of_beq_eq_true l0),
      beq_iff_eq.2 (Nat.eq_of_beq_eq_true l1)⟩,
      beq_iff_eq.2 (Nat.eq_of_beq_eq_true lT')⟩, beq_iff_eq.2 (Nat.eq_of_beq_eq_true lM')⟩, ?_⟩,
      ?_⟩, ?_⟩, beq_iff_eq.2 (Nat.eq_of_beq_eq_true lR')⟩, ?_⟩
    · rw [List.all_eq_true]
      intro k hk
      have hk' := List.mem_range.1 hk
      rw [getD_map_range, ite_eq_left hk', (evalW_eq WPC0 _).1, (evalW_eq WPC1 _).1,
        Bool.and_eq_true]
      exact ⟨eqA_of_beq (allN_spec a0 k hk'), eqA_of_beq (allN_spec a1 k hk')⟩
    · rw [List.all_eq_true]
      intro k hk
      have hk' := List.mem_range.1 hk
      rw [getD_map_range, ite_eq_left hk', (evalW_eq WPE _).1]
      exact eqA_of_beq (allN_spec aT k hk')
    · rw [List.all_eq_true]
      intro k hk
      have hk' := List.mem_range.1 hk
      rw [getD_map_range, ite_eq_left hk', (evalW_eq WPE _).1]
      exact eqA_of_beq (allN_spec aM k hk')
    · rw [List.all_eq_true]
      intro k hk
      have hk' := List.mem_range.1 hk
      rw [getD_map_range, ite_eq_left hk', (evalW_eq WPE _).1]
      exact eqA_of_beq (allN_spec aR k hk')

end CFSG.KC.HeGlueK

end
