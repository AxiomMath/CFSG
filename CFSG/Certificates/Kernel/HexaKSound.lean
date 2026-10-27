
module

public import Certificates.Data.Kernel.HexaK
public import CFSG.Certificates.Kernel.BfsPinUnpack
import CFSG.Certificates.Kernel.HexaKGlue
public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec4HexaTests
import CFSG.Certificates.Kernel.BfsPinSetSound

public section

namespace CFSG.KC.HexaK

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw CFSG.KC.BfsPin
open CFSG.Monster.B.Co2.Native CFSG.RankThree.Native CFSG.ComponentClassification.AS81.Hexa
open CFSG.ComponentClassification.AS81.HeSylow
open CFSG.KLie.CT (anyN andB orB notB)

@[expose] def hexaCheckG (gT gM gC gN gR : List (Array Nat)) (t0 : Array Nat) (W : List Nat)
    (F : Nat × Nat × Nat) (blk4 rep4 blk2 rep2 : Array Nat) : Bool :=
  let T := eltsN 64 gT
  let M := eltsN 64 gM
  let C := eltsN 64 gC
  let N := eltsN 64 gN
  let R := eltsN 64 gR
  enumCheckN 64 gT 64 && enumCheckN 64 gM 2160 && enumCheckN 64 gC 48 &&
    enumCheckN 64 gN 8 && enumCheckN 64 gR 4 && validA 64 t0 &&
    gR.all (inLN 64 T) &&
    gM.all (fun g => gT.all fun q => inLN 64 T (conjA 64 g q)) &&
    orbitW 64 T M t0 W &&
    gC.all (inLN 64 M) && gC.all (fun g => commN 64 g t0) &&
    (M.filter fun m => commN 64 m t0).length == 48 &&
    gC.all (fun g => eqA 64 (powN 64 g 4) (idA 64)) &&
    moveN 64 M gC gR R &&
    gC.all (fun g => gN.all fun q => inLN 64 N (conjA 64 g q)) &&
    normalE8N 64 T C N t0 &&
    blockN 64 4 C blk4 rep4 && blockN 64 2 C blk2 rep2 &&
    faithfulN 64 C blk4 rep4 4 blk2 rep2 2 && fuseW 64 T M N t0 F

theorem hexaCheck_eq : hexaCheck = hexaCheckG hexaTGens hexaMGens hexaCGens hexaN0Gens
    hexaR0Gens hexaT0 hexaOrbConj hexaFuseW hexaBlk4 hexaRep4 hexaBlk2 hexaRep2 := rfl

structure Pin (n w : Nat) (gs : List (Array Nat)) (g : Nat) (G : Nat → Nat) (N : Nat)
    (T E S : Nat → Nat) : Prop where
  size : gs.toArray.size = g
  bind : ∀ k < g, gs.toArray[k]! = unpack n w (G k)
  perm : ∀ k < g, permOK n w (mask w) (n * w) (G k) (pinvS n w (mask w) (G k)) = true
  ok : bfsK n w g G N T E S = true
  fuel : N ≤ 4000

namespace Pin

variable {n w : Nat} {gs : List (Array Nat)} {g : Nat} {G : Nat → Nat} {N : Nat} {T E S : Nat → Nat}

private theorem gen (p : Pin n w gs g G N T E S) : ∀ k < g, PP n w (G k) := PP_gen p.ok p.perm

private theorem pts (p : Pin n w gs g G N T E S) : ∀ i < N, PP n w (T i) := PP_pts p.ok p.perm

private theorem gens (p : Pin n w gs g G N T E S) :
    gs = (List.range g).map fun k => unpack n w (G k) :=
  gens_eq p.size p.bind

private theorem elts (p : Pin n w gs g G N T E S) :
    eltsN n gs = (List.range N).map fun i => unpack n w (T i) :=
  eltsN_eq p.size p.bind p.ok p.fuel

private theorem check (p : Pin n w gs g G N T E S) : enumCheckN n gs N = true :=
  enumCheckN_of p.size p.bind p.perm p.ok p.fuel

end Pin

private theorem blockN_eq {n w k N : Nat} {T : Nat → Nat} {blk rep : Array Nat} :
    blockN n k ((List.range N).map fun i => unpack n w (T i)) blk rep =
      blockK n w k N T blk rep := by
  unfold blockN blockK
  have e1 : ((List.range k).all fun i => decide (rep[i]! < n) && blk[rep[i]!]! == i) =
      (List.range k).all fun i => CFSG.KLie.CT.andB (Nat.blt rep[i]! n) (Nat.beq blk[rep[i]!]! i) :=
    all_congr_mem fun i _ => by rw [andB_eq, blt_eq_decide, beq_nat]
  have e2 : (((List.range N).map fun i => unpack n w (T i)).all fun t => (List.range n).all fun v =>
      !(decide (blk[v]! < k)) ||
        (decide (blk[t[v]!]! < k) && blk[t[v]!]! == blk[t[rep[blk[v]!]!]!]!)) =
      allN N fun j => strictB (T j) fun t => (List.range n).all fun v =>
        CFSG.KLie.CT.orB (CFSG.KLie.CT.notB (Nat.blt blk[v]! k))
          (CFSG.KLie.CT.andB (Nat.blt blk[pgC n w t v]! k)
            (Nat.beq blk[pgC n w t v]! blk[pgC n w t rep[blk[v]!]!]!)) := by
    rw [allN_eq']
    refine all_map_congr fun j _ => ?_
    rw [strictB_eq']
    refine all_congr_mem fun v _ => ?_
    simp only [orB_eq, andB_eq, notB_eq, pgC_eq, blt_eq_decide, beq_nat]
  rw [e1, e2, andB_eq]

theorem hexaK_sound {w : Nat} {gT gM gC gN gR : List (Array Nat)}
    {cT cM cC cN cR NT NM NC NN NR : Nat}
    {GT GM GC GN GR TT TM TC TN TR ET EM EC EN ER ST SM SC SN SR : Nat → Nat}
    {t0 : Array Nat} {P0 : Nat} {W : List Nat} {F : Nat × Nat × Nat}
    {blk4 rep4 blk2 rep2 : Array Nat}
    (pT : Pin 64 w gT cT GT NT TT ET ST) (pM : Pin 64 w gM cM GM NM TM EM SM)
    (pC : Pin 64 w gC cC GC NC TC EC SC) (pN : Pin 64 w gN cN GN NN TN EN SN)
    (pR : Pin 64 w gR cR GR NR TR ER SR)
    (h0 : t0 = unpack 64 w P0) (hp0 : permOK 64 w (mask w) (64 * w) P0 (pinvS 64 w (mask w) P0) = true)
    (hsz : NT = 64 ∧ NM = 2160 ∧ NC = 48 ∧ NN = 8 ∧ NR = 4)
    (hg : gensK 64 w cT GT cM GM cC GC cN GN cR GR NT TT NM TM NN TN P0 = true)
    (ho : orbitK 64 w NT TT NM TM P0 W = true)
    (hc : countK 64 w NM TM P0 = 48)
    (hm : moveK 64 w NM TM cC GC cR GR NR TR = true)
    (hn : normalK 64 w NT TT NC TC NN TN P0 = true)
    (hb4 : blockK 64 w 4 NC TC blk4 rep4 = true) (hb2 : blockK 64 w 2 NC TC blk2 rep2 = true)
    (hfa : faithfulK 64 w NC TC blk4 rep4 4 blk2 rep2 2 = true)
    (hfu : fuseK 64 w NT TT NM TM NN TN P0 F.1 F.2.1 F.2.2 = true) :
    hexaCheckG gT gM gC gN gR t0 W F blk4 rep4 blk2 rep2 = true := by
  obtain ⟨hNT, hNM, hNC, hNN, hNR⟩ := hsz
  have sT := pT.pts
  have sM := pM.pts
  have sC := pC.pts
  have sN := pN.pts
  have sR := pR.pts
  have qT := pT.gen
  have qM := pM.gen
  have qC := pC.gen
  have qN := pN.gen
  have qR := pR.gen
  have hsz : szOK 64 w := (sT 0 (by omega)).sz
  have p0 : PP 64 w P0 := PP_of_permOK hsz hp0
  have hid := PP.id hsz
  subst h0
  unfold hexaCheckG
  rw [pT.elts, pM.elts, pC.elts, pN.elts, pR.elts]
  unfold gensK at hg
  simp only [andB_eq, Bool.and_eq_true] at hg
  obtain ⟨g1, g2, g3, g4, g5, g6⟩ := hg
  simp only [Bool.and_eq_true]
  refine ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩,
    ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · have e := pT.check
    rwa [hNT] at e
  · have e := pM.check
    rwa [hNM] at e
  · have e := pC.check
    rwa [hNC] at e
  · have e := pN.check
    rwa [hNN] at e
  · have e := pR.check
    rwa [hNR] at e
  · exact validA_unpack hp0
  ·
    rw [pR.gens, all_map_congr fun k hk => inLN_eq (qR k (List.mem_range.1 hk)) sT]
    exact List.all_eq_true.2 fun k hk => by
      have := allN_spec g1 k (List.mem_range.1 hk)
      exact this
  ·
    rw [pM.gens, pT.gens, List.all_map]
    refine List.all_eq_true.2 fun k hk => ?_
    rw [List.mem_range] at hk
    rw [Function.comp_apply, List.all_map]
    refine List.all_eq_true.2 fun q hq => ?_
    rw [List.mem_range] at hq
    rw [Function.comp_apply, conjA_PP (qM k hk) (qT q hq),
      inLN_eq ((qM k hk).conjK (qT q hq)) sT]
    exact allN_spec (allN_spec g2 k hk) q hq
  ·
    unfold orbitW
    rw [List.length_map, List.length_range]
    unfold orbitK at ho
    refine List.all_eq_true.2 fun i hi => ?_
    have hi' := List.mem_range.1 hi
    have hk := List.all_eq_true.1 ho i hi
    unfold orbitAt at hk
    rw [strictB_eq'] at hk
    rw [getElem!_map_range _ hi', eqA_id_PP (sT i hi'), List.length_map, List.length_range,
      invCentN_eq sM (sT i hi'), noE8N_eq fun a ha => mem_invCent sM ha,
      List.getElem!_eq_getElem?_getD, ← List.getD_eq_getElem?_getD]
    have hd : (default : Nat) = 0 := rfl
    rw [hd]
    simp only [orB_eq, andB_eq] at hk
    have e : (decide (W.getD i 0 < NM) &&
        eqA 64 (conjA 64 ((List.range NM).map fun i => unpack 64 w (TM i))[W.getD i 0]!
          (unpack 64 w (TT i))) (unpack 64 w P0)) =
        (Nat.blt (W.getD i 0) NM && Nat.beq (conj 64 w (TM (W.getD i 0)) (TT i)) P0) := by
      rw [blt_eq_decide]
      by_cases hw : W.getD i 0 < NM
      · rw [getElem!_map_range _ hw, conjA_PP (sM _ hw) (sT i hi'),
          eqA_PP ((sM _ hw).conjK (sT i hi')) p0]
      · rw [decide_eq_false hw, Bool.false_and, Bool.false_and]
    rw [e]
    exact hk
  ·
    rw [pC.gens, all_map_congr fun k hk => inLN_eq (qC k (List.mem_range.1 hk)) sM]
    exact List.all_eq_true.2 fun k hk => allN_spec g3 k (List.mem_range.1 hk)
  ·
    rw [pC.gens, all_map_congr (p := fun g => commN 64 g (unpack 64 w P0))
      fun k hk => commN_PP (qC k (List.mem_range.1 hk)) p0]
    exact List.all_eq_true.2 fun k hk => allN_spec g4 k (List.mem_range.1 hk)
  ·
    rw [List.filter_map, List.length_map]
    have e : (List.range NM).filter ((fun g => commN 64 g (unpack 64 w P0)) ∘
        fun i => unpack 64 w (TM i)) = (List.range NM).filter fun j => comm 64 w (TM j) P0 :=
      List.filter_congr fun j hj => commN_PP (sM j (List.mem_range.1 hj)) p0
    unfold countK at hc
    rw [sumN_count] at hc
    rw [e, hc]
    rfl
  ·
    rw [pC.gens, List.all_map]
    refine List.all_eq_true.2 fun k hk => ?_
    rw [List.mem_range] at hk
    rw [Function.comp_apply, powN4_PP (qC k hk), eqA_id_PP (qC k hk).pow4K]
    exact allN_spec g5 k hk
  ·
    unfold moveN
    unfold moveK at hm
    rw [allN_eq'] at hm
    rw [pC.gens, pR.gens]
    refine (all_map_congr fun j hj => ?_).trans hm
    have hj' := List.mem_range.1 hj
    have pm := sM j hj'
    rw [strictB_eq', anyN_eq]
    refine any_map_congr fun k hk => ?_
    have pk := qC k (List.mem_range.1 hk)
    rw [anyN_eq]
    refine any_map_congr fun r hr => ?_
    have pr := qR r (List.mem_range.1 hr)
    rw [conjA_PP pm pr, conjA_PP pk (pm.conjK pr), conjInvA_PP pm (pk.conjK (pm.conjK pr)),
      inLN_eq (pm.conjInvK (pk.conjK (pm.conjK pr))) sR, notB_eq]
  ·
    rw [pC.gens, pN.gens, List.all_map]
    refine List.all_eq_true.2 fun k hk => ?_
    rw [List.mem_range] at hk
    rw [Function.comp_apply, List.all_map]
    refine List.all_eq_true.2 fun q hq => ?_
    rw [List.mem_range] at hq
    rw [Function.comp_apply, conjA_PP (qC k hk) (qN q hq),
      inLN_eq ((qC k hk).conjK (qN q hq)) sN]
    exact allN_spec (allN_spec g6 k hk) q hq
  ·
    unfold normalE8N
    unfold normalK at hn
    rw [invCentN_eq sC p0]
    refine (all_map_congr fun a ha => ?_).trans hn
    have pa := mem_invCent sC ha
    rw [inLN_eq pa sN, orB_eq, anyN_eq]
    congr 1
    refine any_map_congr fun t ht => ?_
    have pt := sT t (List.mem_range.1 ht)
    rw [strictB_eq', eqA_id_PP pt, eqA_PP pt p0, andB_eq, andB_eq, notB_eq, notB_eq,
      Bool.and_assoc]
    congr 2
    refine all_map_congr fun b hb => ?_
    have pb := mem_invCent sC hb
    rw [commN_PP pa pb, commN_PP pb pt, orB_eq, notB_eq]
  · exact blockN_eq.trans hb4
  · exact blockN_eq.trans hb2
  ·
    unfold faithfulN
    unfold faithfulK at hfa
    rw [allN_eq'] at hfa
    refine (all_map_congr fun j hj => ?_).trans hfa
    have pt := sC j (List.mem_range.1 hj)
    rw [strictB_eq', eqA_id_PP pt]
    simp only [orB_eq, notB_eq, pgC_eq, beq_nat, Bool.or_assoc]
  ·
    unfold fuseW
    unfold fuseK at hfu
    simp only [andB_eq, Bool.and_eq_true, blt_eq_decide, decide_eq_true_eq] at hfu
    obtain ⟨ha, hx, hm, hk⟩ := hfu
    rw [strictB_eq'] at hk
    simp only [notB_eq, Bool.and_eq_true, Bool.not_eq_true'] at hk
    have pa := sN _ ha
    have px := sT _ hx
    have pm := sM _ hm
    simp only [List.length_map, List.length_range, getElem!_map_range _ ha, getElem!_map_range _ hx,
      getElem!_map_range _ hm, commutatorA_PP pa px, eqA_id_PP (pa.commuK px),
      eqA_PP (pa.commuK px) p0, conjA_PP pm (pa.commuK px), eqA_PP (pm.conjK (pa.commuK px)) p0,
      Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true']
    exact ⟨⟨⟨⟨⟨ha, hx⟩, hm⟩, hk.1⟩, hk.2.1⟩, hk.2.2⟩

end CFSG.KC.HexaK

end
