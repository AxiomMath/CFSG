module

public import Certificates.Data.Kernel.HexaStabK
public import CFSG.Certificates.Kernel.HexaKSound
public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec4HexaStabTests
import CFSG.Certificates.Kernel.HexaStabKGlue
import CFSG.Certificates.Kernel.BfsPinSetSound

public section

namespace CFSG.KC.HexaStabK

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw CFSG.KC.BfsPin CFSG.KC.HexaK
open CFSG.Monster.B.Co2.Native CFSG.RankThree.Native CFSG.ComponentClassification.AS81.Hexa
open CFSG.ComponentClassification.AS81.HeSylow
open CFSG.KLie.CT (pw2 orB andB notB)
open CFSG.KC.N48K (pw2_eq)

@[expose] def ovalPresAG (oval : List (List ℕ)) (t : Array ℕ) : Bool :=
  oval.all fun L => oval.any fun L' => L.all fun x => L'.contains t[x]!

@[expose] def ovalPairsG (oval : List (List ℕ)) : List (ℕ × ℕ) :=
  oval.flatMap fun L => (L.filter (· != 0)).flatMap fun a =>
    ((L.filter (· != 0)).filter (· != a)).map fun b => (a, b)

@[expose] def stabCandsG (oval : List (List ℕ)) : List (Array ℕ) :=
  (ovalPairsG oval).flatMap fun p => (ovalPairsG oval).flatMap fun q => (ovalPairsG oval).map fun r =>
    linA [p.1, p.2, q.1, q.2, r.1, r.2]

@[expose] def stabWG (oval : List (List ℕ)) (M : List (Array ℕ)) (W : List ℕ) : Bool :=
  (List.range (stabCandsG oval).length).all fun c =>
    !(ovalPresAG oval (stabCandsG oval)[c]! && injA (stabCandsG oval)[c]!) ||
      (decide (stabIdx W c < M.length) && eqA 64 (stabCandsG oval)[c]! M[stabIdx W c]!)

@[expose] def offFrameG (oval : List (List ℕ)) (x : ℕ) : Bool :=
  framePairs.all fun p => !((spanL oval[p.1]! oval[p.2]!).contains x)

@[expose] def ovalCompNG (oval : List (List ℕ)) : Bool :=
  (List.range 64).all fun a => (List.range 64).all fun b =>
    !(a != 0 && b != 0 && a != b && offFrameG oval a && offFrameG oval b &&
        offFrameG oval (a ^^^ b)) ||
      (oval[4]!.contains a && oval[4]!.contains b) ||
      (oval[5]!.contains a && oval[5]!.contains b)

@[expose] def hexaStabCheckG (gT gR gM gM2 : List (Array ℕ)) (oval : List (List ℕ)) (W : List ℕ) :
    Bool :=
  let M := eltsN 64 gM
  gT == (List.range 6).map (fun i => translA (2 ^ i)) &&
    gR == [translA 1, translA 2] && stabWG oval M W &&
    enumCheckN 64 gM2 2160 && gM2.all (inLN 64 M) &&
    gM2.all (fun a => eqA 64 (powN 64 a 4) (idA 64)) && ovalCompNG oval

theorem hexaStabCheck_eq : hexaStabCheck =
    hexaStabCheckG hexaTGens hexaR0Gens hexaMGens hexaM2Gens hexaOval hexaStabW := rfl

theorem hexaStabK_sound {w : Nat} {gT gR gM gM2 : List (Array ℕ)} {oval : List (List ℕ)}
    {W : List ℕ} {cT cR cM cM2 NM NM2 : Nat}
    {GT GR GM GM2 TM EM SM TM2 EM2 SM2 : Nat → Nat}
    (hT : gT.toArray.size = cT ∧ ∀ k < cT, gT.toArray[k]! = unpack 64 w (GT k))
    (hR : gR.toArray.size = cR ∧ ∀ k < cR, gR.toArray[k]! = unpack 64 w (GR k))
    (pM : Pin 64 w gM cM GM NM TM EM SM) (pM2 : Pin 64 w gM2 cM2 GM2 NM2 TM2 EM2 SM2)
    (htr : (Nat.beq cT 6 && allN 6 (fun k => Nat.beq (GT k) (translK w (pw2 k))) &&
      Nat.beq cR 2 && Nat.beq (GR 0) (translK w 1) && Nat.beq (GR 1) (translK w 2)) = true)
    (hov : ovalOK oval = true)
    (hst : ∀ i < (ovalPairsG oval).length, stabBlockK w oval (ovalPairsG oval) NM TM W i = true)
    (hm2 : (Nat.beq NM2 2160 && allN cM2 (fun k => inL NM TM (GM2 k)) &&
      allN cM2 (fun k => Nat.beq (pow4 64 w (GM2 k)) (pidn 64 w))) = true)
    (hc : ovalCompNG oval = true) :
    hexaStabCheckG gT gR gM gM2 oval W = true := by
  have sM := PP_pts pM.ok pM.perm
  have qM2 := PP_gen pM2.ok pM2.perm
  have hsz : szOK 64 w :=
    (sM 0 (bfsK_points (fun _ => True) trivial (fun _ _ _ _ => trivial) pM.ok).1).sz
  have hw : 64 < 2 ^ w := by
    have := (szOK_facts' hsz).2
    omega
  have eM := eltsN_eq pM.size pM.bind pM.ok pM.fuel
  simp only [Bool.and_eq_true] at htr hm2
  obtain ⟨⟨⟨⟨hcT, hGT⟩, hcR⟩, hGR0⟩, hGR1⟩ := htr
  obtain ⟨⟨hNM2, hin⟩, hpow⟩ := hm2
  have hcT' := Nat.eq_of_beq_eq_true hcT
  have hcR' := Nat.eq_of_beq_eq_true hcR
  unfold hexaStabCheckG
  rw [eM]
  simp only [Bool.and_eq_true]
  refine ⟨⟨⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, hc⟩
  ·
    rw [gens_eq hT.1 hT.2, hcT']
    apply beq_iff_eq.2
    refine List.map_congr_left fun k hk => ?_
    have hk' := List.mem_range.1 hk
    rw [Nat.eq_of_beq_eq_true (allN_spec hGT k hk'), pw2_eq]
    exact (translA_eq hw (by interval_cases k <;> decide)).symm
  ·
    rw [gens_eq hR.1 hR.2, hcR']
    apply beq_iff_eq.2
    change [unpack 64 w (GR 0), unpack 64 w (GR 1)] = _
    rw [Nat.eq_of_beq_eq_true hGR0, Nat.eq_of_beq_eq_true hGR1, ← translA_eq hw (by decide),
      ← translA_eq hw (by decide)]
  ·
    unfold stabWG stabCandsG
    rw [length_flatMap3]
    refine List.all_eq_true.2 fun c hc' => ?_
    have hc := List.mem_range.1 hc'
    set P := ovalPairsG oval
    set L := P.length
    have hL : 0 < L := Nat.pos_of_ne_zero fun h => by rw [h] at hc; simp at hc
    have hi : c / (L * L) < L := (Nat.div_lt_iff_lt_mul (Nat.mul_pos hL hL)).2 (by
      rw [Nat.mul_comm L (L * L), Nat.mul_assoc]; exact hc)
    have hj : c / L % L < L := Nat.mod_lt _ hL
    have hk : c % L < L := Nat.mod_lt _ hL
    have hcijk : (c / (L * L) * L + c / L % L) * L + c % L = c := by
      rw [← Nat.div_div_eq_div_mul, Nat.div_add_mod', Nat.div_add_mod']
    have hb := hst _ hi
    unfold stabBlockK at hb
    rw [strictB_eq'] at hb
    have hb' := List.all_eq_true.1 (List.all_eq_true.1 hb _ (List.mem_range.2 hj)) _
      (List.mem_range.2 hk)
    change candOK w oval NM TM W ((c / (L * L) * L + c / L % L) * L + c % L) _ = true at hb'
    rw [hcijk] at hb'
    have hgD : ∀ m (hm : m < L), P.getD m (0, 0) = P[m]'hm := fun m hm => by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hm, Option.getD_some]
    rw [hgD _ hi, hgD _ hj, hgD _ hk] at hb'
    rw [← hcijk, getElem!_flatMap3 P _ hi hj hk, hcijk]
    have himgs : ∀ x ∈ candImgs P[c / (L * L)] P[c / L % L] P[c % L], x < 64 := by
      have h1 := ovalPairs_lt hov (List.getElem_mem hi)
      have h2 := ovalPairs_lt hov (List.getElem_mem hj)
      have h3 := ovalPairs_lt hov (List.getElem_mem hk)
      intro x hx
      simp only [candImgs, List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> omega
    change !(ovalPresAG oval (linA (candImgs _ _ _)) && injA (linA (candImgs _ _ _))) ||
      (decide (stabIdx W c < ((List.range NM).map fun i => unpack 64 w (TM i)).length) &&
        eqA 64 (linA (candImgs _ _ _)) ((List.range NM).map fun i => unpack 64 w (TM i))[
          stabIdx W c]!) = true
    unfold candOK at hb'
    rw [orB_eq, notB_eq, andB_eq, strictB_eq', strictB_eq', strictB_eq', andB_eq,
      presL_eq hw hov himgs] at hb'
    rw [Bool.or_eq_true, Bool.not_eq_true', Bool.and_eq_false_iff] at hb' ⊢
    rcases hb' with hb' | hb'
    · left
      rcases hb' with hb' | hb'
      · exact Or.inl hb'
      · right
        cases hA : injA (linA (candImgs P[c / (L * L)] P[c / L % L] P[c % L]))
        · rfl
        · rw [linA_eq hw himgs] at hA
          rw [injK_of_injA hA] at hb'
          cases hb'
    · right
      have hidx : stabIdx W c = Nat.mod (Nat.shiftRight (W.getD (Nat.div c 648) 0)
          (Nat.mul 12 (Nat.mod c 648))) 4096 := by
        unfold stabIdx
        rw [List.getElem!_eq_getElem?_getD, ← List.getD_eq_getElem?_getD]
        rfl
      rw [Bool.and_eq_true] at hb'
      have hlt : stabIdx W c < NM := by
        rw [hidx]
        exact Nat.blt_eq.mp hb'.1
      have heq := Nat.eq_of_beq_eq_true hb'.2
      rw [List.length_map, List.length_range, decide_eq_true hlt, Bool.true_and,
        getElem!_map_range _ hlt, linA_eq hw himgs, hidx, heq]
      exact CFSG.Monster.B.Co2.allLt_iff.2 fun i _ => beq_self_eq_true _
  · have e := enumCheckN_of pM2.size pM2.bind pM2.perm pM2.ok pM2.fuel
    rwa [Nat.eq_of_beq_eq_true hNM2] at e
  · rw [gens_eq pM2.size pM2.bind, List.all_map]
    refine List.all_eq_true.2 fun k hk => ?_
    rw [List.mem_range] at hk
    rw [Function.comp_apply, inLN_eq (qM2 k hk) sM]
    exact allN_spec hin k hk
  · rw [gens_eq pM2.size pM2.bind, List.all_map]
    refine List.all_eq_true.2 fun k hk => ?_
    rw [List.mem_range] at hk
    rw [Function.comp_apply, powN4_PP (qM2 k hk), eqA_id_PP (qM2 k hk).pow4K]
    exact allN_spec hpow k hk

end CFSG.KC.HexaStabK

end
