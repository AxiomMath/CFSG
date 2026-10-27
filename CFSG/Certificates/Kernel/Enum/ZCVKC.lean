module

public import CFSG.Certificates.Kernel.Enum.ZCVGlue
public import CFSG.Certificates.Kernel.Enum.ZCVSound
public import CFSG.Certificates.Kernel.Enum.ZCHSound
public import CFSG.Certificates.Kernel.Enum.ZChkISound
public import CFSG.Certificates.Kernel.Enum.SSound

public section

namespace CFSG.KC.EnumSound

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw.Orb CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporLocal

variable {n w : Nat}

theorem zcw_kc (hn : n < 16777216) (hw : n + 1 < 2 ^ w) (hw0 : 0 < w)
    {A AI B BI IDN : Nat} {ga gb : Equiv.Perm (Fin n)} (ha : PRep n w A ga)
    (hai : PRep n w AI ga⁻¹) (hb : PRep n w B gb) (hbi : PRep n w BI gb⁻¹)
    (hid : Nat.beq IDN (pidn n w) = true)
    {OT : Nat → Nat} {RO iw im NL NX nE : Nat}
    (hL : ∀ i < NL, lChk OT 0 0 0 RO n w (mask w) (n * w) (mask (n * w)) iw im NL A AI B BI i =
      true)
    {p : Nat} (hp : p.Prime) {Z ZI : Nat → Nat} {ZW ZL ZP : Nat}
    (hzl : ∀ k < ZL, wl ZW k < 2)
    (hzw : Nat.beq (Z 1) (wperm n w (mask w) A B AI BI ZW ZL) = true)
    (hzpow : zPowOK n w (mask w) (n * w) (Z 1) Z ZI (p + 1) = true)
    (hzp : Nat.beq (Z p) IDN = true) (hzm : Nat.beq (pg w (mask w) (Z 1) ZP) ZP = false)
    (hzP : ZP < n)
    (hX : ∀ i < NX, zChkI OT 0 0 0 RO n w (mask w) (n * w) (mask (n * w)) iw im ZW ZL nE i = true)
    {nC : Nat} {P1 P1I P2 P2I : Nat → Nat → Nat} {O1 O2 W1 L1 W2 L2 : Nat → Nat}
    (hw1 : ∀ c < nC, Nat.beq (P1 c 1) (wperm n w (mask w) A B AI BI (W1 c) (L1 c)) = true)
    (hw2 : ∀ c < nC, Nat.beq (P2 c 1) (wperm n w (mask w) A B AI BI (W2 c) (L2 c)) = true)
    (hp1 : ∀ c < nC, 0 < O1 c ∧ zPowOK n w (mask w) (n * w) (P1 c 1) (P1 c) (P1I c) (O1 c + 1) =
      true ∧ Nat.beq (P1 c (O1 c)) IDN = true)
    (hp2 : ∀ c < nC, 0 < O2 c ∧ zPowOK n w (mask w) (n * w) (P2 c 1) (P2 c) (P2I c) (O2 c + 1) =
      true ∧ Nat.beq (P2 c (O2 c)) IDN = true)
    (hcomm : ∀ c < nC, eq22 n w (mask w) (P1 c 1) (P2 c 1) (P2 c 1) (P1 c 1) = false)
    {HT : Nat → Nat → Nat} {RH : Nat} {NH nR K3 K3P KZ : Nat → Nat} {REP : Nat → Nat → Nat}
    {NC1 NC2 : Nat → Nat → List Nat}
    (hH : ∀ c < nC, ∀ k < NH c, hChk (HT c) 0 0 0 RH n w (mask w) (n * w) (mask (n * w)) (NH c)
      IDN (P1 c 1) (P2 c 1) (nR c) (REP c) k = true)
    (hNH : ∀ c < nC, 0 < NH c ∧ nR c < 15 ∧ ∀ i < nR c, REP c i < NH c)
    (hnc1 : ∀ c < nC, ∀ i < nR c, ncOK (HT c) 0 0 0 RH n w (mask w) (n * w) (mask (n * w)) (NH c)
      (P1 c 1) i (NC1 c i) = true)
    (hnc2 : ∀ c < nC, ∀ i < nR c, ncOK (HT c) 0 0 0 RH n w (mask w) (n * w) (mask (n * w)) (NH c)
      (P2 c 1) i (NC2 c i) = true)
    (hk3 : ∀ c < nC, K3 c < NH c ∧ K3P c < n ∧
      eq3 n w (mask w) IDN (rperm (HT c) 0 0 0 RH (mask (n * w)) (K3 c))
        (rperm (HT c) 0 0 0 RH (mask (n * w)) (K3 c)) (rperm (HT c) 0 0 0 RH (mask (n * w)) (K3 c))
        = true ∧
      Nat.beq (pg w (mask w) (rperm (HT c) 0 0 0 RH (mask (n * w)) (K3 c)) (K3P c)) (K3P c) = false)
    (hkz : ∀ c < nC, KZ c < NH c ∧
      Nat.beq (rperm (HT c) 0 0 0 RH (mask (n * w)) (KZ c)) (Z 1) = true)
    {VP VC1 VC2 : Nat → Nat}
    (hV : ∀ i < NL, NX ≤ i → ∃ c < nC, ∃ o,
      vChkS OT 0 0 0 RO n w (mask w) (mask (n * w)) Z ZI VP VC1 (P1 c 1) (P1I c 1) p o i = true ∧
      vChkS OT 0 0 0 RO n w (mask w) (mask (n * w)) Z ZI VP VC2 (P2 c 1) (P2I c 1) p o i = true)
    {ET : Nat → Nat} {RE NS k : Nat} {gS wS lS : Nat → Nat}
    (hsyl : ∀ j < 3, Nat.beq (gS j) (wperm n w (mask w) A B AI BI (wS j) (lS j)) = true)
    (hS : ∀ i < NS, sChk ET 0 0 0 RE n w (mask w) (n * w) (mask (n * w)) iw im NS IDN gS 3 true OT
      0 0 0 RO NL false 0 (fun _ => 0) 0 (fun _ => 0) 0 i = true)
    (hNS : NS = 2 ^ k)
    (hk : ¬ 2 ^ (k + 1) ∣ Nat.card ↥(Subgroup.closure ({ga, gb} : Set (Equiv.Perm (Fin n))))) :
    ZCW ↥(Subgroup.closure ({ga, gb} : Set (Equiv.Perm (Fin n)))) p := by
  have hwn : n ≤ 2 ^ w := by omega
  have hidp : PRep n w IDN 1 := by
    rw [Nat.eq_of_beq_eq_true hid]
    exact prep_pidn hn hw
  obtain ⟨U, hU, hUc⟩ := lList_prep hL ha hai hb hbi
  obtain ⟨gz, hgzM, hgz0⟩ := wperm_prep (W := ZW) (len := ZL) hn hwn ha hai hb hbi
  have hgz : PRep n w (Z 1) gz := by
    rw [Nat.eq_of_beq_eq_true hzw]
    exact hgz0
  have hgzw : wG ga gb ZW ZL = gz :=
    prep_unique (wperm_prep_word (ai := AI) (bi := BI) hn hwn ha hb hzl) hgz0
  have hZ := zPowOK_prep hzpow hgz
  have hzp1 : gz ^ p = 1 := by
    have h := (hZ p (by omega)).1
    rw [Nat.eq_of_beq_eq_true hzp] at h
    exact prep_unique h hidp
  have hz1 : gz ≠ 1 := ne_one_of_moves hzm hzP hgz
  have hzo : orderOf gz = p := by
    have : Fact p.Prime := ⟨hp⟩
    exact orderOf_eq_prime hzp1 hz1
  have hcand : ∀ c, ∃ g1 g2 : Equiv.Perm (Fin n), c < nC →
      (PRep n w (P1 c 1) g1 ∧ PRep n w (P1I c 1) g1⁻¹ ∧ PRep n w (P2 c 1) g2 ∧
        PRep n w (P2I c 1) g2⁻¹) ∧
      g1 ∈ Subgroup.closure ({ga, gb} : Set (Equiv.Perm (Fin n))) ∧
      g2 ∈ Subgroup.closure ({ga, gb} : Set (Equiv.Perm (Fin n))) ∧
      IsSimpleGroup ↥(Subgroup.closure ({g1, g2} : Set (Equiv.Perm (Fin n)))) ∧
      ¬ IsMulCommutative ↥(Subgroup.closure ({g1, g2} : Set (Equiv.Perm (Fin n)))) ∧
      gz ∈ Subgroup.closure ({g1, g2} : Set (Equiv.Perm (Fin n))) ∧
      3 ∣ Nat.card ↥(Subgroup.closure ({g1, g2} : Set (Equiv.Perm (Fin n)))) := by
    intro c
    by_cases hc : c < nC
    · obtain ⟨g1, hg1M, hg10⟩ := wperm_prep (W := W1 c) (len := L1 c) hn hwn ha hai hb hbi
      obtain ⟨g2, hg2M, hg20⟩ := wperm_prep (W := W2 c) (len := L2 c) hn hwn ha hai hb hbi
      have hg1 : PRep n w (P1 c 1) g1 := by
        rw [Nat.eq_of_beq_eq_true (hw1 c hc)]
        exact hg10
      have hg2 : PRep n w (P2 c 1) g2 := by
        rw [Nat.eq_of_beq_eq_true (hw2 c hc)]
        exact hg20
      obtain ⟨ho1, hq1, hr1⟩ := hp1 c hc
      obtain ⟨ho2, hq2, hr2⟩ := hp2 c hc
      have hP1 := zPowOK_prep hq1 hg1
      have hP2 := zPowOK_prep hq2 hg2
      have he1 : g1 ^ O1 c = 1 := by
        have h := (hP1 (O1 c) (by omega)).1
        rw [Nat.eq_of_beq_eq_true hr1] at h
        exact prep_unique h hidp
      have he2 : g2 ^ O2 c = 1 := by
        have h := (hP2 (O2 c) (by omega)).1
        rw [Nat.eq_of_beq_eq_true hr2] at h
        exact prep_unique h hidp
      have hg1i : PRep n w (P1I c 1) g1⁻¹ := by simpa using (hP1 1 (by omega)).2
      have hg2i : PRep n w (P2I c 1) g2⁻¹ := by simpa using (hP2 1 (by omega)).2
      obtain ⟨hn0, hnR, hrep⟩ := hNH c hc
      obtain ⟨s, hs, hsimp, hncomm, hsH⟩ := hList_simple (iw := 0) (T := HT c)
        (sh := 0) (lm := 0) (rb := 0) (rm := RH) (nw := n * w) (nH := NH c) (idn := IDN)
        (h1 := P1 c 1) (h2 := P2 c 1) (nR := nR c) (REP := REP c) (o1 := O1 c) (o2 := O2 c)
        (NC1 := NC1 c) (NC2 := NC2 c) (hH c hc) hn0 hidp hg1 hg2 ho1 ho2 he1 he2 hnR hrep
        (hnc1 c hc) (hnc2 c hc) (ne_comm_of_eq22 (hcomm c hc) hg1 hg2)
      obtain ⟨hK3, hK3P, hk3e, hk3m⟩ := hk3 c hc
      have hsk := hs (K3 c) hK3
      have h3 : 3 ∣ Nat.card ↥(Subgroup.closure ({g1, g2} : Set (Equiv.Perm (Fin n)))) := by
        have hc3 : s (K3 c) * s (K3 c) * s (K3 c) = 1 :=
          prep_unique (eq3_prep hk3e hsk hsk hsk) hidp
        have hne : s (K3 c) ≠ 1 := ne_one_of_moves hk3m hK3P hsk
        have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
        refine three_dvd_card_of_orderOf_three (hsH (K3 c) hK3) (orderOf_eq_prime ?_ hne)
        rw [pow_succ, pow_two]
        exact hc3
      obtain ⟨hKZ, hkze⟩ := hkz c hc
      have hzH : gz ∈ Subgroup.closure ({g1, g2} : Set (Equiv.Perm (Fin n))) := by
        have he : s (KZ c) = gz := by
          have h := hs (KZ c) hKZ
          rw [Nat.eq_of_beq_eq_true hkze] at h
          exact prep_unique h hgz
        rw [← he]
        exact hsH (KZ c) hKZ
      exact ⟨g1, g2, fun _ => ⟨⟨hg1, hg1i, hg2, hg2i⟩, hg1M, hg2M, hsimp, hncomm, hzH, h3⟩⟩
    · exact ⟨1, 1, fun h => absurd h hc⟩
  choose g1 g2 hgc using hcand
  have hW : ∀ i < NL, (∃ e : Nat, ∃ j < NL, U j = gz ^ e * U i * (gz ^ e)⁻¹ ∧
      U i * U j ≠ U j * U i) ∨
      ∃ c < nC, ∀ g ∈ ({g1 c, g2 c} : Set (Equiv.Perm (Fin n))), ∀ e < p,
        g * (gz ^ e * U i * (gz ^ e)⁻¹) * g⁻¹ ∈
          Subgroup.closure {x | x ∈ (List.range p).map (fun e => gz ^ e * U i * (gz ^ e)⁻¹)} := by
    intro i hi
    by_cases hx : i < NX
    · left
      obtain ⟨e, -, -, j, hj, h1, h2⟩ := zChkI_prep (hX i hx) hL (fun j hj => (hU j hj).1) ha hai
        hb hbi hi
      rw [hgzw] at h1
      exact ⟨e, j, hj, h1, h2⟩
    · right
      obtain ⟨c, hc, o, hv1, hv2⟩ := hV i hi (by omega)
      obtain ⟨⟨hg1, hg1i, hg2, hg2i⟩, -⟩ := hgc c hc
      have hUi := (hU i hi).1
      refine ⟨c, hc, ?_⟩
      rintro g (rfl | hg)
      · exact vChkS_prep hv1 hUi (fun e he => hZ e (by omega)) hg1 hg1i
      · rw [Set.mem_singleton_iff.mp hg]
        exact vChkS_prep hv2 hUi (fun e he => hZ e (by omega)) hg2 hg2i
  have hgens : ∀ j, ∃ g : Equiv.Perm (Fin n), j < 3 → PRep n w (gS j) g ∧
      g ∈ Subgroup.closure ({ga, gb} : Set (Equiv.Perm (Fin n))) := by
    intro j
    by_cases hj : j < 3
    · obtain ⟨g, hg, hgp⟩ := wperm_prep (W := wS j) (len := lS j) hn hwn ha hai hb hbi
      refine ⟨g, fun _ => ⟨?_, hg⟩⟩
      rw [Nat.eq_of_beq_eq_true (hsyl j hj)]
      exact hgp
    · exact ⟨1, fun h => absurd h hj⟩
  choose gG hgG using hgens
  obtain ⟨Ev, hEv, hmul, hinj, hinv⟩ := sList_prep hS hw0 hidp (fun j hj => (hgG j hj).1)
  exact zcw_of_lists_Hs (k := k) hk hgzM hzo (fun i hi => (hUc i hi).1) (fun i hi => (hUc i hi).2)
    (fun c hc => (hgc c hc).2.1) (fun c hc => (hgc c hc).2.2.1) (fun c hc => (hgc c hc).2.2.2.1)
    (fun c hc => (hgc c hc).2.2.2.2.1) (fun c hc => (hgc c hc).2.2.2.2.2.1)
    (fun c hc => (hgc c hc).2.2.2.2.2.2) hW (fun j hj => (hgG j hj).2) hNS
    (fun i hi => (hEv i hi).2) hmul hinj (hinv rfl U fun ix hix => (hU ix hix).1)

theorem zcw_kcB (hn : n < 16777216) (hw : n + 1 < 2 ^ w) (hw0 : 0 < w)
    {A AI B BI IDN : Nat} {ga gb : Equiv.Perm (Fin n)} (ha : PRep n w A ga)
    (hai : PRep n w AI ga⁻¹) (hb : PRep n w B gb) (hbi : PRep n w BI gb⁻¹)
    (hid : Nat.beq IDN (pidn n w) = true)
    {OT : Nat → Nat} {RO iw im NL NX : Nat}
    (hL : lRange OT 0 0 0 RO n w (mask w) (n * w) (mask (n * w)) iw im NL A AI B BI 0 NL = true)
    {p : Nat} (hp : p.Prime) {Z ZI : Nat → Nat} {ZW ZL ZP : Nat}
    (hzl : allN ZL (fun k => Nat.blt (wl ZW k) 2) = true)
    (hzw : Nat.beq (Z 1) (wperm n w (mask w) A B AI BI ZW ZL) = true)
    (hzpow : zPowOK n w (mask w) (n * w) (Z 1) Z ZI (p + 1) = true)
    (hzp : Nat.beq (Z p) IDN = true) (hzm : Nat.beq (pg w (mask w) (Z 1) ZP) ZP = false)
    (hzP : Nat.blt ZP n = true)
    (hX : zRangeI OT 0 0 0 RO n w (mask w) (n * w) (mask (n * w)) iw im ZW ZL (p + 1) 0 NX = true)
    {nC : Nat} {P1 P1I P2 P2I : Nat → Nat → Nat} {O1 O2 W1 L1 W2 L2 : Nat → Nat}
    (hwd : allN nC (fun c => bAnd(Nat.beq (P1 c 1) (wperm n w (mask w) A B AI BI (W1 c) (L1 c)),
      Nat.beq (P2 c 1) (wperm n w (mask w) A B AI BI (W2 c) (L2 c)))) = true)
    (hp1 : allN nC (fun c => bAnd(Nat.blt 0 (O1 c), bAnd(zPowOK n w (mask w) (n * w) (P1 c 1)
      (P1 c) (P1I c) (Nat.succ (O1 c)), Nat.beq (P1 c (O1 c)) IDN))) = true)
    (hp2 : allN nC (fun c => bAnd(Nat.blt 0 (O2 c), bAnd(zPowOK n w (mask w) (n * w) (P2 c 1)
      (P2 c) (P2I c) (Nat.succ (O2 c)), Nat.beq (P2 c (O2 c)) IDN))) = true)
    (hcomm : allN nC (fun c => bIf(eq22 n w (mask w) (P1 c 1) (P2 c 1) (P2 c 1) (P1 c 1), false,
      true)) = true)
    {HT : Nat → Nat → Nat} {RH : Nat} {NH nR K3 K3P KZ : Nat → Nat} {REP : Nat → Nat → Nat}
    {NC1 NC2 : Nat → Nat → List Nat}
    (hH : allN nC (fun c => hRange (HT c) 0 0 0 RH n w (mask w) (n * w) (mask (n * w)) (NH c) IDN
      (P1 c 1) (P2 c 1) (nR c) (REP c) (NH c)) = true)
    (hNH : allN nC (fun c => bAnd(Nat.blt 0 (NH c), bAnd(Nat.blt (nR c) 15,
      allN (nR c) (fun i => Nat.blt (REP c i) (NH c))))) = true)
    (hnc : allN nC (fun c => allN (nR c) (fun i =>
      bAnd(ncOK (HT c) 0 0 0 RH n w (mask w) (n * w) (mask (n * w)) (NH c) (P1 c 1) i (NC1 c i),
        ncOK (HT c) 0 0 0 RH n w (mask w) (n * w) (mask (n * w)) (NH c) (P2 c 1) i (NC2 c i))))
      = true)
    (hk3 : allN nC (fun c => bAnd(Nat.blt (K3 c) (NH c), bAnd(Nat.blt (K3P c) n,
      bAnd(eq3 n w (mask w) IDN (rperm (HT c) 0 0 0 RH (mask (n * w)) (K3 c))
        (rperm (HT c) 0 0 0 RH (mask (n * w)) (K3 c)) (rperm (HT c) 0 0 0 RH (mask (n * w)) (K3 c)),
      bIf(Nat.beq (pg w (mask w) (rperm (HT c) 0 0 0 RH (mask (n * w)) (K3 c)) (K3P c)) (K3P c),
        false, true))))) = true)
    (hkz : allN nC (fun c => bAnd(Nat.blt (KZ c) (NH c),
      Nat.beq (rperm (HT c) 0 0 0 RH (mask (n * w)) (KZ c)) (Z 1))) = true)
    {VP VC1 VC2 XC XN : Nat → Nat}
    (hV : allN nC (fun c => bAnd(
      vRangeS OT 0 0 0 RO n w (mask w) (mask (n * w)) Z ZI VP VC1 (P1 c 1) (P1I c 1) p (XC c)
        (Nat.add NX (XC c)) (XN c),
      vRangeS OT 0 0 0 RO n w (mask w) (mask (n * w)) Z ZI VP VC2 (P2 c 1) (P2I c 1) p (XC c)
        (Nat.add NX (XC c)) (XN c))) = true)
    (hcov : allN (Nat.sub NL NX) (fun t => (List.range nC).any (fun c =>
      Nat.ble (XC c) t && Nat.blt t (Nat.add (XC c) (XN c)))) = true)
    {ET : Nat → Nat} {RE NS k : Nat} {gS wS lS : Nat → Nat}
    (hsyl : allN 3 (fun j => Nat.beq (gS j) (wperm n w (mask w) A B AI BI (wS j) (lS j))) = true)
    (hS : sRange ET 0 0 0 RE n w (mask w) (n * w) (mask (n * w)) iw im NS IDN gS 3 true OT 0 0 0
      RO NL false 0 (fun _ => 0) 0 (fun _ => 0) 0 0 NS = true)
    (hNS : NS = 2 ^ k)
    (hk : ¬ 2 ^ (k + 1) ∣ Nat.card ↥(Subgroup.closure ({ga, gb} : Set (Equiv.Perm (Fin n))))) :
    ZCW ↥(Subgroup.closure ({ga, gb} : Set (Equiv.Perm (Fin n)))) p := by
  simp only [PK.allN_iff, PK.bAnd_eq, Bool.and_eq_true, Nat.blt_eq] at hzl hwd hp1 hp2 hNH hnc
  simp only [PK.allN_iff, PK.bAnd_eq, Bool.and_eq_true, Nat.blt_eq] at hk3 hkz hV hsyl
  simp only [PK.allN_iff, List.any_eq_true, List.mem_range, Bool.and_eq_true, Nat.ble_eq,
    Nat.blt_eq] at hcov
  rw [PK.allN_iff] at hcomm hH
  refine zcw_kc hn hw hw0 ha hai hb hbi hid
    (fun i hi => by have h := lRange_iff.1 hL i hi; rwa [Nat.zero_add] at h) hp hzl hzw hzpow hzp
    hzm (Nat.blt_eq.mp hzP)
    (fun i hi => by have h := zRangeI_iff.1 hX i hi; rwa [Nat.zero_add] at h)
    (fun c hc => (hwd c hc).1) (fun c hc => (hwd c hc).2) hp1 hp2 (fun c hc => bIf_ft (hcomm c hc))
    (fun c hc => hRange_iff.1 (hH c hc)) hNH (fun c hc i hi => (hnc c hc i hi).1)
    (fun c hc i hi => (hnc c hc i hi).2)
    (fun c hc => ⟨(hk3 c hc).1, (hk3 c hc).2.1, (hk3 c hc).2.2.1, bIf_ft (hk3 c hc).2.2.2⟩) hkz
    (VP := VP) (VC1 := VC1) (VC2 := VC2) ?_ hsyl
    (fun i hi => by have h := sRange_iff.1 hS i hi; rwa [Nat.zero_add] at h) hNS hk
  intro i hi hx
  obtain ⟨c, hc, h1, h2⟩ := hcov (i - NX) (by simp only [Nat.sub_eq]; omega)
  refine ⟨c, hc, p * (XC c + (i - NX - XC c)), ?_, ?_⟩
  · have h := vRangeS_iff.1 (hV c hc).1 (i - NX - XC c) (by simp only [Nat.add_eq] at h2; omega)
    rwa [show Nat.add NX (XC c) + (i - NX - XC c) = i by simp only [Nat.add_eq]; omega] at h
  · have h := vRangeS_iff.1 (hV c hc).2 (i - NX - XC c) (by simp only [Nat.add_eq] at h2; omega)
    rwa [show Nat.add NX (XC c) + (i - NX - XC c) = i by simp only [Nat.add_eq]; omega] at h

end CFSG.KC.EnumSound

end
