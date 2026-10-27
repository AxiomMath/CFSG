module

public import CFSG.Certificates.Kernel.Q47KRunSound
import CFSG.Certificates.Kernel.HexaKGlue
import CFSG.Certificates.Kernel.PackSetSound
import CFSG.Certificates.Kernel.FusYKSound
import CFSG.Certificates.Kernel.Q47KOSound
import CFSG.Certificates.Kernel.Q47KTabSound
public import CFSG.Certificates.Kernel.Q47KGlue
import CFSG.Certificates.Kernel.Q47KModelSound

public section

namespace CFSG.KC.Q47K

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw CFSG.KC.BfsPin CFSG.KC.HexaK CFSG.KC.HeAutK
open CFSG.Monster.B.Co2.Native CFSG.RankThree.Native CFSG.ComponentClassification.AS81.HeSylow
open CFSG.ComponentClassification.AS81.Q47 CFSG.ComponentClassification.GrSLit.HeldFix
open CFSG.KLie.CT (anyN andB orB notB)

theorem all_bound_inv {n w : Nat} {gs : List (Array Nat)} {G : Nat → Nat} (b : Bound n w gs G)
    {f : Array Nat → Bool} (h : gs.all f = true) : ∀ k < gs.length, f (unpack n w (G k)) = true := by
  rw [list_of_bound b, List.all_map, List.all_eq_true] at h
  exact fun k hk => h k (List.mem_range.2 hk)

theorem l30Tab_get {l30 : List (Array Nat)} {j : Nat} (hj : j < l30.length) :
    (l30TabG l30)[j]! = memTab (l30.getD j #[]) := by
  unfold l30TabG
  rw [getElem!_pos _ j (by simpa using hj), Array.getElem_map, List.getElem_toArray,
    List.getD_eq_getElem _ _ hj]

theorem projK_sound {a b : Nat} (h : projK a b = true) : projEq7 (matOf 2 a) (matOf 2 b) = true := by
  unfold projK at h
  rw [anyN_eq, List.any_eq_true] at h
  obtain ⟨l, hl, h⟩ := h
  rw [andB_eq, Bool.and_eq_true, notB_eq] at h
  unfold projEq7
  rw [List.any_eq_true]
  refine ⟨l, hl, ?_⟩
  rw [Bool.and_eq_true]
  refine ⟨by rw [bne, beq_nat]; exact h.1, ?_⟩
  rw [beq_iff_eq]
  unfold matOf
  rw [List.map_map]
  refine List.map_congr_left fun e he => ?_
  have := CFSG.KC.Pack.allN_spec h.2 e (by simpa using List.mem_range.1 he)
  rw [Nat.eq_of_beq_eq_true this]
  rfl

theorem stab_sound {form W : Array Nat} {yg U O : List (Array Nat)} {OP : List Nat}
    {GY GU : Nat → Nat} {gUY NUY : Nat} {GUY TUY EUY SUY : Nat → Nat}
    (hO : O = OP.map (unpack 64 7)) (hOP : ∀ t ∈ OP, PP 64 7 t) (hW : Lt64 W)
    (hcnt : (OP.filter fun t => mapsK t W (maskOf W)).length = 1344)
    (bU : Bound 64 7 U GU) (hUl : U.length = 3) (hrun : (runK 64 7 3 GU 100).length = 8)
    (aU : ∀ k < 3, addK (GU k) = true) (fU : U.all (transElG form 0) = true)
    (pUY : Pin 64 7 (U ++ yg) gUY GUY NUY TUY EUY SUY) (hN : NUY = 1344)
    (hmaps : (U ++ yg).all (fun t => mapsInto t W W) = true)
    (bY : Bound 64 7 yg GY) (hyl : yg.length = 2)
    (hstab : stabYK 2 GY 3 GU (runK 64 7 3 GU 100) = true) :
    stabCheckG form yg O W U = true := by
  have hrun' : (runK 64 7 U.length GU 100).length = 8 := by rw [hUl]; exact hrun
  obtain ⟨pL, eL, cL⟩ := runK_facts (fuel := 100) (m := 8) bU hrun' (by decide) (by decide)
  rw [hUl] at pL eL
  have pY : ∀ y < yg.length, PP 64 7 (GY y) := fun y hy => PP_bound hsz64 bY hy
  have pU : ∀ u < U.length, PP 64 7 (GU u) := fun u hu => PP_bound hsz64 bU hu
  unfold stabCheckG
  simp only [Bool.and_eq_true]
  refine ⟨⟨⟨⟨⟨cL, ?_⟩, ?_⟩, hmaps⟩, ?_⟩, ?_⟩
  · exact isom_all bU (fun k hk => aU k (by omega)) (form_of_trans bU fU)
  · have := enumCheckN_of pUY.size pUY.bind pUY.perm pUY.ok pUY.fuel
    rwa [hN] at this
  · rw [hO, List.filter_map, List.length_map, beq_iff_eq, ← hcnt]
    exact congrArg List.length (List.filter_congr fun t ht => mapsIntoM_eq (hOP t ht) W hW)
  · refine all_bound bY fun y hy => all_bound bU fun u hu => ?_
    rw [eL, conjA_PP (pY y hy) (pU u hu), FusYK.inLN_memK ((pY y hy).conjK (pU u hu)) pL]
    unfold stabYK at hstab
    exact CFSG.KC.Pack.allN_spec (CFSG.KC.Pack.allN_spec hstab y (by omega)) u (by omega)

theorem ref_sound {d : QD} {OP : List Nat}
    {GY GN GU1 GU2 GG1 GG2 : Nat → Nat} {NY NN NUY1 NUY2 : Nat}
    {TY EY SY TN EN SN GUY1 TUY1 EUY1 SUY1 GUY2 TUY2 EUY2 SUY2 : Nat → Nat}
    (hDR : directRefG d = true)
    (hO : oAllG d.trans = OP.map (unpack 64 7)) (hOP : ∀ t ∈ OP, PP 64 7 t)
    (hok : ∀ t ∈ OP, ((List.range 30).any (fun j => mapsK t d.w1 (maskOf (d.l30.getD j #[]))) &&
      (List.range 30).any fun j => mapsK t d.w2 (maskOf (d.l30.getD j #[]))) = true)
    (c1 : (OP.filter fun t => mapsK t d.w1 (maskOf d.w1)).length = 1344)
    (c2 : (OP.filter fun t => mapsK t d.w2 (maskOf d.w2)).length = 1344)
    (c3 : (OP.filter (swapK d.w1 d.w2)).length = 336)
    (bU1 : Bound 64 7 d.u1 GU1) (bU2 : Bound 64 7 d.u2 GU2)
    (bG1 : Bound 64 7 d.g1 GG1) (bG2 : Bound 64 7 d.g2 GG2)
    (pY : Pin 64 7 d.yg 2 GY NY TY EY SY) (pN : Pin 64 7 d.ng 2 GN NN TN EN SN)
    (pUY1 : Pin 64 7 (d.u1 ++ d.yg) 5 GUY1 NUY1 TUY1 EUY1 SUY1)
    (pUY2 : Pin 64 7 (d.u2 ++ d.yg) 5 GUY2 NUY2 TUY2 EUY2 SUY2)
    (hsz : NY = 168 ∧ NN = 336 ∧ NUY1 = 1344 ∧ NUY2 = 1344)
    (hrun : (Nat.beq (runK 64 7 2 GY 200).length 168 && Nat.beq (runK 64 7 3 GU1 100).length 8 &&
      Nat.beq (runK 64 7 3 GU2 100).length 8) = true)
    (hRef : refPK (runK 64 7 2 GY 200) GY GU1 GU2 (runK 64 7 3 GU1 100) (runK 64 7 3 GU2 100) GN
      NN TN d.w1 d.w2 d.orb d.orbRep d.l30 = true)
    (hWit : witsK GY GG1 GG2 (runK 64 7 3 GU1 100) (runK 64 7 3 GU2 100) d.wit = true)
    (aY : ∀ k < 2, addK (GY k) = true) (aN : ∀ k < 2, addK (GN k) = true)
    (aU1 : ∀ k < 3, addK (GU1 k) = true) (aU2 : ∀ k < 3, addK (GU2 k) = true)
    (aG1 : ∀ k < 4, addK (GG1 k) = true) (aG2 : ∀ k < 4, addK (GG2 k) = true) :
    refCheckG d = true := by
  obtain ⟨hNY, hNN, hN1, hN2⟩ := hsz
  unfold directRefG at hDR
  simp only [Bool.and_eq_true, beq_iff_eq, and_assoc] at hDR
  obtain ⟨d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19,
    d20, d21, d22, d23, d24, d25, d26, d27⟩ := hDR
  simp only [Bool.and_eq_true] at hrun
  obtain ⟨⟨r1, r2⟩, r3⟩ := hrun
  unfold refPK at hRef
  simp only [andB_eq, Bool.and_eq_true] at hRef
  obtain ⟨f1, f2, f3, f4, f5, f6, f7⟩ := hRef
  have bY := bnd_pin pY
  have bN := bnd_pin pN
  have hyl := len_pin pY
  have hnl := len_pin pN
  have gY : ∀ k < 2, PP 64 7 (GY k) := fun k hk => PP_bound hsz64 bY (by omega)
  have gN : ∀ k < 2, PP 64 7 (GN k) := fun k hk => PP_bound hsz64 bN (by omega)
  have lY : (runK 64 7 2 GY 200).length = 168 := Nat.eq_of_beq_eq_true r1
  have l1 : (runK 64 7 3 GU1 100).length = 8 := Nat.eq_of_beq_eq_true r2
  have l2 : (runK 64 7 3 GU2 100).length = 8 := Nat.eq_of_beq_eq_true r3
  have lY' : (runK 64 7 d.yg.length GY 200).length = 168 := by rw [hyl]; exact lY
  have l1' : (runK 64 7 d.u1.length GU1 100).length = 8 := by rw [d3]; exact l1
  have l2' : (runK 64 7 d.u2.length GU2 100).length = 8 := by rw [d4]; exact l2
  obtain ⟨pLY, eLY, -⟩ := runK_facts (fuel := 200) (m := 168) bY lY' (by decide) (by decide)
  rw [hyl] at pLY eLY
  obtain ⟨pL1, eL1, -⟩ := runK_facts (fuel := 100) (m := 8) bU1 l1' (by decide) (by decide)
  rw [d3] at pL1 eL1
  obtain ⟨pL2, eL2, -⟩ := runK_facts (fuel := 100) (m := 8) bU2 l2' (by decide) (by decide)
  rw [d4] at pL2 eL2
  have w1 : Lt64 d.w1 := eight_lt (ts_eight d6)
  have w2 : Lt64 d.w2 := eight_lt (ts_eight d7)
  have hdW : (default : List (List Nat)) = [] := rfl
  unfold refCheckG
  simp only [Bool.and_eq_true, and_assoc]
  refine ⟨?_, ?_, d6, d7, d8, d9, ?_, ?_, beq_iff_eq.2 d10, d11, ?_, beq_iff_eq.2 d12, d13,
    beq_iff_eq.2 d14, ?_, beq_iff_eq.2 d16, beq_iff_eq.2 d17, ?_, ?_, d20, ?_, ?_,
    beq_iff_eq.2 d25, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have := enumCheckN_of pY.size pY.bind pY.perm pY.ok pY.fuel
    rwa [hNY] at this
  · exact isom_all bY (fun k hk => aY k (by omega)) (form_of_trans bY d5)
  · rw [eLY, transCheck_eq (ts_eight d6)]
    exact f1
  · rw [eLY, transCheck_eq (ts_eight d7)]
    exact f2
  ·
    rw [hO, List.all_map, List.all_eq_true]
    intro t ht
    have pt := hOP t ht
    have h := hok t ht
    simp only [Function.comp_apply]
    rw [Bool.and_eq_true] at h ⊢
    refine ⟨?_, ?_⟩
    · rw [← h.1]
      refine HexaK.any_congr_mem fun j hj => ?_
      rw [l30Tab_get (by rw [d10]; exact List.mem_range.1 hj), mapsIntoM_eq pt _ w1]
    · rw [← h.2]
      refine HexaK.any_congr_mem fun j hj => ?_
      rw [l30Tab_get (by rw [d10]; exact List.mem_range.1 hj), mapsIntoM_eq pt _ w2]
  ·
    rw [List.all_eq_true]
    intro j hj
    have o1 := List.all_eq_true.1 d15 j hj
    unfold orbK at f3
    have o2 := List.all_eq_true.1 f3 j hj
    have hp : d.orb[j]! = d.orb.getD j (0, 0) := by rw [FusYK.getElem!_getD]; rfl
    rw [← hp] at o2
    simp only [orB_eq, andB_eq, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq,
      beq_iff_eq] at o1 o2 ⊢
    by_cases h4 : d.orb[j]!.1 < 4
    · refine Or.inr ⟨⟨h4, ?_⟩, ?_⟩
      · have := o2.resolve_left (by
          intro e
          have := Nat.le_of_ble_eq_true e
          omega)
        have hlt := Nat.blt_eq.mp this.1
        rwa [lY] at hlt
      · have o3 := (o2.resolve_left (by
          intro e
          have := Nat.le_of_ble_eq_true e
          omega))
        have hlt := Nat.blt_eq.mp o3.1
        have hr : Lt64 (d.orbRep.getD d.orb[j]!.1 #[]) := by
          rw [List.all_eq_true] at d13
          rw [List.getD_eq_getElem _ _ (by omega)]
          exact eight_lt (d13 _ (List.getElem_mem _))
        rw [eLY, FusYK.getElem!_map' (by simpa using hlt), FusYK.getElem!_getD d.orbRep,
          FusYK.getElem!_getD d.l30]
        have hd : (default : Array Nat) = #[] := rfl
        rw [hd, mapsInto_eq _ hr]
        exact o3.2
    · rcases o1 with (o1 | o1) | o1
      · exact absurd o1 h4
      · exact Or.inl (Or.inl o1)
      · exact Or.inl (Or.inr o1)
  · exact isom_all bG1 (fun k hk => aG1 k (by omega)) (form_of_trans bG1 d18)
  · exact isom_all bG2 (fun k hk => aG2 k (by omega)) (form_of_trans bG2 d19)
  · exact stab_sound hO hOP w1 c1 bU1 d3 (Nat.eq_of_beq_eq_true r2) aU1 d21 pUY1 hN1 d23 bY hyl f4
  · exact stab_sound hO hOP w2 c2 bU2 d4 (Nat.eq_of_beq_eq_true r3) aU2 d22 pUY2 hN2 d24 bY hyl f5
  ·
    unfold witsCheckG
    simp only [List.all_eq_true, List.mem_range]
    intro s hs k hk j hj
    have hw := CFSG.KC.Pack.allN_spec (CFSG.KC.Pack.allN_spec (CFSG.KC.Pack.allN_spec hWit s hs) k hk) j hj
    have hi : (s * 4 + k) * 8 + j < d.wit.length := by rw [d25]; omega
    have hl : (d.wit.getD ((s * 4 + k) * 8 + j) []).all
        (·.all fun l => decide (1 ≤ l) && decide (l ≤ 3)) = true := by
      rw [List.all_eq_true] at d26
      rw [List.getD_eq_getElem _ _ hi]
      exact d26 _ (List.getElem_mem hi)
    rw [FusYK.getElem!_getD d.wit, hdW]
    rcases (by omega : s = 0 ∨ s = 1) with rfl | rfl
    · have e : ((0 : Nat) == 0) = true := rfl
      simp only [e, ↓reduceIte]
      have pg' : PP 64 7 (GG1 k) := PP_bound hsz64 bG1 (by omega)
      have pu : PP 64 7 ((runK 64 7 3 GU1 100).getD j 0) :=
        pL1 _ (Q47K.getD_mem (by rw [l1]; exact hj))
      rw [(bG1 k (by omega)).1, eL1, FusYK.getElem!_map' (by rw [l1]; exact hj)]
      exact witCheck_of bY hyl pg' pu hl hw
    · have e : ((1 : Nat) == 0) = false := rfl
      simp only [e, Bool.false_eq_true, ↓reduceIte]
      have pg' : PP 64 7 (GG2 k) := PP_bound hsz64 bG2 (by omega)
      have pu : PP 64 7 ((runK 64 7 3 GU2 100).getD j 0) :=
        pL2 _ (Q47K.getD_mem (by rw [l2]; exact hj))
      rw [(bG2 k (by omega)).1, eL2, FusYK.getElem!_map' (by rw [l2]; exact hj)]
      exact witCheck_of bY hyl pg' pu hl hw
  · have := enumCheckN_of pN.size pN.bind pN.perm pN.ok pN.fuel
    rwa [hNN] at this
  · exact isom_all bN (fun k hk => aN k (by omega)) (form_of_trans bN d27)
  · refine all_bound bY fun y hy => ?_
    rw [eltsN_eq pN.size pN.bind pN.ok pN.fuel, inLN_eq (gY y (by omega)) (PP_pts pN.ok pN.perm)]
    exact CFSG.KC.Pack.allN_spec f6 y (by omega)
  · refine all_bound bN fun k hk => ?_
    rw [swapCheck_eq (gN k (by omega)) w1 w2]
    exact CFSG.KC.Pack.allN_spec f7 k (by omega)
  · rw [hO, List.filter_map, List.length_map, beq_iff_eq, ← c3]
    exact congrArg List.length (List.filter_congr fun t ht => swapCheck_eq (hOP t ht) w1 w2)

theorem trans_sound {d : QD} {SZ : Nat → Nat} {TR : Nat → Nat → Nat}
    (hDT : directTransG d = true)
    (bT : ∀ k < 6, (d.trans[k]!).length = SZ k ∧ Bound 64 7 d.trans[k]! (TR k))
    (aT : ∀ k < 6, ∀ j < SZ k, addK (TR k j) = true) : transCheckOG d.form d.trans = true := by
  unfold directTransG at hDT
  unfold transCheckOG
  simp only [Bool.and_eq_true] at hDT ⊢
  obtain ⟨⟨h1, h2⟩, -⟩ := hDT
  refine ⟨h1, List.all_eq_true.2 fun k hk => ?_⟩
  have hk' := List.mem_range.1 hk
  have h := List.all_eq_true.1 h2 k hk
  rw [Bool.and_eq_true] at h ⊢
  refine ⟨all_bound (bT k hk').2 fun j hj => ?_, h.2⟩
  have e := all_bound_inv (bT k hk').2 h.1 j hj
  unfold transElG at e
  rw [Bool.and_eq_true] at e ⊢
  exact ⟨isom_of ((bT k hk').2 j hj).2 (aT k hk' j (by rw [← (bT k hk').1]; exact hj)) e.1, e.2⟩

theorem q47K_sound {d : QD} {m16 m32 : MD} {k16 k32 : ModelK}
    {TR : Nat → Nat → Nat} {SZ : Nat → Nat} {GY GN GU1 GU2 GG1 GG2 : Nat → Nat}
    {NY NN NUY1 NUY2 : Nat} {TY EY SY TN EN SN GUY1 TUY1 EUY1 SUY1 GUY2 TUY2 EUY2 SUY2 : Nat → Nat}
    {MPY MPN BC : Nat → Nat}
    (hD : q47DirectG d m16 m32 = true)
    (bT : ∀ k < 6, (d.trans[k]!).length = SZ k ∧ Bound 64 7 d.trans[k]! (TR k)) (hSZ : SZ 0 = 35)
    (hSZb : Nat.blt (SZ 1 * SZ 2 * SZ 3 * SZ 4 * SZ 5) 65536 = true)
    (bU1 : Bound 64 7 d.u1 GU1) (bU2 : Bound 64 7 d.u2 GU2)
    (bG1 : Bound 64 7 d.g1 GG1) (bG2 : Bound 64 7 d.g2 GG2)
    (pY : Pin 64 7 d.yg 2 GY NY TY EY SY) (pN : Pin 64 7 d.ng 2 GN NN TN EN SN)
    (pUY1 : Pin 64 7 (d.u1 ++ d.yg) 5 GUY1 NUY1 TUY1 EUY1 SUY1)
    (pUY2 : Pin 64 7 (d.u2 ++ d.yg) 5 GUY2 NUY2 TUY2 EUY2 SUY2)
    (hsz : NY = 168 ∧ NN = 336 ∧ NUY1 = 1344 ∧ NUY2 = 1344)
    (hrun : (Nat.beq (runK 64 7 2 GY 200).length 168 && Nat.beq (runK 64 7 3 GU1 100).length 8 &&
      Nat.beq (runK 64 7 3 GU2 100).length 8) = true)
    (hMP : ((allN 168 fun i => matOf 3 (MPY i) == d.ymat[i]!) &&
      allN 336 fun i => matOf 2 (MPN i) == d.nmat[i]!) = true)
    (hRef : refPK (runK 64 7 2 GY 200) GY GU1 GU2 (runK 64 7 3 GU1 100) (runK 64 7 3 GU2 100) GN
      NN TN d.w1 d.w2 d.orb d.orbRep d.l30 = true)
    (hWit : witsK GY GG1 GG2 (runK 64 7 3 GU1 100) (runK 64 7 3 GU2 100) d.wit = true)
    (hTab : (tableHeadK NY TY MPY 3 (· == [1, 0, 0, 0, 1, 0, 0, 0, 1]) &&
      tableHeadK NN TN MPN 2 (fun m => m[1]! == 0 && m[2]! == 0 && m[0]! == m[3]!)) = true)
    (hRowY : ∀ i < 168, tableRowK NY TY SY MPY 3 2 Nat.beq i = true)
    (hRowN : ∀ i < 336, tableRowK NN TN SN MPN 2 7 projK i = true)
    (hAdd : ((List.range 6).all (fun k => allN (SZ k) fun j => addK (TR k j)) &&
      allN 2 (fun k => addK (GY k) && addK (GN k)) && allN 3 (fun k => addK (GU1 k) && addK (GU2 k)) &&
      allN 4 (fun k => addK (GG1 k) && addK (GG2 k) && addK (k16.CP k) && addK (k32.CP k))) = true)
    (hO : ∀ s < 35, Nat.beq (oBlock SZ TR d.w1 d.w2 d.l30
      [clsOf m16 k16 false, clsOf m16 k16 true, clsOf m32 k32 false, clsOf m32 k32 true] s) (BC s) =
      true)
    (hBC : bcK BC = true)
    (h16 : ModelOK d 16 5 m16 k16 GY) (h32 : ModelOK d 32 6 m32 k32 GY) :
    q47CheckG d m16 m32 = true := by
  unfold q47DirectG at hD
  simp only [Bool.and_eq_true] at hD
  obtain ⟨⟨⟨⟨hDT, hDR⟩, hDM⟩, hD16⟩, hD32⟩ := hD
  have hl : d.trans.length = 6 := by
    have h := hDT
    unfold directTransG at h
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    exact h.1.1
  obtain ⟨OP, eO, pO, kO, c1, c2, c3⟩ := o_sound hl bT hSZ hSZb hO hBC
  simp only [Bool.and_eq_true] at hAdd
  obtain ⟨⟨⟨a6, a2⟩, a3⟩, a4⟩ := hAdd
  have aT : ∀ k < 6, ∀ j < SZ k, addK (TR k j) = true := fun k hk j hj =>
    CFSG.KC.Pack.allN_spec (List.all_eq_true.1 a6 k (List.mem_range.2 hk)) j hj
  have a2' : ∀ k < 2, addK (GY k) = true ∧ addK (GN k) = true := fun k hk =>
    Bool.and_eq_true_iff.1 (CFSG.KC.Pack.allN_spec a2 k hk)
  have a3' : ∀ k < 3, addK (GU1 k) = true ∧ addK (GU2 k) = true := fun k hk =>
    Bool.and_eq_true_iff.1 (CFSG.KC.Pack.allN_spec a3 k hk)
  have a4' : ∀ k < 4, addK (GG1 k) = true ∧ addK (GG2 k) = true ∧ addK (k16.CP k) = true ∧
      addK (k32.CP k) = true := fun k hk => by
    have := CFSG.KC.Pack.allN_spec a4 k hk
    simp only [Bool.and_eq_true] at this
    exact ⟨this.1.1.1, this.1.1.2, this.1.2, this.2⟩
  have hok : ∀ t ∈ OP, okT d.w1 d.w2 d.l30
      [clsOf m16 k16 false, clsOf m16 k16 true, clsOf m32 k32 false, clsOf m32 k32 true] t = true :=
    kO
  have hcls : ∀ t ∈ OP, ord3 t = true →
      (clsC (clsOf m16 k16 false) t = true ∧ clsC (clsOf m16 k16 true) t = true) ∧
        (clsC (clsOf m32 k32 false) t = true ∧ clsC (clsOf m32 k32 true) t = true) := by
    intro t ht h3
    have h := hok t ht
    unfold okT at h
    rw [andB_eq, orB_eq, notB_eq, h3, Bool.and_eq_true] at h
    have h' := h.2
    simp only [Bool.not_true, Bool.false_or, List.all_cons, List.all_nil, Bool.and_true,
      Bool.and_eq_true] at h'
    exact ⟨⟨h'.1, h'.2.1⟩, h'.2.2.1, h'.2.2.2⟩
  have bY := bnd_pin pY
  have hyl := len_pin pY
  unfold q47CheckG
  simp only [Bool.and_eq_true]
  refine ⟨⟨⟨⟨⟨trans_sound hDT bT aT, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · unfold directTransG at hDT
    simp only [Bool.and_eq_true] at hDT
    exact hDT.2
  · refine ref_sound hDR eO pO (fun t ht => ?_) c1 c2 c3 bU1 bU2 bG1 bG2 pY pN pUY1 pUY2 hsz hrun
      hRef hWit (fun k hk => (a2' k hk).1) (fun k hk => (a2' k hk).2) (fun k hk => (a3' k hk).1)
      (fun k hk => (a3' k hk).2) (fun k hk => (a4' k hk).1) (fun k hk => (a4' k hk).2.1)
    have h := hok t ht
    unfold okT at h
    rw [andB_eq, andB_eq, Bool.and_eq_true] at h
    exact h.1
  · obtain ⟨hNY, hNN, -, -⟩ := hsz
    subst hNY hNN
    unfold directMatG at hDM
    simp only [Bool.and_eq_true, beq_iff_eq] at hDM
    obtain ⟨⟨⟨⟨⟨⟨m1, m2⟩, m3⟩, m4⟩, m5⟩, m6⟩, m7⟩ := hDM
    simp only [Bool.and_eq_true] at hMP hTab
    unfold tableCheckG
    simp only [Bool.and_eq_true]
    refine ⟨⟨?_, ?_⟩, m7⟩
    · refine tab_sound pY (by decide) (by decide) (by decide) m1 m2 (beq_iff_eq.2 m3) hMP.1
        (fun a b h => ?_) hTab.1 hRowY
      rw [Nat.eq_of_beq_eq_true h]
      exact beq_self_eq_true _
    · exact tab_sound pN (by decide) (by decide) (by decide) m4 m5 (beq_iff_eq.2 m6) hMP.2
        (fun a b h => projK_sound h) hTab.2 hRowN
  · exact model_sound h16 hD16 bY hyl (fun c hc => (a4' c hc).2.2.1) eO pO
      fun t ht h3 => (hcls t ht h3).1
  · exact model_sound h32 hD32 bY hyl (fun c hc => (a4' c hc).2.2.2) eO pO
      fun t ht h3 => (hcls t ht h3).2

end CFSG.KC.Q47K

end
