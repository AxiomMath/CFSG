module

public import CFSG.Certificates.Kernel.Misc.HypNative

public section

set_option exponentiation.threshold 10000

namespace CFSG.KC.Misc.Hyp

open CFSG.F4.Native CFSG.Sporadic.Th.Native CFSG.Fischer.Native CFSG.KC.Misc.T46
  CFSG.KC.Misc.Lines CFSG.KC.Misc.Xi CFSG.KS.PK CFSG.KC.Ord CFSG.KC.LQT.P CFSG.KC.Misc
  CFSG.KC.Misc.O73 CFSG.KS.TW

private theorem listsP_length {S M : Nat} (h : listsP S M = true) :
    (members (fl S)).length = 126 := by
  have hspec : ∀ p, S.testBit p = true ↔ ∃ i < 126, fd 10 M i = p := (listsP_spec h).2
  unfold listsP at h
  simp only [andB_eq, Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at h
  obtain ⟨-, -, -, hlast, hinc0⟩ := h
  rw [allN_lqt_iff] at hinc0
  have hinc : ∀ i < 125, fd 10 M i < fd 10 M (i + 1) := by
    intro i hi
    have := Nat.blt_eq.mp (hinc0 i hi)
    simpa only [at'_eq] using this
  have hlast' : fd 10 M 125 < 693 := by
    simpa only [at'_eq] using hlast
  have hmono_lt : ∀ i j, i < j → j < 126 → fd 10 M i < fd 10 M j := by
    intro i j
    induction j with
    | zero => intro hlt hj; omega
    | succ j ih =>
      intro hlt hj
      rcases Nat.lt_succ_iff_lt_or_eq.1 hlt with h | h
      · exact lt_trans (ih h (by omega)) (hinc j (by omega))
      · rw [h]; exact hinc j (by omega)
  have hmono_le : ∀ i j, i ≤ j → j < 126 → fd 10 M i ≤ fd 10 M j := by
    intro i j hij hj
    rcases eq_or_lt_of_le hij with rfl | h
    · rfl
    · exact le_of_lt (hmono_lt i j h hj)
  have hlt : ∀ i < 126, fd 10 M i < 693 := fun i hi =>
    lt_of_le_of_lt (hmono_le i 125 (by omega) (by norm_num)) hlast'
  have hmem : ∀ a, a ∈ members (fl S) ↔ a ∈ (List.range 126).map (fd 10 M) := by
    intro a
    rw [mem_members_fl]
    constructor
    · rintro ⟨-, hbit⟩
      obtain ⟨i, hi, rfl⟩ := (hspec a).1 hbit
      exact List.mem_map.2 ⟨i, List.mem_range.2 hi, rfl⟩
    · intro ha
      obtain ⟨i, hi, rfl⟩ := List.mem_map.1 ha
      exact ⟨hlt i (List.mem_range.1 hi), (hspec _).2 ⟨i, List.mem_range.1 hi, rfl⟩⟩
  have hnodup_mem : (members (fl S)).Nodup := by
    rw [members_eq]
    exact List.Nodup.filter _ List.nodup_range
  have hnodup_map : ((List.range 126).map (fd 10 M)).Nodup := by
    refine List.Nodup.map_on (fun x hx y hy hxy => ?_) List.nodup_range
    have hx' : x < 126 := List.mem_range.1 hx
    have hy' : y < 126 := List.mem_range.1 hy
    rcases lt_trichotomy x y with hlt' | heq | hgt
    · have := hmono_lt x y hlt' hy'
      omega
    · exact heq
    · have := hmono_lt y x hgt hx'
      omega
  have hperm := (List.perm_ext_iff_of_nodup hnodup_mem hnodup_map).2 hmem
  have hlen := hperm.length_eq
  simpa using hlen

set_option maxRecDepth 100000 in
private theorem hypOrbitOK_of {UL : List Nat} {UP PP XP YP J : Nat} {xw yw : List Int}
    {HS ML : Nat → Nat} (H : Pts UL UP PP)
    (hTX : TR 693 (powG UL.toArray 3 xw) (fd 10 XP))
    (hTY : TR 693 (powG UL.toArray 2 yw) (fd 10 YP)) (hG : GenFacts XP YP)
    (hmemK : ∀ k < 4224, listsP (HS k) (ML k) = true)
    (hdistS : ∀ j < 4224, ∀ j' < 4224, HS j = HS j' → j = j')
    {o c : Nat} (ho : o < 3) (horbK : orbK UP XP YP HS ML J o c = true)
    (hHu : hypUnionG UL.toArray xw yw = Array.ofFn (n := 4224) fun j => fl (HS j)) :
    hypOrbitOK (rootFlagsG UL.toArray c)
      #[powG UL.toArray 3 xw, powG UL.toArray 2 yw]
      #[powG UL.toArray 3 xw, compT 693 (powG UL.toArray 2 yw) (powG UL.toArray 2 yw)]
      (hypEnumG UL.toArray xw yw c) (famIndex (hypUnionG UL.toArray xw yw)) (1408 * o) = true := by
  obtain ⟨hroot, nn, hn0, hnend, hstep, hset⟩ := orbK_spec o ho hmemK horbK
  have hcY : TR 693 (compT 693 (powG UL.toArray 2 yw) (powG UL.toArray 2 yw))
      (fun p => fd 10 (compP 693 10 YP YP) p) := by
    have h := compT_TR (n := 693) (by norm_num) hTY hTY
    refine ⟨h.1, fun i hi => ?_⟩
    show ap (compT 693 (powG UL.toArray 2 yw) (powG UL.toArray 2 yw)) i =
      fd 10 (compP 693 10 YP YP) i ∧ fd 10 (compP 693 10 YP YP) i < 693
    rw [fd_compP _ _ hi]
    exact h.2 i hi
  have hyp : OrbHyp (rootFlagsG UL.toArray c) #[powG UL.toArray 3 xw, powG UL.toArray 2 yw]
      #[powG UL.toArray 3 xw, compT 693 (powG UL.toArray 2 yw) (powG UL.toArray 2 yw)]
      (fun l p => fd 10 (if l = 1 then YP else XP) p)
      (fun l p => fd 10 (if l = 1 then compP 693 10 YP YP else XP) p)
      (fun j => HS (1408 * o + j)) (fun t => fd 11 J t) nn := by
    refine ⟨rfl, rfl, ?_, ?_, ?_, by simp [rootFlagsG], ?_, ?_, ?_, hn0, hnend, hstep, ?_⟩
    · intro l hl
      interval_cases l
      · exact hTX
      · exact hTY
    · intro l hl
      interval_cases l
      · exact hTX
      · exact hcY
    · intro l hl x hx
      interval_cases l
      · exact ⟨hG.xx x hx, hG.xx x hx⟩
      · show fd 10 (compP 693 10 YP YP) (fd 10 YP x) = x ∧
          fd 10 YP (fd 10 (compP 693 10 YP YP) x) = x
        rw [fd_compP _ _ (hG.ylt x hx), fd_compP _ _ hx]
        exact ⟨hG.yyy x hx, hG.yyy x hx⟩
    · intro p hp
      rw [rootFlagsG_eq H c, fl_get _ hp]
      show (rootK UP c).testBit p = (HS (1408 * o + 0)).testBit p
      rw [Nat.add_zero, hroot]
    · intro j hj
      exact (listsP_spec (hmemK _ (by omega))).1
    · intro j hj j' hj' hjj
      have := hdistS _ (by omega) _ (by omega) hjj
      omega
    · intro t ht
      exact (hset t ht)
  obtain ⟨par, lab, heq, hpsz, hlsz, hp0, hl0, htree⟩ := orbitEnum_spec hyp
  have hO : hypEnumG UL.toArray xw yw c =
      (Array.ofFn (n := 1408) fun j => fl (HS (1408 * o + j)), par, lab) := by
    unfold hypEnumG
    rw [heq]
  rw [hO]
  unfold hypOrbitOK
  simp only []
  have hget : ∀ k < 1408, (Array.ofFn (n := 1408) fun j => fl (HS (1408 * o + j)))[k]! =
      fl (HS (1408 * o + k)) := by
    intro k hk
    rw [getElem!_pos _ k (by simpa using hk), Array.getElem_ofFn]
  have hHu_get : ∀ j < 4224, (hypUnionG UL.toArray xw yw)[j]! = fl (HS j) := by
    intro j hj
    rw [hHu, getElem!_pos _ j (by simpa using hj), Array.getElem_ofFn]
  have hHu_sz : (hypUnionG UL.toArray xw yw).size = 4224 := by
    rw [hHu]; exact Array.size_ofFn
  have hHSlt : ∀ j < 4224, HS j < 2 ^ 693 := fun j hj => (listsP_spec (hmemK j hj)).1
  have hgs2 : (#[powG UL.toArray 3 xw, powG UL.toArray 2 yw] : Array Table).size = 2 := rfl
  have hgi2 : (#[powG UL.toArray 3 xw,
      compT 693 (powG UL.toArray 2 yw) (powG UL.toArray 2 yw)] : Array Table).size = 2 := rfl
  have hinv0 : invOK 693 (#[powG UL.toArray 3 xw, powG UL.toArray 2 yw] : Array Table)[0]!
      (#[powG UL.toArray 3 xw, compT 693 (powG UL.toArray 2 yw) (powG UL.toArray 2 yw)] :
        Array Table)[0]! = true := by
    rw [show (#[powG UL.toArray 3 xw, powG UL.toArray 2 yw] : Array Table)[0]! =
        powG UL.toArray 3 xw by rfl,
      show (#[powG UL.toArray 3 xw, compT 693 (powG UL.toArray 2 yw) (powG UL.toArray 2 yw)] :
        Array Table)[0]! = powG UL.toArray 3 xw by rfl]
    rw [invOK, allIn_iff']
    intro i _ hi
    rw [beq_iff_eq]
    have h1 : ap (powG UL.toArray 3 xw) i = fd 10 XP i := (hTX.2 i hi).1
    have h2 : fd 10 XP i < 693 := (hTX.2 i hi).2
    have h3 : ap (powG UL.toArray 3 xw) (fd 10 XP i) = fd 10 XP (fd 10 XP i) := (hTX.2 _ h2).1
    rw [h1, h3, hG.xx i hi]
  have hinv1 : invOK 693 (#[powG UL.toArray 3 xw, powG UL.toArray 2 yw] : Array Table)[1]!
      (#[powG UL.toArray 3 xw, compT 693 (powG UL.toArray 2 yw) (powG UL.toArray 2 yw)] :
        Array Table)[1]! = true := by
    rw [show (#[powG UL.toArray 3 xw, powG UL.toArray 2 yw] : Array Table)[1]! =
        powG UL.toArray 2 yw by rfl,
      show (#[powG UL.toArray 3 xw, compT 693 (powG UL.toArray 2 yw) (powG UL.toArray 2 yw)] :
        Array Table)[1]! = compT 693 (powG UL.toArray 2 yw) (powG UL.toArray 2 yw) by rfl]
    rw [invOK, allIn_iff']
    intro i _ hi
    rw [beq_iff_eq]
    have h1 : ap (powG UL.toArray 2 yw) i = fd 10 YP i := (hTY.2 i hi).1
    have h2 : fd 10 YP i < 693 := (hTY.2 i hi).2
    have h3 : ap (compT 693 (powG UL.toArray 2 yw) (powG UL.toArray 2 yw)) (fd 10 YP i) =
        fd 10 (compP 693 10 YP YP) (fd 10 YP i) := (hcY.2 _ h2).1
    rw [h1, h3, fd_compP _ _ h2, hG.yyy i hi]
  have hsz1408 : (Array.ofFn (n := 1408) fun j => fl (HS (1408 * o + j))).size = 1408 :=
    Array.size_ofFn
  have hH0 : ((Array.ofFn (n := 1408) fun j => fl (HS (1408 * o + j)))[0]! ==
      rootFlagsG UL.toArray c) = true := by
    rw [hget 0 (by norm_num), beq_iff_eq, rootFlagsG_eq H c, Nat.add_zero, hroot]
  have hall126 : (allIn 0 1408 fun k =>
      (members (Array.ofFn (n := 1408) fun j => fl (HS (1408 * o + j)))[k]!).length == 126) =
      true := by
    rw [allIn_iff']
    intro k _ hk
    rw [hget k hk, beq_iff_eq]
    exact listsP_length (hmemK (1408 * o + k) (by omega))
  have halltree : (allIn 1 1408 fun k => decide (par[k]! < k) && decide (lab[k]! < 2) &&
      (Array.ofFn (n := 1408) fun j => fl (HS (1408 * o + j)))[k]! ==
        imgFlags (#[powG UL.toArray 3 xw, compT 693 (powG UL.toArray 2 yw) (powG UL.toArray 2 yw)] :
          Array Table)[lab[k]!]!
          (Array.ofFn (n := 1408) fun j => fl (HS (1408 * o + j)))[par[k]!]!) = true := by
    rw [allIn_iff']
    intro k hk1 hk2
    obtain ⟨hpk, hlk, hJo, -⟩ := htree k hk1 hk2
    rw [hget k hk2, hget (par[k]!) (by omega)]
    have htr := hyp.Ti (lab[k]!) hlk
    have hinv := hyp.inv (lab[k]!) hlk
    have hst := (hset (2 * par[k]! + lab[k]!) (by omega)).2
    rw [hJo] at hst
    rw [show (2 * par[k]! + lab[k]!) / 2 = par[k]! by omega,
      show (2 * par[k]! + lab[k]!) % 2 = lab[k]! by omega] at hst
    have himg := imgFlags_fl htr hinv hst
    rw [← himg]
    simp [hpk, hlk]
  have hallclos : (allIn 0 1408 fun k =>
      allIn 0 2 fun l =>
        let i := findIn (famIndex (hypUnionG UL.toArray xw yw)) 4224
          (packImg (#[powG UL.toArray 3 xw, powG UL.toArray 2 yw] : Array Table)[l]!
            (members (Array.ofFn (n := 1408) fun j => fl (HS (1408 * o + j)))[k]!))
        decide (1408 * o ≤ i) && decide (i < 1408 * o + 1408) &&
          (Array.ofFn (n := 1408) fun j => fl (HS (1408 * o + j)))[i - 1408 * o]! ==
            imgFlags (#[powG UL.toArray 3 xw,
              compT 693 (powG UL.toArray 2 yw) (powG UL.toArray 2 yw)] : Array Table)[l]!
              (Array.ofFn (n := 1408) fun j => fl (HS (1408 * o + j)))[k]!) = true := by
    rw [allIn_iff']
    intro k _ hk
    rw [allIn_iff']
    intro l _ hl
    have ht : 2 * k + l < 2816 := by omega
    have hJt : fd 11 J (2 * k + l) < 1408 := (hset (2 * k + l) ht).1
    have hst := (hset (2 * k + l) ht).2
    rw [show (2 * k + l) / 2 = k by omega, show (2 * k + l) % 2 = l by omega] at hst
    have hkey := (key_iff (hyp.Ts l hl) (hyp.HS_lt k hk) (hyp.HS_lt _ hJt)
      (hyp.HS_lt _ hJt) hst).2 rfl
    rw [hget k hk]
    have hi : findIn (famIndex (hypUnionG UL.toArray xw yw)) 4224
        (packImg (#[powG UL.toArray 3 xw, powG UL.toArray 2 yw] : Array Table)[l]!
          (members (fl (HS (1408 * o + k))))) = 1408 * o + fd 11 J (2 * k + l) := by
      rw [hkey]
      unfold findIn
      exact famIndex_getD_key hHu_sz hHu_get hHSlt hdistS (by omega)
    rw [hi]
    dsimp only []
    have hsub : 1408 * o + fd 11 J (2 * k + l) - 1408 * o = fd 11 J (2 * k + l) := by omega
    rw [hsub, hget (fd 11 J (2 * k + l)) hJt]
    have himg := imgFlags_fl (hyp.Ti l hl) (hyp.inv l hl) hst
    rw [himg]
    have h1 : 1408 * o ≤ 1408 * o + fd 11 J (2 * k + l) := Nat.le_add_right _ _
    have h2 : 1408 * o + fd 11 J (2 * k + l) < 1408 * o + 1408 := Nat.add_lt_add_left hJt _
    simp [h1, h2]
  rw [hgs2, hgi2, hinv0, hinv1, hsz1408, hpsz, hlsz, hH0, hall126, halltree, hallclos]
  rfl

theorem orbit_sound {UL : List Nat} {UP PP XP YP J0 J1 J2 : Nat} {xw yw : List Int}
    {GP : List Nat} {HS ML : Nat → Nat} {SP : List Nat}
    (hp : ptsK UL UP = true) (hpos : posK UL UP PP = true)
    (hg : ∀ k < 46, gensOK UL UP GP k 1 = true) (hxy : xyK GP xw yw = true)
    (hX : Nat.beq XP (powP 3 (wordG GP xw)) = true) (hY : Nat.beq YP (powP 2 (wordG GP yw)) = true)
    (hmem : ∀ k < 12, memK HS ML (352 * k) 352 = true) (hdist : distinctK HS SP = true)
    (ho0 : orbK UP XP YP HS ML J0 0 1 = true) (ho1 : orbK UP XP YP HS ML J1 1 2 = true)
    (ho2 : orbK UP XP YP HS ML J2 2 3 = true) :
    hypUnionG UL.toArray xw yw = (Array.ofFn (n := 4224) fun j => fl (HS j)) ∧
      hypOrbitOK (rootFlagsG UL.toArray 1)
        #[powG UL.toArray 3 xw, powG UL.toArray 2 yw]
        #[powG UL.toArray 3 xw, compT 693 (powG UL.toArray 2 yw) (powG UL.toArray 2 yw)]
        (hypEnumG UL.toArray xw yw 1) (famIndex (hypUnionG UL.toArray xw yw)) 0 = true ∧
      hypOrbitOK (rootFlagsG UL.toArray 2)
        #[powG UL.toArray 3 xw, powG UL.toArray 2 yw]
        #[powG UL.toArray 3 xw, compT 693 (powG UL.toArray 2 yw) (powG UL.toArray 2 yw)]
        (hypEnumG UL.toArray xw yw 2) (famIndex (hypUnionG UL.toArray xw yw)) 1408 = true ∧
      hypOrbitOK (rootFlagsG UL.toArray 3)
        #[powG UL.toArray 3 xw, powG UL.toArray 2 yw]
        #[powG UL.toArray 3 xw, compT 693 (powG UL.toArray 2 yw) (powG UL.toArray 2 yw)]
        (hypEnumG UL.toArray xw yw 3) (famIndex (hypUnionG UL.toArray xw yw)) 2816 = true ∧
      famOK (hypUnionG UL.toArray xw yw) (famIndex (hypUnionG UL.toArray xw yw)) = true := by
  have H := Pts.of hp hpos
  obtain ⟨-, -, hgen⟩ := gensOK_spec hg
  have hmemK := memK_spec hmem
  have hdistS := distinct_spec hdist
  obtain ⟨hTX, hTY, -, -, hxx, hyyy⟩ := xy_facts H hgen hxy hX hY
  have hG : GenFacts XP YP :=
    ⟨fun p hp => (hTX.2 p hp).2, fun p hp => (hTY.2 p hp).2, hxx, hyyy⟩
  have hsets0 := hypEnum_sets (xw := xw) (yw := yw) H hTX hTY hG hmemK hdistS (by norm_num) ho0
  have hsets1 := hypEnum_sets (xw := xw) (yw := yw) H hTX hTY hG hmemK hdistS (by norm_num) ho1
  have hsets2 := hypEnum_sets (xw := xw) (yw := yw) H hTX hTY hG hmemK hdistS (by norm_num) ho2
  have hUnion : hypUnionG UL.toArray xw yw = (Array.ofFn (n := 4224) fun j => fl (HS j)) := by
    unfold hypUnionG
    rw [hsets0, hsets1, hsets2]
    exact concat_eq HS
  have hHu_get : ∀ j < 4224, (hypUnionG UL.toArray xw yw)[j]! = fl (HS j) := by
    intro j hj
    rw [hUnion, getElem!_pos _ j (by simpa using hj), Array.getElem_ofFn]
  have hHu_sz : (hypUnionG UL.toArray xw yw).size = 4224 := by
    rw [hUnion]; exact Array.size_ofFn
  have hHSlt : ∀ j < 4224, HS j < 2 ^ 693 := fun j hj => (listsP_spec (hmemK j hj)).1
  have hfamOK : famOK (hypUnionG UL.toArray xw yw)
      (famIndex (hypUnionG UL.toArray xw yw)) = true := by
    unfold famOK
    rw [Bool.and_eq_true, allIn_iff']
    refine ⟨?_, fun k _ hk => ?_⟩
    · rw [hHu_sz]; rfl
    · rw [hHu_get k hk]
      unfold findIn
      rw [famIndex_getD_key hHu_sz hHu_get hHSlt hdistS hk]
      simp
  refine ⟨hUnion, ?_, ?_, ?_, hfamOK⟩
  · exact hypOrbitOK_of (J := J0) (o := 0) (c := 1) H hTX hTY hG hmemK hdistS
      (by norm_num) ho0 hUnion
  · exact hypOrbitOK_of (J := J1) (o := 1) (c := 2) H hTX hTY hG hmemK hdistS
      (by norm_num) ho1 hUnion
  · exact hypOrbitOK_of (J := J2) (o := 2) (c := 3) H hTX hTY hG hmemK hdistS
      (by norm_num) ho2 hUnion

end CFSG.KC.Misc.Hyp

end
