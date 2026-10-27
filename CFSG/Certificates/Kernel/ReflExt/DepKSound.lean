module

public import Certificates.Data.Kernel.ReflExt.DepK
public import Certificates.Data.CFSGNative.DepFrame.Check
public import CFSG.Certificates.Kernel.ReflExt.NineKSound

public section

namespace CFSG.ReflExt.DK

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace W6

open CFSG.TwoNodeSmall CFSG.TwoNodeSmall.LaneSound CFSG.TwoNodeSmall.PosBK
  CFSG.TwoNodeSmall.PosBK.OKS CFSG.TwoNodeSmall.WitK CFSG.TwoNodeSmall.WitK.OK CFSG.DepFrame

variable {P : Pt}

theorem chkD_common {k : Nat} {sm : List Nat} {clo : List (Nat × Nat × Nat × Nat)}
    {lv : List (Nat × List Nat × List Nat)} {ex : List (List Nat)}
    (h : chkPtD P (k, sm, clo, lv, ex) = true) :
    ∃ (hp : P.p = 3) (hD : P.D ≤ 10) (_ : Fact P.p.Prime), P.WF ∧ wfCheck P = true ∧
      ∃ Dl : List CE, (∀ x ∈ Dl, Sem P x) ∧
        wK6 P.D (Nat.mul 3 (ones P.D)) (Nat.mul 16 (Nat.sub P.D 1)) (yK P.D) Dl.length
          (P.gens.map (packR P)) (Dl.map fun x => packR P x.1) sm ex lv = true := by
  change (Nat.beq P.p 3 && Nat.ble 1 P.D && Nat.ble P.D 10 && Nat.beq k 3 &&
    (gensK P).all (fun g => Nat.beq (dotK (Nat.mul 16 (Nat.sub P.D 1)) g.2 g.1) 2) &&
    cloK (Nat.mul 3 (ones P.D)) (Nat.mul 16 (Nat.sub P.D 1)) (gensK P).length (gensK P)
      (gensK P ++ clo.map fun e => (e.2.2.1, e.2.2.2)) clo (gensK P).length 0
      (gensK P ++ clo.map fun e => (e.2.2.1, e.2.2.2)) &&
    wK6 P.D (Nat.mul 3 (ones P.D)) (Nat.mul 16 (Nat.sub P.D 1)) (yK P.D)
      (Nat.add (gensK P).length clo.length) (gensK P)
      (gensK P ++ clo.map fun e => (e.2.2.1, e.2.2.2)) sm ex lv) = true at h
  simp only [Bool.and_eq_true, Nat.beq_eq, Nat.ble_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨hp, -⟩, hD⟩, -⟩, hG⟩, hclo⟩, hkind⟩ := h
  have hfact : Fact P.p.Prime := ⟨by rw [hp]; norm_num⟩
  rw [gensK_eqW hp] at hG hclo hkind
  obtain ⟨hWF, hwf⟩ := WF_of_gens hp hD hG
  have hclo' : cloK (Nat.mul 3 (ones P.D)) (Nat.mul 16 (Nat.sub P.D 1)) P.gens.length
      (P.gens.map (packR P)) (P.gens.map (packR P) ++ clo.map ent) clo P.gens.length 0
      (P.gens.map (packR P) ++ clo.map ent) = true := by
    rw [List.length_map] at hclo
    exact hclo
  obtain ⟨hDl, hsem⟩ := clo_specW hp hD clo _ hclo'
  have hlen : (cloD P (baseD P) clo).length = P.gens.length + clo.length := by
    have := congrArg List.length hDl
    simp only [List.length_map, List.length_append] at this
    exact this
  refine ⟨hp, hD, hfact, hWF, hwf, cloD P (baseD P) clo, hsem, ?_⟩
  have e1 : (P.gens.map (packR P) ++ clo.map fun e => (e.2.2.1, e.2.2.2)) =
      (cloD P (baseD P) clo).map (fun x => packR P x.1) := hDl.symm
  have e2 : Nat.add (P.gens.map (packR P)).length clo.length = (cloD P (baseD P) clo).length := by
    rw [hlen, List.length_map]
    rfl
  rw [e1, e2] at hkind
  exact hkind

theorem e6E_eq (i j : Nat) : e6E i j = e6Edge i j := by
  unfold e6E e6Edge
  simp only [nbeqW]

theorem pair_cond6 (i j a b : Nat)
    (h : (bif e6E i j then Nat.beq (Nat.mod (Nat.mul a b) 3) 1 else Nat.beq a 0 && Nat.beq b 0)
      = true) : (if e6Edge i j then (a * b) % 3 == 1 else a == 0 && b == 0) = true := by
  rw [e6E_eq, nbeqW, nbeqW, nbeqW] at h
  cases hx : e6Edge i j
  · rw [hx] at h
    exact h
  · rw [hx] at h
    exact h

theorem weyl6_verify {r : WitK.Rec} (h : chkPtD P r = true) :
    wfCheck P = true ∧ ∃ c, verifyWE6 P c = true := by
  obtain ⟨k, sm, clo, lv, ex⟩ := r
  obtain ⟨hp, hD, hfact, hWF, hwf, Dl, hsem, hk⟩ := chkD_common h
  refine ⟨hwf, ?_⟩
  unfold wK6 at hk
  simp only [Bool.and_eq_true] at hk
  obtain ⟨⟨⟨⟨⟨⟨k2, k3⟩, k4⟩, k5⟩, k6⟩, k7⟩, k8⟩ := hk
  have hsig : ∀ i ∈ sm, i < Dl.length := by
    intro i hi
    have := List.all_eq_true.mp k3 i hi
    rwa [Nat.blt_eq] at this
  have hsigl : sm.length = 6 := Nat.eq_of_beq_eq_true k2
  let xs := sm.map fun i => Dl.getD i dfl
  have hxs : ∀ x ∈ xs, Sem P x := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
    rw [List.getD_eq_getElem _ _ (hsig i hi)]
    exact hsem _ (List.getElem_mem _)
  have hxl : xs.length = 6 := by simp [xs, hsigl]
  have hSK : sm.map (nthK (0, 0) (Dl.map fun x => packR P x.1)) = (xs.map (·.1)).map (packR P) := by
    simp only [xs, List.map_map]
    apply List.map_congr_left
    intro i hi
    rw [nthK_eq', List.getD_eq_getElem _ _ (by simpa using hsig i hi), List.getElem_map,
      Function.comp_apply, Function.comp_apply, List.getD_eq_getElem _ _ (hsig i hi)]
  rw [hSK] at k4 k5 k7
  set Sv := xs.map (·.1) with hSv
  have hSvl : Sv.length = 6 := by simp [hSv, hxl]
  have k8' : 51839 < chainK P.D (Nat.mul 3 (ones P.D)) (Nat.mul 16 (Nat.sub P.D 1)) (yK P.D)
      Dl.length (Dl.map fun x => packR P x.1) lv 0 1 := by
    rwa [Nat.blt_eq] at k8
  obtain ⟨Ls, hLs⟩ := chainK_spec hp hD hWF Dl hsem lv [] 0 1 (by simp) (by simp) (by omega)
  simp only [List.map_nil] at hLs
  have hgetx : ∀ i (hi : i < xs.length), P.vec (P.sigmaVecs xs[i].2.1 xs[i].2.2).1 =
      P.vec (Sv.getD i ⟨[], []⟩).h ∧ P.vec (P.sigmaVecs xs[i].2.1 xs[i].2.2).2 =
      P.vec (Sv.getD i ⟨[], []⟩).f := by
    intro i hi
    have e : Sv.getD i ⟨[], []⟩ = xs[i].1 := by
      simp [hSv, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
    rw [e]
    exact sig_vecs (hxs _ (List.getElem_mem _))
  refine ⟨⟨5, xs.map (fun x => (x.2.1, x.2.2)), ex, ⟨Ls⟩⟩, ?_⟩
  unfold verifyWE6
  simp only [Bool.and_eq_true]
  refine ⟨⟨⟨?_, ?_⟩, ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩⟩, ?_⟩
  · rw [beq_iff_eq, List.length_map]
    exact hxl
  · rw [List.all_eq_true]
    intro s hs
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hs
    have := hxs x hx
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨this.1, this.2.1⟩
  · rw [List.all_eq_true]
    intro cb hcb
    simp only [List.map_map, List.mem_map] at hcb
    obtain ⟨x, hx, rfl⟩ := hcb
    have hsx := sig_vecs (hxs x hx)
    have h2 := List.all_eq_true.mp k4 (packR P x.1)
      (List.mem_map.mpr ⟨x.1, List.mem_map.mpr ⟨x, hx, rfl⟩, rfl⟩)
    rw [Nat.beq_eq, packR3 hp, dotKW_pk hp hD] at h2
    rw [beq_iff_eq, Function.comp_apply, dotv_congr hsx.2 hsx.1, h2, hp]
  · rw [List.all_eq_true]
    intro i hi
    rw [List.all_eq_true]
    intro j hj
    have k5ij := List.all_eq_true.mp (List.all_eq_true.mp k5 i hi) j hj
    rw [List.mem_range] at hi hj
    rw [Bool.or_eq_true] at k5ij ⊢
    rcases k5ij with k | k
    · left
      rw [Nat.beq_eq] at k
      rw [k, beq_self_eq_true]
    · right
      have hiS : i < Sv.length := by omega
      have hjS : j < Sv.length := by omega
      have hl : (xs.map fun x => (x.2.1, x.2.2)).map (fun s => P.sigmaVecs s.1 s.2) =
          xs.map fun x => P.sigmaVecs x.2.1 x.2.2 := by
        rw [List.map_map]
        rfl
      have hgi : ((xs.map fun x => (x.2.1, x.2.2)).map (fun s => P.sigmaVecs s.1 s.2)).getD i
          ([], []) = P.sigmaVecs xs[i].2.1 xs[i].2.2 := by
        rw [hl, List.getD_eq_getElem _ _ (by simp; omega), List.getElem_map]
      have hgj : ((xs.map fun x => (x.2.1, x.2.2)).map (fun s => P.sigmaVecs s.1 s.2)).getD j
          ([], []) = P.sigmaVecs xs[j].2.1 xs[j].2.2 := by
        rw [hl, List.getD_eq_getElem _ _ (by simp; omega), List.getElem_map]
      have hnK : ∀ l (hl : l < Sv.length), nthK (0, 0) (Sv.map (packR P)) l =
          packR P (Sv.getD l ⟨[], []⟩) := by
        intro l hl
        rw [nthK_eq', List.getD_eq_getElem _ _ (by simpa using hl), List.getElem_map,
          List.getD_eq_getElem _ _ hl]
      have ha : dotK (Nat.mul 16 (Nat.sub P.D 1)) (nthK (0, 0) (Sv.map (packR P)) i).2
          (nthK (0, 0) (Sv.map (packR P)) j).1 =
          P.dotv (P.sigmaVecs xs[i].2.1 xs[i].2.2).2 (P.sigmaVecs xs[j].2.1 xs[j].2.2).1 := by
        rw [hnK i hiS, hnK j hjS, packR3 hp, packR3 hp, dotKW_pk hp hD,
          dotv_congr (hgetx i (by omega)).2 (hgetx j (by omega)).1]
      have hb : dotK (Nat.mul 16 (Nat.sub P.D 1)) (nthK (0, 0) (Sv.map (packR P)) j).2
          (nthK (0, 0) (Sv.map (packR P)) i).1 =
          P.dotv (P.sigmaVecs xs[j].2.1 xs[j].2.2).2 (P.sigmaVecs xs[i].2.1 xs[i].2.2).1 := by
        rw [hnK i hiS, hnK j hjS, packR3 hp, packR3 hp, dotKW_pk hp hD,
          dotv_congr (hgetx j (by omega)).2 (hgetx i (by omega)).1]
      unfold pairOK6 at k
      rw [ha, hb] at k
      have hpc := pair_cond6 _ _ _ _ k
      simp only [hgi, hgj, hp]
      exact hpc
  · rw [beq_iff_eq]
    have := Nat.eq_of_beq_eq_true k6
    rwa [List.length_map] at this
  · rw [List.all_eq_true]
    intro x hx
    obtain ⟨w, r⟩ := x
    have hm : (w, packR P r) ∈ ex.zip (P.gens.map (packR P)) := by
      rw [List.zip_map_right]
      exact List.mem_map.mpr ⟨(w, r), hx, rfl⟩
    have h7 := List.all_eq_true.mp k7 _ hm
    simp only [Bool.and_eq_true] at h7
    obtain ⟨hw, he⟩ := h7
    have hw' : ∀ l ∈ w, l < 6 := by
      intro l hl
      have := List.all_eq_true.mp hw l hl
      rwa [Nat.blt_eq] at this
    simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq]
    refine ⟨hw', fun j hj => ?_⟩
    rw [List.mem_range] at hj
    have hej := exprCols_spec _ _ _ w _ P.D he j hj
    rw [shiftLeft_unit P hj, wordK_spec hp hD Sv w (fun l hl => hSvl ▸ hw' l hl), packR3 hp,
      appKW_pk hp hD] at hej
    have hv := vec_of_vecEq P ((pk_inj hp _ _).mp hej)
    apply vecEq_of_vec
    have hSMl : ((xs.map fun x => (x.2.1, x.2.2)).map (fun s => P.sigmaVecs s.1 s.2)).length =
        6 := by simp [hxl]
    have hSM : ∀ l (hl : l < ((xs.map fun x => (x.2.1, x.2.2)).map
        (fun s => P.sigmaVecs s.1 s.2)).length),
        P.vec ((xs.map fun x => (x.2.1, x.2.2)).map (fun s => P.sigmaVecs s.1 s.2))[l].1 =
          P.vec (Sv.getD l ⟨[], []⟩).h ∧
        P.vec ((xs.map fun x => (x.2.1, x.2.2)).map (fun s => P.sigmaVecs s.1 s.2))[l].2 =
          P.vec (Sv.getD l ⟨[], []⟩).f := by
      intro l hl
      simp only [List.getElem_map]
      exact hgetx l (by simpa using hl)
    rw [sigmaWord_spec _ Sv hSM w (fun l hl => hSMl ▸ hw' l hl) (P.unit j), hv]
  · unfold verifyO
    rw [hLs]
    exact decide_eq_true k8'

end W6

open CFSG.TwoNodeSmall CFSG.TwoNodeSmall.WitK CFSG.TwoNodeSmall.ExclK CFSG.TwoNodeSmall.LaneSound
  CFSG.TwoNodeSmall.PosBK CFSG.TwoNodeSmall.PosBK.OKS CFSG.ReflExt CFSG.ReflExt.RXK CFSG.NineAll
  CFSG.DepFrame CFSG.ReflExt.NK CFSG.ReflExt.NK.NS

open Snd (decR)

open Classical in
@[expose] noncomputable def witE6 (Q : Pt) : Witness :=
  if h : ∃ c, verifyWE6 Q c = true then .weyl (Classical.choose h) else .kernel []

theorem witE6_spec {Q : Pt} (h : ∃ c, verifyWE6 Q c = true) :
    ∃ c, witE6 Q = .weyl c ∧ verifyWE6 Q c = true := by
  unfold witE6
  rw [dif_pos h]
  exact ⟨_, rfl, Classical.choose_spec h⟩

@[expose] noncomputable def mk1D (P : Pt) (cd : List (Nat × Nat)) (rp : NK.Rep1) : NRep :=
  { r := decR P.D rp.1
    kind := if rp.2.1 = 0 then .cent
      else if rp.2.2.1.1 = 3 then .w (witE6 (ptX P [rp.1] P.bound))
      else .w (witB (ptX P [rp.1] P.bound) rp.2.2.1.1)
    roots := rootsD (withExtra P [decR P.D rp.1])
      (cloD (withExtra P [decR P.D rp.1]) (baseD (withExtra P [decR P.D rp.1])) rp.2.2.2.1)
    reps2 := (fillL (cn P.D) rp.2.2.2.2.1).map (mk2 P rp.1)
    orb2 := Snd.ob2 P.D cd rp.2.2.2.2.2 }

theorem partD_lt {P : Pt} {B : Nat} {d : FDN} {i : Nat} (hi : i < 15) :
    partD P B d i = partN P B d i := by
  unfold partD
  simp only [Nat.blt_eq.mpr hi, cond_true]

theorem partD_verify (P : Pt) (B : Nat) (d : FDN) (h : ∀ i < 21, partD P B d i = true) :
    ∃ T, verifyAllD P B T = true := by
  have hN : ∀ i < 15, partN P B d i = true := fun i hi => by
    rw [← partD_lt hi]
    exact h i (by omega)
  obtain ⟨rows, bk, cd, tg, R0, R1⟩ := d
  have h0 := hN 0 (by norm_num)
  have h9 := hN 9 (by norm_num)
  have h14 := hN 14 (by norm_num)
  have h15 := h 15 (by norm_num)
  have h20 := h 20 (by norm_num)
  unfold partN at h0 h9 h14
  unfold partD at h15 h20
  simp only [Nat.beq_refl, cond_true, beqF (by norm_num : (9 : Nat) ≠ 0),
    beqF (by norm_num : (14 : Nat) ≠ 0), beqF (by norm_num : (14 : Nat) ≠ 9),
    bltF (by norm_num : ¬ (9 : Nat) < 9), bltF (by norm_num : ¬ (14 : Nat) < 9),
    bltF (by norm_num : ¬ (14 : Nat) < 14), cond_false] at h0 h9 h14
  simp only [Nat.beq_refl, cond_true, bltF (by norm_num : ¬ (15 : Nat) < 15),
    bltF (by norm_num : ¬ (20 : Nat) < 15), beqF (by norm_num : (20 : Nat) ≠ 15),
    bltF (by norm_num : ¬ (20 : Nat) < 20), cond_false, Bool.true_and] at h15 h20
  have hmsk : ∀ k < 8, mskB (ptF P) P.D (cloE (gensK P) rows)
      (slc (Nat.succ (Nat.div bk.length 8)) k bk) = true := by
    intro k hk
    have := hN (k + 1) (by omega)
    unfold partN at this
    simp only [beqF (by omega : k + 1 ≠ 0), cond_false,
      Nat.blt_eq.mpr (by omega : k + 1 < 9), cond_true] at this
    exact this
  have htg : ∀ k < 4, all2 (tagN (ptF P) P.D (gensK P).length (Nat.add (gensK P).length rows.length)
      (pk P.D P.x) (gensK P) (cloE (gensK P) rows) R0 R1)
      (slc (Nat.succ (Nat.div cd.length 4)) k cd) (slc (Nat.succ (Nat.div cd.length 4)) k tg) =
      true := by
    intro k hk
    have := hN (k + 10) (by omega)
    unfold partN at this
    simp only [beqF (by omega : k + 10 ≠ 0), beqF (by omega : k + 10 ≠ 9), cond_false,
      bltF (by omega : ¬ k + 10 < 9), Nat.blt_eq.mpr (by omega : k + 10 < 14), cond_true] at this
    exact this
  have hs2 : ∀ r < 4, allI (fun j rp => bne (Nat.beq (Nat.mod j 4) r) true || !(needs2D rp) ||
      s2N P (ptF P) (gensK P) (pk P.D P.x) cd rp) R1 0 = true := by
    intro r hr
    have := h (r + 16) (by omega)
    unfold partD at this
    simp only [bltF (by omega : ¬ r + 16 < 15), beqF (by omega : r + 16 ≠ 15), cond_false,
      Nat.blt_eq.mpr (by omega : r + 16 < 20), cond_true, Nat.add_sub_cancel] at this
    exact this
  change (Nat.beq P.p 3 && Nat.ble 1 P.D && Nat.ble P.D 9 && allK (reflOK (fdB 3 P.D)) (gensK P) &&
      allK (fun g => Nat.beq (dotK (fdB 3 P.D) g.2 (pk P.D P.x)) 0) (gensK P) &&
      cloP (fdB 3 P.D) (gensK P).length (gensK P) rows (gensK P).length 0 (cloE (gensK P) rows) &&
      allK (fun r => Nat.beq (dotK (fdB 3 P.D) r.2 (pk P.D P.x)) 0) (cloE (gensK P) rows) &&
      bkS (Nat.pow 3 P.D) bk 0 (0, 0, true) (0, 0, true)) = true at h0
  simp only [Bool.and_eq_true, Nat.beq_eq, Nat.ble_eq] at h0
  obtain ⟨⟨⟨⟨⟨⟨⟨hp, -⟩, hD9⟩, hrefl⟩, hGX⟩, hclo⟩, hX⟩, hbkS⟩ := h0
  have hD : P.D ≤ 10 := by omega
  have hfact : Fact P.p.Prime := ⟨by rw [hp]; norm_num⟩
  have hL := laneOK_three hp hD
  have hgk := Snd.gensK_eq hp
  change candOK (fdB 3 P.D) P.D bk cd = true at h9
  change allK (fun rp => reflOK (fdB 3 P.D) rp.1 &&
    Nat.beq (dotK (fdB 3 P.D) rp.1.2 (pk P.D P.x)) 0 && recBad (ptX P [rp.1] B) rp.2) R0 = true at h14
  change allK (fun rp => reflOK (fdB 3 P.D) rp.1 &&
      !(Nat.beq (dotK (fdB 3 P.D) rp.1.2 (pk P.D P.x)) 0) &&
      (bif Nat.beq rp.2.1 0 then centK (fdB 3 P.D) P.D (gensK P) rp.1
       else Nat.beq rp.2.1 1 &&
         (bif Nat.beq rp.2.2.1.1 3 then chkPtD (ptX P [rp.1] P.bound) rp.2.2.1
          else (Nat.beq rp.2.2.1.1 1 || Nat.beq rp.2.2.1.1 2) &&
            chkPt (ptX P [rp.1] P.bound) rp.2.2.1))) R1 = true at h15
  change centTags (fdB 3 P.D) P.D R1 cd tg = true at h20
  unfold ptF at hmsk htg hs2
  rw [hgk] at hrefl hGX hclo hX hmsk htg h15 hs2
  have hrefl' := (Snd.allK_spec _ _).mp hrefl
  have hWF : P.WF := by
    intro g hg
    have := hrefl' (packR P g) (List.mem_map.mpr ⟨g, hg, rfl⟩)
    rw [Snd.packR3 hp, reflOK_pk hp hD] at this
    exact Snd.WF_of_dotv this
  have hwfP := Snd.wfCheck_of_WF hp hWF
  rw [List.length_map] at hclo
  obtain ⟨hDl, hsem⟩ := Snd.clo_spec hL rows hclo
  have hC : cloE (P.gens.map (packR P)) rows =
      ((cloD P (baseD P) rows).map fun x => decR P.D (packR P x.1)).map (packR P) := by
    refine hDl.symm.trans ?_
    rw [List.map_map]
    apply List.map_congr_left
    intro x _
    exact (Snd.packR_decR hp (Snd.canP_packR hp x.1)).symm
  have hnC : Nat.add (P.gens.map (packR P)).length rows.length =
      (cloD P (baseD P) rows).length := by
    have := congrArg List.length hDl
    simp only [List.length_map, List.length_append] at this
    rw [List.length_map]
    exact this.symm
  rw [hC] at hX hmsk htg
  rw [hnC] at htg
  set Dl := cloD P (baseD P) rows with hDl_def
  set ys := Dl.map fun x => decR P.D (packR P x.1) with hys
  have hbk : bkK (fdB 3 P.D) P.D (Nat.pow 3 P.D) (ys.map (packR P)) bk 0 (0, 0, true)
      (0, 0, true) = true := by
    apply bkK_of bk 0 _ _ hbkS
    intro b hb
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hb
    have hs : 0 < Nat.succ (Nat.div bk.length 8) := Nat.succ_pos _
    have hk : i / Nat.succ (Nat.div bk.length 8) < 8 := by
      apply (Nat.div_lt_iff_lt_mul hs).2
      change i < 8 * Nat.succ (bk.length / 8)
      omega
    have hm := hmsk _ hk
    unfold mskB at hm
    have := (Snd.allK_spec _ _).mp hm _ (mem_slc hs hi)
    rw [Bool.and_eq_true] at this
    exact this
  have hcdE : ∀ x ∈ cd, packR P (decR P.D x) = x ∧ P.dotv (decR P.D x).f (decR P.D x).h = 2 :=
    fun x hx => Snd.cd_entry hp hD h9 hx
  have htag := all2_slc (Nat.succ_pos _)
    (by change cd.length ≤ 4 * Nat.succ (cd.length / 4); omega) htg
  set T : NTables := ⟨rootsD P Dl, obT P.D 1 cd tg, (fillL (cn P.D) R0).map (mk0 P B),
    obT P.D 2 cd tg, (fillL (cn P.D) R1).map (mk1D P cd)⟩ with hT
  have hsub : ∀ ρ ∈ ys, ρ ∈ T.roots.map (·.r) := by
    intro ρ hρ
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hρ
    exact List.mem_map.mpr ⟨Snd.rt P x,
      (List.mem_flatMap.mpr ⟨x, hx, by simp⟩ : Snd.rt P x ∈ rootsD P Dl), rfl⟩
  have hcandL : ∀ c ∈ candOfN P T, decR P.D (packR P c) = c ∧ packR P c ∈ cd :=
    fun c hc => cand_mem2 hp hD hsub hbk h9 hc
  have hcanR : ∀ (i : Nat) (hi : i < cd.length) (u : List Nat) (a : Nat × Nat),
      ltAll (P.gens.map (packR P)).length u = true →
      eqPM (fdB 3 P.D) P.D a (cw (fdB 3 P.D) (P.gens.map (packR P)) u cd[i]) = true →
      canP P.D a = true ∧ realizes (withExtra P [decR P.D cd[i]])
        (u ++ [P.gens.length] ++ u.reverse) (decR P.D a) = true := by
    intro i hi u a hu heq
    obtain ⟨hpe, hde⟩ := hcdE cd[i] (List.getElem_mem hi)
    have hu' := Snd.ltAll_spec _ u hu
    rw [← hpe, Snd.cw_pack hL _ _ (gens_nth P) u hu'] at heq
    obtain ⟨hca, heq'⟩ := eqPM_canon hp heq
    refine ⟨hca, Snd.conj_real hp hD hWF _ _ hde u (by simpa using hu) ?_⟩
    rw [Snd.cw_pack hL _ _ (gens_nth P) u hu']
    exact heq'
  have hR0 : ∀ rp ∈ R0, reflOK (fdB 3 P.D) rp.1 = true ∧
      dotK (fdB 3 P.D) rp.1.2 (pk P.D P.x) = 0 ∧ (rp.2.1 = 1 ∨ rp.2.1 = 2) ∧
      chkPt (ptX P [rp.1] B) rp.2 = true := by
    intro rp hrp
    have := (Snd.allK_spec _ _).mp h14 rp hrp
    simp only [recBad, Bool.and_eq_true, Bool.or_eq_true, Nat.beq_eq] at this
    exact ⟨this.1.1, this.1.2, this.2.1, this.2.2⟩
  have hR1 : ∀ rp ∈ R1, reflOK (fdB 3 P.D) rp.1 = true ∧
      dotK (fdB 3 P.D) rp.1.2 (pk P.D P.x) ≠ 0 ∧
      (rp.2.1 = 0 → centK (fdB 3 P.D) P.D (P.gens.map (packR P)) rp.1 = true) ∧
      (rp.2.1 ≠ 0 → rp.2.1 = 1 ∧
        (rp.2.2.1.1 = 3 → chkPtD (ptX P [rp.1] P.bound) rp.2.2.1 = true) ∧
        (rp.2.2.1.1 ≠ 3 → (rp.2.2.1.1 = 1 ∨ rp.2.2.1.1 = 2) ∧
          chkPt (ptX P [rp.1] P.bound) rp.2.2.1 = true)) := by
    intro rp hrp
    have := (Snd.allK_spec _ _).mp h15 rp hrp
    rw [Bool.and_eq_true, Bool.and_eq_true] at this
    obtain ⟨⟨h1, h2⟩, h3⟩ := this
    refine ⟨h1, fun e => ?_, fun e => ?_, fun e => ?_⟩
    · rw [e] at h2
      exact absurd h2 (by decide)
    · rw [e] at h3
      exact h3
    · rw [beqF e, cond_false, Bool.and_eq_true, Nat.beq_eq] at h3
      obtain ⟨hk1, h3⟩ := h3
      refine ⟨hk1, fun e3 => ?_, fun e3 => ?_⟩
      · have e3' : Nat.beq rp.2.2.1.1 3 = true := by rw [e3]; rfl
        rw [e3', cond_true] at h3
        exact h3
      · rw [beqF e3, cond_false, Bool.and_eq_true, Bool.or_eq_true, Nat.beq_eq, Nat.beq_eq] at h3
        exact h3
  have hv0 : vFixN P = true := by
    unfold vFixN
    rw [List.all_eq_true]
    intro g hg
    have := (Snd.allK_spec _ _).mp hGX (packR P g) (List.mem_map.mpr ⟨g, hg, rfl⟩)
    rw [beq_iff_eq]
    exact fix_of_pack hp hD this
  have hv1 : vRootsN P T = true := by
    unfold vRootsN
    rw [List.all_eq_true]
    intro ρ hρ
    have hρ' : ρ ∈ rootsD P Dl := hρ
    obtain ⟨x, hx, hρx⟩ := List.mem_flatMap.mp hρ'
    obtain ⟨hw, hr, hfx⟩ := roots_ok hp hWF (hsem x hx) ρ hρx
    have hfix : P.dotv (decR P.D (packR P x.1)).f P.x = 0 := by
      have := (Snd.allK_spec _ _).mp hX (packR P (decR P.D (packR P x.1)))
        (List.mem_map.mpr ⟨_, List.mem_map.mpr ⟨x, hx, rfl⟩, rfl⟩)
      exact fix_of_pack hp hD this
    simp only [Bool.and_eq_true, beq_iff_eq]
    exact ⟨⟨hw, hr⟩, hfx hfix⟩
  have hv2 : vCover0 P T (candOfN P T) = true := by
    unfold vCover0
    rw [List.all_eq_true]
    intro c hc'
    rw [List.mem_filter] at hc'
    obtain ⟨hc', hfx⟩ := hc'
    rw [beq_iff_eq] at hfx
    obtain ⟨hdc, hcm⟩ := hcandL c hc'
    obtain ⟨i, hi, hci⟩ := List.mem_iff_getElem.mp hcm
    obtain ⟨hi', ht⟩ := htag i hi
    have hfxK : dotK (fdB 3 P.D) cd[i].2 (pk P.D P.x) = 0 := by
      rw [hci, dotK_packR hp hD, hfx]
    rw [Bool.or_eq_true, List.any_eq_true, List.any_eq_true]
    rcases tagN_cases ht with ⟨j, -, -, hj, heq⟩ | ⟨j, u, htj, -, -, -, -⟩ | ⟨j, u, -, hm, -⟩
    · left
      have hjl : j < ys.length := by rw [hys, List.length_map]; exact hj
      rw [Snd.nthK_map _ _ hjl] at heq
      have hyj : packR P ys[j] = packR P Dl[j].1 := by
        simp only [hys, List.getElem_map]
        exact Snd.packR_decR hp (Snd.canP_packR hp _)
      rw [hyj] at heq
      unfold eqPM at heq
      rw [Bool.or_eq_true] at heq
      unfold eqP at heq
      simp only [Bool.and_eq_true, Nat.beq_eq] at heq
      rcases heq with heq | heq
      · refine ⟨Snd.rt P Dl[j], (List.mem_flatMap.mpr ⟨Dl[j], List.getElem_mem _, by simp⟩ :
          Snd.rt P Dl[j] ∈ rootsD P Dl), ?_⟩
        have e : cd[i] = packR P Dl[j].1 := Prod.ext heq.1 heq.2
        change reqb (decR P.D (packR P Dl[j].1)) c = true
        rw [← e, hci, hdc]
        exact Snd.reqb_self c
      · refine ⟨Snd.rtN P Dl[j], (List.mem_flatMap.mpr ⟨Dl[j], List.getElem_mem _, by simp⟩ :
          Snd.rtN P Dl[j] ∈ rootsD P Dl), ?_⟩
        have e : cd[i] = packR P (Snd.negRf P.D Dl[j].1) :=
          (Prod.ext heq.1 heq.2).trans (Snd.negP_packR hp _)
        change reqb (decR P.D (packR P (Snd.negRf P.D Dl[j].1))) c = true
        rw [← e, hci, hdc]
        exact Snd.reqb_self c
    · right
      refine ⟨⟨decR P.D cd[i], u, j⟩, mem_obT hi hi' htj, ?_⟩
      change reqb (decR P.D cd[i]) c = true
      rw [hci, hdc]
      exact Snd.reqb_self c
    · exact absurd hfxK hm
  have hv3 : vCover1 P T (candOfN P T) = true := by
    unfold vCover1 movingOf
    rw [List.all_eq_true]
    intro c hc'
    rw [List.mem_filter] at hc'
    obtain ⟨hc', hmv⟩ := hc'
    obtain ⟨hdc, hcm⟩ := hcandL c hc'
    obtain ⟨i, hi, hci⟩ := List.mem_iff_getElem.mp hcm
    obtain ⟨hi', ht⟩ := htag i hi
    have hmK : dotK (fdB 3 P.D) cd[i].2 (pk P.D P.x) ≠ 0 := by
      rw [hci, dotK_packR hp hD]
      simpa using hmv
    rw [List.any_eq_true]
    rcases tagN_cases ht with ⟨j, -, h0', -⟩ | ⟨j, u, -, h0', -⟩ | ⟨j, u, htj, -, -⟩
    · exact absurd h0' hmK
    · exact absurd h0' hmK
    · refine ⟨⟨decR P.D cd[i], u, j⟩, mem_obT hi hi' htj, ?_⟩
      change reqb (decR P.D cd[i]) c = true
      rw [hci, hdc]
      exact Snd.reqb_self c
  have hv4 : T.orb0.all (entry0OK P T) = true := by
    rw [List.all_eq_true]
    intro e he
    have he' : e ∈ obT P.D 1 cd tg := he
    obtain ⟨i, hi, hi', j, u, hju, rfl⟩ := of_mem_obT he'
    obtain ⟨hi'', ht⟩ := htag i hi
    rw [hju] at ht
    rcases tagN_cases ht with ⟨j', e1, -⟩ | ⟨j', u', e1, -, hj, hu, heq⟩ | ⟨j', u', e1, -⟩
    · exact absurd (List.cons.inj e1).1 (by decide)
    · obtain ⟨rfl, rfl⟩ := List.cons.inj (List.cons.inj e1).2
      rw [nthK_eq', List.getD_eq_getElem _ _ hj] at heq
      obtain ⟨hca, hreal⟩ := hcanR i hi u _ hu heq
      have hget : T.reps0[j]? = some (mk0 P B R0[j]) := by
        change ((fillL (cn P.D) R0).map (mk0 P B))[j]? = _
        rw [List.getElem?_map, fill_get hj hca]
        rfl
      obtain ⟨-, hde⟩ := hcdE cd[i] (List.getElem_mem hi)
      unfold entry0OK
      simp only [Bool.and_eq_true, decide_eq_true_eq]
      refine ⟨⟨Snd.wfR_of_dotv hp hde, lt_of_get hget⟩, ?_⟩
      rw [hget]
      exact hreal
    · exact absurd (List.cons.inj e1).1 (by decide)
  have hv5 : T.reps0.all (rep0OK P B) = true := by
    rw [List.all_eq_true]
    intro rp' hrp'
    have hrp'' : rp' ∈ (fillL (cn P.D) R0).map (mk0 P B) := hrp'
    obtain ⟨rp, hrp, rfl⟩ := List.mem_map.mp hrp''
    obtain ⟨hmem, hca⟩ := fill_mem hrp
    obtain ⟨hrf, hfx, hk, hchk⟩ := hR0 rp hmem
    obtain ⟨hpr, hd2⟩ := canon_facts hp hD hca hrf
    obtain ⟨hbad, hver⟩ := witB_bad hchk hk
    unfold rep0OK verifyBad
    simp only [Bool.and_eq_true, beq_iff_eq]
    refine ⟨⟨Snd.wfR_of_dotv hp hd2, ?_⟩, hbad, hver⟩
    change P.dotv (decR P.D rp.1).f P.x = 0
    rw [← dotK_packR hp hD, hpr]
    exact hfx
  have hv6 : T.orb1.all (entry1OK P T) = true := by
    rw [List.all_eq_true]
    intro e he
    have he' : e ∈ obT P.D 2 cd tg := he
    obtain ⟨i, hi, hi', j, u, hju, rfl⟩ := of_mem_obT he'
    obtain ⟨hi'', ht⟩ := htag i hi
    rw [hju] at ht
    rcases tagN_cases ht with ⟨j', e1, -⟩ | ⟨j', u', e1, -⟩ | ⟨j', u', e1, -, hj, hu, heq⟩
    · exact absurd (List.cons.inj e1).1 (by decide)
    · exact absurd (List.cons.inj e1).1 (by decide)
    · obtain ⟨rfl, rfl⟩ := List.cons.inj (List.cons.inj e1).2
      rw [nthK_eq', List.getD_eq_getElem _ _ hj] at heq
      obtain ⟨hca, hreal⟩ := hcanR i hi u _ hu heq
      have hget : T.reps[j]? = some (mk1D P cd R1[j]) := by
        change ((fillL (cn P.D) R1).map (mk1D P cd))[j]? = _
        rw [List.getElem?_map, fill_get hj hca]
        rfl
      obtain ⟨-, hde⟩ := hcdE cd[i] (List.getElem_mem hi)
      unfold entry1OK
      simp only [Bool.and_eq_true, decide_eq_true_eq]
      refine ⟨⟨Snd.wfR_of_dotv hp hde, lt_of_get hget⟩, ?_⟩
      rw [hget]
      exact hreal
  have hst : ∀ rp ∈ R1, canP P.D rp.1 = true → needs2D rp = true →
      verifyStage2N P (candOfN P T) (mk1D P cd rp) = true := by
    intro rp hrp hca hn2
    obtain ⟨hrf, -, -, -⟩ := hR1 rp hrp
    obtain ⟨j, hj, hjr⟩ := List.mem_iff_getElem.mp hrp
    have hs := allI_spec _ R1 0 (hs2 (j % 4) (Nat.mod_lt _ (by norm_num))) j hj
    rw [Nat.zero_add, hjr] at hs
    have e1 : Nat.beq (Nat.mod j 4) (j % 4) = true := Nat.beq_refl _
    rw [e1, hn2] at hs
    have hs' : s2N P (fdB 3 P.D) (P.gens.map (packR P)) (pk P.D P.x) cd rp = true := hs
    obtain ⟨a, kd, rc, ro, Qs, tg2⟩ := rp
    unfold s2N at hs'
    simp only [Bool.and_eq_true] at hs'
    obtain ⟨⟨⟨hclo2, -⟩, hQ⟩, hall2⟩ := hs'
    dsimp only at hca hrf hQ hall2 hclo2 ⊢
    obtain ⟨hr, hd2⟩ := canon_facts hp hD hca hrf
    set P1 := withExtra P [decR P.D a] with hP1
    have hWF1 : P1.WF := Snd.wf_extra hWF (Snd.WF_of_dotv hd2)
    have hfact1 : Fact P1.p.Prime := hfact
    have hL1 := laneOK_three (P := P1) hp hD
    have hG1 : P1.gens.map (packR P1) = P.gens.map (packR P) ++ [a] := by
      change (P.gens ++ [decR P.D a]).map (packR P) = _
      rw [List.map_append, List.map_singleton, hr]
    rw [← hG1] at hclo2 hall2
    rw [List.length_map] at hclo2
    obtain ⟨hDl2, hsem2⟩ := Snd.clo_spec hL1 ro hclo2
    set Dl2 := cloD P1 (baseD P1) ro with hDl2_def
    have hC2 : cloE (P1.gens.map (packR P1)) ro = Dl2.map (fun x => packR P1 x.1) := hDl2.symm
    rw [hC2] at hall2
    have hlen2 : Nat.add (P1.gens.map (packR P1)).length ro.length = Dl2.length := by
      have := congrArg List.length hDl2
      simp only [List.length_map, List.length_append] at this
      rw [List.length_map]
      exact this.symm
    rw [hlen2] at hall2
    obtain ⟨hl12, hall⟩ := Snd.all2_spec _ cd tg2 hall2
    unfold verifyStage2N
    simp only [Bool.and_eq_true]
    refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
    ·
      unfold s2RootsN
      rw [List.all_eq_true]
      intro ρ hρ
      have hρ' : ρ ∈ rootsD P1 Dl2 := hρ
      obtain ⟨x, hx, hρx⟩ := List.mem_flatMap.mp hρ'
      obtain ⟨hw, hre, -⟩ := roots_ok (P := P1) hp hWF1 (hsem2 x hx) ρ hρx
      rw [Bool.and_eq_true]
      exact ⟨hw, hre⟩
    ·
      unfold s2RepsN
      rw [List.all_eq_true]
      intro q' hq'
      have hq'' : q' ∈ (fillL (cn P.D) Qs).map (mk2 P a) := hq'
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hq''
      obtain ⟨hqm, hqc⟩ := fill_mem hq
      have hq1 := (Snd.allK_spec _ _).mp hQ q hqm
      simp only [recBad, Bool.and_eq_true, Bool.or_eq_true, Nat.beq_eq] at hq1
      obtain ⟨hqr, hqk, hqchk⟩ := hq1
      obtain ⟨-, hqd⟩ := canon_facts hp hD hqc hqr
      obtain ⟨hbad, hver⟩ := witB_bad hqchk hqk
      unfold verifyBad
      simp only [Bool.and_eq_true]
      exact ⟨Snd.wfR_of_dotv hp hqd, hbad, hver⟩
    ·
      unfold s2OrbN
      rw [List.all_eq_true]
      intro x hx
      have hx' : x ∈ Snd.ob2 P.D cd tg2 := hx
      obtain ⟨i, hi, hi2, k, w, htg2, rfl⟩ := Snd.of_mem_ob2 hx'
      have ht2 := hall i hi hi2
      rw [htg2] at ht2
      rcases tag2N_cases ht2 with h' | h' | ⟨-, hk, hw, heq⟩ | h'
      all_goals first | exact absurd h'.1 (by norm_num) | skip
      obtain ⟨hpe, hde⟩ := hcdE cd[i] (List.getElem_mem hi)
      rw [nthK_eq', List.getD_eq_getElem _ _ hk] at heq
      have hw' := Snd.ltAll_spec _ w hw
      have hpe1 : packR P1 (decR P1.D cd[i]) = cd[i] := hpe
      rw [← hpe1, Snd.cw_pack hL1 _ _ (gens_nth P1) w hw'] at heq
      obtain ⟨hqc, heq'⟩ := eqPM_canon (P := P1) hp heq
      have hget : (mk1D P cd (a, kd, rc, ro, Qs, tg2)).reps2[k]? = some (mk2 P a Qs[k]) := by
        change ((fillL (cn P.D) Qs).map (mk2 P a))[k]? = _
        rw [List.getElem?_map, fill_get hk hqc]
        rfl
      simp only [Bool.and_eq_true, decide_eq_true_eq]
      refine ⟨⟨Snd.wfR_of_dotv hp hde, lt_of_get hget⟩, ?_⟩
      rw [hget]
      change realizes (withExtra P [decR P.D a, decR P.D cd[i]])
        (w ++ [P.gens.length + 1] ++ w.reverse) (decR P.D Qs[k].1) = true
      rw [← Snd.withExtra_two]
      have hlen : P.gens.length + 1 = P1.gens.length := by simp [hP1]
      rw [hlen]
      apply Snd.conj_real (P := P1) hp hD hWF1 _ _ hde w (by simpa using hw)
      rw [Snd.cw_pack hL1 _ _ (gens_nth P1) w hw']
      exact heq'
    ·
      rw [List.all_eq_true]
      intro c hc'
      unfold movingOf at hc'
      rw [List.mem_filter] at hc'
      obtain ⟨hc', hmv⟩ := hc'
      obtain ⟨hdc, hcm⟩ := hcandL c hc'
      obtain ⟨i, hi, hci⟩ := List.mem_iff_getElem.mp hcm
      have hi2 : i < tg2.length := by omega
      have ht2 := hall i hi hi2
      rcases htg2 : tg2[i] with ⟨t0, k, w⟩
      rw [htg2, hci] at ht2
      unfold s2CandN asymAny
      simp only [Bool.or_eq_true, List.any_eq_true]
      rcases tag2N_cases ht2 with ⟨-, hk, heq⟩ | ⟨-, hk, has⟩ | ⟨h2, -, -, -⟩ | ⟨-, hfx⟩
      · simp only [Snd.nthK_map _ _ hk] at heq
        unfold eqPM eqP at heq
        simp only [Bool.or_eq_true, Bool.and_eq_true, Nat.beq_eq] at heq
        refine Or.inl (Or.inl ?_)
        rcases heq with ⟨e1, e2⟩ | ⟨e1, e2⟩
        · have he : packR P c = packR P1 Dl2[k].1 := Prod.ext e1 e2
          refine ⟨(Snd.rt P1 Dl2[k]).r, List.mem_map.mpr ⟨_, List.mem_flatMap.mpr
            ⟨Dl2[k], List.getElem_mem hk, by simp [hP1]⟩, rfl⟩, ?_⟩
          change reqb c (decR P.D (packR P1 Dl2[k].1)) = true
          rw [← he, hdc]
          exact Snd.reqb_self c
        · have he : packR P c = packR P1 (Snd.negRf P1.D Dl2[k].1) :=
            (Prod.ext e1 e2).trans (Snd.negP_packR (P := P1) hp _)
          refine ⟨(Snd.rtN P1 Dl2[k]).r, List.mem_map.mpr ⟨_, List.mem_flatMap.mpr
            ⟨Dl2[k], List.getElem_mem hk, by simp [hP1]⟩, rfl⟩, ?_⟩
          change reqb c (decR P.D (packR P1 (Snd.negRf P1.D Dl2[k].1))) = true
          rw [← he, hdc]
          exact Snd.reqb_self c
      · simp only [Snd.nthK_map _ _ hk] at has
        have hpr : packR P1 Dl2[k].1 = packR P (decR P.D (packR P1 Dl2[k].1)) :=
          (Snd.packR_decR hp (Snd.canP_packR (P := P1) hp _)).symm
        rw [hpr] at has
        simp only [Snd.packR3 hp, dotK_pk hp hD, Snd.nbeq] at has
        refine Or.inl (Or.inr ⟨(Snd.rt P1 Dl2[k]).r, List.mem_map.mpr ⟨_,
          List.mem_flatMap.mpr ⟨Dl2[k], List.getElem_mem hk, by simp [hP1]⟩, rfl⟩, ?_⟩)
        exact has
      · refine Or.inr ⟨⟨decR P.D cd[i], w, k⟩, Snd.mem_ob2 hi hi2 (by rw [htg2, h2]), ?_⟩
        change reqb (decR P.D cd[i]) c = true
        rw [hci, hdc]
        exact Snd.reqb_self c
      · exfalso
        rw [dotK_packR hp hD] at hfx
        rw [hfx] at hmv
        exact absurd hmv (by decide)
  have hv7 : T.reps.all (verifyRepD P (candOfN P T)) = true := by
    rw [List.all_eq_true]
    intro rp' hrp'
    have hrp'' : rp' ∈ (fillL (cn P.D) R1).map (mk1D P cd) := hrp'
    obtain ⟨rp, hrp, rfl⟩ := List.mem_map.mp hrp''
    obtain ⟨hmem, hca⟩ := fill_mem hrp
    obtain ⟨hrf, hmvK, hk0, hk1⟩ := hR1 rp hmem
    obtain ⟨hpr, hd2⟩ := canon_facts hp hD hca hrf
    unfold verifyRepD
    rw [Bool.and_eq_true, Bool.and_eq_true]
    refine ⟨⟨Snd.wfR_of_dotv hp hd2, ?_⟩, ?_⟩
    · change (P.dotv (decR P.D rp.1).f P.x != 0) = true
      rw [← dotK_packR hp hD, hpr]
      simpa using hmvK
    by_cases hz : rp.2.1 = 0
    · have hk : (mk1D P cd rp).kind = .cent := if_pos hz
      rw [hk]
      change centOK P (decR P.D rp.1) = true
      refine centOK_of hp hD ?_
      rw [hpr]
      exact hk0 hz
    · obtain ⟨hkd, hk3, hk12⟩ := hk1 hz
      by_cases h3 : rp.2.2.1.1 = 3
      · obtain ⟨hwf1, hc⟩ := W6.weyl6_verify (hk3 h3)
        obtain ⟨c, hc, hver⟩ := witE6_spec hc
        have hk : (mk1D P cd rp).kind = .w (.weyl c) := by
          change (if rp.2.1 = 0 then NKind.cent
            else if rp.2.2.1.1 = 3 then .w (witE6 (ptX P [rp.1] P.bound))
            else .w (witB (ptX P [rp.1] P.bound) rp.2.2.1.1)) = _
          rw [if_neg hz, if_pos h3, hc]
        rw [hk]
        have hs := hst rp hmem hca (by unfold needs2D; rw [hkd, h3]; rfl)
        change (wfCheck (withExtra P [decR P.D rp.1]) && verifyWE6 (withExtra P [decR P.D rp.1]) c &&
          verifyStage2N P (candOfN P T) (mk1D P cd rp)) = true
        rw [hs, Bool.and_true, Bool.and_eq_true]
        exact ⟨hwf1, hver⟩
      · obtain ⟨hkk, hchk⟩ := hk12 h3
        have hk : (mk1D P cd rp).kind = .w (witB (ptX P [rp.1] P.bound) rp.2.2.1.1) := by
          change (if rp.2.1 = 0 then NKind.cent
            else if rp.2.2.1.1 = 3 then .w (witE6 (ptX P [rp.1] P.bound))
            else .w (witB (ptX P [rp.1] P.bound) rp.2.2.1.1)) = _
          rw [if_neg hz, if_neg h3]
        rw [hk]
        obtain ⟨hbad, hver⟩ := witB_bad hchk hkk
        generalize witB (ptX P [rp.1] P.bound) rp.2.2.1.1 = w at hbad hver ⊢
        cases w <;> first | exact hver | simp [isBadW] at hbad
  have hv8 : T.orb1.all (centEntryOK P T) = true := by
    obtain ⟨-, hct⟩ := Snd.all2_spec _ cd tg h20
    rw [List.all_eq_true]
    intro e he
    have he' : e ∈ obT P.D 2 cd tg := he
    obtain ⟨i, hi, hi', j, u, hju, rfl⟩ := of_mem_obT he'
    obtain ⟨hi'', ht⟩ := htag i hi
    have hc := hct i hi hi'
    rw [hju] at ht hc
    rcases tagN_cases ht with ⟨j', e1, -⟩ | ⟨j', u', e1, -⟩ | ⟨j', u', e1, -, hj, hu, heq⟩
    · exact absurd (List.cons.inj e1).1 (by decide)
    · exact absurd (List.cons.inj e1).1 (by decide)
    · obtain ⟨rfl, rfl⟩ := List.cons.inj (List.cons.inj e1).2
      rw [nthK_eq', List.getD_eq_getElem _ _ hj] at heq
      obtain ⟨hca, -⟩ := hcanR i hi u _ hu heq
      have hget : T.reps[j]? = some (mk1D P cd R1[j]) := by
        change ((fillL (cn P.D) R1).map (mk1D P cd))[j]? = _
        rw [List.getElem?_map, fill_get hj hca]
        rfl
      have hc' : (bne (Nat.beq 2 2) true || bne (Nat.beq (nthK r10 R1 j).2.1 0) true ||
          eqPM (fdB 3 P.D) P.D cd[i] (nthK r10 R1 j).1) = true := hc
      rw [nthK_eq', List.getD_eq_getElem _ _ hj] at hc'
      unfold centEntryOK
      rw [hget]
      by_cases hz : R1[j].2.1 = 0
      · have hk : (mk1D P cd R1[j]).kind = .cent := if_pos hz
        obtain ⟨hrf, -, -, -⟩ := hR1 R1[j] (List.getElem_mem hj)
        obtain ⟨hr, -⟩ := canon_facts hp hD hca hrf
        rw [hz] at hc'
        have hpm : eqPM (fdB 3 P.D) P.D cd[i] R1[j].1 = true := by
          simpa [Nat.beq_refl] using hc'
        dsimp only
        rw [hk]
        change (reqb (decR P.D cd[i]) (decR P.D R1[j].1) ||
          reqb (decR P.D cd[i]) (negR P (decR P.D R1[j].1))) = true
        unfold eqPM eqP at hpm
        simp only [Bool.or_eq_true, Bool.and_eq_true, Nat.beq_eq] at hpm
        rw [Bool.or_eq_true]
        rcases hpm with ⟨e1, e2⟩ | ⟨e1, e2⟩
        · left
          have e : cd[i] = R1[j].1 := Prod.ext e1 e2
          rw [e]
          exact Snd.reqb_self _
        · right
          have e : cd[i] = packR P (Snd.negRf P.D (decR P.D R1[j].1)) := by
            rw [← Snd.negP_packR hp, hr]
            exact Prod.ext e1 e2
          rw [e, decR_negRf hp, negR_eq hp]
          exact Snd.reqb_self _
      · have hk : ∃ w, (mk1D P cd R1[j]).kind = .w w := by
          change ∃ w, (if R1[j].2.1 = 0 then NKind.cent
            else if R1[j].2.2.1.1 = 3 then .w (witE6 (ptX P [R1[j].1] P.bound))
            else .w (witB (ptX P [R1[j].1] P.bound) R1[j].2.2.1.1)) = .w w
          rw [if_neg hz]
          by_cases h3 : R1[j].2.2.1.1 = 3
          · rw [if_pos h3]
            exact ⟨_, rfl⟩
          · rw [if_neg h3]
            exact ⟨_, rfl⟩
        obtain ⟨w, hk⟩ := hk
        dsimp only
        rw [hk]
  refine ⟨T, ?_⟩
  unfold verifyAllD
  simp only [hwfP, hv0, hv1, hv2, hv3, hv4, hv5, hv6, hv7, hv8, Bool.and_self]

end CFSG.ReflExt.DK

end
