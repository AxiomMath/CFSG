module

public import CFSG.Certificates.Kernel.SporLatOmRun
public import CFSG.Certificates.Kernel.SporLatOrbSound
public import Certificates.Data.Kernel.SporLatOrbP
import CFSG.Quasithin.EmptyFaithful.GoldschmidtThreeDLocKer
import Mathlib.Data.List.Sort

public section

namespace CFSG.KC.SLOrb

open CFSG.KC.SLOm CFSG.KC.E64F CFSG.QuasithinUnique.Ch1.SporLat CFSG.Quasithin.E6.Spor

theorem good_of_goodB {n : Nat} {t : Array Nat} {f : Nat → Nat} (h : goodB n t f = true) :
    Good n t f := by
  unfold goodB at h
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range, Nat.blt_eq] at h
  exact ⟨h.1, fun p hp => h.2 p hp⟩

theorem lt_of_ltB {n : Nat} {t : Array Nat} (h : ltB n t = true) : ∀ p < n, t.getD p 0 < n := by
  unfold ltB at h
  simp only [List.all_eq_true, List.mem_range, Nat.blt_eq] at h
  exact h

theorem classChk_of_orbit {n : Nat} {ta tb zT : Array Nat} {s : Nat} (O : List (List Nat))
    (hz : ∀ p < n, zT.getD p 0 < n) (hnd : O.Nodup) (hlen : O.length = s)
    (hΔ : grLabel n zT ∈ O)
    (hcl : ∀ x ∈ O, ∀ l < 2, grAct n (#[ta, tb] : Array (Array Nat))[l]! x ∈ O)
    (hreach : ∀ x ∈ O,
      Reach (fun l x => grAct n (#[ta, tb] : Array (Array Nat))[l]! x) 2 (grLabel n zT) x) :
    classChk n ta tb zT s = true := by
  have hact : ∀ l < (#[ta, tb] : Array (Array Nat)).size, ∀ x, x ∈ O →
      grAct n (#[ta, tb] : Array (Array Nat))[l]! x ∈ O ∧
        grAct n (#[ta, tb] : Array (Array Nat))[l]! x =
          grAct n (#[ta, tb] : Array (Array Nat))[l]! x :=
    fun l hl x hx => ⟨hcl x hx l (by simpa using hl), rfl⟩
  obtain ⟨R, hR, hR2, hF⟩ := omTwin_spec
    (actF := fun l x => grAct n (#[ta, tb] : Array (Array Nat))[l]! x) (m := 2) (Lset := O)
    (cap := s + 1) (fuel := s + 2) hΔ (fun l hl x hx => hcl x hx l hl) (by omega) (by omega)
  obtain ⟨hbo, -⟩ := buildOmega_of_twin (act := grAct n) (letters := #[ta, tb]) (· ∈ O) hΔ hact
    hR
  unfold Final at hF
  obtain ⟨f0, f1, f2, f3, f4, f5⟩ := hF
  have hcl' : ∀ x, Reach (fun l x => grAct n (#[ta, tb] : Array (Array Nat))[l]! x) 2
      (grLabel n zT) x → x ∈ R.1.lbl.toList := by
    intro x hx
    induction hx with
    | base =>
      rw [← f1]
      exact getElem!_mem f0
    | step hx hl ih =>
      obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.1 ih
      have hk' : k < R.1.lbl.size := by simpa using hk
      obtain ⟨g1, g2⟩ := f4 _ hl k hk'
      simp only at g2
      have e : R.1.lbl.toList[k] = R.1.lbl[k]! := by
        rw [getElem!_pos R.1.lbl k hk']
        simp
      rw [e, ← g2]
      exact getElem!_mem g1
  have hsize : R.1.lbl.size = s := by
    have hp : R.1.lbl.toList.Perm O :=
      (List.perm_ext_iff_of_nodup f2 hnd).2 fun x => ⟨f3 x, fun hx => hcl' x (hreach x hx)⟩
    rw [← hlen, ← hp.length_eq]
    simp
  unfold classChk
  simp only [hbo, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
  refine ⟨⟨List.all_eq_true.2 fun p hp => by simpa using hz p (List.mem_range.1 hp), ?_⟩, hsize⟩
  refine ⟨f1, f0, fun l hl k hk => ?_, fun k hk hk0 => ?_,
    CFSG.Quasithin.GoldD3.distinctB_of_nodup f2⟩
  · exact f4 l (by simpa using hl) k hk
  · obtain ⟨t1, t2, t3⟩ := f5 k hk hk0
    exact ⟨t1, by simpa using t2, t3⟩

theorem gP_packL {w : Nat} : ∀ (L : List Nat), (∀ e ∈ L, e < 2 ^ w) → ∀ p,
    gP w (packL w L) p = L.getD p 0
  | [], _, p => by simp [gP, packL]
  | a :: L, h, 0 => by
    have ha := h a List.mem_cons_self
    simp only [gP, packL, Nat.mul_zero, Nat.pow_zero, Nat.div_one, List.getD_cons_zero]
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt ha]
  | a :: L, h, p + 1 => by
    have ha := h a List.mem_cons_self
    have ih := gP_packL L (fun e he => h e (List.mem_cons_of_mem _ he)) p
    simp only [gP, packL, List.getD_cons_succ] at ih ⊢
    rw [Nat.mul_succ, Nat.pow_add, Nat.mul_comm (2 ^ (w * p)) (2 ^ w), ← Nat.div_div_eq_div_mul,
      Nat.add_mul_div_left _ _ (Nat.two_pow_pos w), Nat.div_eq_of_lt ha, Nat.zero_add]
    exact ih

def PV (n w T : Nat) : Prop := ∃ L : List Nat, L.length = n ∧ (∀ e ∈ L, e < n) ∧ T = packL w L

theorem gP_of_PV {n w T : Nat} (hw : n ≤ 2 ^ w) (h : PV n w T) :
    ∃ L : List Nat, L.length = n ∧ (∀ e ∈ L, e < n) ∧ ∀ p, gP w T p = L.getD p 0 := by
  obtain ⟨L, hl, he, rfl⟩ := h
  exact ⟨L, hl, he, gP_packL (w := w) L (fun e h' => by have := he e h'; omega)⟩

theorem labP_eq {n w T : Nat} {L : List Nat} (hg : ∀ p, gP w T p = L.getD p 0) :
    labP n w T = (List.range n).map fun p => p * n + L.getD p 0 := by
  unfold labP
  exact List.map_congr_left fun p _ => by rw [hg]

theorem labP_inj {n w T U : Nat} (hw : n ≤ 2 ^ w) (hT : PV n w T) (hU : PV n w U)
    (h : labP n w T = labP n w U) : T = U := by
  obtain ⟨L, hl, he, rfl⟩ := hT
  obtain ⟨M, hm, hme, rfl⟩ := hU
  have gL := gP_packL (w := w) L (fun e h' => by have := he e h'; omega)
  have gM := gP_packL (w := w) M (fun e h' => by have := hme e h'; omega)
  rw [labP_eq gL, labP_eq gM] at h
  congr 1
  refine List.ext_getElem (by rw [hl, hm]) fun p h1 h2 => ?_
  have hp : p < n := by omega
  have e := congrArg (fun l => l.getD p 0) h
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hp,
    Option.map_some, Option.getD_some] at e
  rw [List.getElem?_eq_getElem h1, List.getElem?_eq_getElem h2] at e
  simp only [Option.getD_some] at e
  omega

theorem sorted_codes (n : Nat) (f : Nat → Nat) (hf : ∀ q < n, f q < n) :
    ((List.range n).map fun q => q * n + f q).Pairwise (· ≤ ·) := by
  rw [List.pairwise_map]
  refine (List.pairwise_lt_range).imp_of_mem fun {a b} ha hb hab => ?_
  have hb' := List.mem_range.1 hb
  have := hf a (by omega)
  calc a * n + f a ≤ a * n + n := by omega
    _ = (a + 1) * n := (Nat.succ_mul _ _).symm
    _ ≤ b * n := Nat.mul_le_mul_right _ hab
    _ ≤ b * n + f b := Nat.le_add_right _ _

theorem range_map_perm {n : Nat} {g : Nat → Nat} (hg : ∀ q < n, g q < n)
    (hinj : ∀ a < n, ∀ b < n, g a = g b → a = b) : ((List.range n).map g).Perm (List.range n) := by
  refine (List.perm_ext_iff_of_nodup ?_ (List.nodup_range)).2 fun x => ⟨fun hx => ?_, fun hx => ?_⟩
  · refine List.Nodup.map_on (fun a ha b hb e => hinj a (List.mem_range.1 ha) b
      (List.mem_range.1 hb) e) List.nodup_range
  · obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hx
    exact List.mem_range.2 (hg q (List.mem_range.1 hq))
  · by_contra hn
    have hsub : (List.range n).map g ⊆ (List.range n).erase x := by
      intro y hy
      obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hy
      exact (List.mem_erase_of_ne (fun e => hn (by rw [← e]; exact List.mem_map_of_mem hq))).2
        (List.mem_range.2 (hg q (List.mem_range.1 hq)))
    have hnd : ((List.range n).map g).Nodup :=
      List.Nodup.map_on (fun a ha b hb e => hinj a (List.mem_range.1 ha) b
        (List.mem_range.1 hb) e) List.nodup_range
    have := (List.subperm_of_subset hnd hsub).length_le
    rw [List.length_map, List.length_range, List.length_erase_of_mem hx, List.length_range] at this
    have : 0 < n := by have := List.mem_range.1 hx; omega
    omega

theorem grAct_labP {n w : Nat} (hw : n ≤ 2 ^ w) {t ti T : Nat} {tA : Array Nat}
    (ht : Good n tA (gP w t)) (hi : invB n w t ti = true) (hT : PV n w T) :
    grAct n tA (labP n w T) = labP n w (conjP w n t ti T) ∧ PV n w (conjP w n t ti T) := by
  unfold invB at hi
  simp only [List.all_eq_true, List.mem_range, Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at hi
  obtain ⟨L, hl, he, hg⟩ := gP_of_PV hw hT
  have hLn : ∀ p < n, L.getD p 0 < n := fun p hp => he _ (by
    rw [List.getD_eq_getElem _ _ (by omega)]; exact List.getElem_mem _)
  set M := (List.range n).map fun q => gP w t (gP w T (gP w ti q)) with hM
  have hMe : ∀ e ∈ M, e < n := by
    intro e he'
    obtain ⟨q, hq, rfl⟩ := List.mem_map.1 he'
    have hq' := List.mem_range.1 hq
    rw [hg]
    exact (ht.2 _ (hLn _ (hi _ hq').1.2)).2
  have hMl : M.length = n := by simp [hM]
  have hPV : PV n w (conjP w n t ti T) := ⟨M, hMl, hMe, rfl⟩
  refine ⟨?_, hPV⟩
  have gM := gP_packL (w := w) M (fun e h' => by have := hMe e h'; omega)
  change grAct n tA (labP n w T) = labP n w (packL w M)
  rw [labP_eq gM, labP_eq hg]
  unfold grAct
  rw [sortN_eq, insN_eq]
  have hmap : ((List.range n).map fun p => p * n + L.getD p 0).map
      (fun c => tA.getD (c / n) 0 * n + tA.getD (c % n) 0) =
      (List.range n).map fun p => gP w t p * n + gP w t (L.getD p 0) := by
    rw [List.map_map]
    refine List.map_congr_left fun p hp => ?_
    have hp' := List.mem_range.1 hp
    have hL := hLn p hp'
    have hn : 0 < n := by omega
    have h1 : (p * n + L.getD p 0) / n = p := by
      rw [Nat.mul_comm, Nat.mul_add_div hn, Nat.div_eq_of_lt hL, Nat.add_zero]
    have h2 : (p * n + L.getD p 0) % n = L.getD p 0 := by
      rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt hL]
    simp only [Function.comp]
    rw [h1, h2, (ht.2 p hp').1, (ht.2 _ hL).1]
  rw [hmap]
  have hsorted := sorted_codes n (fun q => M.getD q 0) (fun q hq => hMe _ (by
    rw [List.getD_eq_getElem _ _ (by omega)]; exact List.getElem_mem _))
  refine List.Perm.eq_of_pairwise (fun a b _ _ h1 h2 => Nat.le_antisymm h1 h2)
    (List.pairwise_insertionSort (· ≤ ·) _) hsorted ?_
  refine (List.perm_insertionSort _ _).trans ?_
  have hgi : ∀ q < n, gP w ti q < n := fun q hq => (hi q hq).1.2
  have htp : ∀ p < n, gP w t p < n := fun p hp => (ht.2 p hp).2
  have hinj : ∀ a < n, ∀ b < n, gP w ti a = gP w ti b → a = b := by
    intro a ha b hb e
    rw [← (hi a ha).2, ← (hi b hb).2, e]
  have hperm := range_map_perm hgi hinj
  have e2 : ((List.range n).map fun q => q * n + M.getD q 0) =
      ((List.range n).map (gP w ti)).map fun p => gP w t p * n + gP w t (L.getD p 0) := by
    rw [List.map_map]
    refine List.map_congr_left fun q hq => ?_
    have hq' := List.mem_range.1 hq
    simp only [Function.comp, hM]
    rw [List.getD_eq_getElem _ _ (by simpa using hq'), List.getElem_map, List.getElem_range,
      (hi q hq').2, hg]
  rw [e2]
  exact (hperm.map _).symm

theorem classChk_of_orbP {n w : Nat} {ta tb zT : Array Nat} {t0 ti0 t1 ti1 z s : Nat}
    (hw : n ≤ 2 ^ w) (ha : Good n ta (gP w t0)) (hb : Good n tb (gP w t1))
    (hia : invB n w t0 ti0 = true) (hib : invB n w t1 ti1 = true)
    (hz : z = packL w ((List.range n).map fun p => zT.getD p 0)) (hzn : ltB n zT = true)
    (h : orbChk (actS w n [(t0, ti0), (t1, ti1)]) 2 [z] s = true) :
    classChk n ta tb zT s = true := by
  have hzn' := lt_of_ltB hzn
  obtain ⟨Oc, hnd, hlen, hΔ, hcl, hreach⟩ := orbChk_sound (actS w n [(t0, ti0), (t1, ti1)]) 2 [z] h
  have hzPV : PV n w z := ⟨_, by simp, fun e he => by
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 he
    exact hzn' p (List.mem_range.1 hp), hz⟩
  have hΔl : grLabel n zT = labP n w z := by
    have hb : ∀ e ∈ (List.range n).map (fun p => zT.getD p 0), e < 2 ^ w := by
      intro e he
      obtain ⟨p, hp, rfl⟩ := List.mem_map.1 he
      have := hzn' p (List.mem_range.1 hp)
      omega
    rw [hz]
    unfold labP grLabel
    refine List.map_congr_left fun p hp => ?_
    rw [gP_packL _ hb p]
    simp [List.getD_eq_getElem?_getD, List.getElem?_range (List.mem_range.1 hp)]
  have hlet : ∀ l < 2, ∀ T, PV n w T →
      grAct n (#[ta, tb] : Array (Array Nat))[l]! (labP n w T) =
        labP n w ((actS w n [(t0, ti0), (t1, ti1)] l [T]).headD 0) ∧
      PV n w ((actS w n [(t0, ti0), (t1, ti1)] l [T]).headD 0) := by
    intro l hl T hT
    rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl
    · exact grAct_labP hw ha hia hT
    · exact grAct_labP hw hb hib hT
  have hform : ∀ x, Reach (actS w n [(t0, ti0), (t1, ti1)]) 2 [z] x → ∃ T, x = [T] ∧ PV n w T ∧
      Reach (fun l x => grAct n (#[ta, tb] : Array (Array Nat))[l]! x) 2
        (grLabel n zT) (labP n w T) := by
    intro x hx
    induction hx with
    | base => exact ⟨z, rfl, hzPV, by rw [hΔl]; exact Reach.base⟩
    | step hx hl ih =>
      obtain ⟨T, rfl, hT, hr⟩ := ih
      obtain ⟨e1, e2⟩ := hlet _ hl T hT
      refine ⟨_, rfl, e2, ?_⟩
      have h3 := Reach.step hr hl
      rw [e1] at h3
      exact h3
  have hlab : ∀ x ∈ Oc, ∃ T, x = [T] ∧ PV n w T := fun x hx => by
    obtain ⟨T, e, hT, -⟩ := hform x (hreach x hx)
    exact ⟨T, e, hT⟩
  let lab : List Nat → List Nat := fun x => labP n w (x.headD 0)
  refine classChk_of_orbit (Oc.map lab) hzn' ?_ (by simpa using hlen) ?_ ?_ ?_
  · refine List.Nodup.map_on (fun x hx y hy e => ?_) hnd
    obtain ⟨T, rfl, hT⟩ := hlab x hx
    obtain ⟨U, rfl, hU⟩ := hlab y hy
    rw [labP_inj hw hT hU e]
  · have : grLabel n zT = lab [z] := hΔl
    rw [this]
    exact List.mem_map_of_mem hΔ
  · intro y hy l hl
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hy
    obtain ⟨T, rfl, hT⟩ := hlab x hx
    change grAct n _ (labP n w T) ∈ _
    rw [(hlet l hl T hT).1]
    exact List.mem_map_of_mem (hcl [T] hx l hl)
  · intro y hy
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hy
    obtain ⟨T, rfl, hT, hr⟩ := hform x (hreach x hx)
    exact hr

theorem classChk_of_tab {w n : Nat} {ta tb zT : Array Nat} {s : Nat} (hn : n ≤ 2 ^ w)
    (ht : tabOK w n ta tb = true) (hz : ltB n zT = true)
    (h : orbChk (actS w n [pk w n ta.toList, pk w n tb.toList]) 2 [pz w n zT] s = true) :
    classChk n ta tb zT s = true := by
  unfold tabOK at ht
  simp only [Bool.and_eq_true] at ht
  obtain ⟨⟨⟨ha, hb⟩, hia⟩, hib⟩ := ht
  exact classChk_of_orbP hn (good_of_goodB ha) (good_of_goodB hb) hia hib rfl hz h

end CFSG.KC.SLOrb

end
