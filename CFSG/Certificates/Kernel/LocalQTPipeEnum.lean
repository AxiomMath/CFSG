module

public import CFSG.Certificates.Kernel.LocalQTPipeBasic
public import CFSG.Certificates.Kernel.LocalQTX1HProved
import all CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListPermEnc

public section

namespace CFSG.KC.LQT.PPE

open CFSG.KC.Ord CFSG.KC.LQT.S CFSG.KC.LQT.L CFSG.KC.LQT.PW CFSG.KC.LQT.BC
open CFSG.KC.LQT.PP CFSG.KC.LQT.BW CFSG.KC.LQT.BT CFSG.KC.LQT.BS.Cl
open CFSG.KC.LQT.BW.Pf CFSG.KC.LQT.XH.Pf CFSG.KC.LQT.PPB
open CFSG.QuasithinUnique.K1.SporadicPerm CFSG.QuasithinUnique.Setup.X1
open CFSG.QuasithinUnique.Vol2Native.A312L.PermLat (bfsSet bfsRun bfsRun_sound closedH closedH_spec)

private inductive WR {M : Type} [Mul M] [One M] (gens : List M) : M → Prop
  | one : WR gens 1
  | step {y g : M} : WR gens y → g ∈ gens → WR gens (y * g)

private inductive WL {M : Type} [Mul M] [One M] (gens : List M) : M → Prop
  | one : WL gens 1
  | step {y g : M} : WL gens y → g ∈ gens → WL gens (g * y)

section Words

variable {M : Type} [Mul M] [One M] {gens : List M}
  (hA : ∀ a b : M, ∀ c ∈ gens, a * b * c = a * (b * c)) (hC : ∀ g ∈ gens, (1 : M) * g = g * 1)

include hA hC

private theorem wr_left {y g : M} (hy : WR gens y) (hg : g ∈ gens) : WR gens (g * y) := by
  induction hy with
  | one =>
    rw [← hC g hg]
    exact WR.step WR.one hg
  | @step y g' _ hg' ih =>
    rw [← hA g y g' hg']
    exact WR.step ih hg'

private theorem wl_right {y g : M} (hy : WL gens y) (hg : g ∈ gens) : WL gens (y * g) := by
  induction hy with
  | one =>
    rw [hC g hg]
    exact WL.step WL.one hg
  | @step y g' _ hg' ih =>
    rw [hA g' y g hg]
    exact WL.step ih hg'

private theorem wl_of_wr {x : M} (hx : WR gens x) : WL gens x := by
  induction hx with
  | one => exact WL.one
  | step _ hg ih => exact wl_right hA hC ih hg

private theorem wr_of_wl {x : M} (hx : WL gens x) : WR gens x := by
  induction hx with
  | one => exact WR.one
  | step _ hg ih => exact wr_left hA hC ih hg

end Words

private structure PCd (n w : Nat) where
  val : Nat
  deriving DecidableEq, Hashable

private noncomputable instance (n w : Nat) : Mul (PCd n w) := ⟨fun a b => ⟨mulW n w a.val b.val⟩⟩

private noncomputable instance (n w : Nat) : One (PCd n w) := ⟨⟨oneW n w⟩⟩

private theorem cd_mul_val {n w : Nat} (a b : PCd n w) : (a * b).val = mulW n w a.val b.val := rfl

private theorem cd_one_val {n w : Nat} : (1 : PCd n w).val = oneW n w := rfl

private theorem cd_ext {n w : Nat} {a b : PCd n w} (h : a.val = b.val) : a = b := by
  cases a; cases b; cases h; rfl

private theorem cd_inj {n w : Nat} : Function.Injective (PCd.val : PCd n w → Nat) := fun _ _ h =>
  cd_ext h

private theorem recMap {α β : Type} (f : α → β) : ∀ l : List α,
    List.rec (motive := fun _ => List β) [] (fun x _ ih => f x :: ih) l = l.map f
  | [] => rfl
  | x :: l => by
    change f x :: List.rec (motive := fun _ => List β) [] (fun x _ ih => f x :: ih) l = _
    rw [recMap f l, List.map_cons]

private theorem cd_assoc {n w : Nat} {gens : List (PCd n w)} :
    ∀ a b : PCd n w, ∀ c ∈ gens, (∀ i < n, imgW w c.val i < n) → a * b * c = a * (b * c) := by
  intro a b c _ hc
  exact cd_ext (mulW_assoc hc)

private theorem cd_comm {n w : Nat} (hw : n ≤ 2 ^ w) (g : PCd n w)
    (hv : ∀ i < n, imgW w g.val i < n) : (1 : PCd n w) * g = g * 1 := by
  have h1 := vc_one (n := n) (w := w) hw
  apply cd_ext
  rw [cd_mul_val, cd_mul_val, cd_one_val]
  apply code_eq (vc_mul h1.1 hv) (vc_mul hv h1.1)
  intro i hi
  rw [imgW_mulW hi, imgW_mulW hi, imgW_one hw hi, imgW_one hw (hv i hi)]

private theorem wr_vc {n w : Nat} (hw : n ≤ 2 ^ w) {gens : List (PCd n w)}
    (hG : ∀ g ∈ gens, ∀ i < n, imgW w g.val i < n) {x : PCd n w} (hx : WR gens x) :
    VC n w x.val := by
  induction hx with
  | one => exact vc_one hw
  | step _ hg ih => exact vc_mul ih.1 (hG _ hg)

private noncomputable def tab (n w : Nat) (P : List Nat) (x : PCd n w) : List Nat :=
  P.map (imgW w x.val)

private theorem tab_step {n w : Nat} {P : List Nat} (hP : ∀ p ∈ P, p < n) {g x : PCd n w}
    {s : Array Nat} (hs : Rep n w g.val s) (hx : ∀ i < n, imgW w x.val i < n) :
    applyTab s (tab n w P x) = tab n w P (g * x) := by
  rw [applyTab, tab, tab, List.map_map]
  apply List.map_congr_left
  intro p hp
  rw [Function.comp_apply, cd_mul_val, imgW_mulW (hP p hp), (hs.2 _ (hx p (hP p hp))).2]

private theorem enum_aux {n w : Nat} (hw : n ≤ 2 ^ w) (ta tb : List Nat)
    (prog qp : List (Nat × Nat)) (k fuel d : Nat) (RL : List Nat)
    (h : enumK n w ta tb prog qp k fuel d RL = true) :
    qpOK n (slpTabsA ta.toArray tb.toArray prog) qp ∧
    BaseEnumOK n (List.range n)
      (qp.map fun p => (slpTabsA ta.toArray tb.toArray prog)[p.1]!)
      (qp.map fun p => (slpTabsA ta.toArray tb.toArray prog)[p.2]!)
      (bfsEnumB n (List.range n)
        (qp.map fun p => (slpTabsA ta.toArray tb.toArray prog)[p.1]!)
        (qp.map fun p => (slpTabsA ta.toArray tb.toArray prog)[p.2]!) fuel).1
      (bfsEnumB n (List.range n)
        (qp.map fun p => (slpTabsA ta.toArray tb.toArray prog)[p.1]!)
        (qp.map fun p => (slpTabsA ta.toArray tb.toArray prog)[p.2]!) fuel).2.1
      (bfsEnumB n (List.range n)
        (qp.map fun p => (slpTabsA ta.toArray tb.toArray prog)[p.1]!)
        (qp.map fun p => (slpTabsA ta.toArray tb.toArray prog)[p.2]!) fuel).2.2 ∧
    (bfsEnumB n (List.range n)
        (qp.map fun p => (slpTabsA ta.toArray tb.toArray prog)[p.1]!)
        (qp.map fun p => (slpTabsA ta.toArray tb.toArray prog)[p.2]!)
        fuel).1.size = 2 ^ k := by
  classical
  unfold enumK at h
  simp only [andB_eq, Bool.and_eq_true] at h
  obtain ⟨hta, htb, hso, hR⟩ := h
  obtain ⟨hlen, hrep⟩ := slpW_rep hw hta htb hso
  generalize slpTabsA ta.toArray tb.toArray prog = T at hlen hrep ⊢
  generalize slpW n w (codeK w ta) (codeK w tb) prog = R at hlen hrep hR
  unfold enumR at hR
  simp only [andB_eq, Bool.and_eq_true] at hR
  obtain ⟨hqp, hqi, hQ⟩ := hR
  beta_reduce at hQ
  rw [recMap] at hQ
  simp only [allBs_cons, allBs_nil, Bool.and_true, Bool.and_eq_true] at hQ
  obtain ⟨hcl, hsz, hfu, -⟩ := hQ
  rw [allA_eq, List.all_eq_true] at hqp hqi
  have hq1 : ∀ p ∈ qp, p.1 < T.size ∧ p.2 < T.size := by
    intro p hp
    have := hqp p hp
    rw [Bool.and_eq_true, Nat.blt_eq, Nat.blt_eq, hlen] at this
    exact this
  have hinvq : ∀ a ∈ qp, ∀ q < n, img T[a.2]! (img T[a.1]! q) = q := fun a ha =>
    rep_inv (hrep a.1 (hq1 a ha).1) (hrep a.2 (hq1 a ha).2) hw
      (Nat.eq_of_beq_eq_true (by simpa using hqi a ha))
  refine ⟨fun p hp => ⟨(hq1 p hp).1, (hq1 p hp).2, hinvq p hp⟩, ?_⟩
  set G := qp.map fun p => T[p.1]! with hGdef
  set Gi := qp.map fun p => T[p.2]! with hGidef
  have hGl : G.length = qp.length := by rw [hGdef, List.length_map]
  have hGil : Gi.length = qp.length := by rw [hGidef, List.length_map]
  have hGj : ∀ j (hj : j < qp.length), G[j]! = T[qp[j].1]! := by
    intro j hj
    rw [getElem!_pos G j (by omega)]
    simp only [hGdef, List.getElem_map]
  have hGij : ∀ j (hj : j < qp.length), Gi[j]! = T[qp[j].2]! := by
    intro j hj
    rw [getElem!_pos Gi j (by omega)]
    simp only [hGidef, List.getElem_map]
  generalize hGc : (qp.map fun p => nodeK R p.1) = Gc at hcl hsz hfu
  obtain ⟨gens, hgens⟩ : ∃ gens : List (PCd n w), gens.map PCd.val = Gc :=
    ⟨Gc.map PCd.mk, by rw [List.map_map]; exact List.map_id' _⟩
  subst hgens
  have hgens_mem : ∀ g ∈ gens, ∃ s ∈ G, Rep n w g.val s := by
    intro g hg
    have : g.val ∈ qp.map fun p => nodeK R p.1 := by
      rw [hGc]
      exact List.mem_map_of_mem hg
    obtain ⟨p, hp, hpg⟩ := List.mem_map.1 this
    exact ⟨T[p.1]!, List.mem_map_of_mem hp, by rw [← hpg]; exact hrep p.1 (hq1 p hp).1⟩
  have hmem_gens : ∀ s ∈ G, ∃ g ∈ gens, Rep n w g.val s := by
    intro s hs
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hs
    have : nodeK R p.1 ∈ gens.map PCd.val := by
      rw [← hGc]
      exact List.mem_map_of_mem hp
    obtain ⟨g, hg, hgv⟩ := List.mem_map.1 this
    exact ⟨g, hg, by rw [hgv]; exact hrep p.1 (hq1 p hp).1⟩
  have hGf : ∀ g ∈ gens, ∀ i < n, imgW w g.val i < n := by
    intro g hg
    obtain ⟨s, -, hs⟩ := hgens_mem g hg
    exact rep_fields hs
  have hA : ∀ a b : PCd n w, ∀ c ∈ gens, a * b * c = a * (b * c) := fun a b c hc =>
    cd_assoc a b c hc (hGf c hc)
  have hC : ∀ g ∈ gens, (1 : PCd n w) * g = g * 1 := fun g hg => cd_comm hw g (hGf g hg)
  have hS : CFSG.KC.LQT.L.Rep (PCd.val : PCd n w → Nat)
      (bfsG (mulW n w) ((1 : PCd n w).val) (gens.map PCd.val) d) (bfsSet gens d) :=
    rep_bfs (φ := (PCd.val : PCd n w → Nat)) cd_inj (mulW n w) (fun a b => rfl) gens d
  have hcH : closedH gens (bfsSet gens d) = true :=
    (closedG_eq (φ := (PCd.val : PCd n w → Nat)) cd_inj (mulW n w) (fun a b => rfl) gens hS).symm.trans
      hcl
  obtain ⟨hc1, hclos⟩ := closedH_spec hcH
  obtain ⟨-, -, E, hEnd, hEH, -, hEsz⟩ := hS
  have hH_WR : ∀ x ∈ bfsSet gens d, WR gens x := by
    intro x hx
    unfold bfsSet at hx
    refine bfsRun_sound gens (WR gens) (fun y hy g hg => WR.step hy hg) d
      (((∅ : Std.HashSet (PCd n w)).insert 1), [1]) ?_ ?_ x hx
    · intro y hy
      rw [Std.HashSet.mem_insert] at hy
      rcases hy with hy | hy
      · have : (1 : PCd n w) = y := beq_iff_eq.mp hy
        rw [← this]
        exact WR.one
      · have := Std.HashSet.contains_iff_mem.mpr hy
        simp [Std.HashSet.contains_empty] at this
    · intro y hy
      rw [List.mem_singleton] at hy
      rw [hy]
      exact WR.one
  have hWR_H : ∀ x, WR gens x → x ∈ bfsSet gens d := by
    intro x hx
    induction hx with
    | one => exact hc1
    | step _ hg ih => exact hclos _ ih _ hg
  have hE : ∀ x, x ∈ E ↔ WR gens x := fun x => by
    rw [← hEH]
    exact ⟨hH_WR x, hWR_H x⟩
  have hvc : ∀ x ∈ E, VC n w x.val := fun x hx => wr_vc hw hGf ((hE x).1 hx)
  have hoN : ∀ p ∈ ptsOf (List.range n) G, p < n := by
    intro x hx
    rw [ptsOf, List.mem_append, List.mem_flatMap] at hx
    rcases hx with hx | ⟨s, hs, hx⟩
    · exact List.mem_range.1 hx
    · rw [List.mem_map] at hx
      obtain ⟨b, hb, rfl⟩ := hx
      obtain ⟨g, -, hg⟩ := hmem_gens s hs
      exact (hg.2 b (List.mem_range.1 hb)).1
  have hUget : ∀ x q, q < n → (tab n w (ptsOf (List.range n) G) x).getD q 0 = imgW w x.val q := by
    intro x q hq
    have hlen : q < (ptsOf (List.range n) G).length := by
      rw [ptsOf, List.length_append, List.length_range]
      omega
    rw [tab, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hlen,
      Option.map_some, Option.getD_some]
    have : (ptsOf (List.range n) G).getD q 0 = q := by
      rw [ptsOf, List.getD_eq_getElem?_getD, List.getElem?_append_left (by simp; omega),
        List.getElem?_range hq, Option.getD_some]
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlen, Option.getD_some] at this
    rw [this]
  have hUinj : ∀ x ∈ E, ∀ y ∈ E, (∀ q < n, imgW w x.val q = imgW w y.val q) → x = y :=
    fun x hx y hy h => cd_ext (code_eq (hvc x hx) (hvc y hy) h)
  have hU0 : tab n w (ptsOf (List.range n) G) 1 = ptsOf (List.range n) G := by
    rw [tab]
    conv_rhs => rw [← List.map_id (ptsOf (List.range n) G)]
    apply List.map_congr_left
    intro p hp
    rw [cd_one_val, imgW_one hw (hoN p hp)]
    rfl
  set Ul := E.map (tab n w (ptsOf (List.range n) G)) with hUl
  have hUv : ∀ T ∈ Ul, Val n (ptsOf (List.range n) G).length T := by
    intro T hT
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hT
    refine ⟨by rw [tab, List.length_map], fun y hy => ?_⟩
    rw [tab, List.mem_map] at hy
    obtain ⟨p, hp, rfl⟩ := hy
    exact (hvc x hx).1 p (hoN p hp)
  have hclo : ∀ T ∈ Ul, ∀ s ∈ G, applyTab s T ∈ Ul := by
    intro T hT s hs
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hT
    obtain ⟨g, hg, hrs⟩ := hmem_gens s hs
    rw [tab_step hoN hrs (hvc x hx).1]
    exact List.mem_map_of_mem ((hE _).2 (wr_left hA hC ((hE x).1 hx) hg))
  have hkey : ∀ T ∈ Ul, ∀ V ∈ Ul, keyNat n (List.range n).length T =
      keyNat n (List.range n).length V → T = V := by
    intro T hT V hV e
    rw [keyNat_eq_iff (hUv T hT) (hUv V hV)] at e
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hT
    obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hV
    rw [hUinj x hx y hy fun q hq => by
      have := congrArg (fun l => l.getD q 0) e
      simp only [List.length_range, List.getD_eq_getElem?_getD, List.getElem?_take_of_lt hq]
        at this
      rw [← List.getD_eq_getElem?_getD, ← List.getD_eq_getElem?_getD, hUget x q hq,
        hUget y q hq] at this
      exact this]
  have hoU : ptsOf (List.range n) G ∈ Ul :=
    List.mem_map.2 ⟨1, (hE 1).2 WR.one, hU0⟩
  have hUnd : Ul.Nodup := by
    apply List.Nodup.map_on _ hEnd
    intro x hx y hy e
    exact hUinj x hx y hy fun q hq => by rw [← hUget x q hq, ← hUget y q hq, e]
  have hreach : ∀ A : List (List Nat), ptsOf (List.range n) G ∈ A →
      (∀ T ∈ A, T ∈ Ul → ∀ s ∈ G, applyTab s T ∈ A) → ∀ T ∈ Ul, T ∈ A := by
    intro A hoA hA' T hT
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hT
    have hwl := wl_of_wr hA hC ((hE x).1 hx)
    clear hx hT
    induction hwl with
    | one =>
      rw [hU0]
      exact hoA
    | @step y g hy hg ih =>
      obtain ⟨s, hs, hrs⟩ := hgens_mem g hg
      have hyE : y ∈ E := (hE y).2 (wr_of_wl hA hC hy)
      rw [← tab_step hoN hrs (hvc y hyE).1]
      exact hA' _ ih (List.mem_map_of_mem hyE) s hs
  have hfuel : Ul.length ≤ fuel := by
    rw [hUl, List.length_map, ← hEsz]
    exact Nat.le_of_ble_eq_true hfu
  obtain ⟨hbe, hsize, -⟩ := bfs_closed (G := G) (Gi := Gi) fuel (by rw [hGl, hGil]) (fun j hj q hq => by
      have hj' : j < qp.length := by omega
      rw [hGj j hj', hGij j hj']
      exact hinvq _ (List.getElem_mem _) q hq) hUv hclo hkey hoU hUnd hreach hfuel
  refine ⟨hbe, ?_⟩
  rw [hsize, hUl, List.length_map, ← hEsz]
  exact Nat.eq_of_beq_eq_true hsz

theorem enum_sound {n w : Nat} (hw : n ≤ 2 ^ w) (a b : Array (Array Nat)) (prog qp : List (Nat × Nat))
    (k fuel d : Nat) (RL : List Nat)
    (h : enumK n w (chunksK a) (chunksK b) prog qp k fuel d RL = true) :
    qpOK n (slpTabsA (Array.flatten a) (Array.flatten b) prog) qp ∧
    BaseEnumOK n (List.range n)
      (qp.map fun p => (slpTabsA (Array.flatten a) (Array.flatten b) prog)[p.1]!)
      (qp.map fun p => (slpTabsA (Array.flatten a) (Array.flatten b) prog)[p.2]!)
      (bfsEnumB n (List.range n)
        (qp.map fun p => (slpTabsA (Array.flatten a) (Array.flatten b) prog)[p.1]!)
        (qp.map fun p => (slpTabsA (Array.flatten a) (Array.flatten b) prog)[p.2]!) fuel).1
      (bfsEnumB n (List.range n)
        (qp.map fun p => (slpTabsA (Array.flatten a) (Array.flatten b) prog)[p.1]!)
        (qp.map fun p => (slpTabsA (Array.flatten a) (Array.flatten b) prog)[p.2]!) fuel).2.1
      (bfsEnumB n (List.range n)
        (qp.map fun p => (slpTabsA (Array.flatten a) (Array.flatten b) prog)[p.1]!)
        (qp.map fun p => (slpTabsA (Array.flatten a) (Array.flatten b) prog)[p.2]!) fuel).2.2 ∧
    (bfsEnumB n (List.range n)
        (qp.map fun p => (slpTabsA (Array.flatten a) (Array.flatten b) prog)[p.1]!)
        (qp.map fun p => (slpTabsA (Array.flatten a) (Array.flatten b) prog)[p.2]!)
        fuel).1.size = 2 ^ k := by
  rw [chunksK_eq, chunksK_eq] at h
  have := enum_aux hw _ _ prog qp k fuel d RL h
  rwa [Array.toArray_toList, Array.toArray_toList] at this

end CFSG.KC.LQT.PPE

end
