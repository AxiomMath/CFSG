module

public import CFSG.Certificates.Kernel.Seitz77B45Sound
public import Mathlib.Data.List.Perm.Basic
public import Mathlib.Data.List.Nodup

public section

namespace CFSG.KC.SeitzB45

open Certificates.Seitz77CaseB45

structure GT (mt : Nat → Nat → Nat) (inv : Nat → Nat) : Prop where
  cl : ∀ i j, i < 256 → j < 256 → mt i j < 256
  as : ∀ i j k, i < 256 → j < 256 → k < 256 → mt (mt i j) k = mt i (mt j k)
  e0l : ∀ x, x < 256 → mt 0 x = x
  e0r : ∀ x, x < 256 → mt x 0 = x
  il : ∀ x, x < 256 → inv x < 256
  ir : ∀ x, x < 256 → mt x (inv x) = 0
  ii : ∀ x, x < 256 → mt (inv x) x = 0

@[expose] def cjW (mt : Nat → Nat → Nat) (inv : Nat → Nat) (g h : Nat) (w : WEl) : WEl :=
  if w.2.2 then (mt (mt g w.1) (inv h), mt (mt h w.2.1) (inv g), true)
  else (mt (mt g w.1) (inv g), mt (mt h w.2.1) (inv h), false)

@[expose] def VW (w : WEl) : Prop := w.1 < 256 ∧ w.2.1 < 256

namespace GT

variable {mt : Nat → Nat → Nat} {inv : Nat → Nat} (G : GT mt inv)
include G

theorem canc1 {x z : Nat} (hx : x < 256) (hz : z < 256) : mt x (mt (inv x) z) = z := by
  rw [← G.as _ _ _ hx (G.il _ hx) hz, G.ir _ hx, G.e0l _ hz]

theorem canc2 {x z : Nat} (hx : x < 256) (hz : z < 256) : mt (inv x) (mt x z) = z := by
  rw [← G.as _ _ _ (G.il _ hx) hx hz, G.ii _ hx, G.e0l _ hz]

theorem inv_inv {x : Nat} (hx : x < 256) : inv (inv x) = x := by
  have h1 := G.il _ hx
  have h2 := G.il _ h1
  calc inv (inv x) = mt (inv (inv x)) (mt (inv x) x) := by rw [G.ii _ hx, G.e0r _ h2]
    _ = mt (mt (inv (inv x)) (inv x)) x := (G.as _ _ _ h2 h1 hx).symm
    _ = x := by rw [G.ii _ h1, G.e0l _ hx]

theorem cj_inv {g a : Nat} (hg : g < 256) (ha : a < 256) :
    cj mt inv (inv g) (cj mt inv g a) = a := by
  have := G.il _ hg
  unfold cj
  simp [G.inv_inv hg, G.as, G.cl, G.il, G.canc1, G.canc2, G.ir, G.ii, G.e0l, G.e0r, hg, ha, this]

theorem cj_lt {g a : Nat} (hg : g < 256) (ha : a < 256) : cj mt inv g a < 256 :=
  G.cl _ _ (G.cl _ _ hg ha) (G.il _ hg)

theorem cj_zero {g : Nat} (hg : g < 256) : cj mt inv g 0 = 0 := by
  unfold cj
  rw [G.e0r _ hg, G.ir _ hg]

theorem cj_beq_zero {g a : Nat} (hg : g < 256) (ha : a < 256) :
    (cj mt inv g a == 0) = (a == 0) := by
  by_cases h : a = 0
  · subst h
    rw [G.cj_zero hg]
  · have : cj mt inv g a ≠ 0 := fun e => h (by
      rw [← G.cj_inv hg ha, e, G.cj_zero (G.il _ hg)])
    simp [h, this]

theorem cjW_valid {g h : Nat} (hg : g < 256) (hh : h < 256) {w : WEl} (hw : VW w) :
    VW (cjW mt inv g h w) := by
  obtain ⟨c, d, e⟩ := w
  obtain ⟨hc, hd⟩ := hw
  cases e
  · exact ⟨G.cl _ _ (G.cl _ _ hg hc) (G.il _ hg), G.cl _ _ (G.cl _ _ hh hd) (G.il _ hh)⟩
  · exact ⟨G.cl _ _ (G.cl _ _ hg hc) (G.il _ hh), G.cl _ _ (G.cl _ _ hh hd) (G.il _ hg)⟩

theorem wmul_valid {x y : WEl} (hx : VW x) (hy : VW y) : VW (wmul mt x y) := by
  obtain ⟨c, d, e⟩ := x
  obtain ⟨c', d', e'⟩ := y
  obtain ⟨hc, hd⟩ := hx
  obtain ⟨hc', hd'⟩ := hy
  cases e
  · exact ⟨G.cl _ _ hc hc', G.cl _ _ hd hd'⟩
  · exact ⟨G.cl _ _ hc hd', G.cl _ _ hd hc'⟩

theorem cjW_inv {g h : Nat} (hg : g < 256) (hh : h < 256) {w : WEl} (hw : VW w) :
    cjW mt inv (inv g) (inv h) (cjW mt inv g h w) = w := by
  obtain ⟨c, d, e⟩ := w
  obtain ⟨hc, hd⟩ : c < 256 ∧ d < 256 := hw
  have := G.il _ hg
  have := G.il _ hh
  cases e <;> simp (maxDischargeDepth := 10) [cjW, G.inv_inv hg, G.inv_inv hh, G.as, G.cl, G.il, G.canc1, G.canc2, G.ir,
    G.ii, G.e0l, G.e0r, hg, hh, hc, hd, *]

theorem cjW_mul {g h : Nat} (hg : g < 256) (hh : h < 256) {x y : WEl} (hx : VW x) (hy : VW y) :
    cjW mt inv g h (wmul mt x y) = wmul mt (cjW mt inv g h x) (cjW mt inv g h y) := by
  obtain ⟨c, d, e⟩ := x
  obtain ⟨c', d', e'⟩ := y
  obtain ⟨hc, hd⟩ : c < 256 ∧ d < 256 := hx
  obtain ⟨hc', hd'⟩ : c' < 256 ∧ d' < 256 := hy
  have := G.il _ hg
  have := G.il _ hh
  cases e <;> cases e' <;> simp (maxDischargeDepth := 10) [cjW, wmul, G.as, G.cl, G.il, G.canc1, G.canc2, G.ir, G.ii,
    G.e0l, G.e0r, *]

theorem cjW_one {g h : Nat} (hg : g < 256) (hh : h < 256) : cjW mt inv g h wone = wone := by
  simp [cjW, wone, G.e0r _ hg, G.e0r _ hh, G.ir _ hg, G.ir _ hh]

theorem cjW_beq {g h : Nat} (hg : g < 256) (hh : h < 256) {x y : WEl} (hx : VW x) (hy : VW y) :
    (cjW mt inv g h x == cjW mt inv g h y) = (x == y) := by
  by_cases e : x = y
  · subst e
    simp
  · have : cjW mt inv g h x ≠ cjW mt inv g h y := fun e' => e (by
      rw [← G.cjW_inv hg hh hx, e', G.cjW_inv hg hh hy])
    simp [e, this]

theorem wOrd_cjW {g h : Nat} (hg : g < 256) (hh : h < 256) {w : WEl} (hw : VW w) :
    wOrd mt (cjW mt inv g h w) = wOrd mt w := by
  have v1 := G.wmul_valid hw hw
  have v2 := G.wmul_valid v1 v1
  have v3 := G.wmul_valid v2 v2
  have v4 := G.wmul_valid v3 v3
  have vo : VW wone := ⟨by decide, by decide⟩
  have b1 : ∀ {x : WEl}, VW x → (cjW mt inv g h x == wone) = (x == wone) := fun hx => by
    have := G.cjW_beq hg hh hx vo
    rwa [G.cjW_one hg hh] at this
  dsimp only [wOrd]
  rw [← G.cjW_mul hg hh hw hw, ← G.cjW_mul hg hh v1 v1, ← G.cjW_mul hg hh v2 v2,
    ← G.cjW_mul hg hh v3 v3, b1 hw, b1 v1, b1 v2, b1 v3, b1 v4]

end GT

theorem getD_blk {f : Nat → List Nat} {p d : Nat} :
    d ∈ ((List.range 4).map f).getD p [] ↔ p < 4 ∧ d ∈ f p := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map]
  by_cases hp : p < 4
  · simp [hp]
  · simp [hp]

@[expose] def inCen (mt : Nat → Nat → Nat) (lab : Nat → Nat) (m a b : Nat) (w : WEl) : Prop :=
  w.1 < 256 ∧ w.2.1 < 256 ∧ inM m (lab w.1) (lab w.2.1) = true ∧
    (if w.2.2 then mt a w.1 = mt w.1 b ∧ mt b w.2.1 = mt w.2.1 a
      else mt a w.1 = mt w.1 a ∧ mt b w.2.1 = mt w.2.1 b)

theorem mem_cenList {mt : Nat → Nat → Nat} {lab : Nat → Nat} {m a b : Nat}
    (hlab : ∀ i, i < 256 → lab i < 4) {w : WEl} :
    w ∈ cenList mt lab m a b ↔ inCen mt lab m a b w := by
  obtain ⟨c, d, e⟩ := w
  unfold cenList cenBase cenSwap byLabel inCen
  cases e
  · simp only [List.mem_append, List.mem_flatMap, List.mem_map, getD_blk, List.mem_filter,
      List.mem_range, beq_iff_eq, Prod.mk.injEq, Bool.false_eq_true, Bool.true_eq_false,
      and_false, and_true, exists_false, or_false, false_or, if_false]
    constructor
    · rintro ⟨c', ⟨hc, hac⟩, d', ⟨-, ⟨hd, hbd⟩, hm⟩, rfl, rfl⟩
      exact ⟨hc, hd, hm, hac, hbd⟩
    · rintro ⟨hc, hd, hm, hac, hbd⟩
      exact ⟨c, ⟨hc, hac⟩, d, ⟨hlab c hc, ⟨hd, hbd⟩, hm⟩, rfl, rfl⟩
  · simp only [List.mem_append, List.mem_flatMap, List.mem_map, getD_blk, List.mem_filter,
      List.mem_range, beq_iff_eq, Prod.mk.injEq, Bool.false_eq_true, Bool.true_eq_false,
      and_false, and_true, exists_false, or_false, false_or, if_true]
    constructor
    · rintro ⟨c', ⟨hc, hac⟩, d', ⟨-, ⟨hd, hbd⟩, hm⟩, rfl, rfl⟩
      exact ⟨hc, hd, hm, hac, hbd⟩
    · rintro ⟨hc, hd, hm, hac, hbd⟩
      exact ⟨c, ⟨hc, hac⟩, d, ⟨hlab c hc, ⟨hd, hbd⟩, hm⟩, rfl, rfl⟩

theorem nodup_blk {f : Nat → List Nat} (hf : ∀ q, (f q).Nodup) (p : Nat) :
    (((List.range 4).map f).getD p []).Nodup := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map]
  by_cases hp : p < 4
  · simp [hp, hf]
  · simp [hp]

theorem nodup_part {F : List Nat} (hF : F.Nodup) (B : Nat → List Nat) (hB : ∀ c, (B c).Nodup)
    (e : Bool) : (F.flatMap fun c => (B c).map fun d => ((c, d, e) : WEl)).Nodup := by
  rw [List.nodup_flatMap]
  refine ⟨fun c _ => (hB c).map fun d d' h => by simpa using h, ?_⟩
  refine hF.pairwise_of_forall_ne fun c _ c' _ hne => ?_
  intro w hw hw'
  obtain ⟨d, -, rfl⟩ := List.mem_map.1 hw
  obtain ⟨d', -, h⟩ := List.mem_map.1 hw'
  exact hne (congrArg Prod.fst h).symm

theorem nodup_cenList (mt : Nat → Nat → Nat) (lab : Nat → Nat) (m a b : Nat) :
    (cenList mt lab m a b).Nodup := by
  unfold cenList cenBase cenSwap byLabel
  refine List.Nodup.append (nodup_part (List.nodup_range.filter _) _
    (fun c => nodup_blk (fun q => (List.nodup_range.filter _).filter _) _) false)
    (nodup_part (List.nodup_range.filter _) _
      (fun c => nodup_blk (fun q => (List.nodup_range.filter _).filter _) _) true) ?_
  intro w hw hw'
  obtain ⟨c, -, h1⟩ := List.mem_flatMap.1 hw
  obtain ⟨c', -, h2⟩ := List.mem_flatMap.1 hw'
  obtain ⟨d, -, rfl⟩ := List.mem_map.1 h1
  obtain ⟨d', -, h⟩ := List.mem_map.1 h2
  simp at h

section Conj

variable {mt : Nat → Nat → Nat} {inv : Nat → Nat} {lab : Nat → Nat} (G : GT mt inv)
  (hlab : ∀ i, i < 256 → lab i < 4)
  (hL : ∀ g h c, g < 256 → h < 256 → c < 256 → lab g = 0 → lab h = 0 →
    lab (mt (mt g c) (inv h)) = lab c)
include G hlab hL

theorem inCen_cjW {m a b g h : Nat} (ha : a < 256) (hb : b < 256) (hg : g < 256)
    (hh : h < 256) (hg0 : lab g = 0) (hh0 : lab h = 0) {w : WEl}
    (hw : inCen mt lab m a b w) :
    inCen mt lab m (cj mt inv g a) (cj mt inv h b) (cjW mt inv g h w) := by
  obtain ⟨c, d, e⟩ := w
  obtain ⟨hc, hd, hm, hcd⟩ : c < 256 ∧ d < 256 ∧ inM m (lab c) (lab d) = true ∧
      (if e then mt a c = mt c b ∧ mt b d = mt d a else mt a c = mt c a ∧ mt b d = mt d b) := hw
  have hgi := G.il _ hg
  have hhi := G.il _ hh
  refine ⟨(G.cjW_valid hg hh (w := (c, d, e)) ⟨hc, hd⟩).1,
    (G.cjW_valid hg hh (w := (c, d, e)) ⟨hc, hd⟩).2, ?_, ?_⟩
  · cases e <;> simpa [cjW, hL _ _ _ hg hh hc hg0 hh0, hL _ _ _ hh hg hd hh0 hg0,
      hL _ _ _ hg hg hc hg0 hg0, hL _ _ _ hh hh hd hh0 hh0] using hm
  · cases e
    · simp only [Bool.false_eq_true, if_false] at hcd ⊢
      obtain ⟨h1, h2⟩ := hcd
      have e1 := congrArg (fun t => mt g (mt t (inv g))) h1
      have e2 := congrArg (fun t => mt h (mt t (inv h))) h2
      simp only [cjW, cj, Bool.false_eq_true, if_false] at e1 e2 ⊢
      simp (maxDischargeDepth := 10) only [G.as, G.cl, G.il, G.canc1, G.canc2, hg, hh, ha, hb,
        hc, hd, hgi, hhi] at e1 e2 ⊢
      exact ⟨e1, e2⟩
    · simp only [if_true] at hcd ⊢
      obtain ⟨h1, h2⟩ := hcd
      have e1 := congrArg (fun t => mt g (mt t (inv h))) h1
      have e2 := congrArg (fun t => mt h (mt t (inv g))) h2
      simp only [cjW, cj, if_true] at e1 e2 ⊢
      simp (maxDischargeDepth := 10) only [G.as, G.cl, G.il, G.canc1, G.canc2, hg, hh, ha, hb,
        hc, hd, hgi, hhi] at e1 e2 ⊢
      exact ⟨e1, e2⟩

theorem cenList_perm (hLi : ∀ g, g < 256 → lab g = 0 → lab (inv g) = 0) {m a b g h : Nat}
    (ha : a < 256) (hb : b < 256) (hg : g < 256) (hh : h < 256) (hg0 : lab g = 0)
    (hh0 : lab h = 0) :
    (cenList mt lab m (cj mt inv g a) (cj mt inv h b)).Perm
      ((cenList mt lab m a b).map (cjW mt inv g h)) := by
  have hv : ∀ w ∈ cenList mt lab m a b, VW w := fun w hw =>
    ⟨((mem_cenList hlab).1 hw).1, ((mem_cenList hlab).1 hw).2.1⟩
  have hnd : ((cenList mt lab m a b).map (cjW mt inv g h)).Nodup :=
    (nodup_cenList mt lab m a b).map_on fun x hx y hy e => by
      rw [← G.cjW_inv hg hh (hv x hx), e, G.cjW_inv hg hh (hv y hy)]
  refine (List.perm_ext_iff_of_nodup (nodup_cenList _ _ _ _ _) hnd).2 fun w => ?_
  constructor
  · intro hw
    have hw' := (mem_cenList hlab).1 hw
    have hgi := G.il _ hg
    have hhi := G.il _ hh
    refine List.mem_map.2 ⟨cjW mt inv (inv g) (inv h) w, (mem_cenList hlab).2 ?_, ?_⟩
    · have := inCen_cjW G hlab hL (G.cj_lt hg ha) (G.cj_lt hh hb) hgi hhi
        (hLi g hg hg0) (hLi h hh hh0) hw'
      rwa [G.cj_inv hg ha, G.cj_inv hh hb] at this
    · have := G.cjW_inv hgi hhi (w := w) ⟨hw'.1, hw'.2.1⟩
      rwa [G.inv_inv hg, G.inv_inv hh] at this
  · intro hw
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hw
    exact (mem_cenList hlab).2 (inCen_cjW G hlab hL ha hb hg hh hg0 hh0 ((mem_cenList hlab).1 hx))

end Conj

theorem ordStats_perm {mt : Nat → Nat → Nat} {L L' : List WEl} (hp : L.Perm L') :
    ordStats mt L = ordStats mt L' := by
  unfold ordStats
  have := hp.map (wOrd mt)
  simp only [((this.filter _).length_eq)]

theorem zOf_perm {mt : Nat → Nat → Nat} {L L' : List WEl} (hp : L.Perm L') :
    zOf mt L = zOf mt L' := by
  unfold zOf
  have e : ∀ w, (L.all fun v => wmul mt w v == wmul mt v w) =
      (L'.all fun v => wmul mt w v == wmul mt v w) := fun w => by
    rw [Bool.eq_iff_iff, List.all_eq_true, List.all_eq_true]
    exact ⟨fun h v hv => h v (hp.mem_iff.2 hv), fun h v hv => h v (hp.mem_iff.1 hv)⟩
  simp only [e]
  exact (hp.filter _).length_eq

theorem stats_map {mt : Nat → Nat → Nat} {inv : Nat → Nat} (G : GT mt inv) {g h : Nat}
    (hg : g < 256) (hh : h < 256) {L : List WEl} (hv : ∀ w ∈ L, VW w) :
    ordStats mt (L.map (cjW mt inv g h)) = ordStats mt L ∧
      zOf mt (L.map (cjW mt inv g h)) = zOf mt L := by
  constructor
  · unfold ordStats
    rw [List.map_map, List.map_congr_left (f := wOrd mt ∘ cjW mt inv g h) (g := wOrd mt)
      fun w hw => G.wOrd_cjW hg hh (hv w hw)]
  · unfold zOf
    rw [List.filter_map, List.length_map]
    congr 1
    refine List.filter_congr fun x hx => ?_
    simp only [Function.comp_apply, List.all_map]
    rw [Bool.eq_iff_iff, List.all_eq_true, List.all_eq_true]
    refine forall_congr' fun v => imp_congr_right fun hvL => ?_
    simp only [Function.comp_apply]
    rw [← G.cjW_mul hg hh (hv x hx) (hv v hvL), ← G.cjW_mul hg hh (hv v hvL) (hv x hx),
      G.cjW_beq hg hh (G.wmul_valid (hv x hx) (hv v hvL)) (G.wmul_valid (hv v hvL) (hv x hx))]

theorem condF_cj {mt : Nat → Nat → Nat} {inv : Nat → Nat} {lab : Nat → Nat} (G : GT mt inv)
    (hlab : ∀ i, i < 256 → lab i < 4)
    (hL : ∀ g h c, g < 256 → h < 256 → c < 256 → lab g = 0 → lab h = 0 →
      lab (mt (mt g c) (inv h)) = lab c)
    (hLi : ∀ g, g < 256 → lab g = 0 → lab (inv g) = 0)
    {m len : Nat} {os : List Nat} {zt a b g h : Nat} (ha : a < 256) (hb : b < 256)
    (hg : g < 256) (hh : h < 256) (hg0 : lab g = 0) (hh0 : lab h = 0) :
    condF mt lab m len os zt (cj mt inv g a) (cj mt inv h b) = condF mt lab m len os zt a b := by
  have hp := cenList_perm G hlab hL hLi (m := m) ha hb hg hh hg0 hh0
  have hv : ∀ w ∈ cenList mt lab m a b, VW w := fun w hw =>
    ⟨((mem_cenList hlab).1 hw).1, ((mem_cenList hlab).1 hw).2.1⟩
  obtain ⟨hs1, hs2⟩ := stats_map G hg hh hv
  unfold condF differs
  rw [G.cj_beq_zero hg ha, G.cj_beq_zero hh hb, hp.length_eq, List.length_map,
    ordStats_perm hp, zOf_perm hp, hs1, hs2]
  unfold cj
  rw [hL _ _ _ hg hg ha hg0 hg0, hL _ _ _ hh hh hb hh0 hh0]

theorem sliceO_spec {mt : Nat → Nat → Nat} {lab cr : Nat → Nat} {m len : Nat} {os : List Nat}
    {zt : Nat} {ZW : List (List Nat)} {alo ahi blo bhi a b : Nat}
    (h : sliceO mt lab cr m len os zt ZW alo ahi blo bhi = true) (ha : a ∈ invsF mt)
    (hb : b ∈ invsF mt) (hra : inR alo ahi a = true) (hrb : inR blo bhi b = true)
    (hca : cr a = a) (hcb : cr b = b) : condF mt lab m len os zt a b = true := by
  unfold sliceO at h
  rw [List.all_eq_true] at h
  have h1 := h a ha
  rw [hra, hca, beq_self_eq_true, Bool.not_true, Bool.false_or, Bool.false_or,
    List.all_eq_true] at h1
  have h2 := h1 b hb
  rw [hrb, hcb, beq_self_eq_true, Bool.not_true, Bool.false_or, Bool.false_or] at h2
  exact condF_of_L h2

theorem fb6_of_orb {mt : Nat → Nat → Nat} {inv lab cr cg : Nat → Nat} {ladd : Nat → Nat → Nat}
    {MS : List Nat} {ST SL ZW : List (List Nat)} (G : GT mt inv)
    (hlab : ∀ i, i < 256 → lab i < 4)
    (hL : ∀ g h c, g < 256 → h < 256 → c < 256 → lab g = 0 → lab h = 0 →
      lab (mt (mt g c) (inv h)) = lab c)
    (hLi : ∀ g, g < 256 → lab g = 0 → lab (inv g) = 0)
    (horb : orbOK mt inv lab cr cg = true) (hMS : MS.length = 15)
    (hadm : ∀ c < 16, admOK ladd MS (4096 * c) 4096 = true)
    (hst : ∀ i < 15, statsF mt lab (MS.getD i 0) ((ST.getD i []).getD 0 0)
      [(ST.getD i []).getD 1 0, (ST.getD i []).getD 2 0, (ST.getD i []).getD 3 0,
        (ST.getD i []).getD 4 0] ((ST.getD i []).getD 5 0) = true)
    (hcov : coverO mt cr 15 SL = true)
    (hsl : ∀ c < SL.length, sliceO mt lab cr (MS.getD ((SL.getD c []).getD 0 0) 0)
      ((ST.getD ((SL.getD c []).getD 0 0) []).getD 0 0)
      [(ST.getD ((SL.getD c []).getD 0 0) []).getD 1 0, (ST.getD ((SL.getD c []).getD 0 0) []).getD 2 0,
        (ST.getD ((SL.getD c []).getD 0 0) []).getD 3 0,
        (ST.getD ((SL.getD c []).getD 0 0) []).getD 4 0]
      ((ST.getD ((SL.getD c []).getD 0 0) []).getD 5 0) ZW
      ((SL.getD c []).getD 1 0) ((SL.getD c []).getD 2 0) ((SL.getD c []).getD 3 0)
      ((SL.getD c []).getD 4 0) = true) :
    fb6Check mt lab ladd = true := by
  have ho : ∀ a ∈ invsF mt, cr a ∈ invsF mt ∧ cr (cr a) = cr a ∧ cg a < 256 ∧ lab (cg a) = 0 ∧
      cj mt inv (cg a) (cr a) = a := by
    intro a ha
    have h := List.all_eq_true.1 horb a ha
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
    obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
    refine ⟨?_, h5, h2, h3, h6⟩
    unfold invsF
    simp [h1, h4]
  unfold fb6Check
  rw [List.all_eq_true]
  intro m hm
  have hm' := List.mem_range.1 hm
  by_cases hin : m ∈ MS
  · obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hin
    have hgi : MS.getD i 0 = MS[i] := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]
    rw [hMS] at hi
    have hs := hst i hi
    unfold statsF at hs
    simp only [Bool.and_eq_true, beq_iff_eq] at hs
    obtain ⟨⟨h1, h2⟩, h3⟩ := hs
    rw [hgi] at h1 h2 h3
    rw [Bool.or_eq_true]
    right
    unfold mainOK mainAux
    rw [h1, h2, h3, List.all_eq_true]
    intro a ha
    rw [List.all_eq_true]
    intro b hb
    obtain ⟨hra, hrra, hga, hga0, hca⟩ := ho a ha
    obtain ⟨hrb, hrrb, hgb, hgb0, hcb⟩ := ho b hb
    have hk : condF mt lab MS[i] ((ST.getD i []).getD 0 0)
        [(ST.getD i []).getD 1 0, (ST.getD i []).getD 2 0, (ST.getD i []).getD 3 0,
          (ST.getD i []).getD 4 0] ((ST.getD i []).getD 5 0) (cr a) (cr b) = true := by
      have hc := hcov
      unfold coverO at hc
      simp only [List.all_eq_true, List.mem_range] at hc
      have hc1 := hc i hi (cr a) hra
      rw [hrra, beq_self_eq_true, Bool.not_true, Bool.false_or, List.all_eq_true] at hc1
      have hc2 := hc1 (cr b) hrb
      rw [hrrb, beq_self_eq_true, Bool.not_true, Bool.false_or] at hc2
      obtain ⟨s, hsm, hcs⟩ := List.any_eq_true.1 hc2
      obtain ⟨c, hcl, rfl⟩ := List.getElem_of_mem hsm
      have hgc : SL.getD c [] = SL[c] := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hcl, Option.getD_some]
      unfold coversF at hcs
      simp only [Bool.and_eq_true, beq_iff_eq] at hcs
      obtain ⟨⟨h0, hr1⟩, hr2⟩ := hcs
      have hk := hsl c hcl
      rw [hgc, h0, hgi] at hk
      exact sliceO_spec hk hra hrb hr1 hr2 hrra hrrb
    have hlt : ∀ x ∈ invsF mt, x < 256 := fun x hx => by
      unfold invsF at hx
      exact List.mem_range.1 (List.mem_filter.1 hx).1
    rw [← condF_cj G hlab hL hLi (hlt _ hra) (hlt _ hrb) hga hgb hga0 hgb0, hca, hcb] at hk
    unfold condF at hk
    exact hk
  · have hc := hadm (m / 4096) (by omega)
    unfold admOK at hc
    rw [List.all_eq_true] at hc
    have hk := hc m (List.mem_range'.2 ⟨m % 4096, by omega, by omega⟩)
    rw [Bool.or_eq_true] at hk
    rcases hk with hk | hk
    · exact absurd (List.contains_iff_mem.1 hk) hin
    · rw [hk, Bool.true_or]

end CFSG.KC.SeitzB45

end
