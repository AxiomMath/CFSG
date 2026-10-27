module

public import CFSG.Combinatorics.QuadrangleGraph
import CFSG.Combinatorics.QuadrangleGraphCount
import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.Tactic.Linarith.Frontend

public section

namespace CFSG.Combinatorics.QuadrangleGraph

variable {α : Type*}

@[expose] def FixesLinesThrough (adj : α → α → Prop) (f : α → α) (a : α) : Prop :=
  ∀ y, adj a y → adj (f y) y

namespace IsQuadrangle

variable [Fintype α] {adj : α → α → Prop} {f : α → α}

theorem fixesLinesThrough_of_not_adj (h : IsQuadrangle adj)
    (hf : ∀ x y, adj (f x) (f y) ↔ adj x y) {a q : α} (haq : ¬ adj a q) (hfa : f a = a)
    (hfq : f q = q) (ha : FixesLinesThrough adj f a) : FixesLinesThrough adj f q := by
  classical
  intro y hqy
  by_cases hyq : y = q
  · subst y
    rw [hfq]
    exact h.refl q
  · obtain ⟨xl, hxlq, hxly, haxl⟩ := h.meets a (Ne.symm hyq) hqy
    have hqxl : adj q xl := h.symm hxlq
    have hxl_ne_a : xl ≠ a := fun e => haq (e ▸ hxlq)
    have hxl_ne_q : xl ≠ q := fun e => haq (e ▸ haxl)
    have hfxl : f xl = xl := by
      have hz : ¬ (adj q a ∧ adj q xl) := fun hqa => haq (h.symm hqa.1)
      have hfa' : adj (f xl) a := by
        have h1 : adj (f a) (f xl) := (hf a xl).2 haxl
        rw [hfa] at h1
        exact h.symm h1
      have hfx : adj (f xl) xl := ha xl haxl
      have hfq' : adj q (f xl) := by
        have h1 : adj (f q) (f xl) := (hf q xl).2 hqxl
        rw [hfq] at h1
        exact h1
      exact (h.unique_adj (Ne.symm hxl_ne_a) haxl hz (h.symm haxl) (h.refl xl) hqxl
        hfa' hfx hfq').symm
    have hfy_xl : adj (f y) xl := by
      have h1 : adj (f y) (f xl) := (hf y xl).2 (h.symm hxly)
      rw [hfxl] at h1
      exact h1
    have hfy_q : adj (f y) q := by
      have h1 : adj (f y) (f q) := (hf y q).2 (h.symm hqy)
      rw [hfq] at h1
      exact h1
    exact h.clique hxl_ne_q hxlq hfy_xl hfy_q (h.symm hxly) (h.symm hqy)

theorem apply_eq_of_mem_perp2 (h : IsQuadrangle adj)
    (hf : ∀ x y, adj (f x) (f y) ↔ adj x y) {a q : α} (haq : ¬ adj a q) (hfa : f a = a)
    (hfq : f q = q) (ha : FixesLinesThrough adj f a) {w : α} (hw : w ∈ perp2 adj a q) :
    f w = w := by
  have hwa : adj w a := (mem_perp2.1 hw).1
  have hwq : adj w q := (mem_perp2.1 hw).2
  have hfwa : adj (f w) a := by
    have h1 : adj (f a) (f w) := (hf a w).2 (h.symm hwa)
    rw [hfa] at h1
    exact h.symm h1
  have hfwq : adj (f w) q := by
    have h1 : adj (f q) (f w) := (hf q w).2 (h.symm hwq)
    rw [hfq] at h1
    exact h.symm h1
  have hfww : adj (f w) w :=
    (fixesLinesThrough_of_not_adj h hf haq hfa hfq ha) w (h.symm hwq)
  by_contra hne
  exact (h.not_adj_of_not_adj haq hfwa hfwq hwa hwq hne) hfww

theorem fixesLinesThrough_of_not_adj_of_apply_eq (h : IsQuadrangle adj)
    (hf : ∀ x y, adj (f x) (f y) ↔ adj x y) {w x : α} (hfw : f w = w)
    (hw : FixesLinesThrough adj f w) (hwx : ¬ adj w x) (hfx : f x = x) :
    FixesLinesThrough adj f x := by
  intro y hxy
  by_cases hyx : y = x
  · subst y
    rw [hfx]
    exact h.refl x
  · obtain ⟨p, hpx, hpy, hwp⟩ := h.meets w (Ne.symm hyx) hxy
    have hpx' : p ≠ x := fun e => hwx (e ▸ hwp)
    have hfp : f p = p := by
      have hz : ¬ (adj w x ∧ adj w p) := fun hp => hwx hp.1
      have hfp_x : adj (f p) x := by
        have h1 : adj (f p) (f x) := (hf p x).2 hpx
        rw [hfx] at h1
        exact h1
      have hfp_p : adj (f p) p := hw p hwp
      have hw_fp : adj w (f p) := by
        have h1 : adj (f w) (f p) := (hf w p).2 hwp
        rw [hfw] at h1
        exact h1
      exact (h.unique_adj (Ne.symm hpx') (h.symm hpx) hz hpx (h.refl p) hwp
        hfp_x hfp_p hw_fp).symm
    have hfy_x : adj (f y) x := by
      have h1 : adj (f y) (f x) := (hf y x).2 (h.symm hxy)
      rw [hfx] at h1
      exact h1
    have hfy_p : adj (f y) p := by
      have h1 : adj (f y) (f p) := (hf y p).2 (h.symm hpy)
      rw [hfp] at h1
      exact h1
    exact h.clique (Ne.symm hpx') (h.symm hpx) hfy_x hfy_p (h.symm hxy) (h.symm hpy)

private theorem adj_of_mem_perp2 (h : IsQuadrangle adj) {a b u v : α} (hab : a ≠ b)
    (hadj : adj a b) (hu : u ∈ perp2 adj a b) (hv : v ∈ perp2 adj a b) :
    adj u v :=
  h.clique hab hadj (mem_perp2.1 hu).1 (mem_perp2.1 hu).2
    (mem_perp2.1 hv).1 (mem_perp2.1 hv).2

private theorem mem_perp2_of_adj_of_mem_perp2 (h : IsQuadrangle adj) {a b u v w : α}
    (hab : a ≠ b) (hadj : adj a b) (hu : u ∈ perp2 adj a b) (hv : v ∈ perp2 adj a b)
    (huv : u ≠ v) (hwu : adj w u) (hwv : adj w v) : w ∈ perp2 adj a b := by
  have huv' : adj u v := adj_of_mem_perp2 h hab hadj hu hv
  exact mem_perp2.2
    ⟨h.clique huv huv' hwu hwv (h.symm (mem_perp2.1 hu).1) (h.symm (mem_perp2.1 hv).1),
      h.clique huv huv' hwu hwv (h.symm (mem_perp2.1 hu).2) (h.symm (mem_perp2.1 hv).2)⟩

private theorem existsUnique_adj_of_disjoint_perp2 (h : IsQuadrangle adj) {a b u v p : α}
    (huv : u ≠ v) (hadj' : adj u v)
    (hdisj : Disjoint (perp2 adj a b) (perp2 adj u v)) (hp : p ∈ perp2 adj a b) :
    ∃! z, z ∈ perp2 adj u v ∧ adj p z := by
  obtain ⟨z, hzu, hzv, hpz⟩ := h.meets p huv hadj'
  refine ⟨z, ⟨mem_perp2.2 ⟨hzu, hzv⟩, hpz⟩, ?_⟩
  rintro z' ⟨hz', hpz'⟩
  have hz'u : adj z' u := (mem_perp2.1 hz').1
  have hz'v : adj z' v := (mem_perp2.1 hz').2
  by_contra hne
  have hznot : ¬ (adj p u ∧ adj p v) := fun hpu =>
    (Finset.disjoint_left.1 hdisj) hp (mem_perp2.2 hpu)
  exact hne (h.unique_adj (x := u) (y := v) (z := p) (w := z) (w' := z')
    huv hadj' hznot hzu hzv hpz hz'u hz'v hpz').symm

private theorem maps_perp2_of_fixesLinesThrough (h : IsQuadrangle adj)
    (hf : ∀ x y, adj (f x) (f y) ↔ adj x y) {a b : α} (hfa : f a = a)
    (ha : FixesLinesThrough adj f a) (hadj : adj a b) {z : α}
    (hz : z ∈ perp2 adj a b) : f z ∈ perp2 adj a b := by
  by_cases hza : z = a
  · subst z
    rw [hfa]
    exact mem_perp2.2 ⟨h.refl a, hadj⟩
  · have haz : adj a z := h.symm (mem_perp2.1 hz).1
    have hfa_z : adj a (f z) := by
      have h1 := (hf a z).2 haz
      rwa [hfa] at h1
    have hz_fz : adj (f z) z := ha z haz
    have hfz_b : adj (f z) b :=
      h.clique (Ne.symm hza) haz (h.symm hfa_z) hz_fz
        (h.symm hadj) (h.symm (mem_perp2.1 hz).2)
    exact mem_perp2.2 ⟨h.symm hfa_z, hfz_b⟩

private theorem apply_eq_of_proj_of_adj (h : IsQuadrangle adj)
    (hf : ∀ x y, adj (f x) (f y) ↔ adj x y) {x q w n : α} (hfx : f x = x)
    (hfw : f w = w) (hfq : f q = q) (hxq : ¬ adj x q) (hqw : q ≠ w)
    (hadjqw : adj q w) (hnq : adj n q) (hnw : adj n w) (hxn : adj x n) : f n = n := by
  have hz : ¬ (adj x q ∧ adj x w) := fun hq => hxq hq.1
  have hfn_q : adj (f n) q := by
    have h1 : adj (f n) (f q) := (hf n q).2 hnq
    rwa [hfq] at h1
  have hfn_w : adj (f n) w := by
    have h1 : adj (f n) (f w) := (hf n w).2 hnw
    rwa [hfw] at h1
  have hfx_n : adj x (f n) := by
    have h1 : adj (f n) (f x) := (hf n x).2 (h.symm hxn)
    rw [hfx] at h1
    exact h.symm h1
  exact (h.unique_adj (x := q) (y := w) (z := x) (w := n) (w' := f n)
    hqw hadjqw hz hnq hnw hxn hfn_q hfn_w hfx_n).symm

private theorem card_fixed_filter_le_of_disjoint [DecidableEq α] (h : IsQuadrangle adj)
    (hf : ∀ x y, adj (f x) (f y) ↔ adj x y) {a b u v : α} (hab : a ≠ b) (hadj : adj a b)
    (huv : u ≠ v) (hadj' : adj u v)
    (hdisj : Disjoint (perp2 adj a b) (perp2 adj u v))
    (hNmap : ∀ z ∈ perp2 adj u v, f z ∈ perp2 adj u v) :
    ((perp2 adj a b).filter fun z => f z = z).card ≤
      ((perp2 adj u v).filter fun z => f z = z).card := by
  classical
  let L := perp2 adj a b
  let N := perp2 adj u v
  let proj : α → α := fun p =>
    if hp : p ∈ L then (existsUnique_adj_of_disjoint_perp2 h huv hadj' hdisj hp).choose
    else p
  have hproj_mem : ∀ p ∈ L, proj p ∈ N := by
    intro p hp
    dsimp only [proj]
    rw [dif_pos hp]
    simpa only [N] using
      (existsUnique_adj_of_disjoint_perp2 h huv hadj' hdisj hp).choose_spec.1.1
  have hproj_adj : ∀ p ∈ L, adj p (proj p) := by
    intro p hp
    dsimp only [proj]
    rw [dif_pos hp]
    simpa only [N] using
      (existsUnique_adj_of_disjoint_perp2 h huv hadj' hdisj hp).choose_spec.1.2
  have hproj_fix : ∀ p ∈ L, f p = p → f (proj p) = proj p := by
    intro p hp hfp
    have hyN : proj p ∈ N := hproj_mem p hp
    have hpy : adj p (proj p) := hproj_adj p hp
    have hfyN : f (proj p) ∈ N := hNmap (proj p) hyN
    have hfpy : adj p (f (proj p)) := by
      have h1 : adj (f p) (f (proj p)) := (hf p (proj p)).2 hpy
      rwa [hfp] at h1
    exact (existsUnique_adj_of_disjoint_perp2 h huv hadj' hdisj hp).unique
      ⟨hfyN, hfpy⟩ ⟨hyN, hpy⟩
  have hinj : Set.InjOn proj ((L.filter fun z => f z = z : Finset α) : Set α) := by
    intro p₁ hp₁ p₂ hp₂ heq
    have hp₁L : p₁ ∈ L := (Finset.mem_filter.1 hp₁).1
    have hp₂L : p₂ ∈ L := (Finset.mem_filter.1 hp₂).1
    by_contra hne
    have hyN : proj p₁ ∈ N := hproj_mem p₁ hp₁L
    have h1 : adj p₁ (proj p₁) := hproj_adj p₁ hp₁L
    have h2 : adj p₂ (proj p₂) := hproj_adj p₂ hp₂L
    rw [← heq] at h2
    have hyL : proj p₁ ∈ L :=
      mem_perp2_of_adj_of_mem_perp2 h hab hadj hp₁L hp₂L hne (h.symm h1) (h.symm h2)
    exact (Finset.disjoint_left.1 hdisj) hyL hyN
  exact Finset.card_le_card_of_injOn proj
    (fun p hp => Finset.mem_filter.2
      ⟨hproj_mem p (Finset.mem_filter.1 hp).1,
        hproj_fix p (Finset.mem_filter.1 hp).1 (Finset.mem_filter.1 hp).2⟩)
    hinj

private theorem false_of_mem_two_perp2 (h : IsQuadrangle adj) {a q w₁ w₂ y : α}
    (haq : ¬ adj a q) (hw₁ : w₁ ∈ perp2 adj a q) (hw₂ : w₂ ∈ perp2 adj a q)
    (hwne : w₁ ≠ w₂) (hy₁ : y ∈ perp2 adj q w₁) (hy₂ : y ∈ perp2 adj q w₂)
    (hyq : y ≠ q) : False := by
  have hwnonadj : ¬ adj w₁ w₂ :=
    h.not_adj_of_not_adj haq (mem_perp2.1 hw₁).1 (mem_perp2.1 hw₁).2
      (mem_perp2.1 hw₂).1 (mem_perp2.1 hw₂).2 hwne
  have hyq' : adj y q := (mem_perp2.1 hy₁).1
  exact (h.not_adj_of_not_adj hwnonadj (mem_perp2.1 hy₁).2 (mem_perp2.1 hy₂).2
    (h.symm (mem_perp2.1 hw₁).2) (h.symm (mem_perp2.1 hw₂).2) hyq) hyq'

private theorem not_adj_of_mem_perp2_of_ne (h : IsQuadrangle adj) {a q w₁ w₂ y₁ y₂ : α}
    (haq : ¬ adj a q) (hw₁ : w₁ ∈ perp2 adj a q) (hw₂ : w₂ ∈ perp2 adj a q)
    (hwne : w₁ ≠ w₂) (hy₁ : y₁ ∈ perp2 adj q w₁) (hy₂ : y₂ ∈ perp2 adj q w₂)
    (hy₁q : y₁ ≠ q) (hy₂q : y₂ ≠ q) : ¬ adj y₁ y₂ := by
  intro hadj
  have hy₁₂ : y₁ ≠ y₂ := by
    intro e
    subst y₂
    exact false_of_mem_two_perp2 h haq hw₁ hw₂ hwne hy₁ hy₂ hy₁q
  have hw₁perp : w₁ ∈ perp2 adj a q := hw₁
  have hw₁a : adj w₁ a := (mem_perp2.1 hw₁perp).1
  have hw₁q : adj w₁ q := (mem_perp2.1 hw₁perp).2
  have hqw : q ≠ w₁ := by
    intro e
    rw [← e] at hw₁a
    exact haq (h.symm hw₁a)
  have hqwa : adj q w₁ := h.symm hw₁q
  have hy₂q' : adj y₂ q := (mem_perp2.1 hy₂).1
  have hy₂w₁ : y₂ ∈ perp2 adj q w₁ :=
    mem_perp2_of_adj_of_mem_perp2 h hqw hqwa (h.left_mem_perp2 hqwa) hy₁ (Ne.symm hy₁q)
      hy₂q' (h.symm hadj)
  exact false_of_mem_two_perp2 h haq hw₁ hw₂ hwne hy₂w₁ hy₂ hy₂q

private theorem apply_eq_of_collinear_noncollinear (h : IsQuadrangle adj)
    (hf : ∀ x y, adj (f x) (f y) ↔ adj x y) {y y₁ y₂ : α} (hy₁fix : f y₁ = y₁)
    (hy₁full : FixesLinesThrough adj f y₁) (hy₂fix : f y₂ = y₂)
    (hnon : ¬ adj y₁ y₂) (hy₁ : adj y y₁) (hy₂ : adj y y₂) : f y = y := by
  have hfy₁ : adj (f y) y₁ := by
    have h1 : adj (f y) (f y₁) := (hf y y₁).2 hy₁
    rwa [hy₁fix] at h1
  have hfy₂ : adj (f y) y₂ := by
    have h1 : adj (f y) (f y₂) := (hf y y₂).2 hy₂
    rwa [hy₂fix] at h1
  have hfy : adj (f y) y := hy₁full y (h.symm hy₁)
  by_contra hne
  exact (h.not_adj_of_not_adj hnon hfy₁ hfy₂ hy₁ hy₂ hne) hfy

end IsQuadrangle

namespace IsQuadrangleOfOrder

variable [Fintype α] {adj : α → α → Prop} {s t : ℕ} {f : α → α}

private theorem fixesLinesThrough_of_apply_eq_of_mem_perp2 (h : IsQuadrangleOfOrder adj s t)
    (hst : s < t) (hf : ∀ x y, adj (f x) (f y) ↔ adj x y) {a q x z : α}
    (haq : ¬ adj a q) (hfa : f a = a) (hfq : f q = q) (ha : FixesLinesThrough adj f a)
    (hxa : adj x a) (hxa' : x ≠ a) (hxq : ¬ adj x q) (hfx : f x = x)
    (hxfull : FixesLinesThrough adj f x) (hza : adj z a) (hzq : adj z q) (hfz : f z = z) :
    FixesLinesThrough adj f z := by
  classical
  have hqfull : FixesLinesThrough adj f q :=
    IsQuadrangle.fixesLinesThrough_of_not_adj h.toIsQuadrangle hf haq hfa hfq ha
  by_cases hzx : adj z x
  · have ht1 : 1 ≤ t := Nat.succ_le_of_lt (Nat.lt_of_le_of_lt (Nat.zero_le s) hst)
    have hcard : 1 < (perp2 adj a q).card := by
      rw [h.card_perp haq]
      omega
    obtain ⟨w, hw, hwz⟩ := Finset.exists_mem_ne hcard z
    have hwa : adj w a := (mem_perp2.1 hw).1
    have hwq : adj w q := (mem_perp2.1 hw).2
    have hwfix : f w = w :=
      IsQuadrangle.apply_eq_of_mem_perp2 h.toIsQuadrangle hf haq hfa hfq ha hw
    have hqw : q ≠ w := fun e => haq (e ▸ h.symm hwa)
    have hqwa : adj q w := h.toIsQuadrangle.symm hwq
    obtain ⟨n, hnq, hnw, hxn⟩ := h.toIsQuadrangle.meets x hqw hqwa
    have hfn : f n = n :=
      IsQuadrangle.apply_eq_of_proj_of_adj h.toIsQuadrangle hf hfx hwfix hfq hxq hqw hqwa
        hnq hnw hxn
    have hqn : q ≠ n := fun e => hxq (e ▸ hxn)
    have hnN : n ∈ perp2 adj q w := mem_perp2.2 ⟨hnq, hnw⟩
    have hzN : z ∉ perp2 adj q w := by
      intro hzN
      exact (h.toIsQuadrangle.not_adj_of_not_adj haq hza hzq hwa hwq (Ne.symm hwz))
        (mem_perp2.1 hzN).2
    have hn_a : ¬ adj n a := by
      intro hna
      have hnL : n ∈ perp2 adj a x := mem_perp2.2 ⟨hna, h.toIsQuadrangle.symm hxn⟩
      have hzL : z ∈ perp2 adj a x := mem_perp2.2 ⟨hza, hzx⟩
      have hqnot : ¬ (adj q a ∧ adj q x) := fun hq =>
        haq (h.toIsQuadrangle.symm hq.1)
      have hnz : n = z := h.toIsQuadrangle.unique_adj (x := a) (y := x) (z := q)
        (w := n) (w' := z) (Ne.symm hxa') (h.toIsQuadrangle.symm hxa) hqnot hna
        (h.toIsQuadrangle.symm hxn) (h.toIsQuadrangle.symm hnq) hza hzx
        (h.toIsQuadrangle.symm hzq)
      exact hzN (hnz ▸ hnN)
    have hnfull : FixesLinesThrough adj f n :=
      IsQuadrangle.fixesLinesThrough_of_not_adj_of_apply_eq h.toIsQuadrangle hf hfa ha
        (fun hna => hn_a (h.toIsQuadrangle.symm hna)) hfn
    have hzn : ¬ adj n z := by
      intro hnz
      have hzw : z ∈ perp2 adj q w :=
        IsQuadrangle.mem_perp2_of_adj_of_mem_perp2 h.toIsQuadrangle hqw hqwa
          (h.toIsQuadrangle.left_mem_perp2 hqwa) hnN hqn hzq (h.toIsQuadrangle.symm hnz)
      exact (h.toIsQuadrangle.not_adj_of_not_adj haq hza hzq hwa hwq (Ne.symm hwz))
        (mem_perp2.1 hzw).2
    exact IsQuadrangle.fixesLinesThrough_of_not_adj_of_apply_eq h.toIsQuadrangle hf hfn hnfull
      hzn hfz
  · exact IsQuadrangle.fixesLinesThrough_of_not_adj_of_apply_eq h.toIsQuadrangle hf hfx hxfull
      (fun hxz => hzx (h.toIsQuadrangle.symm hxz)) hfz

private theorem fixesLinesThrough_of_apply_eq (h : IsQuadrangleOfOrder adj s t) (hst : s < t)
    (hf : ∀ x y, adj (f x) (f y) ↔ adj x y) {a q x : α} (haq : ¬ adj a q) (hfa : f a = a)
    (hfq : f q = q) (ha : FixesLinesThrough adj f a) (hxa : adj x a) (hxa' : x ≠ a)
    (hxq : ¬ adj x q) (hfx : f x = x) {z : α} (hfz : f z = z) :
    FixesLinesThrough adj f z := by
  have hqfull : FixesLinesThrough adj f q :=
    IsQuadrangle.fixesLinesThrough_of_not_adj h.toIsQuadrangle hf haq hfa hfq ha
  have hqnotx : ¬ adj q x := fun hqx => hxq (h.toIsQuadrangle.symm hqx)
  have hxfull : FixesLinesThrough adj f x :=
    IsQuadrangle.fixesLinesThrough_of_not_adj_of_apply_eq h.toIsQuadrangle hf hfq hqfull hqnotx
      hfx
  by_cases hza : adj z a
  · by_cases hzq : adj z q
    · exact fixesLinesThrough_of_apply_eq_of_mem_perp2 h hst hf haq hfa hfq ha hxa hxa' hxq
        hfx hxfull hza hzq hfz
    · exact IsQuadrangle.fixesLinesThrough_of_not_adj_of_apply_eq h.toIsQuadrangle hf hfq hqfull
        (fun hqz => hzq (h.toIsQuadrangle.symm hqz)) hfz
  · exact IsQuadrangle.fixesLinesThrough_of_not_adj_of_apply_eq h.toIsQuadrangle hf hfa ha
      (fun haz => hza (h.toIsQuadrangle.symm haz)) hfz

private theorem false_of_fixed_line_count {t s σ : ℕ} (hst : s < t) (hs : 1 ≤ s) (hσ : 1 ≤ σ)
    (h : (1 + t * σ) * t ≤ t * (σ + 1) + (t * s - t)) : False := by
  have htpos : 0 < t := by omega
  have hts : t ≤ t * s := by simpa using Nat.mul_le_mul_left t hs
  have hsub : t * s - t + t = t * s := Nat.sub_add_cancel hts
  have hσpos : 0 < σ := Nat.lt_of_lt_of_le Nat.zero_lt_one hσ
  have h' : t * (1 + t * σ) ≤ t * (σ + s) := by nlinarith [h, hsub]
  have h1 : 1 + t * σ ≤ σ + s := Nat.le_of_mul_le_mul_left h' htpos
  have h2 : s + 1 ≤ t := hst
  have h3 : (s + 1) * σ ≤ t * σ := Nat.mul_le_mul_right σ h2
  have h4 : s * σ + σ ≤ t * σ := by
    rwa [Nat.add_mul, one_mul] at h3
  nlinarith [h1, h4, hσpos]

private theorem line_data_base [DecidableEq α] (h : IsQuadrangleOfOrder adj s t)
    (hf : ∀ x y, adj (f x) (f y) ↔ adj x y) {a q : α} (haq : ¬ adj a q) (hfa : f a = a)
    (hfq : f q = q) (ha : FixesLinesThrough adj f a) {b : α} (hab : a ≠ b) (hbadj : adj a b) :
    ∃ (xl : α) (S : Finset α) (σ : ℕ),
      xl ∈ perp2 adj a b ∧ xl ∈ perp2 adj a q ∧ f xl = xl ∧ 2 ≤ S.card ∧
      S.card = σ + 1 ∧ (S.erase xl).card = σ ∧
      S = (perp2 adj a b).filter (fun y => f y = y) ∧
      ((perp2 adj a q).erase xl).card = t ∧
      (∀ y ∈ perp2 adj a b, adj y q → y = xl) ∧
      (∀ w ∈ (perp2 adj a q).erase xl, Disjoint (perp2 adj a b) (perp2 adj q w)) := by
  classical
  obtain ⟨xl, hxla, hxlb, hqxl⟩ := h.toIsQuadrangle.meets q hab hbadj
  let S : Finset α := (perp2 adj a b).filter fun y => f y = y
  let σ : ℕ := S.card - 1
  let P : Finset α := (perp2 adj a q).erase xl
  have hxlL : xl ∈ perp2 adj a b := mem_perp2.2 ⟨hxla, hxlb⟩
  have hxlperp : xl ∈ perp2 adj a q := mem_perp2.2 ⟨hxla, h.toIsQuadrangle.symm hqxl⟩
  have hxlfix : f xl = xl :=
    IsQuadrangle.apply_eq_of_mem_perp2 h.toIsQuadrangle hf haq hfa hfq ha hxlperp
  have haS : a ∈ S := by
    dsimp only [S]
    rw [Finset.mem_filter]
    exact ⟨mem_perp2.2 ⟨h.toIsQuadrangle.refl a, hbadj⟩, hfa⟩
  have hxlS : xl ∈ S := by
    dsimp only [S]
    rw [Finset.mem_filter]
    exact ⟨hxlL, hxlfix⟩
  have haxl : a ≠ xl := fun e => haq (h.toIsQuadrangle.symm (e ▸ hqxl))
  have hS2 : 2 ≤ S.card := by
    have h1 : 1 < S.card := Finset.one_lt_card.2 ⟨a, haS, xl, hxlS, haxl⟩
    omega
  have hS_card : S.card = σ + 1 := by
    dsimp [σ]
    omega
  have herase : (S.erase xl).card = σ := by
    rw [Finset.card_erase_of_mem hxlS]
  have hPcard : P.card = t := by
    dsimp only [P]
    rw [Finset.card_erase_of_mem hxlperp, h.card_perp haq]
    omega
  have hxl_unique : ∀ y ∈ perp2 adj a b, adj y q → y = xl := by
    intro y hyL hyq
    have hqnot : ¬ (adj q a ∧ adj q b) := fun hq => haq (h.toIsQuadrangle.symm hq.1)
    exact h.toIsQuadrangle.unique_adj (x := a) (y := b) (z := q) (w := y) (w' := xl)
      hab hbadj hqnot (mem_perp2.1 hyL).1 (mem_perp2.1 hyL).2
      (h.toIsQuadrangle.symm hyq) hxla hxlb hqxl
  have hdisj : ∀ w ∈ P, Disjoint (perp2 adj a b) (perp2 adj q w) := by
    intro w hw
    rw [Finset.disjoint_left]
    intro y hyL hyN
    have hwperp : w ∈ perp2 adj a q := (Finset.mem_erase.1 hw).2
    have hwa : adj w a := (mem_perp2.1 hwperp).1
    have hwq : adj w q := (mem_perp2.1 hwperp).2
    have hyq : adj y q := (mem_perp2.1 hyN).1
    have hyw : adj y w := (mem_perp2.1 hyN).2
    have hyxl : y = xl := hxl_unique y hyL hyq
    have hxlw : adj xl w := hyxl ▸ hyw
    have hne : xl ≠ w := Ne.symm (Finset.mem_erase.1 hw).1
    exact (h.toIsQuadrangle.not_adj_of_not_adj haq (mem_perp2.1 hxlperp).1
      (mem_perp2.1 hxlperp).2 hwa hwq hne) hxlw
  exact ⟨xl, S, σ, hxlL, hxlperp, hxlfix, hS2, hS_card, herase, rfl, hPcard,
    hxl_unique, hdisj⟩

private theorem line_data_full [DecidableEq α] (h : IsQuadrangleOfOrder adj s t)
    (hf : ∀ x y, adj (f x) (f y) ↔ adj x y) {a q : α} (haq : ¬ adj a q) (hfa : f a = a)
    (hfq : f q = q) (ha : FixesLinesThrough adj f a) {b : α} (hab : a ≠ b) (hbadj : adj a b)
    {xl : α} {S : Finset α} {σ : ℕ}
    (hS_card : S.card = σ + 1)
    (hS_eq : S = (perp2 adj a b).filter fun y => f y = y)
    (hdisj : ∀ w ∈ (perp2 adj a q).erase xl,
      Disjoint (perp2 adj a b) (perp2 adj q w)) :
    (∀ w ∈ (perp2 adj a q).erase xl, ∀ y ∈ perp2 adj q w, f y ∈ perp2 adj q w) ∧
      (∀ y ∈ perp2 adj a b, f y ∈ perp2 adj a b) ∧
      (∀ w ∈ (perp2 adj a q).erase xl,
        ((perp2 adj q w).filter fun y => f y = y).card = σ + 1) := by
  classical
  have hqfull : FixesLinesThrough adj f q :=
    IsQuadrangle.fixesLinesThrough_of_not_adj h.toIsQuadrangle hf haq hfa hfq ha
  have hNmap : ∀ w ∈ (perp2 adj a q).erase xl, ∀ y ∈ perp2 adj q w, f y ∈ perp2 adj q w := by
    intro w hw y hy
    have hwperp : w ∈ perp2 adj a q := (Finset.mem_erase.1 hw).2
    have hwa : adj w a := (mem_perp2.1 hwperp).1
    have hwq : adj w q := (mem_perp2.1 hwperp).2
    have hqw : q ≠ w := by
      intro e
      rw [← e] at hwa
      exact haq (h.toIsQuadrangle.symm hwa)
    exact IsQuadrangle.maps_perp2_of_fixesLinesThrough h.toIsQuadrangle hf hfq hqfull
      (h.toIsQuadrangle.symm hwq) hy
  have hLmap : ∀ y ∈ perp2 adj a b, f y ∈ perp2 adj a b := fun y hy =>
    IsQuadrangle.maps_perp2_of_fixesLinesThrough h.toIsQuadrangle hf hfa ha hbadj hy
  have hfixN : ∀ w ∈ (perp2 adj a q).erase xl,
      ((perp2 adj q w).filter fun y => f y = y).card = σ + 1 := by
    intro w hw
    have hwperp : w ∈ perp2 adj a q := (Finset.mem_erase.1 hw).2
    have hwq : adj w q := (mem_perp2.1 hwperp).2
    have hqw : q ≠ w := by
      intro e
      have hwa : adj w a := (mem_perp2.1 hwperp).1
      rw [← e] at hwa
      exact haq (h.toIsQuadrangle.symm hwa)
    have hqwa : adj q w := h.toIsQuadrangle.symm hwq
    have hle1 : ((perp2 adj a b).filter fun y => f y = y).card ≤
        ((perp2 adj q w).filter fun y => f y = y).card :=
      IsQuadrangle.card_fixed_filter_le_of_disjoint h.toIsQuadrangle hf hab hbadj hqw hqwa
        (hdisj w hw) (hNmap w hw)
    have hle2 : ((perp2 adj q w).filter fun y => f y = y).card ≤
        ((perp2 adj a b).filter fun y => f y = y).card :=
      IsQuadrangle.card_fixed_filter_le_of_disjoint h.toIsQuadrangle hf hqw hqwa hab hbadj
        (hdisj w hw).symm (fun y hy => hLmap y hy)
    have hEq : ((perp2 adj q w).filter fun y => f y = y).card = σ + 1 := by
      rw [← hS_card, hS_eq]
      exact le_antisymm hle2 hle1
    exact hEq
  exact ⟨hNmap, hLmap, hfixN⟩

private theorem fixed_line_set_card [DecidableEq α] (h : IsQuadrangleOfOrder adj s t)
    {a : α} {q : α} (haq : ¬ adj a q) (hfq : f q = q) {P Y : Finset α} {σ t : ℕ}
    (hPmem : ∀ w, w ∈ P → w ∈ perp2 adj a q) (hPcard : P.card = t)
    (hfixN : ∀ w ∈ P, ((perp2 adj q w).filter fun y => f y = y).card = σ + 1)
    (hY_eq : Y = insert q (P.biUnion fun w =>
      (perp2 adj q w).filter fun y => f y = y ∧ y ≠ q)) :
    Y.card = 1 + t * σ := by
  classical
  have hYterm : ∀ w ∈ P, ((perp2 adj q w).filter fun y => f y = y ∧ y ≠ q).card = σ := by
    intro w hw
    have hwperp : w ∈ perp2 adj a q := hPmem w hw
    have hwq : adj w q := (mem_perp2.1 hwperp).2
    have hqw : adj q w := h.toIsQuadrangle.symm hwq
    have hqN : q ∈ (perp2 adj q w).filter fun y => f y = y := by
      rw [Finset.mem_filter, mem_perp2]
      exact ⟨⟨h.toIsQuadrangle.refl q, hqw⟩, hfq⟩
    have hset : ((perp2 adj q w).filter fun y => f y = y ∧ y ≠ q) =
        ((perp2 adj q w).filter fun y => f y = y).erase q := by
      ext y
      rw [Finset.mem_filter, Finset.mem_erase, Finset.mem_filter]
      tauto
    rw [hset, Finset.card_erase_of_mem hqN, hfixN w hw]
    omega
  have hpd : (P : Set α).PairwiseDisjoint
      (fun w => (perp2 adj q w).filter fun y => f y = y ∧ y ≠ q) := by
    intro w₁ hw₁ w₂ hw₂ hne
    change Disjoint ((perp2 adj q w₁).filter fun y => f y = y ∧ y ≠ q)
      ((perp2 adj q w₂).filter fun y => f y = y ∧ y ≠ q)
    rw [Finset.disjoint_left]
    intro y hy₁ hy₂
    have hy₁' := Finset.mem_filter.1 hy₁
    have hy₂' := Finset.mem_filter.1 hy₂
    have hyN₁ : y ∈ perp2 adj q w₁ := hy₁'.1
    have hyN₂ : y ∈ perp2 adj q w₂ := hy₂'.1
    have hyq : y ≠ q := hy₁'.2.2
    have hw₁perp : w₁ ∈ perp2 adj a q := hPmem w₁ hw₁
    have hw₂perp : w₂ ∈ perp2 adj a q := hPmem w₂ hw₂
    have hwnonadj : ¬ adj w₁ w₂ :=
      h.toIsQuadrangle.not_adj_of_not_adj haq (mem_perp2.1 hw₁perp).1
        (mem_perp2.1 hw₁perp).2 (mem_perp2.1 hw₂perp).1 (mem_perp2.1 hw₂perp).2 hne
    have hyq' : adj y q := (mem_perp2.1 hyN₁).1
    exact (h.toIsQuadrangle.not_adj_of_not_adj hwnonadj (mem_perp2.1 hyN₁).2
      (mem_perp2.1 hyN₂).2 (h.toIsQuadrangle.symm (mem_perp2.1 hw₁perp).2)
      (h.toIsQuadrangle.symm (mem_perp2.1 hw₂perp).2) hyq) hyq'
  have hq_notin : q ∉ P.biUnion fun w =>
      (perp2 adj q w).filter fun y => f y = y ∧ y ≠ q := by
    intro hq
    obtain ⟨w, hw, hqN⟩ := Finset.mem_biUnion.1 hq
    exact (Finset.mem_filter.1 hqN).2.2 rfl
  rw [hY_eq, Finset.card_insert_of_notMem hq_notin, Finset.card_biUnion hpd]
  have hsum : (∑ w ∈ P, ((perp2 adj q w).filter fun y => f y = y ∧ y ≠ q).card) =
      ∑ _w ∈ P, σ := Finset.sum_congr rfl hYterm
  rw [hsum, Finset.sum_const_nat (m := σ) (f := fun _ => σ) (fun _ _ => rfl), hPcard]
  omega

private theorem fixed_line_set_properties [DecidableEq α] (h : IsQuadrangleOfOrder adj s t)
    (hf : ∀ x y, adj (f x) (f y) ↔ adj x y) {a q z b : α} {xl : α}
    (hfq : f q = q) (hab : a ≠ b) (hbadj : adj a b)
    (hzf : f z ≠ z) {P Y : Finset α} (hxlfix : f xl = xl)
    (hxl_unique : ∀ y ∈ perp2 adj a b, adj y q → y = xl)
    (hdisj : ∀ w ∈ P, Disjoint (perp2 adj a b) (perp2 adj q w))
    (hLmap : ∀ y ∈ perp2 adj a b, f y ∈ perp2 adj a b) (hzL : z ∈ perp2 adj a b)
    (hY_eq : Y = insert q (P.biUnion fun w =>
      (perp2 adj q w).filter fun y => f y = y ∧ y ≠ q)) :
    (∀ y ∈ Y, f y = y) ∧ (∀ y ∈ Y, ¬ adj z y) := by
  classical
  have hYfix : ∀ y ∈ Y, f y = y := by
    intro y hy
    rw [hY_eq] at hy
    rcases Finset.mem_insert.1 hy with rfl | hmem
    · exact hfq
    · obtain ⟨w, hw, hyN⟩ := Finset.mem_biUnion.1 hmem
      exact (Finset.mem_filter.1 hyN).2.1
  have hY_opp : ∀ y ∈ Y, ¬ adj z y := by
    intro y hy
    rw [hY_eq] at hy
    rcases Finset.mem_insert.1 hy with rfl | hmem
    · intro hzq
      have hzxl : z = xl := hxl_unique z hzL hzq
      exact hzf (by rw [hzxl]; exact hxlfix)
    · obtain ⟨w, hw, hyN⟩ := Finset.mem_biUnion.1 hmem
      have hyN' := Finset.mem_filter.1 hyN
      have hyfix : f y = y := hyN'.2.1
      have hyperp : y ∈ perp2 adj q w := hyN'.1
      have hyL : y ∉ perp2 adj a b := fun hyL =>
        (Finset.disjoint_left.1 (hdisj w hw)) hyL hyperp
      intro hzy
      have hfz_y : adj (f z) y := by
        have h1 : adj (f z) (f y) := (hf z y).2 hzy
        rwa [hyfix] at h1
      have hzy_not : ¬ (adj y a ∧ adj y b) := fun h => hyL (mem_perp2.2 h)
      exact hzf (h.toIsQuadrangle.unique_adj (x := a) (y := b) (z := y) (w := f z) (w' := z)
        hab hbadj hzy_not (mem_perp2.1 (hLmap z hzL)).1 (mem_perp2.1 (hLmap z hzL)).2
        (h.toIsQuadrangle.symm hfz_y) (mem_perp2.1 hzL).1 (mem_perp2.1 hzL).2
        (h.toIsQuadrangle.symm hzy))
  exact ⟨hYfix, hY_opp⟩

private theorem far_line_data [DecidableEq α] [DecidableRel adj] (h : IsQuadrangleOfOrder adj s t)
    {Y Z : Finset α} {a b z : α} (hzL : z ∈ perp2 adj a b)
    (hZ_eq : Z = (nbhd adj z) \ perp2 adj a b) (hY_opp : ∀ y ∈ Y, ¬ adj z y)
    (hab : a ≠ b) (hbadj : adj a b) :
    (perp2 adj a b ⊆ nbhd adj z) ∧ Z.card = t * s ∧
      (∀ y ∈ Y, (Z.filter fun y' => adj y y').card = t) := by
  classical
  have hLsub : perp2 adj a b ⊆ nbhd adj z := by
    intro y hyL
    rw [mem_nbhd]
    by_cases hyz : y = z
    · rw [hyz]
      exact h.toIsQuadrangle.refl z
    · exact h.toIsQuadrangle.symm
        (IsQuadrangle.adj_of_mem_perp2 h.toIsQuadrangle hab hbadj hyL hzL)
  have hZcard : Z.card = t * s := by
    rw [hZ_eq]
    rw [Finset.card_sdiff_of_subset hLsub, h.card_nbhd z, h.card_line hab hbadj]
    have h1 : (t + 1) * s + 1 = t * s + (s + 1) := by ring
    rw [h1, Nat.add_sub_cancel]
  have hZrow : ∀ y ∈ Y, (Z.filter fun y' => adj y y').card = t := by
    intro y hy
    have hzy : ¬ adj z y := hY_opp y hy
    have hyL : y ∉ perp2 adj a b := fun hyL => hzy (mem_nbhd.1 (hLsub hyL))
    obtain ⟨p, hpa, hpb, hyp⟩ := h.toIsQuadrangle.meets y hab hbadj
    have hpL : p ∈ perp2 adj a b := mem_perp2.2 ⟨hpa, hpb⟩
    have hp_unique : ∀ w ∈ perp2 adj a b, adj w y → w = p := by
      intro w hwL hwy
      have hynot : ¬ (adj y a ∧ adj y b) := fun h => hyL (mem_perp2.2 h)
      exact h.toIsQuadrangle.unique_adj (x := a) (y := b) (z := y) (w := w) (w' := p)
        hab hbadj hynot (mem_perp2.1 hwL).1 (mem_perp2.1 hwL).2
        (h.toIsQuadrangle.symm hwy) hpa hpb hyp
    have hinter : (perp2 adj a b) ∩ (perp2 adj z y) = {p} := by
      ext w
      rw [Finset.mem_inter, Finset.mem_singleton]
      constructor
      · rintro ⟨hwL, hwzy⟩
        exact hp_unique w hwL (mem_perp2.1 hwzy).2
      · intro hwp
        subst w
        exact ⟨hpL, mem_perp2.2
          ⟨h.toIsQuadrangle.symm (mem_nbhd.1 (hLsub hpL)), h.toIsQuadrangle.symm hyp⟩⟩
    have hset : Z.filter (fun y' => adj y y') = (perp2 adj z y) \ perp2 adj a b := by
      ext w
      rw [hZ_eq]
      simp only [Finset.mem_filter, Finset.mem_sdiff, mem_nbhd, mem_perp2]
      constructor
      · rintro ⟨⟨hzw, hwL⟩, hyw⟩
        exact ⟨⟨h.toIsQuadrangle.symm hzw, h.toIsQuadrangle.symm hyw⟩, hwL⟩
      · rintro ⟨⟨hwz, hwy⟩, hwL⟩
        exact ⟨⟨h.toIsQuadrangle.symm hwz, hwL⟩, h.toIsQuadrangle.symm hwy⟩
    rw [hset, Finset.card_sdiff, hinter, Finset.card_singleton, h.card_perp hzy]
    omega
  exact ⟨hLsub, hZcard, hZrow⟩

private theorem special_far_data [DecidableEq α] [DecidableRel adj]
    (h : IsQuadrangleOfOrder adj s t) {a b z : α} {P Z Zs : Finset α} {q : α} {t : ℕ}
    (haq : ¬ adj a q) (hzL : z ∈ perp2 adj a b) (hzLq : ¬ adj z q)
    (hdisj : ∀ w ∈ P, Disjoint (perp2 adj a b) (perp2 adj q w))
    (hPmem : ∀ w, w ∈ P → w ∈ perp2 adj a q) (hPcard : P.card = t)
    (hZ_eq : Z = (nbhd adj z) \ perp2 adj a b)
    (hZs_eq : Zs = P.biUnion fun w => Z.filter fun y => y ∈ perp2 adj q w) :
    (∀ w ∈ P, (Z.filter fun y => y ∈ perp2 adj q w).card = 1) ∧
      (P : Set α).PairwiseDisjoint (fun w => Z.filter fun y => y ∈ perp2 adj q w) ∧
      Zs.card = t ∧ Zs ⊆ Z := by
  classical
  have hZs_term : ∀ w ∈ P, (Z.filter fun y => y ∈ perp2 adj q w).card = 1 := by
    intro w hw
    have hwperp : w ∈ perp2 adj a q := hPmem w hw
    have hwq : adj w q := (mem_perp2.1 hwperp).2
    have hqw : q ≠ w := by
      intro e
      have hwa : adj w a := (mem_perp2.1 hwperp).1
      rw [← e] at hwa
      exact haq (h.toIsQuadrangle.symm hwa)
    have hqwa : adj q w := h.toIsQuadrangle.symm hwq
    have hex := IsQuadrangle.existsUnique_adj_of_disjoint_perp2 h.toIsQuadrangle
      hqw hqwa (hdisj w hw) hzL
    let p := hex.choose
    have hpN : p ∈ perp2 adj q w := hex.choose_spec.1.1
    have hzp : adj z p := hex.choose_spec.1.2
    have hpZ : p ∈ Z := by
      rw [hZ_eq, Finset.mem_sdiff, mem_nbhd]
      exact ⟨hzp, fun hpL => (Finset.disjoint_left.1 (hdisj w hw)) hpL hpN⟩
    have hset : (Z.filter fun y => y ∈ perp2 adj q w) = {p} := by
      ext y
      rw [Finset.mem_filter, Finset.mem_singleton]
      constructor
      · rintro ⟨hyZ, hyN⟩
        rw [hZ_eq] at hyZ
        have hzy : adj z y := mem_nbhd.1 (Finset.mem_sdiff.1 hyZ).1
        exact hex.unique ⟨hyN, hzy⟩ ⟨hpN, hzp⟩
      · intro hyp'
        subst y
        exact ⟨hpZ, hpN⟩
    rw [hset, Finset.card_singleton]
  have hZs_pd : (P : Set α).PairwiseDisjoint
      (fun w => Z.filter fun y => y ∈ perp2 adj q w) := by
    intro w₁ hw₁ w₂ hw₂ hne
    change Disjoint (Z.filter fun y => y ∈ perp2 adj q w₁)
      (Z.filter fun y => y ∈ perp2 adj q w₂)
    rw [Finset.disjoint_left]
    intro y hy₁ hy₂
    have hy₁Z : y ∈ Z := (Finset.mem_filter.1 hy₁).1
    have hy₁N : y ∈ perp2 adj q w₁ := (Finset.mem_filter.1 hy₁).2
    have hy₂N : y ∈ perp2 adj q w₂ := (Finset.mem_filter.1 hy₂).2
    have hyq : y ≠ q := by
      intro e
      subst y
      rw [hZ_eq] at hy₁Z
      have hzq : adj z q := mem_nbhd.1 (Finset.mem_sdiff.1 hy₁Z).1
      exact hzLq hzq
    have hw₁perp : w₁ ∈ perp2 adj a q := hPmem w₁ hw₁
    have hw₂perp : w₂ ∈ perp2 adj a q := hPmem w₂ hw₂
    have hwnonadj : ¬ adj w₁ w₂ :=
      h.toIsQuadrangle.not_adj_of_not_adj haq (mem_perp2.1 hw₁perp).1
        (mem_perp2.1 hw₁perp).2 (mem_perp2.1 hw₂perp).1 (mem_perp2.1 hw₂perp).2 hne
    have hyq' : adj y q := (mem_perp2.1 hy₁N).1
    exact (h.toIsQuadrangle.not_adj_of_not_adj hwnonadj (mem_perp2.1 hy₁N).2
      (mem_perp2.1 hy₂N).2 (h.toIsQuadrangle.symm (mem_perp2.1 hw₁perp).2)
      (h.toIsQuadrangle.symm (mem_perp2.1 hw₂perp).2) hyq) hyq'
  have hZs_card : Zs.card = t := by
    rw [hZs_eq, Finset.card_biUnion hZs_pd]
    have hsum : (∑ w ∈ P, (Z.filter fun y => y ∈ perp2 adj q w).card) = ∑ _w ∈ P, 1 :=
      Finset.sum_congr rfl hZs_term
    rw [hsum, Finset.sum_const_nat (m := 1) (f := fun _ => 1) (fun _ _ => rfl), hPcard,
      Nat.mul_one]
  have hZs_sub : Zs ⊆ Z := by
    intro y hy
    rw [hZs_eq] at hy
    obtain ⟨w, hw, hy'⟩ := Finset.mem_biUnion.1 hy
    exact (Finset.mem_filter.1 hy').1
  exact ⟨hZs_term, hZs_pd, hZs_card, hZs_sub⟩

private theorem special_column [DecidableEq α] [DecidableRel adj]
    (h : IsQuadrangleOfOrder adj s t) {a b q z : α} {P Y Z Zs : Finset α} {σ : ℕ}
    (haq : ¬ adj a q) (hfq : f q = q) (hzLq : ¬ adj z q)
    (hPmem : ∀ w, w ∈ P → w ∈ perp2 adj a q)
    (hfixN : ∀ w ∈ P, ((perp2 adj q w).filter fun y => f y = y).card = σ + 1)
    (hYfix : ∀ y ∈ Y, f y = y)
    (hY_eq : Y = insert q (P.biUnion fun w =>
      (perp2 adj q w).filter fun y => f y = y ∧ y ≠ q))
    (hZ_eq : Z = (nbhd adj z) \ perp2 adj a b)
    (hZs_eq : Zs = P.biUnion fun w => Z.filter fun y => y ∈ perp2 adj q w) :
    ∀ y ∈ Zs, (Y.filter fun y' => adj y y').card ≤ σ + 1 := by
  classical
  intro y hy
  rw [hZs_eq] at hy
  obtain ⟨w, hw, hyZf⟩ := Finset.mem_biUnion.1 hy
  have hyZ : y ∈ Z := (Finset.mem_filter.1 hyZf).1
  have hyN : y ∈ perp2 adj q w := (Finset.mem_filter.1 hyZf).2
  have hyq : q ≠ y := by
    intro e
    have hzy : adj z q := by
      rw [hZ_eq] at hyZ
      have h1 : adj z y := mem_nbhd.1 (Finset.mem_sdiff.1 hyZ).1
      rwa [← e] at h1
    exact hzLq hzy
  have hwperp : w ∈ perp2 adj a q := hPmem w hw
  have hwq : adj w q := (mem_perp2.1 hwperp).2
  have hqw : q ≠ w := by
    intro e
    have hwa : adj w a := (mem_perp2.1 hwperp).1
    rw [← e] at hwa
    exact haq (h.toIsQuadrangle.symm hwa)
  have hqwa : adj q w := h.toIsQuadrangle.symm hwq
  have hsub : (Y.filter fun y' => adj y y') ⊆
      (perp2 adj q w).filter fun y' => f y' = y' := by
    intro y' hy'
    have hy'' := Finset.mem_filter.1 hy'
    have hy'fix : f y' = y' := hYfix y' hy''.1
    have hy'y : adj y y' := hy''.2
    have hyY : y' ∈ Y := hy''.1
    rw [hY_eq] at hyY
    rcases Finset.mem_insert.1 hyY with hy'q | hmem
    · subst y'
      rw [Finset.mem_filter, mem_perp2]
      exact ⟨⟨h.toIsQuadrangle.refl q, hqwa⟩, hfq⟩
    · obtain ⟨w', hw', hy'N⟩ := Finset.mem_biUnion.1 hmem
      have hy'N' := Finset.mem_filter.1 hy'N
      have hy'q : adj y' q := (mem_perp2.1 hy'N'.1).1
      have hy'Nw : y' ∈ perp2 adj q w :=
        IsQuadrangle.mem_perp2_of_adj_of_mem_perp2 h.toIsQuadrangle hqw hqwa
          (h.toIsQuadrangle.left_mem_perp2 hqwa) hyN hyq hy'q
          (h.toIsQuadrangle.symm hy'y)
      rw [Finset.mem_filter]
      exact ⟨hy'Nw, hy'fix⟩
  exact (Finset.card_le_card hsub).trans_eq (hfixN w hw)

private theorem far_line_count [DecidableEq α] [DecidableRel adj]
    (h : IsQuadrangleOfOrder adj s t) {Y Z Zs : Finset α} {t s σ : ℕ}
    (hYcard : Y.card = 1 + t * σ) (hZcard : Z.card = t * s) (hZs_card : Zs.card = t)
    (hZs_sub : Zs ⊆ Z) (hZrow : ∀ y ∈ Y, (Z.filter fun z => adj y z).card = t)
    (hcol₁ : ∀ y ∈ Zs, (Y.filter fun y' => adj y y').card ≤ σ + 1)
    (hcol₀ : ∀ y ∈ Z, y ∉ Zs → (Y.filter fun y' => adj y y').card ≤ 1)
    (hst : s < t) (hs1 : 1 ≤ s) (hσ : 1 ≤ σ) : False := by
  classical
  let r : α → α → Prop := fun y z => adj z y
  have hcol₁' : ∀ z ∈ Zs, (Y.bipartiteBelow r z).card ≤ σ + 1 := by
    intro z hz
    simpa only [r, Finset.bipartiteBelow] using hcol₁ z hz
  have hcol₀' : ∀ z ∈ Z, z ∉ Zs → (Y.bipartiteBelow r z).card ≤ 1 := by
    intro z hz hznot
    simpa only [r, Finset.bipartiteBelow] using hcol₀ z hz hznot
  have hrow : ∀ y ∈ Y, t ≤ (Z.bipartiteAbove r y).card := by
    intro y hy
    have hset : Z.bipartiteAbove r y = Z.filter (fun z => adj y z) := by
      ext z
      rw [Finset.mem_bipartiteAbove, Finset.mem_filter]
      exact ⟨fun hz => ⟨hz.1, h.toIsQuadrangle.symm hz.2⟩,
        fun hz => ⟨hz.1, h.toIsQuadrangle.symm hz.2⟩⟩
    rw [hset, hZrow y hy]
  have hlower : Y.card * t ≤ ∑ y ∈ Y, (Z.bipartiteAbove r y).card := by
    calc Y.card * t = ∑ _y ∈ Y, t :=
          (Finset.sum_const_nat (m := t) (f := fun _ => t) (fun _ _ => rfl)).symm
      _ ≤ ∑ y ∈ Y, (Z.bipartiteAbove r y).card := Finset.sum_le_sum hrow
  have hfilter_eq : Z.filter (fun z => z ∈ Zs) = Zs := by
    ext z
    rw [Finset.mem_filter]
    exact ⟨fun h => h.2, fun h => ⟨hZs_sub h, h⟩⟩
  have hfilter_not : Z.filter (fun z => z ∉ Zs) = Z \ Zs := by
    ext z
    simp only [Finset.mem_filter, Finset.mem_sdiff]
  have hupper₁ : (∑ z ∈ Z.filter (fun z => z ∈ Zs), (Y.bipartiteBelow r z).card) ≤
      t * (σ + 1) := by
    calc (∑ z ∈ Z.filter (fun z => z ∈ Zs), (Y.bipartiteBelow r z).card) ≤
          ∑ z ∈ Z.filter (fun z => z ∈ Zs), (σ + 1) :=
            Finset.sum_le_sum fun z hz => hcol₁' z (Finset.mem_filter.1 hz).2
      _ = (Z.filter (fun z => z ∈ Zs)).card * (σ + 1) :=
            Finset.sum_const_nat (m := σ + 1) (f := fun _ => σ + 1) (fun _ _ => rfl)
      _ = t * (σ + 1) := by rw [hfilter_eq, hZs_card]
  have hupper₂ : (∑ z ∈ Z.filter (fun z => z ∉ Zs), (Y.bipartiteBelow r z).card) ≤
      (Z.card - Zs.card) * 1 := by
    calc (∑ z ∈ Z.filter (fun z => z ∉ Zs), (Y.bipartiteBelow r z).card) ≤
          ∑ z ∈ Z.filter (fun z => z ∉ Zs), 1 :=
            Finset.sum_le_sum fun z hz =>
              hcol₀' z (Finset.mem_filter.1 hz).1 (Finset.mem_filter.1 hz).2
      _ = (Z.filter (fun z => z ∉ Zs)).card * 1 :=
            Finset.sum_const_nat (m := 1) (f := fun _ => 1) (fun _ _ => rfl)
      _ = (Z.card - Zs.card) * 1 := by rw [hfilter_not, Finset.card_sdiff_of_subset hZs_sub]
  have hupper : (∑ z ∈ Z, (Y.bipartiteBelow r z).card) ≤ t * (σ + 1) + (t * s - t) := by
    have hsplit := Finset.sum_filter_add_sum_filter_not (s := Z) (p := fun z => z ∈ Zs)
      (f := fun z => (Y.bipartiteBelow r z).card)
    rw [← hsplit]
    have h₂ := hupper₂
    rw [hZcard, hZs_card, Nat.mul_one] at h₂
    exact add_le_add hupper₁ h₂
  have hdouble := Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
    (r := r) (s := Y) (t := Z)
  have hineq : Y.card * t ≤ t * (σ + 1) + (t * s - t) :=
    hlower.trans (hdouble.trans_le hupper)
  rw [hYcard] at hineq
  exact false_of_fixed_line_count hst hs1 hσ hineq

private theorem nonspecial_q_image [DecidableEq α] [DecidableRel adj]
    (h : IsQuadrangleOfOrder adj s t) {a q y y₂ w₂ : α} {P Z Zs : Finset α}
    (haq : ¬ adj a q) (hPmem : ∀ w, w ∈ P → w ∈ perp2 adj a q)
    (hZs_eq : Zs = P.biUnion fun w => Z.filter fun y => y ∈ perp2 adj q w)
    (hyZ : y ∈ Z) (hyNotZs : y ∉ Zs) (hyadj₁ : adj y q) (hyadj₂ : adj y y₂)
    (hw₂ : w₂ ∈ P)
    (hy₂N : y₂ ∈ (perp2 adj q w₂).filter fun y' => f y' = y' ∧ y' ≠ q) : False := by
  have hy₂N' := Finset.mem_filter.1 hy₂N
  have hw₂perp : w₂ ∈ perp2 adj a q := hPmem w₂ hw₂
  have hw₂q : adj w₂ q := (mem_perp2.1 hw₂perp).2
  have hqw₂ : q ≠ w₂ := by
    intro e
    have hwa : adj w₂ a := (mem_perp2.1 hw₂perp).1
    rw [← e] at hwa
    exact haq (h.toIsQuadrangle.symm hwa)
  have hqwa₂ : adj q w₂ := h.toIsQuadrangle.symm hw₂q
  have hyNw₂ : y ∈ perp2 adj q w₂ :=
    IsQuadrangle.mem_perp2_of_adj_of_mem_perp2 h.toIsQuadrangle hqw₂ hqwa₂
      (h.toIsQuadrangle.left_mem_perp2 hqwa₂) hy₂N'.1 (Ne.symm hy₂N'.2.2) hyadj₁ hyadj₂
  exact hyNotZs (by
    rw [hZs_eq]
    exact Finset.mem_biUnion.2 ⟨w₂, hw₂, Finset.mem_filter.2 ⟨hyZ, hyNw₂⟩⟩)

private theorem nonspecial_image_q [DecidableEq α] [DecidableRel adj]
    (h : IsQuadrangleOfOrder adj s t) {a q y y₁ w₁ : α} {P Z Zs : Finset α}
    (haq : ¬ adj a q) (hPmem : ∀ w, w ∈ P → w ∈ perp2 adj a q)
    (hZs_eq : Zs = P.biUnion fun w => Z.filter fun y => y ∈ perp2 adj q w)
    (hyZ : y ∈ Z) (hyNotZs : y ∉ Zs) (hyadj₁ : adj y y₁) (hyadj₂ : adj y q)
    (hw₁ : w₁ ∈ P)
    (hy₁N : y₁ ∈ (perp2 adj q w₁).filter fun y' => f y' = y' ∧ y' ≠ q) : False := by
  have hy₁N' := Finset.mem_filter.1 hy₁N
  have hy₁q : q ≠ y₁ := Ne.symm hy₁N'.2.2
  have hw₁perp : w₁ ∈ perp2 adj a q := hPmem w₁ hw₁
  have hw₁q : adj w₁ q := (mem_perp2.1 hw₁perp).2
  have hqw₁ : q ≠ w₁ := by
    intro e
    have hwa : adj w₁ a := (mem_perp2.1 hw₁perp).1
    rw [← e] at hwa
    exact haq (h.toIsQuadrangle.symm hwa)
  have hqwa₁ : adj q w₁ := h.toIsQuadrangle.symm hw₁q
  have hyNw₁ : y ∈ perp2 adj q w₁ :=
    IsQuadrangle.mem_perp2_of_adj_of_mem_perp2 h.toIsQuadrangle hqw₁ hqwa₁
      (h.toIsQuadrangle.left_mem_perp2 hqwa₁) hy₁N'.1 hy₁q hyadj₂ hyadj₁
  exact hyNotZs (by
    rw [hZs_eq]
    exact Finset.mem_biUnion.2 ⟨w₁, hw₁, Finset.mem_filter.2 ⟨hyZ, hyNw₁⟩⟩)

private theorem nonspecial_image_image [DecidableEq α] [DecidableRel adj]
    (h : IsQuadrangleOfOrder adj s t)
    (hf : ∀ x y, adj (f x) (f y) ↔ adj x y) {a q x z b y y₁ y₂ w₁ w₂ : α} {P Z Zs : Finset α}
    (hst : s < t) (haq : ¬ adj a q) (hfa : f a = a) (hfq : f q = q)
    (ha : FixesLinesThrough adj f a) (hxa : adj x a) (hxa' : x ≠ a) (hxq : ¬ adj x q)
    (hfx : f x = x) (hab : a ≠ b) (hbadj : adj a b) (hzf : f z ≠ z)
    (hPmem : ∀ w, w ∈ P → w ∈ perp2 adj a q)
    (hLmap : ∀ y ∈ perp2 adj a b, f y ∈ perp2 adj a b) (hzL : z ∈ perp2 adj a b)
    (hZ_eq : Z = (nbhd adj z) \ perp2 adj a b)
    (hZs_eq : Zs = P.biUnion fun w => Z.filter fun y => y ∈ perp2 adj q w)
    (hyZ : y ∈ Z) (hyNotZs : y ∉ Zs)
    (hyadj₁ : adj y y₁) (hyadj₂ : adj y y₂) (hne : y₁ ≠ y₂)
    (hw₁ : w₁ ∈ P) (hw₂ : w₂ ∈ P)
    (hy₁N : y₁ ∈ (perp2 adj q w₁).filter fun y' => f y' = y' ∧ y' ≠ q)
    (hy₂N : y₂ ∈ (perp2 adj q w₂).filter fun y' => f y' = y' ∧ y' ≠ q) : False := by
  have hy₁N' := Finset.mem_filter.1 hy₁N
  have hy₂N' := Finset.mem_filter.1 hy₂N
  have hy₁q : q ≠ y₁ := Ne.symm hy₁N'.2.2
  have hy₁fix : f y₁ = y₁ := hy₁N'.2.1
  have hy₂q : q ≠ y₂ := Ne.symm hy₂N'.2.2
  have hy₂fix : f y₂ = y₂ := hy₂N'.2.1
  have hw₁perp : w₁ ∈ perp2 adj a q := hPmem w₁ hw₁
  have hw₂perp : w₂ ∈ perp2 adj a q := hPmem w₂ hw₂
  have hw₁q : adj w₁ q := (mem_perp2.1 hw₁perp).2
  have hqw₁ : q ≠ w₁ := by
    intro e
    have hwa : adj w₁ a := (mem_perp2.1 hw₁perp).1
    rw [← e] at hwa
    exact haq (h.toIsQuadrangle.symm hwa)
  have hqwa₁ : adj q w₁ := h.toIsQuadrangle.symm hw₁q
  by_cases hw : w₁ = w₂
  · subst w₂
    have hyNw₁ : y ∈ perp2 adj q w₁ :=
      IsQuadrangle.mem_perp2_of_adj_of_mem_perp2 h.toIsQuadrangle hqw₁ hqwa₁
        hy₁N'.1 hy₂N'.1 hne hyadj₁ hyadj₂
    exact hyNotZs (by
      rw [hZs_eq]
      exact Finset.mem_biUnion.2 ⟨w₁, hw₁, Finset.mem_filter.2 ⟨hyZ, hyNw₁⟩⟩)
  · have hnon : ¬ adj y₁ y₂ :=
      IsQuadrangle.not_adj_of_mem_perp2_of_ne h.toIsQuadrangle haq hw₁perp hw₂perp
        hw hy₁N'.1 hy₂N'.1 hy₁N'.2.2 hy₂N'.2.2
    have hy₁full : FixesLinesThrough adj f y₁ :=
      fixesLinesThrough_of_apply_eq h hst hf haq hfa hfq ha hxa hxa' hxq hfx hy₁fix
    have hyfix : f y = y :=
      IsQuadrangle.apply_eq_of_collinear_noncollinear h.toIsQuadrangle hf hy₁fix
        hy₁full hy₂fix hnon hyadj₁ hyadj₂
    rw [hZ_eq] at hyZ
    have hz_y : adj z y := mem_nbhd.1 (Finset.mem_sdiff.1 hyZ).1
    have hyL : y ∉ perp2 adj a b := (Finset.mem_sdiff.1 hyZ).2
    have hfz_y : adj (f z) y := by
      have h1 : adj (f z) (f y) := (hf z y).2 hz_y
      rwa [hyfix] at h1
    have hzy_not : ¬ (adj y a ∧ adj y b) := fun h => hyL (mem_perp2.2 h)
    exact hzf (h.toIsQuadrangle.unique_adj (x := a) (y := b) (z := y) (w := f z)
      (w' := z) hab hbadj hzy_not (mem_perp2.1 (hLmap z hzL)).1
      (mem_perp2.1 (hLmap z hzL)).2 (h.toIsQuadrangle.symm hfz_y)
      (mem_perp2.1 hzL).1 (mem_perp2.1 hzL).2 (h.toIsQuadrangle.symm hz_y))

private theorem apply_eq_of_mem_perp2_line (h : IsQuadrangleOfOrder adj s t) (hst : s < t)
    (hf : ∀ x y, adj (f x) (f y) ↔ adj x y) {a q x : α} (haq : ¬ adj a q) (hfa : f a = a)
    (hfq : f q = q) (ha : FixesLinesThrough adj f a) (hxa : adj x a) (hxa' : x ≠ a)
    (hxq : ¬ adj x q) (hfx : f x = x) {b : α} (hab : a ≠ b) (hbadj : adj a b) :
    ∀ z ∈ perp2 adj a b, f z = z := by
  classical
  intro z hzL
  by_contra hzf
  obtain ⟨xl, S, σ, hxlL, hxlperp, hxlfix, hS2, hS_card, herase, hS_eq, hPcard,
    hxl_unique, hdisj⟩ := line_data_base h hf haq hfa hfq ha hab hbadj
  let P : Finset α := (perp2 adj a q).erase xl
  obtain ⟨hNmap, hLmap, hfixN⟩ :=
    line_data_full h hf haq hfa hfq ha hab hbadj hS_card hS_eq hdisj

  let Y : Finset α := insert q (P.biUnion fun w =>
    (perp2 adj q w).filter fun y => f y = y ∧ y ≠ q)
  have hYcard : Y.card = 1 + t * σ :=
    fixed_line_set_card h haq hfq (fun w hw => (Finset.mem_erase.1 hw).2) hPcard hfixN rfl
  obtain ⟨hYfix, hY_opp⟩ :=
    fixed_line_set_properties h hf hfq hab hbadj hzf hxlfix
      hxl_unique hdisj hLmap hzL rfl
  have hzLq : ¬ adj z q := by
    intro hzq
    have hzxl : z = xl := hxl_unique z hzL hzq
    exact hzf (by rw [hzxl]; exact hxlfix)
  let Z : Finset α := (nbhd adj z) \ perp2 adj a b
  obtain ⟨hLsub, hZcard, hZrow⟩ := far_line_data h hzL rfl hY_opp hab hbadj
  let Zs : Finset α := P.biUnion fun w => Z.filter fun y => y ∈ perp2 adj q w
  obtain ⟨hZs_term, hZs_pd, hZs_card, hZs_sub⟩ :=
    special_far_data h haq hzL hzLq hdisj (fun w hw => (Finset.mem_erase.1 hw).2) hPcard rfl rfl
  have hcol₁ : ∀ y ∈ Zs, (Y.filter fun y' => adj y y').card ≤ σ + 1 :=
    special_column h haq hfq hzLq (fun w hw => (Finset.mem_erase.1 hw).2) hfixN hYfix rfl rfl rfl
  have hcol₀ : ∀ y ∈ Z, y ∉ Zs → (Y.filter fun y' => adj y y').card ≤ 1 := by
    intro y hyZ hyNotZs
    rw [Finset.card_le_one]
    intro y₁ hy₁ y₂ hy₂
    have hy₁' := Finset.mem_filter.1 hy₁
    have hy₂' := Finset.mem_filter.1 hy₂
    have hyadj₁ : adj y y₁ := hy₁'.2
    have hyadj₂ : adj y y₂ := hy₂'.2
    by_contra hne
    have hy₁dec : y₁ = q ∨ ∃ w₁ ∈ P,
        y₁ ∈ (perp2 adj q w₁).filter fun y' => f y' = y' ∧ y' ≠ q := by
      have hyY := hy₁'.1
      dsimp only [Y] at hyY
      simpa only [Finset.mem_insert, Finset.mem_biUnion] using hyY
    have hy₂dec : y₂ = q ∨ ∃ w₂ ∈ P,
        y₂ ∈ (perp2 adj q w₂).filter fun y' => f y' = y' ∧ y' ≠ q := by
      have hyY := hy₂'.1
      dsimp only [Y] at hyY
      simpa only [Finset.mem_insert, Finset.mem_biUnion] using hyY
    rcases hy₁dec with hy₁q | ⟨w₁, hw₁, hy₁N⟩
    · subst y₁
      rcases hy₂dec with hy₂q | ⟨w₂, hw₂, hy₂N⟩
      · subst y₂
        exact hne rfl
      · exact nonspecial_q_image h haq (fun w hw => (Finset.mem_erase.1 hw).2) rfl
          hyZ hyNotZs hyadj₁ hyadj₂ hw₂ hy₂N
    · rcases hy₂dec with hy₂q | ⟨w₂, hw₂, hy₂N⟩
      · subst y₂
        exact nonspecial_image_q h haq (fun w hw => (Finset.mem_erase.1 hw).2) rfl
          hyZ hyNotZs hyadj₁ hyadj₂ hw₁ hy₁N
      · exact nonspecial_image_image h hf hst haq hfa hfq ha hxa hxa' hxq hfx hab hbadj
          hzf (fun w hw => (Finset.mem_erase.1 hw).2) hLmap hzL rfl rfl hyZ hyNotZs
          hyadj₁ hyadj₂ hne hw₁ hw₂ hy₁N hy₂N
  have hs1 : 1 ≤ s := by
    have hc := h.card_line hab hbadj
    have h2 : 1 < (perp2 adj a b).card :=
      Finset.one_lt_card.2 ⟨a, mem_perp2.2 ⟨h.toIsQuadrangle.refl a, hbadj⟩, b,
        mem_perp2.2 ⟨h.toIsQuadrangle.symm hbadj, h.toIsQuadrangle.refl b⟩, hab⟩
    omega
  have hσ : 1 ≤ σ := by omega
  exact far_line_count h hYcard hZcard hZs_card hZs_sub hZrow hcol₁ hcol₀ hst hs1 hσ

private theorem exists_proj_fixed_full (h : IsQuadrangleOfOrder adj s t) (hst : s < t)
    (hf : ∀ x y, adj (f x) (f y) ↔ adj x y) {a q x : α} (haq : ¬ adj a q) (hfa : f a = a)
    (hfq : f q = q) (ha : FixesLinesThrough adj f a) (hxa : adj x a) (hxa' : x ≠ a)
    (hxq : ¬ adj x q) (hfx : f x = x) {b z : α} (hab : a ≠ b) (hbadj : adj a b) :
    ∃ p, adj p a ∧ adj p b ∧ adj z p ∧ f p = p ∧ FixesLinesThrough adj f p := by
  obtain ⟨p, hpa, hpb, hzp⟩ := h.toIsQuadrangle.meets z hab hbadj
  have hpL : p ∈ perp2 adj a b := mem_perp2.2 ⟨hpa, hpb⟩
  have hfp : f p = p :=
    apply_eq_of_mem_perp2_line h hst hf haq hfa hfq ha hxa hxa' hxq hfx hab hbadj p hpL
  exact ⟨p, hpa, hpb, hzp, hfp,
    fixesLinesThrough_of_apply_eq h hst hf haq hfa hfq ha hxa hxa' hxq hfx hfp⟩

private theorem apply_eq_self_aux (h : IsQuadrangleOfOrder adj s t) (hst : s < t)
    (hf : ∀ x y, adj (f x) (f y) ↔ adj x y) {a q x : α} (haq : ¬ adj a q) (hfa : f a = a)
    (hfq : f q = q) (ha : FixesLinesThrough adj f a) (hxa : adj x a) (hxa' : x ≠ a)
    (hxq : ¬ adj x q) (hfx : f x = x) (z : α) : f z = z := by
  classical
  by_cases hza : adj a z
  · by_cases hzxa : z = a
    · subst z
      exact hfa
    · exact apply_eq_of_mem_perp2_line h hst hf haq hfa hfq ha hxa hxa' hxq hfx
        (Ne.symm hzxa) hza z (h.toIsQuadrangle.right_mem_perp2 hza)
  · obtain ⟨z₁, hz₁a, hz₁x, hzz₁, hz₁fix, hz₁full⟩ :=
      exists_proj_fixed_full h hst hf haq hfa hfq ha hxa hxa' hxq hfx
        (b := x) (z := z) (Ne.symm hxa') (h.toIsQuadrangle.symm hxa)
    have haL₁ : a ∈ perp2 adj a x :=
      h.toIsQuadrangle.left_mem_perp2 (h.toIsQuadrangle.symm hxa)
    have hs1 : 1 ≤ s := by
      have h2 : 1 < (perp2 adj a x).card :=
        Finset.one_lt_card.2 ⟨a, haL₁, x, h.toIsQuadrangle.right_mem_perp2
          (h.toIsQuadrangle.symm hxa), Ne.symm hxa'⟩
      have hc := h.card_line (Ne.symm hxa') (h.toIsQuadrangle.symm hxa)
      omega
    have ht1 : 1 ≤ t := by omega
    have hlt : (perp2 adj a x).card < (nbhd adj a).card := by
      rw [h.card_nbhd a, h.card_line (Ne.symm hxa') (h.toIsQuadrangle.symm hxa)]
      nlinarith [Nat.mul_pos ht1 hs1]
    obtain ⟨r, hrN, hrL₁⟩ :=
      Finset.exists_mem_notMem_of_card_lt_card (s := perp2 adj a x) (t := nbhd adj a) hlt
    have har : adj a r := mem_nbhd.1 hrN
    have hra : r ≠ a := by
      intro e
      exact hrL₁ (by rw [e]; exact haL₁)
    have har_ne : a ≠ r := Ne.symm hra
    have hL₂_ne : perp2 adj a r ≠ perp2 adj a x := by
      intro e
      exact hrL₁ (by rw [← e]; exact h.toIsQuadrangle.right_mem_perp2 har)
    obtain ⟨z₂, hz₂a, hz₂r, hzz₂, hz₂fix, hz₂full⟩ :=
      exists_proj_fixed_full h hst hf haq hfa hfq ha hxa hxa' hxq hfx
        (b := r) (z := z) har_ne har
    have hz₁_ne_a : z₁ ≠ a := fun e => hza (h.toIsQuadrangle.symm (e ▸ hzz₁))
    have hz₂_ne_a : z₂ ≠ a := fun e => hza (h.toIsQuadrangle.symm (e ▸ hzz₂))
    have hnon : ¬ adj z₁ z₂ := by
      intro hz₁z₂
      have hxz₂ : adj x z₂ :=
        h.toIsQuadrangle.clique (Ne.symm hz₁_ne_a) (h.toIsQuadrangle.symm hz₁a)
          hxa (h.toIsQuadrangle.symm hz₁x) hz₂a (h.toIsQuadrangle.symm hz₁z₂)
      have hz₂L₁ : z₂ ∈ perp2 adj a x :=
        mem_perp2.2 ⟨hz₂a, h.toIsQuadrangle.symm hxz₂⟩
      have hxr : adj x r :=
        h.toIsQuadrangle.clique (Ne.symm hz₂_ne_a) (h.toIsQuadrangle.symm hz₂a)
          hxa hxz₂ (h.toIsQuadrangle.symm har) (h.toIsQuadrangle.symm hz₂r)
      exact hrL₁ (mem_perp2.2 ⟨h.toIsQuadrangle.symm har, h.toIsQuadrangle.symm hxr⟩)
    exact IsQuadrangle.apply_eq_of_collinear_noncollinear h.toIsQuadrangle hf hz₁fix hz₁full
      hz₂fix hnon hzz₁ hzz₂

theorem apply_eq_self_of_fixesLinesThrough (h : IsQuadrangleOfOrder adj s t) (hst : s < t)
    (hf : ∀ x y, adj (f x) (f y) ↔ adj x y) {a q x : α} (haq : ¬ adj a q) (hfa : f a = a)
    (hfq : f q = q) (ha : FixesLinesThrough adj f a) (hxa : adj x a) (hxa' : x ≠ a)
    (hxq : ¬ adj x q) (hfx : f x = x) (z : α) : f z = z :=
  apply_eq_self_aux h hst hf haq hfa hfq ha hxa hxa' hxq hfx z

theorem mem_span2_of_apply_eq (h : IsQuadrangleOfOrder adj s t) (hst : s < t)
    (hf : ∀ x y, adj (f x) (f y) ↔ adj x y) {a q : α} (haq : ¬ adj a q) (hfa : f a = a)
    (hfq : f q = q) (ha : FixesLinesThrough adj f a) (hne : ∃ z, f z ≠ z) {z : α}
    (hza : ¬ adj z a) (hfz : f z = z) : z ∈ span2 adj a q := by
  classical
  rw [mem_span2]
  intro w hwa hwq
  have hwa' : w ∈ perp2 adj a q := mem_perp2.2 ⟨hwa, hwq⟩
  have hw_a : adj w a := hwa
  have hw_ne_a : w ≠ a := fun e => haq (e ▸ hwq)
  have hfw : f w = w :=
    IsQuadrangle.apply_eq_of_mem_perp2 h.toIsQuadrangle hf haq hfa hfq ha hwa'
  obtain ⟨p, hpa, hpw, hzp⟩ :=
    h.toIsQuadrangle.meets z (Ne.symm hw_ne_a) (h.toIsQuadrangle.symm hw_a)
  have hfp : f p = p :=
    IsQuadrangle.apply_eq_of_proj_of_adj h.toIsQuadrangle hf hfz hfw hfa hza
      (Ne.symm hw_ne_a) (h.toIsQuadrangle.symm hw_a) hpa hpw hzp
  have hp_ne_a : p ≠ a := fun e => hza (e ▸ hzp)
  by_cases hpq : adj p q
  · have hpqa : adj p a := hpa
    have hqnot : ¬ (adj q a ∧ adj q w) := fun hq => haq (h.toIsQuadrangle.symm hq.1)
    have hp_eq : p = w := h.toIsQuadrangle.unique_adj (x := a) (y := w) (z := q)
      (w := p) (w' := w) (Ne.symm hw_ne_a) (h.toIsQuadrangle.symm hw_a) hqnot
      hpqa hpw (h.toIsQuadrangle.symm hpq) hwa (h.toIsQuadrangle.refl w)
      (h.toIsQuadrangle.symm hwq)
    rwa [hp_eq] at hzp
  · exfalso
    obtain ⟨z₀, hz₀⟩ := hne
    exact hz₀ (apply_eq_self_of_fixesLinesThrough h hst hf haq hfa hfq ha hpa hp_ne_a hpq hfp z₀)

private theorem exists_fixed_point_of_odd_iterate {β : Type*} [Fintype β] [DecidableEq β]
    {g : β → β} {e : ℕ} (hodd : ¬ 2 ∣ Fintype.card β) (hg : g^[2 ^ e] = id) :
    ∃ b, g b = b := by
  classical
  have hNpos : 0 < 2 ^ e := pow_pos (by norm_num) e
  have hN1 : 2 ^ e - 1 + 1 = 2 ^ e := Nat.sub_add_cancel (by omega)
  have hg_inj : Function.Injective g := by
    intro x y hxy
    calc x = g^[2 ^ e] x := (congrFun hg x).symm
      _ = g^[2 ^ e - 1] (g x) := by
          conv_lhs => rw [← hN1]
          rw [Function.iterate_succ_apply]
      _ = g^[2 ^ e - 1] (g y) := by rw [hxy]
      _ = g^[2 ^ e] y := by
          conv_rhs => rw [← hN1]
          rw [Function.iterate_succ_apply]
      _ = y := congrFun hg y
  have hg_bij : Function.Bijective g := by
    haveI : Finite β := Finite.of_fintype β
    exact Function.Injective.bijective_of_finite hg_inj
  let σ : Equiv.Perm β := Equiv.ofBijective g hg_bij
  have hσ : σ ^ (2 ^ e) = 1 := by
    ext y
    rw [Equiv.Perm.coe_pow, Equiv.Perm.coe_one]
    have hcoe : (⇑σ : β → β) = g := by
      funext y'
      exact Equiv.ofBijective_apply g hg_bij y'
    rw [hcoe]
    exact congrFun hg y
  haveI : Fact (Nat.Prime 2) := ⟨by decide⟩
  obtain ⟨b, hb⟩ := Equiv.Perm.exists_fixed_point_of_prime (p := 2) (n := e) hodd hσ
  refine ⟨b, ?_⟩
  rw [← Equiv.ofBijective_apply g hg_bij b, hb]

private theorem exists_fixed_point_on_erased_line {B L : Finset α} {a w : α}
    (hBmem : ∀ y, y ∈ B ↔ y ∈ L ∧ y ≠ a ∧ y ≠ w) (hLmap : ∀ y ∈ L, f y ∈ L)
    (hfa : f a = a) (hwfix : f w = w) (hf_inj : Function.Injective f)
    (hodd : ¬ 2 ∣ Fintype.card B) {e : ℕ} (hfe : f^[2 ^ e] = id) :
    ∃ b : B, f b.1 = b.1 := by
  classical
  let g : B → B := fun y =>
    ⟨f y.1, by
      have hy := (hBmem y.1).1 y.2
      have hyL : y.1 ∈ L := hy.1
      have hy_ne_a : y.1 ≠ a := hy.2.1
      have hy_ne_w : y.1 ≠ w := hy.2.2
      exact (hBmem (f y.1)).2 ⟨hLmap y.1 hyL,
        fun hfa' => hy_ne_a (hf_inj (by rw [hfa', hfa])),
        fun hfw => hy_ne_w (hf_inj (by rw [hfw, hwfix]))⟩⟩
  have hg_iter : ∀ n (y : B), ((g^[n] y : B) : α) = f^[n] y.1 := by
    intro n
    induction n with
    | zero => intro y; rfl
    | succ n ih =>
        intro y
        rw [Function.iterate_succ_apply']
        change f ((g^[n] y : B) : α) = f^[n + 1] y.1
        rw [ih, Function.iterate_succ_apply']
  have hgN : g^[2 ^ e] = id := by
    funext y
    apply Subtype.ext
    rw [hg_iter]
    exact congrFun hfe y.1
  obtain ⟨b, hb⟩ := exists_fixed_point_of_odd_iterate hodd hgN
  exact ⟨b, congrArg Subtype.val hb⟩

theorem apply_eq_self_of_iterate_eq_id (h : IsQuadrangleOfOrder adj s t) (hst : s < t)
    (hs : Even s) (hf : ∀ x y, adj (f x) (f y) ↔ adj x y) {e : ℕ} (hfe : f^[2 ^ e] = id)
    {a q : α} (haq : ¬ adj a q) (hfa : f a = a) (hfq : f q = q)
    (ha : FixesLinesThrough adj f a) (z : α) : f z = z := by
  classical
  have ht1 : 1 ≤ t := by omega
  have hcard : 1 < (perp2 adj a q).card := by
    rw [h.card_perp haq]
    omega
  obtain ⟨w, hwperp, hw_ne⟩ := Finset.exists_mem_ne hcard a
  have hwa : adj w a := (mem_perp2.1 hwperp).1
  have hwq : adj w q := (mem_perp2.1 hwperp).2
  have hw_ne_a : w ≠ a := hw_ne
  have ha_ne_w : a ≠ w := Ne.symm hw_ne_a
  have hwfix : f w = w :=
    IsQuadrangle.apply_eq_of_mem_perp2 h.toIsQuadrangle hf haq hfa hfq ha hwperp
  have hLmap : ∀ y ∈ perp2 adj a w, f y ∈ perp2 adj a w := fun y hy =>
    IsQuadrangle.maps_perp2_of_fixesLinesThrough h.toIsQuadrangle hf hfa ha
      (h.toIsQuadrangle.symm hwa) hy
  let L : Finset α := perp2 adj a w
  let B : Finset α := (L.erase a).erase w
  have haL : a ∈ L := by
    dsimp only [L]
    exact h.toIsQuadrangle.left_mem_perp2 (h.toIsQuadrangle.symm hwa)
  have hwL : w ∈ L := by
    dsimp only [L]
    exact h.toIsQuadrangle.right_mem_perp2 (h.toIsQuadrangle.symm hwa)
  have hLcard : L.card = s + 1 := by
    dsimp only [L]
    exact h.card_line ha_ne_w (h.toIsQuadrangle.symm hwa)
  have hBcard : B.card = s - 1 := by
    dsimp only [B]
    rw [Finset.card_erase_of_mem (Finset.mem_erase.2 ⟨hw_ne_a, hwL⟩),
      Finset.card_erase_of_mem haL, hLcard]
    omega
  have hspos : 1 ≤ s := by
    have h2 : 1 < L.card := Finset.one_lt_card.2 ⟨a, haL, w, hwL, ha_ne_w⟩
    rw [hLcard] at h2
    omega
  have hsodd : Odd (s - 1) := Nat.Even.sub_odd (by omega) hs (by norm_num : Odd 1)
  have hBodd : ¬ 2 ∣ Fintype.card B := by
    rw [Fintype.card_coe, hBcard]
    exact Odd.not_two_dvd_nat hsodd
  have hNpos : 0 < 2 ^ e := pow_pos (by norm_num) e
  have hN1 : 2 ^ e - 1 + 1 = 2 ^ e := Nat.sub_add_cancel (by omega)
  have hf_inj : Function.Injective f := by
    intro x y hxy
    calc x = f^[2 ^ e] x := (congrFun hfe x).symm
      _ = f^[2 ^ e - 1] (f x) := by
          conv_lhs => rw [← hN1]
          rw [Function.iterate_succ_apply]
      _ = f^[2 ^ e - 1] (f y) := by rw [hxy]
      _ = f^[2 ^ e] y := by
          conv_rhs => rw [← hN1]
          rw [Function.iterate_succ_apply]
      _ = y := congrFun hfe y
  have hBmem : ∀ y, y ∈ B ↔ y ∈ L ∧ y ≠ a ∧ y ≠ w := by
    intro y
    dsimp only [B]
    rw [Finset.mem_erase, Finset.mem_erase]
    tauto
  obtain ⟨b, hbval⟩ := exists_fixed_point_on_erased_line hBmem hLmap hfa hwfix hf_inj hBodd hfe
  have hbL : b.1 ∈ L := (Finset.mem_erase.1 (Finset.mem_erase.1 b.2).2).2
  have hb_ne_a : b.1 ≠ a := (Finset.mem_erase.1 (Finset.mem_erase.1 b.2).2).1
  have hb_ne_w : b.1 ≠ w := (Finset.mem_erase.1 b.2).1
  have hba : adj b.1 a := (mem_perp2.1 hbL).1
  have hbq : ¬ adj b.1 q := by
    intro hbq
    have hqnot : ¬ (adj q a ∧ adj q w) := fun hq => haq (h.toIsQuadrangle.symm hq.1)
    have hbw : b.1 = w := h.toIsQuadrangle.unique_adj (x := a) (y := w) (z := q)
      (w := b.1) (w' := w) ha_ne_w (h.toIsQuadrangle.symm hwa) hqnot
      (mem_perp2.1 hbL).1 (mem_perp2.1 hbL).2 (h.toIsQuadrangle.symm hbq) hwa
      (h.toIsQuadrangle.refl w) (h.toIsQuadrangle.symm hwq)
    exact hb_ne_w hbw
  exact apply_eq_self_of_fixesLinesThrough h hst hf haq hfa hfq ha hba hb_ne_a hbq hbval z

end IsQuadrangleOfOrder

end CFSG.Combinatorics.QuadrangleGraph
