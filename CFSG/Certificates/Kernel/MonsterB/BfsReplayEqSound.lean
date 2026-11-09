module

public import CFSG.Certificates.Kernel.MonsterB.BfsReplayTSound

namespace CFSG.KC.Bfs

open CFSG.Monster.B.TwoA.Census

section Ext

variable {α : Type} [Inhabited α]

theorem rplExt_refl (a : Array α) : Ext a a := ⟨le_rfl, fun _ _ => rfl⟩

theorem rplExt_push (a : Array α) (x : α) : Ext a (a.push x) :=
  ⟨by rw [Array.size_push]; omega, fun _ hj => push_get_lt a x hj⟩

theorem rplExt_trans {a b c : Array α} (h1 : Ext a b) (h2 : Ext b c) : Ext a c :=
  ⟨le_trans h1.1 h2.1, fun j hj => by rw [h2.2 j (lt_of_lt_of_le hj h1.1), h1.2 j hj]⟩

theorem rplExt_gF (act : ℕ → α → α) (key : α → ℕ) (i : ℕ)
    (acc : Array α × Array ℕ × Array ℕ × Std.HashMap ℕ ℕ × Array ℕ) (k : ℕ) :
    Ext acc.2.1 (gF act key i acc k).2.1 ∧ Ext acc.2.2.1 (gF act key i acc k).2.2.1 := by
  obtain ⟨pts, par, lab, idx, row⟩ := acc
  simp only [gF]
  split
  · exact ⟨rplExt_refl _, rplExt_refl _⟩
  · exact ⟨rplExt_push _ _, rplExt_push _ _⟩

theorem rplExt_fold (act : ℕ → α → α) (key : α → ℕ) (i : ℕ) : ∀ (l : List ℕ)
    (acc : Array α × Array ℕ × Array ℕ × Std.HashMap ℕ ℕ × Array ℕ),
    Ext acc.2.1 (l.foldl (gF act key i) acc).2.1 ∧
      Ext acc.2.2.1 (l.foldl (gF act key i) acc).2.2.1
  | [], _ => ⟨rplExt_refl _, rplExt_refl _⟩
  | k :: l, acc => by
    rw [List.foldl_cons]
    obtain ⟨h1, h2⟩ := rplExt_gF act key i acc k
    obtain ⟨h3, h4⟩ := rplExt_fold act key i l (gF act key i acc k)
    exact ⟨rplExt_trans h1 h3, rplExt_trans h2 h4⟩

theorem rplExt_gLoop (act : ℕ → α → α) (ngen : ℕ) (key : α → ℕ) : ∀ (f i : ℕ) (pts : Array α)
    (edges : Array (Array ℕ)) (par lab : Array ℕ) (idx : Std.HashMap ℕ ℕ),
    Ext par (gLoop act ngen key f i pts edges par lab idx).2.2.1 ∧
      Ext lab (gLoop act ngen key f i pts edges par lab idx).2.2.2
  | 0, _, _, _, _, _, _ => ⟨rplExt_refl _, rplExt_refl _⟩
  | f + 1, i, pts, edges, par, lab, idx => by
    rw [gLoop]
    split
    · have h : Ext par (gStep act ngen key i (pts, par, lab, idx)).2.1 ∧
          Ext lab (gStep act ngen key i (pts, par, lab, idx)).2.2.1 :=
        rplExt_fold act key i (List.range ngen) (pts, par, lab, idx, #[])
      generalize gStep act ngen key i (pts, par, lab, idx) = s at h
      obtain ⟨p, q, l, d, r⟩ := s
      obtain ⟨h3, h4⟩ := rplExt_gLoop act ngen key f (i + 1) p (edges.push r) q l d
      exact ⟨rplExt_trans h.1 h3, rplExt_trans h.2 h4⟩
    · exact ⟨rplExt_refl _, rplExt_refl _⟩

end Ext

theorem rpl_arr_ext {a b : Array ℕ} (hs : a.size = b.size) (h : ∀ j < a.size, a[j]! = b[j]!) :
    a = b :=
  Array.ext hs fun j h1 h2 => by rw [← getElem!_pos a j h1, ← getElem!_pos b j h2]; exact h j h1

theorem rpl_row_size {act : ℕ → ℕ → ℕ} {ngen : ℕ} {valid : ℕ → Bool} {root : ℕ} {c : NatCert}
    (h : natCertOK act ngen valid root c = true) {i : ℕ} (hi : i < c.pts.size) :
    (c.edges[i]!).size = ngen := by
  have := natCertOK_pointOK h hi
  simp only [natPointOK, Bool.and_eq_true, beq_iff_eq] at this
  exact this.1.1.2

public section

theorem natBfs_eq_of_replayT {act : ℕ → ℕ → ℕ} {ngen : ℕ} {valid : ℕ → Bool} {root fuel : ℕ}
    {c : NatCert} (hok : natCertOK act ngen valid root c = true)
    (hrep : replayTOK (fun i k => (c.edges[i]!)[k]!) (fun j => c.par[j]!) (fun j => c.lab[j]!)
      ngen c.pts.size = true)
    (hfuel : c.pts.size ≤ fuel) (hes : c.edges.size = c.pts.size) (hps : c.par.size = c.pts.size)
    (hls : c.lab.size = c.pts.size) (hp0 : c.par[0]! = 0) (hl0 : c.lab[0]! = 0) :
    natBfs act ngen root fuel = c := by
  have hpos := natCertOK_pos hok
  have h0 := natCertOK_root hok
  have hinj : ∀ a < c.pts.size, ∀ b < c.pts.size, c.pts[a]! = c.pts[b]! → a = b :=
    fun a ha b hb e => natCertOK_inj hok ha hb e
  have hE : ∀ i < c.pts.size, ∀ k < ngen, (c.edges[i]!)[k]! < c.pts.size ∧
      c.pts[(c.edges[i]!)[k]!]! = act k c.pts[i]! := fun i hi k hk => natCertOK_edge hok hi hk
  have hpts : (gBfs act ngen id root fuel).1 = c.pts :=
    gBfs_eq_of_replay (key := id) hpos h0 hinj hE (replayTOK_replayOK hrep) hfuel
  have htree := gBfs_tree_of_replayT (key := id) hpos h0 hinj hE hrep hfuel
  have memL : ∀ x, x ∈ c.pts.toList.toFinset ↔ ∃ a < c.pts.size, c.pts[a]! = x := by
    intro x
    rw [List.mem_toFinset, Array.mem_toList_iff, Array.mem_iff_getElem]
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact ⟨a, ha, getElem!_pos c.pts a ha⟩
    · rintro ⟨a, ha, rfl⟩
      exact ⟨a, ha, (getElem!_pos c.pts a ha).symm⟩
  have hroot : root ∈ c.pts.toList.toFinset := (memL _).2 ⟨0, hpos, h0⟩
  have hT : ∀ x ∈ c.pts.toList.toFinset, ∀ k < ngen, act k x ∈ c.pts.toList.toFinset := by
    intro x hx k hk
    obtain ⟨a, ha, rfl⟩ := (memL x).1 hx
    exact (memL _).2 ⟨_, (hE a ha k hk).1, (hE a ha k hk).2⟩
  have hcard : c.pts.toList.toFinset.card ≤ fuel :=
    le_trans (List.toFinset_card_le _) (by rw [Array.length_toList]; exact hfuel)
  obtain ⟨⟨idx, hc⟩, he, hr⟩ := gBfs_out (act := act) (key := id) (fuel := fuel) hroot hT
    (fun _ _ _ _ e => e) hcard
  have hext : Ext #[0] (gBfs act ngen id root fuel).2.2.1 ∧
      Ext #[0] (gBfs act ngen id root fuel).2.2.2 :=
    rplExt_gLoop act ngen id fuel 0 #[root] #[] #[0] #[0] ((∅ : Std.HashMap ℕ ℕ).insert root 0)
  rw [hpts] at he hr hc
  rw [natBfs_eq]
  obtain ⟨p, e, q, l⟩ := c
  dsimp only at *
  simp only [NatCert.mk.injEq]
  refine ⟨hpts, ?_, ?_, ?_⟩
  · refine Array.ext (by rw [he, hes]) fun i h1 h2 => ?_
    have hi : i < p.size := by rw [← he]; exact h1
    rw [← getElem!_pos _ i h1, ← getElem!_pos e i h2]
    refine Array.ext (by rw [(hr i hi).1, rpl_row_size hok hi]) fun k k1 k2 => ?_
    have hk : k < ngen := by rw [← (hr i hi).1]; exact k1
    rw [← getElem!_pos _ k k1, ← getElem!_pos _ k k2]
    obtain ⟨a1, a2⟩ := (hr i hi).2 k hk
    obtain ⟨b1, b2⟩ := hE i hi k hk
    exact hinj _ a1 _ b1 (by rw [a2, b2])
  · refine rpl_arr_ext (by rw [hc.par_size, hps]) fun j hj => ?_
    rcases Nat.eq_zero_or_pos j with rfl | hj0
    · rw [hext.1.2 0 (by simp), hp0]
      rfl
    · exact (htree j hj0 (by rw [← hc.par_size]; exact hj)).1
  · refine rpl_arr_ext (by rw [hc.lab_size, hls]) fun j hj => ?_
    rcases Nat.eq_zero_or_pos j with rfl | hj0
    · rw [hext.2.2 0 (by simp), hl0]
      rfl
    · exact (htree j hj0 (by rw [← hc.lab_size]; exact hj)).2

end

end CFSG.KC.Bfs
