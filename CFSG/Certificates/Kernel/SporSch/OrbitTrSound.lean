
module

public import CFSG.Sporadic.Co2Schreier.ThirdCheckInputs
public import CFSG.Certificates.Kernel.Spor.RawOrbBfs

public section

namespace CFSG.Sporadic.Co2Schreier.OrbTr

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.KS.Raw

structure Facts (G : Subgroup (Equiv.Perm (Fin 2300))) (steps : Array (Array ℕ)) (b : ℕ)
    (T : TLev) : Prop where
  tr_size : T.tr.size = T.pts.size
  pos : 0 < T.pts.size
  le : T.pts.size ≤ 2300
  root : T.pts[0]! = b
  tr_zero : T.tr[0]! = idA 2300
  pt_lt : ∀ k < T.pts.size, T.pts[k]! < 2300
  inj : ∀ k < T.pts.size, ∀ k' < T.pts.size, T.pts[k]! = T.pts[k']! → k = k'
  tr_rep : ∀ k < T.pts.size, (∃ g ∈ G, Rep 2300 T.tr[k]! g) ∧ (T.tr[k]!)[b]! = T.pts[k]!
  closed : ∀ h < T.pts.size, ∀ s ∈ steps, ∃ k < T.pts.size, T.pts[k]! = s[T.pts[h]!]!
  edge : ∀ k < T.pts.size, 0 < k → ∃ h < k, ∃ s ∈ steps, s[T.pts[h]!]! = T.pts[k]!

structure Inv (G : Subgroup (Equiv.Perm (Fin 2300))) (steps : Array (Array ℕ)) (b a : ℕ)
    (pts : Array ℕ) (tr : Array (Array ℕ)) (seen : Array Bool) : Prop where
  tr_size : tr.size = pts.size
  pos : 0 < pts.size
  seen_size : seen.size = 2300
  root : pts[0]! = b
  tr_zero : tr[0]! = idA 2300
  pt : ∀ k < pts.size, pts[k]! < 2300 ∧ seen[pts[k]!]! = true
  seen_pt : ∀ z < 2300, seen[z]! = true → ∃ k < pts.size, pts[k]! = z
  inj : ∀ k < pts.size, ∀ k' < pts.size, pts[k]! = pts[k']! → k = k'
  tr_rep : ∀ k < pts.size, (∃ g ∈ G, Rep 2300 tr[k]! g) ∧ (tr[k]!)[b]! = pts[k]!
  closed : ∀ h < a, h < pts.size → ∀ s ∈ steps, seen[s[pts[h]!]!]! = true
  edge : ∀ k < pts.size, 0 < k → ∃ h < k, ∃ s ∈ steps, s[pts[h]!]! = pts[k]!

theorem seen_mono {seen : Array Bool} {y z : ℕ} (h : seen[z]! = true) :
    (seen.set! y true)[z]! = true := by
  by_cases hz : z = y
  · subst hz
    by_cases hs : z < seen.size
    · rw [Array.getElem!_set!_self _ _ _ hs]
    · rw [getElem!_neg seen z hs] at h
      exact absurd h (by decide)
  · rw [Array.getElem!_set!_ne _ _ _ _ (Ne.symm hz)]
    exact h

theorem le_of_inj {pts : Array ℕ} (hlt : ∀ k < pts.size, pts[k]! < 2300)
    (hinj : ∀ k < pts.size, ∀ k' < pts.size, pts[k]! = pts[k']! → k = k') :
    pts.size ≤ 2300 := by
  have hsub : (Finset.range pts.size).image (fun k => pts[k]!) ⊆ Finset.range 2300 := by
    intro z hz
    rw [Finset.mem_image] at hz
    obtain ⟨k, hk, rfl⟩ := hz
    exact Finset.mem_range.2 (hlt k (Finset.mem_range.1 hk))
  have hc := Finset.card_le_card hsub
  rwa [Finset.card_image_of_injOn (fun k hk k' hk' e => hinj k (by simpa using hk) k'
    (by simpa using hk') e), Finset.card_range, Finset.card_range] at hc

theorem inv_push {G : Subgroup (Equiv.Perm (Fin 2300))} {steps : Array (Array ℕ)} {b a : ℕ}
    {pts : Array ℕ} {tr : Array (Array ℕ)} {seen : Array Bool}
    (hI : Inv G steps b a pts tr seen) {g : Array ℕ} {σ : Equiv.Perm (Fin 2300)}
    (hσ : σ ∈ G) (hg : Rep 2300 g σ) (hgs : g ∈ steps) {h : ℕ} (hh : h < pts.size)
    (ha : a ≤ pts.size)
    (hy : seen[g[pts[h]!]!]! = false) :
    Inv G steps b a (pts.push g[pts[h]!]!) (tr.push (compA 2300 g tr[h]!))
      (seen.set! g[pts[h]!]! true) := by
  set x := pts[h]! with hx
  set y := g[x]! with hydef
  have hxn : x < 2300 := (hI.pt h hh).1
  have hyn : y < 2300 := hg.lt hxn
  have hb : b < 2300 := by
    have := (hI.pt 0 hI.pos).1
    rwa [hI.root] at this
  have absent : ∀ k < pts.size, pts[k]! ≠ y := by
    intro k hk e
    have := (hI.pt k hk).2
    rw [e, hy] at this
    exact absurd this (by decide)
  have sy : (seen.set! y true)[y]! = true :=
    Array.getElem!_set!_self _ _ _ (by rw [hI.seen_size]; exact hyn)
  have pts_lt : ∀ k < pts.size, (pts.push y)[k]! = pts[k]! := fun k hk => push_get_lt hk
  have pts_m : (pts.push y)[pts.size]! = y := push_get_eq rfl
  have tr_lt : ∀ k < pts.size, (tr.push (compA 2300 g tr[h]!))[k]! = tr[k]! := fun k hk =>
    push_get_lt (by rw [hI.tr_size]; exact hk)
  have tr_m : (tr.push (compA 2300 g tr[h]!))[pts.size]! = compA 2300 g tr[h]! :=
    push_get_eq hI.tr_size.symm
  have hsz : (pts.push y).size = pts.size + 1 := by simp
  refine ⟨by simp [hI.tr_size], by simp, by rw [Array.size_set!, hI.seen_size], ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_⟩
  · rw [pts_lt 0 hI.pos]
    exact hI.root
  · rw [tr_lt 0 hI.pos]
    exact hI.tr_zero
  · intro k hk
    rw [hsz] at hk
    rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk | rfl
    · rw [pts_lt k hk]
      exact ⟨(hI.pt k hk).1, seen_mono (hI.pt k hk).2⟩
    · rw [pts_m]
      exact ⟨hyn, sy⟩
  · intro z hz hs
    by_cases hzy : z = y
    · exact ⟨pts.size, by rw [hsz]; omega, by rw [pts_m, hzy]⟩
    · rw [Array.getElem!_set!_ne _ _ _ _ (Ne.symm hzy)] at hs
      obtain ⟨k, hk, e⟩ := hI.seen_pt z hz hs
      exact ⟨k, by rw [hsz]; omega, by rw [pts_lt k hk, e]⟩
  · intro k hk k' hk' e
    rw [hsz] at hk hk'
    rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk | rfl <;>
      rcases Nat.lt_succ_iff_lt_or_eq.1 hk' with hk' | rfl
    · rw [pts_lt k hk, pts_lt k' hk'] at e
      exact hI.inj k hk k' hk' e
    · rw [pts_lt k hk, pts_m] at e
      exact absurd e (absent k hk)
    · rw [pts_m, pts_lt k' hk'] at e
      exact absurd e.symm (absent k' hk')
    · rfl
  · intro k hk
    rw [hsz] at hk
    rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk | rfl
    · rw [tr_lt k hk, pts_lt k hk]
      exact hI.tr_rep k hk
    · rw [tr_m, pts_m]
      obtain ⟨⟨τ, hτ, hrep⟩, hb'⟩ := hI.tr_rep h hh
      refine ⟨⟨σ * τ, G.mul_mem hσ hτ, rep_compA hg hrep⟩, ?_⟩
      rw [compA_get hb, hb']
  · intro h' hh' _ s hs
    have hlt : h' < pts.size := by omega
    rw [pts_lt h' hlt]
    exact seen_mono (hI.closed h' hh' hlt s hs)
  · intro k hk hk0
    rw [hsz] at hk
    rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk | rfl
    · obtain ⟨h', hh', s, hs, e⟩ := hI.edge k hk hk0
      refine ⟨h', hh', s, hs, ?_⟩
      rw [pts_lt k hk, pts_lt h' (by omega)]
      exact e
    · rw [pts_m]
      exact ⟨h, hh, g, hgs, by rw [pts_lt h hh]⟩

theorem forIn_array_eq {α β : Type} [Inhabited α] (xs : Array α) (init : β)
    (f : α → β → Id (ForInStep β)) :
    forIn xs init f = forIn [0:xs.size] init (fun j b => f xs[j]! b) := by
  rw [← Array.forIn_toList, Std.Legacy.Range.forIn_eq_forIn_range']
  have e : xs.toList = (List.range' 0 ([0:xs.size] : Std.Legacy.Range).size).map
      (fun j => xs[j]!) := by
    apply List.ext_getElem
    · simp [Std.Legacy.Range.size]
    · intro i h1 h2
      simp [getElem!_pos xs i (by simpa using h1)]
  rw [e, List.forIn_map]

theorem stepP_yield3 {β γ δ : Type} {I : ℕ → β × γ × δ → Prop} {Q : β × γ × δ → Prop} {a : ℕ}
    {X : β × γ × δ} (h : I (a + 1) X) :
    CFSG.KS.Raw.Orb.StepP I Q a (.yield (X.1, X.2.1, X.2.2)) := h

theorem singleton_get {α : Type} [Inhabited α] (x : α) : (#[x] : Array α)[0]! = x := rfl

theorem mem_steps {steps : Array (Array ℕ)} {s : Array ℕ} (hs : s ∈ steps) :
    ∃ j < steps.size, steps[j]! = s := by
  obtain ⟨j, hj, rfl⟩ := Array.getElem_of_mem hs
  exact ⟨j, hj, getElem!_pos steps j hj⟩

theorem inv_init (G : Subgroup (Equiv.Perm (Fin 2300))) (steps : Array (Array ℕ)) {b : ℕ}
    (hb : b < 2300) (st : Array ℕ × Array (Array ℕ) × Array Bool)
    (hst : st = (#[b], #[idA 2300], (Array.replicate 2300 false).set! b true)) :
    Inv G steps b 0 st.1 st.2.1 st.2.2 := by
  subst hst
  dsimp only
  have sb : ((Array.replicate 2300 false).set! b true)[b]! = true :=
    Array.getElem!_set!_self _ _ _ (by simpa using hb)
  have h1 : (#[b] : Array ℕ).size = 1 := by
    simp only [List.size_toArray, List.length_cons, List.length_nil]
  constructor
  · simp only [List.size_toArray, List.length_cons, List.length_nil]
  · rw [h1]
    exact Nat.one_pos
  · rw [Array.size_set!, Array.size_replicate]
  · exact singleton_get b
  · exact singleton_get _
  · intro k hk
    have : k = 0 := by rw [h1] at hk; omega
    subst this
    rw [singleton_get]
    exact ⟨hb, sb⟩
  · intro z hz hs
    by_cases hzb : z = b
    · exact ⟨0, by rw [h1]; exact Nat.one_pos, by rw [hzb]; exact singleton_get b⟩
    · rw [Array.getElem!_set!_ne _ _ _ _ (Ne.symm hzb),
        getElem!_pos _ z (by simpa using hz), Array.getElem_replicate] at hs
      exact absurd hs (by decide)
  · intro k hk k' hk' _
    rw [h1] at hk hk'
    omega
  · intro k hk
    have : k = 0 := by rw [h1] at hk; omega
    subst this
    rw [singleton_get, singleton_get]
    exact ⟨⟨1, G.one_mem, rep_idA⟩, idA_get hb⟩
  · intro h hh
    exact absurd hh (Nat.not_lt_zero h)
  · intro k hk hk0
    rw [h1] at hk
    omega

theorem orbitTr_facts (G : Subgroup (Equiv.Perm (Fin 2300))) (steps : Array (Array ℕ)) {b : ℕ}
    (hb : b < 2300) (hs : ∀ j < steps.size, ∃ g ∈ G, Rep 2300 steps[j]! g) :
    Facts G steps b (orbitTr steps b) := by
  have hs' : ∀ s ∈ steps, ∃ g ∈ G, Rep 2300 s g := fun s hm => by
    obtain ⟨j, hj, rfl⟩ := mem_steps hm
    exact hs j hj
  have hfin : ∀ st : Array ℕ × Array (Array ℕ) × Array Bool,
      Inv G steps b 2300 st.1 st.2.1 st.2.2 → Facts G steps b ⟨st.1, st.2.1⟩ := by
    intro st hI
    have hle := le_of_inj (fun k hk => (hI.pt k hk).1) hI.inj
    refine ⟨hI.tr_size, hI.pos, hle, hI.root, hI.tr_zero, fun k hk => (hI.pt k hk).1, hI.inj,
      hI.tr_rep, fun h hh s hm => ?_, hI.edge⟩
    obtain ⟨g, -, hg⟩ := hs' s hm
    exact hI.seen_pt _ (hg.lt (hI.pt h hh).1) (hI.closed h (lt_of_lt_of_le hh hle) hh s hm)
  unfold orbitTr
  apply hfin
  refine CFSG.KS.Raw.Orb.forIn_range_idx 2300 _ _
    (fun a (st : Array ℕ × Array (Array ℕ) × Array Bool) => Inv G steps b a st.1 st.2.1 st.2.2)
    (fun st => Inv G steps b 2300 st.1 st.2.1 st.2.2) (inv_init G steps hb _ rfl) ?_ (fun _ h => h)
  intro a _ st hI
  dsimp only
  split
  · rename_i hlt
    simp only [Id.run_bind, Id.run_pure]
    rw [forIn_array_eq]
    refine stepP_yield3 (CFSG.KS.Raw.Orb.forIn_range_idx steps.size _ _
      (fun j (st' : Array ℕ × Array (Array ℕ) × Array Bool) =>
        Inv G steps b a st'.1 st'.2.1 st'.2.2 ∧ a < st'.1.size ∧ st'.1[a]! = st.1[a]! ∧
          st'.2.1[a]! = st.2.1[a]! ∧
          ∀ j' < j, st'.2.2[(steps[j']!)[st.1[a]!]!]! = true)
      (fun st' => Inv G steps b (a + 1) st'.1 st'.2.1 st'.2.2)
      ⟨hI, hlt, rfl, rfl, fun j' hj' => absurd hj' (Nat.not_lt_zero j')⟩ ?_ ?_)
    · intro j hj st' hJ
      obtain ⟨hI', ha', hx, htx, hcl⟩ := hJ
      obtain ⟨σ, hσ, hg⟩ := hs j hj
      split
      · rename_i hy
        simp only [Bool.not_eq_true', Bool.not_eq_eq_eq_not, Bool.not_true] at hy
        rw [← hx] at hy
        have hP := inv_push hI' hσ hg
          (by rw [getElem!_pos steps j hj]; exact Array.getElem_mem hj) ha' ha'.le hy
        rw [hx, htx] at hP
        refine ⟨hP, by simp; omega, by rw [push_get_lt ha', hx], ?_, fun j' hj' => ?_⟩
        · rw [push_get_lt (by rw [hI'.tr_size]; exact ha'), htx]
        · rcases Nat.lt_succ_iff_lt_or_eq.1 hj' with hj' | rfl
          · exact seen_mono (hcl j' hj')
          · exact Array.getElem!_set!_self _ _ _
              (by rw [hI'.seen_size]; exact hg.lt (by rw [← hx]; exact (hI'.pt a ha').1))
      · rename_i hy
        simp only [Bool.not_eq_true', Bool.not_eq_eq_eq_not, Bool.not_false] at hy
        refine ⟨hI', ha', hx, htx, fun j' hj' => ?_⟩
        rcases Nat.lt_succ_iff_lt_or_eq.1 hj' with hj' | rfl
        · exact hcl j' hj'
        · simpa using hy
    · intro st' hJ
      obtain ⟨hI', ha', hx, -, hcl⟩ := hJ
      refine ⟨hI'.tr_size, hI'.pos, hI'.seen_size, hI'.root, hI'.tr_zero, hI'.pt, hI'.seen_pt,
        hI'.inj, hI'.tr_rep, fun h hh hh' s hm => ?_, hI'.edge⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 hh with hh | rfl
      · exact hI'.closed h hh hh' s hm
      · obtain ⟨j, hj, rfl⟩ := mem_steps hm
        rw [hx]
        exact hcl j hj
  · rename_i hlt
    refine ⟨hI.tr_size, hI.pos, hI.seen_size, hI.root, hI.tr_zero, hI.pt, hI.seen_pt, hI.inj,
      hI.tr_rep, fun h hh hh' s hm => hI.closed h (by dsimp only at hh'; omega) hh' s hm,
      hI.edge⟩

end CFSG.Sporadic.Co2Schreier.OrbTr

end
