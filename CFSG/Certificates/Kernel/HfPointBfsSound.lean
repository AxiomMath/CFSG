module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeldFixFourCheckInputs
public import CFSG.Certificates.Kernel.MonsterB.CTIBBfsSound
public import Certificates.Data.Kernel.Child3
public import CFSG.Certificates.Kernel.Spor.Loops
public import CFSG.Certificates.Kernel.Spor.RawDefs

public section

namespace CFSG.KC.PointBfs

open CFSG.ComponentClassification.GrSLit.HeldFix CFSG.PSL3Four.Native CFSG.KC.Bfs

abbrev St := Array Nat × Array Nat × Array Nat × Array Bool

@[expose] def innerF (gens : Array (Array Nat)) (h p : Nat) (s : St) (j : Nat) : St :=
  if (!s.2.2.2[(gens[j]!)[p]!]!) = true then
    (s.1.push (gens[j]!)[p]!, s.2.1.push h, s.2.2.1.push j, s.2.2.2.set! (gens[j]!)[p]! true)
  else s

@[expose] def outerF (gens : Array (Array Nat)) (s : St) (h : Nat) : St :=
  if h < s.1.size then (List.range' 0 gens.size).foldl (innerF gens h s.1[h]!) s else s

@[expose] def initS (n root : Nat) : St := (#[root], #[0], #[0], (Array.replicate n false).set! root true)

theorem hfPointBFS_eq (n : Nat) (gens : Array (Array Nat)) (root : Nat) :
    hfPointBFS n gens root =
      (((List.range' 0 n).foldl (outerF gens) (initS n root)).1,
        ((List.range' 0 n).foldl (outerF gens) (initS n root)).2.1,
        ((List.range' 0 n).foldl (outerF gens) (initS n root)).2.2.1) := by
  unfold hfPointBFS
  dsimp only
  rw [Std.Legacy.Range.forIn_eq_forIn_range', forIn_id_eq_foldl, range_size]
  · rw [List.foldl_ext _ (outerF gens) _ fun s h _ => ?_]
    · rfl
    obtain ⟨pts, par, lab, seen⟩ := s
    unfold outerF
    dsimp only
    by_cases hh : h < pts.size
    · simp only [hh, ↓reduceIte]
      rw [Std.Legacy.Range.forIn_eq_forIn_range', forIn_id_eq_foldl, range_size]
      · rw [List.foldl_ext _ (innerF gens h pts[h]!) _ fun s j _ => ?_]
        · rfl
        obtain ⟨pts', par', lab', seen'⟩ := s
        unfold innerF
        dsimp only
        split <;> rfl
      · intro j s
        obtain ⟨pts', par', lab', seen'⟩ := s
        dsimp only
        split
        · exact ⟨_, rfl⟩
        · exact ⟨_, rfl⟩
    · simp only [hh, ↓reduceIte]
      rfl
  · intro h s
    obtain ⟨pts, par, lab, seen⟩ := s
    dsimp only
    split
    · exact ⟨_, rfl⟩
    · exact ⟨_, rfl⟩

theorem hfPositions_eq (n : Nat) (pts : Array Nat) :
    hfPositions n pts =
      (List.range' 0 pts.size).foldl (fun pos i => pos.set! pts[i]! i) (Array.replicate n 0) := by
  unfold hfPositions
  dsimp only
  rw [Std.Legacy.Range.forIn_eq_forIn_range', forIn_id_eq_foldl, range_size]
  · rfl
  · intro i s
    exact ⟨_, rfl⟩

theorem set_get' {α : Type} [Inhabited α] {a : Array α} {i j : Nat} {v : α} (hi : i < a.size) :
    (a.set! i v)[j]! = if j = i then v else a[j]! := by
  by_cases hj : j < a.size
  · have hj' : j < (a.set! i v).size := by simpa using hj
    rw [getElem!_pos _ j hj', getElem!_pos a j hj]
    simp only [Array.set!_eq_setIfInBounds]
    rw [Array.getElem_setIfInBounds]
    by_cases hij : j = i
    · subst hij
      simp
    · rw [ite_eq_right (Ne.symm hij), ite_eq_right hij]
  · have hj' : ¬ j < (a.set! i v).size := by simpa using hj
    have hij : j ≠ i := by omega
    rw [getElem!_neg _ j hj', getElem!_neg a j hj, ite_eq_right hij]

theorem replicate_get {n x : Nat} (hx : x < n) : (Array.replicate n false)[x]! = false := by
  rw [getElem!_pos _ x (by simpa using hx), Array.getElem_replicate]

structure Good (n : Nat) (gens : Array (Array Nat)) (root : Nat) (s : St) : Prop where
  seen_size : s.2.2.2.size = n
  seen_iff : ∀ x < n, s.2.2.2[x]! = true ↔ ∃ i < s.1.size, s.1[i]! = x
  lt : ∀ i < s.1.size, s.1[i]! < n
  inj : ∀ i < s.1.size, ∀ i' < s.1.size, s.1[i]! = s.1[i']! → i = i'
  par_size : s.2.1.size = s.1.size
  lab_size : s.2.2.1.size = s.1.size
  pos : 0 < s.1.size
  root_eq : s.1[0]! = root
  tree : ∀ i, 0 < i → i < s.1.size → s.2.1[i]! < i ∧ s.2.2.1[i]! < gens.size ∧
    (gens[s.2.2.1[i]!]!)[s.1[s.2.1[i]!]!]! = s.1[i]!

structure Grows (s s' : St) : Prop where
  size_le : s.1.size ≤ s'.1.size
  pts : ∀ i < s.1.size, s'.1[i]! = s.1[i]!
  seen : ∀ x : Nat, s.2.2.2[x]! = true → s'.2.2.2[x]! = true

theorem Grows.refl (s : St) : Grows s s := ⟨le_refl _, fun _ _ => rfl, fun _ h => h⟩

theorem Grows.trans {s s' s'' : St} (h1 : Grows s s') (h2 : Grows s' s'') : Grows s s'' :=
  ⟨le_trans h1.size_le h2.size_le, fun i hi => by rw [h2.pts i (lt_of_lt_of_le hi h1.size_le),
    h1.pts i hi], fun x hx => h2.seen x (h1.seen x hx)⟩

variable {n : Nat} {gens : Array (Array Nat)} {root : Nat}

theorem innerF_spec (hg : ∀ j < gens.size, ∀ x < n, (gens[j]!)[x]! < n) {s : St} {h j : Nat}
    (hs : Good n gens root s) (hh : h < s.1.size) (hj : j < gens.size) :
    Good n gens root (innerF gens h s.1[h]! s j) ∧ Grows s (innerF gens h s.1[h]! s j) ∧
      (innerF gens h s.1[h]! s j).2.2.2[(gens[j]!)[s.1[h]!]!]! = true := by
  obtain ⟨pts, par, lab, seen⟩ := s
  have hq : (gens[j]!)[pts[h]!]! < n := hg j hj _ (hs.lt h hh)
  unfold innerF
  dsimp only at hs hh ⊢
  by_cases hn : (!seen[(gens[j]!)[pts[h]!]!]!) = true
  · rw [ite_eq_left hn]
    have hsq : seen[(gens[j]!)[pts[h]!]!]! = false := by simpa using hn
    have hss : (gens[j]!)[pts[h]!]! < seen.size := by rw [hs.seen_size]; exact hq
    have hnew : ∀ i < pts.size, pts[i]! ≠ (gens[j]!)[pts[h]!]! := by
      intro i hi e
      have := (hs.seen_iff _ hq).2 ⟨i, hi, e⟩
      rw [hsq] at this
      exact Bool.false_ne_true this
    refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ?_⟩
    · simp [hs.seen_size]
    · intro x hx
      rw [set_get' hss, Array.size_push]
      by_cases e : x = (gens[j]!)[pts[h]!]!
      · rw [ite_eq_left e]
        refine ⟨fun _ => ⟨pts.size, Nat.lt_succ_self _, by rw [push_get_size, e]⟩, fun _ => rfl⟩
      · rw [ite_eq_right e, hs.seen_iff x hx]
        constructor
        · rintro ⟨i, hi, hx'⟩
          exact ⟨i, Nat.lt_succ_of_lt hi, by rw [push_get_lt _ _ hi, hx']⟩
        · rintro ⟨i, hi, hx'⟩
          rcases Nat.lt_or_ge i pts.size with h1 | h1
          · exact ⟨i, h1, by rw [push_get_lt _ _ h1] at hx'; exact hx'⟩
          · have e' : i = pts.size := by omega
            subst e'
            rw [push_get_size] at hx'
            exact absurd hx'.symm e
    · intro i hi
      rw [Array.size_push] at hi
      rcases Nat.lt_or_ge i pts.size with h1 | h1
      · rw [push_get_lt _ _ h1]
        exact hs.lt i h1
      · have e' : i = pts.size := by omega
        subst e'
        rw [push_get_size]
        exact hq
    · intro i hi i' hi' e
      rw [Array.size_push] at hi hi'
      rcases Nat.lt_or_ge i pts.size with h1 | h1 <;> rcases Nat.lt_or_ge i' pts.size with h2 | h2
      · rw [push_get_lt _ _ h1, push_get_lt _ _ h2] at e
        exact hs.inj i h1 i' h2 e
      · have e' : i' = pts.size := by omega
        subst e'
        rw [push_get_lt _ _ h1, push_get_size] at e
        exact absurd e (hnew i h1)
      · have e' : i = pts.size := by omega
        subst e'
        rw [push_get_size, push_get_lt _ _ h2] at e
        exact absurd e.symm (hnew i' h2)
      · omega
    · rw [Array.size_push, Array.size_push, hs.par_size]
    · rw [Array.size_push, Array.size_push, hs.lab_size]
    · rw [Array.size_push]
      omega
    · rw [push_get_lt _ _ hs.pos]
      exact hs.root_eq
    · intro i hi0 hi
      rw [Array.size_push] at hi
      rcases Nat.lt_or_ge i pts.size with h1 | h1
      · obtain ⟨t1, t2, t3⟩ := hs.tree i hi0 h1
        rw [push_get_lt _ _ (by rw [hs.par_size]; exact h1),
          push_get_lt _ _ (by rw [hs.lab_size]; exact h1), push_get_lt pts _ (lt_trans t1 h1),
          push_get_lt _ _ h1]
        exact ⟨t1, t2, t3⟩
      · have e' : i = pts.size := by omega
        subst e'
        rw [push_get_of_eq _ _ hs.par_size, push_get_of_eq _ _ hs.lab_size, push_get_lt _ _ hh,
          push_get_size]
        exact ⟨hh, hj, rfl⟩
    · simp
    · intro i hi
      exact push_get_lt _ _ hi
    · intro x hx
      rw [set_get' hss]
      split
      · rfl
      · exact hx
    · dsimp only
      rw [set_get' hss, ite_eq_left rfl]
  · rw [ite_eq_right hn]
    refine ⟨hs, Grows.refl _, ?_⟩
    simpa using hn

theorem fold_spec (hg : ∀ j < gens.size, ∀ x < n, (gens[j]!)[x]! < n) {h : Nat} :
    ∀ (m a : Nat) (s : St), Good n gens root s → h < s.1.size → a + m ≤ gens.size →
      Good n gens root ((List.range' a m).foldl (innerF gens h s.1[h]!) s) ∧
      Grows s ((List.range' a m).foldl (innerF gens h s.1[h]!) s) ∧
      ∀ j, a ≤ j → j < a + m →
        ((List.range' a m).foldl (innerF gens h s.1[h]!) s).2.2.2[(gens[j]!)[s.1[h]!]!]! = true
  | 0, _, s, hs, _, _ => ⟨hs, Grows.refl s, fun j a b => absurd b (by omega)⟩
  | m + 1, a, s, hs, hh, hm => by
    rw [List.range'_succ, List.foldl_cons]
    obtain ⟨hs1, hg1, hq1⟩ := innerF_spec hg hs hh (by omega : a < gens.size)
    have hh1 : h < (innerF gens h s.1[h]! s a).1.size := lt_of_lt_of_le hh hg1.size_le
    have hp1 : (innerF gens h s.1[h]! s a).1[h]! = s.1[h]! := hg1.pts h hh
    obtain ⟨hs2, hg2, hq2⟩ := fold_spec hg m (a + 1) _ hs1 hh1 (by omega)
    rw [hp1] at hs2 hg2 hq2
    refine ⟨hs2, hg1.trans hg2, fun j ha hb => ?_⟩
    rcases Nat.lt_or_ge a j with h1 | h1
    · exact hq2 j (by omega) (by omega)
    · have e : j = a := by omega
      subst e
      exact hg2.seen _ hq1

@[expose] def Done (gens : Array (Array Nat)) (h : Nat) (s : St) : Prop :=
  ∀ h' < h, h' < s.1.size → ∀ j < gens.size, s.2.2.2[(gens[j]!)[s.1[h']!]!]! = true

theorem outerF_spec (hg : ∀ j < gens.size, ∀ x < n, (gens[j]!)[x]! < n) {s : St} {h : Nat}
    (hs : Good n gens root s) (hd : Done gens h s) :
    Good n gens root (outerF gens s h) ∧ Done gens (h + 1) (outerF gens s h) := by
  unfold outerF
  by_cases hh : h < s.1.size
  · rw [ite_eq_left hh]
    obtain ⟨hs1, hg1, hq1⟩ := fold_spec hg gens.size 0 s hs hh (by omega)
    refine ⟨hs1, fun h' hh' _ j hj => ?_⟩
    rcases Nat.lt_or_ge h' h with h1 | h1
    · rw [hg1.pts h' (by omega)]
      exact hg1.seen _ (hd h' h1 (by omega) j hj)
    · have e : h' = h := by omega
      subst e
      rw [hg1.pts h' hh]
      exact hq1 j (Nat.zero_le j) (by omega)
  · rw [ite_eq_right hh]
    refine ⟨hs, fun h' hh' hs' j hj => hd h' (by omega) hs' j hj⟩

theorem loop_spec (hg : ∀ j < gens.size, ∀ x < n, (gens[j]!)[x]! < n) :
    ∀ (m a : Nat) (s : St), Good n gens root s → Done gens a s →
      Good n gens root ((List.range' a m).foldl (outerF gens) s) ∧
        Done gens (a + m) ((List.range' a m).foldl (outerF gens) s)
  | 0, a, s, hs, hd => ⟨hs, hd⟩
  | m + 1, a, s, hs, hd => by
    rw [List.range'_succ, List.foldl_cons]
    obtain ⟨hs1, hd1⟩ := outerF_spec hg hs hd
    obtain ⟨hs2, hd2⟩ := loop_spec hg m (a + 1) _ hs1 hd1
    refine ⟨hs2, ?_⟩
    rw [show a + (m + 1) = a + 1 + m by omega]
    exact hd2

theorem init_good (hroot : root < n) : Good n gens root (initS n root) := by
  have hr : root < (Array.replicate n false).size := by simpa using hroot
  refine ⟨by simp [initS], fun x hx => ?_, fun i hi => ?_, fun i hi i' hi' _ => ?_, rfl, rfl,
    by simp [initS], rfl, fun i hi0 hi => ?_⟩
  · simp only [initS]
    rw [set_get' hr]
    constructor
    · intro h
      by_cases e : x = root
      · exact ⟨0, by simp, by simp [e]⟩
      · rw [ite_eq_right e, replicate_get hx] at h
        exact absurd h Bool.false_ne_true
    · rintro ⟨i, hi, e⟩
      have : i = 0 := by simpa using hi
      subst this
      have e' : x = root := by simpa using e.symm
      rw [ite_eq_left e']
  · have : i = 0 := by simpa [initS] using hi
    subst this
    simpa [initS] using hroot
  · have h1 : i = 0 := by simpa [initS] using hi
    have h2 : i' = 0 := by simpa [initS] using hi'
    rw [h1, h2]
  · have : i = 0 := by simpa [initS] using hi
    omega

inductive OrbR (gens : Array (Array Nat)) (root : Nat) : Nat → Prop
  | root : OrbR gens root root
  | step {x : Nat} (j : Nat) : j < gens.size → OrbR gens root x → OrbR gens root ((gens[j]!)[x]!)

theorem positions_spec {pts : Array Nat} (hlt : ∀ i < pts.size, pts[i]! < n)
    (hinj : ∀ i < pts.size, ∀ i' < pts.size, pts[i]! = pts[i']! → i = i') :
    ∀ k ≤ pts.size,
      ((List.range' 0 k).foldl (fun pos i => pos.set! pts[i]! i) (Array.replicate n 0)).size = n ∧
      ∀ i < k, ((List.range' 0 k).foldl (fun pos i => pos.set! pts[i]! i)
        (Array.replicate n 0))[pts[i]!]! = i
  | 0, _ => ⟨by simp, fun i hi => absurd hi (by omega)⟩
  | k + 1, hk => by
    obtain ⟨h1, h2⟩ := positions_spec hlt hinj k (by omega)
    rw [List.range'_concat, List.foldl_append, List.foldl_cons, List.foldl_nil, Nat.one_mul,
      Nat.zero_add]
    have hs : pts[k]! < ((List.range' 0 k).foldl (fun pos i => pos.set! pts[i]! i)
        (Array.replicate n 0)).size := by rw [h1]; exact hlt k (by omega)
    refine ⟨by rw [Array.size_set!, h1], fun i hi => ?_⟩
    rw [set_get' hs]
    by_cases e : pts[i]! = pts[k]!
    · rw [ite_eq_left e]
      exact (hinj i (by omega) k (by omega) e).symm
    · rw [ite_eq_right e]
      have hik : i < k := by
        rcases Nat.lt_or_ge i k with h | h
        · exact h
        · have : i = k := by omega
          subst this
          exact absurd rfl e
      exact h2 i hik

theorem hfPointTreeOK_of_orbit (hroot : root < n)
    (hg : ∀ j < gens.size, ∀ x < n, (gens[j]!)[x]! < n) (horb : ∀ x < n, OrbR gens root x) :
    hfPointTreeOK n gens root (hfPointBFS n gens root).1 (hfPointBFS n gens root).2.1
      (hfPointBFS n gens root).2.2 (hfPositions n (hfPointBFS n gens root).1) = true := by
  rw [hfPointBFS_eq]
  dsimp only
  generalize hS : (List.range' 0 n).foldl (outerF gens) (initS n root) = s
  obtain ⟨hs, hd⟩ := loop_spec (root := root) hg n 0 (initS n root) (init_good hroot)
    (fun h' hh' => absurd hh' (by omega))
  rw [hS] at hs hd
  rw [Nat.zero_add] at hd
  obtain ⟨pts, par, lab, seen⟩ := s
  dsimp only at hs hd ⊢
  have hle : pts.size ≤ n := by
    have := Fintype.card_le_of_injective (fun i : Fin pts.size => (⟨pts[i.val]!, hs.lt i i.2⟩ :
      Fin n)) (fun i i' e => Fin.ext (hs.inj i i.2 i' i'.2 (congrArg Fin.val e)))
    simpa using this
  have hmem : ∀ x, OrbR gens root x → ∃ i < pts.size, pts[i]! = x := by
    intro x hx
    induction hx with
    | root => exact ⟨0, hs.pos, hs.root_eq⟩
    | step j hj _ ih =>
      obtain ⟨i, hi, rfl⟩ := ih
      exact (hs.seen_iff _ (hg j hj _ (hs.lt i hi))).1 (hd i (by omega) hi j hj)
  have hall : ∀ x < n, ∃ i < pts.size, pts[i]! = x := fun x hx => hmem x (horb x hx)
  have hge : n ≤ pts.size := by
    have hsub : Finset.range n ⊆ (Finset.range pts.size).image (fun i => pts[i]!) := by
      intro x hx
      obtain ⟨i, hi, e⟩ := hall x (Finset.mem_range.1 hx)
      exact Finset.mem_image.2 ⟨i, Finset.mem_range.2 hi, e⟩
    have := Finset.card_le_card hsub
    rw [Finset.card_range] at this
    exact le_trans this (le_trans Finset.card_image_le (by rw [Finset.card_range]))
  have hsz : pts.size = n := le_antisymm hle hge
  obtain ⟨hps, hpos⟩ := positions_spec hs.lt hs.inj pts.size le_rfl
  rw [hfPositions_eq]
  unfold hfPointTreeOK allBelow
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range]
  refine ⟨⟨⟨hsz, hs.root_eq⟩, fun i hi => ?_⟩, fun x hx => ?_⟩
  · rcases Nat.eq_zero_or_pos i with h0 | h0
    · simp [h0]
    · obtain ⟨t1, t2, t3⟩ := hs.tree i h0 (lt_of_lt_of_eq hi hsz.symm)
      dsimp only at t1 t2 t3
      simp only [t1, t2, t3, decide_true, Bool.and_true, beq_self_eq_true, Bool.or_true]
  · obtain ⟨i, hi, rfl⟩ := hall x hx
    rw [hpos i hi]
    have hin : i < n := lt_of_lt_of_eq hi hsz
    simp [hin]

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw in
theorem orbR_of_forestK {w kS : Nat} {PS FP FL FD : Nat → Nat}
    (h : CFSG.KC.Child3.forestK n w PS kS [root] FP FL FD = true) (hs : gens.size = kS)
    (hg : ∀ j < kS, gens[j]! = unpack n w (PS j)) : ∀ x < n, OrbR gens root x := by
  have key : ∀ d, ∀ x < n, FD x = d → OrbR gens root x := by
    intro d
    induction d using Nat.strong_induction_on with
    | _ d ih =>
      intro x hx hd
      have hx' := allN_spec h x hx
      cases h1 : Nat.beq (FD x) 0 <;> cases h2 : [root].contains x <;>
        simp only [h1, h2] at hx'
      all_goals first
        | (have e : x = root := by simpa using h2
           subst e
           exact OrbR.root)
        | (obtain ⟨t1, t2⟩ := (bAnd_iff _ _).1 hx'
           obtain ⟨t3, t4⟩ := (bAnd_iff _ _).1 t2
           obtain ⟨t5, t6⟩ := (bAnd_iff _ _).1 t4
           have hp : FP x < n := Nat.blt_eq.mp t1
           have hl : FL x < kS := Nat.blt_eq.mp t3
           have hdd : FD (FP x) < FD x := Nat.blt_eq.mp t5
           have he : pg w (mask w) (PS (FL x)) (FP x) = x := Nat.eq_of_beq_eq_true t6
           have hxe : (gens[FL x]!)[FP x]! = x := by
             rw [hg _ hl, unpack, getElem!_pos _ _ (by rw [Array.size_ofFn]; exact hp),
               Array.getElem_ofFn, he]
           rw [← hxe]
           exact OrbR.step _ (by rw [hs]; exact hl) (ih _ (hd ▸ hdd) _ hp rfl))
  exact fun x hx => key _ x hx rfl

end CFSG.KC.PointBfs

end
