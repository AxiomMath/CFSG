module

public import Certificates.Data.CFSGNative.PSL3Four.Basic
import CFSG.Certificates.Kernel.Spor.BfsReplay

public section

namespace CFSG.KC.L34KSnd

open CFSG.PSL3Four.Native
open CFSG.KS.BfsReplay (forIn_range'_yield push_lt push_eq)

private abbrev DSt (β : Type) := Array Tab × Array β × Std.HashMap Tab Nat

private def dBody {β : Type} (F : Nat → Nat → Tab) (G : Nat → Nat → β) (u v : Nat)
    (s : DSt β) : Id (ForInStep (DSt β)) :=
  if (!s.2.2.contains (F u v)) = true then
    pure (ForInStep.yield (s.1.push (F u v), s.2.1.push (G u v), s.2.2.insert (F u v) s.1.size))
  else pure (ForInStep.yield (s.1, s.2.1, s.2.2))

private def dLoop {β : Type} (N : Nat) (F : Nat → Nat → Tab) (G : Nat → Nat → β) : DSt β :=
  Id.run (forIn (List.range' 0 N) ((#[] : Array Tab), (#[] : Array β), (∅ : Std.HashMap Tab Nat))
    fun u s => pure (ForInStep.yield (Id.run (forIn (List.range' 0 N) s (dBody F G u)))))

private theorem derivedData_eq (n : Nat) (T inv : Array Tab) :
    derivedData n T inv =
      let s1 := dLoop T.size (fun a b => commTab n T[a]! T[b]! inv[a]! inv[b]!) fun a b => (a, b)
      let s2 := dLoop s1.1.size (fun u v => comp n s1.1[u]! s1.1[v]!)
        (fun u v => (s1.2.1[u]!.1, s1.2.1[u]!.2, s1.2.1[v]!.1, s1.2.1[v]!.2))
      (s2.1, s2.2.1) := by
  unfold derivedData dLoop dBody
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size, Id.run, Nat.sub_zero,
    Nat.add_sub_cancel, Nat.div_one]
  rfl

private structure DInv {β : Type} [Inhabited β] (N : Nat) (F : Nat → Nat → Tab)
    (G : Nat → Nat → β) (s : DSt β) : Prop where
  size_eq : s.2.1.size = s.1.size
  inj : ∀ i < s.1.size, ∀ j < s.1.size, s.1[i]! = s.1[j]! → i = j
  mem : ∀ x, s.2.2.contains x = true ↔ ∃ i < s.1.size, s.1[i]! = x
  src : ∀ i < s.1.size, ∃ u < N, ∃ v < N, s.1[i]! = F u v ∧ s.2.1[i]! = G u v

private def Cov {β : Type} (s : DSt β) (x : Tab) : Prop := ∃ i < s.1.size, s.1[i]! = x

private theorem dBody_step {β : Type} [Inhabited β] {N : Nat} {F : Nat → Nat → Tab}
    {G : Nat → Nat → β} {u v : Nat} (hu : u < N) (hv : v < N) {s : DSt β} (hI : DInv N F G s) :
    ∃ s', dBody F G u v s = pure (ForInStep.yield s') ∧ DInv N F G s' ∧ Cov s' (F u v) ∧
      ∀ x, Cov s x → Cov s' x := by
  by_cases hc : s.2.2.contains (F u v) = true
  · exact ⟨(s.1, s.2.1, s.2.2), by simp [dBody, hc], hI, (hI.mem _).1 hc, fun x hx => hx⟩
  · have hc' : s.2.2.contains (F u v) = false := by simpa using hc
    have hpush : ∀ i < s.1.size, (s.1.push (F u v))[i]! = s.1[i]! := fun i hi => push_lt hi
    refine ⟨(s.1.push (F u v), s.2.1.push (G u v), s.2.2.insert (F u v) s.1.size),
      by simp [dBody, hc'], ⟨?_, ?_, ?_, ?_⟩, ⟨s.1.size, by simp, push_eq⟩, ?_⟩
    · simp [hI.size_eq]
    · intro i hi j hj e
      simp only [Array.size_push] at hi hj
      rcases Nat.lt_or_ge i s.1.size with a | a <;> rcases Nat.lt_or_ge j s.1.size with b | b
      · rw [hpush i a, hpush j b] at e
        exact hI.inj i a j b e
      · have hj' : j = s.1.size := by omega
        subst hj'
        rw [hpush i a, push_eq] at e
        exact absurd ((hI.mem _).2 ⟨i, a, e⟩) (by simp [hc'])
      · have hi' : i = s.1.size := by omega
        subst hi'
        rw [hpush j b, push_eq] at e
        exact absurd ((hI.mem _).2 ⟨j, b, e.symm⟩) (by simp [hc'])
      · omega
    · intro y
      rw [Std.HashMap.contains_insert, Bool.or_eq_true, beq_iff_eq, hI.mem]
      simp only [Array.size_push]
      constructor
      · rintro (e | ⟨i, hi, e⟩)
        · exact ⟨s.1.size, by omega, by rw [push_eq, e]⟩
        · exact ⟨i, by omega, by rw [hpush i hi]; exact e⟩
      · rintro ⟨i, hi, e⟩
        rcases Nat.lt_or_ge i s.1.size with a | a
        · exact Or.inr ⟨i, a, by rw [← hpush i a]; exact e⟩
        · have e' : i = s.1.size := by omega
          subst e'
          rw [push_eq] at e
          exact Or.inl e
    · intro i hi
      simp only [Array.size_push] at hi
      rcases Nat.lt_or_ge i s.1.size with a | a
      · obtain ⟨u', hu', v', hv', e1, e2⟩ := hI.src i a
        refine ⟨u', hu', v', hv', ?_, ?_⟩
        · rw [hpush i a]; exact e1
        · rw [push_lt (by rw [hI.size_eq]; exact a : i < s.2.1.size)]; exact e2
      · have e : i = s.1.size := by omega
        subst e
        refine ⟨u, hu, v, hv, push_eq, ?_⟩
        change (s.2.1.push (G u v))[s.1.size]! = G u v
        rw [← hI.size_eq]
        exact push_eq
    · rintro x ⟨i, hi, e⟩
      exact ⟨i, by simp only [Array.size_push]; omega, by rw [hpush i hi]; exact e⟩

private theorem dRow_spec {β : Type} [Inhabited β] {N : Nat} {F : Nat → Nat → Tab}
    {G : Nat → Nat → β} {u : Nat} (hu : u < N) {s : DSt β} (hI : DInv N F G s)
    (hcov : ∀ u' < u, ∀ v' < N, Cov s (F u' v')) :
    DInv N F G (Id.run (forIn (List.range' 0 N) s (dBody F G u))) ∧
      ∀ u' < u + 1, ∀ v' < N, Cov (Id.run (forIn (List.range' 0 N) s (dBody F G u))) (F u' v') := by
  have := forIn_range'_yield N 0 s (dBody F G u)
    (fun j s' => DInv N F G s' ∧ (∀ u' < u, ∀ v' < N, Cov s' (F u' v')) ∧
      ∀ v' < j, Cov s' (F u v'))
    (fun j hj s' hP => by
      rw [Nat.zero_add]
      obtain ⟨s'', e, hI', hnew, hmono⟩ := dBody_step hu (by omega : j < N) hP.1
      refine ⟨s'', e, hI', fun u' hu' v' hv' => hmono _ (hP.2.1 u' hu' v' hv'), fun v' hv' => ?_⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 hv' with h | h
      · exact hmono _ (hP.2.2 v' h)
      · rw [h]; exact hnew)
    ⟨hI, hcov, fun v' hv' => absurd hv' (Nat.not_lt_zero _)⟩
  refine ⟨this.1, fun u' hu' v' hv' => ?_⟩
  rcases Nat.lt_succ_iff_lt_or_eq.1 hu' with h | h
  · exact this.2.1 u' h v' hv'
  · rw [h]; exact this.2.2 v' hv'

private theorem dInv_init {β : Type} [Inhabited β] (N : Nat) (F : Nat → Nat → Tab)
    (G : Nat → Nat → β) :
    DInv N F G ((#[] : Array Tab), (#[] : Array β), (∅ : Std.HashMap Tab Nat)) :=
  ⟨rfl, fun i hi => absurd hi (Nat.not_lt_zero _),
    fun x => by simp, fun i hi => absurd hi (Nat.not_lt_zero _)⟩

private theorem dLoop_spec {β : Type} [Inhabited β] (N : Nat) (F : Nat → Nat → Tab)
    (G : Nat → Nat → β) :
    DInv N F G (dLoop N F G) ∧ ∀ u < N, ∀ v < N, Cov (dLoop N F G) (F u v) :=
  forIn_range'_yield N 0 ((#[] : Array Tab), (#[] : Array β), (∅ : Std.HashMap Tab Nat))
    (fun u s => pure (ForInStep.yield (Id.run (forIn (List.range' 0 N) s (dBody F G u)))))
    (fun u s => DInv N F G s ∧ ∀ u' < u, ∀ v' < N, Cov s (F u' v'))
    (fun j hj s hP => by
      rw [Nat.zero_add]
      have h := dRow_spec (F := F) (G := G) (by omega : j < N) hP.1 hP.2
      exact ⟨_, rfl, h.1, h.2⟩)
    ⟨dInv_init N F G, fun u' hu' => absurd hu' (Nat.not_lt_zero _)⟩

private theorem nodup_of_inj {α : Type} [Inhabited α] {a : Array α}
    (h : ∀ i < a.size, ∀ j < a.size, a[i]! = a[j]! → i = j) : a.toList.Nodup := by
  rw [List.nodup_iff_pairwise_ne, List.pairwise_iff_getElem]
  intro i j hi hj hij e
  have hi' : i < a.size := hi
  have hj' : j < a.size := hj
  have := h i hi' j hj' (by rw [getElem!_pos a i hi', getElem!_pos a j hj']; exact e)
  omega

private theorem derivedData_spec (n : Nat) (T inv : Array Tab) :
    ∃ (cs : Array Tab) (cw : Array (Nat × Nat)) (D : Array Tab)
      (W : Array (Nat × Nat × Nat × Nat)),
      derivedData n T inv = (D, W) ∧
      cw.size = cs.size ∧
      (∀ i < cs.size, ∃ a < T.size, ∃ b < T.size,
        cs[i]! = commTab n T[a]! T[b]! inv[a]! inv[b]! ∧ cw[i]! = (a, b)) ∧
      (∀ a < T.size, ∀ b < T.size,
        ∃ i < cs.size, cs[i]! = commTab n T[a]! T[b]! inv[a]! inv[b]!) ∧
      D.toList.Nodup ∧ W.size = D.size ∧
      (∀ i < D.size, ∃ u < cs.size, ∃ v < cs.size, D[i]! = comp n cs[u]! cs[v]! ∧
        W[i]! = (cw[u]!.1, cw[u]!.2, cw[v]!.1, cw[v]!.2)) ∧
      (∀ u < cs.size, ∀ v < cs.size, ∃ i < D.size, D[i]! = comp n cs[u]! cs[v]!) := by
  rw [derivedData_eq]
  dsimp only
  obtain ⟨hI1, hC1⟩ := dLoop_spec T.size
    (fun a b => commTab n T[a]! T[b]! inv[a]! inv[b]!) (fun a b => (a, b))
  generalize dLoop T.size (fun a b => commTab n T[a]! T[b]! inv[a]! inv[b]!)
    (fun a b => (a, b)) = s1 at hI1 hC1 ⊢
  obtain ⟨hI2, hC2⟩ := dLoop_spec s1.1.size (fun u v => comp n s1.1[u]! s1.1[v]!)
    (fun u v => (s1.2.1[u]!.1, s1.2.1[u]!.2, s1.2.1[v]!.1, s1.2.1[v]!.2))
  generalize dLoop s1.1.size (fun u v => comp n s1.1[u]! s1.1[v]!)
    (fun u v => (s1.2.1[u]!.1, s1.2.1[u]!.2, s1.2.1[v]!.1, s1.2.1[v]!.2)) = s2 at hI2 hC2 ⊢
  exact ⟨s1.1, s1.2.1, s2.1, s2.2.1, rfl, hI1.size_eq, hI1.src, hC1, nodup_of_inj hI2.inj,
    hI2.size_eq, hI2.src, hC2⟩

theorem derivedData_nodup (n : Nat) (T inv : Array Tab) :
    (derivedData n T inv).1.toList.Nodup := by
  obtain ⟨cs, cw, D, W, hD, -, -, -, hnd, -⟩ := derivedData_spec n T inv
  rw [hD]
  exact hnd

theorem derivedData_size (n : Nat) (T inv : Array Tab) :
    (derivedData n T inv).2.size = (derivedData n T inv).1.size := by
  obtain ⟨cs, cw, D, W, hD, -, -, -, -, hsz, -⟩ := derivedData_spec n T inv
  rw [hD]
  exact hsz

theorem derivedData_wit (n : Nat) (T inv : Array Tab) :
    ∀ i < (derivedData n T inv).1.size,
      (derivedData n T inv).2[i]!.1 < T.size ∧ (derivedData n T inv).2[i]!.2.1 < T.size ∧
      (derivedData n T inv).2[i]!.2.2.1 < T.size ∧ (derivedData n T inv).2[i]!.2.2.2 < T.size ∧
      (derivedData n T inv).1[i]! =
        comp n (commTab n T[(derivedData n T inv).2[i]!.1]! T[(derivedData n T inv).2[i]!.2.1]!
            inv[(derivedData n T inv).2[i]!.1]! inv[(derivedData n T inv).2[i]!.2.1]!)
          (commTab n T[(derivedData n T inv).2[i]!.2.2.1]! T[(derivedData n T inv).2[i]!.2.2.2]!
            inv[(derivedData n T inv).2[i]!.2.2.1]! inv[(derivedData n T inv).2[i]!.2.2.2]!) := by
  obtain ⟨cs, cw, D, W, hD, -, hsrc1, -, -, -, hsrc2, -⟩ := derivedData_spec n T inv
  rw [hD]
  intro i hi
  obtain ⟨u, hu, v, hv, hDi, hWi⟩ := hsrc2 i hi
  obtain ⟨a, ha, b, hb, hcu, hwu⟩ := hsrc1 u hu
  obtain ⟨c, hc, d, hd, hcv, hwv⟩ := hsrc1 v hv
  dsimp only
  rw [hWi, hwu, hwv, hDi, hcu, hcv]
  exact ⟨ha, hb, hc, hd, rfl⟩

theorem derivedData_complete (n : Nat) (T inv : Array Tab) :
    ∀ a₁ < T.size, ∀ a₂ < T.size, ∀ a₃ < T.size, ∀ a₄ < T.size,
      comp n (commTab n T[a₁]! T[a₂]! inv[a₁]! inv[a₂]!)
          (commTab n T[a₃]! T[a₄]! inv[a₃]! inv[a₄]!) ∈ (derivedData n T inv).1.toList := by
  obtain ⟨cs, cw, D, W, hD, -, -, hcov1, -, -, -, hcov2⟩ := derivedData_spec n T inv
  rw [hD]
  intro a₁ h₁ a₂ h₂ a₃ h₃ a₄ h₄
  obtain ⟨u, hu, hcu⟩ := hcov1 a₁ h₁ a₂ h₂
  obtain ⟨v, hv, hcv⟩ := hcov1 a₃ h₃ a₄ h₄
  obtain ⟨i, hi, hDi⟩ := hcov2 u hu v hv
  dsimp only
  rw [← hcu, ← hcv, ← hDi, getElem!_pos D i hi]
  exact Array.mem_toList_iff.2 (Array.getElem_mem hi)

end CFSG.KC.L34KSnd

end
