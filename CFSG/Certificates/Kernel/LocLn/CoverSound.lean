module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinLeafLocLin

public section

namespace CFSG.KS.LocLn

open CFSG.CGT.PushingUpLit.SolKNA.R4.TwinLeaf.Loc

theorem foldl_pres {α β : Type _} (P : α → Prop) (f : α → β → α) (l : List β) (m : α)
    (h : ∀ m b, b ∈ l → P m → P (f m b)) (hm : P m) : P (l.foldl f m) := by
  induction l generalizing m with
  | nil => exact hm
  | cons a t ih =>
    exact ih (f m a) (fun m b hb hP => h m b (List.mem_cons_of_mem a hb) hP)
      (h m a List.mem_cons_self hm)

theorem foldl_hit {α β : Type _} (P : α → Prop) (f : α → β → α) (l : List β) (m : α) (b : β)
    (hb : b ∈ l) (hmono : ∀ m b, P m → P (f m b)) (hhit : ∀ m, P (f m b)) :
    P (l.foldl f m) := by
  induction l generalizing m with
  | nil => simp at hb
  | cons a t ih =>
    rcases List.mem_cons.1 hb with rfl | hb
    · exact foldl_pres P f t _ (fun m b _ hP => hmono m b hP) (hhit m)
    · exact ih (f m a) hb

theorem ofDigits3_map_inj {m : ℕ} {f g : ℕ → ℕ} (hf : ∀ k, f k < 3) (hg : ∀ k, g k < 3)
    (h : Nat.ofDigits 3 ((List.range m).map f) = Nat.ofDigits 3 ((List.range m).map g)) :
    ∀ k < m, f k = g k := by
  have := Nat.ofDigits_inj_of_len_eq (by norm_num) (by simp)
    (by simpa using fun k _ => hf k) (by simpa using fun k _ => hg k) h
  intro k hk
  exact (List.map_inj_left.1 this) k (List.mem_range.2 hk)

theorem eltEq_of_key {n : ℕ} {x y : Array ℕ} (hx : eE n x < 2) (hy : eE n y < 2)
    (h : eltKey n x = eltKey n y) : eltEq n x y = true := by
  unfold eltKey at h
  have hε : eE n x = eE n y := by omega
  have hc : kA n x = kA n y ∨ kA n x = kN n y ∨ kN n x = kA n y ∨ kN n x = kN n y := by omega
  simp only [eltEq, Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true, List.all_eq_true,
    List.mem_range, hε, true_and]
  rcases hc with hc | hc | hc | hc
  · have := ofDigits3_map_inj (fun k => Nat.mod_lt _ (by norm_num))
      (fun k => Nat.mod_lt _ (by norm_num)) hc
    exact Or.inl fun k hk => by simpa using this k hk
  · have := ofDigits3_map_inj (fun k => Nat.mod_lt _ (by norm_num))
      (fun k => Nat.mod_lt _ (by norm_num)) hc
    refine Or.inr fun k hk => ?_
    have h1 := this k hk
    omega
  · have := ofDigits3_map_inj (fun k => Nat.mod_lt _ (by norm_num))
      (fun k => Nat.mod_lt _ (by norm_num)) hc
    refine Or.inr fun k hk => ?_
    have h1 := this k hk
    omega
  · have := ofDigits3_map_inj (fun k => Nat.mod_lt _ (by norm_num))
      (fun k => Nat.mod_lt _ (by norm_num)) hc
    refine Or.inl fun k hk => ?_
    have h1 := this k hk
    omega

theorem locIdx_fold {n : ℕ} {pts : Array (Array ℕ)}
    (hkey : ∀ i < pts.size, ∀ j < pts.size, eltKey n pts[i]! = eltKey n pts[j]! → i = j) :
    ∀ m ≤ pts.size,
      (∀ i < m, ((List.range m).foldl (fun mp i => mp.insert (eltKey n pts[i]!) i)
        (∅ : Std.HashMap ℕ ℕ))[eltKey n pts[i]!]? = some i) ∧
      (∀ k v, ((List.range m).foldl (fun mp i => mp.insert (eltKey n pts[i]!) i)
        (∅ : Std.HashMap ℕ ℕ))[k]? = some v → v < m ∧ eltKey n pts[v]! = k) := by
  intro m
  induction m with
  | zero => intro _; simp
  | succ m ih =>
    intro hm
    obtain ⟨ih1, ih2⟩ := ih (by omega)
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    refine ⟨fun i hi => ?_, fun k v hkv => ?_⟩
    · rw [Std.HashMap.getElem?_insert]
      by_cases him : i = m
      · subst him; simp
      · have hne : eltKey n pts[m]! ≠ eltKey n pts[i]! := fun he =>
          him (hkey i (by omega) m (by omega) he.symm)
        simp only [beq_iff_eq, hne, if_false]
        exact ih1 i (by omega)
    · rw [Std.HashMap.getElem?_insert] at hkv
      by_cases hk : eltKey n pts[m]! = k
      · simp only [beq_iff_eq, hk, if_true, Option.some.injEq] at hkv
        subst hkv; exact ⟨by omega, hk⟩
      · simp only [beq_iff_eq, hk, if_false] at hkv
        have := ih2 k v hkv
        exact ⟨by omega, this.2⟩

theorem locIdx_self {n : ℕ} {pts : Array (Array ℕ)}
    (hkey : ∀ i < pts.size, ∀ j < pts.size, eltKey n pts[i]! = eltKey n pts[j]! → i = j)
    {i : ℕ} (hi : i < pts.size) : (locIdx n pts).get? (eltKey n pts[i]!) = some i := by
  rw [Std.HashMap.get?_eq_getElem?]
  exact (locIdx_fold hkey pts.size le_rfl).1 i hi

theorem locIdx_spec {n : ℕ} {pts : Array (Array ℕ)}
    (hkey : ∀ i < pts.size, ∀ j < pts.size, eltKey n pts[i]! = eltKey n pts[j]! → i = j)
    {k v : ℕ} (h : (locIdx n pts).get? k = some v) : v < pts.size ∧ eltKey n pts[v]! = k := by
  rw [Std.HashMap.get?_eq_getElem?] at h
  exact (locIdx_fold hkey pts.size le_rfl).2 k v h

def CovInv (n : ℕ) (pts : Array (Array ℕ)) (reps : Array LocRep)
    (m : Std.HashMap (ℕ × ℕ) (ℕ × ℕ)) : Prop :=
  ∀ p v, m.get? p = some v → v.1 < reps.size ∧ v.2 < pts.size ∧
    (locIdx n pts).get? (eltKey n (eltConj n pts[v.2]! reps[v.1]!.x)) = some p.1 ∧
    (locIdx n pts).get? (eltKey n (eltConj n pts[v.2]! reps[v.1]!.t)) = some p.2

theorem locCov_inv {n : ℕ} {pts : Array (Array ℕ)} {reps : Array LocRep} :
    ∀ p v, (locCov n pts reps).get? p = some v → v.1 < reps.size ∧ v.2 < pts.size ∧
      (locIdx n pts).get? (eltKey n (eltConj n pts[v.2]! reps[v.1]!.x)) = some p.1 ∧
      (locIdx n pts).get? (eltKey n (eltConj n pts[v.2]! reps[v.1]!.t)) = some p.2 := by
  unfold locCov
  dsimp only
  refine foldl_pres (CovInv n pts reps) _ _ _ ?_ ?_
  · intro m ri hri hm
    refine foldl_pres (CovInv n pts reps) _ _ _ ?_ hm
    intro m si hsi hm'
    unfold CovInv at hm' ⊢
    split
    next ix it h1 h2 =>
      intro p v hpv
      rw [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert] at hpv
      by_cases hp : (ix, it) = p
      · subst hp
        simp only [beq_self_eq_true, if_true, Option.some.injEq] at hpv
        subst hpv
        exact ⟨List.mem_range.1 hri, List.mem_range.1 hsi, h1, h2⟩
      · simp only [beq_iff_eq, hp, if_false] at hpv
        exact hm' p v (by rwa [Std.HashMap.get?_eq_getElem?])
    next => exact hm'
  · unfold CovInv
    intro p v h
    simp [Std.HashMap.get?_eq_getElem?] at h

theorem locCov_hit {n : ℕ} {pts : Array (Array ℕ)} {reps : Array LocRep} {i j ri si : ℕ}
    (hri : ri < reps.size) (hsi : si < pts.size)
    (h1 : (locIdx n pts).get? (eltKey n (eltConj n pts[si]! reps[ri]!.x)) = some i)
    (h2 : (locIdx n pts).get? (eltKey n (eltConj n pts[si]! reps[ri]!.t)) = some j) :
    ((locCov n pts reps).get? (i, j)).isSome = true := by
  have mono : ∀ (m : Std.HashMap (ℕ × ℕ) (ℕ × ℕ)) (k : ℕ × ℕ) (v : ℕ × ℕ),
      (m.get? (i, j)).isSome = true → ((m.insert k v).get? (i, j)).isSome = true := by
    intro m k v h
    rw [Std.HashMap.get?_eq_getElem?] at h ⊢
    rw [Std.HashMap.getElem?_insert]
    split <;> simp_all
  have imono : ∀ (ri' : ℕ) (m : Std.HashMap (ℕ × ℕ) (ℕ × ℕ)) (si' : ℕ),
      (m.get? (i, j)).isSome = true →
      ((match (locIdx n pts).get? (eltKey n (eltConj n pts[si']! reps[ri']!.x)),
          (locIdx n pts).get? (eltKey n (eltConj n pts[si']! reps[ri']!.t)) with
        | some ix, some it => m.insert (ix, it) (ri', si')
        | _, _ => m).get? (i, j)).isSome = true := by
    intro ri' m si' h
    split
    · exact mono _ _ _ h
    · exact h
  unfold locCov
  dsimp only
  refine foldl_hit (fun m : Std.HashMap (ℕ × ℕ) (ℕ × ℕ) => (m.get? (i, j)).isSome = true)
    _ _ _ ri (List.mem_range.2 hri) ?_ ?_
  · intro m ri' h
    exact foldl_pres _ _ _ _ (fun m si' _ h => imono ri' m si' h) h
  · intro m
    refine foldl_hit _ _ _ _ si (List.mem_range.2 hsi) (fun m si' h => imono ri m si' h) ?_
    intro m
    simp only [h1, h2]
    rw [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert]
    simp

theorem eE_lt_of_valid {n : ℕ} {x : Array ℕ} (h : eltValid n x = true) : eE n x < 2 :=
  ((eltValid_iff (ZMod 3) x).1 h).2.2.1

theorem locCover_of {n : ℕ} (hn : 0 < n) {pts : Array (Array ℕ)} {reps : Array LocRep}
    (hkey : ∀ i < pts.size, ∀ j < pts.size, eltKey n pts[i]! = eltKey n pts[j]! → i = j)
    (hval : ∀ i < pts.size, eltValid n pts[i]! = true)
    (hrep : ∀ r < reps.size, eltValid n reps[r]!.x = true ∧ eltValid n reps[r]!.t = true)
    (hcov : ∀ i < pts.size, ∀ j < pts.size, isO8 n pts[i]! = true → isO2 n pts[j]! = true →
      eltEq n (eltMul n pts[i]! pts[j]!) (eltMul n pts[j]! pts[i]!) = true →
      ∃ ri < reps.size, ∃ si < pts.size, eltEq n (eltConj n pts[si]! reps[ri]!.x) pts[i]! = true ∧
        eltEq n (eltConj n pts[si]! reps[ri]!.t) pts[j]! = true) :
    locCover n pts reps = true := by
  unfold locCover
  simp only [List.all_eq_true, List.mem_filter, List.mem_range, Bool.or_eq_true,
    Bool.not_eq_true']
  intro i ⟨hi, ho8⟩ j ⟨hj, ho2⟩
  by_cases hc : eltEq n (eltMul n pts[i]! pts[j]!) (eltMul n pts[j]! pts[i]!) = true
  · right
    obtain ⟨ri, hri, si, hsi, hx, ht⟩ := hcov i hi j hj ho8 ho2 hc
    have h1 := locIdx_self hkey hi
    have h2 := locIdx_self hkey hj
    rw [← eltKey_eq_of_eltEq hx] at h1
    rw [← eltKey_eq_of_eltEq ht] at h2
    obtain ⟨⟨ri', si'⟩, hv⟩ := Option.isSome_iff_exists.1 (locCov_hit hri hsi h1 h2)
    rw [hv]
    obtain ⟨hri', hsi', g1, g2⟩ := locCov_inv (i, j) (ri', si') hv
    obtain ⟨_, k1⟩ := locIdx_spec hkey g1
    obtain ⟨_, k2⟩ := locIdx_spec hkey g2
    simp only at hri' hsi' k1 k2
    have vx := eltValid_eltConj hn (hval si' hsi') (hrep ri' hri').1
    have vt := eltValid_eltConj hn (hval si' hsi') (hrep ri' hri').2
    simp only [hri', hsi', decide_true, Bool.true_and, Bool.and_eq_true]
    exact ⟨eltEq_of_key (eE_lt_of_valid vx) (eE_lt_of_valid (hval i hi)) k1.symm,
      eltEq_of_key (eE_lt_of_valid vt) (eE_lt_of_valid (hval j hj)) k2.symm⟩
  · left
    simpa using hc

end CFSG.KS.LocLn
