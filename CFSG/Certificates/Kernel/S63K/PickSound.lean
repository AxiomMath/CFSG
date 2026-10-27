module

public import CFSG.Certificates.Kernel.S63K.Pack
public import Certificates.Data.Kernel.S63K.Pick
public import CFSG.LargeExtraspecial.S63CD4InputsA

public section

set_option exponentiation.threshold 600

namespace CFSG.KC.S63K

open CFSG.KC.Co1F2 CFSG.LargeExtraspecial.S63 CFSG.Sporadic.SmallF2.Native

abbrev PState := Std.HashSet (Array ℕ) × Array (Array ℕ) × Array ℕ

@[expose] def bodyP (f : ℕ → Array ℕ) (t : ℕ) (c : ℕ) (s : PState) : Id (ForInStep PState) :=
  if s.2.1.size ≥ t then pure (ForInStep.done (s.1, s.2.1, s.2.2))
  else
    if (!s.1.contains (f c)) = true then
      pure (ForInStep.yield (Id.run (forIn (Array.map (mulR (f c)) s.2.1) s.1
          fun e s => pure (ForInStep.yield (s.insert e))),
        s.2.1 ++ Array.map (mulR (f c)) s.2.1, s.2.2.push c))
    else pure (ForInStep.yield (s.1, s.2.1, s.2.2))

theorem pickSpan_eq_run (n : ℕ) (f : ℕ → Array ℕ) (z : Array ℕ) (t : ℕ) :
    pickSpan n f z t = (Id.run (forIn (List.range' 0 n)
      (((∅ : Std.HashSet (Array ℕ)).insert oneR).insert z, #[oneR, z], (#[] : Array ℕ))
      (bodyP f t))).2.2.toList := by
  unfold pickSpan
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size, Id.run,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one]
  rfl

def Rel (s : PState) (E P : List ℕ) : Prop :=
  s.2.1 = (E.map (unpackR 24)).toArray ∧ s.2.2 = P.reverse.toArray ∧
    ∀ y, s.1.contains (unpackR 24 y) = E.any (fun e => eqM e y)

theorem beq_eqM (a y : ℕ) : (unpackR 24 a == unpackR 24 y) = eqM a y := beq_unpackR a y

theorem fold_insert (S : Std.HashSet (Array ℕ)) :
    ∀ (L : List ℕ) (y : ℕ),
      (L.foldl (fun S e => S.insert (unpackR 24 e)) S).contains (unpackR 24 y) =
        (S.contains (unpackR 24 y) || L.any fun e => eqM e y)
  | [], y => by simp
  | e :: L, y => by
    rw [List.foldl_cons, fold_insert _ L y, Std.HashSet.contains_insert, beq_eqM, List.any_cons]
    cases S.contains (unpackR 24 y) <;> cases eqM e y <;> simp

theorem forIn_ins (S : Std.HashSet (Array ℕ)) (L : List (Array ℕ)) :
    forIn (m := Id) L S (fun e s => pure (ForInStep.yield (s.insert e))) =
      L.foldl (fun S e => S.insert e) S := by
  induction L generalizing S with
  | nil => rfl
  | cons a L ih =>
    rw [List.forIn_cons, List.foldl_cons]
    exact ih _

theorem loop (f : ℕ → Array ℕ) (F : ℕ → ℕ) (t : ℕ) :
    ∀ (k c : ℕ) (s : PState) (E P : List ℕ), Rel s E P →
      (∀ c', c ≤ c' → c' < c + k → f c' = unpackR 24 (F c')) →
      (Id.run (forIn (List.range' c k) s (bodyP f t))).2.2.toList = pickK F t k c E P := by
  intro k
  induction k with
  | zero =>
    intro c s E P hr _
    change s.2.2.toList = P.reverse
    rw [hr.2.1]
  | succ k ih =>
    intro c s E P hr hf
    obtain ⟨he, hp, hc⟩ := hr
    have hfc : f c = unpackR 24 (F c) := hf c le_rfl (by omega)
    have hf' : ∀ c', c + 1 ≤ c' → c' < c + 1 + k → f c' = unpackR 24 (F c') :=
      fun c' h1 h2 => hf c' (by omega) (by omega)
    rw [List.range'_succ, List.forIn_cons]
    have hsz : s.2.1.size = E.length := by rw [he]; simp
    change _ = (bif Nat.ble t E.length then P.reverse
      else bif E.any (fun e => eqM e (F c)) then pickK F t k (c + 1) E P
      else pickK F t k (c + 1) (E ++ E.map (CFSG.KC.F2W.mulW 24 (F c))) (c :: P))
    by_cases ht : t ≤ E.length
    · have hb : Nat.ble t E.length = true := by simpa using ht
      rw [hb]
      simp only [bodyP, ge_iff_le, hsz, ht, ↓reduceIte, Id.run, cond_true]
      change s.2.2.toList = _
      rw [hp]
    · have hb : Nat.ble t E.length = false := by
        cases e : Nat.ble t E.length
        · rfl
        · exact absurd (Nat.le_of_ble_eq_true e) ht
      rw [hb, cond_false]
      have hcont : s.1.contains (f c) = E.any (fun e => eqM e (F c)) := by rw [hfc, hc]
      cases ha : E.any (fun e => eqM e (F c))
      · simp only [bodyP, ge_iff_le, hsz, ht, ↓reduceIte, hcont, ha, Bool.not_false, cond_false]
        apply ih (c + 1) _ _ _ _ hf'
        refine ⟨?_, ?_, fun y => ?_⟩
        · change s.2.1 ++ Array.map (mulR (f c)) s.2.1 = _
          rw [he, hfc, List.map_append, List.map_map]
          simp only [List.map_toArray, List.append_toArray]
          congr 2
          rw [List.map_map]
          apply List.map_congr_left
          intro e _
          exact mulR_unpackR _ _
        · change s.2.2.push c = _
          rw [hp, List.reverse_cons]
          simp
        · change (Id.run (forIn (Array.map (mulR (f c)) s.2.1) s.1
            fun e s => pure (ForInStep.yield (s.insert e)))).contains (unpackR 24 y) = _
          rw [← Array.forIn_toList, Id.run, forIn_ins, he, hfc]
          simp only [List.map_toArray, List.toList_toArray, List.map_map]
          have e2 : (E.map ((mulR (unpackR 24 (F c))) ∘ (unpackR 24))) =
              (E.map (CFSG.KC.F2W.mulW 24 (F c))).map (unpackR 24) := by
            rw [List.map_map]
            apply List.map_congr_left
            intro e _
            exact mulR_unpackR _ _
          rw [e2, List.foldl_map, fold_insert, hc, List.any_append]
      · simp only [bodyP, ge_iff_le, hsz, ht, ↓reduceIte, hcont, ha, Bool.not_true,
          Bool.false_eq_true, cond_true]
        exact ih (c + 1) _ _ _ ⟨he, hp, hc⟩ hf'

theorem pickSpan_eq {n t Z : ℕ} {f : ℕ → Array ℕ} {F : ℕ → ℕ}
    (hf : ∀ c < n, f c = unpackR 24 (F c)) :
    pickSpan n f (unpackR 24 Z) t = pickK F t n 0 [idP, Z] [] := by
  rw [pickSpan_eq_run]
  apply loop f F t n 0 _ [idP, Z] [] _ (fun c' _ h => hf c' (by omega))
  refine ⟨?_, rfl, fun y => ?_⟩
  · change #[oneR, unpackR 24 Z] = _
    rw [oneR_eq]
    rfl
  · rw [Std.HashSet.contains_insert, Std.HashSet.contains_insert, Std.HashSet.contains_empty,
      oneR_eq, beq_eqM, beq_eqM]
    simp [List.any_cons, Bool.or_comm]

end CFSG.KC.S63K

end
