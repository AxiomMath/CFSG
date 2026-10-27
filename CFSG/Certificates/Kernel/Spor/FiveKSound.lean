module

public import Certificates.Data.Kernel.Spor.FiveK
public import CFSG.Certificates.Kernel.Spor.HKeyBSound
public import CFSG.Certificates.Kernel.Spor.FiveConj
import CFSG.Certificates.Kernel.Spor.PcompFacts

public section

namespace CFSG.KS.MulH

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.HBfs
open CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore.Native

theorem bAnd_eqF (a b : Bool) : Bool.rec (motive := fun _ => Bool) false b a = (a && b) := by
  cases a <;> rfl

theorem bIf_eqF (c t e : Bool) : Bool.rec (motive := fun _ => Bool) e t c = cond c t e := by
  cases c <;> rfl

theorem keyMemK_cons (x a : Nat) (L : List Nat) :
    keyMemK x (a :: L) = (Nat.beq a x || keyMemK x L) := by
  change Bool.rec (motive := fun _ => Bool) (keyMemK x L) true (Nat.beq a x) = _
  cases Nat.beq a x <;> rfl

theorem keyMemK_iff (x : Nat) (L : List Nat) : keyMemK x L = true ↔ x ∈ L := by
  induction L with
  | nil => exact ⟨fun h => Bool.noConfusion h, fun h => absurd h List.not_mem_nil⟩
  | cons a L ih =>
    rw [keyMemK_cons, Bool.or_eq_true, ih, Nat.beq_eq, List.mem_cons]
    exact ⟨fun h => h.elim (fun e => Or.inl e.symm) Or.inr,
      fun h => h.elim (fun e => Or.inl e.symm) Or.inr⟩

theorem appK_eq (L L' : List Nat) : appK L L' = L ++ L' := by
  induction L with
  | nil => rfl
  | cons a L ih =>
    change a :: appK L L' = _
    rw [ih]
    rfl

theorem cntD_cons (a : Nat) (L seen : List Nat) :
    cntD (a :: L) seen = cond (keyMemK a seen) (cntD L seen) (cntD L (a :: seen) + 1) := by
  change Bool.rec (motive := fun _ => Nat) (Nat.succ (cntD L (a :: seen))) (cntD L seen)
    (keyMemK a seen) = _
  cases keyMemK a seen <;> rfl

theorem cnt_spec {α : Type} (key : α → Nat) : ∀ (T : List α) (seen : List Nat),
    ∃ Xs : List α, (∀ x ∈ Xs, x ∈ T) ∧ (Xs.map key).Nodup ∧ (∀ x ∈ Xs, key x ∉ seen) ∧
      Xs.length = cntD (T.map key) seen
  | [], _ => ⟨[], by simp, by simp, by simp, rfl⟩
  | a :: T, seen => by
    rw [List.map_cons, cntD_cons]
    cases hm : keyMemK (key a) seen
    · obtain ⟨Xs, h1, h2, h3, h4⟩ := cnt_spec key T (key a :: seen)
      refine ⟨a :: Xs, fun x hx => ?_, ?_, fun x hx => ?_, ?_⟩
      · rcases List.mem_cons.1 hx with rfl | hx
        · exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ (h1 x hx)
      · rw [List.map_cons, List.nodup_cons]
        refine ⟨fun hk => ?_, h2⟩
        obtain ⟨y, hy, e⟩ := List.mem_map.1 hk
        exact h3 y hy (e ▸ List.mem_cons_self)
      · rcases List.mem_cons.1 hx with rfl | hx
        · intro hs
          rw [← keyMemK_iff] at hs
          rw [hs] at hm
          exact Bool.noConfusion hm
        · exact fun hs => h3 x hx (List.mem_cons_of_mem _ hs)
      · rw [List.length_cons, h4]
        rfl
    · obtain ⟨Xs, h1, h2, h3, h4⟩ := cnt_spec key T seen
      exact ⟨Xs, fun x hx => List.mem_cons_of_mem _ (h1 x hx), h2, h3, h4⟩

theorem anyNewK_spec (kk : List Nat) : ∀ ck, anyNewK kk ck = true → ∃ a ∈ ck, a ∉ kk
  | [], h => Bool.noConfusion h
  | a :: ck, h => by
    change Bool.rec (motive := fun _ => Bool) true (anyNewK kk ck) (keyMemK a kk) = true at h
    cases hm : keyMemK a kk
    · refine ⟨a, List.mem_cons_self, fun ha => ?_⟩
      rw [← keyMemK_iff] at ha
      rw [ha] at hm
      exact Bool.noConfusion hm
    · rw [hm] at h
      obtain ⟨b, hb, hb'⟩ := anyNewK_spec kk ck h
      exact ⟨b, List.mem_cons_of_mem _ hb, hb'⟩

section

variable (n w m : Nat) (G GI : Nat → Nat)

theorem extK_spec (c : Nat) : ∀ r l cs ck (kont : List Nat → List Nat → Bool),
    extK n w m G GI c r l cs ck kont =
      kont (cs ++ (List.range' l r).map fun j => cjK n w m G GI j c)
        (ck ++ (List.range' l r).map fun j => hkeyB n w m (cjK n w m G GI j c))
  | 0, l, cs, ck, kont => by
    change kont cs ck = _
    simp
  | r + 1, l, cs, ck, kont => by
    change strictB (cjK n w m G GI l c) (fun y => strictB (hkeyB n w m y) (fun hy =>
      extK n w m G GI c r (Nat.succ l) (appK cs [y]) (appK ck [hy]) kont)) = _
    rw [CFSG.KS.PF.strictB_eqP, CFSG.KS.PF.strictB_eqP, extK_spec c r, appK_eq, appK_eq,
      List.range'_succ, List.map_cons, List.map_cons, List.append_assoc, List.append_assoc]
    rfl

theorem kidsK_spec (k : Nat) (nx : List Nat → List Nat → List Nat → Bool) (kk cs0 ck0 : List Nat) :
    ∀ cs : List Nat, kidsK n w m G GI k nx kk cs0 ck0 cs (cs.map (hkeyB n w m)) = true →
      ∀ c ∈ cs, hkeyB n w m c ∉ kk →
        extK n w m G GI c k (nat_lit 0) cs0 ck0
          (fun cs' ck' => nx (appK kk [hkeyB n w m c]) cs' ck') = true
  | [], _, c, hc, _ => absurd hc List.not_mem_nil
  | c :: cs, h, c', hc', hn => by
    change bAnd(bIf(keyMemK (hkeyB n w m c) kk, true, extK n w m G GI c k (nat_lit 0) cs0 ck0
        (fun cs' ck' => nx (appK kk [hkeyB n w m c]) cs' ck')),
      kidsK n w m G GI k nx kk cs0 ck0 cs (cs.map (hkeyB n w m))) = true at h
    rw [bAnd_eqF, bIf_eqF, Bool.and_eq_true] at h
    rcases List.mem_cons.1 hc' with rfl | hc'
    · have hm : keyMemK (hkeyB n w m c') kk = false := by
        cases e : keyMemK (hkeyB n w m c') kk
        · rfl
        · exact absurd ((keyMemK_iff _ _).1 e) hn
      rw [hm] at h
      exact h.1
    · exact kidsK_spec k nx kk cs0 ck0 cs h.2 c' hc' hn

theorem leaf_of_cnt {k : Nat} {Kn cs : List Nat}
    (hcs : ∀ x, x ∈ cs ↔ ∃ Y ∈ Kn, ∃ l < k, x = cjK n w m G GI l Y)
    (h : Nat.ble 5 (cntD (appK (Kn.map (hkeyB n w m)) (cs.map (hkeyB n w m))) []) = true) :
    FiveTree (hkeyB n w m) (cjK n w m G GI) k 0 Kn := by
  rw [appK_eq, ← List.map_append] at h
  obtain ⟨Xs, h1, h2, -, h4⟩ := cnt_spec (hkeyB n w m) (Kn ++ cs) []
  rw [FiveTree.eq_1]
  refine ⟨Xs, fun X hX => (List.mem_append.1 (h1 X hX)).imp id fun hc => (hcs X).1 hc, h2, ?_⟩
  rw [h4]
  exact Nat.le_of_ble_eq_true h

theorem fiveK_sound (k : Nat) : ∀ f (Kn cs : List Nat),
    (∀ x, x ∈ cs ↔ ∃ Y ∈ Kn, ∃ l < k, x = cjK n w m G GI l Y) →
    fiveK n w m G GI k f (Kn.map (hkeyB n w m)) cs (cs.map (hkeyB n w m)) = true →
      FiveTree (hkeyB n w m) (cjK n w m G GI) k f Kn := by
  intro f
  induction f with
  | zero =>
    intro Kn cs hcs h
    exact leaf_of_cnt n w m G GI hcs h
  | succ f ih =>
    intro Kn cs hcs h
    change bIf(Nat.ble (nat_lit 5) (cntD (appK (Kn.map (hkeyB n w m)) (cs.map (hkeyB n w m)))
        List.nil), true,
      bAnd(anyNewK (Kn.map (hkeyB n w m)) (cs.map (hkeyB n w m)),
        kidsK n w m G GI k (fiveK n w m G GI k f) (Kn.map (hkeyB n w m)) cs
          (cs.map (hkeyB n w m)) cs (cs.map (hkeyB n w m)))) = true at h
    rw [FiveTree.eq_2]
    rw [bIf_eqF] at h
    cases hl : Nat.ble 5 (cntD (appK (Kn.map (hkeyB n w m)) (cs.map (hkeyB n w m))) [])
    · rw [hl, Bool.cond_false, bAnd_eqF, Bool.and_eq_true] at h
      obtain ⟨ha, hk⟩ := h
      refine Or.inr ⟨?_, fun Y hY l hl hn => ?_⟩
      · obtain ⟨a, ha', hnew⟩ := anyNewK_spec _ _ ha
        obtain ⟨c, hc, rfl⟩ := List.mem_map.1 ha'
        obtain ⟨Y, hY, l, hl, rfl⟩ := (hcs c).1 hc
        exact ⟨Y, hY, l, hl, hnew⟩
      · have hc : cjK n w m G GI l Y ∈ cs := (hcs _).2 ⟨Y, hY, l, hl, rfl⟩
        have hx := kidsK_spec n w m G GI k (fiveK n w m G GI k f) _ cs (cs.map (hkeyB n w m)) cs
          hk _ hc hn
        rw [extK_spec, appK_eq] at hx
        refine ih (Kn ++ [cjK n w m G GI l Y])
          (cs ++ (List.range' 0 k).map fun j => cjK n w m G GI j (cjK n w m G GI l Y))
          (fun x => ?_) ?_
        · rw [List.mem_append]
          constructor
          · rintro (hx | hx)
            · obtain ⟨Y', hY', l', hl', e⟩ := (hcs x).1 hx
              exact ⟨Y', List.mem_append_left _ hY', l', hl', e⟩
            · obtain ⟨j, hj, e⟩ := List.mem_map.1 hx
              rw [List.mem_range'_1] at hj
              exact ⟨_, List.mem_append_right _ (List.mem_singleton_self _), j, by omega, e.symm⟩
          · rintro ⟨Y', hY', l', hl', e⟩
            rcases List.mem_append.1 hY' with hY' | hY'
            · exact Or.inl ((hcs x).2 ⟨Y', hY', l', hl', e⟩)
            · rw [List.mem_singleton.1 hY'] at e
              exact Or.inr (List.mem_map.2 ⟨l', by rw [List.mem_range'_1]; omega, e.symm⟩)
        · rw [List.map_append, List.map_append, List.map_singleton, List.map_map]
          exact hx
    · exact Or.inl (leaf_of_cnt n w m G GI hcs hl)

theorem fiveTopK_sound {k f S : Nat} (h : fiveTopK n w m G GI k f S = true) :
    FiveTree (hkeyB n w m) (cjK n w m G GI) k f [S] := by
  change strictB (hkeyB n w m S) (fun hs => extK n w m G GI S k (nat_lit 0) [] []
    (fun cs ck => fiveK n w m G GI k f [hs] cs ck)) = true at h
  rw [CFSG.KS.PF.strictB_eqP, extK_spec, List.nil_append, List.nil_append] at h
  refine fiveK_sound n w m G GI k f [S] ((List.range' 0 k).map fun j => cjK n w m G GI j S)
    (fun x => ?_) ?_
  · constructor
    · intro hx
      obtain ⟨j, hj, e⟩ := List.mem_map.1 hx
      rw [List.mem_range'_1] at hj
      exact ⟨S, List.mem_singleton_self _, j, by omega, e.symm⟩
    · rintro ⟨Y, hY, l, hl, e⟩
      rw [List.mem_singleton.1 hY] at e
      exact List.mem_map.2 ⟨l, by rw [List.mem_range'_1]; omega, e.symm⟩
  · rw [List.map_map, List.map_singleton]
    exact h

end

theorem fiveConjOK_of_fiveTopK {n w k f cap S : Nat} {G GI : Nat → Nat} {cg cgInv : Array Table}
    (hcap : 5 ≤ cap) (hg : TabsOK n w k G cg) (hgi : TabsOK n w k GI cgInv)
    (hS : canonK n w (mask w) (n * w) S = true) (h : fiveTopK n w (mask w) G GI k f S = true) :
    CFSG.EvenSporadicStandard.HypOne.fiveConjOK n cap cg cgInv (tabT (unpack n w S)) = true := by
  refine fiveConjOK_of_tree (f := f) hcap ?_
  rw [hg.1]
  have hst : ∀ l < k, ∀ x, canonK n w (mask w) (n * w) x = true →
      canonK n w (mask w) (n * w) (cjK n w (mask w) G GI l x) = true ∧
        tabT (unpack n w (cjK n w (mask w) G GI l x)) =
          conjT n cg[l]! cgInv[l]! (tabT (unpack n w x)) := by
    intro l hl x hx
    have h1 := CFSG.KC.BfsPin.canonK_pcomp (hg.2 l hl).2 hx
    refine ⟨CFSG.KC.BfsPin.canonK_pcomp h1 (hgi.2 l hl).2, ?_⟩
    unfold conjT
    rw [(hg.2 l hl).1, (hgi.2 l hl).1, compT_tabT _ _ fun x _ => unpack_lt hx,
      compT_tabT _ _ fun x _ => unpack_lt (hgi.2 l hl).2,
      CFSG.KC.BfsPin.compA_unpack (hg.2 l hl).2 hx, CFSG.KC.BfsPin.compA_unpack h1 (hgi.2 l hl).2]
    rfl
  have := FiveTree.map (k := k) (st := fun l y => conjT n cg[l]! cgInv[l]! y) (key' := hkey n)
    (g := UInt64.toNat) (keyA := hkeyB n w (mask w)) (stA := cjK n w (mask w) G GI)
    (Good := fun x => canonK n w (mask w) (n * w) x = true) (fun a b e => UInt64.toNat_inj.1 e)
    (fun x => tabT (unpack n w x)) hst (fun x hx => hkeyB_tabT hx) f [S] (by simpa using hS)
    (fiveTopK_sound n w (mask w) G GI h)
  simpa using this

end CFSG.KS.MulH

end
