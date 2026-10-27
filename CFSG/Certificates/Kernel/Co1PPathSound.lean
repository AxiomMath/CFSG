module

public import CFSG.Certificates.Kernel.Co1PPinSound
public import Certificates.Data.Kernel.Co1PPath

public section

namespace CFSG.KC.Co1P

open CFSG.KC.Loop CFSG.KC.Co1B CFSG.KC.Co1F2 CFSG.KLie.CT CFSG.KC.TreeK
  CFSG.Sporadic.Co1Schreier.Native

theorem pathK_sound {act : Nat → Nat → Nat} {root N : Nat} {R H : Nat → Nat} (hH0 : H 0 = root)
    (hHs : ∀ i, 0 < i → i < N → H i = act (labK R i) (H (parK R i))) :
    ∀ d i, i < N → (pathK act root R d i).2 = true → (pathK act root R d i).1 = H i
  | 0, i, _, h => by
    have h' : Nat.beq i 0 = true := h
    rw [Nat.eq_of_beq_eq_true h', ← hH0]
    rfl
  | d + 1, i, hi, h => by
    by_cases h0 : i = 0
    · subst h0
      rw [hH0]
      rfl
    · have hb : Nat.beq i 0 = false := by rw [← Bool.not_eq_true, Nat.beq_eq]; exact h0
      have e : pathK act root R (d + 1) i = Prod.rec (motive := fun _ => Nat × Bool)
          (fun v ok => Prod.mk (act (labK R i) v) (CFSG.KLie.CT.andB ok (Nat.blt (parK R i) i)))
          (pathK act root R d (parK R i)) := by
        change Bool.rec (motive := fun _ => Nat × Bool) _ _ (Nat.beq i 0) = _
        rw [hb]
        rfl
      rw [e] at h ⊢
      rcases hq : pathK act root R d (parK R i) with ⟨v, ok⟩
      rw [hq] at h
      obtain ⟨h1, h2⟩ := CFSG.KC.TreeK.andB_true h
      have hp := lt_of_blt' h2
      have hv : v = H (parK R i) := by
        have h3 := pathK_sound hH0 hHs d (parK R i) (by omega) (by rw [hq]; exact h1)
        rw [hq] at h3
        exact h3
      change act (labK R i) v = H i
      rw [hv, hHs i (by omega) hi]

theorem walk_rec {act : Nat → Nat → Nat} {ng root : Nat} {rs : List (Nat × Nat)} {R : Nat → Nat}
    (hw : (treePts act ng root rs).2 = true) (hr : recsEqK R rs 0 = true) :
    ∀ i, 0 < i → i < rs.length + 1 →
      walkAt act ng root rs i = act (labK R i) (walkAt act ng root rs (parK R i)) := by
  intro i hi0 hi
  obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
  have hj : j < rs.length := by omega
  obtain ⟨-, -, he⟩ := walkAt_succ hw hj
  have hrj := recsEqK_sound rs 0 hr j hj
  rw [Nat.zero_add] at hrj
  rw [he, hrj]
  rfl

theorem pathK_walk {act : Nat → Nat → Nat} {ng root : Nat} {rs : List (Nat × Nat)} {R : Nat → Nat}
    (hw : (treePts act ng root rs).2 = true) (hr : recsEqK R rs 0 = true) {d i : Nat}
    (hi : i < rs.length + 1) (h : (pathK act root R d i).2 = true) :
    (pathK act root R d i).1 = walkAt act ng root rs i :=
  pathK_sound (walkAt_zero hw) (walk_rec hw hr) d i hi h

theorem ptPK_sound {GK GiK : List Nat} {ng R0 : Nat} {rs : List (Nat × Nat)} {R : Nat → Nat}
    (hh : (treePts (hsAct GK) ng oneK rs).2 = true) (hhi : (treePts (hisAct GiK) ng oneK rs).2 = true)
    (hr : recsEqK R rs 0 = true) {d i : Nat} (hi : i < rs.length + 1)
    (h : (ptPK GK GiK R R0 d i).2 = true) :
    (ptPK GK GiK R R0 d i).1 = mulWK (mulWK (walkAt (hsAct GK) ng oneK rs i) R0)
      (walkAt (hisAct GiK) ng oneK rs i) := by
  unfold ptPK at h ⊢
  rcases ha : pathK (hsAct GK) oneK R d i with ⟨a, oka⟩
  rcases hb : pathK (hisAct GiK) oneK R d i with ⟨b, okb⟩
  rw [ha, hb] at h
  obtain ⟨h1, h2⟩ := CFSG.KC.TreeK.andB_true h
  have ea : a = walkAt (hsAct GK) ng oneK rs i := by
    have h3 := pathK_walk hh hr hi (by rw [ha]; exact h1)
    rw [ha] at h3
    exact h3
  have eb : b = walkAt (hisAct GiK) ng oneK rs i := by
    have h3 := pathK_walk hhi hr hi (by rw [hb]; exact h2)
    rw [hb] at h3
    exact h3
  change mulWK (mulWK a R0) b = _
  rw [ea, eb]

theorem keys_inj {N kw : Nat} {SK IX P : Nat → Nat} (hk : ∀ s < N, keyAt N kw SK IX P s = true)
    {i j : Nat} (hi : i < N) (hj : j < N) (e : lowK kw (P i) = lowK kw (P j)) : i = j := by
  obtain ⟨s, hs, rfl⟩ := ix_surj hk hi
  obtain ⟨t, ht, rfl⟩ := ix_surj hk hj
  have es := (keyAt_parts hk hs).2.2
  have et := (keyAt_parts hk ht).2.2
  have hst : s = t := by
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with h | h
    · have h1 := keys_mono hk s t h ht
      rw [es, et, e] at h1
      exact Nat.lt_irrefl _ h1
    · have h1 := keys_mono hk t s h hs
      rw [es, et, e] at h1
      exact Nat.lt_irrefl _ h1
  rw [hst]

theorem nodup_of_inj' {L : List Nat} {f : Nat → Nat} {n : Nat} (hl : L.length = n)
    (hf : ∀ i < n, f i = L[i]?.getD 0) (hinj : ∀ i < n, ∀ j < n, f i = f j → i = j) : L.Nodup := by
  rw [List.nodup_iff_injective_get]
  intro ⟨i, hi⟩ ⟨j, hj⟩ e
  have hi' : i < n := by omega
  have hj' : j < n := by omega
  have ei := hf i hi'
  have ej := hf j hj'
  rw [List.getElem?_eq_getElem hi, Option.getD_some] at ei
  rw [List.getElem?_eq_getElem hj, Option.getD_some] at ej
  simp only [List.get_eq_getElem] at e
  exact Fin.ext (hinj i hi' j hj' (by rw [ei, ej, e]))

theorem nodup_modL_of_keys {L : List Nat} {N kw : Nat} {SK IX P : Nat → Nat} (hkw : kw ≤ 576)
    (hk : ∀ s < N, keyAt N kw SK IX P s = true) (hl : L.length = N)
    (hP : ∀ i < N, L[i]?.getD 0 = P i) : (modL L).Nodup := by
  rw [modL_eq]
  refine nodup_of_inj' (f := fun i => Nat.mod (P i) (Nat.shiftLeft 1 576)) (by rw [List.length_map, hl])
    (fun i hi => ?_) (fun i hi j hj e => ?_)
  · rw [List.getElem?_map, List.getElem?_eq_getElem (by omega), Option.map_some, Option.getD_some,
      ← Option.getD_some (a := L[i]) (b := 0), ← List.getElem?_eq_getElem (by omega), hP i hi]
  · refine keys_inj hk hi hj (lowK_of_eqK hkw ?_)
    rw [eqK_iff]
    exact e

section Chk

open CFSG.Sporadic.Co1Patterson.Native

variable {rs : List (Nat × Nat)} {ng : Nat}

theorem orbOK_of_nodup {G Gi : Array Rows} {GK GiK : List Nat} {R : Nat} (hGs : G.size = ng)
    (hG : ∀ l < ng, G[l]! = unpackR 24 (getL 0 GK l))
    (hGi : ∀ l < ng, Gi[l]! = unpackR 24 (getL 0 GiK l))
    (hh : (treePts (hsAct GK) ng oneK rs).2 = true) (hhi : (treePts (hisAct GiK) ng oneK rs).2 = true)
    (hlenG : GK.length = ng) (hinv : invsOK GK GiK = true)
    (hd : (modL (conjL R (treePts (hsAct GK) ng oneK rs).1 (treePts (hisAct GiK) ng oneK rs).1)).Nodup) :
    orbOK G Gi (unpackR 24 R) (mkOrbT G Gi (unpackR 24 R) (treeArr rs)) = true := by
  obtain ⟨hGG, hgi⟩ := invsOK_sound GK GiK hinv
  have l1 := walk_length hh
  have l2 := walk_length hhi
  obtain ⟨cl, cg⟩ := conjL_get R _ _ (l1.trans l2.symm)
  have hn := mkOrbT_size (G := G) (Gi := Gi) (R := R) (rs := rs)
  have hhs := treeHs_get hG hh (Array.replicate (treeArr rs).1.size (unpackR 24 R))
    (by simp [treeArr_size])
  have hhis := treeHis_get hGi hhi (Array.replicate (treeArr rs).1.size (unpackR 24 R))
    (by simp [treeArr_size])
  have hpts : (mkOrbT G Gi (unpackR 24 R) (treeArr rs)).c.pts.toList =
      (conjL R (treePts (hsAct GK) ng oneK rs).1 (treePts (hisAct GiK) ng oneK rs).1).map
        (unpackR 24) := by
    refine toList_eq_map (by rw [hn, cl, l1]) fun j hj => ?_
    rw [cl, l1] at hj
    rw [mkOrbT_pts hG hGi hh hhi hj, cg j (by rw [l1]; exact hj)]
    rfl
  have epar : (mkOrbT G Gi (unpackR 24 R) (treeArr rs)).c.par = (treeArr rs).1 := rfl
  have elab' : (mkOrbT G Gi (unpackR 24 R) (treeArr rs)).c.lab = (treeArr rs).2 := rfl
  have ehs : (mkOrbT G Gi (unpackR 24 R) (treeArr rs)).hs = CFSG.Sporadic.Co1Patterson.Native.treeHs G
      ⟨Array.replicate (treeArr rs).1.size (unpackR 24 R), (treeArr rs).1, (treeArr rs).2⟩ := rfl
  have ehis : (mkOrbT G Gi (unpackR 24 R) (treeArr rs)).his =
      CFSG.Sporadic.Co1Patterson.Native.treeHis Gi
        ⟨Array.replicate (treeArr rs).1.size (unpackR 24 R), (treeArr rs).1, (treeArr rs).2⟩ := rfl
  unfold orbOK
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.all_eq_true, List.mem_range,
    Bool.or_eq_true]
  refine ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨by rw [hn]; omega, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · rw [hn]; exact hhs.1
  · rw [hn]; exact hhis.1
  · simp [mkOrbT, treeArr_size]
  · simp [mkOrbT, treeArr]
  · intro l hl
    rw [hGs] at hl
    rw [hG l hl, hGi l hl, CFSG.KC.F2W.mul_unpackW, CFSG.KC.Co1B.one_eq]
    exact congrArg (unpackR 24) (Nat.eq_of_beq_eq_true (hgi l (by rw [hlenG]; exact hl)))
  · rw [ehs, hhs.2 0 (by omega), walkAt_zero hh, ← CFSG.KC.Co1B.one_eq]
  · rw [ehis, hhis.2 0 (by omega), walkAt_zero hhi, ← CFSG.KC.Co1B.one_eq]
  · intro i hi
    rw [hn] at hi
    rcases i with _ | i
    · exact Or.inl rfl
    · refine Or.inr ?_
      have hi' : i < rs.length := by omega
      obtain ⟨hp, hl, he⟩ := walkAt_succ hh hi'
      obtain ⟨-, -, he'⟩ := walkAt_succ hhi hi'
      rw [epar, elab', ehs, ehis, treeArr_par hi', treeArr_lab hi', hhs.2 _ (by omega),
        hhs.2 _ (by omega), hhis.2 _ (by omega), hhis.2 _ (by omega), he, he', hG _ hl, hGi _ hl,
        hGs, CFSG.KC.F2W.mul_unpackW, CFSG.KC.F2W.mul_unpackW]
      exact ⟨⟨⟨by omega, hl⟩, rfl⟩, rfl⟩
  · intro i hi
    rw [hn] at hi
    refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
    · rw [mkOrbT_pts hG hGi hh hhi hi]
      exact validRows_unpackR _
    · rw [ehs, hhs.2 i hi]
      exact validRows_unpackR _
    · rw [ehis, hhis.2 i hi]
      exact validRows_unpackR _
    · simp only [mkOrbT]
      rw [getElem!_pos _ i (by simp [treeArr_size]; omega)]
      simp
  · rw [hpts]
    apply distinctKeys_of_nodup
    apply nodup_keys
    exact hd

end Chk

theorem sumN_zero (g : Nat → Nat) : sumN 0 g = 0 := rfl

theorem sumN_succ (n : Nat) (g : Nat → Nat) : sumN (n + 1) g = g n + sumN n g := rfl

theorem sumN_add (g : Nat → Nat) (a : Nat) : ∀ b, sumN (a + b) g = sumN a g + sumN b fun k => g (a + k)
  | 0 => rfl
  | b + 1 => by
    rw [← Nat.add_assoc, sumN_succ, sumN_add g a b, sumN_succ]
    omega

theorem sumN_zero_tail (g : Nat → Nat) (N : Nat) (hz : ∀ i, N ≤ i → g i = 0) :
    ∀ j, sumN (N + j) g = sumN N g
  | 0 => rfl
  | j + 1 => by
    rw [← Nat.add_assoc, sumN_succ, sumN_zero_tail g N hz j, hz _ (by omega), Nat.zero_add]

theorem count_chunks (f : Nat → Bool) {N nc : Nat} (hN : N ≤ 64 * nc) :
    ((List.range N).filter f).length = sumN nc (cntK N f) := by
  let g : Nat → Nat := fun i => Bool.rec (motive := fun _ => Nat) 0 1 (CFSG.KLie.CT.andB (Nat.blt i N) (f i))
  have hg : ∀ i, i < N → g i = if f i = true then 1 else 0 := by
    intro i hi
    have e : Nat.blt i N = true := by rw [Nat.blt_eq]; exact hi
    change Bool.rec (motive := fun _ => Nat) 0 1 (CFSG.KLie.CT.andB (Nat.blt i N) (f i)) = _
    rw [e]
    cases f i <;> rfl
  have hz : ∀ i, N ≤ i → g i = 0 := by
    intro i hi
    have e : Nat.blt i N = false := by rw [← Bool.not_eq_true, Nat.blt_eq]; omega
    change Bool.rec (motive := fun _ => Nat) 0 1 (CFSG.KLie.CT.andB (Nat.blt i N) (f i)) = 0
    rw [e]
    rfl
  have h1 : ∀ n, n ≤ N → ((List.range n).filter f).length = sumN n g := by
    intro n
    induction n with
    | zero => intro _; rfl
    | succ n ih =>
      intro hn
      rw [List.range_succ, List.filter_append, List.length_append, ih (by omega), sumN_succ,
        hg n (by omega)]
      cases hf : f n <;> simp [hf, Nat.add_comm]
  have hc : ∀ c, cntK N f c = sumN 64 fun k => g (64 * c + k) := fun c => rfl
  have h2 : ∀ m, sumN m (cntK N f) = sumN (64 * m) g := by
    intro m
    induction m with
    | zero => rw [Nat.mul_zero, sumN_zero, sumN_zero]
    | succ m ih =>
      rw [sumN_succ, ih, Nat.mul_succ, sumN_add g (64 * m) 64, hc m]
      omega
  rw [h1 N le_rfl, h2 nc]
  obtain ⟨j, hj⟩ : ∃ j, 64 * nc = N + j := ⟨64 * nc - N, by omega⟩
  rw [hj, sumN_zero_tail g N hz j]

end CFSG.KC.Co1P

end
