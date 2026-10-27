module

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaSec3XSpec
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaSec3YCheck

public noncomputable section

namespace CFSG.EvenSmallLie.UnitarySix.YamadaSec3

open CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
open CFSG.Monster.B.Fischer CFSG.RankThree.Native

theorem gensOK_chA2s0 : chA2s0.GensOK := by unfold ChainData.GensOK; decide

theorem nodup_chA2s0 : chA2s0.baseFin.Nodup := by decide

theorem gensOK_chA2s1 : chA2s1.GensOK := by unfold ChainData.GensOK; decide

theorem nodup_chA2s1 : chA2s1.baseFin.Nodup := by decide

theorem gensOK_chA2s2 : chA2s2.GensOK := by unfold ChainData.GensOK; decide

theorem nodup_chA2s2 : chA2s2.baseFin.Nodup := by decide

theorem gensOK_chA1s0 : chA1s0.GensOK := by unfold ChainData.GensOK; decide

theorem nodup_chA1s0 : chA1s0.baseFin.Nodup := by decide

theorem gensOK_chA1s1 : chA1s1.GensOK := by unfold ChainData.GensOK; decide

theorem nodup_chA1s1 : chA1s1.baseFin.Nodup := by decide

theorem gensOK_chA3s0 : chA3s0.GensOK := by unfold ChainData.GensOK; decide

theorem nodup_chA3s0 : chA3s0.baseFin.Nodup := by decide

theorem gensOK_chA3s1 : chA3s1.GensOK := by unfold ChainData.GensOK; decide

theorem nodup_chA3s1 : chA3s1.baseFin.Nodup := by decide

theorem gensOK_chA3s2 : chA3s2.GensOK := by unfold ChainData.GensOK; decide

theorem nodup_chA3s2 : chA3s2.baseFin.Nodup := by decide

theorem gensOK_chA3s3 : chA3s3.GensOK := by unfold ChainData.GensOK; decide

theorem nodup_chA3s3 : chA3s3.baseFin.Nodup := by decide

theorem gensOK_chA3s4 : chA3s4.GensOK := by unfold ChainData.GensOK; decide

theorem nodup_chA3s4 : chA3s4.baseFin.Nodup := by decide

theorem a2Tab_lt : ∀ p ∈ a2Tab, ∀ k ∈ cjW p.1 a2Reps[p.2]!, k < 18 := by decide +kernel

theorem a1Tab_lt : ∀ p ∈ a1Tab, ∀ k ∈ cjW p.1 a1Reps[p.2]!, k < 18 := by decide +kernel

theorem a3Tab_lt : ∀ p ∈ a3Tab, ∀ k ∈ cjW p.1 a3Reps[p.2]!, k < 18 := by decide +kernel

theorem singReps_lt : ∀ s ∈ singReps, ∀ k ∈ s, k < 18 := by decide +kernel

theorem zCls_lt : ∀ c ∈ zCls, ∀ k ∈ c, k < 18 := by decide +kernel

theorem zMs_lt : ∀ j < 20, ∀ k ∈ zMs[j]!, k < 18 ∧ [k] ∈ chK2.gens := by decide +kernel

theorem card_chA2s0 : Nat.card chA2s0.grp = 512 := by
  rw [ChainData.card_grp tabs_check gensOK_chA2s0 chA2s0_ok nodup_chA2s0, chA2s0_order]

theorem card_chA2s1 : Nat.card chA2s1.grp = 512 := by
  rw [ChainData.card_grp tabs_check gensOK_chA2s1 chA2s1_ok nodup_chA2s1, chA2s1_order]

theorem card_chA2s2 : Nat.card chA2s2.grp = 512 := by
  rw [ChainData.card_grp tabs_check gensOK_chA2s2 chA2s2_ok nodup_chA2s2, chA2s2_order]

theorem card_chA1s0 : Nat.card chA1s0.grp = 512 := by
  rw [ChainData.card_grp tabs_check gensOK_chA1s0 chA1s0_ok nodup_chA1s0, chA1s0_order]

theorem card_chA1s1 : Nat.card chA1s1.grp = 512 := by
  rw [ChainData.card_grp tabs_check gensOK_chA1s1 chA1s1_ok nodup_chA1s1, chA1s1_order]

theorem card_chA3s0 : Nat.card chA3s0.grp = 4096 := by
  rw [ChainData.card_grp tabs_check gensOK_chA3s0 chA3s0_ok nodup_chA3s0, chA3s0_order]

theorem card_chA3s1 : Nat.card chA3s1.grp = 4096 := by
  rw [ChainData.card_grp tabs_check gensOK_chA3s1 chA3s1_ok nodup_chA3s1, chA3s1_order]

theorem card_chA3s2 : Nat.card chA3s2.grp = 4096 := by
  rw [ChainData.card_grp tabs_check gensOK_chA3s2 chA3s2_ok nodup_chA3s2, chA3s2_order]

theorem card_chA3s3 : Nat.card chA3s3.grp = 4096 := by
  rw [ChainData.card_grp tabs_check gensOK_chA3s3 chA3s3_ok nodup_chA3s3, chA3s3_order]

theorem card_chA3s4 : Nat.card chA3s4.grp = 4096 := by
  rw [ChainData.card_grp tabs_check gensOK_chA3s4 chA3s4_ok nodup_chA3s4, chA3s4_order]

theorem inv_mul_fix {t g : Equiv.Perm (Fin 693)} {p : Fin 693} (h : t p = g p) :
    (t⁻¹ * g) p = p := by
  rw [Equiv.Perm.mul_apply, ← h, perm_inv_apply']

theorem apply_eq_of_get {a b : Array ℕ} {X Y : Equiv.Perm (Fin 693)} (hX : Rep 693 a X)
    (hY : Rep 693 b Y) {p : ℕ} (hp : p < 693) (h : a[p]! = b[p]!) :
    X ⟨p, hp⟩ = Y ⟨p, hp⟩ :=
  Fin.ext (by rw [← hX.apply hp, ← hY.apply hp, h])

theorem cjW_mem {c d : ChainData} (hn : d.grp ≤ Subgroup.normalizer (c.grp : Set _))
    {q r : List ℕ} (hq : ∀ k ∈ q, [k] ∈ d.gens) (hr : ∀ k ∈ r, [k] ∈ c.gens)
    (hq18 : ∀ k ∈ q, k < 18) : wP (cjW q r) ∈ c.grp := by
  rw [cjW, wP_append, wP_append, wP_reverse q hq18]
  exact (Subgroup.mem_normalizer_iff.1 (hn (wP_mem_of_letters q hq)) _).1
    (wP_mem_of_letters r hr)

theorem digit_inj {x1 u1 x2 u2 : ℕ} (hx1 : x1 < 1024) (hx2 : x2 < 1024)
    (h : x1 + 1024 * u1 = x2 + 1024 * u2) : x1 = x2 ∧ u1 = u2 := by
  have e1 := congrArg (· % 1024) h
  simp only [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hx1, Nat.mod_eq_of_lt hx2] at e1
  subst e1
  exact ⟨rfl, Nat.eq_of_mul_eq_mul_left (by norm_num) (Nat.add_left_cancel h)⟩

theorem key3_inj {x1 y1 z1 x2 y2 z2 : ℕ} (hy1 : y1 < 693) (hx1 : x1 < 693) (hy2 : y2 < 693)
    (hx2 : x2 < 693) (h : x1 + 1024 * (y1 + 1024 * z1) = x2 + 1024 * (y2 + 1024 * z2)) :
    x1 = x2 ∧ y1 = y2 ∧ z1 = z2 := by
  obtain ⟨e1, e2⟩ := digit_inj (lt_trans hx1 (by norm_num)) (lt_trans hx2 (by norm_num)) h
  obtain ⟨e3, e4⟩ := digit_inj (lt_trans hy1 (by norm_num)) (lt_trans hy2 (by norm_num)) e2
  exact ⟨e1, e3, e4⟩

theorem keyA3_inj {x1 y1 x2 y2 : ℕ} (hy1 : y1 < 693) (hy2 : y2 < 693)
    (h : x1 * 1024 + y1 = x2 * 1024 + y2) : x1 = x2 ∧ y1 = y2 := by
  rw [Nat.add_comm, Nat.mul_comm, Nat.add_comm (x2 * 1024), Nat.mul_comm x2] at h
  obtain ⟨e1, e2⟩ := digit_inj (lt_trans hy1 (by norm_num)) (lt_trans hy2 (by norm_num)) h
  exact ⟨e2, e1⟩

theorem yKeys_spec : a2Tab.map (fun p => key3 (wA (cjW p.1 a2Reps[p.2]!))) = a2Keys ∧
    a1Tab.map (fun p => (wA (cjW p.1 a1Reps[p.2]!))[1]!) = a1Keys ∧
    a1Tab.map (fun p => (wA (cjW p.1 a1Reps[p.2]! ++ [14]))[1]!) = a1KeysZ ∧
    a3Tab.map (fun p => keyA3 (wA (cjW p.1 a3Reps[p.2]!))) = a3Keys ∧
    singReps.map (fun s => (wA s)[1]!) = singKeys ∧
    singReps.map (fun s => (wA (s ++ [14]))[1]!) = singKeysZ := by
  have h := yKeys_check
  unfold yKeysCheck at h
  rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true,
    Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
  exact ⟨beq_iff_eq.1 h1, beq_iff_eq.1 h2, beq_iff_eq.1 h3, beq_iff_eq.1 h4, beq_iff_eq.1 h5,
    beq_iff_eq.1 h6⟩

theorem a2Tab_mem : ∀ p ∈ a2Tab, wP (cjW p.1 a2Reps[p.2]!) ∈ chA2.grp := by
  have hq : ∀ p ∈ a2Tab, (∀ k ∈ p.1, k ∈ [0, 1, 2, 3, 15, 16]) ∧ p.2 < 3 := by decide +kernel
  have hK : ∀ k ∈ [0, 1, 2, 3, 15, 16], [k] ∈ chK2.gens ∧ k < 18 := by decide
  have hR : ∀ i < 3, ∀ k ∈ a2Reps[i]!, [k] ∈ chA2.gens := by decide
  exact fun p hp => cjW_mem chK2_le_normalizer_A2 (fun k hk => (hK k ((hq p hp).1 k hk)).1)
    (hR _ (hq p hp).2) (fun k hk => (hK k ((hq p hp).1 k hk)).2)

theorem A2_base : ∀ h ∈ chA2.grp, h 45 = 45 → h 3 = 3 → h 1 = 1 → h = 1 := by
  intro h hh h45 h3 h1
  obtain ⟨a, hX, ha⟩ := a2Orb_check h hh
  unfold a2OrbAt at ha
  simp only [Bool.and_eq_true, Bool.or_eq_true, bne_iff_ne, ne_eq] at ha
  rcases ha.1 with ((h' | h') | h') | he
  · exact absurd (by rw [hX.apply (by norm_num : 45 < 693)]; exact congrArg Fin.val h45) h'
  · exact absurd (by rw [hX.apply (by norm_num : 3 < 693)]; exact congrArg Fin.val h3) h'
  · exact absurd (by rw [hX.apply (by norm_num : 1 < 693)]; exact congrArg Fin.val h1) h'
  · exact eq_one_of_eqA hX he

theorem a2Orb_spec : ∀ g ∈ chA2.grp, g ≠ 1 → ∃ p ∈ a2Tab, wP (cjW p.1 a2Reps[p.2]!) = g := by
  intro g hg hne
  obtain ⟨a, hX, ha⟩ := a2Orb_check g hg
  unfold a2OrbAt at ha
  rw [Bool.and_eq_true] at ha
  rcases Bool.or_eq_true _ _ ▸ ha.2 with hk | he
  · rw [← yKeys_spec.1, List.contains_iff_mem, List.mem_map] at hk
    obtain ⟨p, hp, hkey⟩ := hk
    have hr := rep_wA tabs_check _ (a2Tab_lt p hp)
    unfold key3 at hkey
    obtain ⟨e1, e2, e3⟩ := key3_inj (hr.lt (by norm_num : 3 < 693)) (hr.lt (by norm_num : 45 < 693))
      (hX.lt (by norm_num : 3 < 693)) (hX.lt (by norm_num : 45 < 693)) hkey
    have hm := mul_mem (inv_mem (a2Tab_mem p hp)) hg
    have h1 := A2_base _ hm (inv_mul_fix (apply_eq_of_get hr hX _ e1))
      (inv_mul_fix (apply_eq_of_get hr hX _ e2)) (inv_mul_fix (apply_eq_of_get hr hX _ e3))
    exact ⟨p, hp, (inv_mul_eq_one.1 h1)⟩
  · exact absurd (eq_one_of_eqA hX he) hne

theorem A1_reg : ∀ h ∈ chA1.grp, h 1 = 1 → h = 1 := by
  intro h hh h1
  obtain ⟨a, hX, ha⟩ := a1Orb_check h hh
  unfold a1OrbAt at ha
  rw [Bool.and_eq_true] at ha
  have hb := ha.1
  rw [Bool.or_eq_true, bne_iff_ne, ne_eq] at hb
  rcases hb with h' | he
  · exact absurd (by rw [hX.apply (by norm_num : 1 < 693)]; exact congrArg Fin.val h1) h'
  · exact eq_one_of_eqA hX he

theorem A1_eq_of {t g : Equiv.Perm (Fin 693)} (ht : t ∈ chA1.grp) (hg : g ∈ chA1.grp)
    (h : t 1 = g 1) : t = g :=
  inv_mul_eq_one.1 (A1_reg _ (mul_mem (inv_mem ht) hg) (inv_mul_fix h))

theorem A1_eq_of' {t g : Equiv.Perm (Fin 693)} (ht : t ∈ chA1.grp) (hg : g ∈ chA1.grp)
    (h : t ⟨1, by norm_num⟩ = g ⟨1, by norm_num⟩) : t = g :=
  A1_eq_of ht hg h

theorem a1Tab_mem : ∀ p ∈ a1Tab, wP (cjW p.1 a1Reps[p.2]!) ∈ chA1.grp := by
  have hq : ∀ p ∈ a1Tab, (∀ k ∈ p.1, k ∈ [2, 3, 4, 16, 17]) ∧ p.2 < 2 := by decide +kernel
  have hK : ∀ k ∈ [2, 3, 4, 16, 17], [k] ∈ chK1.gens ∧ k < 18 := by decide
  have hR : ∀ i < 2, ∀ k ∈ a1Reps[i]!, [k] ∈ chA1.gens := by decide
  exact fun p hp => cjW_mem chK1_le_normalizer_A1 (fun k hk => (hK k ((hq p hp).1 k hk)).1)
    (hR _ (hq p hp).2) (fun k hk => (hK k ((hq p hp).1 k hk)).2)

theorem gP14_mem : gP 14 ∈ chA1.grp := by
  rw [← wP_single]
  exact wP_mem_grp (by decide)

theorem a1Orb_spec : ∀ g ∈ chA1.grp, g ∉ chZ.grp → ∃ p ∈ a1Tab,
    wP (cjW p.1 a1Reps[p.2]!) = g ∨ wP (cjW p.1 a1Reps[p.2]!) * gP 14 = g := by
  intro g hg hne
  obtain ⟨a, hX, ha⟩ := a1Orb_check g hg
  unfold a1OrbAt at ha
  rw [Bool.and_eq_true] at ha
  have hy := ha.2
  rw [Bool.or_eq_true, Bool.or_eq_true, Bool.or_eq_true] at hy
  have hz := rep_gA tabs_check (by norm_num : 14 < 18)
  have h1g : g 1 = ⟨a[1]!, hX.lt (by norm_num)⟩ := Fin.ext (hX.apply (by norm_num)).symm
  rcases hy with ((hk | hk) | h1) | h2
  · rw [← yKeys_spec.2.1, List.contains_iff_mem, List.mem_map] at hk
    obtain ⟨p, hp, hkey⟩ := hk
    have hr := rep_wA tabs_check _ (a1Tab_lt p hp)
    exact ⟨p, hp, Or.inl (A1_eq_of' (a1Tab_mem p hp) hg (apply_eq_of_get hr hX _ hkey))⟩
  · rw [← yKeys_spec.2.2.1, List.contains_iff_mem, List.mem_map] at hk
    obtain ⟨p, hp, hkey⟩ := hk
    have hlt : ∀ k ∈ cjW p.1 a1Reps[p.2]! ++ [14], k < 18 := fun k hk =>
      (List.mem_append.1 hk).elim (a1Tab_lt p hp k) fun h => by simp at h; omega
    have hr := rep_wA tabs_check _ hlt
    rw [wP_append, wP_single] at hr
    exact ⟨p, hp, Or.inr (A1_eq_of' (mul_mem (a1Tab_mem p hp) gP14_mem) hg
      (apply_eq_of_get hr hX _ hkey))⟩
  · exfalso
    have e1 : a[1]! = 1 := beq_iff_eq.1 h1
    have e : g 1 = 1 := by
      rw [h1g]
      exact Fin.ext e1
    exact hne (A1_reg g hg e ▸ one_mem _)
  · exfalso
    have hz' : gP 14 ∈ chZ.grp := by
      rw [← wP_single]
      exact wP_mem_grp (by decide)
    have e2 : (gA 14)[1]! = a[1]! := (beq_iff_eq.1 h2).symm
    have e : gP 14 ⟨1, by norm_num⟩ = g ⟨1, by norm_num⟩ :=
      apply_eq_of_get (p := 1) hz hX (by norm_num) e2
    have f1 : (⟨1, by norm_num⟩ : Fin 693) = 1 := rfl
    rw [f1] at e
    rw [← A1_eq_of gP14_mem hg e] at hne
    exact hne hz'

theorem a1Reps_sq : wP (a1Reps[0]! ++ a1Reps[0]!) = 1 ∧ wP (a1Reps[1]! ++ a1Reps[1]!) = gP 14 := by
  have h0 := a1Reps_check
  unfold a1RepsCheck at h0
  rw [Bool.and_eq_true] at h0
  replace h0 := And.intro (beq_iff_eq.1 h0.1) (beq_iff_eq.1 h0.2)
  have hm : ∀ i < 2, wP (a1Reps[i]! ++ a1Reps[i]!) ∈ chA1.grp := by
    intro i hi
    refine wP_mem_of_letters _ fun k hk => ?_
    have : ∀ i < 2, ∀ k ∈ a1Reps[i]! ++ a1Reps[i]!, [k] ∈ chA1.gens := by decide
    exact this i hi k hk
  have hr0 := rep_wA tabs_check (a1Reps[0]! ++ a1Reps[0]!) (by decide)
  have hr1 := rep_wA tabs_check (a1Reps[1]! ++ a1Reps[1]!) (by decide)
  have hz := rep_gA tabs_check (by norm_num : 14 < 18)
  refine ⟨A1_eq_of' (hm 0 (by norm_num)) (one_mem _) (Fin.ext ((hr0.apply _).symm.trans ?_)),
    A1_eq_of' (hm 1 (by norm_num)) gP14_mem (apply_eq_of_get hr1 hz _ h0.2)⟩
  rw [h0.1]
  rfl

theorem a3Tab_lsgens : ∀ p ∈ a3Tab, (∀ k ∈ p.1, [k] ∈ chLam.gens ∨ [k] ∈ chSig.gens) ∧
    (∀ k ∈ a3Reps[p.2]!, [k] ∈ chA3.gens) := by
  have hq : ∀ p ∈ a3Tab, (∀ k ∈ p.1, k ∈ [0, 1, 15, 4, 17]) ∧ p.2 < 5 := by decide +kernel
  have hK : ∀ k ∈ [0, 1, 15, 4, 17], [k] ∈ chLam.gens ∨ [k] ∈ chSig.gens := by decide
  have hR : ∀ i < 5, ∀ k ∈ a3Reps[i]!, [k] ∈ chA3.gens := by decide
  exact fun p hp => ⟨fun k hk => hK k ((hq p hp).1 k hk), hR _ (hq p hp).2⟩

theorem a3Tab_mem : ∀ p ∈ a3Tab, wP (cjW p.1 a3Reps[p.2]!) ∈ chA3.grp := by
  intro p hp
  have hn : chLam.grp ⊔ chSig.grp ≤ Subgroup.normalizer (chA3.grp : Set _) :=
    sup_le xNorm_spec.2.1 xNorm_spec.2.2.1
  have hq : wP p.1 ∈ chLam.grp ⊔ chSig.grp := by
    have h : ∀ w : List ℕ, (∀ k ∈ w, [k] ∈ chLam.gens ∨ [k] ∈ chSig.gens) →
        wP w ∈ chLam.grp ⊔ chSig.grp := by
      intro w
      induction w with
      | nil =>
        intro _
        simp [wP]
      | cons k w ih =>
        intro hw
        rw [wP_cons]
        refine mul_mem ?_ (ih fun j hj => hw j (List.mem_cons_of_mem k hj))
        rw [← wP_single]
        rcases hw k List.mem_cons_self with h1 | h1
        · exact Subgroup.mem_sup_left (wP_mem_grp h1)
        · exact Subgroup.mem_sup_right (wP_mem_grp h1)
    exact h p.1 (a3Tab_lsgens p hp).1
  have h18 : ∀ k ∈ p.1, k < 18 := fun k hk => by
    have := a3Tab_lt p hp k (by simp [cjW, hk])
    exact this
  rw [cjW, wP_append, wP_append, wP_reverse p.1 h18]
  exact (Subgroup.mem_normalizer_iff.1 (hn hq) _).1
    (wP_mem_of_letters _ (a3Tab_lsgens p hp).2)

theorem A3_stab : ∀ h ∈ chA3.grp, h 205 = 205 → h 251 = 251 → h ∈ chA4.grp := by
  intro h hh h1 h2
  obtain ⟨a, hX, ha⟩ := a3Orb_check h hh
  unfold a3OrbAt at ha
  simp only [Bool.and_eq_true, Bool.or_eq_true, bne_iff_ne, ne_eq] at ha
  rcases ha.1 with (h' | h') | hs
  · exact absurd (by rw [hX.apply (by norm_num : 205 < 693)]; exact congrArg Fin.val h1) h'
  · exact absurd (by rw [hX.apply (by norm_num : 251 < 693)]; exact congrArg Fin.val h2) h'
  · exact (mem_chA4_iff hX).2 hs

theorem a3Orb_spec : ∀ g ∈ chA3.grp, g ∉ chA4.grp → ∃ p ∈ a3Tab,
    (wP (cjW p.1 a3Reps[p.2]!))⁻¹ * g ∈ chA4.grp := by
  intro g hg hne
  obtain ⟨a, hX, ha⟩ := a3Orb_check g hg
  unfold a3OrbAt at ha
  rw [Bool.and_eq_true] at ha
  have ha2 := ha.2
  rw [Bool.or_eq_true, beq_iff_eq] at ha2
  have b1 := hX.lt (by norm_num : 205 < 693)
  have b2 := hX.lt (by norm_num : 251 < 693)
  rcases ha2 with hk | h0
  · rw [← yKeys_spec.2.2.2.1, List.contains_iff_mem, List.mem_map] at hk
    obtain ⟨p, hp, hkey⟩ := hk
    have hr := rep_wA tabs_check _ (a3Tab_lt p hp)
    unfold keyA3 at hkey
    obtain ⟨e1, e2⟩ := keyA3_inj (hr.lt (by norm_num : 251 < 693)) (b2) hkey
    exact ⟨p, hp, A3_stab _ (mul_mem (inv_mem (a3Tab_mem p hp)) hg)
      (inv_mul_fix (apply_eq_of_get hr hX _ e1)) (inv_mul_fix (apply_eq_of_get hr hX _ e2))⟩
  · exfalso
    unfold keyA3 at h0
    obtain ⟨e1, e2⟩ := keyA3_inj (x2 := 205) (y2 := 251) b2 (by norm_num) h0
    exact hne (A3_stab g hg (Fin.ext ((hX.apply (by norm_num : 205 < 693)).symm.trans e1))
      (Fin.ext ((hX.apply (by norm_num : 251 < 693)).symm.trans e2)))

theorem sing_spec : (∀ s ∈ singReps, wP s ∈ chA1.grp ∧ wP s * wP s = 1) ∧
    (∀ i (hi : i < singReps.length) j (hj : j < singReps.length), i ≠ j →
      wP singReps[i] ≠ wP singReps[j] ∧ wP singReps[i] * gP 14 ≠ wP singReps[j]) ∧
    ∀ g ∈ chA1.grp, g * g = 1 → ∃ s ∈ singReps, wP s = g ∨ wP s * gP 14 = g := by
  have h0 := singGen_check
  unfold singGenCheck at h0
  rw [Bool.and_eq_true, decide_eq_true_eq] at h0
  obtain ⟨h1, hnd⟩ := h0
  have hK := yKeys_spec
  have hrep : ∀ s ∈ singReps, Rep 693 (wA s) (wP s) := fun s hs =>
    rep_wA tabs_check _ (singReps_lt s hs)
  have hlet : ∀ s ∈ singReps, ∀ k ∈ s, [k] ∈ chA1.gens := by
    have h1 : ∀ s ∈ singReps, ∀ k ∈ s, k ∈ [0, 1, 5, 6, 9, 10, 12, 13] := by decide +kernel
    have h2 : ∀ k ∈ [0, 1, 5, 6, 9, 10, 12, 13], [k] ∈ chA1.gens := by decide
    exact fun s hs k hk => h2 k (h1 s hs k hk)
  have hmem : ∀ s ∈ singReps, wP s ∈ chA1.grp := fun s hs => wP_mem_of_letters s (hlet s hs)
  have hz := rep_gA tabs_check (by norm_num : 14 < 18)
  have hrepZ : ∀ s ∈ singReps, Rep 693 (wA (s ++ [14])) (wP s * gP 14) := fun s hs => by
    have := rep_wA tabs_check (s ++ [14]) fun k hk =>
      (List.mem_append.1 hk).elim (singReps_lt s hs k) fun h => by simp at h; omega
    rwa [wP_append, wP_single] at this
  have hk1 : singKeys = singReps.map fun s => (wA s)[1]! := hK.2.2.2.2.1.symm
  have hkZ : singKeysZ = singReps.map fun s => (wA (s ++ [14]))[1]! := hK.2.2.2.2.2.symm
  refine ⟨fun s hs => ⟨hmem s hs, ?_⟩, fun i hi j hj hij => ?_, ?_⟩
  · have hsq := List.all_eq_true.1 h1 s hs
    rw [beq_iff_eq] at hsq
    have hr := rep_wA tabs_check (s ++ s) fun k hk =>
      (List.mem_append.1 hk).elim (singReps_lt s hs k) (singReps_lt s hs k)
    rw [wP_append] at hr
    exact A1_eq_of' (mul_mem (hmem s hs) (hmem s hs)) (one_mem _)
      (Fin.ext (by rw [← hr.apply (by norm_num), hsq]; rfl))
  · have hl1 : singKeys.length = singReps.length := by rw [hk1, List.length_map]
    have hlZ : singKeysZ.length = singReps.length := by rw [hkZ, List.length_map]
    have gen : ∀ (f : List ℕ → ℕ) (L : List ℕ), L = singReps.map f →
        ∀ k (hk : k < L.length) (hk' : k < singReps.length), L[k] = f singReps[k] := by
      intro f L hL k hk hk'
      subst hL
      exact List.getElem_map _
    have g1 := gen _ _ hk1 i (hl1 ▸ hi) hi
    have g2 := gen _ _ hk1 j (hl1 ▸ hj) hj
    have g3 := gen _ _ hkZ i (hlZ ▸ hi) hi
    have hd1 : singKeys[i]'(hl1 ▸ hi) ≠ singKeys[j]'(hl1 ▸ hj) := fun he =>
      hij ((List.Nodup.getElem_inj_iff (List.Nodup.of_append_left hnd)).1 he)
    have hd2 : singKeysZ[i]'(hlZ ▸ hi) ≠ singKeys[j]'(hl1 ▸ hj) := fun he =>
      List.disjoint_of_nodup_append hnd (List.getElem_mem _) (he ▸ List.getElem_mem _)
    have hi' := List.getElem_mem hi
    have hj' := List.getElem_mem hj
    refine ⟨fun he => hd1 ?_, fun he => hd2 ?_⟩
    · rw [g1, g2, (hrep _ hi').apply (by norm_num), (hrep _ hj').apply (by norm_num), he]
    · rw [g3, g2, (hrepZ _ hi').apply (by norm_num), (hrep _ hj').apply (by norm_num), he]
  · intro g hg hsq
    obtain ⟨a, hX, ha⟩ := sing_check g hg
    unfold singAt at ha
    simp only [Bool.or_eq_true, bne_iff_ne, ne_eq] at ha
    have h1g : g 1 = ⟨a[1]!, hX.lt (by norm_num)⟩ := Fin.ext (hX.apply (by norm_num)).symm
    rcases ha with (hn | hk) | hk
    · exfalso
      apply hn
      have e : g (g 1) = 1 := by rw [← Equiv.Perm.mul_apply, hsq]; rfl
      rw [hX.apply (hX.lt (by norm_num)), ← h1g, e]
      rfl
    · rw [hk1, List.contains_iff_mem, List.mem_map] at hk
      obtain ⟨s, hs, hkey⟩ := hk
      exact ⟨s, hs, Or.inl (A1_eq_of' (hmem s hs) hg (apply_eq_of_get (hrep s hs) hX _ hkey))⟩
    · rw [hkZ, List.contains_iff_mem, List.mem_map] at hk
      obtain ⟨s, hs, hkey⟩ := hk
      exact ⟨s, hs, Or.inr (A1_eq_of' (mul_mem (hmem s hs) gP14_mem) hg
        (apply_eq_of_get (hrepZ s hs) hX _ hkey))⟩

theorem zCls_spec : (∀ w ∈ chK2.gens, ∀ c ∈ zCls, ∃ c' ∈ zCls,
      wP w * wP c * (wP w)⁻¹ = wP c') ∧
    ∀ j < 20, wP zMs[j]! * gP 14 = gP 14 * wP zMs[j]! ∧
      wP (cjW zMs[j]! zCls[1]!) = wP zCls[j + 1]! := by
  have h0 := zCls_check
  unfold zClsCheck at h0
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range] at h0
  obtain ⟨h1, h2⟩ := h0
  have hrep : ∀ c ∈ zCls, Rep 693 (wA c) (wP c) := fun c hc => rep_wA tabs_check _ (zCls_lt c hc)
  refine ⟨fun w hw c hc => ?_, fun j hj => ?_⟩
  · have hs := all_O_spec (p := fun s => zClsA.all fun c => zClsA.any fun c' =>
      eqA 693 (conjA 693 s c) c') h1 w hw
    have hc' := Array.all_eq_true'.1 hs (wA c) (List.mem_toArray.2 (List.mem_map.2 ⟨c, hc, rfl⟩))
    rw [Array.any_eq_true'] at hc'
    obtain ⟨t, ht, hf⟩ := hc'
    rw [zClsA, List.mem_toArray, List.mem_map] at ht
    obtain ⟨c', hc'', rfl⟩ := ht
    have hv : validA 693 (wA w) :=
      valid_wA_of_O (Array.all_eq_true'.1 valid_spec.2.2.2.2.2.2.2.2.2) hw
    exact ⟨c', hc'', eq_of_eqA (rep_conj hv (rep_wA_gens gensOK_chK2 hw) (hrep c hc))
      (hrep c' hc'') hf⟩
  · have := h2 j hj
    have hm : ∀ k ∈ zMs[j]!, k < 18 := fun k hk => (zMs_lt j hj k hk).1
    have hc1 : ∀ k ∈ zCls[1]!, k < 18 := zCls_lt _ (by decide)
    have hcj : ∀ k ∈ zCls[j + 1]!, k < 18 := zCls_lt _ (by interval_cases j <;> decide)
    have e1 := eq_of_eqA (rep_wA tabs_check _ (fun k hk => (List.mem_append.1 hk).elim (hm k)
      (fun h => by simp at h; omega))) (rep_wA tabs_check _ (fun k hk =>
        (List.mem_append.1 hk).elim (fun h => by simp at h; omega) (hm k))) this.1
    rw [wP_append, wP_append, wP_single] at e1
    refine ⟨e1, eq_of_eqA (rep_wA tabs_check _ ?_) (rep_wA tabs_check _ hcj) this.2⟩
    intro k hk
    simp only [cjW, List.mem_append, List.mem_reverse] at hk
    rcases hk with (h | h) | h
    · exact hm k h
    · exact hc1 k h
    · exact hm k h

end CFSG.EvenSmallLie.UnitarySix.YamadaSec3
