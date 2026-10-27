module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5BHeartCoord

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

private def T (a b c : Fin 8) : Equiv.Perm (Fin 8) := Equiv.swap a b * Equiv.swap b c

private def cast6 (i : Fin 6) : Fin 8 := Fin.castLE (by norm_num) i

private lemma cast6_ne {u v : Fin 6} (h : u ≠ v) : cast6 u ≠ cast6 v := by
  intro hh
  exact h (Fin.ext (by simpa [cast6] using congrArg Fin.val hh))

private lemma six_ne_cast6 (v : Fin 6) : (6 : Fin 8) ≠ cast6 v := by
  intro h
  have hv := v.isLt
  have := congrArg Fin.val h
  simp [cast6] at this
  omega

private lemma seven_ne_cast6 (v : Fin 6) : (7 : Fin 8) ≠ cast6 v := by
  intro h
  have hv := v.isLt
  have := congrArg Fin.val h
  simp [cast6] at this
  omega

private lemma T_conj (f : Equiv.Perm (Fin 8)) (a b c : Fin 8) :
    f * T a b c * f⁻¹ = T (f a) (f b) (f c) := by
  rw [T, T]
  rw [show f * (Equiv.swap a b * Equiv.swap b c) * f⁻¹ =
      (f * Equiv.swap a b * f⁻¹) * (f * Equiv.swap b c * f⁻¹) by group]
  rw [Equiv.swap_apply_apply, Equiv.swap_apply_apply]

private lemma T_inv : ∀ a b c : Fin 8, a ≠ b → a ≠ c → b ≠ c → (T a b c)⁻¹ = T a c b := by
  decide +kernel

private lemma extPerm_six : ∀ σ : Equiv.Perm (Fin 6), extPerm σ 6 = 6 ∧ extPerm σ 7 = 7 := by
  decide +kernel

private lemma extPerm_cast : ∀ (σ : Equiv.Perm (Fin 6)) (i : Fin 6),
    extPerm σ (cast6 i) = cast6 (σ i) := by
  decide +kernel

private lemma extPerm_T : ∀ a b c : Fin 6,
    extPerm (Equiv.swap a b * Equiv.swap b c) = T (cast6 a) (cast6 b) (cast6 c) := by
  decide +kernel

private lemma a6_transitive : ∀ u v : Fin 6,
    ∃ g : Equiv.Perm (Fin 6), Equiv.Perm.sign g = 1 ∧ g u = v := by
  decide +kernel

private lemma exists_third : ∀ a b : Fin 8, a.val < 6 → b.val < 6 → a ≠ b →
    ∃ d : Fin 8, d.val < 6 ∧ d ≠ a ∧ d ≠ b := by
  decide +kernel

private lemma T_prod : ∀ u v : Fin 6, u ≠ v →
    (T 6 7 (cast6 u))⁻¹ * T 6 7 (cast6 v) = T 7 (cast6 v) (cast6 u) := by
  decide +kernel

private lemma T6w7_seven : ∀ w : Fin 6, T 6 (cast6 w) 7 7 = 6 := by
  decide +kernel

private lemma T6w7_fix : ∀ w u : Fin 6, w ≠ u → T 6 (cast6 w) 7 (cast6 u) = cast6 u := by
  decide +kernel

private lemma T_canon_red : ∀ a b c : Fin 8, a ≠ b → a ≠ c → b ≠ c →
    (a.val < 6 ∧ b.val < 6 ∧ c.val < 6) ∨
    (∃ u v : Fin 6, u ≠ v ∧ ((T a b c = T 6 (cast6 u) (cast6 v)) ∨
        (T a b c = (T 6 (cast6 u) (cast6 v))⁻¹))) ∨
    (∃ u : Fin 6, (T a b c = T 6 7 (cast6 u)) ∨ (T a b c = (T 6 7 (cast6 u))⁻¹)) ∨
    (∃ u v : Fin 6, u ≠ v ∧ ((T a b c = T 7 (cast6 u) (cast6 v)) ∨
        (T a b c = (T 7 (cast6 u) (cast6 v))⁻¹))) := by
  decide +kernel

private lemma T_mem_X {H : Subgroup (Equiv.Perm (Fin 8))}
    (h6 : ∀ σ ∈ alternatingGroup (Fin 6), extPerm σ ∈ H)
    (a b c : Fin 8) (ha : a.val < 6) (hb : b.val < 6) (hc : c.val < 6)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) : T a b c ∈ H := by
  let a' : Fin 6 := ⟨a.val, ha⟩
  let b' : Fin 6 := ⟨b.val, hb⟩
  let c' : Fin 6 := ⟨c.val, hc⟩
  have hab' : a' ≠ b' := fun h => hab (Fin.ext (by simpa [a', b'] using congrArg Fin.val h))
  have hac' : a' ≠ c' := fun h => hac (Fin.ext (by simpa [a', c'] using congrArg Fin.val h))
  have hbc' : b' ≠ c' := fun h => hbc (Fin.ext (by simpa [b', c'] using congrArg Fin.val h))
  have h3 : Equiv.Perm.IsThreeCycle (Equiv.swap a' b' * Equiv.swap b' c') := by
    have := Equiv.Perm.isThreeCycle_swap_mul_swap_same (a := b') (b := a') (c := c')
      (Ne.symm hab') hbc' hac'
    simpa [Equiv.swap_comm] using this
  have hmem : extPerm (Equiv.swap a' b' * Equiv.swap b' c') ∈ H :=
    h6 _ (Equiv.Perm.IsThreeCycle.mem_alternatingGroup h3)
  have hcast_a : cast6 a' = a := by simp [cast6, a']
  have hcast_b : cast6 b' = b := by simp [cast6, b']
  have hcast_c : cast6 c' = c := by simp [cast6, c']
  have hkey : extPerm (Equiv.swap a' b' * Equiv.swap b' c') = T a b c := by
    rw [extPerm_T, hcast_a, hcast_b, hcast_c]
  rwa [hkey] at hmem

private lemma T67_mem {H : Subgroup (Equiv.Perm (Fin 8))}
    (h6 : ∀ σ ∈ alternatingGroup (Fin 6), extPerm σ ∈ H)
    (hmove : ∃ x ∈ H, (x 6).val < 6 ∧ (x 7).val < 6) :
    ∀ u : Fin 6, T 6 7 (cast6 u) ∈ H := by
  obtain ⟨x, hxH, hx6, hx7⟩ := hmove
  have h67 : (6 : Fin 8) ≠ 7 := by decide
  have hab : x 6 ≠ x 7 := by
    intro h
    apply h67
    have := congrArg (⇑x⁻¹) h
    simpa using this
  obtain ⟨d, hd6, hda, hdb⟩ := exists_third (x 6) (x 7) hx6 hx7 hab
  have hT : T (x 6) (x 7) d ∈ H :=
    T_mem_X h6 (x 6) (x 7) d hx6 hx7 hd6 hab (Ne.symm hda) (Ne.symm hdb)
  have hconj : x⁻¹ * T (x 6) (x 7) d * x = T (x⁻¹ (x 6)) (x⁻¹ (x 7)) (x⁻¹ d) := by
    simpa using T_conj x⁻¹ (x 6) (x 7) d
  have hmem : T 6 7 (x⁻¹ d) ∈ H := by
    have hh : x⁻¹ * T (x 6) (x 7) d * x ∈ H :=
      H.mul_mem (H.mul_mem (H.inv_mem hxH) hT) hxH
    rw [hconj] at hh
    simpa using hh
  have hu0 : (x⁻¹ d).val < 6 := by
    have h1 := (x⁻¹ d).isLt
    have h2 : (x⁻¹ d) ≠ 6 := by
      intro h
      apply hda
      have := congrArg x h
      simpa using this
    have h3 : (x⁻¹ d) ≠ 7 := by
      intro h
      apply hdb
      have := congrArg x h
      simpa using this
    have hv2 : (x⁻¹ d).val ≠ 6 := fun h => h2 (Fin.ext h)
    have hv3 : (x⁻¹ d).val ≠ 7 := fun h => h3 (Fin.ext h)
    omega
  intro u
  obtain ⟨g, hgsign, hgu⟩ := a6_transitive ⟨(x⁻¹ d).val, hu0⟩ u
  have hgH : extPerm g ∈ H := h6 g (Equiv.Perm.mem_alternatingGroup.mpr hgsign)
  have hconj2 := T_conj (extPerm g) 6 7 (x⁻¹ d)
  have hcast : cast6 ⟨(x⁻¹ d).val, hu0⟩ = x⁻¹ d := by simp [cast6]
  have h2 : extPerm g (x⁻¹ d) = cast6 u := by
    rw [← hcast, extPerm_cast, hgu]
  have heq : extPerm g * T 6 7 (x⁻¹ d) * (extPerm g)⁻¹ = T 6 7 (cast6 u) := by
    obtain ⟨hs6, hs7⟩ := extPerm_six g
    rw [hconj2, hs6, hs7, h2]
  have hh : extPerm g * T 6 7 (x⁻¹ d) * (extPerm g)⁻¹ ∈ H :=
    H.mul_mem (H.mul_mem hgH hmem) (H.inv_mem hgH)
  rwa [heq] at hh

private lemma T7_mem {H : Subgroup (Equiv.Perm (Fin 8))}
    (h67 : ∀ u : Fin 6, T 6 7 (cast6 u) ∈ H) :
    ∀ u v : Fin 6, u ≠ v → T 7 (cast6 u) (cast6 v) ∈ H := by
  intro u v huv
  have hprod := T_prod u v huv
  have hmem : T 7 (cast6 v) (cast6 u) ∈ H := by
    rw [← hprod]
    exact H.mul_mem (H.inv_mem (h67 u)) (h67 v)
  have hinv : (T 7 (cast6 v) (cast6 u))⁻¹ ∈ H := H.inv_mem hmem
  have heq : (T 7 (cast6 v) (cast6 u))⁻¹ = T 7 (cast6 u) (cast6 v) :=
    T_inv 7 (cast6 v) (cast6 u) (seven_ne_cast6 v) (seven_ne_cast6 u) (cast6_ne huv.symm)
  rwa [heq] at hinv

private lemma T6_mem {H : Subgroup (Equiv.Perm (Fin 8))}
    (h67 : ∀ u : Fin 6, T 6 7 (cast6 u) ∈ H)
    (h7 : ∀ u v : Fin 6, u ≠ v → T 7 (cast6 u) (cast6 v) ∈ H) :
    ∀ u v : Fin 6, u ≠ v → T 6 (cast6 u) (cast6 v) ∈ H := by
  intro u v huv
  obtain ⟨w, hw6, hwv, hwu⟩ :=
    exists_third (cast6 v) (cast6 u) (by simpa [cast6] using v.isLt)
      (by simpa [cast6] using u.isLt) (cast6_ne huv.symm)
  let w' : Fin 6 := ⟨w.val, hw6⟩
  have hwcast : cast6 w' = w := by simp [cast6, w']
  have hwv' : w' ≠ v := fun h => hwv (by rw [← hwcast, h])
  have hwu' : w' ≠ u := fun h => hwu (by rw [← hwcast, h])
  have hw7 : T 6 (cast6 w') 7 ∈ H := by
    have hh := H.inv_mem (h67 w')
    rwa [T_inv 6 7 (cast6 w') (by decide) (six_ne_cast6 w') (seven_ne_cast6 w')] at hh
  have hmem : T 6 (cast6 v) (cast6 u) ∈ H := by
    have hh : T 6 (cast6 w') 7 * T 7 (cast6 v) (cast6 u) * (T 6 (cast6 w') 7)⁻¹ ∈ H :=
      H.mul_mem (H.mul_mem hw7 (h7 v u huv.symm)) (H.inv_mem hw7)
    rw [T_conj (T 6 (cast6 w') 7) 7 (cast6 v) (cast6 u)] at hh
    rwa [T6w7_seven w', T6w7_fix w' v hwv', T6w7_fix w' u hwu'] at hh
  have hinv : (T 6 (cast6 v) (cast6 u))⁻¹ ∈ H := H.inv_mem hmem
  have heq : (T 6 (cast6 v) (cast6 u))⁻¹ = T 6 (cast6 u) (cast6 v) :=
    T_inv 6 (cast6 v) (cast6 u) (six_ne_cast6 v) (six_ne_cast6 u) (cast6_ne huv.symm)
  rwa [heq] at hinv

private lemma T_all {H : Subgroup (Equiv.Perm (Fin 8))}
    (hX : ∀ a b c : Fin 8, a.val < 6 → b.val < 6 → c.val < 6 →
      a ≠ b → a ≠ c → b ≠ c → T a b c ∈ H)
    (h67 : ∀ u : Fin 6, T 6 7 (cast6 u) ∈ H)
    (h6 : ∀ u v : Fin 6, u ≠ v → T 6 (cast6 u) (cast6 v) ∈ H)
    (h7 : ∀ u v : Fin 6, u ≠ v → T 7 (cast6 u) (cast6 v) ∈ H) :
    ∀ a b c : Fin 8, a ≠ b → a ≠ c → b ≠ c → T a b c ∈ H := by
  intro a b c hab hac hbc
  rcases T_canon_red a b c hab hac hbc with h | ⟨u, v, huv, h | h⟩ | ⟨u, h | h⟩ |
    ⟨u, v, huv, h | h⟩
  · exact hX a b c h.1 h.2.1 h.2.2 hab hac hbc
  · rw [h]; exact h6 u v huv
  · rw [h]; exact H.inv_mem (h6 u v huv)
  · rw [h]; exact h67 u
  · rw [h]; exact H.inv_mem (h67 u)
  · rw [h]; exact h7 u v huv
  · rw [h]; exact H.inv_mem (h7 u v huv)

theorem sec5b_alt8_le {H : Subgroup (Equiv.Perm (Fin 8))}
    (h6 : ∀ σ ∈ alternatingGroup (Fin 6), extPerm σ ∈ H)
    (hmove : ∃ x ∈ H, (x 6).val < 6 ∧ (x 7).val < 6) :
    alternatingGroup (Fin 8) ≤ H := by
  have hX := T_mem_X h6
  have h67 := T67_mem h6 hmove
  have h7 := T7_mem h67
  have h6' := T6_mem h67 h7
  have hTall := T_all hX h67 h6' h7
  rw [← Equiv.Perm.closure_three_cycles_eq_alternating]
  rw [Subgroup.closure_le]
  intro σ hσ
  obtain ⟨a, ha⟩ := hσ.isCycle.nonempty_support
  have hnodup := hσ.nodup_iff_mem_support.mpr ha
  have ha1 : a ≠ σ a := by
    intro hh
    have hmem : a ∈ [σ a, σ (σ a)] := by
      simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false]
      exact Or.inl hh
    exact (List.nodup_cons.mp hnodup).1 hmem
  have ha2 : a ≠ σ (σ a) := by
    intro hh
    have hmem : a ∈ [σ a, σ (σ a)] := by
      simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false]
      exact Or.inr hh
    exact (List.nodup_cons.mp hnodup).1 hmem
  have h12 : σ a ≠ σ (σ a) := by
    intro hh
    have hmem : σ a ∈ [σ (σ a)] := by
      simp only [List.mem_singleton, List.not_mem_nil, or_false]
      exact hh
    exact (List.nodup_cons.mp (List.nodup_cons.mp hnodup).2).1 hmem
  have heq : σ = T a (σ a) (σ (σ a)) := by
    have := hσ.eq_swap_mul_swap_iff_mem_support.mpr ha
    simpa [T] using this
  rw [heq]
  exact hTall a (σ a) (σ (σ a)) ha1 ha2 h12

theorem sec5b_alt8_cases {H : Subgroup (Equiv.Perm (Fin 8))} (h : alternatingGroup (Fin 8) ≤ H) :
    H = alternatingGroup (Fin 8) ∨ H = ⊤ := by
  have hdiv : H.index ∣ 2 := by
    have := Subgroup.index_dvd_of_le h
    rwa [alternatingGroup.index_eq_two] at this
  rcases (Nat.dvd_prime Nat.prime_two).mp hdiv with h1 | h2
  · right
    exact Subgroup.index_eq_one.mp h1
  · left
    exact Equiv.Perm.eq_alternatingGroup_of_index_eq_two h2

end CFSG.OddStandard.SmallF3.Omega
