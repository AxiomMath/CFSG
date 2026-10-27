module

public import CFSG.GH74.GLS.Stage2.Bender.Thm2.IVK812PermDefs

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm2.IVK812

open Equiv Equiv.Perm Subgroup

section Reg

variable {T V : Subgroup (Perm (Fin 11))}

private theorem reg_conj_mem (hn : T ≤ normalizer (V : Set (Perm (Fin 11))))
    {t : Perm (Fin 11)} (ht : t ∈ T) {v : Perm (Fin 11)} (hv : v ∈ V) : t * v * t⁻¹ ∈ V :=
  (Subgroup.mem_normalizer_iff.1 (hn ht) v).1 hv

private theorem reg_inv_fix {t : Perm (Fin 11)} (h : t 10 = 10) : t⁻¹ 10 = 10 :=
  Perm.inv_eq_iff_eq.2 h.symm

private theorem reg_stab10 (hT : SylData T) (hD : FixDichotomy T) (hV : IsPGroup 3 ↥V)
    (hn : T ≤ normalizer (V : Set (Perm (Fin 11)))) {v : Perm (Fin 11)} (hv : v ∈ V)
    (h10 : v 10 = 10) : v = 1 := by
  set Y : Subgroup (Perm (Fin 11)) := V ⊓ MulAction.stabilizer (Perm (Fin 11)) (10 : Fin 11)
    with hY
  have hmemY : ∀ y, y ∈ Y ↔ y ∈ V ∧ y 10 = 10 := fun y => by
    simp [hY, Subgroup.mem_inf, MulAction.mem_stabilizer_iff]
  have hYp : IsPGroup 3 ↥Y := hV.to_le inf_le_left
  have hYn : T ≤ normalizer (Y : Set (Perm (Fin 11))) := by
    intro t ht
    rw [Subgroup.mem_normalizer_iff]
    intro y
    have ht10 := hT.fix10 t ht
    rw [hmemY, hmemY, Subgroup.mem_normalizer_iff.1 (hn ht) y]
    simp only [Perm.mul_apply, reg_inv_fix ht10]
    constructor
    · rintro ⟨hy, hy10⟩
      exact ⟨hy, by rw [hy10, ht10]⟩
    · rintro ⟨hy, hy10⟩
      exact ⟨hy, t.injective (hy10.trans ht10.symm)⟩
  by_contra hne
  have hYne : Y ≠ ⊥ := by
    intro h
    have hmem : v ∈ Y := (hmemY v).2 ⟨hv, h10⟩
    rw [h] at hmem
    exact hne (Subgroup.mem_bot.1 hmem)
  have hall : ∀ v ∈ Y, v 10 = 10 := fun y hy => ((hmemY y).1 hy).2
  rcases hD Y hYp hYne hYn with h | h
  · have := (h 10).1 hall
    revert this
    decide
  · have := (h 10).1 hall
    revert this
    decide

private theorem reg_orbit_sub (hfix : ∀ x : Fin 11, (∀ v ∈ V, v x = x) ↔ x = 8 ∨ x = 9)
    {v : Perm (Fin 11)} (hv : v ∈ V) : (v 10).val < 8 ∨ v 10 = 10 := by
  have h8 : v 8 = 8 := (hfix 8).2 (Or.inl rfl) v hv
  have h9 : v 9 = 9 := (hfix 9).2 (Or.inr rfl) v hv
  by_contra hcon
  push Not at hcon
  have hlt := (v 10).isLt
  have hne : (v 10).val ≠ 10 := fun h => hcon.2 (Fin.ext h)
  have hcases : (v 10).val = 8 ∨ (v 10).val = 9 := by omega
  rcases hcases with h | h
  · have h' : v 10 = v 8 := by
      rw [h8]
      exact Fin.ext h
    exact absurd (v.injective h') (by decide)
  · have h' : v 10 = v 9 := by
      rw [h9]
      exact Fin.ext h
    exact absurd (v.injective h') (by decide)

private theorem reg_orbit (hT : SylData T) (hn : T ≤ normalizer (V : Set (Perm (Fin 11))))
    (hfix : ∀ x : Fin 11, (∀ v ∈ V, v x = x) ↔ x = 8 ∨ x = 9) {x : Fin 11} (hx : x.val < 8) :
    ∃ v ∈ V, v 10 = x := by
  have h10 : ¬ ∀ v ∈ V, v 10 = 10 := fun h => by
    have := (hfix 10).1 h
    revert this
    decide
  push Not at h10
  obtain ⟨v₀, hv₀, hne⟩ := h10
  have hx₀ : (v₀ 10).val < 8 := (reg_orbit_sub hfix hv₀).resolve_right hne
  obtain ⟨t, ht, htx⟩ := hT.trans8 _ _ hx₀ hx
  refine ⟨t * v₀ * t⁻¹, reg_conj_mem hn ht hv₀, ?_⟩
  simp only [Perm.mul_apply, reg_inv_fix (hT.fix10 t ht), htx]

private theorem reg_card (hT : SylData T) (hD : FixDichotomy T) (hV : IsPGroup 3 ↥V)
    (hn : T ≤ normalizer (V : Set (Perm (Fin 11))))
    (hfix : ∀ x : Fin 11, (∀ v ∈ V, v x = x) ↔ x = 8 ∨ x = 9) : Nat.card ↥V = 9 := by
  let f : ↥V → {x : Fin 11 // x.val < 8 ∨ x = 10} := fun v => ⟨v.1 10, reg_orbit_sub hfix v.2⟩
  have hf : Function.Bijective f := by
    constructor
    · intro v w hvw
      have h : v.1 10 = w.1 10 := congrArg Subtype.val hvw
      have h1 : w.1⁻¹ * v.1 = 1 :=
        reg_stab10 hT hD hV hn (V.mul_mem (V.inv_mem w.2) v.2)
          (by rw [Perm.mul_apply, h]; simp)
      exact Subtype.ext (inv_mul_eq_one.1 h1).symm
    · rintro ⟨x, hx⟩
      rcases hx with hx | rfl
      · obtain ⟨v, hv, h⟩ := reg_orbit hT hn hfix hx
        exact ⟨⟨v, hv⟩, Subtype.ext h⟩
      · exact ⟨1, Subtype.ext rfl⟩
  rw [Nat.card_congr (Equiv.ofBijective f hf), Nat.card_eq_fintype_card, Fintype.card_subtype]
  decide

private theorem reg_dvd_nine {n : ℕ} (h : n ∣ 9) : n = 1 ∨ n = 3 ∨ n = 9 := by
  have hmem : n ∈ Nat.divisors 9 := Nat.mem_divisors.2 ⟨h, by norm_num⟩
  have h9 : Nat.divisors 9 = {1, 3, 9} := by decide
  rw [h9] at hmem
  simpa using hmem

private theorem reg_two_gen {G : Type*} [Group G] [Finite G] {V : Subgroup G}
    (hcard : Nat.card ↥V = 9) (hV1 : V ≠ ⊥) : ∃ a ∈ V, ∃ b ∈ V, closure {a, b} = V := by
  by_cases hcyc : ∃ a ∈ V, zpowers a = V
  · obtain ⟨a, ha, hza⟩ := hcyc
    exact ⟨a, ha, a, ha, by rw [Set.pair_eq_singleton, ← zpowers_eq_closure, hza]⟩
  · push Not at hcyc
    obtain ⟨⟨a, ha⟩, hne⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hV1
    have ha1 : a ≠ 1 := fun h => hne (Subtype.ext h)
    have hlt : zpowers a < V := lt_of_le_of_ne (zpowers_le.2 ha) (hcyc a ha)
    obtain ⟨b, hb, hbn⟩ := IsConcreteLE.exists_of_lt hlt
    have hH : closure {a, b} ≤ V := by
      rw [closure_le]
      rintro x (rfl | rfl)
      · exact ha
      · exact hb
    have hza : zpowers a ≤ closure {a, b} := by
      rw [zpowers_le]
      exact subset_closure (Set.mem_insert _ _)
    have hbH : b ∈ closure {a, b} := subset_closure (by simp)
    have hdH : Nat.card ↥(closure {a, b}) ∣ 9 := hcard ▸ Subgroup.card_dvd_of_le hH
    have hdA : Nat.card ↥(zpowers a) ∣ Nat.card ↥(closure {a, b}) :=
      Subgroup.card_dvd_of_le hza
    have hA1 : Nat.card ↥(zpowers a) ≠ 1 := fun h =>
      ha1 (zpowers_eq_bot.1 (Subgroup.card_eq_one.1 h))
    have hA9 : Nat.card ↥(zpowers a) ≠ 9 := fun h =>
      hcyc a ha (eq_of_le_of_card_ge (zpowers_le.2 ha) (by rw [hcard, h]))
    have hA3 : Nat.card ↥(zpowers a) = 3 := by
      rcases reg_dvd_nine (hcard ▸ Subgroup.card_dvd_of_le (zpowers_le.2 ha)) with h | h | h
      · exact absurd h hA1
      · exact h
      · exact absurd h hA9
    have hcardH : Nat.card ↥(closure {a, b}) = 9 := by
      rcases reg_dvd_nine hdH with h | h | h
      · rw [h, hA3] at hdA
        exact absurd (Nat.le_of_dvd one_pos hdA) (by norm_num)
      · exfalso
        apply hbn
        have := eq_of_le_of_card_ge hza (by rw [h, hA3])
        rw [this]
        exact hbH
      · exact h
    exact ⟨a, ha, b, hb, eq_of_le_of_card_ge hH (by rw [hcard, hcardH])⟩

private theorem reg_central (hT : SylData T) (hn : T ≤ normalizer (V : Set (Perm (Fin 11))))
    (hfix : ∀ x : Fin 11, (∀ v ∈ V, v x = x) ↔ x = 8 ∨ x = 9) {s : Perm (Fin 11)} (hs : s ∈ T)
    (hc : ∀ v ∈ V, s * v = v * s) : s = 1 := by
  have hs10 := hT.fix10 s hs
  have hpt : ∀ x : Fin 11, (x.val < 8 ∨ x = 10) → s x = x := by
    rintro x (hx | rfl)
    · obtain ⟨v, hv, rfl⟩ := reg_orbit hT hn hfix hx
      have := congrArg (fun p : Perm (Fin 11) => p 10) (hc v hv)
      simpa only [Perm.mul_apply, hs10] using this
    · exact hs10
  have hP : ∀ x : Fin 11, x ≠ 8 → x ≠ 9 → (x.val < 8 ∨ x = 10) := by decide
  have hfx : ∀ x : Fin 11, x ≠ 8 → x ≠ 9 → s x = x := fun x h8 h9 => hpt x (hP x h8 h9)
  have h8 : s 8 = 8 ∨ s 8 = 9 := by
    by_contra h
    push Not at h
    exact h.1 (s.injective (hfx (s 8) h.1 h.2))
  have h9 : s 9 = 8 ∨ s 9 = 9 := by
    by_contra h
    push Not at h
    exact h.2 (s.injective (hfx (s 9) h.1 h.2))
  have hsg := hT.even s hs
  rcases h8 with h8 | h8
  · rcases h9 with h9 | h9
    · exact absurd (s.injective (h9.trans h8.symm)) (by decide)
    · refine Equiv.ext fun x => ?_
      by_cases hx8 : x = 8
      · rw [hx8, h8]
        rfl
      by_cases hx9 : x = 9
      · rw [hx9, h9]
        rfl
      · exact hfx x hx8 hx9
  · rcases h9 with h9 | h9
    · have hs : s = swap 8 9 := by
        refine Equiv.ext fun x => ?_
        by_cases hx8 : x = 8
        · rw [hx8, h8, swap_apply_left]
        by_cases hx9 : x = 9
        · rw [hx9, h9, swap_apply_right]
        · rw [hfx x hx8 hx9, swap_apply_of_ne_of_ne hx8 hx9]
      rw [hs, sign_swap (by decide)] at hsg
      exact absurd hsg (by decide)
    · exact absurd (s.injective (h9.trans h8.symm)) (by decide)

private theorem reg_comm {G : Type*} [Group G] {t t' a : G}
    (h : t * a * t⁻¹ = t' * a * t'⁻¹) : a * (t⁻¹ * t') = t⁻¹ * t' * a :=
  calc a * (t⁻¹ * t') = t⁻¹ * (t * a * t⁻¹) * t' := by group
    _ = t⁻¹ * (t' * a * t'⁻¹) * t' := by rw [h]
    _ = t⁻¹ * t' * a := by group

end Reg

theorem not_fix_two {T : Subgroup (Perm (Fin 11))} (hT : SylData T) (hD : FixDichotomy T)
    {V : Subgroup (Perm (Fin 11))} (hV : IsPGroup 3 ↥V) (hV1 : V ≠ ⊥)
    (hn : T ≤ normalizer (V : Set (Perm (Fin 11))))
    (hfix : ∀ x : Fin 11, (∀ v ∈ V, v x = x) ↔ x = 8 ∨ x = 9) : False := by
  have hcard := reg_card hT hD hV hn hfix
  obtain ⟨a, ha, b, hb, hab⟩ := reg_two_gen hcard hV1
  let φ : ↥T → ↥V × ↥V := fun t =>
    (⟨t.1 * a * t.1⁻¹, reg_conj_mem hn t.2 ha⟩, ⟨t.1 * b * t.1⁻¹, reg_conj_mem hn t.2 hb⟩)
  have hφ : Function.Injective φ := by
    intro t t' h
    have h1 : t.1 * a * t.1⁻¹ = t'.1 * a * t'.1⁻¹ := congrArg (fun p => p.1.1) h
    have h2 : t.1 * b * t.1⁻¹ = t'.1 * b * t'.1⁻¹ := congrArg (fun p => p.2.1) h
    have hle : closure {a, b} ≤ centralizer {t.1⁻¹ * t'.1} := by
      rw [closure_le]
      rintro x (rfl | rfl)
      · exact mem_centralizer_singleton_iff.2 (reg_comm h1)
      · exact mem_centralizer_singleton_iff.2 (reg_comm h2)
    have hs : t.1⁻¹ * t'.1 = 1 := by
      refine reg_central hT hn hfix (T.mul_mem (T.inv_mem t.2) t'.2) fun v hv => ?_
      rw [← hab] at hv
      exact (mem_centralizer_singleton_iff.1 (hle hv)).symm
    exact Subtype.ext (inv_mul_eq_one.1 hs)
  have hle := Nat.card_le_card_of_injective φ hφ
  rw [Nat.card_prod, hT.card, hcard] at hle
  norm_num at hle

end CFSG.GH74.GLS.Stage2.Bender.Thm2.IVK812
