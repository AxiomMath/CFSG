module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3SporLineGroup

public section

namespace CFSG.QuasithinUnique.A5.Kc3SporLine

section Greedy

variable {Γ : Type} [Group Γ]

theorem ite_congr_bit {f f' : Γ} {a s t : ℕ} (ha : a < 2 ^ t) (h : s < t → f = f') :
    (if a.testBit s then f else 1) = (if a.testBit s then f' else 1) := by
  by_cases hs : s < t
  · rw [h hs]
  · have : a.testBit s = false :=
      Nat.testBit_eq_false_of_lt
        (lt_of_lt_of_le ha (Nat.pow_le_pow_right (by norm_num) (by omega)))
    simp [this]

theorem gE_congr {f f' : Fin 4 → Γ} {t : ℕ} (h : ∀ s : Fin 4, (s : ℕ) < t → f s = f' s)
    {a : ℕ} (ha : a < 2 ^ t) : gE f a = gE f' a := by
  unfold gE
  rw [ite_congr_bit (f := f 0) (f' := f' 0) ha (fun hs => h 0 (by simpa using hs)),
    ite_congr_bit (f := f 1) (f' := f' 1) ha (fun hs => h 1 (by simpa using hs)),
    ite_congr_bit (f := f 2) (f' := f' 2) ha (fun hs => h 2 (by simpa using hs)),
    ite_congr_bit (f := f 3) (f' := f' 3) ha (fun hs => h 3 (by simpa using hs))]

theorem gE_two_pow (f : Fin 4 → Γ) (t : Fin 4) : gE f (2 ^ (t : ℕ)) = f t := by
  fin_cases t
  · exact gE_two_pow_0 f
  · exact gE_two_pow_1 f
  · exact gE_two_pow_2 f
  · exact gE_two_pow_3 f

variable {g : Fin 4 → Γ}

theorem gE_ne_one_of_new (hsq : ∀ t, g t * g t = 1) (hc : ∀ s t, g s * g t = g t * g s)
    (hnew : ∀ t : Fin 4, ∀ a < 2 ^ (t : ℕ), g t ≠ gE g a) {c : ℕ} (hc1 : 1 ≤ c) (hc16 : c < 16) :
    gE g c ≠ 1 := by
  have hdec : ∀ c < 16, 1 ≤ c → ∃ t : Fin 4, ∃ c' < 2 ^ (t : ℕ), c = c' ^^^ 2 ^ (t : ℕ) := by
    decide +kernel
  obtain ⟨t, c', hc', rfl⟩ := hdec c hc16 hc1
  intro h
  apply hnew t c' hc'
  have h1 : gE g (c' ^^^ 2 ^ (t : ℕ)) = gE g c' * g t := by
    rw [gE_xor g hsq hc, gE_two_pow]
  rw [h1] at h
  exact mul_left_cancel (h.trans (gE_self_mul g hsq hc c').symm)

theorem gE_label_inj (hsq : ∀ t, g t * g t = 1) (hc : ∀ s t, g s * g t = g t * g s)
    (hnew : ∀ t : Fin 4, ∀ a < 2 ^ (t : ℕ), g t ≠ gE g a) {a b : ℕ} (ha : a < 16) (hb : b < 16)
    (h : gE g a = gE g b) : a = b := by
  have h1 : gE g (a ^^^ b) = 1 := by
    rw [gE_xor g hsq hc, h]
    exact gE_self_mul g hsq hc b
  by_contra hne
  have hx : a ^^^ b ≠ 0 := fun h0 => hne (Nat.eq_of_xor_eq_zero h0)
  exact gE_ne_one_of_new hsq hc hnew (Nat.pos_of_ne_zero hx) (xor_lt_16 ha hb) h1

end Greedy

section Exists

variable {Γ : Type} [Group Γ] [Finite Γ] {E : Subgroup Γ} (num : Γ → ℕ)

theorem exists_pick (hcard : Nat.card E = 16) (g : Fin 4 → Γ) {t : ℕ} (ht : t ≤ 3) :
    ∃ x ∈ E, (∀ a < 2 ^ t, x ≠ gE g a) ∧
      ∀ y ∈ E, (∀ a < 2 ^ t, y ≠ gE g a) → num x ≤ num y := by
  classical
  set S : Set Γ := {y | y ∈ E ∧ ∀ a < 2 ^ t, y ≠ gE g a} with hS
  have hne : S.Nonempty := by
    by_contra hemp
    rw [Set.not_nonempty_iff_eq_empty] at hemp
    have hsub : (E : Set Γ) ⊆ ((Finset.range (2 ^ t)).image (gE g) : Finset Γ) := by
      intro y hy
      by_contra hyn
      have : y ∈ S := by
        refine ⟨hy, fun a ha hya => hyn ?_⟩
        rw [Finset.mem_coe, Finset.mem_image]
        exact ⟨a, Finset.mem_range.2 ha, hya.symm⟩
      rw [hemp] at this
      exact this
    have h1 := Set.ncard_le_ncard hsub (Finset.finite_toSet _)
    rw [Set.ncard_coe_finset] at h1
    have h2 : (E : Set Γ).ncard = 16 := by rw [← Nat.card_coe_set_eq]; exact hcard
    have h3 := Finset.card_image_le (s := Finset.range (2 ^ t)) (f := gE g)
    rw [Finset.card_range] at h3
    have h4 : 2 ^ t ≤ 8 := by
      calc 2 ^ t ≤ 2 ^ 3 := Nat.pow_le_pow_right (by norm_num) ht
        _ = 8 := by norm_num
    omega
  obtain ⟨x, hx, hmin⟩ := Set.exists_min_image S num (Set.toFinite S) hne
  exact ⟨x, hx.1, hx.2, fun y hy hy' => hmin y ⟨hy, hy'⟩⟩

@[expose] def GreedyUpTo (E : Subgroup Γ) (num : Γ → ℕ) (t : ℕ) (g : Fin 4 → Γ) : Prop :=
  ∀ s : Fin 4, (s : ℕ) < t → g s ∈ E ∧ (∀ a < 2 ^ (s : ℕ), g s ≠ gE g a) ∧
    ∀ y ∈ E, (∀ a < 2 ^ (s : ℕ), y ≠ gE g a) → num (g s) ≤ num y

theorem exists_greedyUpTo (hcard : Nat.card E = 16) :
    ∀ t ≤ 4, ∃ g : Fin 4 → Γ, GreedyUpTo E num t g := by
  intro t
  induction t with
  | zero =>
    intro _
    exact ⟨fun _ => 1, fun s hs => absurd hs (Nat.not_lt_zero _)⟩
  | succ t ih =>
    intro ht
    obtain ⟨g, hg⟩ := ih (by omega)
    obtain ⟨x, hxE, hxnew, hxmin⟩ := exists_pick num hcard g (t := t) (by omega)
    have ht4 : t < 4 := by omega
    let g' : Fin 4 → Γ := Function.update g ⟨t, ht4⟩ x
    have hg'lt : ∀ s : Fin 4, (s : ℕ) < t → g' s = g s := by
      intro s hs
      have : s ≠ ⟨t, ht4⟩ := fun h => by
        have := congrArg Fin.val h
        simp at this
        omega
      simp [g', Function.update_of_ne this]
    have hgE : ∀ a < 2 ^ t, gE g' a = gE g a := fun a ha =>
      (gE_congr (fun s hs => (hg'lt s hs).symm) ha).symm
    refine ⟨g', fun s hs => ?_⟩
    by_cases hst : (s : ℕ) < t
    · obtain ⟨h1, h2, h3⟩ := hg s hst
      have hs2 : 2 ^ (s : ℕ) ≤ 2 ^ t := Nat.pow_le_pow_right (by norm_num) hst.le
      refine ⟨by rw [hg'lt s hst]; exact h1, fun a ha => ?_, fun y hy hy' => ?_⟩
      · rw [hg'lt s hst, hgE a (lt_of_lt_of_le ha hs2)]
        exact h2 a ha
      · rw [hg'lt s hst]
        exact h3 y hy fun a ha => by
          rw [← hgE a (lt_of_lt_of_le ha hs2)]
          exact hy' a ha
    · have hseq : s = ⟨t, ht4⟩ := Fin.ext (by show (s : ℕ) = t; omega)
      subst hseq
      have hgt : g' ⟨t, ht4⟩ = x := by simp [g']
      simp only [hgt]
      refine ⟨hxE, fun a ha => ?_, fun y hy hy' => hxmin y hy fun a ha => ?_⟩
      · rw [hgE a ha]
        exact hxnew a ha
      · rw [← hgE a ha]
        exact hy' a ha

end Exists

section Existence

variable {Γ : Type} [Group Γ]

@[expose] def Greedy (num : Γ → ℕ) (g : Fin 4 → Γ) : Prop :=
  ∀ t : ℕ, t < 4 → ∀ q : ℕ, q < 16 → 2 ^ t < q → num (gE g (2 ^ t)) < num (gE g q)

variable [Finite Γ]

theorem exists_greedy {E : Subgroup Γ} (hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x)
    (hsq : ∀ x ∈ E, x * x = 1) (hcard : Nat.card E = 16) (num : Γ → ℕ)
    (hnum : ∀ x ∈ E, x ≠ 1 → ∀ y ∈ E, y ≠ 1 → num x = num y → x = y) :
    ∃ g : Fin 4 → Γ, (∀ t, g t ∈ E) ∧ E4 g = E ∧ Greedy num g := by
  obtain ⟨g, hg⟩ := exists_greedyUpTo num hcard 4 le_rfl
  have hgE : ∀ t, g t ∈ E := fun t => (hg t (by omega)).1
  have hnew : ∀ t : Fin 4, ∀ a < 2 ^ (t : ℕ), g t ≠ gE g a := fun t => (hg t (by omega)).2.1
  have hmin := fun t : Fin 4 => (hg t (by omega)).2.2
  have hsq' : ∀ t, g t * g t = 1 := fun t => hsq _ (hgE t)
  have hc' : ∀ s t, g s * g t = g t * g s := fun s t => hcomm _ (hgE s) _ (hgE t)
  have hle : E4 g ≤ E := by
    rw [E4, Subgroup.closure_le]
    rintro _ ⟨t, rfl⟩
    exact hgE t
  have hEg : E4 g = E := by
    refine Subgroup.eq_of_le_of_card_ge hle ?_
    let L : Fin 16 → E4 g := fun a => ⟨gE g a, gE_mem g a⟩
    have hL : Function.Injective L := by
      intro a b hab
      exact Fin.ext (gE_label_inj hsq' hc' hnew a.2 b.2 (congrArg Subtype.val hab))
    have := Nat.card_le_card_of_injective L hL
    rw [Nat.card_eq_fintype_card (α := Fin 16), Fintype.card_fin] at this
    rw [hcard]
    exact this
  refine ⟨g, hgE, hEg, fun t ht q hq htq => ?_⟩
  have hqE : gE g q ∈ E := hEg ▸ gE_mem g q
  have hq1 : gE g q ≠ 1 :=
    gE_ne_one_of_new hsq' hc' hnew (by have := Nat.one_le_two_pow (n := t); omega) hq
  have ht16 : 2 ^ t < 16 := by
    calc 2 ^ t ≤ 2 ^ 3 := Nat.pow_le_pow_right (by norm_num) (by omega)
      _ < 16 := by norm_num
  have hgt : gE g (2 ^ t) = g ⟨t, ht⟩ := gE_two_pow g ⟨t, ht⟩
  have hgt1 : g ⟨t, ht⟩ ≠ 1 := by
    rw [← hgt]
    exact gE_ne_one_of_new hsq' hc' hnew (Nat.one_le_two_pow) ht16
  have hle' : num (g ⟨t, ht⟩) ≤ num (gE g q) :=
    hmin ⟨t, ht⟩ _ hqE fun a ha hqa => by
      have := gE_label_inj hsq' hc' hnew hq (lt_trans ha ht16) hqa
      simp only at ha
      omega
  rw [hgt]
  refine lt_of_le_of_ne hle' fun heq => ?_
  have := hnum _ (hgE _) hgt1 _ hqE hq1 heq
  have hlab := gE_label_inj hsq' hc' hnew ht16 hq (by rw [hgt]; exact this)
  omega

end Existence

end CFSG.QuasithinUnique.A5.Kc3SporLine
