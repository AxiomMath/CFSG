module

public import CFSG.LocalAnalysis.ComponentClassification.AS81Inputs

public section

namespace CFSG.ComponentClassification.AS81

section Plane

variable {P : Type} [Finite P] (line : P → P → Set P)

@[expose] def linesOf : Set (Set P) := {ℓ | ∃ p q : P, p ≠ q ∧ ℓ = line p q}

variable {line}
variable (hmem : ∀ p q : P, p ≠ q → p ∈ line p q ∧ q ∈ line p q)
  (heq : ∀ p q r s : P, p ≠ q → r ≠ s → r ∈ line p q → s ∈ line p q → line r s = line p q)
  (hcard : ∀ p q : P, p ≠ q → (line p q).ncard = 4)
  (hP : Nat.card P = 16)

omit [Finite P] in
include heq in
theorem eq_of_mem_linesOf {ℓ m : Set P} (hℓ : ℓ ∈ linesOf line) (hm : m ∈ linesOf line)
    {a b : P} (hab : a ≠ b) (haℓ : a ∈ ℓ) (hbℓ : b ∈ ℓ) (ham : a ∈ m) (hbm : b ∈ m) : ℓ = m := by
  obtain ⟨p, q, hpq, rfl⟩ := hℓ
  obtain ⟨r, s, hrs, rfl⟩ := hm
  rw [← heq p q a b hpq hab haℓ hbℓ, heq r s a b hrs hab ham hbm]

include hmem heq hcard hP in
theorem isAffinePlane_of_line : IsAffinePlane P (linesOf line) := by
  classical
  have := Fintype.ofFinite P
  have hlines : ∀ p q : P, p ≠ q → line p q ∈ linesOf line := fun p q hpq => ⟨p, q, hpq, rfl⟩
  have hcardF : ∀ p q : P, p ≠ q → (line p q).toFinset.card = 4 := fun p q hpq => by
    rw [← Set.ncard_eq_toFinset_card']
    exact hcard p q hpq
  have huniv : (Finset.univ : Finset P).card = 16 := by
    rw [Finset.card_univ, ← Nat.card_eq_fintype_card, hP]
  refine ⟨fun p q hpq => ⟨line p q, ⟨hlines p q hpq, hmem p q hpq⟩, ?_⟩, ?_, ?_⟩
  · rintro m ⟨hm, hpm, hqm⟩
    exact (eq_of_mem_linesOf heq (hlines p q hpq) hm hpq (hmem p q hpq).1
      (hmem p q hpq).2 hpm hqm).symm
  ·
    rintro ℓ hℓ p hpℓ
    obtain ⟨r, s, hrs, hℓdef⟩ := hℓ
    have hℓl : ℓ ∈ linesOf line := hℓdef ▸ hlines r s hrs
    have hapℓ : ∀ a ∈ ℓ, a ≠ p := fun a ha h => hpℓ (h ▸ ha)
    have hpa : ∀ a, a ≠ p → ∀ x ∈ line p a, x ≠ p → line p x = line p a := fun a hap x hx hxp =>
      heq p a p x hap.symm hxp.symm (hmem p a hap.symm).1 hx
    have hone : ∀ a ∈ ℓ, ∀ b ∈ ℓ, a ≠ b → ∀ x ∈ line p a, x ∈ line p b → x = p := by
      intro a ha b hb hab x hxa hxb
      by_contra hxp
      apply hpℓ
      have h1 := hpa a (hapℓ a ha) x hxa hxp
      have h2 := hpa b (hapℓ b hb) x hxb hxp
      have hbl : b ∈ line p a := h1 ▸ h2.symm ▸ (hmem p b (hapℓ b hb).symm).2
      have := eq_of_mem_linesOf heq (hlines p a (hapℓ a ha).symm) hℓl hab
        (hmem p a (hapℓ a ha).symm).2 hbl ha hb
      rw [← this]
      exact (hmem p a (hapℓ a ha).symm).1
    set t : P → Finset P := fun a => (line p a).toFinset.erase p
    set U : Finset P := ℓ.toFinset.biUnion t
    have hUdisj : (ℓ.toFinset : Set P).PairwiseDisjoint t := by
      intro a ha b hb hab
      simp only [Set.coe_toFinset] at ha hb
      rw [Function.onFun, Finset.disjoint_left]
      intro x hxa hxb
      simp only [t, Finset.mem_erase, Set.mem_toFinset] at hxa hxb
      exact hxa.1 (hone a ha b hb hab x hxa.2 hxb.2)
    have hUcard : U.card = 12 := by
      rw [Finset.card_biUnion hUdisj, Finset.sum_const_nat (m := 3)]
      · rw [← Set.ncard_eq_toFinset_card', hℓdef, hcard r s hrs]
      · intro a ha
        simp only [Set.mem_toFinset] at ha
        simp only [t]
        rw [Finset.card_erase_of_mem (by simpa using (hmem p a (hapℓ a ha).symm).1),
          hcardF p a (hapℓ a ha).symm]
    set S : Finset P := (Finset.univ.erase p) \ U
    have hUsub : U ⊆ Finset.univ.erase p := by
      intro x hx
      simp only [U, t, Finset.mem_biUnion, Finset.mem_erase] at hx
      obtain ⟨a, -, hxp, -⟩ := hx
      exact Finset.mem_erase.mpr ⟨hxp, Finset.mem_univ x⟩
    have hScard : S.card = 3 := by
      rw [Finset.card_sdiff_of_subset hUsub, Finset.card_erase_of_mem (Finset.mem_univ p), huniv,
        hUcard]
    have hmiss : ∀ m ∈ linesOf line, p ∈ m → Disjoint ℓ m → m.toFinset.erase p = S := by
      intro m hm hpm hdm
      obtain ⟨u, v, huv, rfl⟩ := hm
      have hsub : (line u v).toFinset.erase p ⊆ S := by
        intro x hx
        simp only [Finset.mem_erase, Set.mem_toFinset] at hx
        refine Finset.mem_sdiff.mpr ⟨Finset.mem_erase.mpr ⟨hx.1, Finset.mem_univ x⟩, ?_⟩
        intro hxU
        simp only [U, t, Finset.mem_biUnion, Finset.mem_erase, Set.mem_toFinset] at hxU
        obtain ⟨a, ha, -, hxa⟩ := hxU
        have h1 := hpa a (hapℓ a ha) x hxa hx.1
        have h2 : line p x = line u v :=
          heq u v p x huv (fun h => hx.1 h.symm) hpm hx.2
        apply Set.disjoint_left.mp hdm ha
        rw [← h2, h1]
        exact (hmem p a (hapℓ a ha).symm).2
      refine Finset.eq_of_subset_of_card_le hsub ?_
      rw [hScard, Finset.card_erase_of_mem (by simpa using hpm)]
      have := hcardF u v huv
      omega
    obtain ⟨x, hxS⟩ : S.Nonempty := Finset.card_pos.mp (by omega)
    have hxp : x ≠ p := (Finset.mem_erase.mp (Finset.mem_sdiff.mp hxS).1).1
    have hdisj : Disjoint ℓ (line p x) := by
      rw [Set.disjoint_left]
      intro a ha hax
      have hxa : x ∈ line p a := by
        rw [hpa x hxp a hax (hapℓ a ha)]
        exact (hmem p x hxp.symm).2
      apply (Finset.mem_sdiff.mp hxS).2
      simp only [U, t, Finset.mem_biUnion, Finset.mem_erase, Set.mem_toFinset]
      exact ⟨a, ha, hxp, hxa⟩
    refine ⟨line p x, ⟨hlines p x hxp.symm, (hmem p x hxp.symm).1, hdisj⟩, ?_⟩
    rintro m ⟨hm, hpm, hdm⟩
    have h1 := hmiss m hm hpm hdm
    have h2 := hmiss (line p x) (hlines p x hxp.symm) (hmem p x hxp.symm).1 hdisj
    ext y
    by_cases hyp : y = p
    · rw [hyp]
      exact ⟨fun _ => (hmem p x hxp.symm).1, fun _ => hpm⟩
    · have := congrArg (fun F : Finset P => y ∈ F) (h1.trans h2.symm)
      simpa [hyp] using this
  ·
    obtain ⟨p, q, hpq⟩ : ∃ p q : P, p ≠ q := by
      by_contra h
      push Not at h
      have : (Finset.univ : Finset P).card ≤ 1 := Finset.card_le_one.mpr fun a _ b _ => h a b
      omega
    obtain ⟨x, hx⟩ : ∃ x, x ∉ line p q := by
      by_contra h
      push Not at h
      have : (Finset.univ : Finset P) ⊆ (line p q).toFinset := fun y _ => by simpa using h y
      have := Finset.card_le_card this
      rw [huniv, hcardF p q hpq] at this
      omega
    refine ⟨p, q, x, ?_⟩
    rintro ⟨m, hm, hpm, hqm, hxm⟩
    apply hx
    rw [eq_of_mem_linesOf heq (hlines p q hpq) hm hpq (hmem p q hpq).1 (hmem p q hpq).2
      hpm hqm]
    exact hxm

end Plane

end CFSG.ComponentClassification.AS81
