module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.EData

public section

namespace CFSG.EvenSporadicStandard.Fin76b.TableE

open Subgroup

@[expose] def sqrtList (n : ℕ) (mul : ℕ → ℕ → ℕ) (tI : ℕ) : List ℕ :=
  (List.range n).filter fun a => mul a a == tI

@[expose] def eList (n : ℕ) (mul : ℕ → ℕ → ℕ) (tI : ℕ) : List ℕ :=
  let R := sqrtList n mul tI
  (0 :: R ++ R.flatMap (fun x => R.map (mul x))).dedup

@[expose] def eCheck (n : ℕ) (mul : ℕ → ℕ → ℕ) (tI : ℕ) : Bool :=
  let R := sqrtList n mul tI
  let E := eList n mul tI
  let I := E.filter fun a => mul a a == 0 && a != 0
  decide (20 ≤ R.length) &&
    E.contains 0 && E.contains tI && R.all E.contains &&
    E.all (fun a => E.all fun b => E.contains (mul a b)) &&
    E.all (fun a => E.any fun b => mul a b == 0) &&
    E.all (fun a => a == 0 || R.contains a || R.any (fun x => R.any fun y => mul x y == a)) &&
    E.all (fun a => a == 0 || I.contains a || I.any (fun x => I.any fun y => mul x y == a)) &&
    (mul tI tI == 0 && tI != 0) &&
    E.any (fun a => E.any fun b => mul a b != mul b a) &&
    E.all (fun a => E.all fun b => mul a b == mul b a || mul a b == mul (mul b a) tI) &&
    E.all (fun y => !(E.all fun f => mul f y == mul y f) || y == 0 || y == tI) &&
    (List.range n).all (fun a => mul a tI == mul tI a) &&
    (List.range n).all (fun c => !(mul c c == 0 && c != 0 && c != tI) ||
      decide (((List.range n).filter fun a => mul a a == c).length < 20)) &&
    E.all (fun e => (List.range n).all fun a => E.any fun e' => mul a e == mul e' a) &&
    (List.range n).all (fun a => !(E.all fun e => mul a e == mul e a) || a == 0 || a == tI)

theorem sylowEData_of_table {X : Type*} [Group X] {T : Subgroup X} {t b : X}
    (hT : IsPGroup 2 T) (hodd : ∃ m : ℕ, Odd m ∧ Nat.card X = Nat.card T * m)
    (ht2 : t * t = 1) (ht1 : t ≠ 1) (htT : t ∈ T) (htc : ∀ x ∈ T, x * t = t * x)
    (hcen : ∀ y ∈ T, (∀ x ∈ T, x * y = y * x) → y = 1 ∨ y = t) (hsq : ∃ g : X, g * g = t)
    (hcls : ∀ a : X, a * a = 1 → a ≠ 1 →
      (∃ c : X, a = c * t * c⁻¹) ∨ (∃ c : X, a = c * b * c⁻¹))
    (n : ℕ) (elt : ℕ → X) (mul : ℕ → ℕ → ℕ) (tI : ℕ)
    (hmemT : ∀ a < n, elt a ∈ T) (hsurj : ∀ x ∈ T, ∃ a < n, elt a = x)
    (hinj : ∀ a b, a < n → b < n → elt a = elt b → a = b)
    (hmul : ∀ a b, a < n → b < n → mul a b < n ∧ elt a * elt b = elt (mul a b))
    (h0 : elt 0 = 1) (htI : tI < n ∧ elt tI = t) (hn : 0 < n)
    (hconj : ∀ a ∈ eList n mul tI, mul a a = 0 → a ≠ 0 → ∃ c : X, elt a = c * t * c⁻¹)
    (hcheck : eCheck n mul tI = true) : SylowEData X := by
  simp only [eCheck, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.any_eq_true,
    Bool.or_eq_true, Bool.not_eq_true', beq_iff_eq, bne_iff_ne, ne_eq, List.contains_iff_mem,
    List.mem_range, List.mem_filter] at hcheck
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hR20, h0E⟩, htE⟩, hRE⟩, hmulE⟩, hinvE⟩, hRprod⟩, hIprod⟩, ht⟩, hnab⟩,
    hcomm⟩, hcen'⟩, -⟩, hsqrt⟩, hnormT⟩, hcentT⟩ := hcheck
  obtain ⟨htIn, hteq⟩ := htI
  have hRlt : ∀ a ∈ sqrtList n mul tI, a < n ∧ mul a a = tI := by
    intro a ha
    simpa [sqrtList] using ha
  have hElt : ∀ a ∈ eList n mul tI, a < n := by
    intro a ha
    simp only [eList, List.mem_dedup, List.mem_cons, List.mem_append, List.mem_flatMap,
      List.mem_map] at ha
    rcases ha with (ha | ha) | ⟨x, hx, y, hy, hxy⟩
    · rw [ha]; exact hn
    · exact (hRlt a ha).1
    · rw [← hxy]; exact (hmul x y (hRlt x hx).1 (hRlt y hy).1).1
  let E : Subgroup X :=
    { carrier := {x | ∃ a ∈ eList n mul tI, elt a = x}
      mul_mem' := by
        rintro _ _ ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
        exact ⟨mul a b, hmulE a ha b hb, ((hmul a b (hElt a ha) (hElt b hb)).2).symm⟩
      one_mem' := ⟨0, h0E, h0⟩
      inv_mem' := by
        rintro _ ⟨a, ha, rfl⟩
        obtain ⟨b, hb, hab⟩ := hinvE a ha
        refine ⟨b, hb, ?_⟩
        have h1 := (hmul a b (hElt a ha) (hElt b hb)).2
        rw [hab, h0] at h1
        exact eq_inv_of_mul_eq_one_right h1 }
  have hmemE : ∀ x, x ∈ E ↔ ∃ a ∈ eList n mul tI, elt a = x := fun _ => Iff.rfl
  have hsq0 : ∀ a < n, mul a a = 0 ↔ elt a * elt a = 1 := by
    intro a ha
    have h1 := hmul a a ha ha
    constructor
    · intro h; rw [h1.2, h, h0]
    · intro h
      exact hinj _ _ h1.1 hn (by rw [← h1.2, h, h0])
  have hne0 : ∀ a < n, a ≠ 0 ↔ elt a ≠ 1 := by
    intro a ha
    constructor
    · intro h h'; exact h (hinj a 0 ha hn (by rw [h', h0]))
    · intro h h'; exact h (by rw [h', h0])
  have hinvol : ∀ x ∈ eList n mul tI, mul x x = 0 → x ≠ 0 →
      elt x ∈ E ∧ elt x * elt x = 1 ∧ elt x ≠ 1 := fun x hx h1 h2 =>
    ⟨⟨x, hx, rfl⟩, (hsq0 x (hElt x hx)).1 h1, (hne0 x (hElt x hx)).1 h2⟩
  have hfinE : Finite E := by
    have : (E : Set X) ⊆ elt '' ((eList n mul tI).toFinset : Set ℕ) := by
      rintro _ ⟨a, ha, rfl⟩
      exact ⟨a, by simpa using ha, rfl⟩
    exact (Set.finite_coe_iff).2 (((Finset.finite_toSet _).image elt).subset this)
  refine ⟨T, E, t, b, hT, hodd, ht2, ht1, htT, htc, hcen, hsq, hcls, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_⟩
  · rintro _ ⟨a, ha, rfl⟩
    exact hmemT a (hElt a ha)
  · exact ⟨tI, htE, hteq⟩
  · intro e he he2 he1
    obtain ⟨a, ha, rfl⟩ := he
    exact hconj a ha ((hsq0 a (hElt a ha)).2 he2) ((hne0 a (hElt a ha)).2 he1)
  · apply le_antisymm
    · rintro _ ⟨a, ha, rfl⟩
      rcases hIprod a ha with (h | ⟨h1, h2, h3⟩) |
        ⟨x₁, ⟨hx₁, hx₁2, hx₁0⟩, x₂, ⟨hx₂, hx₂2, hx₂0⟩, hx⟩
      · rw [h, h0]; exact one_mem _
      · exact subset_closure (hinvol a h1 h2 h3)
      · rw [← hx, ← (hmul x₁ x₂ (hElt x₁ hx₁) (hElt x₂ hx₂)).2]
        exact mul_mem (subset_closure (hinvol x₁ hx₁ hx₁2 hx₁0))
          (subset_closure (hinvol x₂ hx₂ hx₂2 hx₂0))
    · rw [closure_le]
      exact fun e he => he.1
  · obtain ⟨a, ha, b', hb, hne⟩ := hnab
    refine ⟨elt a, ⟨a, ha, rfl⟩, elt b', ⟨b', hb, rfl⟩, fun h => hne ?_⟩
    exact hinj _ _ (hmul a b' (hElt a ha) (hElt b' hb)).1 (hmul b' a (hElt b' hb) (hElt a ha)).1
      (by rw [← (hmul a b' (hElt a ha) (hElt b' hb)).2, ← (hmul b' a (hElt b' hb) (hElt a ha)).2]
          exact h)
  · rintro _ ⟨a, ha, rfl⟩ _ ⟨b', hb, rfl⟩
    have hat : (elt a)⁻¹ * t = t * (elt a)⁻¹ := htc _ (inv_mem (hmemT a (hElt a ha)))
    have hbt : elt b' * t = t * elt b' := htc _ (hmemT b' (hElt b' hb))
    rcases hcomm a ha b' hb with h1 | h1
    · left
      have h2 : elt a * elt b' = elt b' * elt a := by
        rw [(hmul a b' (hElt a ha) (hElt b' hb)).2, (hmul b' a (hElt b' hb) (hElt a ha)).2, h1]
      calc elt a * elt b' * (elt a)⁻¹ * (elt b')⁻¹ = elt b' * elt a * (elt a)⁻¹ * (elt b')⁻¹ := by
            rw [h2]
        _ = 1 := by group
    · right
      have h2 : elt a * elt b' = elt b' * elt a * t := by
        have e1 := (hmul a b' (hElt a ha) (hElt b' hb)).2
        have e2 := (hmul b' a (hElt b' hb) (hElt a ha)).2
        have e3 := (hmul (mul b' a) tI (hmul b' a (hElt b' hb) (hElt a ha)).1 htIn).2
        rw [e1, h1, ← e3, ← e2, hteq]
      calc elt a * elt b' * (elt a)⁻¹ * (elt b')⁻¹
          = elt b' * elt a * (t * (elt a)⁻¹) * (elt b')⁻¹ := by rw [h2]; group
        _ = elt b' * elt a * ((elt a)⁻¹ * t) * (elt b')⁻¹ := by rw [hat]
        _ = elt b' * t * (elt b')⁻¹ := by group
        _ = t * elt b' * (elt b')⁻¹ := by rw [hbt]
        _ = t := by group
  · rintro _ ⟨a, ha, rfl⟩ hc
    have hall : ((eList n mul tI).all fun f => mul f a == mul a f) = true := by
      rw [List.all_eq_true]
      intro f hf
      rw [beq_iff_eq]
      exact hinj _ _ (hmul f a (hElt f hf) (hElt a ha)).1 (hmul a f (hElt a ha) (hElt f hf)).1
        (by rw [← (hmul f a (hElt f hf) (hElt a ha)).2, ← (hmul a f (hElt a ha) (hElt f hf)).2]
            exact hc (elt f) ⟨f, hf, rfl⟩)
    rcases hcen' a ha with (h | h) | h
    · rw [hall] at h; exact absurd h (by decide)
    · left; rw [h, h0]
    · right; rw [h, hteq]
  · intro P hP hiso
    obtain ⟨φ⟩ := hiso
    have hRmemE : ∀ a ∈ sqrtList n mul tI, elt a ∈ E := fun a ha => ⟨a, hRE a ha, rfl⟩
    have hRsq : ∀ a ∈ sqrtList n mul tI, elt a * elt a = t := by
      intro a ha
      obtain ⟨hlt, hmm⟩ := hRlt a ha
      rw [(hmul a a hlt hlt).2, hmm, hteq]
    have htEmem : t ∈ E := ⟨tI, htE, hteq⟩
    set c : X := (φ ⟨t, htEmem⟩ : X) with hcdef
    have hcP : c ∈ P := (φ ⟨t, htEmem⟩).2
    have hcT : c ∈ T := hP hcP
    have hcc : c * c = 1 := by
      have h1 : φ ⟨t, htEmem⟩ * φ ⟨t, htEmem⟩ = 1 := by
        rw [← map_mul]
        have : (⟨t, htEmem⟩ : E) * ⟨t, htEmem⟩ = 1 := Subtype.ext ht2
        rw [this, map_one]
      exact congrArg Subtype.val h1
    have hc1 : c ≠ 1 := by
      intro h
      have h1 : φ ⟨t, htEmem⟩ = 1 := Subtype.ext h
      have h2 : (⟨t, htEmem⟩ : E) = 1 := φ.injective (by rw [h1, map_one])
      exact ht1 (congrArg Subtype.val h2)
    let g : ℕ → ℕ := fun a =>
      if h : a ∈ sqrtList n mul tI then
        Classical.choose (hsurj (φ ⟨elt a, hRmemE a h⟩ : X) (hP (φ ⟨elt a, hRmemE a h⟩).2))
      else 0
    have hg : ∀ a (h : a ∈ sqrtList n mul tI),
        g a < n ∧ elt (g a) = (φ ⟨elt a, hRmemE a h⟩ : X) := by
      intro a h
      simp only [g, h, ↓reduceDIte]
      exact Classical.choose_spec (hsurj (φ ⟨elt a, hRmemE a h⟩ : X)
        (hP (φ ⟨elt a, hRmemE a h⟩).2))
    have hφsq : ∀ a (h : a ∈ sqrtList n mul tI),
        (φ ⟨elt a, hRmemE a h⟩ : X) * (φ ⟨elt a, hRmemE a h⟩ : X) = c := by
      intro a h
      have h1 : (⟨elt a, hRmemE a h⟩ : E) * ⟨elt a, hRmemE a h⟩ = ⟨t, htEmem⟩ :=
        Subtype.ext (hRsq a h)
      have h2 : φ ⟨elt a, hRmemE a h⟩ * φ ⟨elt a, hRmemE a h⟩ = φ ⟨t, htEmem⟩ := by
        rw [← map_mul, h1]
      exact congrArg Subtype.val h2
    have hct : c = t := by
      by_contra hne
      obtain ⟨k, hk, hkc⟩ := hsurj c hcT
      have hkk : mul k k = 0 := (hsq0 k hk).2 (by rw [hkc]; exact hcc)
      have hk0 : k ≠ 0 := (hne0 k hk).2 (by rw [hkc]; exact hc1)
      have hktI : k ≠ tI := fun h => hne (by rw [← hkc, h, hteq])
      rcases hsqrt k hk with h | hlt
      · simp [hkk, hk0, hktI] at h
      · have hmap : ∀ a ∈ sqrtList n mul tI,
            g a ∈ (List.range n).filter (fun a => mul a a == k) := by
          intro a ha
          obtain ⟨hlt', hel⟩ := hg a ha
          simp only [List.mem_filter, List.mem_range, beq_iff_eq]
          refine ⟨hlt', hinj _ _ (hmul _ _ hlt' hlt').1 hk ?_⟩
          rw [← (hmul _ _ hlt' hlt').2, hel, hkc, hφsq a ha]
        have hinjg : ∀ a ∈ sqrtList n mul tI, ∀ a' ∈ sqrtList n mul tI, g a = g a' → a = a' := by
          intro a ha a' ha' h
          have e1 := (hg a ha).2
          have e2 := (hg a' ha').2
          have h3 : (φ ⟨elt a, hRmemE a ha⟩ : X) = φ ⟨elt a', hRmemE a' ha'⟩ := by
            rw [← e1, ← e2, h]
          have h4 := congrArg Subtype.val (φ.injective (Subtype.ext h3))
          exact hinj a a' (hRlt a ha).1 (hRlt a' ha').1 h4
        have hcard : (sqrtList n mul tI).toFinset.card ≤
            ((List.range n).filter (fun a => mul a a == k)).toFinset.card :=
          Finset.card_le_card_of_injOn g (fun a ha => by
            simpa using hmap a (by simpa using ha))
            (fun a ha a' ha' h => hinjg a (by simpa using ha) a' (by simpa using ha') h)
        have hRnd : (sqrtList n mul tI).Nodup := List.nodup_range.filter _
        rw [List.toFinset_card_of_nodup hRnd] at hcard
        have h5 := List.toFinset_card_le ((List.range n).filter (fun a => mul a a == k))
        omega
    have hφR : ∀ a (h : a ∈ sqrtList n mul tI), (φ ⟨elt a, hRmemE a h⟩ : X) ∈ E := by
      intro a h
      obtain ⟨hlt', hel⟩ := hg a h
      have hmem : g a ∈ sqrtList n mul tI := by
        simp only [sqrtList, List.mem_filter, List.mem_range, beq_iff_eq]
        refine ⟨hlt', hinj _ _ (hmul _ _ hlt' hlt').1 htIn ?_⟩
        rw [← (hmul _ _ hlt' hlt').2, hel, hφsq a h, hct, hteq]
      rw [← hel]
      exact hRmemE _ hmem
    have hPE : P ≤ E := by
      intro p hp
      obtain ⟨e, he⟩ := φ.surjective ⟨p, hp⟩
      have hpe : p = (φ e : X) := (congrArg Subtype.val he).symm
      rw [hpe]
      obtain ⟨a, ha, hae⟩ := e.2
      have hea : e = ⟨elt a, ⟨a, ha, rfl⟩⟩ := Subtype.ext hae.symm
      rcases hRprod a ha with (h | h) | ⟨x, hx, y, hy, hxy⟩
      · have : e = 1 := by rw [hea]; exact Subtype.ext (by simp [h, h0])
        rw [this, map_one]
        exact one_mem E
      · have : e = ⟨elt a, hRmemE a h⟩ := hea
        rw [this]
        exact hφR a h
      · have : e = ⟨elt x, hRmemE x hx⟩ * ⟨elt y, hRmemE y hy⟩ := by
          rw [hea]
          exact Subtype.ext (by
            simp only [Subgroup.coe_mul]
            rw [← hxy, (hmul x y (hRlt x hx).1 (hRlt y hy).1).2])
        rw [this, map_mul]
        exact mul_mem (hφR x hx) (hφR y hy)
    exact Subgroup.eq_of_le_of_card_ge hPE (Nat.card_congr φ.toEquiv).le
  · rintro s hs _ ⟨b', hb, rfl⟩
    obtain ⟨a, ha, rfl⟩ := hsurj s hs
    obtain ⟨e', he', hee'⟩ := hnormT b' hb a ha
    refine ⟨e', he', ?_⟩
    have h1 := (hmul a b' ha (hElt b' hb)).2
    have h2 := (hmul e' a (hElt e' he') ha).2
    have h3 : elt a * elt b' = elt e' * elt a := by rw [h1, h2, hee']
    refine Eq.symm ?_
    calc elt a * elt b' * (elt a)⁻¹ = elt e' * elt a * (elt a)⁻¹ := by rw [h3]
      _ = elt e' := by group
  · rintro s hs hc
    obtain ⟨a, ha, rfl⟩ := hsurj s hs
    have hall : ((eList n mul tI).all fun e => mul a e == mul e a) = true := by
      rw [List.all_eq_true]
      intro e he
      rw [beq_iff_eq]
      exact hinj _ _ (hmul a e ha (hElt e he)).1 (hmul e a (hElt e he) ha).1
        (by rw [← (hmul a e ha (hElt e he)).2, ← (hmul e a (hElt e he) ha).2]
            exact hc (elt e) ⟨e, he, rfl⟩)
    rcases hcentT a ha with (h | h) | h
    · rw [hall] at h; exact absurd h (by decide)
    · left; rw [h, h0]
    · right; rw [h, hteq]

end CFSG.EvenSporadicStandard.Fin76b.TableE
