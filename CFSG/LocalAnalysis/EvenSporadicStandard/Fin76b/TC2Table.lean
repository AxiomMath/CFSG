module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TC2Data
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TC2TableSpec

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open Subgroup TableX

section Facts

variable {Y : Type*} [Group Y] {n : ℕ} {inn : ℕ → Bool} {elt : ℕ → MulAut Y}
  {mul : ℕ → ℕ → ℕ} {tI : ℕ} {t : Y}

theorem exists_outerEFacts_of_card [Finite (MulAut Y)] (ht2 : t * t = 1) (ht1 : t ≠ 1)
    (hinj : ∀ a b, a < n → b < n → elt a = elt b → a = b)
    (hmul : ∀ a b, a < n → b < n → mul a b < n ∧ elt a * elt b = elt (mul a b))
    (h0 : elt 0 = 1) (htI : tI < n ∧ elt tI = MulAut.conj t)
    (hInn : ∀ a, a < n → inn a = true → ∃ y : Y, elt a = MulAut.conj y)
    (hconj : ∀ a, a < n → inn a = true → a ∈ eListX n inn mul tI → mul a a = 0 → a ≠ 0 →
      ∃ c : Y, elt a = MulAut.conj (c * t * c⁻¹))
    (hspec : CheckSpec0 n inn mul tI)
    (hcard : ∀ E : Subgroup (MulAut Y), (∀ x, x ∈ E ↔ ∃ a ∈ eListX n inn mul tI, elt a = x) →
      (∀ a ∈ eListX n inn mul tI, a < n) → Nat.card (MulAut ↥E) = 1920) :
    ∃ K E : Subgroup (MulAut Y), OuterEFacts Y K t E ∧ ∀ x, x ∈ K ↔ ∃ a, a < n ∧ elt a = x := by
  classical
  have hn : 0 < n := by have := hspec.n_eq; omega
  set El := eListX n inn mul tI with hEl
  set R := rootsIn n inn mul tI with hR
  have hRlt : ∀ a ∈ R, a < n ∧ inn a = true ∧ mul a a = tI := fun a ha => by
    obtain ⟨⟨h1, h2⟩, h3⟩ := mem_rootsIn.1 ha
    exact ⟨h1, h2, h3⟩
  have hElt : ∀ a ∈ El, a < n ∧ inn a = true := by
    intro a ha
    rcases mem_eListX.1 ha with rfl | h | ⟨x, hx, y, hy, rfl⟩
    · exact ⟨hn, hspec.inn_zero⟩
    · exact ⟨(hRlt a h).1, (hRlt a h).2.1⟩
    · obtain ⟨hx1, hx2, -⟩ := hRlt x hx
      obtain ⟨hy1, hy2, -⟩ := hRlt y hy
      exact ⟨(hmul x y hx1 hy1).1, hspec.inn_closed x hx1 hx2 y hy1 hy2⟩
  let K : Subgroup (MulAut Y) :=
    { carrier := {x | ∃ a, a < n ∧ elt a = x}
      mul_mem' := by
        rintro _ _ ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
        exact ⟨mul a b, (hmul a b ha hb).1, ((hmul a b ha hb).2).symm⟩
      one_mem' := ⟨0, hn, h0⟩
      inv_mem' := by
        rintro _ ⟨a, ha, rfl⟩
        obtain ⟨b, hb, hab⟩ := hspec.inv a ha
        refine ⟨b, hb, ?_⟩
        have h1 := (hmul a b ha hb).2
        rw [hab, h0] at h1
        exact eq_inv_of_mul_eq_one_right h1 }
  let E : Subgroup (MulAut Y) :=
    { carrier := {x | ∃ a ∈ El, elt a = x}
      mul_mem' := by
        rintro _ _ ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
        exact ⟨mul a b, hspec.E_mul a ha b hb, ((hmul a b (hElt a ha).1 (hElt b hb).1).2).symm⟩
      one_mem' := ⟨0, hspec.E_zero, h0⟩
      inv_mem' := by
        rintro _ ⟨a, ha, rfl⟩
        obtain ⟨b, hb, hab⟩ := hspec.E_inv a ha
        refine ⟨b, hb, ?_⟩
        have h1 := (hmul a b (hElt a ha).1 (hElt b hb).1).2
        rw [hab, h0] at h1
        exact eq_inv_of_mul_eq_one_right h1 }
  have hsq0 : ∀ a < n, mul a a = 0 ↔ elt a * elt a = 1 := by
    intro a ha
    have h1 := hmul a a ha ha
    constructor
    · intro h
      rw [h1.2, h, h0]
    · intro h
      exact hinj _ _ h1.1 hn (by rw [← h1.2, h, h0])
  have hne0 : ∀ a < n, a ≠ 0 ↔ elt a ≠ 1 := by
    intro a ha
    constructor
    · intro h h'
      exact h (hinj a 0 ha hn (by rw [h', h0]))
    · intro h h'
      exact h (by rw [h', h0])
  have hcommK : ∀ a b, a < n → b < n → (mul a b = mul b a ↔ elt a * elt b = elt b * elt a) := by
    intro a b ha hb
    constructor
    · intro h
      rw [(hmul a b ha hb).2, (hmul b a hb ha).2, h]
    · intro h
      exact hinj _ _ (hmul a b ha hb).1 (hmul b a hb ha).1
        (by rw [← (hmul a b ha hb).2, ← (hmul b a hb ha).2]; exact h)
  have htcentral : ∀ a < n, elt a * elt tI = elt tI * elt a := fun a ha =>
    (hcommK a tI ha htI.1).1 (hspec.t_central a ha)
  have hRmemE : ∀ a ∈ R, elt a ∈ E := fun a ha => ⟨a, hspec.E_roots a ha, rfl⟩
  have hRsq : ∀ a ∈ R, elt a * elt a = MulAut.conj t := by
    intro a ha
    obtain ⟨hlt, -, hmm⟩ := hRlt a ha
    rw [(hmul a a hlt hlt).2, hmm, htI.2]
  have htEmem : MulAut.conj t ∈ E := ⟨tI, hspec.E_t, htI.2⟩
  have hRnd : R.Nodup := by
    simp only [hR, rootsIn, innList]
    exact (List.nodup_range.filter _).filter _
  refine ⟨K, E, ?_, fun x => Iff.rfl⟩
  refine
  { t_sq := ht2
    t_ne := ht1
    conj_mem := ⟨tI, htI.1, htI.2⟩
    center := ?_
    card_S := ?_
    card_aut := ?_
    E_le := ?_
    E_inner := ?_
    t_mem := ⟨tI, hspec.E_t, htI.2⟩
    E_conj := ?_
    E_gen := ?_
    E_roots := ?_
    E_roots_ge := ?_
    E_nonab := ?_
    E_comm := ?_
    E_center := ?_
    unique := ?_
    cent := ?_ }
  · intro α hα
    obtain ⟨a, ha, rfl⟩ := hα
    constructor
    · intro hall
      have hc : ∀ x, x < n → mul x a = mul a x := fun x hx =>
        (hcommK x a hx ha).2 (hall (elt x) ⟨x, hx, rfl⟩)
      rcases hspec.K_center a ha hc with rfl | rfl
      · exact Or.inl h0
      · exact Or.inr htI.2
    · rintro (h | h) _ ⟨x, hx, rfl⟩
      · rw [h]; simp
      · have ha' : a = tI := hinj _ _ ha htI.1 (by rw [h, htI.2])
        subst ha'
        exact htcentral x hx
  · have e : Fin n ≃ K := Equiv.ofBijective (fun a => ⟨elt a, ⟨a, a.2, rfl⟩⟩)
      ⟨fun a b hab => Fin.ext (hinj a b a.2 b.2 (congrArg Subtype.val hab)),
        fun ⟨x, a, ha, hax⟩ => ⟨⟨a, ha⟩, Subtype.ext hax⟩⟩
    rw [← Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_fin]
    exact hspec.n_eq
  · exact hcard E (fun x => Iff.rfl) fun a ha => (hElt a ha).1
  · rintro _ ⟨a, ha, rfl⟩
    exact ⟨a, (hElt a ha).1, rfl⟩
  · rintro _ ⟨a, ha, rfl⟩
    exact hInn a (hElt a ha).1 (hElt a ha).2
  · rintro _ ⟨a, ha, rfl⟩ he2 he1
    exact hconj a (hElt a ha).1 (hElt a ha).2 ha ((hsq0 a (hElt a ha).1).2 he2)
      ((hne0 a (hElt a ha).1).2 he1)
  · apply le_antisymm
    · rintro _ ⟨a, ha, rfl⟩
      rcases hspec.E_prod_invol a ha with h | ⟨h1, h2, h3⟩ |
        ⟨x, hx, hx2, hx0, y, hy, hy2, hy0, hxy⟩
      · rw [h, h0]; exact one_mem _
      · exact subset_closure ⟨⟨a, h1, rfl⟩, (hsq0 a (hElt a h1).1).1 h2,
          (hne0 a (hElt a h1).1).1 h3⟩
      · rw [← hxy, ← (hmul x y (hElt x hx).1 (hElt y hy).1).2]
        exact mul_mem
          (subset_closure ⟨⟨x, hx, rfl⟩, (hsq0 x (hElt x hx).1).1 hx2,
            (hne0 x (hElt x hx).1).1 hx0⟩)
          (subset_closure ⟨⟨y, hy, rfl⟩, (hsq0 y (hElt y hy).1).1 hy2,
            (hne0 y (hElt y hy).1).1 hy0⟩)
    · rw [closure_le]
      exact fun e he => he.1
  · apply le_antisymm
    · rintro _ ⟨a, ha, rfl⟩
      rcases hspec.E_prod_roots a ha with h | h | ⟨x, hx, y, hy, hxy⟩
      · rw [h, h0]; exact one_mem _
      · exact subset_closure ⟨hRmemE a h, hRsq a h⟩
      · rw [← hxy, ← (hmul x y (hRlt x hx).1 (hRlt y hy).1).2]
        exact mul_mem (subset_closure ⟨hRmemE x hx, hRsq x hx⟩)
          (subset_closure ⟨hRmemE y hy, hRsq y hy⟩)
    · rw [closure_le]
      exact fun e he => he.1
  · have himg : elt '' (R.toFinset : Set ℕ) ⊆ {ε | ε ∈ E ∧ ε * ε = MulAut.conj t} := by
      rintro _ ⟨a, ha, rfl⟩
      have ha' : a ∈ R := by simpa using ha
      exact ⟨hRmemE a ha', hRsq a ha'⟩
    have hinjOn : Set.InjOn elt (R.toFinset : Set ℕ) := by
      intro a ha b hb hab
      exact hinj a b (hRlt a (by simpa using ha)).1 (hRlt b (by simpa using hb)).1 hab
    have h1 : (elt '' (R.toFinset : Set ℕ)).ncard = R.length := by
      rw [hinjOn.ncard_image, Set.ncard_coe_finset,
        List.toFinset_card_of_nodup hRnd]
    calc 20 ≤ R.length := hspec.roots_ge
      _ = (elt '' (R.toFinset : Set ℕ)).ncard := h1.symm
      _ ≤ _ := Set.ncard_le_ncard himg (Set.toFinite _)
  · obtain ⟨a, ha, b, hb, hne⟩ := hspec.E_nonab
    exact ⟨elt a, ⟨a, ha, rfl⟩, elt b, ⟨b, hb, rfl⟩, fun h =>
      hne ((hcommK a b (hElt a ha).1 (hElt b hb).1).2 h)⟩
  · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    have ha' := (hElt a ha).1
    have hb' := (hElt b hb).1
    have hat : (elt a)⁻¹ * elt tI = elt tI * (elt a)⁻¹ := by
      have := htcentral a ha'
      calc (elt a)⁻¹ * elt tI = (elt a)⁻¹ * (elt tI * elt a) * (elt a)⁻¹ := by group
        _ = (elt a)⁻¹ * (elt a * elt tI) * (elt a)⁻¹ := by rw [this]
        _ = elt tI * (elt a)⁻¹ := by group
    rcases hspec.E_comm a ha b hb with h | h
    · left
      have h2 : elt a * elt b = elt b * elt a := (hcommK a b ha' hb').1 h
      calc elt a * elt b * (elt a)⁻¹ * (elt b)⁻¹ = elt b * elt a * (elt a)⁻¹ * (elt b)⁻¹ := by
            rw [h2]
        _ = 1 := by group
    · right
      have h2 : elt a * elt b = elt b * elt a * elt tI := by
        have e1 := (hmul a b ha' hb').2
        have e2 := (hmul b a hb' ha').2
        have e3 := (hmul (mul b a) tI (hmul b a hb' ha').1 htI.1).2
        rw [e1, h, ← e3, ← e2]
      rw [← htI.2]
      calc elt a * elt b * (elt a)⁻¹ * (elt b)⁻¹
          = elt b * elt a * (elt tI * (elt a)⁻¹) * (elt b)⁻¹ := by rw [h2]; group
        _ = elt b * elt a * ((elt a)⁻¹ * elt tI) * (elt b)⁻¹ := by rw [hat]
        _ = elt b * elt tI * (elt b)⁻¹ := by group
        _ = elt tI * elt b * (elt b)⁻¹ := by rw [htcentral b hb']
        _ = elt tI := by group
  · rintro _ ⟨a, ha, rfl⟩ hc
    have hall : ∀ f ∈ El, mul f a = mul a f := fun f hf =>
      (hcommK f a (hElt f hf).1 (hElt a ha).1).2 (hc (elt f) ⟨f, hf, rfl⟩)
    rcases hspec.E_center a ha hall with rfl | rfl
    · exact Or.inl h0
    · exact Or.inr htI.2
  · intro P hP hiso
    obtain ⟨φ⟩ := hiso
    have hconjt1 : MulAut.conj t ≠ 1 := by
      rw [← htI.2]
      exact (hne0 tI htI.1).1 hspec.t_invol.2
    set c : MulAut Y := (φ ⟨MulAut.conj t, htEmem⟩ : MulAut Y) with hcdef
    have hcP : c ∈ P := (φ ⟨MulAut.conj t, htEmem⟩).2
    have hcK : c ∈ K := hP hcP
    have hcc : c * c = 1 := by
      have h1 : φ ⟨MulAut.conj t, htEmem⟩ * φ ⟨MulAut.conj t, htEmem⟩ = 1 := by
        rw [← map_mul]
        have : (⟨MulAut.conj t, htEmem⟩ : ↥E) * ⟨MulAut.conj t, htEmem⟩ = 1 :=
          Subtype.ext (show MulAut.conj t * MulAut.conj t = 1 by rw [← map_mul, ht2, map_one])
        rw [this, map_one]
      exact congrArg Subtype.val h1
    have hc1 : c ≠ 1 := by
      intro h
      have h1 : φ ⟨MulAut.conj t, htEmem⟩ = 1 := Subtype.ext h
      have h2 : (⟨MulAut.conj t, htEmem⟩ : ↥E) = 1 := φ.injective (by rw [h1, map_one])
      exact hconjt1 (congrArg Subtype.val h2)
    let g : ℕ → ℕ := fun a =>
      if h : a ∈ R then
        Classical.choose (hP (φ ⟨elt a, hRmemE a h⟩).2 :
          ∃ b, b < n ∧ elt b = (φ ⟨elt a, hRmemE a h⟩ : MulAut Y))
      else 0
    have hg : ∀ a (h : a ∈ R), g a < n ∧ elt (g a) = (φ ⟨elt a, hRmemE a h⟩ : MulAut Y) := by
      intro a h
      simp only [g, h, ↓reduceDIte]
      exact Classical.choose_spec (hP (φ ⟨elt a, hRmemE a h⟩).2 :
        ∃ b, b < n ∧ elt b = (φ ⟨elt a, hRmemE a h⟩ : MulAut Y))
    have hφsq : ∀ a (h : a ∈ R),
        (φ ⟨elt a, hRmemE a h⟩ : MulAut Y) * (φ ⟨elt a, hRmemE a h⟩ : MulAut Y) = c := by
      intro a h
      have h1 : (⟨elt a, hRmemE a h⟩ : ↥E) * ⟨elt a, hRmemE a h⟩ = ⟨MulAut.conj t, htEmem⟩ :=
        Subtype.ext (hRsq a h)
      have h2 : φ ⟨elt a, hRmemE a h⟩ * φ ⟨elt a, hRmemE a h⟩ = φ ⟨MulAut.conj t, htEmem⟩ := by
        rw [← map_mul, h1]
      exact congrArg Subtype.val h2
    have hR20 : 20 ≤ R.length := hspec.roots_ge
    have hginj : ∀ a ∈ R, ∀ a' ∈ R, g a = g a' → a = a' := by
      intro a ha a' ha' h
      have e1 := (hg a ha).2
      have e2 := (hg a' ha').2
      have h3 : (φ ⟨elt a, hRmemE a ha⟩ : MulAut Y) = φ ⟨elt a', hRmemE a' ha'⟩ := by
        rw [← e1, ← e2, h]
      have h4 := congrArg Subtype.val (φ.injective (Subtype.ext h3))
      exact hinj a a' (hRlt a ha).1 (hRlt a' ha').1 h4
    have hct : c = MulAut.conj t := by
      by_contra hne
      obtain ⟨k, hk, hkc⟩ := hcK
      have hkk : mul k k = 0 := (hsq0 k hk).2 (by rw [hkc]; exact hcc)
      have hk0 : k ≠ 0 := (hne0 k hk).2 (by rw [hkc]; exact hc1)
      have hktI : k ≠ tI := fun h => hne (by rw [← hkc, h, htI.2])
      have hlt := hspec.sqrt_lt k hk hkk hk0 hktI
      have hmap : ∀ a ∈ R, g a ∈ (List.range n).filter (fun a => mul a a == k) := by
        intro a ha
        obtain ⟨hlt', hel⟩ := hg a ha
        simp only [List.mem_filter, List.mem_range, beq_iff_eq]
        refine ⟨hlt', hinj _ _ (hmul _ _ hlt' hlt').1 hk ?_⟩
        rw [← (hmul _ _ hlt' hlt').2, hel, hkc, hφsq a ha]
      have hcard : R.toFinset.card ≤
          (((List.range n).filter (fun a => mul a a == k)).toFinset).card :=
        Finset.card_le_card_of_injOn g (fun a ha => by
          simpa using hmap a (by simpa using ha))
          (fun a ha a' ha' h => hginj a (by simpa using ha) a' (by simpa using ha') h)
      rw [List.toFinset_card_of_nodup hRnd] at hcard
      have h5 := List.toFinset_card_le ((List.range n).filter (fun a => mul a a == k))
      omega
    have hgsq : ∀ a (ha : a ∈ R), mul (g a) (g a) = tI := by
      intro a ha
      obtain ⟨hlt', hel⟩ := hg a ha
      refine hinj _ _ (hmul _ _ hlt' hlt').1 htI.1 ?_
      rw [← (hmul _ _ hlt' hlt').2, hel, hφsq a ha, hct, htI.2]
    have hφcomm : ∀ a ∈ R, ∀ a' ∈ R, mul (g a) (g a') = mul (g a') (g a) ∨
        mul (g a) (g a') = mul (mul (g a') (g a)) tI := by
      intro a ha a' ha'
      obtain ⟨hlt1, hel1⟩ := hg a ha
      obtain ⟨hlt2, hel2⟩ := hg a' ha'
      have hm12 := hmul (g a) (g a') hlt1 hlt2
      have hm21 := hmul (g a') (g a) hlt2 hlt1
      have hm3 := hmul (mul (g a') (g a)) tI hm21.1 htI.1
      rcases hspec.E_comm a (hspec.E_roots a ha) a' (hspec.E_roots a' ha') with h | h
      · left
        have h1 : (⟨elt a, hRmemE a ha⟩ : ↥E) * ⟨elt a', hRmemE a' ha'⟩ =
            ⟨elt a', hRmemE a' ha'⟩ * ⟨elt a, hRmemE a ha⟩ :=
          Subtype.ext ((hcommK a a' (hRlt a ha).1 (hRlt a' ha').1).1 h)
        have h2 := congrArg Subtype.val (congrArg φ h1)
        rw [map_mul, map_mul] at h2
        have h3 : elt (g a) * elt (g a') = elt (g a') * elt (g a) := by
          rw [hel1, hel2]; exact h2
        exact (hcommK (g a) (g a') hlt1 hlt2).2 h3
      · right
        have hE1 : elt a * elt a' = elt a' * elt a * MulAut.conj t := by
          have e1 := (hmul a a' (hRlt a ha).1 (hRlt a' ha').1).2
          have e2 := (hmul a' a (hRlt a' ha').1 (hRlt a ha).1).2
          have e3 := (hmul (mul a' a) tI (hmul a' a (hRlt a' ha').1 (hRlt a ha).1).1 htI.1).2
          rw [e1, h, ← htI.2, ← e3, ← e2]
        have h1 : (⟨elt a, hRmemE a ha⟩ : ↥E) * ⟨elt a', hRmemE a' ha'⟩ =
            ⟨elt a', hRmemE a' ha'⟩ * ⟨elt a, hRmemE a ha⟩ * ⟨MulAut.conj t, htEmem⟩ :=
          Subtype.ext hE1
        have h2 := congrArg Subtype.val (congrArg φ h1)
        rw [map_mul, map_mul, map_mul] at h2
        have h3 : elt (g a) * elt (g a') = elt (g a') * elt (g a) * elt tI := by
          rw [hel1, hel2, htI.2, ← hct]; exact h2
        apply hinj _ _ hm12.1 hm3.1
        rw [← hm12.2, ← hm3.2, ← hm21.2]
        exact h3
    have hgi : ∀ a ∈ R, inn (g a) = true := by
      intro a₀ ha₀
      by_contra hinn
      have hinn' : inn (g a₀) = false := by simpa using hinn
      have hnbr := hspec.outer_nbr (g a₀) (hg a₀ ha₀).1 hinn' (hgsq a₀ ha₀)
      have hmapN : ∀ a ∈ R.erase a₀, g a ∈ (rootsAll n mul tI).filter
          (fun b => b != g a₀ && isNbr mul tI (g a₀) b) := by
        intro a ha
        obtain ⟨hne, ha'⟩ := (List.Nodup.mem_erase_iff hRnd).1 ha
        simp only [List.mem_filter, rootsAll, List.mem_range, beq_iff_eq, Bool.and_eq_true,
          bne_iff_ne, ne_eq, isNbr, Bool.or_eq_true]
        refine ⟨⟨(hg a ha').1, hgsq a ha'⟩, fun h => hne (hginj a ha' a₀ ha₀ h), ?_⟩
        exact hφcomm a₀ ha₀ a ha'
      have hcardN : (R.erase a₀).toFinset.card ≤ (((rootsAll n mul tI).filter
          (fun b => b != g a₀ && isNbr mul tI (g a₀) b)).toFinset).card :=
        Finset.card_le_card_of_injOn g (fun a ha => by
          simpa using hmapN a (by simpa using ha))
          (fun a ha a' ha' h => hginj a (List.mem_of_mem_erase (by simpa using ha)) a'
            (List.mem_of_mem_erase (by simpa using ha')) h)
      rw [List.toFinset_card_of_nodup (hRnd.erase a₀), List.length_erase_of_mem ha₀] at hcardN
      have h5 := List.toFinset_card_le ((rootsAll n mul tI).filter
        (fun b => b != g a₀ && isNbr mul tI (g a₀) b))
      have h6 : nbrCount n mul tI (g a₀) = ((rootsAll n mul tI).filter
        (fun b => b != g a₀ && isNbr mul tI (g a₀) b)).length := rfl
      omega
    have hgR : ∀ a ∈ R, g a ∈ R := fun a ha =>
      mem_rootsIn.2 ⟨⟨(hg a ha).1, hgi a ha⟩, hgsq a ha⟩
    have hφR : ∀ a (h : a ∈ R), (φ ⟨elt a, hRmemE a h⟩ : MulAut Y) ∈ E := by
      intro a h
      rw [← (hg a h).2]
      exact hRmemE _ (hgR a h)
    have hPE : P ≤ E := by
      intro p hp
      obtain ⟨e, he⟩ := φ.surjective ⟨p, hp⟩
      have hpe : p = (φ e : MulAut Y) := (congrArg Subtype.val he).symm
      rw [hpe]
      obtain ⟨a, ha, hae⟩ := e.2
      have hea : e = ⟨elt a, ⟨a, ha, rfl⟩⟩ := Subtype.ext hae.symm
      rcases hspec.E_prod_roots a ha with h | h | ⟨x, hx, y, hy, hxy⟩
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
  · rintro _ ⟨a, ha, rfl⟩ hc
    have hall : ∀ e ∈ El, mul a e = mul e a := fun e he =>
      (hcommK a e ha (hElt e he).1).2 (hc (elt e) ⟨e, he, rfl⟩)
    rcases hspec.K_cent a ha hall with rfl | rfl
    · exact Or.inl h0
    · exact Or.inr htI.2

end Facts

theorem OuterEData.of_card {Y : Type*} [Group Y] [Finite (MulAut Y)] {K E : Subgroup (MulAut Y)}
    {t : Y} (hAut : ∃ k : ℕ, Odd k ∧ Nat.card (MulAut Y) = 256 * k) (hf : OuterEFacts Y K t E) :
    OuterEData Y := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKp : IsPGroup 2 K := IsPGroup.of_card (n := 8) (by rw [hf.card_S]; norm_num)
  obtain ⟨k, hk, hcard⟩ := hAut
  have hKidx : ¬ 2 ∣ K.index := by
    have h1 := K.index_mul_card
    rw [hf.card_S, hcard] at h1
    have : K.index = k := by omega
    rw [this]
    exact fun hd => (Nat.not_even_iff_odd.2 hk) (even_iff_two_dvd.2 hd)
  exact OuterEData.of_sylow hKp hKidx hf

end CFSG.EvenSporadicStandard.Fin76b
