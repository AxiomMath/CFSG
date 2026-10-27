module

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.C9Native
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.C9Lift
public import CFSG.LocalAnalysis.SectionRank.Ccomm.ElementaryAut

public section

namespace CFSG.EvenSmallLie.UnitarySix.ToddOrbit

open Subgroup CFSG.Sporadic.Schreier CFSG.Fischer
open scoped commutatorElement

variable {G : Type*} [Group G]

@[expose] def orb (E : Subgroup G) (t : G) : Set G :=
  {s | ∃ n ∈ normalizer (E : Set G), n⁻¹ * t * n = s}

section Orbit

variable {E : Subgroup G} {t : G}

theorem t_mem_orb : t ∈ orb E t := ⟨1, one_mem _, by simp⟩

theorem conj_mem_orb {n : G} (hn : n ∈ normalizer (E : Set G)) {s : G} (hs : s ∈ orb E t) :
    n⁻¹ * s * n ∈ orb E t := by
  obtain ⟨m, hm, rfl⟩ := hs
  exact ⟨m * n, mul_mem hm hn, by group⟩

theorem conj_mem_orb_iff {n : G} (hn : n ∈ normalizer (E : Set G)) {s : G} :
    n⁻¹ * s * n ∈ orb E t ↔ s ∈ orb E t := by
  refine ⟨fun h => ?_, conj_mem_orb hn⟩
  have := conj_mem_orb (inv_mem hn) h
  simpa [mul_assoc] using this

theorem conj_mem_orb_iff' {n : G} (hn : n ∈ normalizer (E : Set G)) {s : G} :
    n * s * n⁻¹ ∈ orb E t ↔ s ∈ orb E t := by
  have := conj_mem_orb_iff (E := E) (t := t) (inv_mem hn) (s := s)
  simpa using this

theorem orb_subset (htE : t ∈ E) : orb E t ⊆ E := by
  rintro _ ⟨n, hn, rfl⟩
  have h := (mem_normalizer_iff.1 (inv_mem hn) t).1 htE
  simpa using h

theorem one_notMem_orb (ht : t ≠ 1) : (1 : G) ∉ orb E t := by
  rintro ⟨n, -, h⟩
  apply ht
  have := congrArg (fun x => n * x * n⁻¹) h
  simpa [mul_assoc] using this

@[expose] noncomputable def dcount (E : Subgroup G) (t a : G) : ℕ :=
  {b | b ∈ orb E t ∧ b ≠ a ∧ a * b ∉ orb E t}.ncard

theorem dcount_conj {n : G} (hn : n ∈ normalizer (E : Set G)) (a : G) :
    dcount E t (n⁻¹ * a * n) = dcount E t a := by
  unfold dcount
  have himage : {b | b ∈ orb E t ∧ b ≠ n⁻¹ * a * n ∧ n⁻¹ * a * n * b ∉ orb E t} =
      (fun b => n⁻¹ * b * n) '' {b | b ∈ orb E t ∧ b ≠ a ∧ a * b ∉ orb E t} := by
    ext b
    simp only [Set.mem_ofPred_eq, Set.mem_image]
    constructor
    · rintro ⟨hb, hba, hab⟩
      refine ⟨n * b * n⁻¹, ⟨(conj_mem_orb_iff' hn).2 hb, fun h => hba ?_, fun h => hab ?_⟩, by
        group⟩
      · rw [← h]; group
      · have := conj_mem_orb hn h
        rwa [show n⁻¹ * (a * (n * b * n⁻¹)) * n = n⁻¹ * a * n * b by group] at this
    · rintro ⟨c, ⟨hc, hca, hac⟩, rfl⟩
      refine ⟨conj_mem_orb hn hc, fun h => hca ?_, fun h => hac ?_⟩
      · have := congrArg (fun x => n * x * n⁻¹) h
        simpa [mul_assoc] using this
      · rw [show n⁻¹ * a * n * (n⁻¹ * c * n) = n⁻¹ * (a * c) * n by group] at h
        exact (conj_mem_orb_iff hn).1 h
  rw [himage, Set.ncard_image_of_injective _ (fun x y h => by simpa using h)]

theorem dcount_eq {a : G} (ha : a ∈ orb E t) : dcount E t a = dcount E t t := by
  obtain ⟨n, hn, rfl⟩ := ha
  exact dcount_conj hn t

end Orbit

section Fibre

variable {t : G} {L E : Subgroup G} {p : L →* Equiv.Perm (Fin 693)}

@[expose] noncomputable def mcount (E : Subgroup G) (t : G) (p : L →* Equiv.Perm (Fin 693))
    (x : Equiv.Perm (Fin 693)) : ℕ :=
  {s | s ∈ orb E t ∧ pe p s = x}.ncard

namespace Hyp

theorem orb_subset_E
    (H : Hyp t L E p) : orb E t ⊆ E := orb_subset H.t_mem_E

theorem orb_subset_L
    (H : Hyp t L E p) {s : G} (hs : s ∈ orb E t) : s ∈ L :=
  H.E_le_L (H.orb_subset_E hs)

theorem fibre_subset
    (H : Hyp t L E p) {g : G} (hg : g ∈ L) :
    {s | s ∈ orb E t ∧ pe p s = pe p g} ⊆ {g, g * t} := by
  rintro s ⟨hs, hsg⟩
  rcases (H.pe_eq_pe_iff hg (H.orb_subset_L hs)).1 hsg with rfl | rfl
  · exact Set.mem_insert _ _
  · exact Set.mem_insert_of_mem _ rfl

theorem ne_mul_t
    (H : Hyp t L E p) (g : G) : g ≠ g * t := fun h =>
  H.t_ne_one (by simpa using h.symm)

theorem lift_mem_normalizer
    (H : Hyp t L E p) {c : Equiv.Perm (Fin 693)} (hc : c ∈ uK) {ℓ : G}
    (hℓ : ℓ ∈ L) (hpℓ : pe p ℓ = c) : ℓ ∈ normalizer (E : Set G) := by
  have key : ∀ {ℓ : G} {c : Equiv.Perm (Fin 693)}, c ∈ uK → ℓ ∈ L → pe p ℓ = c →
      ∀ g ∈ E, ℓ * g * ℓ⁻¹ ∈ E := by
    intro ℓ c hc hℓ hpℓ g hg
    obtain ⟨hgL, hgA⟩ := H.mem_E_iff.1 hg
    refine H.mem_E_iff.2 ⟨L.mul_mem (L.mul_mem hℓ hgL) (L.inv_mem hℓ), ?_⟩
    rw [pe_conj p hℓ hgL, hpℓ]
    exact uK_conj_mem hc hgA
  rw [mem_normalizer_iff]
  intro g
  refine ⟨key hc hℓ hpℓ g, fun h => ?_⟩
  have := key (uK.inv_mem hc) (L.inv_mem hℓ) (by rw [pe_inv p hℓ, hpℓ]) _ h
  simpa [mul_assoc] using this

variable [Finite G]

theorem mcount_le_two
    (H : Hyp t L E p) {g : G} (hg : g ∈ L) : mcount E t p (pe p g) ≤ 2 :=
  (Set.ncard_le_ncard (H.fibre_subset hg) (Set.toFinite _)).trans
    ((Set.ncard_insert_le _ _).trans (by rw [Set.ncard_singleton]))

theorem mem_orb_of_mcount_two
    (H : Hyp t L E p) {g : G} (hg : g ∈ L)
    (h : mcount E t p (pe p g) = 2) : g ∈ orb E t ∧ g * t ∈ orb E t := by
  have hpair : ({g, g * t} : Set G).ncard = 2 := Set.ncard_pair (H.ne_mul_t g)
  have heq := Set.eq_of_subset_of_ncard_le (H.fibre_subset hg) (by rw [hpair]; exact h.ge)
    (Set.toFinite _)
  have h1 : g ∈ {s | s ∈ orb E t ∧ pe p s = pe p g} := by rw [heq]; exact Set.mem_insert _ _
  have h2 : g * t ∈ {s | s ∈ orb E t ∧ pe p s = pe p g} := by
    rw [heq]; exact Set.mem_insert_of_mem _ rfl
  exact ⟨h1.1, h2.1⟩

theorem notMem_orb_of_mcount_zero {x : Equiv.Perm (Fin 693)}
    (h : mcount E t p x = 0) {s : G} (hs : pe p s = x) : s ∉ orb E t := by
  intro hso
  have hne : ({s | s ∈ orb E t ∧ pe p s = x} : Set G).Nonempty := ⟨s, hso, hs⟩
  exact (Set.ncard_pos (Set.toFinite _)).2 hne |>.ne' h

theorem one_le_mcount {s : G} (hs : s ∈ orb E t) : 1 ≤ mcount E t p (pe p s) :=
  (Set.ncard_pos (Set.toFinite _)).2 ⟨s, hs, rfl⟩

theorem mem_orb_iff_of_mcount_one
    (H : Hyp t L E p) {g : G} (hg : g ∈ L)
    (h : mcount E t p (pe p g) = 1) : g ∈ orb E t ↔ g * t ∉ orb E t := by
  constructor
  · intro hgo hgto
    have hsub : ({g, g * t} : Set G) ⊆ {s | s ∈ orb E t ∧ pe p s = pe p g} := by
      rintro s (rfl | rfl)
      · exact ⟨hgo, rfl⟩
      · exact ⟨hgto, by rw [pe_mul p hg H.t_mem, H.pe_t, mul_one]⟩
    have := Set.ncard_le_ncard hsub (Set.toFinite _)
    have h' : {s | s ∈ orb E t ∧ pe p s = pe p g}.ncard = 1 := h
    rw [Set.ncard_pair (H.ne_mul_t g), h'] at this
    exact absurd this (by norm_num)
  · intro hgt
    by_contra hgo
    have hempty : {s | s ∈ orb E t ∧ pe p s = pe p g} = ∅ := by
      ext s
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and]
      intro hs hsg
      rcases (H.pe_eq_pe_iff hg (H.orb_subset_L hs)).1 hsg with rfl | rfl
      · exact hgo hs
      · exact hgt hs
    have h0 : mcount E t p (pe p g) = 0 := by
      unfold mcount
      rw [hempty, Set.ncard_empty]
    omega

omit [Finite G] in
theorem mcount_one
    (H : Hyp t L E p) : mcount E t p 1 = 1 := by
  have h : {s | s ∈ orb E t ∧ pe p s = 1} = {t} := by
    ext s
    simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨hs, hs1⟩
      rcases (H.pe_eq_one_iff (H.orb_subset_L hs)).1 hs1 with rfl | rfl
      · exact absurd hs (one_notMem_orb H.t_ne_one)
      · rfl
    · rintro rfl
      exact ⟨t_mem_orb, H.pe_t⟩
  unfold mcount
  rw [h, Set.ncard_singleton]

omit [Finite G] in
theorem mcount_conj
    (H : Hyp t L E p) {c : Equiv.Perm (Fin 693)} (hc : c ∈ uK)
    (x : Equiv.Perm (Fin 693)) : mcount E t p (c * x * c⁻¹) = mcount E t p x := by
  obtain ⟨ℓ, hℓ, hpℓ⟩ := H.exists_lift (uK_le_T46 hc)
  have hℓN := H.lift_mem_normalizer hc hℓ hpℓ
  unfold mcount
  have himage : {s | s ∈ orb E t ∧ pe p s = c * x * c⁻¹} =
      (fun s => ℓ * s * ℓ⁻¹) '' {s | s ∈ orb E t ∧ pe p s = x} := by
    ext s
    simp only [Set.mem_ofPred_eq, Set.mem_image]
    constructor
    · rintro ⟨hs, hsx⟩
      have hsL := H.orb_subset_L hs
      refine ⟨ℓ⁻¹ * s * ℓ, ⟨conj_mem_orb hℓN hs, ?_⟩, by group⟩
      have e := pe_conj p (L.inv_mem hℓ) hsL
      rw [inv_inv, pe_inv p hℓ, hpℓ, hsx, inv_inv] at e
      rw [e]
      group
    · rintro ⟨u, ⟨hu, hux⟩, rfl⟩
      refine ⟨(conj_mem_orb_iff' hℓN).2 hu, ?_⟩
      rw [pe_conj p hℓ (H.orb_subset_L hu), hpℓ, hux]
  rw [himage, Set.ncard_image_of_injective _ (fun a b h => by simpa using h)]

omit [Finite G] in
theorem mcount_eq_of_mem_conjClass
    (H : Hyp t L E p) {j x : Equiv.Perm (Fin 693)}
    (hx : x ∈ conjClass uK j) : mcount E t p x = mcount E t p j := by
  obtain ⟨c, hc, rfl⟩ := hx
  exact H.mcount_conj hc j

end Hyp

end Fibre

section Count

theorem ncard_eq_sum_ncard_fibre {α β : Type*} [Finite α] [DecidableEq β] (S : Set α)
    (f : α → β) (T : Finset β) (hST : ∀ s ∈ S, f s ∈ T) :
    S.ncard = ∑ b ∈ T, {s | s ∈ S ∧ f s = b}.ncard := by
  classical
  have := Fintype.ofFinite α
  rw [Set.ncard_eq_toFinset_card' S,
    Finset.card_eq_sum_card_fiberwise (f := f) (t := T) (fun s hs => hST s (by simpa using hs))]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Set.ncard_eq_toFinset_card']
  congr 1
  ext s
  simp

@[expose] noncomputable def cls
    (j : Equiv.Perm (Fin 693)) : Finset (Equiv.Perm (Fin 693)) :=
  (conjClass_finite uK j).toFinset

theorem mem_cls
    {j x : Equiv.Perm (Fin 693)} : x ∈ cls j ↔ x ∈ conjClass uK j := by
  simp [cls]

theorem card_cls
    : (cls j1).card = 21 ∧ (cls j2).card = 210 ∧ (cls j3).card = 280 := by
  obtain ⟨-, h1, h2, h3⟩ := korbits
  refine ⟨?_, ?_, ?_⟩
  · rw [cls, ← Set.ncard_eq_toFinset_card]
    exact h1
  · rw [cls, ← Set.ncard_eq_toFinset_card]
    exact h2
  · rw [cls, ← Set.ncard_eq_toFinset_card]
    exact h3

@[expose] noncomputable def uAf : Finset (Equiv.Perm (Fin 693)) :=
  (Set.toFinite (uA : Set (Equiv.Perm (Fin 693)))).toFinset

theorem mem_uAf {x : Equiv.Perm (Fin 693)} : x ∈ uAf ↔ x ∈ uA := by
  simp [uAf]

theorem notMem_cls_one
    {j : Equiv.Perm (Fin 693)} (hj : j = j1 ∨ j = j2 ∨ j = j3) :
    (1 : Equiv.Perm (Fin 693)) ∉ cls j := by
  rw [mem_cls]
  intro h
  rcases hj with rfl | rfl | rfl
  · exact (conjClass_facts j1_mem j1_ne_one 1 h).1.2 rfl
  · exact (conjClass_facts j2_mem j2_ne_one 1 h).1.2 rfl
  · exact (conjClass_facts j3_mem j3_ne_one 1 h).1.2 rfl

theorem cls_subset
    {j : Equiv.Perm (Fin 693)} (hj : j = j1 ∨ j = j2 ∨ j = j3) :
    ∀ x ∈ cls j, x ∈ uA := by
  intro x hx
  rw [mem_cls] at hx
  rcases hj with rfl | rfl | rfl
  · exact (conjClass_facts j1_mem j1_ne_one x hx).1.1
  · exact (conjClass_facts j2_mem j2_ne_one x hx).1.1
  · exact (conjClass_facts j3_mem j3_ne_one x hx).1.1

theorem disjoint_cls_12
    : Disjoint (cls j1) (cls j2) := by
  rw [Finset.disjoint_left]
  intro x h1 h2
  rw [mem_cls] at h1 h2
  have := (ncard_fixed_of_mem_conjClass.1 h1).symm.trans (ncard_fixed_of_mem_conjClass.2.1 h2)
  exact absurd this (by norm_num)

theorem disjoint_cls_13
    : Disjoint (cls j1) (cls j3) := by
  rw [Finset.disjoint_left]
  intro x h1 h3
  rw [mem_cls] at h1 h3
  have := (ncard_fixed_of_mem_conjClass.1 h1).symm.trans (ncard_fixed_of_mem_conjClass.2.2 h3)
  exact absurd this (by norm_num)

theorem disjoint_cls_23
    : Disjoint (cls j2) (cls j3) := by
  rw [Finset.disjoint_left]
  intro x h2 h3
  rw [mem_cls] at h2 h3
  have := (ncard_fixed_of_mem_conjClass.2.1 h2).symm.trans (ncard_fixed_of_mem_conjClass.2.2 h3)
  exact absurd this (by norm_num)

theorem uAf_eq
    : uAf = insert 1 (cls j1 ∪ cls j2 ∪ cls j3) := by
  ext x
  rw [mem_uAf, Finset.mem_insert, Finset.mem_union, Finset.mem_union, mem_cls, mem_cls, mem_cls]
  constructor
  · intro hx
    by_cases hx1 : x = 1
    · exact Or.inl hx1
    · rcases korbits.1 x hx hx1 with h | h | h
      · exact Or.inr (Or.inl (Or.inl h))
      · exact Or.inr (Or.inl (Or.inr h))
      · exact Or.inr (Or.inr h)
  · rintro (rfl | (h | h) | h)
    · exact uA.one_mem
    · exact cls_subset (Or.inl rfl) x (mem_cls.2 h)
    · exact cls_subset (Or.inr (Or.inl rfl)) x (mem_cls.2 h)
    · exact cls_subset (Or.inr (Or.inr rfl)) x (mem_cls.2 h)

theorem mem_cls_of_mem_uA
    {x : Equiv.Perm (Fin 693)} (hx : x ∈ uA) (hx1 : x ≠ 1) :
    x ∈ cls j1 ∨ x ∈ cls j2 ∨ x ∈ cls j3 := by
  rw [mem_cls, mem_cls, mem_cls]
  exact korbits.1 x hx hx1

theorem sum_cls_const
    {j : Equiv.Perm (Fin 693)} {f : Equiv.Perm (Fin 693) → ℕ}
    (hf : ∀ x ∈ conjClass uK j, f x = f j) : ∑ x ∈ cls j, f x = (cls j).card * f j := by
  rw [Finset.sum_congr rfl fun x hx => hf x (mem_cls.1 hx), Finset.sum_const, smul_eq_mul]

theorem j2_mem_cls
    : j2 ∈ cls j2 := mem_cls.2 ⟨1, uK.one_mem, by simp⟩

end Count

section Main

theorem cases_of_dvd {m₁ m₂ m₃ : ℕ} (h₁ : m₁ ≤ 2) (h₂ : m₂ ≤ 2) (h₃ : m₃ ≤ 2)
    (h : 1 + 21 * m₁ + 210 * m₂ + 280 * m₃ ∣ 366440137299948128422802227200) :
    (m₁ = 0 ∧ m₂ = 0 ∧ m₃ = 0) ∨ (m₁ = 1 ∧ m₂ = 0 ∧ m₃ = 0) ∨ (m₁ = 1 ∧ m₂ = 1 ∧ m₃ = 1) ∨
      (m₁ = 0 ∧ m₂ = 0 ∧ m₃ = 2) ∨ (m₁ = 1 ∧ m₂ = 1 ∧ m₃ = 2) ∨
      (m₁ = 2 ∧ m₂ = 2 ∧ m₃ = 2) := by
  interval_cases m₁ <;> interval_cases m₂ <;> interval_cases m₃ <;> revert h <;> decide

variable {t : G} {L E : Subgroup G} {p : L →* Equiv.Perm (Fin 693)} [Finite G]

namespace Hyp

theorem ncard_orb_filter (T : Finset (Equiv.Perm (Fin 693))) :
    {s | s ∈ orb E t ∧ pe p s ∈ T}.ncard = ∑ x ∈ T, mcount E t p x := by
  classical
  rw [ncard_eq_sum_ncard_fibre _ (pe p) T (fun s hs => hs.2)]
  refine Finset.sum_congr rfl fun x hx => ?_
  unfold mcount
  congr 1
  ext s
  simp only [Set.mem_ofPred_eq]
  constructor
  · rintro ⟨⟨hs, -⟩, hsx⟩
    exact ⟨hs, hsx⟩
  · rintro ⟨hs, rfl⟩
    exact ⟨⟨hs, hx⟩, rfl⟩

omit [Finite G] in
theorem ncard_fibre_L
    (H : Hyp t L E p) {x : Equiv.Perm (Fin 693)} (hx : x ∈ T46) :
    {g | g ∈ L ∧ pe p g = x}.ncard = 2 := by
  obtain ⟨g, hg, rfl⟩ := H.exists_lift hx
  have h : {s | s ∈ L ∧ pe p s = pe p g} = {g, g * t} := by
    ext s
    simp only [Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨hs, hsg⟩
      exact (H.pe_eq_pe_iff hg hs).1 hsg
    · rintro (rfl | rfl)
      · exact ⟨hg, rfl⟩
      · exact ⟨L.mul_mem hg H.t_mem, by rw [pe_mul p hg H.t_mem, H.pe_t, mul_one]⟩
  rw [h, Set.ncard_pair (H.ne_mul_t g)]

theorem ncard_L_filter
    (H : Hyp t L E p) (T : Finset (Equiv.Perm (Fin 693)))
    (hT : ∀ x ∈ T, x ∈ T46) : {g | g ∈ L ∧ pe p g ∈ T}.ncard = 2 * T.card := by
  classical
  rw [ncard_eq_sum_ncard_fibre _ (pe p) T (fun s hs => hs.2)]
  rw [Finset.sum_congr rfl fun x hx => ?_, Finset.sum_const, smul_eq_mul, mul_comm]
  rw [← H.ncard_fibre_L (hT x hx)]
  congr 1
  ext g
  simp only [Set.mem_ofPred_eq]
  constructor
  · rintro ⟨⟨hg, -⟩, hgx⟩
    exact ⟨hg, hgx⟩
  · rintro ⟨hg, rfl⟩
    exact ⟨⟨hg, hx⟩, rfl⟩

theorem ncard_orb_eq
    (H : Hyp t L E p) :
    (orb E t).ncard = 1 + 21 * mcount E t p j1 + 210 * mcount E t p j2 +
      280 * mcount E t p j3 := by
  classical
  have hmaps : ∀ s ∈ orb E t, pe p s ∈ uAf := fun s hs =>
    mem_uAf.2 (H.mem_E_iff.1 (H.orb_subset_E hs)).2
  rw [ncard_eq_sum_ncard_fibre _ (pe p) uAf hmaps, uAf_eq,
    Finset.sum_insert (by
      simp only [Finset.mem_union, not_or]
      exact ⟨⟨notMem_cls_one (Or.inl rfl), notMem_cls_one (Or.inr (Or.inl rfl))⟩,
        notMem_cls_one (Or.inr (Or.inr rfl))⟩),
    Finset.sum_union (Finset.disjoint_union_left.2 ⟨disjoint_cls_13, disjoint_cls_23⟩),
    Finset.sum_union disjoint_cls_12]
  have hc : ∀ j : Equiv.Perm (Fin 693), ∑ x ∈ cls j, {s | s ∈ orb E t ∧ pe p s = x}.ncard =
      (cls j).card * mcount E t p j :=
    fun j => sum_cls_const (f := mcount E t p) fun x hx => H.mcount_eq_of_mem_conjClass hx
  obtain ⟨c1, c2, c3⟩ := card_cls
  have h1 := H.mcount_one
  unfold mcount at h1
  rw [h1, hc, hc, hc, c1, c2, c3]
  ring

theorem card_E
    (H : Hyp t L E p) : Nat.card E = 2 ^ 10 := by
  classical
  have hset : (E : Set G) = {g | g ∈ L ∧ pe p g ∈ uAf} := by
    ext g
    simp only [SetLike.mem_coe, Set.mem_ofPred_eq, mem_uAf]
    exact H.mem_E_iff
  have huAf : uAf.card = 512 := by
    rw [uAf, ← Set.ncard_eq_toFinset_card, ← Nat.card_coe_set_eq, SetLike.coe_sort_coe, card_uA]
  rw [← SetLike.coe_sort_coe, Nat.card_coe_set_eq, hset,
    H.ncard_L_filter uAf fun x hx => uA_le_T46 (mem_uAf.1 hx), huAf]
  norm_num

theorem card_mulAut_E
    (H : Hyp t L E p) :
    Nat.card (MulAut E) = 366440137299948128422802227200 := by
  have hc : ∀ a b : E, a * b = b * a := fun a b => Subtype.ext (H.E_comm a.2 b.2)
  have hp : ∀ a : E, a ^ 2 = 1 := fun a => Subtype.ext (by simpa using H.E_sq a a.2)
  obtain ⟨e⟩ := CFSG.SectionRank.Ccomm.nonempty_mulEquiv_of_elementary (p := 2) hc hp H.card_E
  rw [CFSG.SectionRank.Ccomm.card_mulAut_eq_card_GL e, CFSG.SectionRank.Ccomm.card_GL_zmod]
  simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, Fin.val_zero, Fin.val_succ]
  norm_num

theorem ncard_orb_dvd
    (H : Hyp t L E p) :
    (orb E t).ncard ∣ 366440137299948128422802227200 := by
  set φ := E.normalizerMonoidHom
  set R := φ.range
  let t' : E := ⟨t, H.t_mem_E⟩
  have hφ : ∀ m : normalizer (E : Set G), ((φ m t' : E) : G) = (m : G) * t * (m : G)⁻¹ :=
    fun m => Subgroup.normalizerMonoidHom_apply_apply_coe E m t'
  have horb : orb E t = Subtype.val '' MulAction.orbit R t' := by
    ext s
    constructor
    · rintro ⟨n, hn, rfl⟩
      refine ⟨(⟨φ ⟨n⁻¹, inv_mem hn⟩, ⟨n⁻¹, inv_mem hn⟩, rfl⟩ : R) • t', ⟨_, rfl⟩, ?_⟩
      change ((φ ⟨n⁻¹, inv_mem hn⟩ t' : E) : G) = n⁻¹ * t * n
      rw [hφ]
      simp
    · rintro ⟨y, ⟨r, rfl⟩, rfl⟩
      obtain ⟨_, ⟨m, rfl⟩⟩ := r
      refine ⟨(m : G)⁻¹, inv_mem m.2, ?_⟩
      change (m : G)⁻¹⁻¹ * t * (m : G)⁻¹ = ((φ m t' : E) : G)
      rw [hφ, inv_inv]
  rw [horb, Set.ncard_image_of_injective _ Subtype.val_injective, ← MulAction.index_stabilizer,
    ← H.card_mulAut_E]
  exact (Subgroup.index_dvd_card _).trans (Subgroup.card_subgroup_dvd_card R)

omit [Finite G] in
theorem mem_cls_of_mem_orb
    (H : Hyp t L E p) {b : G} (hb : b ∈ orb E t) (hbt : b ≠ t) :
    pe p b ∈ cls j1 ∨ pe p b ∈ cls j2 ∨ pe p b ∈ cls j3 := by
  obtain ⟨hbL, hbA⟩ := H.mem_E_iff.1 (H.orb_subset_E hb)
  refine mem_cls_of_mem_uA hbA fun h1 => ?_
  rcases (H.pe_eq_one_iff hbL).1 h1 with rfl | rfl
  · exact one_notMem_orb H.t_ne_one hb
  · exact hbt rfl

omit [Finite G] in
theorem mcount_of_mem_cls
    (H : Hyp t L E p) {j x : Equiv.Perm (Fin 693)} (hx : x ∈ cls j) :
    mcount E t p x = mcount E t p j :=
  H.mcount_eq_of_mem_conjClass (mem_cls.1 hx)

theorem mcount_j1_ne_two
    (H : Hyp t L E p) : mcount E t p j1 ≠ 2 := by
  intro h2
  obtain ⟨z, hzE, hpz, u, -, v, -, hu3, hv3, huz, hvz, hz⟩ := H.exists_sq_lift
  rw [← hpz] at h2
  obtain ⟨n, -, hn⟩ := (H.mem_orb_of_mcount_two (H.E_le_L hzE) h2).1
  exact H.not_conj_of_sq hu3 hv3 huz hvz hz n hn

theorem not_case_000
    (H : Hyp t L E p) (h1 : mcount E t p j1 = 0) (h2 : mcount E t p j2 = 0)
    (h3 : mcount E t p j3 = 0) : False := by
  have hcard : (orb E t).ncard = 1 := by rw [H.ncard_orb_eq, h1, h2, h3]
  obtain ⟨n, hn, hnt⟩ := H.move
  have heq : ({t} : Set G) = orb E t := Set.eq_of_subset_of_ncard_le
    (Set.singleton_subset_iff.2 t_mem_orb) (by rw [hcard, Set.ncard_singleton]) (Set.toFinite _)
  have hmem : n⁻¹ * t * n ∈ orb E t := ⟨n, hn, rfl⟩
  rw [← heq] at hmem
  exact hnt hmem

theorem mem_cls12_of_notMem
    (H : Hyp t L E p) (h3 : mcount E t p j3 = 2) {a b : G}
    (haL : a ∈ L) (hpa : pe p a = j3) (hb : b ∈ orb E t) (hab : a * b ∉ orb E t)
    (hab1 : a * b ≠ 1) : j3 * pe p b ∈ cls j1 ∨ j3 * pe p b ∈ cls j2 := by
  have hbL := H.orb_subset_L hb
  have hcL : a * b ∈ L := L.mul_mem haL hbL
  have hpc : pe p (a * b) = j3 * pe p b := by rw [pe_mul p haL hbL, hpa]
  have hcA : j3 * pe p b ∈ uA :=
    uA.mul_mem j3_mem (H.mem_E_iff.1 (H.orb_subset_E hb)).2
  have hc1 : j3 * pe p b ≠ 1 := by
    intro h
    rw [← hpc] at h
    rcases (H.pe_eq_one_iff hcL).1 h with h' | h'
    · exact hab1 h'
    · exact hab (h' ▸ t_mem_orb)
  rcases mem_cls_of_mem_uA hcA hc1 with h | h | h
  · exact Or.inl h
  · exact Or.inr h
  · exfalso
    have hm : mcount E t p (pe p (a * b)) = 2 := by rw [hpc, H.mcount_of_mem_cls h, h3]
    exact hab (H.mem_orb_of_mcount_two hcL hm).1

theorem not_case_002
    (H : Hyp t L E p) (h1 : mcount E t p j1 = 0) (h2 : mcount E t p j2 = 0)
    (h3 : mcount E t p j3 = 2) : False := by
  have hdt : dcount E t t = 0 := by
    unfold dcount
    rw [Set.ncard_eq_zero (Set.toFinite _)]
    ext b
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and, not_not]
    intro hb hbt
    have hbL := H.orb_subset_L hb
    have hpos := one_le_mcount (p := p) hb
    rcases H.mem_cls_of_mem_orb hb hbt with hc | hc | hc
    · rw [H.mcount_of_mem_cls hc, h1] at hpos
      omega
    · rw [H.mcount_of_mem_cls hc, h2] at hpos
      omega
    · have hm : mcount E t p (pe p b) = 2 := by rw [H.mcount_of_mem_cls hc, h3]
      have := (H.mem_orb_of_mcount_two hbL hm).2
      rwa [H.comm_t hbL] at this
  obtain ⟨x, hxL, hpx⟩ := H.exists_lift (uA_le_T46 j3_mem)
  have hx := (H.mem_orb_of_mcount_two hxL (by rw [hpx, h3])).1
  obtain ⟨y, hyL, hpy⟩ := H.exists_lift (uA_le_T46 (uA.mul_mem j3_mem c3_mem))
  have hy := (H.mem_orb_of_mcount_two hyL (by
    rw [hpy, H.mcount_eq_of_mem_conjClass j3_mul_c3_mem_conjClass, h3])).1
  have hyx : y ≠ x := by
    rintro rfl
    rw [hpx] at hpy
    have hc : c3 = 1 := by
      have := congrArg (fun z => j3⁻¹ * z) hpy
      simpa using this.symm
    exact (conjClass_facts j1_mem j1_ne_one c3 c3_mem_conjClass).1.2 hc
  have hxy : x * y ∉ orb E t := by
    have hp : pe p (x * y) = c3 := by
      rw [pe_mul p hxL hyL, hpx, hpy, ← mul_assoc, ← sq, uA_sq _ j3_mem, one_mul]
    exact notMem_orb_of_mcount_zero (by rw [H.mcount_eq_of_mem_conjClass c3_mem_conjClass, h1]) hp
  have hdx : 0 < dcount E t x := (Set.ncard_pos (Set.toFinite _)).2 ⟨y, hy, hyx, hxy⟩
  rw [dcount_eq hx, hdt] at hdx
  exact absurd hdx (lt_irrefl 0)

theorem not_case_112
    (H : Hyp t L E p) (h1 : mcount E t p j1 = 1) (h2 : mcount E t p j2 = 1)
    (h3 : mcount E t p j3 = 2) : False := by
  classical
  set C12 : Finset (Equiv.Perm (Fin 693)) := cls j1 ∪ cls j2 with hC12
  have hm12 : ∀ x ∈ C12, mcount E t p x = 1 := by
    intro x hx
    rcases Finset.mem_union.1 hx with hx | hx
    · rw [H.mcount_of_mem_cls hx, h1]
    · rw [H.mcount_of_mem_cls hx, h2]
  have hC12card : C12.card = 231 := by
    rw [hC12, Finset.card_union_of_disjoint disjoint_cls_12, card_cls.1, card_cls.2.1]
  have hdt : dcount E t t = 231 := by
    have hset : {b | b ∈ orb E t ∧ b ≠ t ∧ t * b ∉ orb E t} =
        {b | b ∈ orb E t ∧ pe p b ∈ C12} := by
      ext b
      simp only [Set.mem_ofPred_eq, hC12, Finset.mem_union]
      constructor
      · rintro ⟨hb, hbt, htb⟩
        refine ⟨hb, ?_⟩
        rcases H.mem_cls_of_mem_orb hb hbt with hc | hc | hc
        · exact Or.inl hc
        · exact Or.inr hc
        · exfalso
          have hm : mcount E t p (pe p b) = 2 := by rw [H.mcount_of_mem_cls hc, h3]
          have := (H.mem_orb_of_mcount_two (H.orb_subset_L hb) hm).2
          rw [H.comm_t (H.orb_subset_L hb)] at this
          exact htb this
      · rintro ⟨hb, hc⟩
        have hbL := H.orb_subset_L hb
        have hm : mcount E t p (pe p b) = 1 := hm12 _ (by rw [hC12]; exact Finset.mem_union.2 hc)
        refine ⟨hb, ?_, ?_⟩
        · rintro rfl
          rw [H.pe_t] at hc
          rcases hc with hc | hc
          · exact notMem_cls_one (Or.inl rfl) hc
          · exact notMem_cls_one (Or.inr (Or.inl rfl)) hc
        · rw [← H.comm_t hbL]
          exact (H.mem_orb_iff_of_mcount_one hbL hm).1 hb
    unfold dcount
    rw [hset, ncard_orb_filter, Finset.sum_congr rfl hm12, Finset.sum_const, smul_eq_mul,
      hC12card]
  obtain ⟨x, hxL, hpx⟩ := H.exists_lift (uA_le_T46 j3_mem)
  obtain ⟨hx, hxt⟩ := H.mem_orb_of_mcount_two hxL (by rw [hpx, h3])
  have hxE := H.orb_subset_E hx
  have hxtL : x * t ∈ L := L.mul_mem hxL H.t_mem
  have hpxt : pe p (x * t) = j3 := by rw [pe_mul p hxL H.t_mem, H.pe_t, mul_one, hpx]
  set B := {b | b ∈ orb E t ∧ j3 * pe p b ∈ C12} with hB
  set Sx := {b | b ∈ orb E t ∧ b ≠ x ∧ x * b ∉ orb E t} with hSx
  set Sxt := {b | b ∈ orb E t ∧ b ≠ x * t ∧ x * t * b ∉ orb E t} with hSxt
  have hsub : ∀ {a : G}, a ∈ E → a ∈ L → pe p a = j3 →
      {b | b ∈ orb E t ∧ b ≠ a ∧ a * b ∉ orb E t} ⊆ B := by
    intro a haE haL hpa b ⟨hb, hba, hab⟩
    refine ⟨hb, ?_⟩
    have hab1 : a * b ≠ 1 := by
      intro h
      apply hba
      rw [← H.inv_eq_self haE]
      exact eq_inv_of_mul_eq_one_right h
    rcases H.mem_cls12_of_notMem h3 haL hpa hb hab hab1 with h | h
    · exact Finset.mem_union.2 (Or.inl h)
    · exact Finset.mem_union.2 (Or.inr h)
  have hSxB : Sx ⊆ B := hsub hxE hxL hpx
  have hSxtB : Sxt ⊆ B := hsub (H.mul_t_mem_E hxE) hxtL hpxt
  have hdisj : Disjoint Sx Sxt := by
    rw [Set.disjoint_left]
    rintro b ⟨hb, hbx, hxb⟩ ⟨-, -, hxtb⟩
    have hbL := H.orb_subset_L hb
    have hxbL : x * b ∈ L := L.mul_mem hxL hbL
    have hm : mcount E t p (pe p (x * b)) = 1 := by
      rw [pe_mul p hxL hbL, hpx]
      exact hm12 _ (hSxB ⟨hb, hbx, hxb⟩).2
    have := (H.mem_orb_iff_of_mcount_one hxbL hm).2
    by_contra hcon
    have h' : x * b * t ∈ orb E t := by
      by_contra h''
      exact hxb (this h'')
    rw [mul_assoc, H.comm_t hbL, ← mul_assoc] at h'
    exact hxtb h'
  obtain ⟨g1, hg1L, hpg1⟩ := H.exists_lift (uA_le_T46 j1_mem)
  obtain ⟨w, hwL, hpw, hw⟩ : ∃ w ∈ L, pe p w = j1 ∧ w ∉ orb E t := by
    by_cases hg1 : g1 ∈ orb E t
    · refine ⟨g1 * t, L.mul_mem hg1L H.t_mem, by rw [pe_mul p hg1L H.t_mem, H.pe_t, mul_one,
        hpg1], ?_⟩
      exact (H.mem_orb_iff_of_mcount_one hg1L (by rw [hpg1, h1])).1 hg1
    · exact ⟨g1, hg1L, hpg1, hg1⟩
  set T12 := {g | g ∈ L ∧ pe p g ∈ C12} with hT12
  have hT12card : T12.ncard = 462 := by
    rw [hT12, H.ncard_L_filter C12 fun x hx => ?_, hC12card]
    rcases Finset.mem_union.1 hx with hx | hx
    · exact uA_le_T46 (cls_subset (Or.inl rfl) x hx)
    · exact uA_le_T46 (cls_subset (Or.inr (Or.inl rfl)) x hx)
  have hxw : x * w ∈ T12 := by
    refine ⟨L.mul_mem hxL hwL, ?_⟩
    rw [pe_mul p hxL hwL, hpx, hpw, j3_mul_j1]
    exact Finset.mem_union.2 (Or.inr j2_mem_cls)
  have himg : (fun b => x * b) '' B ⊆ T12 \ {x * w} := by
    rintro _ ⟨b, ⟨hb, hbc⟩, rfl⟩
    refine ⟨⟨L.mul_mem hxL (H.orb_subset_L hb), ?_⟩, fun h => hw ?_⟩
    · rw [pe_mul p hxL (H.orb_subset_L hb), hpx]
      exact hbc
    · rw [Set.mem_singleton_iff, mul_right_inj] at h
      exact h ▸ hb
  have hBcard : B.ncard ≤ 461 := by
    have h := Set.ncard_le_ncard himg (Set.toFinite _)
    rw [Set.ncard_image_of_injective _ (mul_right_injective x),
      Set.ncard_sdiff_singleton_of_mem hxw, hT12card] at h
    exact h
  have hsum : dcount E t x + dcount E t (x * t) ≤ 461 := by
    unfold dcount
    rw [← hSx, ← hSxt, ← Set.ncard_union_eq hdisj (Set.toFinite _) (Set.toFinite _)]
    exact (Set.ncard_le_ncard (Set.union_subset hSxB hSxtB) (Set.toFinite _)).trans hBcard
  rw [dcount_eq hx, dcount_eq hxt, hdt] at hsum
  omega

theorem not_case_111
    (H : Hyp t L E p) (h1 : mcount E t p j1 = 1) (h2 : mcount E t p j2 = 1)
    (h3 : mcount E t p j3 = 1) : False := by
  have hcard : (orb E t).ncard = 512 := by rw [H.ncard_orb_eq, h1, h2, h3]
  have hm1 : ∀ b ∈ orb E t, b ≠ t → mcount E t p (pe p b) = 1 := by
    intro b hb hbt
    rcases H.mem_cls_of_mem_orb hb hbt with hc | hc | hc
    · rw [H.mcount_of_mem_cls hc, h1]
    · rw [H.mcount_of_mem_cls hc, h2]
    · rw [H.mcount_of_mem_cls hc, h3]
  have hdt : dcount E t t = 511 := by
    have hset : {b | b ∈ orb E t ∧ b ≠ t ∧ t * b ∉ orb E t} = orb E t \ {t} := by
      ext b
      simp only [Set.mem_ofPred_eq, Set.mem_sdiff, Set.mem_singleton_iff]
      constructor
      · rintro ⟨hb, hbt, -⟩
        exact ⟨hb, hbt⟩
      · rintro ⟨hb, hbt⟩
        refine ⟨hb, hbt, ?_⟩
        rw [← H.comm_t (H.orb_subset_L hb)]
        exact (H.mem_orb_iff_of_mcount_one (H.orb_subset_L hb) (hm1 b hb hbt)).1 hb
    unfold dcount
    rw [hset, Set.ncard_sdiff_singleton_of_mem t_mem_orb, hcard]
  have hfree : ∀ a ∈ orb E t, ∀ b ∈ orb E t, b ≠ a → a * b ∉ orb E t := by
    intro a ha b hb hba
    have hda : dcount E t a = 511 := (dcount_eq ha).trans hdt
    have hsub : {b | b ∈ orb E t ∧ b ≠ a ∧ a * b ∉ orb E t} ⊆ orb E t \ {a} :=
      fun b hb => ⟨hb.1, hb.2.1⟩
    have heq := Set.eq_of_subset_of_ncard_le hsub (by
      rw [Set.ncard_sdiff_singleton_of_mem ha, hcard]
      unfold dcount at hda
      omega) (Set.toFinite _)
    have hmem : b ∈ orb E t \ {a} := ⟨hb, hba⟩
    rw [← heq] at hmem
    exact hmem.2.2
  have hEcard : (E : Set G).ncard = 1024 := by
    rw [← Nat.card_coe_set_eq, SetLike.coe_sort_coe, H.card_E]
    norm_num
  have hcomp : ∀ g ∈ E, g ∉ orb E t → t * g ∈ orb E t := by
    have himg : (fun b => t * b) '' orb E t ⊆ (E : Set G) \ orb E t := by
      rintro _ ⟨b, hb, rfl⟩
      refine ⟨E.mul_mem H.t_mem_E (H.orb_subset_E hb), fun h => ?_⟩
      change t * b ∈ orb E t at h
      by_cases hbt : b = t
      · rw [hbt, H.t_mul_t] at h
        exact one_notMem_orb H.t_ne_one h
      · exact hfree t t_mem_orb b hb hbt h
    have heq := Set.eq_of_subset_of_ncard_le himg (by
      rw [Set.ncard_sdiff (H.orb_subset_E) (Set.toFinite _), hEcard, hcard,
        Set.ncard_image_of_injective _ (mul_right_injective t), hcard]) (Set.toFinite _)
    intro g hg hgo
    have hmem : g ∈ (E : Set G) \ orb E t := ⟨hg, hgo⟩
    rw [← heq] at hmem
    obtain ⟨b, hb, rfl⟩ := hmem
    rwa [← mul_assoc, H.t_mul_t, one_mul]
  let W : Subgroup G :=
    { carrier := {g | g ∈ E ∧ g ∉ orb E t}
      mul_mem' := by
        rintro g h ⟨hg, hgo⟩ ⟨hh, hho⟩
        refine ⟨E.mul_mem hg hh, ?_⟩
        have hgh : g * h = (t * g) * (t * h) := by
          have hgt : g * t = t * g := H.comm_t (H.E_le_L hg)
          calc g * h = (t * t) * (g * h) := by rw [H.t_mul_t, one_mul]
            _ = t * (t * g) * h := by group
            _ = t * (g * t) * h := by rw [hgt]
            _ = (t * g) * (t * h) := by group
        rw [hgh]
        by_cases he : t * h = t * g
        · rw [he, ← sq, H.E_sq _ (E.mul_mem H.t_mem_E hg)]
          exact one_notMem_orb H.t_ne_one
        · exact hfree _ (hcomp g hg hgo) _ (hcomp h hh hho) he
      one_mem' := ⟨E.one_mem, one_notMem_orb H.t_ne_one⟩
      inv_mem' := by
        rintro g ⟨hg, hgo⟩
        exact ⟨E.inv_mem hg, by rwa [H.inv_eq_self hg]⟩ }
  have hle : ⁅E, normalizer (E : Set G) ⊓ L⁆ ≤ W := by
    rw [commutator_le]
    intro e he h hh
    have hf : h * e * h⁻¹ ∈ E := (mem_normalizer_iff.1 hh.1 e).1 he
    have hcomm : ⁅e, h⁆ = e * (h * e * h⁻¹) := by
      rw [commutatorElement_def, H.inv_eq_self he]
      group
    rw [hcomm]
    by_cases heo : e ∈ orb E t
    · have hfo : h * e * h⁻¹ ∈ orb E t := (conj_mem_orb_iff' hh.1).2 heo
      by_cases hfe : h * e * h⁻¹ = e
      · rw [hfe, ← sq, H.E_sq _ he]
        exact W.one_mem
      · exact ⟨E.mul_mem he hf, hfree e heo _ hfo hfe⟩
    · have hfo : h * e * h⁻¹ ∉ orb E t := fun h' => heo ((conj_mem_orb_iff' hh.1).1 h')
      exact W.mul_mem ⟨he, heo⟩ ⟨hf, hfo⟩
  exact (hle (H.nonsplit H.t_mem_E)).2 t_mem_orb

theorem mcount_values
    (H : Hyp t L E p) :
    mcount E t p j1 = 1 ∧ mcount E t p j2 = 0 ∧ mcount E t p j3 = 0 := by
  have hb : ∀ {j : Equiv.Perm (Fin 693)}, j ∈ uA → mcount E t p j ≤ 2 := by
    intro j hj
    obtain ⟨g, hg, hpg⟩ := H.exists_lift (uA_le_T46 hj)
    rw [← hpg]
    exact H.mcount_le_two hg
  have hdvd := H.ncard_orb_dvd
  rw [H.ncard_orb_eq] at hdvd
  rcases cases_of_dvd (hb j1_mem) (hb j2_mem) (hb j3_mem) hdvd with
    ⟨a, b, c⟩ | ⟨a, b, c⟩ | ⟨a, b, c⟩ | ⟨a, b, c⟩ | ⟨a, b, c⟩ | ⟨a, -, -⟩
  · exact (H.not_case_000 a b c).elim
  · exact ⟨a, b, c⟩
  · exact (H.not_case_111 a b c).elim
  · exact (H.not_case_002 a b c).elim
  · exact (H.not_case_112 a b c).elim
  · exact (H.mcount_j1_ne_two a).elim

theorem ncard_orb
    (H : Hyp t L E p) : (orb E t).ncard = 22 := by
  obtain ⟨h1, h2, h3⟩ := H.mcount_values
  rw [H.ncard_orb_eq, h1, h2, h3]

theorem notMem_orb_of_mem_conjClass_j3
    (H : Hyp t L E p) {x : G}
    (hx : pe p x ∈ conjClass uK j3) : x ∉ orb E t :=
  notMem_orb_of_mcount_zero (by rw [H.mcount_eq_of_mem_conjClass hx, H.mcount_values.2.2]) rfl

theorem notMem_orb_of_mem_conjClass_j2
    (H : Hyp t L E p) {x : G}
    (hx : pe p x ∈ conjClass uK j2) : x ∉ orb E t :=
  notMem_orb_of_mcount_zero (by rw [H.mcount_eq_of_mem_conjClass hx, H.mcount_values.2.1]) rfl

theorem mem_conjClass_j1_of_mem_orb
    (H : Hyp t L E p) {s : G} (hs : s ∈ orb E t)
    (hst : s ≠ t) : pe p s ∈ conjClass uK j1 := by
  rcases H.mem_cls_of_mem_orb hs hst with hc | hc | hc
  · exact mem_cls.1 hc
  · exact absurd hs (H.notMem_orb_of_mem_conjClass_j2 (mem_cls.1 hc))
  · exact absurd hs (H.notMem_orb_of_mem_conjClass_j3 (mem_cls.1 hc))

theorem existsUnique_mem_orb
    (H : Hyp t L E p) {x : Equiv.Perm (Fin 693)}
    (hx : x ∈ conjClass uK j1) : ∃! s, s ∈ orb E t ∧ pe p s = x := by
  have h : mcount E t p x = 1 := by rw [H.mcount_eq_of_mem_conjClass hx, H.mcount_values.1]
  obtain ⟨s, hs⟩ := Set.ncard_eq_one.1 h
  have hmem : s ∈ {s | s ∈ orb E t ∧ pe p s = x} := by rw [hs]; rfl
  refine ⟨s, hmem, fun s' hs' => ?_⟩
  have : s' ∈ {s | s ∈ orb E t ∧ pe p s = x} := hs'
  rw [hs] at this
  exact this

theorem orb_eq
    (H : Hyp t L E p) :
    ∃ z ∈ E, pe p z = j1 ∧ (∀ g : G, g⁻¹ * t * g ≠ z) ∧ z * t ∈ orb E t ∧
      orb E t = insert t {s | ∃ ℓ ∈ normalizer (E : Set G) ⊓ L, ℓ⁻¹ * (z * t) * ℓ = s} := by
  obtain ⟨z, hzE, hpz, u, -, v, -, hu3, hv3, huz, hvz, hz⟩ := H.exists_sq_lift
  have hzL := H.E_le_L hzE
  have hnc : ∀ g : G, g⁻¹ * t * g ≠ z := H.not_conj_of_sq hu3 hv3 huz hvz hz
  have hzo : z ∉ orb E t := fun ⟨n, _, hn⟩ => hnc n hn
  have hzt : z * t ∈ orb E t := by
    by_contra h
    exact hzo ((H.mem_orb_iff_of_mcount_one hzL (by rw [hpz, H.mcount_values.1])).2 h)
  refine ⟨z, hzE, hpz, hnc, hzt, ?_⟩
  have hztL : z * t ∈ L := L.mul_mem hzL H.t_mem
  have hpzt : pe p (z * t) = j1 := by rw [pe_mul p hzL H.t_mem, H.pe_t, mul_one, hpz]
  ext s
  simp only [Set.mem_insert_iff, Set.mem_ofPred_eq]
  constructor
  · intro hs
    by_cases hst : s = t
    · exact Or.inl hst
    right
    obtain ⟨c, hc, hcs⟩ := H.mem_conjClass_j1_of_mem_orb hs hst
    obtain ⟨ℓ, hℓL, hpℓ⟩ := H.exists_lift (uK_le_T46 (uK.inv_mem hc))
    have hℓN := H.lift_mem_normalizer (uK.inv_mem hc) hℓL hpℓ
    refine ⟨ℓ, ⟨hℓN, hℓL⟩, ?_⟩
    have h1 : ℓ⁻¹ * (z * t) * ℓ ∈ orb E t := conj_mem_orb hℓN hzt
    have h2 : pe p (ℓ⁻¹ * (z * t) * ℓ) = pe p s := by
      have e := pe_conj p (L.inv_mem hℓL) hztL
      rw [inv_inv, pe_inv p hℓL, hpℓ, inv_inv, hpzt] at e
      rw [e, hcs]
    obtain ⟨s0, -, huniq⟩ := H.existsUnique_mem_orb (x := pe p s) ⟨c, hc, hcs⟩
    exact (huniq _ ⟨h1, h2⟩).trans (huniq s ⟨hs, rfl⟩).symm
  · rintro (rfl | ⟨ℓ, hℓ, rfl⟩)
    · exact t_mem_orb
    · exact conj_mem_orb hℓ.1 hzt

end Hyp

end Main

end CFSG.EvenSmallLie.UnitarySix.ToddOrbit
