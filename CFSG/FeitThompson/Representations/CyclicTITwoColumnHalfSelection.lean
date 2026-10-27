module

public import CFSG.FeitThompson.Representations.TIRectangleCoefficientExchange
import CFSG.FeitThompson.Representations.EqualDegreeZeroLatticeBasis

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

theorem exists_ne_ne_of_three_le_natCard {α : Type*} (h : 3 ≤ Nat.card α) (a b : α) :
    ∃ c : α, c ≠ a ∧ c ≠ b := by
  by_contra hc
  have hsub : (Set.univ : Set α) ⊆ {a, b} := fun c _ => by
    rcases eq_or_ne c a with rfl | hca
    · exact Set.mem_insert _ _
    · rcases eq_or_ne c b with rfl | hcb
      · exact Set.mem_insert_of_mem _ rfl
      · exact absurd ⟨hca, hcb⟩ fun h => hc ⟨c, h⟩
  have : Finite α := Nat.finite_of_card_ne_zero (by omega)
  have hle := Set.ncard_le_ncard hsub (Set.toFinite _)
  rw [Set.ncard_univ] at hle
  have h2 : ({a, b} : Set α).ncard ≤ 2 := le_trans (Set.ncard_insert_le _ _) (by simp)
  omega

theorem iff_of_ite_eq_ite {c : ℂ} (hc : c ≠ 0) {P Q : Prop} [Decidable P] [Decidable Q]
    (h : (if P then c else 0) = (if Q then c else 0)) : P ↔ Q := by
  refine ⟨fun hP => ?_, fun hQ => ?_⟩ <;> by_contra hn
  · rw [if_pos hP, if_neg hn] at h; exact hc h
  · rw [if_neg hn, if_pos hQ] at h; exact hc h.symm

variable {G : Type*} [Group G] {W W1 W2 : Subgroup G}
  {σ : classFun ↥W →ₗ[ℂ] classFun G}

namespace IsCyclicTIPair

noncomputable def signedTwoColumn (hW : IsCyclicTIPair W W1 W2)
    (σ : classFun ↥W →ₗ[ℂ] classFun G) (δ : ℂ) (j k : Irr ↥W2) (p : Irr ↥W1 × Bool) : G → ℂ :=
  if p.2 then δ • hW.prodCharEta σ p.1 j else (-δ) • hW.prodCharEta σ p.1 k

@[simp]
theorem signedTwoColumn_apply_true (hW : IsCyclicTIPair W W1 W2) (δ : ℂ) (j k : Irr ↥W2)
    (i : Irr ↥W1) : hW.signedTwoColumn σ δ j k (i, true) = δ • hW.prodCharEta σ i j := (rfl)

@[simp]
theorem signedTwoColumn_apply_false (hW : IsCyclicTIPair W W1 W2) (δ : ℂ) (j k : Irr ↥W2)
    (i : Irr ↥W1) : hW.signedTwoColumn σ δ j k (i, false) = (-δ) • hW.prodCharEta σ i k := (rfl)

theorem range_signedTwoColumn (hW : IsCyclicTIPair W W1 W2) (δ : ℂ) (j k : Irr ↥W2) :
    Set.range (hW.signedTwoColumn σ δ j k) =
      (Set.range fun i : Irr ↥W1 => δ • hW.prodCharEta σ i j) ∪
        (Set.range fun i : Irr ↥W1 => (-δ) • hW.prodCharEta σ i k) := by
  ext x
  refine ⟨?_, ?_⟩
  · rintro ⟨⟨i, b⟩, rfl⟩
    cases b
    · exact Or.inr ⟨i, rfl⟩
    · exact Or.inl ⟨i, rfl⟩
  · rintro (⟨i, rfl⟩ | ⟨i, rfl⟩)
    · exact ⟨(i, true), rfl⟩
    · exact ⟨(i, false), rfl⟩

theorem signedTwoColumn_mem_classFun (hW : IsCyclicTIPair W W1 W2) (δ : ℂ) (j k : Irr ↥W2)
    (p : Irr ↥W1 × Bool) : hW.signedTwoColumn σ δ j k p ∈ classFun G := by
  rcases p with ⟨i, b⟩
  cases b
  · exact Submodule.smul_mem _ _ (hW.prodCharEta_mem_classFun i k)
  · exact Submodule.smul_mem _ _ (hW.prodCharEta_mem_classFun i j)

theorem sum_signedTwoColumn_mem_classFun (hW : IsCyclicTIPair W W1 W2) (δ : ℂ) (j k : Irr ↥W2)
    (S : Finset (Irr ↥W1 × Bool)) :
    (∑ p ∈ S, hW.signedTwoColumn σ δ j k p) ∈ classFun G :=
  Submodule.sum_mem _ fun p _ => hW.signedTwoColumn_mem_classFun δ j k p

noncomputable def prodCharEtaColSum (hW : IsCyclicTIPair W W1 W2)
    (σ : classFun ↥W →ₗ[ℂ] classFun G) (j : Irr ↥W2) : G → ℂ :=
  letI := hW.finite_left
  letI : Fintype (Irr ↥W1) := Fintype.ofFinite _
  ∑ i : Irr ↥W1, hW.prodCharEta σ i j

theorem prodCharEtaColSum_eq_sum [Fintype (Irr ↥W1)] (hW : IsCyclicTIPair W W1 W2)
    (j : Irr ↥W2) : hW.prodCharEtaColSum σ j = ∑ i : Irr ↥W1, hW.prodCharEta σ i j := by
  rw [prodCharEtaColSum]
  congr 1
  exact congrArg (@Finset.univ (Irr ↥W1)) (Subsingleton.elim _ _)

theorem prodCharEtaColSum_mem_classFun (hW : IsCyclicTIPair W W1 W2) (j : Irr ↥W2) :
    hW.prodCharEtaColSum σ j ∈ classFun G := by
  have := hW.finite_left
  have : Fintype (Irr ↥W1) := Fintype.ofFinite _
  rw [hW.prodCharEtaColSum_eq_sum]
  exact Submodule.sum_mem _ fun i _ => hW.prodCharEta_mem_classFun i j

private theorem sum_eq_col_of_card_eq [Fintype (Irr ↥W1)] (hW : IsCyclicTIPair W W1 W2) (δ : ℂ)
    (j k : Irr ↥W2) {S : Finset (Irr ↥W1 × Bool)}
    (hmem : ∀ (b : Bool) (i i' : Irr ↥W1), (i, b) ∈ S ↔ (i', b) ∈ S)
    (hcard : S.card = Fintype.card (Irr ↥W1)) (hI : Fintype.card (Irr ↥W1) ≠ 0) :
    (∑ p ∈ S, hW.signedTwoColumn σ δ j k p) = δ • ∑ i, hW.prodCharEta σ i j ∨
      (∑ p ∈ S, hW.signedTwoColumn σ δ j k p) = (-δ) • ∑ i, hW.prodCharEta σ i k := by
  classical
  obtain ⟨i₀⟩ : Nonempty (Irr ↥W1) := Fintype.card_pos_iff.mp (by omega)
  by_cases ht : (i₀, true) ∈ S <;> by_cases hf : (i₀, false) ∈ S
  ·
    have hSu : S = Finset.univ := by
      refine Finset.eq_univ_of_forall ?_
      rintro ⟨i, b⟩
      cases b
      · exact (hmem false i₀ i).mp hf
      · exact (hmem true i₀ i).mp ht
    rw [hSu, Finset.card_univ, Fintype.card_prod, Fintype.card_bool] at hcard
    omega
  ·
    left
    have hSj : S = Finset.univ.image (fun i : Irr ↥W1 => (i, true)) := by
      ext ⟨i, b⟩
      simp only [Finset.mem_image, Finset.mem_univ, true_and, Prod.mk.injEq]
      cases b
      · exact ⟨fun h => absurd ((hmem false i i₀).mp h) hf, fun ⟨_, _, h⟩ => absurd h (by simp)⟩
      · exact ⟨fun _ => ⟨i, rfl, rfl⟩, fun _ => (hmem true i₀ i).mp ht⟩
    rw [hSj, Finset.sum_image (by intro a _ b _ h; exact ((Prod.mk.injEq _ _ _ _).mp h).1),
      Finset.smul_sum]
    exact Finset.sum_congr rfl fun i _ => rfl
  ·
    right
    have hSk : S = Finset.univ.image (fun i : Irr ↥W1 => (i, false)) := by
      ext ⟨i, b⟩
      simp only [Finset.mem_image, Finset.mem_univ, true_and, Prod.mk.injEq]
      cases b
      · exact ⟨fun _ => ⟨i, rfl, rfl⟩, fun _ => (hmem false i₀ i).mp hf⟩
      · exact ⟨fun h => absurd ((hmem true i i₀).mp h) ht, fun ⟨_, _, h⟩ => absurd h (by simp)⟩
    rw [hSk, Finset.sum_image (by intro a _ b _ h; exact ((Prod.mk.injEq _ _ _ _).mp h).1),
      Finset.smul_sum]
    exact Finset.sum_congr rfl fun i _ => rfl
  ·
    have hSe : S = ∅ := by
      refine Finset.eq_empty_iff_forall_notMem.mpr ?_
      rintro ⟨i, b⟩ hmemS
      cases b
      · exact hf ((hmem false i i₀).mp hmemS)
      · exact ht ((hmem true i i₀).mp hmemS)
    rw [hSe, Finset.card_empty] at hcard
    omega

section

variable [Fintype G] [Fintype ↥W]

theorem cfInner_signedTwoColumn_true_self (hW : IsCyclicTIPair W W1 W2)
    (hσ : IsCyclicTIIsometry W W1 W2 σ) (δ : ℂ) (j k : Irr ↥W2) (i : Irr ↥W1) :
    cfInner (hW.signedTwoColumn σ δ j k (i, true)) (hW.prodCharEta σ i j) = δ := by
  rw [signedTwoColumn_apply_true, cfInner_smul_left, hW.cfInner_prodCharEta hσ]
  simp

theorem cfInner_signedTwoColumn_false_self (hW : IsCyclicTIPair W W1 W2)
    (hσ : IsCyclicTIIsometry W W1 W2 σ) (δ : ℂ) (j k : Irr ↥W2) (i : Irr ↥W1) :
    cfInner (hW.signedTwoColumn σ δ j k (i, false)) (hW.prodCharEta σ i k) = -δ := by
  rw [signedTwoColumn_apply_false, cfInner_smul_left, hW.cfInner_prodCharEta hσ]
  simp

theorem cfInner_signedTwoColumn_true_eq_zero (hW : IsCyclicTIPair W W1 W2)
    (hσ : IsCyclicTIIsometry W W1 W2 σ) (δ : ℂ) {j k : Irr ↥W2} {i i' : Irr ↥W1} {l : Irr ↥W2}
    (h : i' ≠ i ∨ j ≠ l) :
    cfInner (hW.signedTwoColumn σ δ j k (i', true)) (hW.prodCharEta σ i l) = 0 := by
  rw [signedTwoColumn_apply_true, cfInner_smul_left, hW.cfInner_prodCharEta hσ]
  rcases h with h | h <;> simp [h]

theorem cfInner_signedTwoColumn_false_eq_zero (hW : IsCyclicTIPair W W1 W2)
    (hσ : IsCyclicTIIsometry W W1 W2 σ) (δ : ℂ) {j k : Irr ↥W2} {i i' : Irr ↥W1} {l : Irr ↥W2}
    (h : i' ≠ i ∨ k ≠ l) :
    cfInner (hW.signedTwoColumn σ δ j k (i', false)) (hW.prodCharEta σ i l) = 0 := by
  rw [signedTwoColumn_apply_false, cfInner_smul_left, hW.cfInner_prodCharEta hσ]
  rcases h with h | h <;> simp [h]

theorem signedTwoColumn_injective (hW : IsCyclicTIPair W W1 W2)
    (hσ : IsCyclicTIIsometry W W1 W2 σ) {δ : ℂ} (hδ : δ ≠ 0) {j k : Irr ↥W2} (hjk : j ≠ k) :
    Function.Injective (hW.signedTwoColumn σ δ j k) := by
  rintro ⟨i, b⟩ ⟨i', b'⟩ h
  cases b <;> cases b'
  · have h1 := hW.cfInner_signedTwoColumn_false_self hσ δ j k i
    rw [h] at h1
    rcases eq_or_ne i' i with rfl | hne
    · rfl
    · rw [hW.cfInner_signedTwoColumn_false_eq_zero hσ δ (Or.inl hne)] at h1
      exact absurd (neg_eq_zero.mp h1.symm) hδ
  · have h1 := hW.cfInner_signedTwoColumn_false_self hσ δ j k i
    rw [h, hW.cfInner_signedTwoColumn_true_eq_zero hσ δ (Or.inr hjk)] at h1
    exact absurd (neg_eq_zero.mp h1.symm) hδ
  · have h1 := hW.cfInner_signedTwoColumn_true_self hσ δ j k i
    rw [h, hW.cfInner_signedTwoColumn_false_eq_zero hσ δ (Or.inr (Ne.symm hjk))] at h1
    exact absurd h1.symm hδ
  · have h1 := hW.cfInner_signedTwoColumn_true_self hσ δ j k i
    rw [h] at h1
    rcases eq_or_ne i' i with rfl | hne
    · rfl
    · rw [hW.cfInner_signedTwoColumn_true_eq_zero hσ δ (Or.inl hne)] at h1
      exact absurd h1.symm hδ

open scoped Classical in
theorem cfInner_sum_signedTwoColumn_left (hW : IsCyclicTIPair W W1 W2)
    (hσ : IsCyclicTIIsometry W W1 W2 σ) (δ : ℂ) {j k : Irr ↥W2} (hjk : j ≠ k)
    (S : Finset (Irr ↥W1 × Bool)) (i : Irr ↥W1) :
    cfInner (∑ p ∈ S, hW.signedTwoColumn σ δ j k p) (hW.prodCharEta σ i j) =
      if (i, true) ∈ S then δ else 0 := by
  have key : ∀ p ∈ S, cfInner (hW.signedTwoColumn σ δ j k p) (hW.prodCharEta σ i j) =
      if p = (i, true) then δ else 0 := by
    rintro ⟨i', b⟩ -
    cases b
    · rw [hW.cfInner_signedTwoColumn_false_eq_zero hσ δ (Or.inr (Ne.symm hjk)), if_neg (by simp)]
    · rcases eq_or_ne i' i with rfl | hne
      · rw [hW.cfInner_signedTwoColumn_true_self hσ δ j k, if_pos rfl]
      · rw [hW.cfInner_signedTwoColumn_true_eq_zero hσ δ (Or.inl hne), if_neg (by simp [hne])]
  rw [cfInner_sum_left, Finset.sum_congr rfl key, Finset.sum_ite_eq' S (i, true) fun _ => δ]

open scoped Classical in
theorem cfInner_sum_signedTwoColumn_right (hW : IsCyclicTIPair W W1 W2)
    (hσ : IsCyclicTIIsometry W W1 W2 σ) (δ : ℂ) {j k : Irr ↥W2} (hjk : j ≠ k)
    (S : Finset (Irr ↥W1 × Bool)) (i : Irr ↥W1) :
    cfInner (∑ p ∈ S, hW.signedTwoColumn σ δ j k p) (hW.prodCharEta σ i k) =
      if (i, false) ∈ S then -δ else 0 := by
  have key : ∀ p ∈ S, cfInner (hW.signedTwoColumn σ δ j k p) (hW.prodCharEta σ i k) =
      if p = (i, false) then -δ else 0 := by
    rintro ⟨i', b⟩ -
    cases b
    · rcases eq_or_ne i' i with rfl | hne
      · rw [hW.cfInner_signedTwoColumn_false_self hσ δ j k, if_pos rfl]
      · rw [hW.cfInner_signedTwoColumn_false_eq_zero hσ δ (Or.inl hne), if_neg (by simp [hne])]
    · rw [hW.cfInner_signedTwoColumn_true_eq_zero hσ δ (Or.inr hjk), if_neg (by simp)]
  rw [cfInner_sum_left, Finset.sum_congr rfl key, Finset.sum_ite_eq' S (i, false) fun _ => -δ]

theorem cfInner_sum_signedTwoColumn_eq_zero (hW : IsCyclicTIPair W W1 W2)
    (hσ : IsCyclicTIIsometry W W1 W2 σ) (δ : ℂ) {j k l : Irr ↥W2} (hjl : j ≠ l) (hkl : k ≠ l)
    (S : Finset (Irr ↥W1 × Bool)) (i : Irr ↥W1) :
    cfInner (∑ p ∈ S, hW.signedTwoColumn σ δ j k p) (hW.prodCharEta σ i l) = 0 := by
  rw [cfInner_sum_left]
  refine Finset.sum_eq_zero ?_
  rintro ⟨i', b⟩ -
  cases b
  · exact hW.cfInner_signedTwoColumn_false_eq_zero hσ δ (Or.inr hkl)
  · exact hW.cfInner_signedTwoColumn_true_eq_zero hσ δ (Or.inr hjl)

theorem cfInner_prodCharEta_rectangle (hW : IsCyclicTIPair W W1 W2)
    (hσ : IsCyclicTIIsometry W W1 W2 σ) {f : G → ℂ} (hf : f ∈ classFun G)
    (hf0 : ∀ x ∈ cyclicTIDiff W W1 W2, f x = 0) (i i' : Irr ↥W1) (l l' : Irr ↥W2) :
    cfInner f (hW.prodCharEta σ i l) + cfInner f (hW.prodCharEta σ i' l') =
      cfInner f (hW.prodCharEta σ i l') + cfInner f (hW.prodCharEta σ i' l) := by
  have E := fun (a : Irr ↥W1) (b : Irr ↥W2) => hW.cfInner_prodCharEta_exchange hσ hf hf0 a b
  linear_combination E i l + E i' l' - E i l' - E i' l

open scoped Classical in
theorem mem_signedTwoColumn_index_iff (hW : IsCyclicTIPair W W1 W2)
    (hσ : IsCyclicTIIsometry W W1 W2 σ) {δ : ℂ} (hδ : δ ≠ 0) {j k : Irr ↥W2} (hjk : j ≠ k)
    {S : Finset (Irr ↥W1 × Bool)}
    (hQ0 : ∀ x ∈ cyclicTIDiff W W1 W2, (∑ p ∈ S, hW.signedTwoColumn σ δ j k p) x = 0)
    (b : Bool) (i i' : Irr ↥W1) : (i, b) ∈ S ↔ (i', b) ∈ S := by
  obtain ⟨m, hmj, hmk⟩ := exists_ne_ne_of_three_le_natCard
    (a := j) (b := k) (by rw [hW.card_Irr_right]; exact hW.three_le_natCard_right)
  set Q := ∑ p ∈ S, hW.signedTwoColumn σ δ j k p with hQ
  have hQc : Q ∈ classFun G := hW.sum_signedTwoColumn_mem_classFun δ j k S
  have hzero : ∀ a : Irr ↥W1, cfInner Q (hW.prodCharEta σ a m) = 0 := fun a =>
    hW.cfInner_sum_signedTwoColumn_eq_zero hσ δ (Ne.symm hmj) (Ne.symm hmk) S a
  have hrect := hW.cfInner_prodCharEta_rectangle hσ hQc hQ0 i i'
  cases b
  · have h1 := hrect k m
    rw [hzero i, hzero i', add_zero, zero_add,
      hW.cfInner_sum_signedTwoColumn_right hσ δ hjk S i,
      hW.cfInner_sum_signedTwoColumn_right hσ δ hjk S i'] at h1
    exact iff_of_ite_eq_ite (neg_ne_zero.mpr hδ) h1
  · have h1 := hrect j m
    rw [hzero i, hzero i', add_zero, zero_add,
      hW.cfInner_sum_signedTwoColumn_left hσ δ hjk S i,
      hW.cfInner_sum_signedTwoColumn_left hσ δ hjk S i'] at h1
    exact iff_of_ite_eq_ite hδ h1

open scoped Classical in
theorem eq_col_sum_of_card_eq_of_vanishing_on_cyclicTIDiff_of_ne_zero
    (hW : IsCyclicTIPair W W1 W2) (hσ : IsCyclicTIIsometry W W1 W2 σ) {δ : ℂ} (hδ : δ ≠ 0)
    {j k : Irr ↥W2} (hjk : j ≠ k) {T0 : Finset (G → ℂ)}
    (hT0 : (T0 : Set (G → ℂ)) ⊆ Set.range (hW.signedTwoColumn σ δ j k))
    (hcard : T0.card = Nat.card (Irr ↥W1))
    (hQ0 : ∀ x ∈ cyclicTIDiff W W1 W2, (∑ t ∈ T0, t) x = 0) :
    (∑ t ∈ T0, t) = δ • hW.prodCharEtaColSum σ j ∨
      (∑ t ∈ T0, t) = (-δ) • hW.prodCharEtaColSum σ k := by
  have := hW.finite_left
  have : Fintype (Irr ↥W1) := Fintype.ofFinite _
  rw [hW.prodCharEtaColSum_eq_sum, hW.prodCharEtaColSum_eq_sum]
  have hinj := hW.signedTwoColumn_injective hσ hδ hjk
  set S : Finset (Irr ↥W1 × Bool) :=
    {p ∈ Finset.univ | hW.signedTwoColumn σ δ j k p ∈ T0} with hS
  have hmemS : ∀ p, p ∈ S ↔ hW.signedTwoColumn σ δ j k p ∈ T0 := by simp [hS]
  have himage : S.image (hW.signedTwoColumn σ δ j k) = T0 := by
    ext t
    simp only [Finset.mem_image]
    refine ⟨fun ⟨p, hp, hpt⟩ => hpt ▸ (hmemS p).mp hp, fun ht => ?_⟩
    obtain ⟨p, rfl⟩ := hT0 ht
    exact ⟨p, (hmemS p).mpr ht, rfl⟩
  have hsum : (∑ t ∈ T0, t) = ∑ p ∈ S, hW.signedTwoColumn σ δ j k p := by
    rw [← himage, Finset.sum_image fun a _ b _ h => hinj h]
  have hcardS : S.card = Fintype.card (Irr ↥W1) := by
    rw [← Finset.card_image_of_injective S hinj, himage, hcard, Nat.card_eq_fintype_card]
  have hIne : Fintype.card (Irr ↥W1) ≠ 0 := by
    have h3 : 3 ≤ Nat.card (Irr ↥W1) := by
      rw [hW.card_Irr_left]; exact hW.three_le_natCard_left
    rw [Nat.card_eq_fintype_card] at h3
    omega
  rw [hsum] at hQ0 ⊢
  exact hW.sum_eq_col_of_card_eq δ j k
    (hW.mem_signedTwoColumn_index_iff hσ hδ hjk hQ0) hcardS hIne

theorem eq_col_sum_of_card_eq_of_vanishing_on_cyclicTIDiff (hW : IsCyclicTIPair W W1 W2)
    (hσ : IsCyclicTIIsometry W W1 W2 σ) {δ : ℂ} (hδ : δ = 1 ∨ δ = -1) {j k : Irr ↥W2}
    (hjk : j ≠ k) {T0 : Finset (G → ℂ)}
    (hT0 : (T0 : Set (G → ℂ)) ⊆ Set.range (hW.signedTwoColumn σ δ j k))
    (hcard : T0.card = Nat.card (Irr ↥W1))
    (hQ0 : ∀ x ∈ cyclicTIDiff W W1 W2, (∑ t ∈ T0, t) x = 0) :
    (∑ t ∈ T0, t) = δ • hW.prodCharEtaColSum σ j ∨
      (∑ t ∈ T0, t) = (-δ) • hW.prodCharEtaColSum σ k :=
  hW.eq_col_sum_of_card_eq_of_vanishing_on_cyclicTIDiff_of_ne_zero hσ
    (by rcases hδ with rfl | rfl <;> norm_num) hjk hT0 hcard hQ0

end

end IsCyclicTIPair

end CFSG.FeitThompson

end
