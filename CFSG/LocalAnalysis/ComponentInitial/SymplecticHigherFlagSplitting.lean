module

public import CFSG.LocalAnalysis.ComponentInitial.SymplecticFlagExtension
public import TauCeti.LinearAlgebra.BilinearForm.Orthogonal
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticFlagData

public noncomputable section

namespace CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher

open Module Submodule SymplecticFlag
open LinearMap (BilinForm)

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

@[expose] def IsSelfDualChain (B : BilinForm K V) (N : ℕ) (F : ℕ → Submodule K V) : Prop :=
  F 0 = ⊥ ∧ (∀ i < N, F i ≤ F (i + 1)) ∧ ∀ i ≤ N, B.orthogonal (F i) = F (N - i)

@[expose] def IsSelfDualFlag (B : BilinForm K V) (r : ℕ) (F : ℕ → Submodule K V) : Prop :=
  (∀ i ≤ 2 * r, finrank K (F i) = i) ∧ (∀ i < 2 * r, F i ≤ F (i + 1)) ∧
    ∀ i ≤ 2 * r, B.orthogonal (F i) = F (2 * r - i)

variable {B : BilinForm K V}

theorem IsSelfDualFlag.isSelfDualChain [FiniteDimensional K V] {r : ℕ}
    {F : ℕ → Submodule K V} (hF : IsSelfDualFlag B r F) : IsSelfDualChain B (2 * r) F :=
  ⟨Submodule.finrank_eq_zero.mp (hF.1 0 (Nat.zero_le _)), hF.2.1, hF.2.2⟩

theorem IsSelfDualChain.le {N : ℕ} {F : ℕ → Submodule K V} (hF : IsSelfDualChain B N F)
    {i j : ℕ} (hij : i ≤ j) (hj : j ≤ N) : F i ≤ F j :=
  flag_le hF.2.1 hij hj

theorem IsSelfDualChain.top {N : ℕ} {F : ℕ → Submodule K V} (hF : IsSelfDualChain B N F) :
    F N = ⊤ := by
  have h := hF.2.2 0 (Nat.zero_le _)
  rw [hF.1, BilinForm.orthogonal_bot, Nat.sub_zero] at h
  exact h.symm

@[expose] def IsPairCompatible (B : BilinForm K V) (N : ℕ) (F : ℕ → Submodule K V) (e f : V) :
    Prop :=
  ∀ i ≤ N, ∀ u ∈ F i, (B f u = 0 ∨ e ∈ F i) ∧ (B e u = 0 ∨ f ∈ F i)

variable {N : ℕ} {F : ℕ → Submodule K V} {e f : V}

theorem IsPairCompatible.smul_left_mem (h : IsPairCompatible B N F e f) {i : ℕ} (hi : i ≤ N)
    {u : V} (hu : u ∈ F i) : B f u • e ∈ F i := by
  rcases (h i hi u hu).1 with h1 | h1
  · rw [h1, zero_smul]
    exact zero_mem _
  · exact smul_mem _ _ h1

theorem IsPairCompatible.smul_right_mem (h : IsPairCompatible B N F e f) {i : ℕ} (hi : i ≤ N)
    {u : V} (hu : u ∈ F i) : B e u • f ∈ F i := by
  rcases (h i hi u hu).2 with h1 | h1
  · rw [h1, zero_smul]
    exact zero_mem _
  · exact smul_mem _ _ h1

theorem IsPairCompatible.proj_mem (h : IsPairCompatible B N F e f) {i : ℕ} (hi : i ≤ N)
    {u : V} (hu : u ∈ F i) : u - B f u • e + B e u • f ∈ F i :=
  add_mem (sub_mem hu (h.smul_left_mem hi hu)) (h.smul_right_mem hi hu)

theorem isPairCompatible_of_first (hF : IsSelfDualChain B N F) {i₀ : ℕ} (hi₀ : i₀ ≤ N)
    (hbot : ∀ m < i₀, F m = ⊥) (he : e ∈ F i₀) (f : V) : IsPairCompatible B N F e f := by
  intro i hi u hu
  constructor
  · by_cases h : i₀ ≤ i
    · exact Or.inr (hF.le h hi he)
    · left
      rw [hbot i (by omega), mem_bot] at hu
      rw [hu, map_zero]
  · by_cases h : i ≤ N - i₀
    · left
      have hu' : u ∈ F (N - i₀) := hF.le h (Nat.sub_le _ _) hu
      rw [← hF.2.2 i₀ hi₀] at hu'
      exact hu' e he
    · right
      have h1 := hF.2.2 (N - i) (Nat.sub_le _ _)
      rw [hbot (N - i) (by omega), BilinForm.orthogonal_bot, Nat.sub_sub_self hi] at h1
      rw [← h1]
      trivial

theorem isPairCompatible_of_least {G : ℕ → Submodule K V} (hG : IsSelfDualChain B N G) {j : ℕ}
    (hj1 : 1 ≤ j) (hjN : j ≤ N) (he : e ∈ G j) (hf : f ∈ G (N + 1 - j)) :
    IsPairCompatible B N G e f := by
  intro i hi u hu
  constructor
  · by_cases h : j ≤ i
    · exact Or.inr (hG.le h hi he)
    · left
      have hu' : u ∈ G (j - 1) := hG.le (by omega) (by omega) hu
      have h1 := hG.2.2 (N + 1 - j) (by omega)
      rw [show N - (N + 1 - j) = j - 1 by omega] at h1
      rw [← h1] at hu'
      exact hu' f hf
  · by_cases h : N + 1 - j ≤ i
    · exact Or.inr (hG.le h hi hf)
    · left
      have hu' : u ∈ G (N - j) := hG.le (by omega) (by omega) hu
      rw [← hG.2.2 j hjN] at hu'
      exact hu' e he

theorem exists_partner {G : ℕ → Submodule K V} (hG : IsSelfDualChain B N G) {j : ℕ}
    (hj1 : 1 ≤ j) (hjN : j ≤ N) (he : e ∉ G (j - 1)) : ∃ f ∈ G (N + 1 - j), B f e = 1 := by
  have h1 := hG.2.2 (N + 1 - j) (by omega)
  rw [show N - (N + 1 - j) = j - 1 by omega] at h1
  rw [← h1, BilinForm.mem_orthogonal_iff] at he
  push Not at he
  obtain ⟨n, hn, hne⟩ := he
  exact ⟨(B n e)⁻¹ • n, smul_mem _ _ hn, by
    rw [map_smul, LinearMap.smul_apply, smul_eq_mul, inv_mul_cancel₀ hne]⟩

section Pair

variable (hB : B.IsAlt) (hfe : B f e = 1)
include hB hfe

theorem proj_mem_orthogonal (u : V) :
    u - B f u • e + B e u • f ∈ B.orthogonal (span K {e, f}) :=
  hB.sub_smul_add_smul_mem_orthogonal_span_pair hfe u

omit hB hfe in
theorem eq_proj_add (u : V) : u = (B f u • e - B e u • f) + (u - B f u • e + B e u • f) := by
  abel

theorem span_pair_inf_orthogonal :
    span K {e, f} ⊓ B.orthogonal (span K {e, f}) = ⊥ := by
  rw [eq_bot_iff]
  rintro x ⟨hx, hxZ⟩
  obtain ⟨a, c, rfl⟩ := mem_span_pair.mp hx
  obtain ⟨h1, h2⟩ := (BilinForm.mem_orthogonal_span_pair_iff B).mp hxZ
  have hef : B e f = -1 := by rw [← hB.neg_eq, hfe]
  simp only [map_add, map_smul, smul_eq_mul, hB.self_eq_zero, hef, hfe, mul_zero, zero_add,
    add_zero, mul_neg, mul_one, neg_eq_zero] at h1 h2
  rw [h1, h2, zero_smul, zero_smul, add_zero]
  exact zero_mem _

theorem eq_of_mem_span_pair {x : V} (hx : x ∈ span K {e, f}) :
    x = B f x • e - B e x • f := by
  have h := proj_mem_orthogonal hB hfe x
  have hH : x - B f x • e + B e x • f ∈ span K {e, f} :=
    add_mem (sub_mem hx (smul_mem _ _ (subset_span (Set.mem_insert e {f}))))
      (smul_mem _ _ (subset_span (Set.mem_insert_of_mem e (Set.mem_singleton f))))
  have h0 : x - B f x • e + B e x • f = 0 := by
    have := span_pair_inf_orthogonal hB hfe
    rw [eq_bot_iff] at this
    exact (mem_bot K).mp (this ⟨hH, h⟩)
  calc x = (B f x • e - B e x • f) + (x - B f x • e + B e x • f) := eq_proj_add x
    _ = B f x • e - B e x • f := by rw [h0, add_zero]

theorem IsPairCompatible.sup_eq (h : IsPairCompatible B N F e f) {i : ℕ} (hi : i ≤ N) :
    F i ⊓ span K {e, f} ⊔ F i ⊓ B.orthogonal (span K {e, f}) = F i := by
  refine le_antisymm (sup_le inf_le_left inf_le_left) fun u hu => ?_
  rw [eq_proj_add (B := B) (e := e) (f := f) u]
  refine add_mem_sup ⟨?_, ?_⟩ ⟨h.proj_mem hi hu, proj_mem_orthogonal hB hfe u⟩
  · exact sub_mem (h.smul_left_mem hi hu) (h.smul_right_mem hi hu)
  · exact sub_mem (smul_mem _ _ (subset_span (Set.mem_insert e {f})))
      (smul_mem _ _ (subset_span (Set.mem_insert_of_mem e (Set.mem_singleton f))))

theorem IsPairCompatible.inf_span_pair_le (h : IsPairCompatible B N F e f) {i : ℕ} (hi : i ≤ N) :
    F i ⊓ span K {e, f} ≤ span K {x | (x = e ∧ e ∈ F i) ∨ (x = f ∧ f ∈ F i)} := by
  rintro x ⟨hxF, hx⟩
  rw [eq_of_mem_span_pair hB hfe hx]
  refine sub_mem ?_ ?_
  · rcases (h i hi x hxF).1 with h1 | h1
    · rw [h1, zero_smul]
      exact zero_mem _
    · exact smul_mem _ _ (subset_span (Or.inl ⟨rfl, h1⟩))
  · rcases (h i hi x hxF).2 with h1 | h1
    · rw [h1, zero_smul]
      exact zero_mem _
    · exact smul_mem _ _ (subset_span (Or.inr ⟨rfl, h1⟩))

theorem isSelfDualChain_comap (hF : IsSelfDualChain B N F) (h : IsPairCompatible B N F e f) :
    IsSelfDualChain (B.restrict (B.orthogonal (span K {e, f}))) N
      fun i => (F i).comap (B.orthogonal (span K {e, f})).subtype := by
  set Z := B.orthogonal (span K {e, f})
  refine ⟨by show (F 0).comap Z.subtype = ⊥; rw [hF.1, comap_bot, ker_subtype],
    fun i hi => comap_mono (hF.2.1 i hi), fun i hi => ?_⟩
  ext z
  simp only [BilinForm.mem_orthogonal_iff, mem_comap, subtype_apply, BilinForm.restrict_apply,
    LinearMap.domRestrict_apply]
  rw [← hF.2.2 i hi, BilinForm.mem_orthogonal_iff]
  have hz := (BilinForm.mem_orthogonal_span_pair_iff B).mp z.2
  constructor
  · intro hzF n hn
    have hP : n - B f n • e + B e n • f ∈ Z := proj_mem_orthogonal hB hfe n
    have h1 := hzF ⟨_, hP⟩ (h.proj_mem hi hn)
    simp only at h1
    have : B n z = B (n - B f n • e + B e n • f) z + B f n * B e z - B e n * B f z := by
      simp only [map_add, map_sub, map_smul, LinearMap.add_apply, LinearMap.sub_apply,
        LinearMap.smul_apply, smul_eq_mul]
      ring
    rw [this, h1, hz.1, hz.2]
    ring
  · intro hzF y hy
    exact hzF y hy

end Pair

open Classical in
theorem finrank_inf_span_pair [FiniteDimensional K V] (hB : B.IsAlt) (hfe : B f e = 1)
    (h : IsPairCompatible B N F e f) {i : ℕ} (hi : i ≤ N) :
    finrank K ↥(F i ⊓ span K {e, f}) = (if e ∈ F i then 1 else 0) + (if f ∈ F i then 1 else 0) := by
  have hli := hB.linearIndependent_pair_of_apply_eq_one hfe
  have he0 : e ≠ 0 := hli.ne_zero 0
  have hf0 : f ≠ 0 := hli.ne_zero 1
  have hle := h.inf_span_pair_le hB hfe hi
  by_cases he : e ∈ F i <;> by_cases hf : f ∈ F i
  · have heq : F i ⊓ span K {e, f} = span K {e, f} := by
      refine inf_eq_right.mpr (span_le.mpr ?_)
      rintro x (rfl | rfl)
      · exact he
      · exact hf
    rw [heq, ite_eq_left he, ite_eq_left hf, ← Matrix.range_cons_cons_empty e f ![],
      finrank_span_eq_card hli, Fintype.card_fin]
  · have heq : F i ⊓ span K {e, f} = span K {e} := by
      refine le_antisymm (hle.trans (span_le.mpr ?_))
        (le_inf ((span_singleton_le_iff_mem _ _).mpr he) (span_mono (by simp)))
      rintro x (⟨rfl, -⟩ | ⟨rfl, hx⟩)
      · exact mem_span_singleton_self _
      · exact absurd hx hf
    rw [heq, finrank_span_singleton he0, ite_eq_left he, ite_eq_right hf]
  · have heq : F i ⊓ span K {e, f} = span K {f} := by
      refine le_antisymm (hle.trans (span_le.mpr ?_))
        (le_inf ((span_singleton_le_iff_mem _ _).mpr hf) (span_mono (by simp)))
      rintro x (⟨rfl, hx⟩ | ⟨rfl, -⟩)
      · exact absurd hx he
      · exact mem_span_singleton_self _
    rw [heq, finrank_span_singleton hf0, ite_eq_right he, ite_eq_left hf]
  · have heq : F i ⊓ span K {e, f} = ⊥ := by
      refine eq_bot_iff.mpr (hle.trans (span_le.mpr ?_))
      rintro x (⟨rfl, hx⟩ | ⟨rfl, hx⟩)
      · exact absurd hx he
      · exact absurd hx hf
    rw [heq, finrank_bot, ite_eq_right he, ite_eq_right hf]

open Classical in
theorem finrank_comap_add [FiniteDimensional K V] (hB : B.IsAlt) (hfe : B f e = 1)
    (h : IsPairCompatible B N F e f) {i : ℕ} (hi : i ≤ N) :
    finrank K ((F i).comap (B.orthogonal (span K {e, f})).subtype) +
      (if e ∈ F i then 1 else 0) + (if f ∈ F i then 1 else 0) = finrank K (F i) := by
  set Z := B.orthogonal (span K {e, f})
  have hcomap : finrank K ((F i).comap Z.subtype) = finrank K ↥(F i ⊓ Z) := by
    have : (F i).comap Z.subtype = (F i ⊓ Z).comap Z.subtype := by
      rw [comap_inf, comap_subtype_self, inf_top_eq]
    rw [this, (comapSubtypeEquivOfLe (inf_le_right : F i ⊓ Z ≤ Z)).finrank_eq]
  have hsum := Submodule.finrank_sup_add_finrank_inf_eq (F i ⊓ span K {e, f}) (F i ⊓ Z)
  have hinf : F i ⊓ span K {e, f} ⊓ (F i ⊓ Z) = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨⟨-, hx⟩, -, hxZ⟩
    have := span_pair_inf_orthogonal hB hfe
    rw [eq_bot_iff] at this
    exact this ⟨hx, hxZ⟩
  rw [h.sup_eq hB hfe hi, hinf, finrank_bot, add_zero, finrank_inf_span_pair hB hfe h hi] at hsum
  omega

theorem eq_of_finrank_eq_of_chain [FiniteDimensional K V] {X : ℕ → Submodule K V}
    (hX : ∀ {a b : ℕ}, a ≤ b → b ≤ N → X a ≤ X b) {a b : ℕ} (ha : a ≤ N) (hb : b ≤ N)
    (h : finrank K (X a) = finrank K (X b)) : X a = X b := by
  rcases le_total a b with hab | hab
  · exact eq_of_le_of_finrank_eq (hX hab hb) h
  · exact (eq_of_le_of_finrank_eq (hX hab ha) h.symm).symm

@[expose] def skipTwo (j k m : ℕ) : ℕ :=
  if j < k then (if m < j then m else if m + 2 ≤ k then m + 1 else m + 2)
  else (if m < k then m else if m + 2 ≤ j then m + 1 else m + 2)

theorem two_selfdual_flag_splitting [FiniteDimensional K V] {r : ℕ} (hB : B.IsAlt)
    (hnd : B.Nondegenerate) (hV : finrank K V = 2 * r) {F G : ℕ → Submodule K V}
    (hF : IsSelfDualFlag B r F) (hG : IsSelfDualFlag B r G) {v : V} (hv : v ∈ F 1)
    (hv0 : v ≠ 0) {j : ℕ} (hj : v ∈ G j) (hjmin : ∀ i < j, v ∉ G i) :
    ∃ w ∈ G (2 * r + 1 - j), B v w = 1 ∧
      (∀ x, x - B x w • v + B x v • w ∈ B.orthogonal (span K {v, w})) ∧
      (∀ x ∈ B.orthogonal (span K {v, w}), x - B x w • v + B x v • w = x) ∧
      (∀ i ≤ 2 * r, ∀ x ∈ F i, x - B x w • v + B x v • w ∈ F i) ∧
      (∀ i ≤ 2 * r, ∀ x ∈ G i, x - B x w • v + B x v • w ∈ G i) ∧
      span K {v, w} ⊓ B.orthogonal (span K {v, w}) = ⊥ ∧
      (∀ i ≤ 2 * r, F i ⊓ span K {v, w} ⊔ F i ⊓ B.orthogonal (span K {v, w}) = F i) ∧
      (∀ i ≤ 2 * r, G i ⊓ span K {v, w} ⊔ G i ⊓ B.orthogonal (span K {v, w}) = G i) ∧
      (∀ i ≤ 2 * r, (v ∈ F i ↔ 1 ≤ i) ∧ (w ∈ F i ↔ 2 * r ≤ i)) ∧
      (∀ i ≤ 2 * r, (v ∈ G i ↔ j ≤ i) ∧ (w ∈ G i ↔ 2 * r + 1 - j ≤ i)) ∧
      (∀ i ≤ 2 * r, F i ⊓ span K {v, w} =
        span K {x | (x = v ∧ 1 ≤ i) ∨ (x = w ∧ 2 * r ≤ i)}) ∧
      (∀ i ≤ 2 * r, G i ⊓ span K {v, w} =
        span K {x | (x = v ∧ j ≤ i) ∨ (x = w ∧ 2 * r + 1 - j ≤ i)}) ∧
      j ≠ 2 * r + 1 - j ∧
      ∃ F' G' : ℕ → Submodule K (B.orthogonal (span K {v, w})),
        IsSelfDualFlag (B.restrict (B.orthogonal (span K {v, w}))) (r - 1) F' ∧
        IsSelfDualFlag (B.restrict (B.orthogonal (span K {v, w}))) (r - 1) G' ∧
        (∀ i ≤ 2 * r, ∃ m ≤ 2 * (r - 1),
          (F i).comap (B.orthogonal (span K {v, w})).subtype = F' m) ∧
        (∀ m ≤ 2 * (r - 1), ∃ i ≤ 2 * r,
          F' m = (F i).comap (B.orthogonal (span K {v, w})).subtype) ∧
        (∀ i ≤ 2 * r, ∃ m ≤ 2 * (r - 1),
          (G i).comap (B.orthogonal (span K {v, w})).subtype = G' m) ∧
        (∀ m ≤ 2 * (r - 1), ∃ i ≤ 2 * r,
          G' m = (G i).comap (B.orthogonal (span K {v, w})).subtype) := by
  classical
  have hFc := hF.isSelfDualChain
  have hGc := hG.isSelfDualChain
  have hr : 1 ≤ r := by
    by_contra hr0
    have : Subsingleton V := (Module.finrank_zero_iff (R := K)).mp (by omega)
    exact hv0 (Subsingleton.elim v 0)
  have hj1 : 1 ≤ j := by
    by_contra h0
    have : j = 0 := by omega
    rw [this, hGc.1, mem_bot] at hj
    exact hv0 hj
  have hjN : j ≤ 2 * r := by
    by_contra hlt
    exact hjmin (2 * r) (by omega) (by rw [hGc.top]; trivial)
  have hvj : v ∉ G (j - 1) := hjmin (j - 1) (by omega)
  set k := 2 * r + 1 - j with hk
  obtain ⟨f, hfG, hfe⟩ := exists_partner hGc hj1 hjN hvj
  set w := -f with hw
  have hvw : B v w = 1 := by rw [hw, map_neg, ← hB.neg_eq, neg_neg, hfe]
  have hwG : w ∈ G k := neg_mem hfG
  have hspan : span K {v, w} = span K {v, f} := by
    apply le_antisymm
    · rw [span_le]
      rintro x (rfl | rfl)
      · exact subset_span (Set.mem_insert _ _)
      · exact neg_mem (subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _)))
    · rw [span_le]
      rintro x (rfl | rfl)
      · exact subset_span (Set.mem_insert _ _)
      · have : -w ∈ span K {v, w} :=
          neg_mem (subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _)))
        rwa [hw, neg_neg] at this
  have hproj : ∀ x, x - B x w • v + B x v • w = x - B f x • v + B v x • f := by
    intro x
    have h1 : B x w = B f x := by rw [hw, map_neg, hB.neg_eq]
    have h2 : B x v = -B v x := (hB.neg_eq v x).symm
    rw [h1, h2, hw, smul_neg, neg_smul, neg_neg]
  have hbot : ∀ m < 1, F m = ⊥ := fun m hm => by rw [show m = 0 by omega, hFc.1]
  have hcF : IsPairCompatible B (2 * r) F v f := isPairCompatible_of_first hFc (by omega) hbot hv f
  have hcG : IsPairCompatible B (2 * r) G v f := isPairCompatible_of_least hGc hj1 hjN hj hfG
  have hwF : ∀ i ≤ 2 * r, w ∈ F i ↔ 2 * r ≤ i := by
    intro i hi
    refine ⟨fun hwi => ?_, fun h2 => by rw [show i = 2 * r by omega, hFc.top]; trivial⟩
    by_contra hlt
    have : w ∈ F (2 * r - 1) := hFc.le (by omega) (by omega) hwi
    rw [← show B.orthogonal (F 1) = F (2 * r - 1) from hF.2.2 1 (by omega)] at this
    have h0 := this v hv
    rw [hvw] at h0
    exact one_ne_zero h0
  have hvF : ∀ i ≤ 2 * r, v ∈ F i ↔ 1 ≤ i := by
    intro i hi
    refine ⟨fun hvi => ?_, fun h1 => hFc.le h1 hi hv⟩
    by_contra h0
    rw [show i = 0 by omega, hFc.1, mem_bot] at hvi
    exact hv0 hvi
  have hvG : ∀ i ≤ 2 * r, v ∈ G i ↔ j ≤ i := fun i hi =>
    ⟨fun hvi => by by_contra hlt; exact hjmin i (by omega) hvi, fun hji => hGc.le hji hi hj⟩
  have hwG' : ∀ i ≤ 2 * r, w ∈ G i ↔ k ≤ i := by
    intro i hi
    refine ⟨fun hwi => ?_, fun hki => hGc.le hki hi hwG⟩
    by_contra hlt
    have : w ∈ G (2 * r - j) := hGc.le (by omega) (by omega) hwi
    rw [← hG.2.2 j hjN] at this
    have h0 := this v hj
    rw [hvw] at h0
    exact one_ne_zero h0
  have hjk : j ≠ k := by omega
  set Z := B.orthogonal (span K {v, f}) with hZ
  have hZdim : finrank K Z = 2 * (r - 1) := by
    have h : finrank K Z + 2 = finrank K V := hB.finrank_orthogonal_span_pair_add_two hnd hfe
    omega
  have hndZ : (B.restrict Z).Nondegenerate := hB.restrict_nondegenerate_orthogonal_span_pair hfe hnd
  have hFZ := isSelfDualChain_comap hB hfe hFc hcF
  have hGZ := isSelfDualChain_comap hB hfe hGc hcG
  have hfF : ∀ i ≤ 2 * r, f ∈ F i ↔ 2 * r ≤ i := fun i hi => by
    rw [← hwF i hi, hw, neg_mem_iff]
  have hfG' : ∀ i ≤ 2 * r, f ∈ G i ↔ k ≤ i := fun i hi => by
    rw [← hwG' i hi, hw, neg_mem_iff]
  have hdimF : ∀ i ≤ 2 * r, finrank K ((F i).comap Z.subtype) + (if 1 ≤ i then 1 else 0) +
      (if 2 * r ≤ i then 1 else 0) = i := by
    intro i hi
    have := finrank_comap_add hB hfe hcF hi
    rw [hF.1 i hi, if_congr (hvF i hi) rfl rfl, if_congr (hfF i hi) rfl rfl] at this
    exact this
  have hdimG : ∀ i ≤ 2 * r, finrank K ((G i).comap Z.subtype) + (if j ≤ i then 1 else 0) +
      (if k ≤ i then 1 else 0) = i := by
    intro i hi
    have := finrank_comap_add hB hfe hcG hi
    rw [hG.1 i hi, if_congr (hvG i hi) rfl rfl, if_congr (hfG' i hi) rfl rfl] at this
    exact this
  have hchainF : ∀ {a b : ℕ}, a ≤ b → b ≤ 2 * r →
      (F a).comap Z.subtype ≤ (F b).comap Z.subtype := fun hab hb => hFZ.le hab hb
  have hchainG : ∀ {a b : ℕ}, a ≤ b → b ≤ 2 * r →
      (G a).comap Z.subtype ≤ (G b).comap Z.subtype := fun hab hb => hGZ.le hab hb
  have hfinZ : ∀ X : Submodule K Z,
      finrank K ((B.restrict Z).orthogonal X) = 2 * (r - 1) - finrank K X := fun X => by
    rw [BilinForm.finrank_orthogonal hndZ, hZdim]
  set F' : ℕ → Submodule K Z := fun m => (F (m + 1)).comap Z.subtype with hF'
  set G' : ℕ → Submodule K Z := fun m => (G (skipTwo j k m)).comap Z.subtype with hG'
  have hskip : ∀ m ≤ 2 * (r - 1), skipTwo j k m ≤ 2 * r ∧
      finrank K (G' m) = m := by
    intro m hm
    have hle : skipTwo j k m ≤ 2 * r := by unfold skipTwo; split_ifs <;> omega
    refine ⟨hle, ?_⟩
    have h := hdimG _ hle
    have hge : m ≤ skipTwo j k m := by unfold skipTwo; split_ifs <;> omega
    have hval : (if j ≤ skipTwo j k m then 1 else 0) + (if k ≤ skipTwo j k m then 1 else 0) =
        skipTwo j k m - m := by
      unfold skipTwo
      split_ifs <;> omega
    change finrank K ((G (skipTwo j k m)).comap Z.subtype) = m
    omega
  have hskip_mono : ∀ {m m' : ℕ}, m ≤ m' → skipTwo j k m ≤ skipTwo j k m' := by
    intro m m' h
    unfold skipTwo
    split_ifs <;> omega
  have hF'flag : IsSelfDualFlag (B.restrict Z) (r - 1) F' := by
    refine ⟨fun m hm => ?_, fun m hm => hchainF (by omega) (by omega), fun m hm => ?_⟩
    · have := hdimF (m + 1) (by omega)
      change finrank K ((F (m + 1)).comap Z.subtype) = m
      split_ifs at this <;> omega
    · change (B.restrict Z).orthogonal ((F (m + 1)).comap Z.subtype) =
        (F (2 * (r - 1) - m + 1)).comap Z.subtype
      rw [hFZ.2.2 (m + 1) (by omega), show 2 * r - (m + 1) = 2 * (r - 1) - m + 1 by omega]
  have hG'flag : IsSelfDualFlag (B.restrict Z) (r - 1) G' := by
    refine ⟨fun m hm => (hskip m hm).2, fun m hm => hchainG (hskip_mono (Nat.le_succ m))
      (hskip (m + 1) (by omega)).1, fun m hm => ?_⟩
    change (B.restrict Z).orthogonal ((G (skipTwo j k m)).comap Z.subtype) =
      (G (skipTwo j k (2 * (r - 1) - m))).comap Z.subtype
    have h1 := hGZ.2.2 (skipTwo j k m) (hskip m hm).1
    rw [h1]
    refine eq_of_finrank_eq_of_chain hchainG (Nat.sub_le _ _)
      (hskip (2 * (r - 1) - m) (Nat.sub_le _ _)).1 ?_
    have h2 := hfinZ ((G (skipTwo j k m)).comap Z.subtype)
    rw [h1, (hskip m hm).2] at h2
    rw [h2]
    exact ((hskip (2 * (r - 1) - m) (Nat.sub_le _ _)).2).symm
  refine ⟨w, hwG, hvw, fun x => ?_, fun x hx => ?_, fun i hi x hx => ?_, fun i hi x hx => ?_,
    ?_, fun i hi => ?_, fun i hi => ?_, fun i hi => ⟨hvF i hi, hwF i hi⟩,
    fun i hi => ⟨hvG i hi, hwG' i hi⟩, fun i hi => ?_, fun i hi => ?_, hjk, ?_⟩
  · rw [hspan, hproj]
    exact proj_mem_orthogonal hB hfe x
  · rw [hspan] at hx
    obtain ⟨h1, h2⟩ := (BilinForm.mem_orthogonal_span_pair_iff B).mp hx
    rw [hproj, h2, h1]
    simp
  · rw [hproj]
    exact hcF.proj_mem hi hx
  · rw [hproj]
    exact hcG.proj_mem hi hx
  · rw [hspan]
    exact span_pair_inf_orthogonal hB hfe
  · rw [hspan]
    exact hcF.sup_eq hB hfe hi
  · rw [hspan]
    exact hcG.sup_eq hB hfe hi
  · refine le_antisymm ?_ (le_inf (span_le.mpr ?_) (span_le.mpr ?_))
    · rw [hspan]
      refine (hcF.inf_span_pair_le hB hfe hi).trans (span_le.mpr ?_)
      rintro x (⟨rfl, hx⟩ | ⟨rfl, hx⟩)
      · exact subset_span (Or.inl ⟨rfl, (hvF i hi).mp hx⟩)
      · have : -w ∈ span K {x | (x = v ∧ 1 ≤ i) ∨ (x = w ∧ 2 * r ≤ i)} :=
          neg_mem (subset_span (Or.inr ⟨rfl, (hfF i hi).mp hx⟩))
        rwa [hw, neg_neg] at this
    · rintro x (⟨rfl, h1⟩ | ⟨rfl, h2⟩)
      · exact (hvF i hi).mpr h1
      · exact (hwF i hi).mpr h2
    · rintro x (⟨rfl, -⟩ | ⟨rfl, -⟩)
      · exact subset_span (by simp)
      · exact subset_span (by simp)
  · refine le_antisymm ?_ (le_inf (span_le.mpr ?_) (span_le.mpr ?_))
    · rw [hspan]
      refine (hcG.inf_span_pair_le hB hfe hi).trans (span_le.mpr ?_)
      rintro x (⟨rfl, hx⟩ | ⟨rfl, hx⟩)
      · exact subset_span (Or.inl ⟨rfl, (hvG i hi).mp hx⟩)
      · have : -w ∈ span K {x | (x = v ∧ j ≤ i) ∨ (x = w ∧ 2 * r + 1 - j ≤ i)} :=
          neg_mem (subset_span (Or.inr ⟨rfl, (hfG' i hi).mp hx⟩))
        rwa [hw, neg_neg] at this
    · rintro x (⟨rfl, h1⟩ | ⟨rfl, h2⟩)
      · exact (hvG i hi).mpr h1
      · exact (hwG' i hi).mpr h2
    · rintro x (⟨rfl, -⟩ | ⟨rfl, -⟩)
      · exact subset_span (by simp)
      · exact subset_span (by simp)
  · rw [hspan]
    refine ⟨F', G', hF'flag, hG'flag, fun i hi => ?_, fun m hm => ⟨m + 1, by omega, rfl⟩,
      fun i hi => ?_, fun m hm => ⟨skipTwo j k m, (hskip m hm).1, rfl⟩⟩
    ·
      set d := finrank K ((F i).comap Z.subtype)
      have h2 := hdimF i hi
      have hd : d ≤ 2 * (r - 1) := by
        by_cases h1 : 1 ≤ i
        · rw [ite_eq_left h1] at h2
          by_cases h3 : 2 * r ≤ i
          · rw [ite_eq_left h3] at h2
            omega
          · rw [ite_eq_right h3] at h2
            omega
        · rw [ite_eq_right h1, ite_eq_right (by omega : ¬2 * r ≤ i)] at h2
          omega
      refine ⟨d, hd, eq_of_finrank_eq_of_chain hchainF hi (by omega) ?_⟩
      have h4 := hdimF (d + 1) (by omega)
      rw [ite_eq_left (by omega : 1 ≤ d + 1), ite_eq_right (by omega : ¬2 * r ≤ d + 1)] at h4
      omega
    · set d := finrank K ((G i).comap Z.subtype)
      have h2 := hdimG i hi
      have hd : d ≤ 2 * (r - 1) := by
        by_cases hj' : j ≤ i <;> by_cases hk' : k ≤ i
        · rw [ite_eq_left hj', ite_eq_left hk'] at h2
          omega
        · rw [ite_eq_left hj', ite_eq_right hk'] at h2
          omega
        · rw [ite_eq_right hj', ite_eq_left hk'] at h2
          omega
        · rw [ite_eq_right hj', ite_eq_right hk'] at h2
          omega
      refine ⟨d, hd, eq_of_finrank_eq_of_chain hchainG hi (hskip d hd).1 ?_⟩
      exact ((hskip d hd).2).symm

end CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
