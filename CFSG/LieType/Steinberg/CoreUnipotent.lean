module

public import CFSG.LieType.Steinberg.CoreBasic
import Mathlib.Tactic.Linarith

public noncomputable section

namespace CFSG.LieType.Steinberg

open scoped commutatorElement

theorem ne_single_of_one_lt_ht {ι : Type*} [Fintype ι] [DecidableEq ι] {i : ι} {γ : ι → ℤ}
    (h : 1 < ht γ) : γ ≠ Pi.single i 1 := by
  rintro rfl
  rw [ht_single] at h
  exact lt_irrefl _ h

namespace RootSystem

variable {ι : Type*} [Fintype ι] [DecidableEq ι] (Φ : RootSystem ι)

theorem mem_pos_of_two_smul_mem_pos {δ : ι → ℤ} (h : 2 • δ ∈ Φ.pos) (hδ : δ ∈ Φ.roots) :
    δ ∈ Φ.pos := by
  refine ⟨hδ, ?_⟩
  have h1 := h.2
  rw [ht_two_smul] at h1
  linarith

theorem mem_posExcept_of_two_smul_mem {i : ι} {δ : ι → ℤ} (h : 2 • δ ∈ Φ.posExcept i)
    (hδ : δ ∈ Φ.roots) : δ ∈ Φ.posExcept i := by
  obtain ⟨hp, hne⟩ := h
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hne
  refine ⟨Φ.mem_pos_of_two_smul_mem_pos hp hδ, ?_⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
  refine ⟨fun h => hne.2 (by rw [h]), fun h => ?_⟩
  exact Φ.isIndiv_of_two_smul_mem hp.1 _ (Φ.single_mem i) h

theorem mem_negExcept_of_two_smul_mem {i : ι} {δ : ι → ℤ} (h : 2 • δ ∈ Φ.negExcept i)
    (hδ : δ ∈ Φ.roots) : -δ ∈ Φ.posExcept i := by
  refine Φ.mem_posExcept_of_two_smul_mem ?_ (Φ.neg_mem δ hδ)
  rw [neg_nsmul, neg_mem_posExcept_iff]
  exact h

theorem refl_mem_posExcept_iff {i : ι} {γ : ι → ℤ} :
    γ ∈ Φ.posExcept i ↔ Φ.refl i γ ∈ Φ.posExcept i :=
  ⟨Φ.refl_mem_posExcept, fun h => by simpa [Φ.refl_refl] using Φ.refl_mem_posExcept h⟩

theorem refl_mem_negExcept_iff {i : ι} {γ : ι → ℤ} :
    γ ∈ Φ.negExcept i ↔ Φ.refl i γ ∈ Φ.negExcept i :=
  ⟨Φ.refl_mem_negExcept, fun h => by simpa [Φ.refl_refl] using Φ.refl_mem_negExcept h⟩

theorem notMem_posExcept_negExcept {i : ι} {γ : ι → ℤ}
    (h : γ = Pi.single i 1 ∨ γ = -Pi.single i 1 ∨ γ = 2 • Pi.single i 1 ∨
      γ = -(2 • Pi.single i 1)) : γ ∉ Φ.posExcept i ∧ γ ∉ Φ.negExcept i := by
  have hpos : ∀ v : ι → ℤ, 0 < ht v → v ∉ Φ.negExcept i := fun v hv hn =>
    absurd hn.1.2 (not_lt.2 hv.le)
  have hneg : ∀ v : ι → ℤ, ht v < 0 → v ∉ Φ.posExcept i := fun v hv hp =>
    absurd hp.1.2 (not_lt.2 hv.le)
  rcases h with rfl | rfl | rfl | rfl
  · exact ⟨fun h => h.2 (Or.inl rfl), hpos _ (by rw [ht_single]; exact one_pos)⟩
  · exact ⟨hneg _ (by rw [ht_neg, ht_single]; exact neg_one_lt_zero), fun h => h.2 (Or.inl rfl)⟩
  · exact ⟨fun h => h.2 (Or.inr rfl), hpos _ (by rw [ht_two_smul, ht_single]; norm_num)⟩
  · exact ⟨hneg _ (by rw [ht_neg, ht_two_smul, ht_single]; norm_num), fun h => h.2 (Or.inr rfl)⟩

end RootSystem

namespace RootGroupData

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {Φ : RootSystem ι} {K : Type*} [Group K]
variable {D : RootGroupData Φ K}

theorem ProdInjective.filter {L : List (ι → ℤ)} (hL : D.ProdInjective L) (p : (ι → ℤ) → Bool) :
    D.ProdInjective (L.filter p) := by
  intro f g hf hg hfg γ hγ
  have hprod : ∀ (u : (ι → ℤ) → K) (M : List (ι → ℤ)),
      (M.map fun γ => if p γ then u γ else 1).prod = ((M.filter p).map u).prod := by
    intro u M
    induction M with
    | nil => rfl
    | cons a M ih => by_cases ha : p a <;> simp [ha, ih]
  have hmem : ∀ u : (ι → ℤ) → K, (∀ γ ∈ L.filter p, u γ ∈ D.X γ) →
      ∀ γ ∈ L, (fun γ => if p γ then u γ else 1) γ ∈ D.X γ := by
    intro u hu γ hγL
    by_cases hp : p γ
    · simpa [hp] using hu γ (List.mem_filter.2 ⟨hγL, hp⟩)
    · simp [hp]
  have := hL _ _ (hmem f hf) (hmem g hg) (by rw [hprod f L, hprod g L]; exact hfg) γ
    (List.mem_of_mem_filter hγ)
  simpa [(List.mem_filter.1 hγ).2] using this

theorem injOn_iSup_stRoot_of_list {L : List (ι → ℤ)} {h : (ι → ℤ) → ℤ} (hnd : L.Nodup)
    (hr : ∀ γ ∈ L, γ ∈ Φ.roots) (hs : L.Pairwise fun a b => h a ≤ h b)
    (hinj : D.ProdInjective L)
    (hc : ∀ a ∈ L, ∀ b ∈ L, a ≠ b → ∀ x ∈ D.stRoot a, ∀ y ∈ D.stRoot b,
      ⁅x, y⁆ ∈ ⨆ c ∈ L, ⨆ (_ : min (h a) (h b) < h c), D.stRoot c) :
    Set.InjOn (stPi Φ D.X) (⨆ γ ∈ L, D.stRoot γ : Subgroup (StGroup Φ D.X)) := by
  refine injOn_of_eq_one fun g hg h1 => ?_
  obtain ⟨f, hf, rfl⟩ := exists_prod_eq_of_commutator_mem D.stRoot h hnd hs hc g hg
  have h1' : (L.map (stPi Φ D.X ∘ f)).prod = (L.map fun _ => (1 : K)).prod := by
    rw [← List.map_map, ← map_list_prod, h1]
    simp
  have key := hinj _ _ (fun γ hγ => D.stPi_mem_X (hr γ hγ) (hf γ hγ)) (fun γ _ => one_mem _) h1'
  refine List.prod_eq_one fun x hx => ?_
  obtain ⟨γ, hγ, rfl⟩ := List.mem_map.1 hx
  refine D.injOn_stRoot (hr γ hγ) (hf γ hγ) (one_mem _) ?_
  rw [map_one]
  exact key γ hγ

namespace IsSteinberg

variable (hD : D.IsSteinberg)
include hD

theorem commutator_mem_of_cone {L : List (ι → ℤ)} {h : (ι → ℤ) → ℤ}
    (hr : ∀ γ ∈ L, γ ∈ Φ.roots) (hlin : ∀ a ∈ L, ∀ b ∈ L, a ≠ b → LinIndepPair a b)
    (hcone : ∀ a ∈ L, ∀ b ∈ L, a ≠ b → ∀ ε ∈ openCone Φ.roots a b,
      ∃ c ∈ L, min (h a) (h b) < h c ∧ (c = ε ∨ ε = 2 • c)) :
    ∀ a ∈ L, ∀ b ∈ L, a ≠ b → ∀ x ∈ D.stRoot a, ∀ y ∈ D.stRoot b,
      ⁅x, y⁆ ∈ ⨆ c ∈ L, ⨆ (_ : min (h a) (h b) < h c), D.stRoot c := by
  intro a ha b hb hab x hx y hy
  have hxy := hD.commutator_mem_stSub (hr a ha) (hr b hb) (hlin a ha b hb hab) hx hy
  rw [stSub_eq_iSup] at hxy
  have hle : ⨆ ε ∈ openCone Φ.roots a b, D.stRoot ε ≤
      ⨆ c ∈ L, ⨆ (_ : min (h a) (h b) < h c), D.stRoot c := by
    refine iSup₂_le fun ε hε => ?_
    obtain ⟨c, hc, hlt, hcε⟩ := hcone a ha b hb hab ε hε
    have : D.stRoot ε ≤ D.stRoot c := by
      rcases hcε with rfl | rfl
      · exact le_rfl
      · exact hD.stRoot_two_smul_le (hr c hc) hε.1
    exact this.trans (le_iSup₂_of_le c hc (le_iSup_of_le hlt le_rfl))
  exact hle hxy

theorem stSub_eq_iSup_list {P : Set (ι → ℤ)} (hP : P ⊆ Φ.roots)
    (hhalf : ∀ δ ∈ Φ.roots, 2 • δ ∈ P → δ ∈ P) {L : List (ι → ℤ)}
    (hL : ∀ γ, γ ∈ L ↔ γ ∈ P ∧ Φ.IsIndiv γ) : D.stSub P = ⨆ γ ∈ L, D.stRoot γ := by
  rw [stSub_eq_iSup]
  apply le_antisymm
  · refine iSup₂_le fun γ hγ => ?_
    by_cases hind : Φ.IsIndiv γ
    · exact le_iSup₂ (f := fun γ (_ : γ ∈ L) => D.stRoot γ) γ ((hL γ).2 ⟨hγ, hind⟩)
    · obtain ⟨δ, hδ, hδ', rfl⟩ := Φ.exists_eq_two_smul (hP hγ) hind
      exact (hD.stRoot_two_smul_le hδ (hP hγ)).trans
        (le_iSup₂ (f := fun γ (_ : γ ∈ L) => D.stRoot γ) δ ((hL δ).2 ⟨hhalf δ hδ hγ, hδ'⟩))
  · exact iSup₂_le fun γ hγ => le_iSup₂ (f := fun γ (_ : γ ∈ P) => D.stRoot γ) γ ((hL γ).1 hγ).1

theorem injOn_stSub_pos : Set.InjOn (stPi Φ D.X) (D.stSub Φ.pos) := by
  obtain ⟨L, hnd, hL, hs, hinj⟩ := hD.exists_posList
  have hr : ∀ γ ∈ L, γ ∈ Φ.roots := fun γ hγ => ((hL γ).1 hγ).1.1
  rw [hD.stSub_eq_iSup_list (fun γ hγ => hγ.1)
    (fun δ hδ h => Φ.mem_pos_of_two_smul_mem_pos h hδ) hL]
  refine injOn_iSup_stRoot_of_list hnd hr hs hinj (hD.commutator_mem_of_cone hr ?_ ?_)
  · intro a ha b hb hab
    exact Φ.linIndepPair_of_mem_pos ((hL a).1 ha).1 ((hL a).1 ha).2 ((hL b).1 hb).1
      ((hL b).1 hb).2 hab
  · intro a ha b hb hab ε hε
    obtain ⟨c, hc, hlt, hcε⟩ := Φ.exists_of_mem_openCone_pos ((hL a).1 ha).1 ((hL a).1 ha).2
      ((hL b).1 hb).1 ((hL b).1 hb).2 hab hε
    exact ⟨c, (hL c).2 hc, hlt, hcε⟩

theorem injOn_stSub_posExcept (i : ι) :
    Set.InjOn (stPi Φ D.X) (D.stSub (Φ.posExcept i)) := by
  obtain ⟨L, hnd, hL, hs, hinj⟩ := hD.exists_posList
  set L' := L.filter fun γ => γ ≠ Pi.single i 1
  have hL' : ∀ γ, γ ∈ L' ↔ γ ∈ Φ.posExcept i ∧ Φ.IsIndiv γ := by
    intro γ
    simp only [L', List.mem_filter, hL, decide_eq_true_eq, RootSystem.posExcept, Set.mem_sdiff,
      Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    constructor
    · rintro ⟨⟨hp, hind⟩, hne⟩
      exact ⟨⟨hp, hne, fun h => hind _ (Φ.single_mem i) h⟩, hind⟩
    · rintro ⟨⟨hp, hne, -⟩, hind⟩
      exact ⟨⟨hp, hind⟩, hne⟩
  have hr : ∀ γ ∈ L', γ ∈ Φ.roots := fun γ hγ => ((hL' γ).1 hγ).1.1.1
  rw [hD.stSub_eq_iSup_list (fun γ hγ => hγ.1.1)
    (fun δ hδ h => Φ.mem_posExcept_of_two_smul_mem h hδ) hL']
  refine injOn_iSup_stRoot_of_list (hnd.filter _) hr (hs.filter _) (hinj.filter _)
    (hD.commutator_mem_of_cone hr ?_ ?_)
  · intro a ha b hb hab
    exact Φ.linIndepPair_of_mem_pos ((hL' a).1 ha).1.1 ((hL' a).1 ha).2 ((hL' b).1 hb).1.1
      ((hL' b).1 hb).2 hab
  · intro a ha b hb hab ε hε
    have ha' := (hL' a).1 ha
    have hb' := (hL' b).1 hb
    obtain ⟨c, ⟨hc, hc'⟩, hlt, hcε⟩ := Φ.exists_of_mem_openCone_pos ha'.1.1 ha'.2 hb'.1.1 hb'.2
      hab hε
    have h1 : 1 < ht c := lt_of_le_of_lt (le_min ha'.1.1.2 hb'.1.1.2) hlt
    refine ⟨c, (hL' c).2 ⟨⟨hc, ?_⟩, hc'⟩, hlt, hcε⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨ne_single_of_one_lt_ht h1, fun h => hc' _ (Φ.single_mem i) h⟩

theorem injOn_stSub_negExcept (i : ι) :
    Set.InjOn (stPi Φ D.X) (D.stSub (Φ.negExcept i)) := by
  obtain ⟨L, hnd, hL, hs, hinj⟩ := hD.exists_negList
  set L' := L.filter fun γ => γ ≠ -Pi.single i 1
  have hL' : ∀ γ, γ ∈ L' ↔ γ ∈ Φ.negExcept i ∧ Φ.IsIndiv γ := by
    intro γ
    simp only [L', List.mem_filter, hL, decide_eq_true_eq, RootSystem.negExcept, Set.mem_sdiff,
      Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    constructor
    · rintro ⟨⟨hp, hind⟩, hne⟩
      refine ⟨⟨hp, hne, fun h => hind _ (Φ.neg_mem _ (Φ.single_mem i)) ?_⟩, hind⟩
      rw [h, neg_nsmul]
    · rintro ⟨⟨hp, hne, -⟩, hind⟩
      exact ⟨⟨hp, hind⟩, hne⟩
  have hr : ∀ γ ∈ L', γ ∈ Φ.roots := fun γ hγ => ((hL' γ).1 hγ).1.1.1
  have hhalf : ∀ δ ∈ Φ.roots, 2 • δ ∈ Φ.negExcept i → δ ∈ Φ.negExcept i := fun δ hδ h => by
    simpa using Φ.neg_mem_posExcept_iff.1 (by simpa using Φ.mem_negExcept_of_two_smul_mem h hδ)
  rw [hD.stSub_eq_iSup_list (fun γ hγ => hγ.1.1) hhalf hL']
  refine injOn_iSup_stRoot_of_list (h := fun γ => -ht γ) (hnd.filter _) hr
    ((hs.imp fun h => neg_le_neg h).filter _) (hinj.filter _)
    (hD.commutator_mem_of_cone hr ?_ ?_)
  · intro a ha b hb hab
    exact Φ.linIndepPair_of_mem_neg ((hL' a).1 ha).1.1 ((hL' a).1 ha).2 ((hL' b).1 hb).1.1
      ((hL' b).1 hb).2 hab
  · intro a ha b hb hab ε hε
    have ha' := (hL' a).1 ha
    have hb' := (hL' b).1 hb
    obtain ⟨c, ⟨hc, hc'⟩, hlt, hcε⟩ := Φ.exists_of_mem_openCone_neg ha'.1.1 ha'.2 hb'.1.1 hb'.2
      hab hε
    have ha1 : 1 ≤ -ht a := by have := ha'.1.1.2; linarith
    have hb1 : 1 ≤ -ht b := by have := hb'.1.1.2; linarith
    have h1 : 1 < -ht c := lt_of_le_of_lt (le_min ha1 hb1) hlt
    refine ⟨c, (hL' c).2 ⟨⟨hc, ?_⟩, hc'⟩, hlt, hcε⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    refine ⟨fun h => ?_, fun h => hc' _ (Φ.neg_mem _ (Φ.single_mem i)) (by rw [h, neg_nsmul])⟩
    rw [h, ht_neg, ht_single, neg_neg] at h1
    exact lt_irrefl _ h1

omit hD in
theorem _root_.CFSG.LieType.Steinberg.RootGroupData.le_normalizer_stSub
    {A : Subgroup (StGroup Φ D.X)} {P : Set (ι → ℤ)}
    (h : ∀ x ∈ A, ∀ γ ∈ P, ∀ y ∈ D.stRoot γ, x * y * x⁻¹ ∈ D.stSub P) :
    A ≤ Subgroup.normalizer (D.stSub P : Set (StGroup Φ D.X)) := by
  refine le_normalizer_of_map_conj_le fun x hx => ?_
  conv_lhs => rw [stSub_eq_iSup]
  simp only [Subgroup.map_iSup]
  exact iSup₂_le fun γ hγ => map_conj_le_iff.2 fun y hy => h x hx γ hγ y hy

omit hD in
theorem _root_.CFSG.LieType.Steinberg.RootGroupData.le_normalizer_stSub_of_le
    {A : Subgroup (StGroup Φ D.X)} {P : Set (ι → ℤ)}
    (h : ∀ γ ∈ P, A ≤ Subgroup.normalizer (D.stRoot γ : Set (StGroup Φ D.X))) :
    A ≤ Subgroup.normalizer (D.stSub P : Set (StGroup Φ D.X)) := by
  rw [stSub_eq_iSup]
  exact le_normalizer_iSup fun γ => le_normalizer_iSup fun hγ => h γ hγ

theorem stRoot_le_normalizer_posExcept {i : ι} {s : ι → ℤ}
    (hs : s = Pi.single i 1 ∨ s = -Pi.single i 1) :
    D.stRoot s ≤ Subgroup.normalizer (D.stSub (Φ.posExcept i) : Set (StGroup Φ D.X)) := by
  have hsr : s ∈ Φ.roots := by
    rcases hs with rfl | rfl
    · exact Φ.single_mem i
    · exact Φ.neg_mem _ (Φ.single_mem i)
  refine le_normalizer_stSub fun x hx γ hγ y hy => ?_
  have h1 : ⁅x, y⁆ ∈ D.stSub (Φ.posExcept i) := D.stSub_mono (Φ.openCone_subset_posExcept hs hγ)
    (hD.commutator_mem_stSub hsr hγ.1.1 (Φ.linIndepPair_of_mem_posExcept hs hγ) hx hy)
  have := Subgroup.mul_mem _ h1 (D.stRoot_le_stSub hγ hy)
  rwa [commutatorElement_def, inv_mul_cancel_right] at this

theorem stRoot_le_normalizer_negExcept {i : ι} {s : ι → ℤ}
    (hs : s = Pi.single i 1 ∨ s = -Pi.single i 1) :
    D.stRoot s ≤ Subgroup.normalizer (D.stSub (Φ.negExcept i) : Set (StGroup Φ D.X)) := by
  have hsr : s ∈ Φ.roots := by
    rcases hs with rfl | rfl
    · exact Φ.single_mem i
    · exact Φ.neg_mem _ (Φ.single_mem i)
  refine le_normalizer_stSub fun x hx γ hγ y hy => ?_
  have h1 : ⁅x, y⁆ ∈ D.stSub (Φ.negExcept i) := D.stSub_mono (Φ.openCone_subset_negExcept hs hγ)
    (hD.commutator_mem_stSub hsr hγ.1.1 (Φ.linIndepPair_of_mem_negExcept hs hγ) hx hy)
  have := Subgroup.mul_mem _ h1 (D.stRoot_le_stSub hγ hy)
  rwa [commutatorElement_def, inv_mul_cancel_right] at this

theorem stRankOne_le_normalizer_posExcept (i : ι) :
    D.stRankOne i ≤ Subgroup.normalizer (D.stSub (Φ.posExcept i) : Set (StGroup Φ D.X)) :=
  sup_le (hD.stRoot_le_normalizer_posExcept (Or.inl rfl))
    (hD.stRoot_le_normalizer_posExcept (Or.inr rfl))

theorem stRankOne_le_normalizer_negExcept (i : ι) :
    D.stRankOne i ≤ Subgroup.normalizer (D.stSub (Φ.negExcept i) : Set (StGroup Φ D.X)) :=
  sup_le (hD.stRoot_le_normalizer_negExcept (Or.inl rfl))
    (hD.stRoot_le_normalizer_negExcept (Or.inr rfl))

theorem stRoot_le_stRankOne {i : ι} {γ : ι → ℤ} (hγ : γ ∈ Φ.roots)
    (h : γ = Pi.single i 1 ∨ γ = -Pi.single i 1 ∨ γ = 2 • Pi.single i 1 ∨
      γ = -(2 • Pi.single i 1)) : D.stRoot γ ≤ D.stRankOne i := by
  rcases h with rfl | rfl | rfl | rfl
  · exact D.stRoot_single_le_stRankOne i
  · exact D.stRoot_neg_single_le_stRankOne i
  · exact (hD.stRoot_two_smul_le (Φ.single_mem i) hγ).trans (D.stRoot_single_le_stRankOne i)
  · rw [← neg_nsmul] at hγ ⊢
    exact (hD.stRoot_two_smul_le (Φ.neg_mem _ (Φ.single_mem i)) hγ).trans
      (D.stRoot_neg_single_le_stRankOne i)

theorem map_conj_stRoot_eq {i : ι} {g : StGroup Φ D.X} (hg : g ∈ D.stRankOne i)
    {γ δ : ι → ℤ} (hγ : γ ∈ Φ.roots) (hδ : δ ∈ Φ.roots)
    (hpos : γ ∈ Φ.posExcept i ↔ δ ∈ Φ.posExcept i) (hneg : γ ∈ Φ.negExcept i ↔ δ ∈ Φ.negExcept i)
    (hK : (D.X γ).map (MulAut.conj (stPi Φ D.X g)).toMonoidHom = D.X δ) :
    (D.stRoot γ).map (MulAut.conj g).toMonoidHom = D.stRoot δ := by
  have key : ∀ M : Subgroup (StGroup Φ D.X), Set.InjOn (stPi Φ D.X) M →
      D.stRankOne i ≤ Subgroup.normalizer (M : Set (StGroup Φ D.X)) → D.stRoot γ ≤ M →
      D.stRoot δ ≤ M → (D.stRoot γ).map (MulAut.conj g).toMonoidHom = D.stRoot δ := by
    intro M hM hnorm hγM hδM
    refine eq_of_injOn hM ((Subgroup.map_mono hγM).trans
      (mem_normalizer_iff_map_conj.1 (hnorm hg)).le) hδM ?_
    rw [map_map_conj, D.map_stRoot hγ, hK, D.map_stRoot hδ]
  rcases Φ.mem_cases i hγ with hE | hP | hN
  · have hδE : δ = Pi.single i 1 ∨ δ = -Pi.single i 1 ∨ δ = 2 • Pi.single i 1 ∨
        δ = -(2 • Pi.single i 1) := by
      rcases Φ.mem_cases i hδ with hδE | hδP | hδN
      · exact hδE
      · exact absurd (hpos.2 hδP) (Φ.notMem_posExcept_negExcept hE).1
      · exact absurd (hneg.2 hδN) (Φ.notMem_posExcept_negExcept hE).2
    exact key _ (D.injOn_stRankOne i) (Subgroup.le_normalizer) (hD.stRoot_le_stRankOne hγ hE)
      (hD.stRoot_le_stRankOne hδ hδE)
  · exact key _ (hD.injOn_stSub_posExcept i) (hD.stRankOne_le_normalizer_posExcept i)
      (D.stRoot_le_stSub hP) (D.stRoot_le_stSub (hpos.1 hP))
  · exact key _ (hD.injOn_stSub_negExcept i) (hD.stRankOne_le_normalizer_negExcept i)
      (D.stRoot_le_stSub hN) (D.stRoot_le_stSub (hneg.1 hN))

theorem map_conj_stn_stRoot (i : ι) {γ : ι → ℤ} (hγ : γ ∈ Φ.roots) :
    (D.stRoot γ).map (MulAut.conj (D.stn i)).toMonoidHom = D.stRoot (Φ.refl i γ) :=
  hD.map_conj_stRoot_eq (hD.stn_mem i) hγ (Φ.refl_mem i γ hγ) Φ.refl_mem_posExcept_iff
    Φ.refl_mem_negExcept_iff (by rw [hD.stPi_stn]; exact hD.map_conj_n i γ hγ)

theorem map_conj_stnw_stRoot (w : List ι) {γ : ι → ℤ} (hγ : γ ∈ Φ.roots) :
    (D.stRoot γ).map (MulAut.conj (D.stnw w)).toMonoidHom = D.stRoot (wordAct Φ.refl w γ) := by
  induction w with
  | nil => rw [stnw_nil, map_conj_one, wordAct_nil]
  | cons i w ih =>
    rw [stnw_cons, map_conj_mul, ih, hD.map_conj_stn_stRoot i (Φ.wordAct_mem w hγ), wordAct_cons]

theorem stPi_stnw (w : List ι) : stPi Φ D.X (D.stnw w) = (w.map D.n).prod := by
  rw [stnw, map_list_prod, List.map_map]
  exact congrArg List.prod (List.map_congr_left fun i _ => hD.stPi_stn i)

theorem map_conj_stPi_stnw (w : List ι) {γ : ι → ℤ} (hγ : γ ∈ Φ.roots) :
    (D.X γ).map (MulAut.conj (stPi Φ D.X (D.stnw w))).toMonoidHom =
      D.X (wordAct Φ.refl w γ) := by
  rw [← D.map_stRoot hγ, ← map_map_conj, hD.map_conj_stnw_stRoot w hγ,
    D.map_stRoot (Φ.wordAct_mem w hγ)]

end IsSteinberg

end RootGroupData

end CFSG.LieType.Steinberg
