module

public import CFSG.LocalAnalysis.ComponentInitial.SymplecticHigherFlagSplitting
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticFlagTriangular

public noncomputable section

namespace CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher

open Module Submodule SymplecticFlag
open LinearMap (BilinForm)

universe u

variable {K : Type*} [Field K]

theorem flagOrder_succ_inl_zero (m : ℕ) : (flagOrder (m + 1) (Sum.inl 0) : ℕ) = 0 := by
  rw [flagOrder_inl]
  rfl

theorem flagOrder_succ_inr_zero (m : ℕ) : (flagOrder (m + 1) (Sum.inr 0) : ℕ) = 2 * m + 1 := by
  rw [flagOrder_inr]
  simp
  omega

theorem flagOrder_succ_inl_succ (m : ℕ) (y : Fin m) :
    (flagOrder (m + 1) (Sum.inl y.succ) : ℕ) = flagOrder m (Sum.inl y) + 1 := by
  rw [flagOrder_inl, flagOrder_inl, Fin.val_succ]

theorem flagOrder_succ_inr_succ (m : ℕ) (y : Fin m) :
    (flagOrder (m + 1) (Sum.inr y.succ) : ℕ) = flagOrder m (Sum.inr y) + 1 := by
  rw [flagOrder_inr, flagOrder_inr, Fin.val_succ]
  have := y.2
  omega

theorem exists_common_basis_aux (m : ℕ) :
    ∀ {V : Type u} [AddCommGroup V] [Module K V] [FiniteDimensional K V] (B : BilinForm K V),
      B.IsAlt → B.Nondegenerate → finrank K V = 2 * m →
      ∀ (N : ℕ) (F : ℕ → Submodule K V) (N' : ℕ) (G : ℕ → Submodule K V),
        IsSelfDualChain B N F → IsSelfDualChain B N' G →
        ∃ b : Basis (Fin m ⊕ Fin m) K V, (∀ x y, B (b x) (b y) = Matrix.J (Fin m) K x y) ∧
          (∀ i ≤ N, ∀ x, (flagOrder m x : ℕ) < finrank K (F i) → b x ∈ F i) ∧
          (∀ i ≤ N', G i ≤ span K (b '' {x | b x ∈ G i})) := by
  induction m with
  | zero =>
    intro V _ _ _ B _ _ hV N F N' G _ _
    have : Subsingleton V := (Module.finrank_zero_iff (R := K)).mp (by rw [hV])
    refine ⟨Basis.empty V, fun x => isEmptyElim x, fun _ _ x => isEmptyElim x, fun i _ u _ => ?_⟩
    rw [Subsingleton.elim u 0]
    exact zero_mem _
  | succ m ih =>
    intro V _ _ _ B hB hnd hV N F N' G hF hG
    classical
    have hVnt : Nontrivial V := Module.nontrivial_of_finrank_pos (R := K) (by rw [hV]; omega)
    have hex : ∃ i, F i ≠ ⊥ := ⟨N, by rw [hF.top]; exact top_ne_bot⟩
    have hi₀ : F (Nat.find hex) ≠ ⊥ := Nat.find_spec hex
    have hi₀N : Nat.find hex ≤ N := Nat.find_min' hex (by rw [hF.top]; exact top_ne_bot)
    have hbot : ∀ m < Nat.find hex, F m = ⊥ := fun m hm => not_not.mp (Nat.find_min hex hm)
    obtain ⟨e, heF, he0⟩ := (Submodule.ne_bot_iff _).mp hi₀
    have hexj : ∃ j, e ∈ G j := ⟨N', by rw [hG.top]; trivial⟩
    have hej : e ∈ G (Nat.find hexj) := Nat.find_spec hexj
    have hjN : Nat.find hexj ≤ N' := Nat.find_min' hexj (by rw [hG.top]; trivial)
    have hj1 : 1 ≤ Nat.find hexj := by
      by_contra h0
      have h0' : Nat.find hexj = 0 := by omega
      rw [h0', hG.1, mem_bot] at hej
      exact he0 hej
    have hej' : e ∉ G (Nat.find hexj - 1) := Nat.find_min hexj (by omega)
    obtain ⟨f, hfG, hfe⟩ := exists_partner hG hj1 hjN hej'
    have hcF := isPairCompatible_of_first hF hi₀N hbot heF f
    have hcG := isPairCompatible_of_least hG hj1 hjN hej hfG
    set Z := B.orthogonal (span K {e, f}) with hZdef
    have hZ : finrank K Z = 2 * m := by
      have h : finrank K Z + 2 = finrank K V := hB.finrank_orthogonal_span_pair_add_two hnd hfe
      omega
    obtain ⟨c, hc, hcF', hcG'⟩ := ih (B.restrict Z) (fun z => hB.self_eq_zero z)
      (hB.restrict_nondegenerate_orthogonal_span_pair hfe hnd) hZ N _ N' _
      (isSelfDualChain_comap hB hfe hF hcF) (isSelfDualChain_comap hB hfe hG hcG)
    have hc' : ∀ x y, B (c x) (c y) = Matrix.J (Fin m) K x y := fun x y => by
      rw [← hc x y, BilinForm.restrict_apply, LinearMap.domRestrict_apply]
    obtain ⟨b, hb, hbd⟩ := hB.exists_basis_apply_eq_J_of_basis_orthogonal_span_pair hnd hfe c hc'
    have hb_inl0 : b (Sum.inl 0) = e := by rw [hbd]; simp
    have hb_inr0 : b (Sum.inr 0) = f := by rw [hbd]; simp
    have hb_inl : ∀ y : Fin m, b (Sum.inl y.succ) = c (Sum.inl y) := fun y => by
      rw [hbd]; simp
    have hb_inr : ∀ y : Fin m, b (Sum.inr y.succ) = c (Sum.inr y) := fun y => by
      rw [hbd]; simp
    refine ⟨b, hb, fun i hi x hx => ?_, fun i hi u hu => ?_⟩
    ·
      by_cases hi1 : i < Nat.find hex
      · rw [hbot i hi1, finrank_bot] at hx
        exact absurd hx (Nat.not_lt_zero _)
      by_cases hi2 : N - Nat.find hex < i
      · have h1 := hF.2.2 (N - i) (Nat.sub_le _ _)
        rw [hbot (N - i) (by omega), BilinForm.orthogonal_bot, Nat.sub_sub_self hi] at h1
        rw [← h1]
        trivial
      have hW : ∀ x ∈ F i, B e x = 0 := by
        intro x hxF
        have hx' : x ∈ F (N - Nat.find hex) := hF.le (by omega) (Nat.sub_le _ _) hxF
        rw [← hF.2.2 _ hi₀N] at hx'
        exact hx' e heF
      have heFi : e ∈ F i := hF.le (by omega) hi heF
      have hdim := finrank_comap_orthogonal_add_one hB hfe heFi hW
      have hZle : finrank K ((F i).comap (B.orthogonal (span K {e, f})).subtype) ≤ 2 * m := by
        rw [← hZ]
        exact Submodule.finrank_le _
      rcases x with x | x
      · induction x using Fin.cases with
        | zero =>
          rw [hb_inl0]
          exact heFi
        | succ y =>
          rw [flagOrder_succ_inl_succ, ← hdim] at hx
          rw [hb_inl]
          exact hcF' i hi (Sum.inl y) (Nat.lt_of_succ_lt_succ hx)
      · induction x using Fin.cases with
        | zero =>
          rw [flagOrder_succ_inr_zero, ← hdim] at hx
          omega
        | succ y =>
          rw [flagOrder_succ_inr_succ, ← hdim] at hx
          rw [hb_inr]
          exact hcF' i hi (Sum.inr y) (Nat.lt_of_succ_lt_succ hx)
    ·
      rw [eq_proj_add (B := B) (e := e) (f := f) u]
      refine add_mem (sub_mem ?_ ?_) ?_
      · rcases (hcG i hi u hu).1 with h1 | h1
        · rw [h1, zero_smul]
          exact zero_mem _
        · exact smul_mem _ _
            (subset_span ⟨Sum.inl 0, by show b _ ∈ G i; rw [hb_inl0]; exact h1, hb_inl0⟩)
      · rcases (hcG i hi u hu).2 with h1 | h1
        · rw [h1, zero_smul]
          exact zero_mem _
        · exact smul_mem _ _
            (subset_span ⟨Sum.inr 0, by show b _ ∈ G i; rw [hb_inr0]; exact h1, hb_inr0⟩)
      · set z : Z := ⟨_, proj_mem_orthogonal hB hfe u⟩
        have hz : z ∈ (G i).comap Z.subtype := hcG.proj_mem hi hu
        have hz' := Submodule.mem_map_of_mem (f := Z.subtype) (hcG' i hi hz)
        rw [Submodule.map_span] at hz'
        refine span_mono ?_ hz'
        rintro _ ⟨_, ⟨y, hy, rfl⟩, rfl⟩
        rcases y with y | y
        · exact ⟨Sum.inl y.succ, by show b _ ∈ G i; rw [hb_inl]; exact hy, hb_inl y⟩
        · exact ⟨Sum.inr y.succ, by show b _ ∈ G i; rw [hb_inr]; exact hy, hb_inr y⟩

variable {V : Type*} [AddCommGroup V] [Module K V]

theorem exists_isSymplecticBasis_of_J' {r : ℕ} {B : BilinForm K V}
    (b : Basis (Fin r ⊕ Fin r) K V) (hb : ∀ x y, B (b x) (b y) = Matrix.J (Fin r) K x y) :
    ∃ b' : Basis (Fin r ⊕ Fin r) K V, IsSymplecticBasis B b' ∧
      ∀ x, ∃ s : Kˣ, b' x = s • b x := by
  refine ⟨b.unitsSMul (Sum.elim 1 (-1)), ?_, fun x => ⟨Sum.elim 1 (-1) x, ?_⟩⟩
  · ext (x | x) (y | y) <;>
      simp [BilinForm.toMatrix_apply, Basis.unitsSMul_apply, hb, Matrix.J, Units.smul_def,
        Matrix.one_apply]
  · rw [Basis.unitsSMul_apply]

theorem span_image_eq_of_smul {ι : Type*} {b b' : ι → V} (h : ∀ x, ∃ s : Kˣ, b' x = s • b x)
    (s : Set ι) : span K (b' '' s) = span K (b '' s) := by
  apply le_antisymm
  · rw [span_le]
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨t, ht⟩ := h x
    rw [ht]
    exact smul_mem _ _ (subset_span ⟨x, hx, rfl⟩)
  · rw [span_le]
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨t, ht⟩ := h x
    have : b x = t⁻¹ • b' x := by rw [ht, smul_smul, inv_mul_cancel, one_smul]
    rw [this]
    exact smul_mem _ _ (subset_span ⟨x, hx, rfl⟩)

theorem common_symplectic_flag_basis [FiniteDimensional K V] {r : ℕ} {B : BilinForm K V}
    (hB : B.IsAlt) (hnd : B.Nondegenerate) (hV : finrank K V = 2 * r)
    {F G : ℕ → Submodule K V} (hF : IsSelfDualFlag B r F) (hG : IsSelfDualFlag B r G) :
    ∃ b : Basis (Fin r ⊕ Fin r) K V, IsSymplecticBasis B b ∧
      (∀ i ≤ 2 * r, F i = span K (b '' {x | (flagOrder r x : ℕ) < i})) ∧
      (∀ i ≤ 2 * r, G i = span K (b '' {x | b x ∈ G i})) := by
  obtain ⟨b₀, hb₀, hF₀, hG₀⟩ := exists_common_basis_aux.{_, _} r B hB hnd hV (2 * r) F (2 * r) G
    hF.isSelfDualChain hG.isSelfDualChain
  obtain ⟨b, hb, hbb₀⟩ := exists_isSymplecticBasis_of_J' b₀ hb₀
  have hmem : ∀ (W : Submodule K V) x, b x ∈ W ↔ b₀ x ∈ W := by
    intro W x
    obtain ⟨s, hs⟩ := hbb₀ x
    rw [hs]
    exact ⟨fun h => by simpa using W.smul_mem (s⁻¹ : Kˣ) h, fun h => W.smul_mem s h⟩
  refine ⟨b, hb, fun i hi => ?_, fun i hi => ?_⟩
  ·
    set u : Fin (2 * r) → V := b ∘ (flagOrder r).symm
    have hu : LinearIndependent K u := b.linearIndependent.comp _ (flagOrder r).symm.injective
    have himage : u '' {j : Fin (2 * r) | (j : ℕ) < i} = b '' {x | (flagOrder r x : ℕ) < i} := by
      ext y
      constructor
      · rintro ⟨j, hj, rfl⟩
        exact ⟨(flagOrder r).symm j, by simpa using hj, rfl⟩
      · rintro ⟨x, hx, rfl⟩
        exact ⟨flagOrder r x, hx, by simp [u]⟩
    refine (eq_of_le_of_finrank_eq (span_le.mpr ?_) ?_).symm
    · rintro _ ⟨x, hx, rfl⟩
      rw [SetLike.mem_coe, hmem]
      exact hF₀ i hi x (by rw [hF.1 i hi]; exact hx)
    · rw [← himage, finrank_span_image_lt hu hi, hF.1 i hi]
  · refine le_antisymm ?_ (span_le.mpr fun _ ⟨x, hx, h⟩ => h ▸ hx)
    have hset : {x | b x ∈ G i} = {x | b₀ x ∈ G i} := Set.ext fun x => hmem (G i) x
    rw [hset, span_image_eq_of_smul hbb₀]
    exact hG₀ i hi

end CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
