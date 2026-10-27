module

public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherBruhat
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherReducedWord

public section

namespace CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

open Matrix Module Submodule CFSG.ClassicalGroups.UnitaryFlag CFSG.LinearGroups
  CFSG.LocalAnalysis.ComponentInitial
open scoped Pointwise
open CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl (IsLinePerm isLinePerm_one)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher (simpleRefl spWordProd
  spWordProd_cons IsSpReducedWord exists_word_length_eq spLength_eq_invCount)

variable {p f : ℕ} {K : Type} [Field K] {r ε : ℕ}

theorem smul_span_single_of_isLinePerm {h : UnitaryFieldData p f K} {g : hypSU h r ε}
    {σ : Equiv.Perm (HypIndex r ε)}
    (hg : IsLinePerm σ ((g : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K))
    (S : Set (HypIndex r ε)) :
    g • span K ((fun x => (Pi.single x (1 : K) : HypIndex r ε → K)) '' S) =
      span K ((fun x => (Pi.single x (1 : K) : HypIndex r ε → K)) '' (σ '' S)) := by
  rw [hypSU_smul_eq_map, map_span, Set.image_image, Set.image_image]
  simp only [mulVecLin_apply, monomial_mulVec_single hg]
  exact span_image_smul (v := fun x => (Pi.single (σ x) (1 : K) : HypIndex r ε → K))
    (fun x => hg.apply_ne_zero x) S

theorem fullPos_weylPerm_simpleRefl_lt (k : Fin r) {i : ℕ} (hi : i ≤ r) (hik : i ≠ k + 1)
    {x : HypIndex r ε} (hx : fullPos x < i) :
    fullPos (weylPerm (simpleRefl r k) x) < i := by
  obtain ⟨j, rfl, hj⟩ := exists_inl_of_fullPos_lt hi hx
  rw [weylPerm_inl]
  unfold simpleRefl
  split_ifs with hk
  · change ((Equiv.swap k ⟨k + 1, hk⟩ j : Fin r) : ℕ) < i
    rw [Equiv.swap_apply_def]
    split_ifs with h1 h2
    · subst h1
      change (j : ℕ) + 1 < i
      omega
    · subst h2
      change (k : ℕ) + 1 < i at hj
      omega
    · exact hj
  · have hjk : j ≠ k := fun e => by
      subst e
      have := j.2
      omega
    have hsw : Equiv.swap (Sum.inl k) (Sum.inr k) (Sum.inl j : Fin r ⊕ Fin r) = Sum.inl j :=
      Equiv.swap_apply_of_ne_of_ne (by simpa using hjk) (by simp)
    rw [hsw]
    exact hj

theorem le_fullPos_weylPerm_simpleRefl_inl (k : Fin r) :
    (k : ℕ) + 1 ≤ fullPos (weylPerm (ε := ε) (simpleRefl r k) (.inl k)) := by
  rw [weylPerm_inl]
  unfold simpleRefl
  split_ifs with hk
  · rw [Equiv.sumCongr_apply, Sum.map_inl, Equiv.swap_apply_left]
    exact le_rfl
  · rw [Equiv.swap_apply_left]
    change (k : ℕ) + 1 ≤ 2 * r + ε - 1 - k
    have := k.2
    omega

theorem uWeylRep_smul_hypFlag (h : UnitaryFieldData p f K) (hε : ε ≤ 1) {c : K}
    (hc : c ∈ h.traceZero) (hc0 : c ≠ 0) (k : Fin r) {i : ℕ} (hi : i ≤ r) :
    uWeylRep ε h k c hc • hypFlag h r ε i = hypFlag h r ε i ↔ i ≠ k + 1 := by
  rw [hypFlag_eq_posFlag h hε (by omega)]
  have hl := isLinePerm_uWeylRep (ε := ε) hc hc0 k
  constructor
  · intro heq hik
    subst hik
    have hek : (Pi.single (.inl k) (1 : K) : HypIndex r ε → K) ∈ posFlag r ε K (k + 1) := by
      rw [posFlag_eq_span]
      exact subset_span ⟨.inl k, by simp, rfl⟩
    have hmem : uWeylRep ε h k c hc • (Pi.single (.inl k) (1 : K) : HypIndex r ε → K) ∈
        posFlag r ε K (k + 1) := by
      rw [← heq]
      exact Submodule.smul_mem_pointwise_smul _ _ _ hek
    change (((uWeylRep ε h k c hc : hypSU h r ε) : GL (HypIndex r ε) K) :
      Matrix (HypIndex r ε) (HypIndex r ε) K) *ᵥ Pi.single (.inl k) 1 ∈ _ at hmem
    rw [monomial_mulVec_single hl] at hmem
    have h0 := mem_posFlag.mp hmem _ (le_fullPos_weylPerm_simpleRefl_inl k)
    simp only [Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one] at h0
    exact hl.apply_ne_zero _ h0
  · intro hik
    have hle : uWeylRep ε h k c hc • posFlag r ε K i ≤ posFlag r ε K i := by
      conv_lhs => rw [posFlag_eq_span]
      rw [smul_span_single_of_isLinePerm hl, posFlag_eq_span]
      refine span_mono (Set.image_mono ?_)
      rintro _ ⟨x, hx, rfl⟩
      exact fullPos_weylPerm_simpleRefl_lt k hi hik hx
    exact eq_of_le_of_finrank_eq hle (finrank_smul _ _)

theorem hypBorel_le_flagStabilizer {h : UnitaryFieldData p f K} {I : Set ℕ}
    (hI : I ⊆ Set.Icc 1 r) : hypBorel h r ε ≤ flagStabilizer h r ε I :=
  fun _ hg => mem_flagStabilizer.mpr fun i hi => (mem_hypBorel.mp hg) i (hI hi).1 (hI hi).2

theorem uWeylRep_mem_flagStabilizer_iff (h : UnitaryFieldData p f K) (hε : ε ≤ 1) {c : K}
    (hc : c ∈ h.traceZero) (hc0 : c ≠ 0) {I : Set ℕ} (hI : I ⊆ Set.Icc 1 r) (k : Fin r) :
    uWeylRep ε h k c hc ∈ flagStabilizer h r ε I ↔ (k : ℕ) + 1 ∉ I := by
  rw [mem_flagStabilizer]
  constructor
  · intro hmem hkI
    exact (uWeylRep_smul_hypFlag h hε hc hc0 k (hI hkI).2).mp (hmem _ hkI) rfl
  · intro hkI i hiI
    exact (uWeylRep_smul_hypFlag h hε hc hc0 k (hI hiI).2).mpr fun e => hkI (e ▸ hiI)

variable (ε) in
@[expose] noncomputable def uWordProd (h : UnitaryFieldData p f K) (c : K)
    (hc : c ∈ h.traceZero) (l : List (Fin r)) : hypSU h r ε :=
  (l.map fun k => uWeylRep ε h k c hc).prod

theorem uWordProd_cons (h : UnitaryFieldData p f K) {c : K} (hc : c ∈ h.traceZero)
    (k : Fin r) (l : List (Fin r)) :
    uWordProd ε h c hc (k :: l) = uWeylRep ε h k c hc * uWordProd ε h c hc l := by
  simp [uWordProd]

theorem isLinePerm_uWordProd {h : UnitaryFieldData p f K} {c : K} (hc : c ∈ h.traceZero)
    (hc0 : c ≠ 0) (l : List (Fin r)) :
    IsLinePerm (weylPerm (ε := ε) (spWordProd l))
      (((uWordProd ε h c hc l : hypSU h r ε) : GL (HypIndex r ε) K) :
        Matrix (HypIndex r ε) (HypIndex r ε) K) := by
  induction l with
  | nil =>
    have h1 : spWordProd ([] : List (Fin r)) = 1 := by simp [spWordProd]
    have h2 : uWordProd ε h c hc ([] : List (Fin r)) = 1 := by simp [uWordProd]
    rw [h1, weylPerm_one, h2, Subgroup.coe_one, Units.val_one]
    exact isLinePerm_one
  | cons k l ih =>
    rw [uWordProd_cons, spWordProd_cons, weylPerm_mul, Subgroup.coe_mul, Units.val_mul]
    exact (isLinePerm_uWeylRep hc hc0 k).mul ih

theorem uWordProd_mem_closure {h : UnitaryFieldData p f K} {c : K} (hc : c ∈ h.traceZero)
    {I : Set ℕ} {l : List (Fin r)} (hl : ∀ k ∈ l, (k : ℕ) + 1 ∉ I) :
    uWordProd ε h c hc l ∈ Subgroup.closure
      {g | ∃ k : Fin r, (k : ℕ) + 1 ∉ I ∧ uWeylRep ε h k c hc = g} := by
  induction l with
  | nil =>
    have h2 : uWordProd ε h c hc ([] : List (Fin r)) = 1 := by simp [uWordProd]
    rw [h2]
    exact one_mem _
  | cons k l ih =>
    rw [uWordProd_cons]
    exact mul_mem (Subgroup.subset_closure ⟨k, hl k List.mem_cons_self, rfl⟩)
      (ih fun k' hk' => hl k' (List.mem_cons_of_mem _ hk'))

theorem unitary_subflag_generation (h : UnitaryFieldData p f K) (hr : 1 ≤ r) (hε : ε ≤ 1)
    {c : K} (hc : c ∈ h.traceZero) (hc0 : c ≠ 0) {I : Set ℕ} (hI : I ⊆ Set.Icc 1 r) :
    flagStabilizer h r ε I = hypBorel h r ε ⊔
      Subgroup.closure {g | ∃ k : Fin r, (k : ℕ) + 1 ∉ I ∧ uWeylRep ε h k c hc = g} ∧
    (∀ k : Fin r, uWeylRep ε h k c hc ∈ flagStabilizer h r ε I ↔ (k : ℕ) + 1 ∉ I) ∧
    ∀ W : Submodule K (HypIndex r ε → K),
      ((∀ x ∈ W, ∀ y ∈ W, hypForm h r ε x y = 0) ∧
        ∀ g ∈ flagStabilizer h r ε I, g • W = W) ↔
      (W = hypFlag h r ε 0 ∨ ∃ i ∈ I, W = hypFlag h r ε i) := by
  have hB := hypBorel_le_flagStabilizer (h := h) (ε := ε) hI
  have hmemiff := uWeylRep_mem_flagStabilizer_iff h hε hc hc0 hI
  have hth := unitriangular_invariant_isotropic_subspaces h hr hε
  refine ⟨le_antisymm ?_ ?_, hmemiff, fun W => ⟨?_, ?_⟩⟩
  ·
    intro g hg
    obtain ⟨w, b₁, hb₁, b₂, hb₂, rfl⟩ := exists_mem_uBruhatCell h hε hc hc0 g
    have hdot : weylElt h hc hc0 w.2 ∈ flagStabilizer h r ε I := by
      have := mul_mem (mul_mem (inv_mem (hB hb₁)) hg) (inv_mem (hB hb₂))
      rwa [show b₁⁻¹ * (b₁ * weylElt h hc hc0 w.2 * b₂) * b₂⁻¹ = weylElt h hc hc0 w.2 by
        group] at this
    have hwA : (hypBorel h r ε).map (MulAut.conj (weylElt h hc hc0 w.2)).toMonoidHom ≤
        flagStabilizer h r ε I := by
      rintro _ ⟨b, hb, rfl⟩
      exact mul_mem (mul_mem hdot (hB hb)) (inv_mem hdot)
    obtain ⟨l, hlen, hprod⟩ := exists_word_length_eq _ (w : Equiv.Perm (Fin r ⊕ Fin r)) w.2 rfl
    have hred : IsSpReducedWord (w : Equiv.Perm (Fin r ⊕ Fin r)) l :=
      ⟨hprod, by rw [hlen, spLength_eq_invCount w.2]⟩
    have hall := unitary_reduced_word_extraction h hc hc0 _ hB l _ w.2 hwA hred
    have hallow : ∀ k ∈ l, (k : ℕ) + 1 ∉ I := fun k hk => (hmemiff k).mp (hall k hk)
    have hmono : IsLinePerm (weylPerm (ε := ε) (w : Equiv.Perm (Fin r ⊕ Fin r)))
        (((uWordProd ε h c hc l : hypSU h r ε) : GL (HypIndex r ε) K) :
          Matrix (HypIndex r ε) (HypIndex r ε) K) := by
      rw [← hprod]
      exact isLinePerm_uWordProd hc hc0 l
    obtain ⟨t, ht, hteq⟩ := exists_torus_of_isLinePerm hc hc0 w.2 hmono
    have hw' : weylElt h hc hc0 w.2 = uWordProd ε h c hc l * t⁻¹ := by
      rw [hteq, mul_inv_cancel_right]
    rw [hw']
    exact mul_mem (mul_mem (Subgroup.mem_sup_left hb₁) (mul_mem
      (Subgroup.mem_sup_right (uWordProd_mem_closure hc hallow))
      (Subgroup.mem_sup_left (inv_mem (hypTorus_le_hypBorel h ht)))))
      (Subgroup.mem_sup_left hb₂)
  ·
    refine sup_le hB ((Subgroup.closure_le _).mpr ?_)
    rintro _ ⟨k, hk, rfl⟩
    exact (hmemiff k).mpr hk
  ·
    rintro ⟨hiso, hinv⟩
    obtain ⟨d, hd, rfl⟩ := hth.2.2.1 W hiso fun u hu =>
      hinv u (hB (hypUnitriangular_le_hypBorel h hu))
    rcases Nat.eq_zero_or_pos d with rfl | hd0
    · exact Or.inl rfl
    · refine Or.inr ⟨d, ?_, rfl⟩
      by_contra hdI
      have hk : ((⟨d - 1, by omega⟩ : Fin r) : ℕ) + 1 ∉ I := by
        rw [show ((⟨d - 1, by omega⟩ : Fin r) : ℕ) + 1 = d by
          change d - 1 + 1 = d
          omega]
        exact hdI
      exact (uWeylRep_smul_hypFlag h hε hc hc0 ⟨d - 1, by omega⟩ hd).mp
        (hinv _ ((hmemiff _).mpr hk)) (by
          change d = d - 1 + 1
          omega)
  ·
    rintro (rfl | ⟨i, hi, rfl⟩)
    · refine ⟨(hth.2.2.2.1 0 (Nat.zero_le r)).1, fun g _ => ?_⟩
      rw [hypFlag_eq_posFlag h hε (Nat.zero_le _), posFlag_zero]
      exact Submodule.smul_bot' g
    · exact ⟨(hth.2.2.2.1 i (hI hi).2).1, fun g hg => mem_flagStabilizer.mp hg i hi⟩

end CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
