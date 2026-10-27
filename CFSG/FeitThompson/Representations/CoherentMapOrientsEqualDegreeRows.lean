module

public import CFSG.FeitThompson.Representations.CoherentRowImageSelectsSignedColumn
public import CFSG.FeitThompson.Representations.ConjugatePairsDisjointBlocksCoherence
public import CFSG.FeitThompson.Representations.CyclicTIAxesNonrealConjugatePairs
import CFSG.FeitThompson.Representations.OddBridgeProjectionRigidity
import CFSG.FeitThompson.Representations.CentralLayerCoherenceExtension
import CFSG.FeitThompson.Representations.NormalInducedCharactersOrthogonal
public import CFSG.FeitThompson.Representations.DisjointAntirealBlocksOrthogonal
public import CFSG.FeitThompson.Representations.RectangleDifferencesBasisSupportedFunctions

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

namespace CoherentSimultaneousOrientation

theorem card_univ_Irr_left {G : Type*} [Group G] {W W1 W2 : Subgroup G} [Fintype ↑(Irr ↥W1)]
    (hW : IsCyclicTIPair W W1 W2) :
    (Finset.univ : Finset ↑(Irr ↥W1)).card = Nat.card ↥W1 := by
  rw [Finset.card_univ, ← Nat.card_eq_fintype_card, hW.card_Irr_left]

theorem natCard_left_ne_zero {G : Type*} [Group G] {W W1 W2 : Subgroup G}
    (hW : IsCyclicTIPair W W1 W2) : (Nat.card ↥W1 : ℂ) ≠ 0 := by
  have h3 := hW.three_le_natCard_left
  have h0 : Nat.card ↥W1 ≠ 0 := by omega
  exact_mod_cast h0

section Columns

variable {G : Type*} [Group G] [Fintype G] {W W1 W2 : Subgroup G} [Fintype ↥W]
  {ω : classFun ↥W →ₗ[ℂ] classFun G}

open scoped Classical in
theorem cfInner_prodCharEtaColSum (hW : IsCyclicTIPair W W1 W2)
    (hω : IsCyclicTIIsometry W W1 W2 ω) (j l : Irr ↥W2) :
    cfInner (hW.prodCharEtaColSum ω j) (hW.prodCharEtaColSum ω l)
      = if j = l then (Nat.card ↥W1 : ℂ) else 0 := by
  have hfin := hW.finite_left
  have : Fintype ↑(Irr ↥W1) := Fintype.ofFinite _
  rw [hW.prodCharEtaColSum_eq_sum (σ := ω) l, cfInner_sum_right]
  have hkey : ∀ i : Irr ↥W1, cfInner (hW.prodCharEtaColSum ω j) (hW.prodCharEta ω i l)
      = if j = l then (1 : ℂ) else 0 := fun i => hW.cfInner_prodCharEtaColSum_prodCharEta hω j i l
  rw [Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) => hkey i]
  by_cases h : j = l
  · rw [if_pos h, if_pos h, Finset.sum_const, card_univ_Irr_left hW]
    simp
  · rw [if_neg h, if_neg h, Finset.sum_const]
    simp

theorem smul_prodCharEtaColSum_mem_span_Irr (hW : IsCyclicTIPair W W1 W2)
    (hω : IsCyclicTIIsometry W W1 W2 ω) {δ : ℂ} (hδ : δ = 1 ∨ δ = -1) (j : Irr ↥W2) :
    δ • hW.prodCharEtaColSum ω j ∈ Submodule.span ℤ (Irr G) := by
  have hP := hW.prodCharEtaColSum_mem_span_Irr hω j
  rcases hδ with rfl | rfl
  · simpa using hP
  · simpa using neg_mem hP

open scoped Classical in
theorem cfInner_smul_prodCharEtaColSum (hW : IsCyclicTIPair W W1 W2)
    (hω : IsCyclicTIIsometry W W1 W2 ω) {δ : ℂ} (hδ : δ = 1 ∨ δ = -1) (j l : Irr ↥W2) :
    cfInner (δ • hW.prodCharEtaColSum ω j) (δ • hW.prodCharEtaColSum ω l)
      = if j = l then (Nat.card ↥W1 : ℂ) else 0 := by
  rw [cfInner_smul_left, cfInner_smul_right, cfInner_prodCharEtaColSum hW hω]
  rcases hδ with rfl | rfl <;> by_cases h : j = l <;> simp [h]

open scoped Classical in
theorem eq_or_eq_starIrr_of_col_eq (hW : IsCyclicTIPair W W1 W2)
    (hω : IsCyclicTIIsometry W W1 W2 ω) {δ : ℂ} (hδ : δ = 1 ∨ δ = -1) {j k : Irr ↥W2}
    (hj : j ≠ principalIrr ↥W2)
    (h : (-δ) • hW.prodCharEtaColSum ω (starIrr j) - (-δ) • hW.prodCharEtaColSum ω (starIrr k)
      = δ • hW.prodCharEtaColSum ω j - δ • hW.prodCharEtaColSum ω k) :
    k = j ∨ k = starIrr j := by
  by_contra hcon
  rw [not_or] at hcon
  obtain ⟨hkj, hkbj⟩ := hcon
  have hbjj : starIrr j ≠ j := starIrr_ne_self hW.odd_natCard_right hj
  have hbkj : starIrr k ≠ j := fun he => hkbj (by
    have h2 := congrArg starIrr he
    rwa [starIrr_starIrr] at h2)
  have hpair := congrArg (fun f => cfInner f (hW.prodCharEtaColSum ω j)) h
  simp only [cfInner_sub_left, cfInner_smul_left, cfInner_prodCharEtaColSum hW hω,
    if_neg hbjj, if_neg hbkj, mul_zero, sub_zero, if_neg hkj] at hpair
  have hδ0 : δ ≠ 0 := by rcases hδ with rfl | rfl <;> norm_num
  exact (mul_ne_zero hδ0 (natCard_left_ne_zero hW)) hpair.symm

end Columns

theorem natCard_right_eq_three {G : Type*} [Group G] {W W1 W2 : Subgroup G} [Finite ↥W2]
    (hW : IsCyclicTIPair W W1 W2) {j : Irr ↥W2}
    (h : ∀ k : Irr ↥W2, k ≠ principalIrr ↥W2 → k = j ∨ k = starIrr j) :
    Nat.card ↥W2 = 3 := by
  have hsub : (Set.univ : Set (Irr ↥W2)) ⊆ {principalIrr ↥W2, j, starIrr j} := by
    intro k _
    rcases eq_or_ne k (principalIrr ↥W2) with rfl | hk
    · exact Set.mem_insert _ _
    · rcases h k hk with rfl | rfl
      · exact Set.mem_insert_of_mem _ (Set.mem_insert _ _)
      · exact Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ rfl)
  have hu : (Set.univ : Set (Irr ↥W2)).ncard = Nat.card (Irr ↥W2) := by simp [Set.ncard_univ]
  have hle : Nat.card ↑(Irr ↥W2) ≤ 3 := by
    have h1 := Set.ncard_le_ncard hsub (Set.toFinite _)
    have h3 : ({principalIrr ↥W2, j, starIrr j} : Set (Irr ↥W2)).ncard ≤ 3 := by
      refine le_trans (Set.ncard_insert_le _ _) ?_
      have h4 := Set.ncard_insert_le j ({starIrr j} : Set (Irr ↥W2))
      simp only [Set.ncard_singleton] at h4 ⊢
      omega
    omega
  have h3le : 3 ≤ Nat.card ↥W2 := hW.three_le_natCard_right
  have hcard : Nat.card ↑(Irr ↥W2) = Nat.card ↥W2 := hW.card_Irr_right
  omega

section Rows

variable {G : Type*} [Group G] [Fintype G] {L : Subgroup G} [Fintype ↥L] {A0 : Set G}
  {Tsig : G → Subgroup G} {S : Set (↥L → ℂ)} {τ : charSpanZero S →+ virtualChars G}
  {ν0 : Submodule.span ℤ S →+ virtualChars G} {K : Subgroup ↥L} [K.Normal] {H : Subgroup ↥K}
  {W W1 W2 : Subgroup G} [Fintype ↥W] {ω : classFun ↥W →ₗ[ℂ] classFun G}

omit [Fintype G] [Fintype ↥L] in
theorem coe_nu_of_coe_eq_sum {ν : Submodule.span ℤ S →+ virtualChars G}
    {ι : Type*} [Fintype ι] {M : ι → ↥L → ℂ} (hMS : ∀ i, M i ∈ S)
    (c : ι → ℤ) (w : Submodule.span ℤ S) (hw : (w : ↥L → ℂ) = ∑ i, (c i : ℂ) • M i) :
    (ν w : G → ℂ) = ∑ i, (c i : ℂ) • (ν ⟨M i, Submodule.subset_span (hMS i)⟩ : G → ℂ) := by
  have hsplit : w = ∑ i, c i • (⟨M i, Submodule.subset_span (hMS i)⟩ : Submodule.span ℤ S) := by
    refine Subtype.ext ?_
    rw [AddSubmonoidClass.coe_finsetSum, hw]
    exact Finset.sum_congr rfl fun i _ => by rw [SetLike.val_smul, Int.cast_smul_eq_zsmul]
  rw [hsplit, map_sum, AddSubmonoidClass.coe_finsetSum]
  exact Finset.sum_congr rfl fun i _ => by rw [map_zsmul, SetLike.val_smul, Int.cast_smul_eq_zsmul]

open scoped Classical in
theorem exists_isCoherentWith_row_family (hW : IsCyclicTIPair W W1 W2)
    (hω : IsCyclicTIIsometry W W1 W2 ω) {δ : ℂ} (hδ : δ = 1 ∨ δ = -1)
    {ι : Type*} [Finite ι] [Nonempty ι] {c : ι → Irr ↥W2}
    (hc : Function.Injective c) {M : ι → ↥L → ℂ} (hSM : S = Set.range M)
    (hnorm : ∀ i, cfInner (M i) (M i) = (Nat.card ↥W1 : ℂ))
    (horth : ∀ i i', i ≠ i' → cfInner (M i) (M i') = 0)
    {b : ℤ} (hbne : b ≠ 0) (hb : ∀ i, M i 1 = (b : ℂ))
    (hν0 : IsCoherentWith S τ ν0)
    (htau : ∀ i i', (ν0 ⟨M i, Submodule.subset_span (hSM ▸ Set.mem_range_self i)⟩ : G → ℂ)
        - (ν0 ⟨M i', Submodule.subset_span (hSM ▸ Set.mem_range_self i')⟩ : G → ℂ)
      = δ • hW.prodCharEtaColSum ω (c i) - δ • hW.prodCharEtaColSum ω (c i')) :
    ∃ ν : Submodule.span ℤ S →+ virtualChars G, IsCoherentWith S τ ν ∧
      ∀ i, ∀ w : Submodule.span ℤ S, (w : ↥L → ℂ) = M i →
        (ν w : G → ℂ) = δ • hW.prodCharEtaColSum ω (c i) := by
  have : Fintype ι := Fintype.ofFinite ι
  have hMS : ∀ i, M i ∈ S := fun i => hSM ▸ Set.mem_range_self i
  have hq := natCard_left_ne_zero (W1 := W1) hW
  obtain ⟨ν, hνc, hνval⟩ := exists_isCoherentWith_of_gram_eq (L := ↥L) (G := G)
    (S := S) (u := M) hSM (g := fun _ => (Nat.card ↥W1 : ℂ))
    (fun i i' => by
      by_cases h : i = i'
      · subst h; rw [if_pos rfl]; exact hnorm i
      · rw [if_neg h]; exact horth i i' h)
    (fun _ => hq)
    (v := fun i => δ • hW.prodCharEtaColSum ω (c i))
    (fun i => smul_prodCharEtaColSum_mem_span_Irr hW hω hδ (c i))
    (fun i i' => by
      rw [cfInner_smul_prodCharEtaColSum hW hω hδ]
      by_cases h : i = i'
      · simp [h]
      · rw [if_neg (fun hcc => h (hc hcc)), if_neg h])
    (τ := virtToSpanIrr.comp τ)
    (by
      intro w cc hcw
      have hzC : ∑ i, (cc i : ℂ) = 0 := by
        have h1 : (w : ↥L → ℂ) 1 = 0 := charSpanZero_apply_one w
        rw [hcw] at h1
        simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hb] at h1
        have h2 : (∑ i, (cc i : ℂ)) * (b : ℂ) = 0 := by rw [Finset.sum_mul]; exact h1
        exact (mul_eq_zero.1 h2).resolve_right (by exact_mod_cast hbne)
      obtain ⟨i0⟩ := ‹Nonempty ι›
      have hτw : ((virtToSpanIrr.comp τ) w : G → ℂ)
          = ∑ i, (cc i : ℂ) • (ν0 ⟨M i, Submodule.subset_span (hMS i)⟩ : G → ℂ) := by
        rw [coe_virtToSpanIrr_comp, ← hν0.eq_on_zero w]
        exact coe_nu_of_coe_eq_sum hMS cc _ hcw
      rw [hτw]
      have key : ∀ i, (cc i : ℂ) • (ν0 ⟨M i, Submodule.subset_span (hMS i)⟩ : G → ℂ)
          = (cc i : ℂ) • (δ • hW.prodCharEtaColSum ω (c i))
            + (cc i : ℂ) • ((ν0 ⟨M i0, Submodule.subset_span (hMS i0)⟩ : G → ℂ)
              - δ • hW.prodCharEtaColSum ω (c i0)) := by
        intro i
        rw [← smul_add]
        congr 1
        have h' : (ν0 ⟨M i, Submodule.subset_span (hMS i)⟩ : G → ℂ)
            - (ν0 ⟨M i0, Submodule.subset_span (hMS i0)⟩ : G → ℂ)
          = δ • hW.prodCharEtaColSum ω (c i) - δ • hW.prodCharEtaColSum ω (c i0) := htau i i0
        linear_combination (norm := module) h'
      rw [Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) => key i, Finset.sum_add_distrib,
        ← Finset.sum_smul, hzC, zero_smul, add_zero])
  refine ⟨ν, ⟨hνc.inner_eq, fun f => (hνc.eq_on_zero f).trans (Subtype.ext ?_)⟩, hνval⟩
  rw [AddMonoidHom.comp_apply, coe_spanIrrToVirtualChars, coe_virtToSpanIrr_comp]

theorem eq_col_or_eq_neg_starIrr_col (hodd : Odd (Nat.card G)) (hW : IsCyclicTIPair W W1 W2)
    (hW2 : W2 ≤ K.map L.subtype) (hW1 : W1 ⊓ K.map L.subtype = ⊥)
    (hω : IsCyclicTIIsometry W W1 W2 ω) (hD : IsDadeData L A0 Tsig)
    (hVA : cyclicTIDiff W W1 W2 ⊆ A0) (hS : S ⊆ indFamDetect K H)
    (hSstar : ∀ χ ∈ S, star χ ∈ S)
    (hS0 : ∀ (f : charSpanZero S) (x : ↥L), (x : G) ∉ A0 → (f : ↥L → ℂ) x = 0)
    (hν0 : IsCoherentWith S τ ν0)
    (hντ : ∀ (f : Submodule.span ℤ S) (F : dadeDomain L A0), (f : ↥L → ℂ) = (F : ↥L → ℂ) →
      (ν0 f : G → ℂ) = ((dadeMap hD F : classFun G) : G → ℂ))
    {M : {j : Irr ↥W2 // j ≠ principalIrr ↥W2} → ↥L → ℂ} (hMS : ∀ j, M j ∈ S)
    (hnorm : ∀ j, cfInner (M j) (M j) = (Nat.card ↥W1 : ℂ))
    (horth : ∀ j k, j ≠ k → cfInner (M j) (M k) = 0)
    {n : ℕ} (hb : ∀ j, M j 1 = (n : ℂ)) {δ : ℂ} (hδ : δ = 1 ∨ δ = -1)
    (htau : ∀ j k, (ν0 ⟨M j, Submodule.subset_span (hMS j)⟩ : G → ℂ)
        - (ν0 ⟨M k, Submodule.subset_span (hMS k)⟩ : G → ℂ)
      = δ • hW.prodCharEtaColSum ω (j : Irr ↥W2) - δ • hW.prodCharEtaColSum ω (k : Irr ↥W2))
    {ξ : ↥L → ℂ} (hξS : ξ ∈ S) (hξIrr : ξ ∈ Irr ↥L)
    (j : {j : Irr ↥W2 // j ≠ principalIrr ↥W2}) :
    (ν0 ⟨M j, Submodule.subset_span (hMS j)⟩ : G → ℂ) = δ • hW.prodCharEtaColSum ω (j : Irr ↥W2) ∨
      (ν0 ⟨M j, Submodule.subset_span (hMS j)⟩ : G → ℂ)
        = (-δ) • hW.prodCharEtaColSum ω (starIrr (j : Irr ↥W2)) := by
  have hfinW2 := hW.finite_right
  obtain ⟨a, -, ha⟩ := NormalInducedFamily.exists_apply_one_eq_of_mem_Irr hξIrr
  set jb : {j : Irr ↥W2 // j ≠ principalIrr ↥W2} :=
    ⟨starIrr (j : Irr ↥W2), starIrr_ne_principalIrr j.2⟩ with hjb
  have hjjb : (j : Irr ↥W2) ≠ (jb : Irr ↥W2) :=
    fun he => (starIrr_ne_self hW.odd_natCard_right j.2) he.symm
  exact CoherentRowColumn.eq_signed_col_or_neg_signed_col hodd hW hW2 hW1 hω hD hVA hS hSstar
    hS0 hν0 hντ (hMS j) (hMS jb) hξS hξIrr (a := (a : ℤ)) (b := (n : ℤ))
    (by rw [ha]; push_cast; ring) (by rw [hb j]; push_cast; ring)
    (hnorm j) (horth j jb (fun he => hjjb (congrArg Subtype.val he))) hδ hjjb (htau j jb)

theorem exists_isCoherentWith_forall_eq_signed_col (hodd : Odd (Nat.card G))
    (hW : IsCyclicTIPair W W1 W2)
    (hW2 : W2 ≤ K.map L.subtype) (hW1 : W1 ⊓ K.map L.subtype = ⊥)
    (hω : IsCyclicTIIsometry W W1 W2 ω) (hD : IsDadeData L A0 Tsig)
    (hVA : cyclicTIDiff W W1 W2 ⊆ A0) (hS : S ⊆ indFamDetect K H)
    (hSstar : ∀ χ ∈ S, star χ ∈ S)
    (hS0 : ∀ (f : charSpanZero S) (x : ↥L), (x : G) ∉ A0 → (f : ↥L → ℂ) x = 0)
    (hν0 : IsCoherentWith S τ ν0)
    (hντ : ∀ (f : Submodule.span ℤ S) (F : dadeDomain L A0), (f : ↥L → ℂ) = (F : ↥L → ℂ) →
      (ν0 f : G → ℂ) = ((dadeMap hD F : classFun G) : G → ℂ))
    {M : {j : Irr ↥W2 // j ≠ principalIrr ↥W2} → ↥L → ℂ} (hMS : ∀ j, M j ∈ S)
    (hnorm : ∀ j, cfInner (M j) (M j) = (Nat.card ↥W1 : ℂ))
    (horth : ∀ j k, j ≠ k → cfInner (M j) (M k) = 0)
    {n : ℕ} (hn : 0 < n) (hb : ∀ j, M j 1 = (n : ℂ))
    {δ : ℂ} (hδ : δ = 1 ∨ δ = -1)
    (htau : ∀ j k, (ν0 ⟨M j, Submodule.subset_span (hMS j)⟩ : G → ℂ)
        - (ν0 ⟨M k, Submodule.subset_span (hMS k)⟩ : G → ℂ)
      = δ • hW.prodCharEtaColSum ω (j : Irr ↥W2) - δ • hW.prodCharEtaColSum ω (k : Irr ↥W2))
    (hclass : S ∩ Irr ↥L = ∅ → S = Set.range M) :
    ∃ ν : Submodule.span ℤ S →+ virtualChars G, IsCoherentWith S τ ν ∧ ∃ e : ℕ, (e = 0 ∨ e = 1) ∧
      (∀ j, (ν ⟨M j, Submodule.subset_span (hMS j)⟩ : G → ℂ)
        = ((-1 : ℂ) ^ e * δ) • hW.prodCharEtaColSum ω (starIrr^[e] (j : Irr ↥W2))) ∧
      (e = 1 → Nat.card ↥W2 = 3) ∧ ((S ∩ Irr ↥L).Nonempty → ν = ν0) := by
  classical
  have hfinW2 := hW.finite_right
  have hfinIrr : Finite ↑(Irr ↥W2) := finite_coe_Irr
  have hne := hW.nontrivial_Irr_right
  obtain ⟨j0, hj0⟩ := exists_ne (principalIrr ↥W2)
  have hnonempty : Nonempty {j : Irr ↥W2 // j ≠ principalIrr ↥W2} := ⟨⟨j0, hj0⟩⟩
  rcases Set.eq_empty_or_nonempty (S ∩ Irr ↥L) with hSirr | hSirr
  ·
    obtain ⟨ν, hνc, hνval⟩ := exists_isCoherentWith_row_family (τ := τ) (ω := ω) hW hω hδ
      (c := fun j : {j : Irr ↥W2 // j ≠ principalIrr ↥W2} => (j : Irr ↥W2))
      (fun j k h => Subtype.ext h) (hclass hSirr) hnorm horth
      (b := (n : ℤ)) (by exact_mod_cast hn.ne') (fun j => by rw [hb j]; push_cast; ring) hν0
      (fun j k => htau j k)
    refine ⟨ν, hνc, 0, Or.inl rfl, fun j => ?_, by simp, fun hc => ?_⟩
    · rw [hνval j _ rfl]; simp
    · rw [hSirr] at hc; exact absurd hc Set.not_nonempty_empty
  ·
    obtain ⟨ξ, hξS, hξIrr⟩ := hSirr
    by_cases hpos : ∃ j, (ν0 ⟨M j, Submodule.subset_span (hMS j)⟩ : G → ℂ)
        = δ • hW.prodCharEtaColSum ω (j : Irr ↥W2)
    ·
      obtain ⟨j1, hj1⟩ := hpos
      refine ⟨ν0, hν0, 0, Or.inl rfl, fun j => ?_, by simp, fun _ => rfl⟩
      have h := htau j1 j
      rw [hj1] at h
      simp only [Function.iterate_zero, id_eq, pow_zero, one_mul]
      linear_combination (norm := module) -h
    ·
      rw [not_exists] at hpos
      have hneg : ∀ j, (ν0 ⟨M j, Submodule.subset_span (hMS j)⟩ : G → ℂ)
          = (-δ) • hW.prodCharEtaColSum ω (starIrr (j : Irr ↥W2)) := fun j =>
        (eq_col_or_eq_neg_starIrr_col hodd hW hW2 hW1 hω hD hVA hS hSstar hS0 hν0 hντ hMS hnorm
          horth hb hδ htau hξS hξIrr j).resolve_left (hpos j)
      refine ⟨ν0, hν0, 1, Or.inr rfl, fun j => ?_, fun _ => ?_, fun _ => rfl⟩
      · rw [hneg j]; simp
      · refine natCard_right_eq_three (W := W) (W1 := W1) hW (j := j0) fun k hk => ?_
        refine eq_or_eq_starIrr_of_col_eq (ω := ω) hW hω hδ hj0 ?_
        have h := htau ⟨j0, hj0⟩ ⟨k, hk⟩
        rw [hneg ⟨j0, hj0⟩, hneg ⟨k, hk⟩] at h
        exact h

end Rows

end CoherentSimultaneousOrientation

end CFSG.FeitThompson

end
