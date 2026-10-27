module

public import CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.Leaf.ClosingE8TenAux7

public noncomputable section

namespace CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.E8TenAux

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.SeitzReduction
open CFSG.LieType.Steinberg.Adjoint CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.HardMathSupport.Foote.Coordinator.SplitFrame CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Heis
open CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.DetectE8

set_option linter.unusedSectionVars false


section Descent

variable {K L : Type} [Field K] [Field L] [Algebra K L] {ι : Type} {V : Type} [AddCommGroup V]
  [Module L V] [Module K V] [IsScalarTower K L V]

theorem linIndep_of_fixed (Fr : L →+* L) (hFr : ∀ a : L, Fr a = a → a ∈ Set.range (algebraMap K L))
    (σ : V → V) (hσ : ∀ (a : L) (x : V), σ (a • x) = Fr a • σ x)
    (hσa : ∀ x y : V, σ (x + y) = σ x + σ y) [Fintype ι] {b : ι → V} (hb : ∀ i, σ (b i) = b i)
    (hK : LinearIndependent K b) : LinearIndependent L b := by
  classical
  rw [Fintype.linearIndependent_iff]
  have hsum : ∀ (g : ι → L), σ (∑ i, g i • b i) = ∑ i, Fr (g i) • b i := by
    intro g
    have h0 : σ (0 : V) = 0 := by
      have := hσa 0 0
      rw [add_zero] at this
      exact add_left_cancel (a := σ 0) (by rw [add_zero]; exact this.symm)
    have key : ∀ s : Finset ι, σ (∑ i ∈ s, g i • b i) = ∑ i ∈ s, Fr (g i) • b i := by
      intro s
      induction s using Finset.induction_on with
      | empty => simpa using h0
      | insert j s hj ih =>
        rw [Finset.sum_insert hj, Finset.sum_insert hj, hσa, ih, hσ, hb]
    exact key Finset.univ
  suffices h : ∀ n : ℕ, ∀ g : ι → L, (Finset.univ.filter fun i => g i ≠ 0).card ≤ n →
      ∑ i, g i • b i = 0 → ∀ i, g i = 0 by
    intro g hg
    exact h _ g le_rfl hg
  intro n
  induction n with
  | zero =>
    intro g hcard _ i
    by_contra hne
    have : i ∈ Finset.univ.filter fun i => g i ≠ 0 := by simp [hne]
    have := Finset.card_pos.2 ⟨i, this⟩
    omega
  | succ n ih =>
    intro g hcard hg i₁
    by_contra hne
    set g' : ι → L := fun i => (g i₁)⁻¹ * g i with hg'
    have hg'1 : g' i₁ = 1 := by simp [hg', hne]
    have hg'0 : ∑ i, g' i • b i = 0 := by
      have : ∑ i, g' i • b i = (g i₁)⁻¹ • ∑ i, g i • b i := by
        rw [Finset.smul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [smul_smul]
      rw [this, hg, smul_zero]
    have hsupp : (Finset.univ.filter fun i => g' i ≠ 0) =
        (Finset.univ.filter fun i => g i ≠ 0) := by
      ext i
      simp [hg', hne]
    have hσg : ∑ i, Fr (g' i) • b i = 0 := by
      rw [← hsum, hg'0]
      have := hσa 0 0
      rw [add_zero] at this
      exact add_left_cancel (a := σ 0) (by rw [add_zero]; exact this.symm)
    set h : ι → L := fun i => Fr (g' i) - g' i with hh
    have hh0 : ∑ i, h i • b i = 0 := by
      simp only [hh, sub_smul, Finset.sum_sub_distrib, hσg, hg'0, sub_zero]
    have hhi : h i₁ = 0 := by simp [hh, hg'1]
    have hhsupp : (Finset.univ.filter fun i => h i ≠ 0).card ≤ n := by
      have hsub : (Finset.univ.filter fun i => h i ≠ 0) ⊆
          (Finset.univ.filter fun i => g' i ≠ 0).erase i₁ := by
        intro i hi
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, ne_eq, Finset.mem_erase] at hi ⊢
        refine ⟨?_, ?_⟩
        · rintro rfl
          exact hi hhi
        · intro hz
          apply hi
          simp [hh, hz]
      have hmem : i₁ ∈ Finset.univ.filter fun i => g' i ≠ 0 := by simp [hg'1]
      calc (Finset.univ.filter fun i => h i ≠ 0).card
          ≤ ((Finset.univ.filter fun i => g' i ≠ 0).erase i₁).card := Finset.card_le_card hsub
        _ = (Finset.univ.filter fun i => g' i ≠ 0).card - 1 := Finset.card_erase_of_mem hmem
        _ ≤ n := by rw [hsupp]; omega
    have hhz := ih h hhsupp hh0
    have hfix : ∀ i, g' i ∈ Set.range (algebraMap K L) := fun i => by
      apply hFr
      have := hhz i
      simp only [hh, sub_eq_zero] at this
      exact this
    choose k hk using hfix
    have hkb : ∑ i, k i • b i = 0 := by
      have : ∑ i, g' i • b i = ∑ i, k i • b i := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [← hk i, algebraMap_smul]
      rw [← this]
      exact hg'0
    have := (Fintype.linearIndependent_iff.1 hK) k hkb i₁
    have h1 : algebraMap K L (k i₁) = 1 := by rw [hk, hg'1]
    rw [this, map_zero] at h1
    exact zero_ne_one h1

theorem desc_of_fixed (Fr : L →+* L) (hFr : ∀ a : L, Fr a = a → a ∈ Set.range (algebraMap K L))
    (σ : V → V) (hσ : ∀ (a : L) (x : V), σ (a • x) = Fr a • σ x)
    (hσa : ∀ x y : V, σ (x + y) = σ x + σ y) (W : Submodule K V) (hW : ∀ w ∈ W, σ w = w)
    {c : V} (hc : c ∈ Submodule.span L (W : Set V)) (hσc : σ c = c) : c ∈ W := by
  classical
  obtain ⟨T, hTW, hcT⟩ := Submodule.mem_span_finite_of_mem_span hc
  set W₀ : Submodule K V := Submodule.span K (T : Set V) with hW₀
  have hW₀W : W₀ ≤ W := Submodule.span_le.2 hTW
  haveI : FiniteDimensional K W₀ := inferInstance
  let B := Module.finBasis K W₀
  set b : Fin (Module.finrank K W₀) → V := fun j => (B j : V) with hb
  have hbW : ∀ j, b j ∈ W := fun j => hW₀W (B j).2
  have hbfix : ∀ j, σ (b j) = b j := fun j => hW _ (hbW j)
  have hbK : LinearIndependent K b := B.linearIndependent.map' W₀.subtype W₀.ker_subtype
  have hbL : LinearIndependent L b := linIndep_of_fixed Fr hFr σ hσ hσa hbfix hbK
  have hT : (T : Set V) ⊆ (Submodule.span L (Set.range b) : Submodule L V) := by
    intro t ht
    have htW₀ : t ∈ W₀ := Submodule.subset_span ht
    have hrep := B.sum_repr ⟨t, htW₀⟩
    have h1 : ((∑ j, (B.repr ⟨t, htW₀⟩ j) • B j : W₀) : V) = t := by rw [hrep]
    rw [Submodule.coe_sum] at h1
    simp only [Submodule.coe_smul] at h1
    have : t = ∑ j, (B.repr ⟨t, htW₀⟩ j) • b j := h1.symm
    rw [this]
    refine Submodule.sum_mem _ fun j _ => ?_
    rw [← algebraMap_smul L (B.repr ⟨t, htW₀⟩ j) (b j)]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  have hcb : c ∈ Submodule.span L (Set.range b) :=
    (Submodule.span_le.2 hT) hcT
  obtain ⟨e, he⟩ := (Submodule.mem_span_range_iff_exists_fun L).1 hcb
  have hsum : σ (∑ j, e j • b j) = ∑ j, Fr (e j) • b j := by
    have h0 : σ (0 : V) = 0 := by
      have := hσa 0 0
      rw [add_zero] at this
      exact add_left_cancel (a := σ 0) (by rw [add_zero]; exact this.symm)
    have key : ∀ s : Finset (Fin (Module.finrank K W₀)),
        σ (∑ j ∈ s, e j • b j) = ∑ j ∈ s, Fr (e j) • b j := by
      intro s
      induction s using Finset.induction_on with
      | empty => simpa using h0
      | insert j s hj ih =>
        rw [Finset.sum_insert hj, Finset.sum_insert hj, hσa, ih, hσ, hbfix]
    exact key Finset.univ
  have hdiff : ∑ j, (Fr (e j) - e j) • b j = 0 := by
    simp only [sub_smul, Finset.sum_sub_distrib]
    rw [← hsum, he, hσc, sub_self]
  have hz := Fintype.linearIndependent_iff.1 hbL _ hdiff
  have hk : ∀ j, e j ∈ Set.range (algebraMap K L) := fun j => hFr _ (sub_eq_zero.1 (hz j))
  choose k hk' using hk
  have : c = ∑ j, k j • b j := by
    rw [← he]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← hk' j, algebraMap_smul]
  rw [this]
  exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (hbW j)

end Descent

section SetupDescent

variable {K : Type} [Field K] [Finite K] {L : Type} [Field L] [Algebra K L]

theorem Cc_inv {h : ModGL Tag.E8 L} {q : ModGL Tag.E8 K} (hq : q ∈ Qrat h) :
    Cc h q⁻¹ = - Cc h q := by
  have e : h⁻¹ * baseChangeGL (algebraMap K L) q⁻¹ * h =
      (h⁻¹ * baseChangeGL (algebraMap K L) q * h)⁻¹ := by
    rw [map_inv]
    group
  unfold Cc
  rw [e]
  exact heisCoord_inv hq

theorem Cc_one {h : ModGL Tag.E8 L} : Cc h (1 : ModGL Tag.E8 K) = 0 := by
  unfold Cc
  rw [map_one, mul_one, inv_mul_cancel]
  exact heisCoord_one

@[expose] def Setup.sig (S : Setup K L) (c : Fn L) : Fn L := Mg S.w S.sg (Fv S.Fr c)

theorem Setup.sig_smul (S : Setup K L) (a : L) (c : Fn L) : S.sig (a • c) = S.Fr a • S.sig c := by
  unfold Setup.sig
  rw [Fv_smul, map_smul]

theorem Setup.sig_add (S : Setup K L) (c c' : Fn L) : S.sig (c + c') = S.sig c + S.sig c' := by
  unfold Setup.sig
  rw [Fv_add, map_add]

theorem Setup.fix_mem_range (S : Setup K L) (a : L) (ha : S.Fr a = a) :
    a ∈ Set.range (algebraMap K L) := by
  rw [S.hFr] at ha
  exact mem_range_algebraMap_of_pow_card_eq ha

theorem Setup.sig_Cc (S : Setup K L) {q : ModGL Tag.E8 K} (hq : q ∈ Qrat S.h) :
    S.sig (Cc S.h q) = Cc S.h q :=
  sigma_fixed_coords (algebraMap K L) S.Fr S.hfix S.hlang S.hn q hq

@[expose] def Setup.ScalClosed (S : Setup K L) : Prop :=
  ∀ a : K, a ≠ 0 → ∃ t ∈ S.H, ∀ q ∈ Qrat (K := K) S.h, t * q * t⁻¹ ∈ Qrat (K := K) S.h ∧
    Cc S.h (t * q * t⁻¹) = algebraMap K L a • Cc S.h q

@[expose] def Setup.Wset (S : Setup K L) : Set (Fn L) :=
  {c | ∃ q ∈ S.H ⊓ Qrat (K := K) S.h, Cc S.h q = c}

theorem Setup.Uspace_eq (S : Setup K L) :
    Uspace S.h S.H = Submodule.span L (S.Wset : Set (Fn L)) := by
  unfold Uspace Setup.Wset
  rfl

@[expose] def Setup.Wsub (S : Setup K L) (hs : S.ScalClosed) : Submodule K (Fn L) where
  carrier := S.Wset
  add_mem' := by
    rintro a b ⟨q, hq, rfl⟩ ⟨q', hq', rfl⟩
    exact ⟨q * q', mul_mem hq hq', Cc_mul hq.2 hq'.2⟩
  zero_mem' := ⟨1, one_mem _, Cc_one⟩
  smul_mem' := by
    rintro a c ⟨q, hq, rfl⟩
    by_cases ha : a = 0
    · subst ha
      exact ⟨1, one_mem _, by rw [Cc_one, zero_smul]⟩
    · obtain ⟨t, htH, ht⟩ := hs a ha
      obtain ⟨htQ, htc⟩ := ht q hq.2
      have h1 : t * q * t⁻¹ ∈ S.H := S.H.mul_mem (S.H.mul_mem htH hq.1) (S.H.inv_mem htH)
      refine ⟨t * q * t⁻¹, ⟨h1, htQ⟩, ?_⟩
      rw [htc, algebraMap_smul]

theorem Setup.mem_Wset_of_Uspace (S : Setup K L) (hs : S.ScalClosed) {c : Fn L}
    (hc : c ∈ Uspace S.h S.H) (hσ : S.sig c = c) : c ∈ S.Wset := by
  refine desc_of_fixed (K := K) (L := L) S.Fr S.fix_mem_range S.sig S.sig_smul S.sig_add
    (S.Wsub hs) ?_ (c := c) ?_ hσ
  · rintro w ⟨q, hq, rfl⟩
    exact S.sig_Cc hq.2
  · rw [Setup.Uspace_eq] at hc
    exact hc

theorem Setup.mem_H_of_Uspace (S : Setup K L) (hs : S.ScalClosed)
    (hHG : S.H ≤ adjointGroup Tag.E8 K)
    (hker : ∀ l ∈ Qrat (K := K) S.h, l ∈ adjointGroup Tag.E8 K → Cc S.h l = 0 → l ∈ S.H)
    {l : ModGL Tag.E8 K} (hl : l ∈ Qrat S.h) (hladj : l ∈ adjointGroup Tag.E8 K)
    (hc : Cc S.h l ∈ Uspace S.h S.H) : l ∈ S.H := by
  obtain ⟨q, hq, hqc⟩ := S.mem_Wset_of_Uspace hs hc (S.sig_Cc hl)
  have hq2 : q ∈ Qrat (K := K) S.h := hq.2
  have hlq : l * q⁻¹ ∈ Qrat (K := K) S.h := mul_mem hl (inv_mem hq2)
  have h0 : Cc S.h (l * q⁻¹) = 0 := by
    rw [Cc_mul hl (inv_mem hq2), Cc_inv hq2, hqc, add_neg_cancel]
  have hladj' : l * q⁻¹ ∈ adjointGroup Tag.E8 K := mul_mem hladj (inv_mem (hHG hq.1))
  have := hker _ hlq hladj' h0
  have e : l = (l * q⁻¹) * q := by group
  rw [e]
  exact mul_mem this hq.1

end SetupDescent

end CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.E8TenAux
