module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.PlanesToralFive
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwCompChain
public import CFSG.RankThree.E6.NativeTwoA2
public import CFSG.HardMathSupport.Timmesfeld.Torality.A4Block

public noncomputable section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple

section Chains

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.HardMathSupport.Timmesfeld.CrossChar

variable {τ : Tag}

theorem iform_chainGram_of_isAChain (hSL : ∀ γ, IsRoot τ γ → iform γ γ = 2) {n : ℕ}
    {β : Fin n → Fin τ.rank → ℤ} (h : IsAChain β) (c d : Fin n) :
    iform (β c) (β d) = chainGram c d := by
  by_cases hcd : c = d
  · subst hcd
    simp [chainGram, hSL _ (h.isRoot c)]
  · by_cases h1 : (c : ℕ) + 1 = d
    · simp [chainGram, hcd, h1, h.adj c d h1.symm]
    · by_cases h2 : (d : ℕ) + 1 = c
      · rw [iform_comm]
        simp [chainGram, hcd, h.adj d c h2.symm, h2]
      · have hc : (c : ℕ) ≠ d := fun e => hcd (Fin.ext e)
        rcases lt_or_gt_of_ne hc with h3 | h3
        · simp [chainGram, hcd, h1, h2, h.orth c d (by omega)]
        · rw [iform_comm]
          simp [chainGram, hcd, h1, h2, h.orth d c (by omega)]

theorem chainσ_eq_sum_Icc {m : ℕ} (β : Fin m → Fin τ.rank → ℤ) {a b : Fin (m + 1)}
    (hab : a < b) : chainσ β a b =
      ∑ k ∈ Finset.Icc (⟨a, by omega⟩ : Fin m) ⟨b - 1, by omega⟩, β k := by
  classical
  have hab' : (a : ℕ) < b := hab
  rw [chainσ, chainω, chainω, ← Finset.sum_sub_distrib]
  have e : ∀ c : Fin m, ((if (c : ℕ) < b then β c else 0) - (if (c : ℕ) < a then β c else 0)) =
      if c ∈ Finset.Icc (⟨a, by omega⟩ : Fin m) ⟨b - 1, by omega⟩ then β c else 0 := by
    intro c
    simp only [Finset.mem_Icc, Fin.le_iff_val_le_val]
    by_cases h1 : (c : ℕ) < a
    · have : (c : ℕ) < b := by omega
      simp [h1, this] <;> omega
    · by_cases h2 : (c : ℕ) < b
      · simp [h1, h2] <;> omega
      · simp [h1, h2] <;> omega
  rw [Finset.sum_congr rfl fun c _ => e c, ← Finset.sum_filter]
  congr 1
  ext c
  simp [Finset.mem_Icc]

theorem chainσ_mem_aChainRoots {m : ℕ} (β : Fin m → Fin τ.rank → ℤ) {a b : Fin (m + 1)}
    (hab : a ≠ b) : chainσ β a b ∈ aChainRoots β := by
  rcases lt_or_gt_of_ne hab with h | h
  · refine ⟨⟨a, by omega⟩, ⟨b - 1, by omega⟩, ?_, Or.inl (chainσ_eq_sum_Icc β h)⟩
    have : (a : ℕ) < b := h
    exact Fin.le_iff_val_le_val.2 (by simp; omega)
  · have h' : (b : ℕ) < a := h
    refine ⟨⟨b, by omega⟩, ⟨a - 1, by omega⟩, ?_, Or.inr ?_⟩
    · exact Fin.le_iff_val_le_val.2 (by simp; omega)
    · rw [← chainσ_eq_sum_Icc β h, chainσ_neg β a b, neg_neg]

end Chains

section Frame

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.Torality
  CFSG.ClassicalInvolution.WeakCT CFSG.RankThree.PartOne.KE
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped MatrixGroups

theorem exists_diag_eq_prod_five {L : Type} [Field L] (A : SL(5, L))
    (hA : ∀ i j, i ≠ j → (A : Matrix (Fin 5) (Fin 5) L) i j = 0) :
    ∃ s : Fin 4 → Lˣ, A = blockSL2 L 4 0 (HSL (s 0)) * blockSL2 L 4 1 (HSL (s 1)) *
      blockSL2 L 4 2 (HSL (s 2)) * blockSL2 L 4 3 (HSL (s 3)) := by
  have hdiag : (A : Matrix (Fin 5) (Fin 5) L) =
      Matrix.diagonal fun i => (A : Matrix (Fin 5) (Fin 5) L) i i := by
    ext i j
    by_cases hij : i = j
    · subst hij
      simp
    · simp [hA i j hij, Matrix.diagonal_apply_ne _ hij]
  have hdet : ∏ i, (A : Matrix (Fin 5) (Fin 5) L) i i = 1 := by
    have h := A.2
    rwa [hdiag, Matrix.det_diagonal] at h
  have hne : ∀ i, (A : Matrix (Fin 5) (Fin 5) L) i i ≠ 0 := by
    intro i h0
    have : ∏ j, (A : Matrix (Fin 5) (Fin 5) L) j j = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ i) h0
    rw [hdet] at this
    exact one_ne_zero this
  set u : Fin 5 → Lˣ := fun i => Units.mk0 _ (hne i) with hu
  refine ⟨![u 0, u 0 * u 1, u 0 * u 1 * u 2, u 0 * u 1 * u 2 * u 3], ?_⟩
  apply Subtype.ext
  simp only [Matrix.SpecialLinearGroup.coe_mul, coe_blockSL2_HSL, Matrix.diagonal_mul_diagonal]
  rw [hdiag]
  congr 1
  funext i
  have h4 : (A : Matrix (Fin 5) (Fin 5) L) 4 4 = ((u 0 * u 1 * u 2 * u 3)⁻¹ : Lˣ) := by
    rw [Units.val_inv_eq_inv_val]
    refine eq_inv_of_mul_eq_one_right ?_
    rw [Fin.prod_univ_five] at hdet
    simp only [hu, Units.val_mul, Units.val_mk0]
    linear_combination hdet
  have n0 := hne 0
  have n1 := hne 1
  have n2 := hne 2
  have n3 := hne 3
  fin_cases i <;> simp [h4, hu] <;> field_simp

section Std

variable {τ : Tag}

theorem chainBlock_of_std (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {β₀ : Fin 4 → Fin τ.rank → ℤ} (hβ₀ : IsAChain β₀)
    {L : Type} [Field L] [IsAlgClosed L] (hL : ringChar L ≠ 5)
    (hθ : ∀ (c : Fin 4) (h : (c : ℕ) + 1 < 4), ∃ θ : SL(3, L) →* ModGL τ L,
      θ.comp (blockSL L 3 2 0 (by omega)) = rootSL2 τ L (β₀ c) ∧
        θ.comp (blockSL L 3 2 1 (by omega)) = rootSL2 τ L (β₀ ⟨c + 1, h⟩))
    (hcop : ∃ i, IsCoprime (chainExp β₀ 4 i) 5)
    {β : Fin 4 → Fin τ.rank → ℤ} (v : WeylGroup τ) (hv : ∀ k, v • β₀ k = β k) :
    ∃ m ∈ rootSpan τ L (aChainRoots β), ∃ hm : m ∈ monomialSubgroup τ L,
      weylQuotientHom τ L ⟨m, hm⟩ = chainRefl β ∧
      ∀ t ∈ torusGroup τ L, ∃ y ∈ rootSpan τ L (aChainRoots β),
        y * (m * t) * y⁻¹ ∈ torusGroup τ L := by
  have hSL : ∀ γ, IsRoot τ γ → iform γ γ = 2 := fun γ hγ =>
    EvenOddRadical.iform_self_eq_two hτ hγ
  have hG := iform_chainGram_of_isAChain hSL hβ₀
  obtain ⟨ψ, hψ⟩ := exists_chainHom hτ β₀ hβ₀.isRoot hG hθ
  have hSLF : IsSLFrame ψ (chainσ β₀) := isSLFrame_chainHom hτ hβ₀.isRoot hG hψ
  have hcenter : ∀ ζ : Lˣ, ζ ^ (4 + 1) = 1 → (∀ i, ζ ^ chainExp β₀ 4 i = 1) → ζ = 1 := by
    obtain ⟨i, a, b, hab⟩ := hcop
    intro ζ h5 hn
    have h5' : ζ ^ (5 : ℤ) = 1 := by simpa using h5
    have : ζ = ζ ^ (a * chainExp β₀ 4 i + b * 5) := by rw [hab, zpow_one]
    rw [this, zpow_add, zpow_mul', zpow_mul', hn i, h5']
    simp
  have hinj : Function.Injective ψ :=
    chainHom_injective hτ hβ₀.isRoot hG hψ (by norm_num) hcenter
  have hdiag : ∀ A : SL(5, L), (∀ i j, i ≠ j → (A : Matrix (Fin 5) (Fin 5) L) i j = 0) →
      ψ A ∈ torusGroup τ L := by
    intro A hA
    obtain ⟨s, rfl⟩ := exists_diag_eq_prod_five A hA
    simp only [map_mul]
    have hb : ∀ (c : Fin 4) (s : Lˣ), ψ (blockSL2 L 4 c (HSL s)) ∈ torusGroup τ L :=
      fun c s => by
        rw [← MonoidHom.comp_apply, hψ]
        exact rootSL2_HSL_mem_torusGroup (hβ₀.isRoot c) s
    exact mul_mem (mul_mem (mul_mem (hb 0 _) (hb 1 _)) (hb 2 _)) (hb 3 _)
  set ρ : SL(5, L) →* ModGL τ L :=
    (MulAut.conj (canonicalRep (coxeterSystem τ) L v)).toMonoidHom.comp ψ with hρ
  have hSLF' : IsSLFrame ρ (fun i j => v • chainσ β₀ i j) := hSLF.transport v
  have hfr : IsA4Frame ρ (fun i j => v • chainσ β₀ i j) :=
    { injective := (MulAut.conj _).injective.comp hinj
      isRoot := hSLF'.isRoot
      neg := hSLF'.neg
      add := hSLF'.add
      transv := hSLF'.transv
      range := hSLF'.range
      torus := fun b => hSLF'.exists_torus (by norm_num) b
      diag := fun A hA => by
        have hH := hdiag A hA
        simp only [hρ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        exact (Subgroup.mem_normalizer_iff.1 (canonicalRep_mem_normalizer v) _).1 hH }
  obtain ⟨m, hmS, hm, hmρ, hmt⟩ := a4BlockAt_of_frame hL hfr
  have hω : ∀ k, v • chainω β₀ k = chainω β k := by
    intro k
    simp only [chainω, Finset.smul_sum, smul_ite, smul_zero, hv]
  have hσ : ∀ a b, v • chainσ β₀ a b = chainσ β a b := fun a b => by
    rw [chainσ, chainσ, smul_sub, hω, hω]
  have hsub : rootSpan τ L (frameRoots5 (fun i j => v • chainσ β₀ i j)) ≤
      rootSpan τ L (aChainRoots β) := by
    refine biSup_mono ?_
    rintro r ⟨i, j, hij, rfl⟩
    show v • chainσ β₀ i j ∈ aChainRoots β
    rw [hσ]
    exact chainσ_mem_aChainRoots β hij
  refine ⟨m, hsub hmS, hm, ?_, fun t ht => ?_⟩
  · rw [hmρ, chainRefl_four]
    have e0 : chainσ β 0 1 = β 0 := chainσ_castSucc_succ β 0
    have e1 : chainσ β 1 2 = β 1 := chainσ_castSucc_succ β 1
    have e2 : chainσ β 2 3 = β 2 := chainσ_castSucc_succ β 2
    have e3 : chainσ β 3 4 = β 3 := chainσ_castSucc_succ β 3
    simp only [hσ, e0, e1, e2, e3]
  · obtain ⟨y, hy, hyt⟩ := hmt t ht
    exact ⟨y, hsub hy, hyt⟩

end Std

end Frame

section Tables

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.RankThree.Lattice CFSG.HardMathSupport.Timmesfeld.CrossChar

variable {τ : Tag}

@[expose] def fiveLvec (τ : Tag) (l : List ℤ) : Fin τ.rank → ℤ := fun i => l.getD i 0

@[expose] def fiveRootAt (τ : Tag) (k : ℕ) : Fin τ.rank → ℤ :=
  fiveLvec τ (τ.artifactRoots.getD k [])

@[expose] def fiveReflWord (τ : Tag) (ws : List ℕ) (v : Fin τ.rank → ℤ) : Fin τ.rank → ℤ :=
  ws.foldr (fun g v => v - corootPair (fiveRootAt τ g) v • fiveRootAt τ g) v

@[expose] def ChainCand (τ : Tag) (s : Fin 4 → Fin τ.rank → ℤ) (k : Fin 4)
    (t : Fin τ.rank → ℤ) : Prop :=
  ∀ j : Fin 4, j < k → iform t (s j) = if j.val + 1 = k.val then -1 else 0

instance (s : Fin 4 → Fin τ.rank → ℤ) (k : Fin 4) (t : Fin τ.rank → ℤ) :
    Decidable (ChainCand τ s k t) := by
  unfold ChainCand; infer_instance

@[expose] def ChainTabOK (τ : Tag) (N : ℕ) (s : Fin 4 → Fin τ.rank → ℤ)
    (tab : Fin 4 → List (ℕ × List ℕ)) (k : Fin 4) : Prop :=
  ∀ ia : Fin N, ChainCand τ s k (fiveRootAt τ ia) →
    ∃ e ∈ tab k, e.1 = ia ∧ (∀ i ∈ e.2, i < N ∧ ∀ j : Fin 4, j < k →
        iform (fiveRootAt τ i) (s j) = 0) ∧ fiveReflWord τ e.2 (s k) = fiveRootAt τ ia

section

variable {N : ℕ}
  (hN : τ.artifactRoots.length = N)

include hN in
theorem exists_rvecAt_of_isRoot {t : Fin τ.rank → ℤ} (ht : IsRoot τ t) :
    ∃ ia : Fin N, fiveRootAt τ ia = t := by
  have h1 := (isRoot_iff_mem_artifactRoots (τ := τ)).1 ht
  obtain ⟨k, hk, hkt⟩ := List.mem_iff_getElem.1 h1
  refine ⟨⟨k, by omega⟩, ?_⟩
  rw [fiveRootAt, List.getD_eq_getElem _ _ hk, hkt]
  funext i
  simp [fiveLvec]

include hN in
theorem isRoot_rvecAt {k : ℕ} (hk : k < N) : IsRoot τ (fiveRootAt τ k) := by
  have hmem : τ.artifactRoots.getD k [] ∈ τ.artifactRoots := by
    rw [List.getD_eq_getElem _ _ (by omega)]
    exact List.getElem_mem _
  rw [isRoot_iff_mem_artifactRoots, fiveRootAt]
  generalize τ.artifactRoots.getD k [] = l at hmem ⊢
  have hl := length_of_mem_artifactRoots hmem
  have : List.ofFn (fiveLvec τ l) = l := by
    refine List.ext_getElem (by simp [hl]) fun i h1 h2 => ?_
    simp [fiveLvec, List.getD_eq_getElem?_getD, h2]
  rw [this]
  exact hmem

@[expose] def refProd (τ : Tag) (ws : List ℕ) : WeylGroup τ :=
  (ws.map fun g => rootReflection (fiveRootAt τ g)).prod

include hN in
theorem refProd_smul {ws : List ℕ} (hws : ∀ g ∈ ws, g < N) (v : Fin τ.rank → ℤ) :
    refProd τ ws • v = fiveReflWord τ ws v := by
  induction ws with
  | nil => simp [refProd, fiveReflWord]
  | cons g ws ih =>
    have hg : g < N := hws g (by simp)
    have ih' := ih (fun x hx => hws x (by simp [hx]))
    simp only [refProd, List.map_cons, List.prod_cons] at ih' ⊢
    rw [mul_smul, ih', rootReflection_smul (isRoot_rvecAt hN hg)]
    rfl

include hN in
theorem refProd_fix {x : Fin τ.rank → ℤ} {ws : List ℕ}
    (hws : ∀ g ∈ ws, g < N ∧ iform (fiveRootAt τ g) x = 0) : refProd τ ws • x = x := by
  induction ws with
  | nil => simp [refProd]
  | cons g ws ih =>
    have hg := hws g (by simp)
    have ih' := ih (fun y hy => hws y (by simp [hy]))
    simp only [refProd, List.map_cons, List.prod_cons] at ih' ⊢
    rw [mul_smul, ih', rootReflection_smul_of_iform_eq_zero (isRoot_rvecAt hN hg.1) hg.2]

include hN in
theorem chain_step_of_word {s : Fin 4 → Fin τ.rank → ℤ} {k : Fin 4} {ws : List ℕ}
    {x : Fin τ.rank → ℤ}
    (hws : ∀ g ∈ ws, g < N ∧ ∀ j : Fin 4, j < k → iform (fiveRootAt τ g) (s j) = 0)
    (happ : fiveReflWord τ ws (s k) = x) :
    ∃ u : WeylGroup τ, (∀ j : Fin 4, j < k → u • s j = s j) ∧ u • s k = x :=
  ⟨refProd τ ws, fun j hj => refProd_fix hN fun g hg => ⟨(hws g hg).1, (hws g hg).2 j hj⟩, by
    rw [refProd_smul hN fun g hg => (hws g hg).1, happ]⟩

include hN in
theorem chain_level_step {s : Fin 4 → Fin τ.rank → ℤ} {tab : Fin 4 → List (ℕ × List ℕ)}
    {k : Fin 4} (hk : ChainTabOK τ N s tab k) {t : Fin τ.rank → ℤ} (ht : IsRoot τ t)
    (hc : ChainCand τ s k t) :
    ∃ u : WeylGroup τ, (∀ j : Fin 4, j < k → u • s j = s j) ∧ u • s k = t := by
  obtain ⟨ia, rfl⟩ := exists_rvecAt_of_isRoot hN ht
  obtain ⟨e, he, he1, hwords, happ⟩ := hk ia hc
  exact chain_step_of_word hN hwords happ

end

instance (N : ℕ) (s : Fin 4 → Fin τ.rank → ℤ) (tab : Fin 4 → List (ℕ × List ℕ)) (k : Fin 4) :
    Decidable (ChainTabOK τ N s tab k) := by
  unfold ChainTabOK; infer_instance

section

variable {N : ℕ}

theorem chain_gram_of_isAChain {γ : Fin 4 → Fin τ.rank → ℤ} (h : IsAChain γ) (j k : Fin 4)
    (hjk : j < k) : iform (γ k) (γ j) = if j.val + 1 = k.val then -1 else 0 := by
  rw [iform_comm]
  split_ifs with h1
  · exact h.adj j k h1.symm
  · exact h.orth j k (by have : j.val < k.val := hjk; omega)

theorem exists_weyl_prefix (hN : τ.artifactRoots.length = N)
    {s : Fin 4 → Fin τ.rank → ℤ} {tab : Fin 4 → List (ℕ × List ℕ)}
    {β : Fin 4 → Fin τ.rank → ℤ} (n : ℕ) (hn : n ≤ 4)
    (hroot : ∀ k : Fin 4, k.val < n → IsRoot τ (β k))
    (hgram : ∀ j k : Fin 4, j < k → k.val < n →
      iform (β k) (β j) = if j.val + 1 = k.val then -1 else 0)
    (htab : ∀ k : Fin 4, k.val < n → ChainTabOK τ N s tab k) :
    ∃ v : WeylGroup τ, ∀ j : Fin 4, j.val < n → v • s j = β j := by
  induction n with
  | zero => exact ⟨1, fun j hj => absurd hj (by omega)⟩
  | succ n ih =>
    obtain ⟨v, hv⟩ := ih (by omega) (fun k hk => hroot k (by omega))
      (fun j k hjk hk => hgram j k hjk (by omega)) (fun k hk => htab k (by omega))
    set k : Fin 4 := ⟨n, by omega⟩ with hk
    have hkn : k.val < n + 1 := by simp [hk]
    have htroot : IsRoot τ (v⁻¹ • β k) := IsRoot.smul (hroot k hkn) v⁻¹
    have hcand : ChainCand τ s k (v⁻¹ • β k) := by
      intro j hj
      have hjn : j.val < n := hj
      have h1 : iform (v⁻¹ • β k) (s j) = iform (β k) (β j) := by
        rw [← hv j hjn, ← iform_smul v (v⁻¹ • β k), smul_inv_smul]
      rw [h1, hgram j k hj hkn]
    obtain ⟨u, hu1, hu2⟩ := chain_level_step hN (htab k hkn) htroot hcand
    refine ⟨v * u, fun j hj => ?_⟩
    by_cases hjn : j.val < n
    · rw [mul_smul, hu1 j hjn, hv j hjn]
    · have : j = k := Fin.ext (by simp [hk]; omega)
      subst this
      rw [mul_smul, hu2, smul_inv_smul]

theorem exists_weyl_chain_prefix (hN : τ.artifactRoots.length = N)
    {s : Fin 4 → Fin τ.rank → ℤ} {tab : Fin 4 → List (ℕ × List ℕ)}
    {β : Fin 4 → Fin τ.rank → ℤ} (hβ : IsAChain β) (n : ℕ) (hn : n ≤ 4)
    (htab : ∀ k : Fin 4, k.val < n → ChainTabOK τ N s tab k) :
    ∃ v : WeylGroup τ, ∀ j : Fin 4, j.val < n → v • s j = β j :=
  exists_weyl_prefix hN n hn (fun k _ => hβ.isRoot k)
    (fun j k hjk _ => chain_gram_of_isAChain hβ j k hjk) htab

theorem exists_weyl_pair_of_tables (hN : τ.artifactRoots.length = N)
    {s : Fin 4 → Fin τ.rank → ℤ} {tab : Fin 4 → List (ℕ × List ℕ)}
    (htab : ∀ k : Fin 4, k.val < 2 → ChainTabOK τ N s tab k) {α γ : Fin τ.rank → ℤ}
    (hα : IsRoot τ α) (hγ : IsRoot τ γ) (hαγ : iform γ α = -1) :
    ∃ v : WeylGroup τ, v • s 0 = α ∧ v • s 1 = γ := by
  obtain ⟨v, hv⟩ := exists_weyl_prefix hN (s := s) (tab := tab) (β := ![α, γ, α, α]) 2
    (by omega)
    (fun k hk => by
      fin_cases k
      · exact hα
      · exact hγ
      · exact absurd hk (by simp)
      · exact absurd hk (by simp))
    (fun j k hjk hk => by
      fin_cases j <;> fin_cases k <;> simp_all [Fin.lt_def])
    htab
  exact ⟨v, hv 0 (by simp), hv 1 (by simp)⟩

theorem exists_weyl_chain_of_tables (hN : τ.artifactRoots.length = N)
    {s : Fin 4 → Fin τ.rank → ℤ} {tab : Fin 4 → List (ℕ × List ℕ)}
    (htab : ∀ k : Fin 4, ChainTabOK τ N s tab k) {β : Fin 4 → Fin τ.rank → ℤ}
    (hβ : IsAChain β) : ∃ v : WeylGroup τ, ∀ k : Fin 4, v • s k = β k := by
  obtain ⟨v, hv⟩ := exists_weyl_chain_prefix hN hβ 4 le_rfl (fun k _ => htab k)
  exact ⟨v, fun k => hv k k.2⟩

end

end Tables

section E7

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.RankThree.Lattice CFSG.HardMathSupport.Timmesfeld.CrossChar

@[expose] def e7FiveChain : Fin 4 → Fin Tag.E7.rank → ℤ :=
  ![Pi.single 0 1, Pi.single 2 1, Pi.single 3 1, Pi.single 4 1]

@[expose] def e7ChainTab0 : List (ℕ × List ℕ) :=
  [(0, [32, 0]), (1, [0]), (2, [52, 0]), (3, [51, 0]), (4, [50, 0]), (5, [49, 0]), (6, [48, 0]),
   (7, [42, 0]), (8, [41, 0]), (9, [40, 0]), (10, [39, 0]), (11, [38, 0]), (12, [37, 0]),
   (13, [36, 0]), (14, [35, 0]), (15, [34, 0]), (16, [33, 0]), (17, [32, 17]), (18, [32, 18]),
   (19, [32, 19]), (20, [32, 20]), (21, [32, 21]), (22, [32, 22]), (23, [32, 23]),
   (24, [32, 24]), (25, [32, 25]), (26, [32, 26]), (27, [32, 27]), (28, [32, 28]),
   (29, [32, 29]), (30, [32, 30]), (31, [32, 31]), (32, [32]), (33, [17]), (34, [18]),
   (35, [19]), (36, [20]), (37, [21]), (38, [22]), (39, [23]), (40, [24]), (41, [25]),
   (42, [26]), (43, [49, 17]), (44, [48, 17]), (45, [48, 18]), (46, [48, 20]), (47, [48, 23]),
   (48, [27]), (49, [28]), (50, [29]), (51, [30]), (52, [31]), (53, [40, 17]), (54, [39, 17]),
   (55, [39, 18]), (56, [39, 20]), (57, [37, 17]), (58, [36, 17]), (59, [36, 18]),
   (60, [35, 17]), (61, [34, 17]), (62, [35, 18]), (63, [34, 19]), (64, [33, 18]),
   (65, [33, 19]), (66, [34, 20]), (67, [33, 20]), (68, [33, 21]), (69, [36, 23]),
   (70, [34, 23]), (71, [33, 23]), (72, [33, 24]), (73, [52, 31]), (74, [51, 30]),
   (75, [50, 29]), (76, [49, 28]), (77, [48, 27]), (78, [39, 27]), (79, [36, 27]),
   (80, [34, 27]), (81, [33, 27]), (82, [33, 28]), (83, [42, 26]), (84, [41, 25]),
   (85, [40, 24]), (86, [39, 23]), (87, [38, 22]), (88, [37, 21]), (89, [36, 20]),
   (90, [35, 19]), (91, [34, 18]), (92, [33, 17]), (93, []), (94, [52]), (95, [51]), (96, [50]),
   (97, [49]), (98, [48]), (99, [42]), (100, [41]), (101, [40]), (102, [39]), (103, [38]),
   (104, [37]), (105, [36]), (106, [35]), (107, [34]), (108, [33]), (109, [17, 1]),
   (110, [18, 1]), (111, [19, 1]), (112, [20, 1]), (113, [21, 1]), (114, [22, 1]),
   (115, [23, 1]), (116, [24, 1]), (117, [25, 1]), (118, [26, 1]), (119, [27, 1]),
   (120, [28, 1]), (121, [29, 1]), (122, [30, 1]), (123, [31, 1]), (124, [1, 0]), (125, [1])]

@[expose] def e7ChainTab1 : List (ℕ × List ℕ) :=
  [(0, [16, 11]), (17, [11]), (18, [12]), (19, [13]), (20, [14]), (21, [15]), (22, [16]),
   (23, [54, 11]), (24, [53, 11]), (25, [53, 12]), (26, [53, 14]), (27, [44, 11]),
   (28, [43, 11]), (29, [43, 12]), (30, [43, 14]), (31, [16, 11, 2]), (73, []), (74, [56]),
   (75, [55]), (76, [54]), (77, [53]), (83, [46]), (84, [45]), (85, [44]), (86, [43]),
   (87, [11, 2]), (88, [12, 2]), (89, [13, 2]), (90, [14, 2]), (91, [15, 2]), (92, [16, 2]),
   (124, [2])]

@[expose] def e7ChainTab2 : List (ℕ × List ℕ) :=
  [(11, [8]), (12, [9]), (13, [10]), (14, [58, 8]), (15, [57, 8]), (16, [57, 9]), (69, []),
   (70, [59]), (71, [58]), (72, [57]), (79, [47]), (80, [8, 3]), (81, [9, 3]), (82, [10, 3]),
   (123, [3])]

@[expose] def e7ChainTab3 : List (ℕ × List ℕ) :=
  [(8, [7]), (9, [61, 7]), (10, [60, 7]), (66, []), (67, [61]), (68, [60]), (78, [7, 4]),
   (122, [4])]

@[expose] def e7ChainTab (k : Fin 4) : List (ℕ × List ℕ) :=
  match k with
  | 0 => e7ChainTab0
  | 1 => e7ChainTab1
  | 2 => e7ChainTab2
  | 3 => e7ChainTab3

set_option maxRecDepth 100000 in
theorem e7ChainTab_ok : ∀ k : Fin 4, ChainTabOK Tag.E7 126 e7FiveChain e7ChainTab k := by
  decide +kernel

theorem iform_e7FiveChain (j k : Fin 4) : iform (e7FiveChain j) (e7FiveChain k) =
    if j = k then 2 else if (j : ℕ) + 1 = k ∨ (k : ℕ) + 1 = j then -1 else 0 := by
  revert j k
  decide +kernel

theorem chainExp_e7FiveChain : chainExp e7FiveChain 4 5 = -4 := by
  decide +kernel

section


theorem isAChain_e7FiveChain : IsAChain e7FiveChain where
  isRoot i := by
    fin_cases i <;> exact IsRoot.basis _
  adj i j h := by
    rw [iform_e7FiveChain]
    have hij : i ≠ j := fun e => by subst e; omega
    rw [if_neg hij, if_pos (Or.inl h.symm)]
  orth i j h := by
    rw [iform_e7FiveChain]
    have hij : i ≠ j := fun e => by subst e; omega
    have h1 : ¬ ((i : ℕ) + 1 = j ∨ (j : ℕ) + 1 = i) := by omega
    rw [if_neg hij, if_neg h1]

theorem exists_weyl_chain_E7 {β : Fin 4 → Fin Tag.E7.rank → ℤ} (hβ : IsAChain β) :
    ∃ v : WeylGroup Tag.E7, ∀ k : Fin 4, v • e7FiveChain k = β k :=
  exists_weyl_chain_of_tables (show Tag.E7.artifactRoots.length = 126 from
    Tag.length_artifactRoots Tag.E7) e7ChainTab_ok hβ

end

section Frames

open CFSG.RankThree.PartOne.KE CFSG.RankThree.PartOne.KF4 CFSG.ClassicalInvolution.WeakCT
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.HardMathSupport.Timmesfeld.Torality
open scoped MatrixGroups


theorem e7FiveFrame {L : Type} [Field L] : IsA2Frame (rhoSigma L 1) (sigmaRoot 1) where
  injective := rhoSigma_injective 1
  isRoot _ _ hij := isRoot_sigmaRoot 1 hij
  neg i j := (sigmaRoot_neg 1 i j).symm
  add := sigmaRoot_add 1
  transv := rhoSigma_transvection 1
  range := by rw [rhoSigma_range, sigmaSet_eq]
  diag := rhoSigma_diagonal 1

theorem e7FiveRoot01 : sigmaRoot 1 0 1 = (Pi.single 0 1 : Fin Tag.E7.rank → ℤ) := by
  rw [sigmaRoot_eq_smul, one_smul, chainRoot13_values.1]
  rfl

theorem e7FiveRoot12 : sigmaRoot 1 1 2 = (Pi.single 2 1 : Fin Tag.E7.rank → ℤ) := by
  rw [sigmaRoot_eq_smul, one_smul, chainRoot13_values.2.1]
  rfl

theorem e7FiveFrames {L : Type} [Field L] {β₀ : Fin 4 → Fin Tag.E7.rank → ℤ}
    (hβ₀ : IsAChain β₀) (c : Fin 4) (h : (c : ℕ) + 1 < 4) :
    ∃ θ : SL(3, L) →* ModGL Tag.E7 L,
      θ.comp (blockSL L 3 2 0 (by omega)) = rootSL2 Tag.E7 L (β₀ c) ∧
        θ.comp (blockSL L 3 2 1 (by omega)) = rootSL2 Tag.E7 L (β₀ ⟨c + 1, h⟩) := by
  have hN : Tag.E7.artifactRoots.length = 126 := Tag.length_artifactRoots Tag.E7
  have hadj : iform (β₀ ⟨c + 1, h⟩) (β₀ c) = -1 := by
    rw [iform_comm]
    exact hβ₀.adj c ⟨c + 1, h⟩ rfl
  obtain ⟨v, hv0, hv2⟩ := exists_weyl_pair_of_tables hN (s := e7FiveChain) (tab := e7ChainTab)
    (fun k _ => e7ChainTab_ok k) (hβ₀.isRoot c) (hβ₀.isRoot _) hadj
  obtain ⟨θ, h1, h2⟩ := exists_normalized_a2Frame ((e7FiveFrame (L := L)).transport v)
  refine ⟨θ, ?_, ?_⟩
  · rw [h1]
    show rootSL2 Tag.E7 L (v • sigmaRoot 1 0 1) = _
    rw [e7FiveRoot01]
    exact congrArg _ hv0
  · rw [h2]
    show rootSL2 Tag.E7 L (v • sigmaRoot 1 1 2) = _
    rw [e7FiveRoot12]
    exact congrArg _ hv2

theorem chainBlockToral_E7_four : ChainBlockToral Tag.E7 4 := by
  intro L _ _ hL β hβ
  obtain ⟨v, hv⟩ := exists_weyl_chain_E7 hβ
  exact chainBlock_of_std (Or.inr (Or.inr (Or.inl rfl))) isAChain_e7FiveChain hL
    (fun c h => e7FiveFrames isAChain_e7FiveChain c h)
    ⟨5, by rw [chainExp_e7FiveChain]; exact ⟨1, 1, by norm_num⟩⟩ v hv

theorem monomialToralAt_E7_five : MonomialToralAt Tag.E7 5 :=
  monomialToralAt_five_of_chainBlock
    (fun _ hγ => EvenOddRadical.iform_self_eq_two (Or.inr (Or.inr (Or.inl rfl))) hγ)
    chainBlockToral_E7_four

end Frames

end E7

section E6

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.RankThree.Lattice CFSG.HardMathSupport.Timmesfeld.CrossChar

@[expose] def e6FiveChain : Fin 4 → Fin Tag.E6.rank → ℤ :=
  ![Pi.single 0 1, Pi.single 2 1, Pi.single 3 1, Pi.single 4 1]

@[expose] def e6FiveChainRev : Fin 4 → Fin Tag.E6.rank → ℤ :=
  ![Pi.single 4 1, Pi.single 3 1, Pi.single 2 1, Pi.single 0 1]

@[expose] def e6ChainTab0 : List (ℕ × List ℕ) :=
  [(0, [10, 5]), (1, [13, 5]), (2, [14, 5]), (3, [14, 6]), (4, [14, 7]), (5, [15, 5]),
   (6, [15, 6]), (7, [15, 7]), (8, [15, 8]), (9, [15, 9]), (10, [15, 10]), (11, [15, 11]),
   (12, [15, 12]), (13, [15, 13]), (14, [15, 14]), (15, [15]), (16, [5]), (17, [6]), (18, [7]),
   (19, [8]), (20, [9]), (21, [10]), (22, [27, 5]), (23, [26, 5]), (24, [26, 6]), (25, [26, 8]),
   (26, [11]), (27, [12]), (28, [13]), (29, [14]), (30, [20, 5]), (31, [19, 5]), (32, [19, 6]),
   (33, [18, 5]), (34, [17, 5]), (35, [18, 6]), (36, [17, 7]), (37, [16, 6]), (38, [16, 7]),
   (39, [17, 8]), (40, [16, 8]), (41, [16, 9]), (42, [29, 14]), (43, [28, 13]), (44, [27, 12]),
   (45, [26, 11]), (46, [19, 11]), (47, [17, 11]), (48, [16, 11]), (49, [16, 12]),
   (50, [21, 10]), (51, [20, 9]), (52, [19, 8]), (53, [18, 7]), (54, [17, 6]), (55, [16, 5]),
   (56, []), (57, [29]), (58, [28]), (59, [27]), (60, [26]), (61, [21]), (62, [20]), (63, [19]),
   (64, [18]), (65, [17]), (66, [16]), (67, [29, 18]), (68, [29, 17]), (69, [29, 16]),
   (70, [28, 16]), (71, [21, 16])]

@[expose] def e6ChainTab1 : List (ℕ × List ℕ) :=
  [(5, [2]), (6, [3]), (7, [4]), (8, [31, 2]), (9, [30, 2]), (10, [30, 3]), (11, [23, 2]),
   (12, [22, 2]), (13, [22, 3]), (14, [31, 22, 2]), (42, []), (43, [32]), (44, [31]), (45, [30]),
   (50, [24]), (51, [23]), (52, [22]), (53, [32, 23]), (54, [32, 22]), (55, [31, 22])]

@[expose] def e6ChainTab2 : List (ℕ × List ℕ) :=
  [(2, [1]), (3, [34, 1]), (4, [33, 1]), (39, []), (40, [34]), (41, [33]), (47, [25]),
   (48, [34, 25]), (49, [33, 25])]

@[expose] def e6ChainTab3 : List (ℕ × List ℕ) :=
  [(37, []), (38, [35])]

@[expose] def e6SpecTab : List (ℕ × List ℕ) :=
  [(1, [46, 39, 37, 42, 39, 56, 42, 46, 39, 37, 36, 56, 42, 39, 37, 46, 39, 42, 56]),
   (46, [37, 39, 42, 46, 39, 37, 56, 42, 39, 46])]

@[expose] def e6ChainTab (k : Fin 4) : List (ℕ × List ℕ) :=
  match k with
  | 0 => e6ChainTab0
  | 1 => e6ChainTab1
  | 2 => e6ChainTab2
  | 3 => e6ChainTab3

set_option maxRecDepth 100000 in
theorem e6ChainTab_ok : ∀ k : Fin 4, k.val < 3 → ChainTabOK Tag.E6 72 e6FiveChain e6ChainTab k := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem e6Level3 : ∀ ia : Fin 72, ChainCand Tag.E6 e6FiveChain 3 (fiveRootAt Tag.E6 ia) →
    (∃ e ∈ e6ChainTab 3, e.1 = ia ∧ (∀ i ∈ e.2, i < 72 ∧ ∀ j : Fin 4, j < 3 →
        iform (fiveRootAt Tag.E6 i) (e6FiveChain j) = 0) ∧
          fiveReflWord Tag.E6 e.2 (e6FiveChain 3) = fiveRootAt Tag.E6 ia) ∨
    (∃ e ∈ e6SpecTab, e.1 = ia ∧ (∀ i ∈ e.2, i < 72) ∧
      (∀ j : Fin 4, j < 3 → fiveReflWord Tag.E6 e.2 (e6FiveChainRev j) = e6FiveChain j) ∧
        fiveReflWord Tag.E6 e.2 (e6FiveChainRev 3) = fiveRootAt Tag.E6 ia) := by
  decide +kernel

theorem iform_e6FiveChain (j k : Fin 4) : iform (e6FiveChain j) (e6FiveChain k) =
    if j = k then 2 else if (j : ℕ) + 1 = k ∨ (k : ℕ) + 1 = j then -1 else 0 := by
  revert j k
  decide +kernel

theorem iform_e6FiveChainRev (j k : Fin 4) : iform (e6FiveChainRev j) (e6FiveChainRev k) =
    if j = k then 2 else if (j : ℕ) + 1 = k ∨ (k : ℕ) + 1 = j then -1 else 0 := by
  revert j k
  decide +kernel

theorem chainExp_e6FiveChain : chainExp e6FiveChain 4 5 = -4 := by
  decide +kernel

theorem chainExp_e6FiveChainRev : chainExp e6FiveChainRev 4 1 = -2 := by
  decide +kernel

section


theorem isAChain_e6FiveChain : IsAChain e6FiveChain where
  isRoot i := by
    fin_cases i <;> exact IsRoot.basis _
  adj i j h := by
    rw [iform_e6FiveChain]
    have hij : i ≠ j := fun e => by subst e; omega
    rw [if_neg hij, if_pos (Or.inl h.symm)]
  orth i j h := by
    rw [iform_e6FiveChain]
    have hij : i ≠ j := fun e => by subst e; omega
    have h1 : ¬ ((i : ℕ) + 1 = j ∨ (j : ℕ) + 1 = i) := by omega
    rw [if_neg hij, if_neg h1]

theorem isAChain_e6FiveChainRev : IsAChain e6FiveChainRev where
  isRoot i := by
    fin_cases i <;> exact IsRoot.basis _
  adj i j h := by
    rw [iform_e6FiveChainRev]
    have hij : i ≠ j := fun e => by subst e; omega
    rw [if_neg hij, if_pos (Or.inl h.symm)]
  orth i j h := by
    rw [iform_e6FiveChainRev]
    have hij : i ≠ j := fun e => by subst e; omega
    have h1 : ¬ ((i : ℕ) + 1 = j ∨ (j : ℕ) + 1 = i) := by omega
    rw [if_neg hij, if_neg h1]

theorem exists_weyl_chain_E6 {β : Fin 4 → Fin Tag.E6.rank → ℤ} (hβ : IsAChain β) :
    (∃ v : WeylGroup Tag.E6, ∀ k : Fin 4, v • e6FiveChain k = β k) ∨
      ∃ v : WeylGroup Tag.E6, ∀ k : Fin 4, v • e6FiveChainRev k = β k := by
  have hN : Tag.E6.artifactRoots.length = 72 := Tag.length_artifactRoots Tag.E6
  obtain ⟨v, hv⟩ := exists_weyl_chain_prefix hN hβ 3 (by omega) fun k hk => e6ChainTab_ok k hk
  have hcand : ChainCand Tag.E6 e6FiveChain 3 (v⁻¹ • β 3) := by
    intro j hj
    have hjn : j.val < 3 := hj
    have h1 : iform (v⁻¹ • β 3) (e6FiveChain j) = iform (β 3) (β j) := by
      rw [← hv j hjn, ← iform_smul v (v⁻¹ • β 3), smul_inv_smul]
    rw [h1, chain_gram_of_isAChain hβ j 3 hj]
  obtain ⟨ia, hia⟩ := exists_rvecAt_of_isRoot hN (IsRoot.smul (hβ.isRoot 3) v⁻¹)
  rw [← hia] at hcand
  rcases e6Level3 ia hcand with ⟨e, he, he1, hwords, happ⟩ | ⟨e, he, he1, hw, hs, happ⟩
  · left
    obtain ⟨u, hu1, hu2⟩ := chain_step_of_word hN hwords happ
    refine ⟨v * u, fun j => ?_⟩
    by_cases hjn : j.val < 3
    · rw [mul_smul, hu1 j hjn, hv j hjn]
    · have : j = 3 := Fin.ext (by omega)
      subst this
      rw [mul_smul, hu2, hia, smul_inv_smul]
  · right
    refine ⟨v * refProd Tag.E6 e.2, fun j => ?_⟩
    rw [mul_smul, refProd_smul hN hw]
    by_cases hjn : j.val < 3
    · rw [hs j hjn, hv j hjn]
    · have : j = 3 := Fin.ext (by omega)
      subst this
      rw [happ, hia, smul_inv_smul]

end

section Frames

open CFSG.RankThree.PartOne.KF4 CFSG.ClassicalInvolution.WeakCT
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.HardMathSupport.Timmesfeld.Torality
open CFSG.RankThree.E6 (chain13 chain134 chainRoot support13 e6Index e6RootVec mem_support13
  isRoot_iff_exists_e6RootVec chainRoot_swap a2Equiv₁ a2Mat₁ coe_a2Rep₁ a2Equiv₁_apply
  e6TorusPair e6TorusPair_mem_subsystemGroup e6TorusPair_mem_torusGroup a2Mat₁_torus
  chainRoot134_mem_parabolicRoots a3RootFamily_all)
open Matrix
open scoped MatrixGroups

theorem e6FiveCastSucc : ∀ i j : Fin 3,
    chainRoot chain134 (Fin.castSucc i) (Fin.castSucc j) = chainRoot chain13 i j := by
  decide +kernel

theorem e6FiveRoot13_apply : ∀ i j : Fin 3, ∀ l : Fin Tag.E6.rank, l ∉ support13 →
    chainRoot chain13 i j l = 0 := by
  intro i j l hl
  simp only [chainRoot]
  refine Finset.sum_eq_zero fun k _ => ?_
  have hk : chain13 k ≠ l := fun h => hl (by
    rw [← h]
    fin_cases k
    · exact (mem_support13 _).2 (Or.inl rfl)
    · exact (mem_support13 _).2 (Or.inr rfl))
  simp [hk]

theorem e6FiveExistsRoot13 : ∀ m : Fin 72,
    (∀ i, ¬(i = e6Index 0 ∨ i = e6Index 2) → e6RootVec m i = 0) →
      ∃ k l : Fin 3, k ≠ l ∧ chainRoot chain13 k l = e6RootVec m := by
  decide +kernel

theorem e6FiveRoot13_add : ∀ i j k : Fin 3,
    chainRoot chain13 i j + chainRoot chain13 j k = chainRoot chain13 i k := by
  decide +kernel

theorem e6FiveRoot01 :
    chainRoot chain13 0 1 = (Pi.single 0 1 : Fin Tag.E6.rank → ℤ) := by
  decide +kernel

theorem e6FiveRoot12 :
    chainRoot chain13 1 2 = (Pi.single 2 1 : Fin Tag.E6.rank → ℤ) := by
  decide +kernel


theorem e6FiveRoot13_mem {i j : Fin 3} (hij : i ≠ j) :
    chainRoot chain13 i j ∈ parabolicRoots Tag.E6 support13 := by
  have h := chainRoot134_mem_parabolicRoots (k := Fin.castSucc i) (l := Fin.castSucc j)
    (fun h => hij (Fin.castSucc_injective _ h))
  rw [e6FiveCastSucc] at h
  exact ⟨h.1, fun l hl => e6FiveRoot13_apply i j l hl⟩

theorem e6FivePinnedX_mem {L : Type} [Field L] {i j : Fin 3} (hij : i ≠ j) (t : L) :
    pinnedX Tag.E6 L (chainRoot chain13 i j) t ∈ subsystemGroup Tag.E6 L support13 :=
  rootSubgroup_le_subsystemGroup (e6FiveRoot13_mem hij)
    (Subgroup.subset_closure ⟨t, rfl⟩)

theorem e6FiveA2Mat_pinnedX {Ω : Type} [Field Ω] {i j : Fin 3} (hij : i ≠ j) :
    ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧ ∀ t : Ω,
      a2Mat₁ (pinnedX Tag.E6 Ω (chainRoot chain13 i j) t) = 1 + single i j ((ε : Ω) * t) := by
  obtain ⟨ε, hε, h⟩ := a3RootFamily_all (K := Ω) (Fin.castSucc i) (Fin.castSucc j)
    (fun h => hij (Fin.castSucc_injective _ h))
  refine ⟨ε, hε, fun t => ?_⟩
  rw [a2Mat₁, ← e6FiveCastSucc, h t]
  ext a b
  simp only [Matrix.submatrix_apply, Matrix.add_apply, Matrix.one_apply, Matrix.single_apply,
    Fin.castSucc_inj]

@[expose] def e6FiveRho (L : Type) [Field L] : SL(3, L) →* ModGL Tag.E6 L :=
  (subsystemGroup Tag.E6 L support13).subtype.comp (a2Equiv₁ L).symm.toMonoidHom

variable {L : Type} [Field L]

theorem e6FiveRho_range : (e6FiveRho L).range = subsystemGroup Tag.E6 L support13 := by
  ext g
  constructor
  · rintro ⟨X, rfl⟩
    exact ((a2Equiv₁ L).symm X).2
  · intro hg
    exact ⟨a2Equiv₁ L ⟨g, hg⟩, by simp [e6FiveRho]⟩

theorem e6FiveRho_transvection {i j : Fin 3} (hij : i ≠ j) :
    ∃ ε : Lˣ, ∀ t : L, e6FiveRho L (Matrix.SpecialLinearGroup.transvection hij t) =
      pinnedX Tag.E6 L (chainRoot chain13 i j) ((ε : L) * t) := by
  obtain ⟨s, hs, hρ⟩ := e6FiveA2Mat_pinnedX (Ω := L) hij
  have hss : (s : L) * s = 1 := by rcases hs with rfl | rfl <;> simp
  refine ⟨⟨(s : L), (s : L), hss, hss⟩, fun t => ?_⟩
  have h : (a2Equiv₁ L).symm (Matrix.SpecialLinearGroup.transvection hij t) =
      ⟨pinnedX Tag.E6 L (chainRoot chain13 i j) ((s : L) * t),
        e6FivePinnedX_mem hij _⟩ := by
    rw [MulEquiv.symm_apply_eq]
    refine Subtype.ext ?_
    rw [a2Equiv₁_apply, coe_a2Rep₁, hρ, ← mul_assoc, hss, one_mul]
    rfl
  simp only [e6FiveRho, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, Subgroup.coe_subtype]
  rw [h]

theorem e6FiveRho_diagonal (A : SL(3, L))
    (hA : ∀ i j : Fin 3, i ≠ j → (A : Matrix (Fin 3) (Fin 3) L) i j = 0) :
    e6FiveRho L A ∈ torusGroup Tag.E6 L := by
  have hdiag : (A : Matrix (Fin 3) (Fin 3) L) =
      Matrix.diagonal fun i => (A : Matrix (Fin 3) (Fin 3) L) i i := by
    ext i j
    by_cases hij : i = j
    · subst hij
      simp
    · simp [hA i j hij, Matrix.diagonal_apply_ne _ hij]
  have hdet : (A : Matrix (Fin 3) (Fin 3) L).det = 1 := A.2
  rw [hdiag, Matrix.det_diagonal, Fin.prod_univ_three] at hdet
  have h0 : (A : Matrix (Fin 3) (Fin 3) L) 0 0 ≠ 0 := fun h => by
    rw [h, zero_mul, zero_mul] at hdet
    exact zero_ne_one hdet
  have h01 : (A : Matrix (Fin 3) (Fin 3) L) 0 0 * (A : Matrix (Fin 3) (Fin 3) L) 1 1 ≠ 0 :=
    fun h => by
      rw [h, zero_mul] at hdet
      exact zero_ne_one hdet
  set ua : Lˣ := Units.mk0 _ h0 with hua
  set ub : Lˣ := Units.mk0 _ h01 with hub
  have h22 : (A : Matrix (Fin 3) (Fin 3) L) 2 2 =
      ((A : Matrix (Fin 3) (Fin 3) L) 0 0 * (A : Matrix (Fin 3) (Fin 3) L) 1 1)⁻¹ :=
    eq_inv_of_mul_eq_one_right hdet
  have hrep : a2Equiv₁ L ⟨e6TorusPair (e6Index 0) (e6Index 2) ua ub,
      e6TorusPair_mem_subsystemGroup _ _ ua ub⟩ = A := by
    rw [a2Equiv₁_apply]
    apply Subtype.ext
    rw [coe_a2Rep₁]
    change a2Mat₁ (e6TorusPair (e6Index 0) (e6Index 2) ua ub) = _
    rw [a2Mat₁_torus, hdiag]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hua, hub, Matrix.diagonal_apply_ne]
    rw [h22, _root_.mul_inv_rev]
  have hsymm : (a2Equiv₁ L).symm A = ⟨e6TorusPair (e6Index 0) (e6Index 2) ua ub,
      e6TorusPair_mem_subsystemGroup _ _ ua ub⟩ := by
    rw [MulEquiv.symm_apply_eq, hrep]
  simp only [e6FiveRho, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, Subgroup.coe_subtype]
  rw [hsymm]
  exact e6TorusPair_mem_torusGroup _ _ ua ub

theorem e6FiveFrame : IsA2Frame (e6FiveRho L) (fun i j => chainRoot chain13 i j) where
  injective := Subtype.val_injective.comp (a2Equiv₁ L).symm.injective
  isRoot _ _ hij := (e6FiveRoot13_mem hij).1
  neg i j := chainRoot_swap chain13 i j
  add := e6FiveRoot13_add
  transv _ _ hij := e6FiveRho_transvection hij
  range := by
    rw [e6FiveRho_range, subsystemGroup_eq_rootSpan]
    congr 1
    ext r
    refine ⟨fun hr => ?_, fun ⟨i, j, hij, h⟩ => h ▸ e6FiveRoot13_mem hij⟩
    obtain ⟨m, rfl⟩ := isRoot_iff_exists_e6RootVec.1 hr.1
    obtain ⟨k, l, hkl, h⟩ := e6FiveExistsRoot13 m
      (fun i hi => hr.2 i ((mem_support13 i).not.2 hi))
    exact ⟨k, l, hkl, h.symm⟩
  diag := e6FiveRho_diagonal

theorem e6FiveFrames {β₀ : Fin 4 → Fin Tag.E6.rank → ℤ} (hβ₀ : IsAChain β₀) (c : Fin 4)
    (h : (c : ℕ) + 1 < 4) : ∃ θ : SL(3, L) →* ModGL Tag.E6 L,
      θ.comp (blockSL L 3 2 0 (by omega)) = rootSL2 Tag.E6 L (β₀ c) ∧
        θ.comp (blockSL L 3 2 1 (by omega)) = rootSL2 Tag.E6 L (β₀ ⟨c + 1, h⟩) := by
  have hN : Tag.E6.artifactRoots.length = 72 := Tag.length_artifactRoots Tag.E6
  have hadj : iform (β₀ ⟨c + 1, h⟩) (β₀ c) = -1 := by
    rw [iform_comm]
    exact hβ₀.adj c ⟨c + 1, h⟩ rfl
  obtain ⟨v, hv0, hv2⟩ := exists_weyl_pair_of_tables hN (s := e6FiveChain) (tab := e6ChainTab)
    (fun k hk => e6ChainTab_ok k (by omega)) (hβ₀.isRoot c) (hβ₀.isRoot _) hadj
  obtain ⟨θ, h1, h2⟩ := exists_normalized_a2Frame ((e6FiveFrame (L := L)).transport v)
  refine ⟨θ, ?_, ?_⟩
  · rw [h1]
    show rootSL2 Tag.E6 L (v • chainRoot chain13 0 1) = _
    rw [e6FiveRoot01]
    exact congrArg _ hv0
  · rw [h2]
    show rootSL2 Tag.E6 L (v • chainRoot chain13 1 2) = _
    rw [e6FiveRoot12]
    exact congrArg _ hv2

theorem chainBlockToral_E6_four : ChainBlockToral Tag.E6 4 := by
  intro L _ _ hL β hβ
  rcases exists_weyl_chain_E6 hβ with ⟨v, hv⟩ | ⟨v, hv⟩
  · exact chainBlock_of_std (Or.inr (Or.inl rfl)) isAChain_e6FiveChain hL
      (fun c h => e6FiveFrames isAChain_e6FiveChain c h)
      ⟨5, by rw [chainExp_e6FiveChain]; exact ⟨1, 1, by norm_num⟩⟩ v hv
  · exact chainBlock_of_std (Or.inr (Or.inl rfl)) isAChain_e6FiveChainRev hL
      (fun c h => e6FiveFrames isAChain_e6FiveChainRev c h)
      ⟨1, by rw [chainExp_e6FiveChainRev]; exact ⟨2, 1, by norm_num⟩⟩ v hv

theorem monomialToralAt_E6_five : MonomialToralAt Tag.E6 5 :=
  monomialToralAt_five_of_chainBlock
    (fun _ hγ => EvenOddRadical.iform_self_eq_two (Or.inr (Or.inl rfl)) hγ)
    chainBlockToral_E6_four

end Frames

end E6

end CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
