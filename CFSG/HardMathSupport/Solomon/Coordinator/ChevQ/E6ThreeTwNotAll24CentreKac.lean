module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KS.TwE6InnerCompFrames

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

namespace KSConn

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.RankThree.Lattice
  CFSG.LieType.Steinberg.Adjoint CFSG.HardMathSupport.Solomon.Coordinator.ChevQ
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.TwE6UniqAbs
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.TwE6InnerAbs
open scoped MatrixGroups

set_option maxRecDepth 100000

@[expose] def lA4a : Fin 4 → Option (Fin Tag.E6.rank) :=
  (![some 2, some 3, some 4, some 5] : Fin 4 → Option (Fin 6))

@[expose] def lA4b : Fin 4 → Option (Fin Tag.E6.rank) :=
  (![none, some 1, some 3, some 2] : Fin 4 → Option (Fin 6))

@[expose] def lA4c : Fin 4 → Option (Fin Tag.E6.rank) :=
  (![some 0, some 2, some 3, some 4] : Fin 4 → Option (Fin 6))

@[expose] def lA4d : Fin 4 → Option (Fin Tag.E6.rank) :=
  (![none, some 1, some 3, some 4] : Fin 4 → Option (Fin 6))

@[expose] def lA4e : Fin 4 → Option (Fin Tag.E6.rank) :=
  (![some 1, some 3, some 4, some 5] : Fin 4 → Option (Fin 6))

@[expose] def lA4f : Fin 4 → Option (Fin Tag.E6.rank) :=
  (![some 0, some 2, some 3, some 1] : Fin 4 → Option (Fin 6))

@[expose] def lA1a : Fin 1 → Option (Fin Tag.E6.rank) := (![none] : Fin 1 → Option (Fin 6))

@[expose] def lA1b : Fin 1 → Option (Fin Tag.E6.rank) := (![some 0] : Fin 1 → Option (Fin 6))

@[expose] def lA1c : Fin 1 → Option (Fin Tag.E6.rank) := (![some 5] : Fin 1 → Option (Fin 6))

@[expose] def IsChainLabel {m : ℕ} (l : Fin m → Option (Fin Tag.E6.rank)) : Prop :=
  Function.Injective l ∧
    (∀ c d : Fin m, iform (e6ExtVec (l c)) (e6ExtVec (l d)) = chainGram c d) ∧
    ∀ (c : Fin m) (h : c.val + 1 < m),
      (nodeIdx (l c), nodeIdx (l ⟨c.val + 1, h⟩)) ∈ e6EdgeIdx

theorem lA5a_isChain : IsChainLabel lA5a := lA5a_chk
theorem lA5b_isChain : IsChainLabel lA5b := lA5b_chk
theorem lA5c_isChain : IsChainLabel lA5c := lA5c_chk
theorem lA4a_isChain : IsChainLabel lA4a := by unfold IsChainLabel; decide +kernel
theorem lA4b_isChain : IsChainLabel lA4b := by unfold IsChainLabel; decide +kernel
theorem lA4c_isChain : IsChainLabel lA4c := by unfold IsChainLabel; decide +kernel
theorem lA4d_isChain : IsChainLabel lA4d := by unfold IsChainLabel; decide +kernel
theorem lA4e_isChain : IsChainLabel lA4e := by unfold IsChainLabel; decide +kernel
theorem lA4f_isChain : IsChainLabel lA4f := by unfold IsChainLabel; decide +kernel
theorem lA1a_isChain : IsChainLabel lA1a := by unfold IsChainLabel; decide +kernel
theorem lA1b_isChain : IsChainLabel lA1b := by unfold IsChainLabel; decide +kernel
theorem lA1c_isChain : IsChainLabel lA1c := by unfold IsChainLabel; decide +kernel

@[expose] def chainSet {m : ℕ} (l : Fin m → Option (Fin Tag.E6.rank)) :
    Finset (Option (Fin Tag.E6.rank)) :=
  Finset.univ.image l

theorem coe_chainSet {m : ℕ} (l : Fin m → Option (Fin Tag.E6.rank)) :
    (↑(chainSet l) : Set (Option (Fin Tag.E6.rank))) = Set.range l := by
  simp [chainSet, Finset.coe_image]

@[expose] def kcConnB (zl : List ℕ) : Bool :=
  zl.all fun x =>
    (szF zl x == 30 && ((cmpF zl x == chainSet lA5a) || (cmpF zl x == chainSet lA5b) ||
      (cmpF zl x == chainSet lA5c))) ||
    (szF zl x == 20 && ((cmpF zl x == chainSet lA4a) || (cmpF zl x == chainSet lA4b) ||
      (cmpF zl x == chainSet lA4c) || (cmpF zl x == chainSet lA4d) ||
      (cmpF zl x == chainSet lA4e) || (cmpF zl x == chainSet lA4f))) ||
    (szF zl x == 2 && ((cmpF zl x == chainSet lA1a) || (cmpF zl x == chainSet lA1b) ||
      (cmpF zl x == chainSet lA1c)))

@[expose] def cntB (m0 m1 m2 m3 m4 m5 : ℤ) : ℕ :=
  (R6.filter fun γ => dotμ γ m0 m1 m2 m3 m4 m5 % 3 == 0).length

set_option synthInstance.maxSize 1024 in
theorem kc_conn : ∀ m0 m1 m2 m3 m4 m5 : Fin 4,
    (m0.val + 2 * m1.val + 2 * m2.val + 3 * m3.val + 2 * m4.val + m5.val ≤ 3) →
    (cntB m0.val m1.val m2.val m3.val m4.val m5.val = 22 ∨
      cntB m0.val m1.val m2.val m3.val m4.val m5.val = 30) →
    kcConnB (zlC m0 m1 m2 m3 m4 m5) = true := by
  decide +kernel

set_option synthInstance.maxSize 1024 in
theorem kc_thirty : ∀ m0 m1 m2 m3 m4 m5 : Fin 4,
    (m0.val + 2 * m1.val + 2 * m2.val + 3 * m3.val + 2 * m4.val + m5.val ≤ 3) →
    cntB m0.val m1.val m2.val m3.val m4.val m5.val = 30 →
    (zlC m0 m1 m2 m3 m4 m5).all (fun x => szF (zlC m0 m1 m2 m3 m4 m5) x == 30) = true := by
  decide +kernel

theorem R6_nodup' : R6.Nodup := by decide +kernel

section Count


theorem ncard_kernelRoots_eq_cntB {L : Type} [Field L] {a : Fin Tag.E6.rank → Lˣ} {ζ : Lˣ}
    (hζ : IsPrimitiveRoot (ζ : L) 3) (w : WeylGroup Tag.E6) {m0 m1 m2 m3 m4 m5 : ℤ}
    (hchar : ∀ β, rootChar a β = ζ ^ dotμ (w • β) m0 m1 m2 m3 m4 m5) :
    (kernelRoots (rootCharHom a)).ncard = cntB m0 m1 m2 m3 m4 m5 := by
  classical
  have hζ' : IsPrimitiveRoot ζ 3 := IsPrimitiveRoot.coe_units_iff.1 hζ
  have hset : kernelRoots (rootCharHom a) = (fun δ => w⁻¹ • δ) ''
      ↑(R6.filter fun γ => dotμ γ m0 m1 m2 m3 m4 m5 % 3 == 0).toFinset := by
    ext α
    constructor
    · rintro ⟨hα, hχ⟩
      refine ⟨w • α, ?_, inv_smul_smul w α⟩
      simp only [Finset.mem_coe, List.mem_toFinset, List.mem_filter, beq_iff_eq]
      refine ⟨mem_R6_of_isRoot (IsRoot.smul hα w), ?_⟩
      have h1 : rootChar a α = 1 := hχ
      rw [hchar] at h1
      exact Int.emod_eq_zero_of_dvd ((hζ'.zpow_eq_one_iff_dvd _).1 h1)
    · rintro ⟨δ, hδ, rfl⟩
      simp only [Finset.mem_coe, List.mem_toFinset, List.mem_filter, beq_iff_eq] at hδ
      obtain ⟨hδR, hδ3⟩ := hδ
      have hδr : IsRoot Tag.E6 δ := isRoot_of_mem_R6 hδR
      refine ⟨IsRoot.smul hδr w⁻¹, ?_⟩
      change rootChar a (w⁻¹ • δ) = 1
      rw [hchar, smul_inv_smul, hζ'.zpow_eq_one_iff_dvd]
      exact Int.dvd_of_emod_eq_zero hδ3
  rw [hset, Set.ncard_image_of_injective _ (MulAction.injective w⁻¹), Set.ncard_coe_finset,
    List.toFinset_card_of_nodup (R6_nodup'.filter _)]
  rfl

end Count

section Frames


theorem frame_of_chain {L : Type} [Field L] {m : ℕ} {l : Fin m → Option (Fin Tag.E6.rank)}
    (hl : IsChainLabel l) :
    ∃ (ψ : SL(m + 1, L) →* ModGL Tag.E6 L)
      (σ : Fin (m + 1) → Fin (m + 1) → Fin Tag.E6.rank → ℤ),
      IsSLFrame ψ σ ∧ (∀ a b, a ≠ b → iform (σ a b) (σ a b) = 2) ∧
        frameRoots σ = kacE6.rootsOf (Set.range l) := by
  obtain ⟨ψ, σ, hψ, hn, hr⟩ := frame_of_path6 (L := L) hl.1 hl.2.1 hl.2.2 1
  refine ⟨ψ, σ, hψ, hn, ?_⟩
  rw [hr]
  simp only [one_smul, Set.image_id']

theorem conn_class_data {L : Type} [Field L] [IsAlgClosed L] (h3 : ((3 : ℕ) : L) ≠ 0)
    {a : Fin Tag.E6.rank → Lˣ} (hap : ∀ i, a i ^ 3 = 1)
    (hk : (kernelRoots (rootCharHom a)).ncard = 22 ∨ (kernelRoots (rootCharHom a)).ncard = 30)
    (i : KernelComponent (rootCharHom a)) :
    ∃ m : ℕ, (m = 1 ∨ m = 4 ∨ m = 5) ∧ ∃ (v : WeylGroup Tag.E6)
      (ψ₀ : SL(m + 1, L) →* ModGL Tag.E6 L)
      (σ₀ : Fin (m + 1) → Fin (m + 1) → Fin Tag.E6.rank → ℤ),
      IsSLFrame ψ₀ σ₀ ∧ (∀ x y, x ≠ y → iform (σ₀ x y) (σ₀ x y) = 2) ∧
        componentRoots (rootCharHom a) i = (fun α => v • α) '' frameRoots σ₀ ∧
        (m = 5 → ∃ S : Finset (Option (Fin Tag.E6.rank)),
          (S = sA5a ∨ S = sA5b ∨ S = sA5c) ∧
            frameRoots σ₀ = kacE6.rootsOf (↑S : Set (Option (Fin Tag.E6.rank)))) ∧
        (m = 1 → compRank (componentRoots (rootCharHom a) i) = 1 ∧
          (componentRoots (rootCharHom a) i).ncard = 2 ∧
            (kernelRoots (rootCharHom a)).ncard = 22) := by
  classical
  obtain ⟨ζ, w, m0, m1, m2, m3, m4, m5, hζ, hsum, hchar, hcl⟩ := kac_class_data h3 hap
  have hcnt := ncard_kernelRoots_eq_cntB hζ w hchar
  have hk0 : cntB m0.val m1.val m2.val m3.val m4.val m5.val = 22 ∨
      cntB m0.val m1.val m2.val m3.val m4.val m5.val = 30 := by rwa [hcnt] at hk
  have hB := kc_conn m0 m1 m2 m3 m4 m5 hsum hk0
  obtain ⟨x, hx, hroots, hncard, hrank, -⟩ := hcl i
  have hx' := List.all_eq_true.1 hB x hx
  simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at hx'
  have key : ∀ {m : ℕ} {l : Fin m → Option (Fin Tag.E6.rank)}, IsChainLabel l →
      cmpF (zlC m0 m1 m2 m3 m4 m5) x = chainSet l →
      ∃ (ψ₀ : SL(m + 1, L) →* ModGL Tag.E6 L)
        (σ₀ : Fin (m + 1) → Fin (m + 1) → Fin Tag.E6.rank → ℤ),
        IsSLFrame ψ₀ σ₀ ∧ (∀ x y, x ≠ y → iform (σ₀ x y) (σ₀ x y) = 2) ∧
          componentRoots (rootCharHom a) i = (fun α => w⁻¹ • α) '' frameRoots σ₀ ∧
          frameRoots σ₀ = kacE6.rootsOf (Set.range l) := by
    intro m l hl hcm
    obtain ⟨ψ, σ, hψ, hn, hr⟩ := frame_of_chain (L := L) hl
    refine ⟨ψ, σ, hψ, hn, ?_, hr⟩
    rw [hroots, hcm, coe_chainSet, hr]
  have key5 : ∀ {l : Fin 5 → Option (Fin Tag.E6.rank)} {S : Finset (Option (Fin Tag.E6.rank))},
      IsChainLabel l → Set.range l = ↑S → (S = sA5a ∨ S = sA5b ∨ S = sA5c) →
      cmpF (zlC m0 m1 m2 m3 m4 m5) x = chainSet l →
      ∃ m : ℕ, (m = 1 ∨ m = 4 ∨ m = 5) ∧ ∃ (v : WeylGroup Tag.E6)
        (ψ₀ : SL(m + 1, L) →* ModGL Tag.E6 L)
        (σ₀ : Fin (m + 1) → Fin (m + 1) → Fin Tag.E6.rank → ℤ),
        IsSLFrame ψ₀ σ₀ ∧ (∀ x y, x ≠ y → iform (σ₀ x y) (σ₀ x y) = 2) ∧
          componentRoots (rootCharHom a) i = (fun α => v • α) '' frameRoots σ₀ ∧
          (m = 5 → ∃ S : Finset (Option (Fin Tag.E6.rank)),
            (S = sA5a ∨ S = sA5b ∨ S = sA5c) ∧
              frameRoots σ₀ = kacE6.rootsOf (↑S : Set (Option (Fin Tag.E6.rank)))) ∧
          (m = 1 → compRank (componentRoots (rootCharHom a) i) = 1 ∧
            (componentRoots (rootCharHom a) i).ncard = 2 ∧
              (kernelRoots (rootCharHom a)).ncard = 22) := by
    intro l S hl hS hSc hcm
    obtain ⟨ψ, σ, hψ, hn, hΨ, hr⟩ := key hl hcm
    exact ⟨5, Or.inr (Or.inr rfl), w⁻¹, ψ, σ, hψ, hn, hΨ, fun _ => ⟨S, hSc, by rw [hr, hS]⟩,
      fun h => absurd h (by norm_num)⟩
  have key4 : ∀ {l : Fin 4 → Option (Fin Tag.E6.rank)}, IsChainLabel l →
      cmpF (zlC m0 m1 m2 m3 m4 m5) x = chainSet l →
      ∃ m : ℕ, (m = 1 ∨ m = 4 ∨ m = 5) ∧ ∃ (v : WeylGroup Tag.E6)
        (ψ₀ : SL(m + 1, L) →* ModGL Tag.E6 L)
        (σ₀ : Fin (m + 1) → Fin (m + 1) → Fin Tag.E6.rank → ℤ),
        IsSLFrame ψ₀ σ₀ ∧ (∀ x y, x ≠ y → iform (σ₀ x y) (σ₀ x y) = 2) ∧
          componentRoots (rootCharHom a) i = (fun α => v • α) '' frameRoots σ₀ ∧
          (m = 5 → ∃ S : Finset (Option (Fin Tag.E6.rank)),
            (S = sA5a ∨ S = sA5b ∨ S = sA5c) ∧
              frameRoots σ₀ = kacE6.rootsOf (↑S : Set (Option (Fin Tag.E6.rank)))) ∧
          (m = 1 → compRank (componentRoots (rootCharHom a) i) = 1 ∧
            (componentRoots (rootCharHom a) i).ncard = 2 ∧
              (kernelRoots (rootCharHom a)).ncard = 22) := by
    intro l hl hcm
    obtain ⟨ψ, σ, hψ, hn, hΨ, -⟩ := key hl hcm
    exact ⟨4, Or.inr (Or.inl rfl), w⁻¹, ψ, σ, hψ, hn, hΨ, fun h => absurd h (by norm_num),
      fun h => absurd h (by norm_num)⟩
  have key1 : ∀ {l : Fin 1 → Option (Fin Tag.E6.rank)}, IsChainLabel l → (chainSet l).card = 1 →
      cmpF (zlC m0 m1 m2 m3 m4 m5) x = chainSet l →
      szF (zlC m0 m1 m2 m3 m4 m5) x = 2 →
      ∃ m : ℕ, (m = 1 ∨ m = 4 ∨ m = 5) ∧ ∃ (v : WeylGroup Tag.E6)
        (ψ₀ : SL(m + 1, L) →* ModGL Tag.E6 L)
        (σ₀ : Fin (m + 1) → Fin (m + 1) → Fin Tag.E6.rank → ℤ),
        IsSLFrame ψ₀ σ₀ ∧ (∀ x y, x ≠ y → iform (σ₀ x y) (σ₀ x y) = 2) ∧
          componentRoots (rootCharHom a) i = (fun α => v • α) '' frameRoots σ₀ ∧
          (m = 5 → ∃ S : Finset (Option (Fin Tag.E6.rank)),
            (S = sA5a ∨ S = sA5b ∨ S = sA5c) ∧
              frameRoots σ₀ = kacE6.rootsOf (↑S : Set (Option (Fin Tag.E6.rank)))) ∧
          (m = 1 → compRank (componentRoots (rootCharHom a) i) = 1 ∧
            (componentRoots (rootCharHom a) i).ncard = 2 ∧
              (kernelRoots (rootCharHom a)).ncard = 22) := by
    intro l hl hc1 hcm hsz
    obtain ⟨ψ, σ, hψ, hn, hΨ, -⟩ := key hl hcm
    have h22 : (kernelRoots (rootCharHom a)).ncard = 22 := by
      rcases hk0 with h | h
      · rw [hcnt]; exact h
      · exfalso
        have h30 := List.all_eq_true.1 (kc_thirty m0 m1 m2 m3 m4 m5 hsum h) x hx
        simp only [beq_iff_eq] at h30
        omega
    exact ⟨1, Or.inl rfl, w⁻¹, ψ, σ, hψ, hn, hΨ, fun h => absurd h (by norm_num),
      fun _ => ⟨by rw [hrank, hcm, hc1], by rw [hncard, hsz], h22⟩⟩
  rcases hx' with (⟨-, (hc | hc) | hc⟩ | ⟨-, ((((hc | hc) | hc) | hc) | hc) | hc⟩) |
    ⟨hsz, (hc | hc) | hc⟩
  · exact key5 lA5a_isChain range_lA5a (Or.inl rfl) hc
  · exact key5 lA5b_isChain range_lA5b (Or.inr (Or.inl rfl)) hc
  · exact key5 lA5c_isChain range_lA5c (Or.inr (Or.inr rfl)) hc
  · exact key4 lA4a_isChain hc
  · exact key4 lA4b_isChain hc
  · exact key4 lA4c_isChain hc
  · exact key4 lA4d_isChain hc
  · exact key4 lA4e_isChain hc
  · exact key4 lA4f_isChain hc
  · exact key1 lA1a_isChain (by decide) hc hsz
  · exact key1 lA1b_isChain (by decide) hc hsz
  · exact key1 lA1c_isChain (by decide) hc hsz

end Frames

end KSConn

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three
