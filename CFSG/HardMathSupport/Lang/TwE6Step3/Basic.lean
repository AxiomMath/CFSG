module

public import CFSG.RankThree.PartOne.KE6.Tw6Solvable
public import CFSG.HardMathSupport.Lang.TwE6Step3.Glue

public noncomputable section

namespace CFSG.HardMathSupport.Lang.TwE6Step3

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.E6 CFSG.RankThree.Lattice
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.RankThree.PartOne.KE CFSG.RankThree.PartOne.KE6 CFSG.RankThree.Classical2
  CFSG.LieType.SeitzGeneration CFSG.Open CFSG.AGLEmbedding
open scoped Matrix

set_option linter.unusedSectionVars false

@[expose] def TwE6SixLines : Prop :=
  ∀ (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.twistedE6 q).Valid) (p : ℕ), p.Prime →
    p ≠ 3 → p ≠ q.p → orderOf ((q.card : ℕ) : ZMod p) = 6 →
    ∀ E : Subgroup (Cat ⟨.twistedE6 q, hv⟩), IsElemAbelian p E → Nat.card E = p ^ 3 →
      ∀ y ∈ E, y ≠ 1 → ∀ k, k * y = y * k → k ∈ hyperClosure p ⊤ E



section Psi

variable {K : Type} [Field K] {σ : K ≃+* K} {L : Type} [Field L] [Algebra K L]

@[expose] def psiT (g0 : ModGL Tag.E6 L) (c x : twistedE6RootGroup K σ) : ModGL Tag.E6 L :=
  g0⁻¹ * twE6Emb K σ L (c * x * c⁻¹) * g0

theorem psiT_mul (g0 : ModGL Tag.E6 L) (c x y : twistedE6RootGroup K σ) :
    psiT g0 c (x * y) = psiT g0 c x * psiT g0 c y := by
  have h : c * (x * y) * c⁻¹ = (c * x * c⁻¹) * (c * y * c⁻¹) := by group
  simp only [psiT, h, map_mul]
  group

theorem psiT_injective (g0 : ModGL Tag.E6 L) (c : twistedE6RootGroup K σ) :
    Function.Injective (psiT (σ := σ) (L := L) g0 c) := by
  intro x y h
  have h0 : twE6Emb K σ L (c * x * c⁻¹) = twE6Emb K σ L (c * y * c⁻¹) := by
    have h' : g0⁻¹ * twE6Emb K σ L (c * x * c⁻¹) * g0 = g0⁻¹ * twE6Emb K σ L (c * y * c⁻¹) * g0 := h
    exact mul_left_cancel (mul_right_cancel h')
  have h1 : c * x * c⁻¹ = c * y * c⁻¹ := twE6Emb_injective (K := K) (σ := σ) (L := L) h0
  have h2 : c⁻¹ * (c * x * c⁻¹) * c = c⁻¹ * (c * y * c⁻¹) * c := by rw [h1]
  simpa [mul_assoc] using h2

theorem commute_of_psiT_commute {g0 : ModGL Tag.E6 L} {c x y : twistedE6RootGroup K σ}
    (h : psiT g0 c x * psiT g0 c y = psiT g0 c y * psiT g0 c x) : x * y = y * x := by
  apply psiT_injective g0 c
  rw [psiT_mul, psiT_mul, h]

end Psi


@[expose] def LinesOfType (P : Set (Fin Tag.E6.rank → ℤ) → Prop) : Prop :=
  ∀ {ℓ f : ℕ} [Fact ℓ.Prime] (K : Type) [Field K] [Finite K] [CharP K ℓ], 1 ≤ f →
    Nat.card K = (ℓ ^ f) ^ 2 → ∀ σ : K ≃+* K, (∀ c, σ c = c ^ (ℓ ^ f)) →
    ∀ {p : ℕ} [Fact p.Prime], 3 < p → (p : ℤ) ∣ ((ℓ ^ f : ℕ) : ℤ) ^ 2 - ((ℓ ^ f : ℕ) : ℤ) + 1 →
    ∀ (L : Type) [Field L] [Algebra K L] [IsAlgClosure K L] [CharP L ℓ] (g0 : ModGL Tag.E6 L),
    g0 ∈ adjointGroup Tag.E6 L → twistE6 L (iterateFrobenius L ℓ f) g0 = g0 * tw6N L →
    (∀ P : Subgroup (ModGL Tag.E6 L), Finite P → P ≤ adjointGroup Tag.E6 L →
      (∀ x ∈ P, twistE6 L (iterateFrobenius L ℓ f) x = x) → ⁅P, P⁆ = P →
        P ≤ (twE6Emb K σ L).range) →
    ∀ E : Subgroup (twistedE6RootGroup K σ), IsElemAbelian p E → Nat.card E = p ^ 3 →
    ∀ c : twistedE6RootGroup K σ,
      (∀ e ∈ E, psiT g0 c e ∈ twistedTorusOf (tw6N L) (twistE6 L (iterateFrobenius L ℓ f))) →
    ∀ y ∈ E, y ≠ 1 → P (torusRootKernel (psiT g0 c y)) →
    ∀ k : twistedE6RootGroup K σ, k * y = y * k → k ∈ hyperClosure p ⊤ E

@[expose] def IsA2Kernel (S : Set (Fin Tag.E6.rank → ℤ)) : Prop :=
  ∃ w : WeylGroup Tag.E6, (w • ·) '' S = parabolicRoots Tag.E6 support13

@[expose] def IsA2A2Kernel (S : Set (Fin Tag.E6.rank → ℤ)) : Prop :=
  ∃ w : WeylGroup Tag.E6, (w • ·) '' S = parabolicRoots Tag.E6 supportA2A2

@[expose] def IsD4Kernel (S : Set (Fin Tag.E6.rank → ℤ)) : Prop :=
  ∃ w : WeylGroup Tag.E6, (w • ·) '' S =
    parabolicRoots Tag.E6 {i : Fin Tag.E6.rank | i ≠ 0 ∧ i ≠ 5}

theorem le_hyperClosure_of_kernel_empty {ℓ f : ℕ} [Fact ℓ.Prime] (K : Type) [Field K] [Finite K]
    [CharP K ℓ] (hf : 1 ≤ f) (hK : Nat.card K = (ℓ ^ f) ^ 2) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) {p : ℕ} [hpF : Fact p.Prime] (hp3 : 3 < p)
    (hpq : (p : ℤ) ∣ ((ℓ ^ f : ℕ) : ℤ) ^ 2 - ((ℓ ^ f : ℕ) : ℤ) + 1)
    (L : Type) [Field L] [Algebra K L] [IsAlgClosure K L] [CharP L ℓ]
    {g0 : ModGL Tag.E6 L} (hg0C : g0 ∈ adjointGroup Tag.E6 L)
    (hg0 : twistE6 L (iterateFrobenius L ℓ f) g0 = g0 * tw6N L)
    (hperf : ∀ P : Subgroup (ModGL Tag.E6 L), Finite P → P ≤ adjointGroup Tag.E6 L →
      (∀ x ∈ P, twistE6 L (iterateFrobenius L ℓ f) x = x) → ⁅P, P⁆ = P →
        P ≤ (twE6Emb K σ L).range)
    {E : Subgroup (twistedE6RootGroup K σ)} (hE : IsElemAbelian p E) (hEc : Nat.card E = p ^ 3)
    (c : twistedE6RootGroup K σ)
    (hT : ∀ e ∈ E, psiT g0 c e ∈ twistedTorusOf (tw6N L) (twistE6 L (iterateFrobenius L ℓ f)))
    {y : twistedE6RootGroup K σ} (hy : y ∈ E) (hy1 : y ≠ 1)
    (hSig : torusRootKernel (psiT g0 c y) = ∅) {k : twistedE6RootGroup K σ} (hk : k * y = y * k) :
    k ∈ hyperClosure p ⊤ E := by
  have hyo : orderOf y = p := orderOf_eq_prime (hE.2 y hy) hy1
  obtain ⟨ι', KL, ψ, -, hψ, hspan, -⟩ := tw6_perx K hf hK σ hσ hpF.out hp3 hpq L hg0C hg0 hperf
    hyo c (hT y hy)
  obtain ⟨e, he, hey⟩ := exists_mem_not_mem_zpowers hE hEc hy
  have hkC : k ∈ Subgroup.centralizer ({y} : Set (twistedE6RootGroup K σ)) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact hk
  have hψk := hspan ⟨k, hkC⟩
  rw [hψ] at hψk
  change psiT g0 c k ∈ torusGroup Tag.E6 L ⊔ rootSpan Tag.E6 L (torusRootKernel (psiT g0 c y)) at hψk
  rw [hSig] at hψk
  have hbot : rootSpan Tag.E6 L (∅ : Set (Fin Tag.E6.rank → ℤ)) = ⊥ := by simp [rootSpan]
  rw [hbot, sup_bot_eq] at hψk
  have hke : k * e = e * k :=
    commute_of_psiT_commute (torusGroup_comm hψk (mem_twistedTorusOf.1 (hT e he)).1)
  exact mem_hyperClosure_of_commute_pair hE hEc hy he hy1 hey hk hke


theorem support13_root_cases : ∀ α ∈ rootFinset .E6, (∀ i : Fin Tag.E6.rank, i ≠ 0 → i ≠ 2 → α i = 0) →
    (α 2 = 1 ∨ α 2 = -1) ∨ (α = Pi.single 0 1 ∨ α = -Pi.single 0 1) := by
  decide +kernel

theorem e6T3Matrix_mulVec_ne : ∀ α ∈ rootFinset .E6,
    e6T3Matrix *ᵥ α ≠ α ∧ e6T3Matrix *ᵥ α ≠ -α := by
  decide +kernel

theorem e6T3W_smul_ne {α : Fin Tag.E6.rank → ℤ} (hα : IsRoot Tag.E6 α) :
    e6T3W • α ≠ α ∧ e6T3W • α ≠ -α := by
  rw [← weylMatrix_mulVec, weylMatrix_e6T3W_eq]
  exact e6T3Matrix_mulVec_ne α (mem_rootFinset.2 hα)

theorem subset_rootCharKernel_of_A2 {L : Type} [Field L] [IsAlgClosed L] {Fr : L →+* L} {q : ℕ}
    (hFr : ∀ c, Fr c = c ^ q) {t : ModGL Tag.E6 L}
    (ht : t ∈ twistedTorusOf (tw6N L) (twistE6 L Fr)) {w : WeylGroup Tag.E6}
    (hw : (w • ·) '' torusRootKernel t = parabolicRoots Tag.E6 support13)
    {b : Fin Tag.E6.rank → Lˣ} (hb : rootDiagUnit Tag.E6 b ∈ twistedTorusOf (tw6N L) (twistE6 L Fr))
    (hβ : rootChar b (w⁻¹ • (Pi.single 0 1 : Fin Tag.E6.rank → ℤ)) = 1) :
    torusRootKernel t ⊆ rootCharKernel b := by
  set β : Fin Tag.E6.rank → ℤ := w⁻¹ • (Pi.single 0 1 : Fin Tag.E6.rank → ℤ) with hβdef
  set γ : Fin Tag.E6.rank → ℤ := w⁻¹ • (Pi.single 2 1 : Fin Tag.E6.rank → ℤ) with hγdef
  have hker := (mem_twistedTorus_rootDiagUnit_iff6 hFr b).1 hb
  have hrel : ∀ μ, rootChar b (e6T3W • μ) * rootChar b μ ^ q = 1 := fun μ => by
    rw [← rootChar_tw6Matrix_mulVec]
    exact (mem_ker_monomialHom_iff_forall (tw6Matrix q) b).1 hker μ
  have hsupp : ∀ α ∈ torusRootKernel t, ∀ i : Fin Tag.E6.rank, i ≠ 0 → i ≠ 2 → (w • α) i = 0 := by
    intro α hα i hi0 hi2
    have hmem : w • α ∈ parabolicRoots Tag.E6 support13 := hw ▸ ⟨α, hα, rfl⟩
    refine hmem.2 i ?_
    rintro (h | h)
    · exact hi0 h
    · exact hi2 (Set.mem_singleton_iff.1 h)
  have hdecomp : ∀ α ∈ torusRootKernel t, α = (w • α) 0 • β + (w • α) 2 • γ := by
    intro α hα
    have hv : w • α = (w • α) 0 • (Pi.single 0 1 : Fin Tag.E6.rank → ℤ) +
        (w • α) 2 • (Pi.single 2 1 : Fin Tag.E6.rank → ℤ) := by
      funext i
      by_cases h0 : i = 0
      · subst h0; simp
      · by_cases h2 : i = 2
        · subst h2; simp
        · rw [hsupp α hα i h0 h2]; simp [h0, h2]
    have := congrArg (w⁻¹ • ·) hv
    simp only [inv_smul_smul, smul_add, smul_comm w⁻¹ ((w • α) 0), smul_comm w⁻¹ ((w • α) 2)] at this
    exact this
  have hsingle : (Pi.single 0 1 : Fin Tag.E6.rank → ℤ) ∈ rootFinset .E6 := by decide +kernel
  have hβS : β ∈ torusRootKernel t := by
    have hmem : (Pi.single 0 1 : Fin Tag.E6.rank → ℤ) ∈ parabolicRoots Tag.E6 support13 := by
      refine ⟨mem_rootFinset.1 hsingle, fun i hi => ?_⟩
      have hi0 : i ≠ 0 := fun h => hi (h ▸ Or.inl rfl)
      simp [hi0]
    rw [← hw] at hmem
    obtain ⟨α, hα, hαw⟩ := hmem
    rw [hβdef, ← hαw, inv_smul_smul]
    exact hα
  have huβ : e6T3W • β ∈ torusRootKernel t := tw6_torusRootKernel_smul_stable hFr ht β hβS
  have hχuβ : rootChar b (e6T3W • β) = 1 := by
    have h := hrel β
    rw [hβ, one_pow, mul_one] at h
    exact h
  obtain ⟨hne1, hne2⟩ := e6T3W_smul_ne hβS.1
  have hcases := support13_root_cases (w • (e6T3W • β)) (mem_rootFinset.2 (IsRoot.smul huβ.1 w))
    (hsupp _ huβ)
  have hd := hdecomp _ huβ
  obtain ⟨A, hA⟩ : ∃ A, (w • (e6T3W • β)) 0 = A := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B, (w • (e6T3W • β)) 2 = B := ⟨_, rfl⟩
  rw [hA, hB] at hd
  rw [hB] at hcases
  have hγ : rootChar b γ = 1 := by
    rcases hcases with h | h
    · rcases h with h | h
      · have e : γ = e6T3W • β + (-A) • β := by
          rw [hd, h, one_smul, neg_smul]; abel
        rw [e, rootChar_add, rootChar_zsmul, hχuβ, hβ, one_zpow, mul_one]
      · have e : γ = A • β + (-1 : ℤ) • (e6T3W • β) := by
          rw [hd, h]; simp only [neg_smul, one_smul, neg_add_rev, neg_neg]; abel
        rw [e, rootChar_add, rootChar_zsmul, rootChar_zsmul, hχuβ, hβ, one_zpow, one_zpow, mul_one]
    · exfalso
      rcases h with h | h
      · rw [← hA, ← hB] at hd
        have e := congrArg (w⁻¹ • ·) h
        simp only [inv_smul_smul] at e
        exact hne1 e
      · have e := congrArg (w⁻¹ • ·) h
        simp only [inv_smul_smul, smul_neg] at e
        exact hne2 e
  intro α hα
  refine ⟨hα.1, ?_⟩
  rw [hdecomp α hα, rootChar_add, rootChar_zsmul, rootChar_zsmul, hβ, hγ, one_zpow, one_zpow,
    mul_one]


theorem torusRootChar_rootDiagUnit' {L : Type} [Field L] (b : Fin Tag.E6.rank → Lˣ)
    {α : Fin Tag.E6.rank → ℤ} (hα : IsRoot Tag.E6 α) :
    torusRootChar (rootDiagUnit Tag.E6 b) α = ((rootChar b α : Lˣ) : L) :=
  torusRootChar_eq_of_apply hα (rootDiag_rootVec b hα)

section Char

variable {K : Type} [Field K] {σ : K ≃+* K} {L : Type} [Field L] [Algebra K L]

@[expose] def cubeChar (g0 : ModGL Tag.E6 L) (c : twistedE6RootGroup K σ)
    {E : Subgroup (twistedE6RootGroup K σ)} (hE : ∀ e ∈ E, psiT g0 c e ∈ torusGroup Tag.E6 L)
    (β : Fin Tag.E6.rank → ℤ) : E →* Lˣ where
  toFun e := Units.mk0 (torusRootChar (psiT g0 c (e : twistedE6RootGroup K σ)) β)
    (torusRootChar_ne_zero (torusGroup_le_diagonalGroup (hE e e.2)) β)
  map_one' := by
    ext
    have h1 : psiT g0 c (1 : twistedE6RootGroup K σ) = 1 := by simp [psiT]
    simp only [OneMemClass.coe_one, Units.val_mk0, Units.val_one, h1, torusRootChar_one]
  map_mul' a b := by
    ext
    simp only [Subgroup.coe_mul, Units.val_mk0, Units.val_mul, psiT_mul]
    exact torusRootChar_mul (torusGroup_le_diagonalGroup (hE a a.2))
      (torusGroup_le_diagonalGroup (hE b b.2)) β

theorem cubeChar_eq_one_iff {g0 : ModGL Tag.E6 L} {c : twistedE6RootGroup K σ}
    {E : Subgroup (twistedE6RootGroup K σ)} (hE : ∀ e ∈ E, psiT g0 c e ∈ torusGroup Tag.E6 L)
    {β : Fin Tag.E6.rank → ℤ} (hβ : IsRoot Tag.E6 β) (e : E) {b : Fin Tag.E6.rank → Lˣ}
    (hb : psiT g0 c (e : twistedE6RootGroup K σ) = rootDiagUnit Tag.E6 b) :
    cubeChar g0 c hE β e = 1 ↔ rootChar b β = 1 := by
  have h : ((cubeChar g0 c hE β e : Lˣ) : L) = ((rootChar b β : Lˣ) : L) := by
    show torusRootChar (psiT g0 c (e : twistedE6RootGroup K σ)) β = _
    rw [hb, torusRootChar_rootDiagUnit' b hβ]
  constructor
  · intro h1
    exact Units.ext (by rw [← h, h1])
  · intro h1
    exact Units.ext (by rw [h, h1])

end Char

theorem le_hyperClosure_of_kernel_A2 {ℓ f : ℕ} [Fact ℓ.Prime] (K : Type) [Field K] [Finite K]
    [CharP K ℓ] (hf : 1 ≤ f) (hK : Nat.card K = (ℓ ^ f) ^ 2) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) {p : ℕ} [hpF : Fact p.Prime] (hp3 : 3 < p)
    (hpq : (p : ℤ) ∣ ((ℓ ^ f : ℕ) : ℤ) ^ 2 - ((ℓ ^ f : ℕ) : ℤ) + 1)
    (L : Type) [Field L] [Algebra K L] [IsAlgClosure K L] [CharP L ℓ]
    {g0 : ModGL Tag.E6 L} (hg0C : g0 ∈ adjointGroup Tag.E6 L)
    (hg0 : twistE6 L (iterateFrobenius L ℓ f) g0 = g0 * tw6N L)
    (hperf : ∀ P : Subgroup (ModGL Tag.E6 L), Finite P → P ≤ adjointGroup Tag.E6 L →
      (∀ x ∈ P, twistE6 L (iterateFrobenius L ℓ f) x = x) → ⁅P, P⁆ = P →
        P ≤ (twE6Emb K σ L).range)
    {E : Subgroup (twistedE6RootGroup K σ)} (hE : IsElemAbelian p E) (hEc : Nat.card E = p ^ 3)
    (c : twistedE6RootGroup K σ)
    (hT : ∀ e ∈ E, psiT g0 c e ∈ twistedTorusOf (tw6N L) (twistE6 L (iterateFrobenius L ℓ f)))
    {y : twistedE6RootGroup K σ} (hy : y ∈ E) (hy1 : y ≠ 1)
    (hA2 : ∃ w : WeylGroup Tag.E6,
      (w • ·) '' torusRootKernel (psiT g0 c y) = parabolicRoots Tag.E6 support13)
    {k : twistedE6RootGroup K σ} (hk : k * y = y * k) :
    k ∈ hyperClosure p ⊤ E := by
  classical
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  have hFr : ∀ c, (iterateFrobenius L ℓ f) c = c ^ (ℓ ^ f) := fun c => iterateFrobenius_def ℓ f c
  obtain ⟨w, hw⟩ := hA2
  set β : Fin Tag.E6.rank → ℤ := w⁻¹ • (Pi.single 0 1 : Fin Tag.E6.rank → ℤ) with hβdef
  have hyo : orderOf y = p := orderOf_eq_prime (hE.2 y hy) hy1
  have hsingle : (Pi.single 0 1 : Fin Tag.E6.rank → ℤ) ∈ rootFinset .E6 := by decide +kernel
  have hβS : β ∈ torusRootKernel (psiT g0 c y) := by
    have hmem : (Pi.single 0 1 : Fin Tag.E6.rank → ℤ) ∈ parabolicRoots Tag.E6 support13 := by
      refine ⟨mem_rootFinset.1 hsingle, fun i hi => ?_⟩
      have hi0 : i ≠ 0 := fun h => hi (h ▸ Or.inl rfl)
      simp [hi0]
    rw [← hw] at hmem
    obtain ⟨α, hα, hαw⟩ := hmem
    rw [hβdef, ← hαw, inv_smul_smul]
    exact hα
  have hβroot : IsRoot Tag.E6 β := hβS.1
  have hET : ∀ e ∈ E, psiT g0 c e ∈ torusGroup Tag.E6 L := fun e he => (mem_twistedTorusOf.1 (hT e he)).1
  obtain ⟨⟨e, he⟩, hey, hχe⟩ := exists_mem_ker_not_mem_zpowers hE hEc (cubeChar g0 c hET β) hy
  obtain ⟨b, hb⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup (hET e he)
  have hbβ : rootChar b β = 1 := (cubeChar_eq_one_iff hET hβroot ⟨e, he⟩ hb).1 hχe
  have hbT : rootDiagUnit Tag.E6 b ∈ twistedTorusOf (tw6N L) (twistE6 L (iterateFrobenius L ℓ f)) := by
    rw [← hb]
    exact hT e he
  have hsub := subset_rootCharKernel_of_A2 hFr (hT y hy) hw hbT hbβ
  have hcent : torusGroup Tag.E6 L ⊔ rootSpan Tag.E6 L (torusRootKernel (psiT g0 c y)) ≤
      Subgroup.centralizer {rootDiagUnit Tag.E6 b} := by
    refine sup_le ?_ (CFSG.LieType.Chevalley.rootSpan_le_centralizer b hsub)
    intro x hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact torusGroup_comm hx (mem_twistedTorusOf.1 hbT).1
  obtain ⟨ι', KL, ψ, -, hψ, hspan, -⟩ := tw6_perx K hf hK σ hσ hpF.out hp3 hpq L hg0C hg0 hperf
    hyo c (hT y hy)
  have hkC : k ∈ Subgroup.centralizer ({y} : Set (twistedE6RootGroup K σ)) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact hk
  have hψk : psiT g0 c k ∈ torusGroup Tag.E6 L ⊔ rootSpan Tag.E6 L (torusRootKernel (psiT g0 c y)) := by
    have h := hspan ⟨k, hkC⟩
    rw [hψ] at h
    exact h
  have hc := Subgroup.mem_centralizer_singleton_iff.1 (hcent hψk)
  rw [← hb] at hc
  have hc' : psiT g0 c k * psiT g0 c e = psiT g0 c e * psiT g0 c k := hc
  have hke : k * e = e * k := by
    apply psiT_injective g0 c
    rw [psiT_mul, psiT_mul]
    exact hc'
  exact mem_hyperClosure_of_commute_pair hE hEc hy he hy1 hey hk hke

end CFSG.HardMathSupport.Lang.TwE6Step3
