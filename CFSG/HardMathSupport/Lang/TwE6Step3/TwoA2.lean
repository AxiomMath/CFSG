module

public import CFSG.HardMathSupport.Lang.TwE6Step3.Lines

public noncomputable section

namespace CFSG.HardMathSupport.Lang.TwE6Step3

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.E6 CFSG.RankThree.Lattice
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.RankThree.PartOne.KE CFSG.RankThree.PartOne.KE6 CFSG.RankThree.Classical2
  CFSG.LieType.SeitzGeneration CFSG.Open CFSG.AGLEmbedding
open scoped Matrix

set_option linter.unusedSectionVars false


theorem psiT_inv {K : Type} [Field K] {σ : K ≃+* K} {L : Type} [Field L] [Algebra K L]
    (g0 : ModGL Tag.E6 L) (c x : twistedE6RootGroup K σ) :
    psiT g0 c x⁻¹ = (psiT g0 c x)⁻¹ := by
  refine eq_inv_of_mul_eq_one_left ?_
  rw [← psiT_mul, inv_mul_cancel, psiT_one]

theorem conj_e6T3W_preserves_blocks {w : WeylGroup Tag.E6}
    (hT : ∀ β ∈ parabolicRoots Tag.E6 supportA2A2,
      (w * e6T3W * w⁻¹) • β ∈ parabolicRoots Tag.E6 supportA2A2) :
    (∀ β ∈ parabolicRoots Tag.E6 support13,
      (w * e6T3W * w⁻¹) • β ∈ parabolicRoots Tag.E6 support13) ∧
    (∀ β ∈ parabolicRoots Tag.E6 support56,
      (w * e6T3W * w⁻¹) • β ∈ parabolicRoots Tag.E6 support56) := by
  obtain ⟨L, hL, hLT⟩ := weylMatrix_conj_e6T3W_mem_orbit w
  have hcolJ : ∀ j ∈ supportA2A2, ∀ i ∉ supportA2A2, lget L i j = 0 := by
    intro j hj i hi
    have hsingle : (Pi.single j 1 : Fin Tag.E6.rank → ℤ) ∈
        parabolicRoots Tag.E6 supportA2A2 :=
      ⟨isRoot_single Tag.E6 j, fun i' hi' =>
        Pi.single_eq_of_ne (fun h => hi' (by rw [h]; exact hj)) 1⟩
    have h := (hT _ hsingle).2 i hi
    rw [smul_single_apply_eq_lget hLT] at h
    exact h
  have hmemJ : ∀ j : Fin Tag.E6.rank, (j = 0 ∨ j = 2 ∨ j = 4 ∨ j = 5) → j ∈ supportA2A2 := by
    intro j hj
    rw [mem_supportA2A2]
    exact hj
  have hnJ : ∀ i : Fin Tag.E6.rank, (i = 1 ∨ i = 3) → i ∉ supportA2A2 := by
    intro i hi hmem
    rw [mem_supportA2A2] at hmem
    revert hi hmem
    revert i
    decide
  obtain ⟨hblk, -, -⟩ := e6T3Orbit_A2A2_shape L hL
    ⟨hcolJ 0 (hmemJ 0 (Or.inl rfl)) 1 (hnJ 1 (Or.inl rfl)),
      hcolJ 0 (hmemJ 0 (Or.inl rfl)) 3 (hnJ 3 (Or.inr rfl)),
      hcolJ 2 (hmemJ 2 (Or.inr (Or.inl rfl))) 1 (hnJ 1 (Or.inl rfl)),
      hcolJ 2 (hmemJ 2 (Or.inr (Or.inl rfl))) 3 (hnJ 3 (Or.inr rfl)),
      hcolJ 4 (hmemJ 4 (Or.inr (Or.inr (Or.inl rfl)))) 1 (hnJ 1 (Or.inl rfl)),
      hcolJ 4 (hmemJ 4 (Or.inr (Or.inr (Or.inl rfl)))) 3 (hnJ 3 (Or.inr rfl)),
      hcolJ 5 (hmemJ 5 (Or.inr (Or.inr (Or.inr rfl)))) 1 (hnJ 1 (Or.inl rfl)),
      hcolJ 5 (hmemJ 5 (Or.inr (Or.inr (Or.inr rfl)))) 3 (hnJ 3 (Or.inr rfl))⟩
  obtain ⟨hb40, hb50, hb42, hb52, hb04, hb24, hb05, hb25⟩ := hblk
  have hcol13 : ∀ j ∈ CFSG.RankThree.E6.support13, ∀ i ∉ CFSG.RankThree.E6.support13,
      lget L i j = 0 := by
    intro j hj i hi
    have hj' : j = e6Index 0 ∨ j = e6Index 2 := hj
    by_cases hiJ : i ∈ supportA2A2
    · rw [mem_supportA2A2] at hiJ
      rcases hj' with rfl | rfl <;> rcases hiJ with rfl | rfl | rfl | rfl <;>
        first | exact absurd (Or.inl rfl) hi | exact absurd (Or.inr rfl) hi | assumption
    · refine hcolJ j ?_ i hiJ
      rw [mem_supportA2A2]
      rcases hj' with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
  have hcol56 : ∀ j ∈ support56, ∀ i ∉ support56, lget L i j = 0 := by
    intro j hj i hi
    have hj' : j = e6Index 4 ∨ j = e6Index 5 := hj
    by_cases hiJ : i ∈ supportA2A2
    · rw [mem_supportA2A2] at hiJ
      rcases hj' with rfl | rfl <;> rcases hiJ with rfl | rfl | rfl | rfl <;>
        first | exact absurd (Or.inl rfl) hi | exact absurd (Or.inr rfl) hi | assumption
    · refine hcolJ j ?_ i hiJ
      rw [mem_supportA2A2]
      rcases hj' with h | h
      · exact Or.inr (Or.inr (Or.inl h))
      · exact Or.inr (Or.inr (Or.inr h))
  exact ⟨fun β hβ => smul_mem_parabolicRoots_of_lget hLT hcol13 hβ,
    fun β hβ => smul_mem_parabolicRoots_of_lget hLT hcol56 hβ⟩


theorem support56_root_cases : ∀ α ∈ rootFinset .E6, (∀ i : Fin Tag.E6.rank, i ≠ 4 → i ≠ 5 → α i = 0) →
    (α 5 = 1 ∨ α 5 = -1) ∨ (α = Pi.single 4 1 ∨ α = -Pi.single 4 1) := by
  decide +kernel

theorem subset_rootCharKernel_of_block {L : Type} [Field L] [IsAlgClosed L] {Fr : L →+* L}
    {q : ℕ} (hFr : ∀ c, Fr c = c ^ q) {S : Set (Fin Tag.E6.rank → ℤ)}
    (hvS : ∀ α ∈ S, e6T3W • α ∈ S) {w : WeylGroup Tag.E6} {i j : Fin Tag.E6.rank}
    {J : Set (Fin Tag.E6.rank)} (hJ : ∀ k, k ∈ J ↔ (k = i ∨ k = j)) (hij : i ≠ j)
    (hcases : ∀ α ∈ rootFinset .E6, (∀ k : Fin Tag.E6.rank, k ≠ i → k ≠ j → α k = 0) →
      (α j = 1 ∨ α j = -1) ∨ (α = Pi.single i 1 ∨ α = -Pi.single i 1))
    (hw : (w • ·) '' S = parabolicRoots Tag.E6 J)
    {b : Fin Tag.E6.rank → Lˣ} (hb : rootDiagUnit Tag.E6 b ∈ twistedTorusOf (tw6N L) (twistE6 L Fr))
    (hβ : rootChar b (w⁻¹ • (Pi.single i 1 : Fin Tag.E6.rank → ℤ)) = 1) :
    S ⊆ rootCharKernel b := by
  set β : Fin Tag.E6.rank → ℤ := w⁻¹ • (Pi.single i 1 : Fin Tag.E6.rank → ℤ) with hβdef
  set γ : Fin Tag.E6.rank → ℤ := w⁻¹ • (Pi.single j 1 : Fin Tag.E6.rank → ℤ) with hγdef
  have hker := (mem_twistedTorus_rootDiagUnit_iff6 hFr b).1 hb
  have hrel : ∀ μ, rootChar b (e6T3W • μ) * rootChar b μ ^ q = 1 := fun μ => by
    rw [← rootChar_tw6Matrix_mulVec]
    exact (mem_ker_monomialHom_iff_forall (tw6Matrix q) b).1 hker μ
  have hmemS : ∀ α ∈ S, w • α ∈ parabolicRoots Tag.E6 J := fun α hα => hw ▸ ⟨α, hα, rfl⟩
  have hrootS : ∀ α ∈ S, IsRoot Tag.E6 α := fun α hα => by
    have h := IsRoot.smul (hmemS α hα).1 w⁻¹
    simpa using h
  have hsupp : ∀ α ∈ S, ∀ k : Fin Tag.E6.rank, k ≠ i → k ≠ j → (w • α) k = 0 := by
    intro α hα k hki hkj
    exact (hmemS α hα).2 k (fun hk => by rcases (hJ k).1 hk with h | h <;> contradiction)
  have hdecomp : ∀ α ∈ S, α = (w • α) i • β + (w • α) j • γ := by
    intro α hα
    have hv : w • α = (w • α) i • (Pi.single i 1 : Fin Tag.E6.rank → ℤ) +
        (w • α) j • (Pi.single j 1 : Fin Tag.E6.rank → ℤ) := by
      funext k
      by_cases hki : k = i
      · subst hki; simp [hij]
      · by_cases hkj : k = j
        · subst hkj; simp [Ne.symm hij]
        · rw [hsupp α hα k hki hkj]; simp [hki, hkj]
    have := congrArg (w⁻¹ • ·) hv
    simp only [inv_smul_smul, smul_add, smul_comm w⁻¹ ((w • α) i), smul_comm w⁻¹ ((w • α) j)] at this
    exact this
  have hβS : β ∈ S := by
    have hmem : (Pi.single i 1 : Fin Tag.E6.rank → ℤ) ∈ parabolicRoots Tag.E6 J := by
      refine ⟨isRoot_single Tag.E6 i, fun k hk => ?_⟩
      have hki : k ≠ i := fun h => hk ((hJ k).2 (Or.inl h))
      simp [hki]
    rw [← hw] at hmem
    obtain ⟨α, hα, hαw⟩ := hmem
    rw [hβdef, ← hαw, inv_smul_smul]
    exact hα
  have huβ : e6T3W • β ∈ S := hvS β hβS
  have hχuβ : rootChar b (e6T3W • β) = 1 := by
    have h := hrel β
    rw [hβ, one_pow, mul_one] at h
    exact h
  obtain ⟨hne1, hne2⟩ := e6T3W_smul_ne (hrootS β hβS)
  have hcases' := hcases (w • (e6T3W • β)) (mem_rootFinset.2 (IsRoot.smul (hrootS _ huβ) w))
    (hsupp _ huβ)
  have hd := hdecomp _ huβ
  obtain ⟨A, hA⟩ : ∃ A, (w • (e6T3W • β)) i = A := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B, (w • (e6T3W • β)) j = B := ⟨_, rfl⟩
  rw [hA, hB] at hd
  rw [hB] at hcases'
  have hγ : rootChar b γ = 1 := by
    rcases hcases' with h | h
    · rcases h with h | h
      · have e : γ = e6T3W • β + (-A) • β := by
          rw [hd, h, one_smul, neg_smul]; abel
        rw [e, rootChar_add, rootChar_zsmul, hχuβ, hβ, one_zpow, mul_one]
      · have e : γ = A • β + (-1 : ℤ) • (e6T3W • β) := by
          rw [hd, h]; simp only [neg_smul, one_smul, neg_add_rev, neg_neg]; abel
        rw [e, rootChar_add, rootChar_zsmul, rootChar_zsmul, hχuβ, hβ, one_zpow, one_zpow, mul_one]
    · exfalso
      rcases h with h | h
      · have e := congrArg (w⁻¹ • ·) h
        simp only [inv_smul_smul] at e
        exact hne1 e
      · have e := congrArg (w⁻¹ • ·) h
        simp only [inv_smul_smul, smul_neg] at e
        exact hne2 e
  intro α hα
  refine ⟨hrootS α hα, ?_⟩
  rw [hdecomp α hα, rootChar_add, rootChar_zsmul, rootChar_zsmul, hβ, hγ, one_zpow, one_zpow,
    mul_one]


theorem supportA2A2_root_split : ∀ α ∈ rootFinset .E6,
    (α 1 = 0 ∧ α 3 = 0) → (α 4 = 0 ∧ α 5 = 0) ∨ (α 0 = 0 ∧ α 2 = 0) := by
  decide +kernel

section Layer

variable {K : Type} [Field K] {σ : K ≃+* K} {L : Type} [Field L] [Algebra K L]

theorem exists_psiT_eq_of_mem {Fr : L →+* L} {g0 : ModGL Tag.E6 L}
    (hg0C : g0 ∈ adjointGroup Tag.E6 L) (hg0 : twistE6 L Fr g0 = g0 * tw6N L)
    (hperf : ∀ P : Subgroup (ModGL Tag.E6 L), Finite P → P ≤ adjointGroup Tag.E6 L →
      (∀ x ∈ P, twistE6 L Fr x = x) → ⁅P, P⁆ = P → P ≤ (twE6Emb K σ L).range)
    (c : twistedE6RootGroup K σ) {P : Subgroup (ModGL Tag.E6 L)} (hPfin : Finite P)
    (hPperf : ⁅P, P⁆ = P) (hPadj : P ≤ adjointGroup Tag.E6 L)
    (hPfix : ∀ u ∈ P, tw6N L * twistE6 L Fr u * (tw6N L)⁻¹ = u) {u : ModGL Tag.E6 L}
    (hu : u ∈ P) : ∃ x : twistedE6RootGroup K σ, psiT g0 c x = u := by
  set P' : Subgroup (ModGL Tag.E6 L) := P.map (MulAut.conj g0).toMonoidHom with hP'
  have hP'adj : P' ≤ adjointGroup Tag.E6 L := by
    rintro _ ⟨v, hv, rfl⟩
    exact mul_mem (mul_mem hg0C (hPadj hv)) (inv_mem hg0C)
  have hP'fix : ∀ w ∈ P', twistE6 L Fr w = w := by
    rintro _ ⟨v, hv, rfl⟩
    have hvR := hPfix v hv
    change twistE6 L Fr (g0 * v * g0⁻¹) = g0 * v * g0⁻¹
    rw [map_mul, map_mul, map_inv, hg0]
    calc g0 * tw6N L * twistE6 L Fr v * (g0 * tw6N L)⁻¹ =
          g0 * (tw6N L * twistE6 L Fr v * (tw6N L)⁻¹) * g0⁻¹ := by group
      _ = g0 * v * g0⁻¹ := by rw [hvR]
  have hP'perf : ⁅P', P'⁆ = P' := by
    rw [hP', ← Subgroup.map_commutator, hPperf]
  have hP'fin : Finite P' := Finite.of_surjective
    ((MulAut.conj g0).toMonoidHom.subgroupMap P)
    ((MulAut.conj g0).toMonoidHom.subgroupMap_surjective P)
  have hmem : g0 * u * g0⁻¹ ∈ P' := Subgroup.mem_map_of_mem _ hu
  obtain ⟨y', hy'⟩ := hperf P' hP'fin hP'adj hP'fix hP'perf hmem
  refine ⟨c⁻¹ * y' * c, ?_⟩
  simp only [psiT]
  have h1 : c * (c⁻¹ * y' * c) * c⁻¹ = y' := by group
  rw [h1, hy']
  group

end Layer

@[expose] def TwoA2Split (L : Type) [Field L] (Fr : L →+* L) (S₁ S₂ : Set (Fin Tag.E6.rank → ℤ)) :
    Prop :=
  ∀ m ∈ torusGroup Tag.E6 L ⊔ rootSpan Tag.E6 L (S₁ ∪ S₂), tw6Theta L Fr m = m →
    ∃ t ∈ torusGroup Tag.E6 L, tw6Theta L Fr t = t ∧ ∃ a₁ ∈ rootSpan Tag.E6 L S₁,
      tw6Theta L Fr a₁ = a₁ ∧ ∃ a₂ ∈ rootSpan Tag.E6 L S₂, tw6Theta L Fr a₂ = a₂ ∧ m = t * a₁ * a₂


theorem le_hyperClosure_of_kernel_A2A2 {ℓ f : ℕ} [Fact ℓ.Prime] (K : Type) [Field K] [Finite K]
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
    {y : twistedE6RootGroup K σ} (hy : y ∈ E) (hy1 : y ≠ 1) {w : WeylGroup Tag.E6}
    (hw : (w • ·) '' torusRootKernel (psiT g0 c y) = parabolicRoots Tag.E6 supportA2A2)
    (hsplit : TwoA2Split L (iterateFrobenius L ℓ f)
      ((fun α => w⁻¹ • α) '' parabolicRoots Tag.E6 support13)
      ((fun α => w⁻¹ • α) '' parabolicRoots Tag.E6 support56))
    {k : twistedE6RootGroup K σ} (hk : k * y = y * k) :
    k ∈ hyperClosure p ⊤ E := by
  classical
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  have hℓ : ℓ.Prime := Fact.out
  set Fr : L →+* L := iterateFrobenius L ℓ f with hFrdef
  have hFr : ∀ c, Fr c = c ^ (ℓ ^ f) := fun c => iterateFrobenius_def ℓ f c
  have hyo : orderOf y = p := orderOf_eq_prime (hE.2 y hy) hy1
  set Sx := torusRootKernel (psiT g0 c y) with hSxdef
  have hvS := tw6_torusRootKernel_smul_stable hFr (hT y hy)
  have hT' : ∀ β ∈ parabolicRoots Tag.E6 supportA2A2,
      (w * e6T3W * w⁻¹) • β ∈ parabolicRoots Tag.E6 supportA2A2 := by
    intro β hβ
    rw [← hw] at hβ ⊢
    obtain ⟨α, hα, rfl⟩ := hβ
    exact ⟨e6T3W • α, hvS α hα, by simp [mul_smul]⟩
  obtain ⟨hT13, hT56⟩ := conj_e6T3W_preserves_blocks hT'
  set S₁ : Set (Fin Tag.E6.rank → ℤ) :=
    (fun α => w⁻¹ • α) '' parabolicRoots Tag.E6 support13 with hS₁
  set S₂ : Set (Fin Tag.E6.rank → ℤ) :=
    (fun α => w⁻¹ • α) '' parabolicRoots Tag.E6 support56 with hS₂
  have hw₁ : (w • ·) '' S₁ = parabolicRoots Tag.E6 support13 := by
    rw [hS₁, Set.image_image]
    simp
  have hw₂ : (w • ·) '' S₂ = parabolicRoots Tag.E6 support56 := by
    rw [hS₂, Set.image_image]
    simp
  have hvS₁ : ∀ α ∈ S₁, e6T3W • α ∈ S₁ := by
    rintro _ ⟨β, hβ, rfl⟩
    exact ⟨(w * e6T3W * w⁻¹) • β, hT13 β hβ, by simp [mul_smul]⟩
  have hvS₂ : ∀ α ∈ S₂, e6T3W • α ∈ S₂ := by
    rintro _ ⟨β, hβ, rfl⟩
    exact ⟨(w * e6T3W * w⁻¹) • β, hT56 β hβ, by simp [mul_smul]⟩
  have hSx : Sx = S₁ ∪ S₂ := by
    ext α
    constructor
    · intro hα
      have hmem : w • α ∈ parabolicRoots Tag.E6 supportA2A2 := hw ▸ ⟨α, hα, rfl⟩
      have h13 : (w • α) 1 = 0 ∧ (w • α) 3 = 0 := by
        refine ⟨hmem.2 1 ?_, hmem.2 3 ?_⟩ <;> (rw [mem_supportA2A2]; decide)
      rcases supportA2A2_root_split _ (mem_rootFinset.2 hmem.1) h13 with h | h
      · left
        refine ⟨w • α, ⟨hmem.1, fun i hi => ?_⟩, by simp⟩
        have hiA : i ∈ supportA2A2 ∨ i ∉ supportA2A2 := em _
        rcases hiA with hiA | hiA
        · rw [mem_supportA2A2] at hiA
          rcases hiA with rfl | rfl | rfl | rfl
          · exact absurd (Or.inl rfl) hi
          · exact absurd (Or.inr rfl) hi
          · exact h.1
          · exact h.2
        · exact hmem.2 i hiA
      · right
        refine ⟨w • α, ⟨hmem.1, fun i hi => ?_⟩, by simp⟩
        have hiA : i ∈ supportA2A2 ∨ i ∉ supportA2A2 := em _
        rcases hiA with hiA | hiA
        · rw [mem_supportA2A2] at hiA
          rcases hiA with rfl | rfl | rfl | rfl
          · exact h.1
          · exact h.2
          · exact absurd (Or.inl rfl) hi
          · exact absurd (Or.inr rfl) hi
        · exact hmem.2 i hiA
    · rintro (⟨β, hβ, rfl⟩ | ⟨β, hβ, rfl⟩)
      · have hβA : β ∈ parabolicRoots Tag.E6 supportA2A2 :=
          ⟨hβ.1, fun i hi => hβ.2 i (fun hi' => hi (by
            rw [mem_supportA2A2]
            rcases hi' with h | h
            · exact Or.inl h
            · exact Or.inr (Or.inl h)))⟩
        rw [← hw] at hβA
        obtain ⟨α, hα, rfl⟩ := hβA
        simpa using hα
      · have hβA : β ∈ parabolicRoots Tag.E6 supportA2A2 :=
          ⟨hβ.1, fun i hi => hβ.2 i (fun hi' => hi (by
            rw [mem_supportA2A2]
            rcases hi' with h | h
            · exact Or.inr (Or.inr (Or.inl h))
            · exact Or.inr (Or.inr (Or.inr h))))⟩
        rw [← hw] at hβA
        obtain ⟨α, hα, rfl⟩ := hβA
        simpa using hα
  have hET : ∀ e ∈ E, psiT g0 c e ∈ torusGroup Tag.E6 L :=
    fun e he => (mem_twistedTorusOf.1 (hT e he)).1
  have hblock : ∀ (i j : Fin Tag.E6.rank) (J : Set (Fin Tag.E6.rank)) (S : Set (Fin Tag.E6.rank → ℤ)),
      (∀ k, k ∈ J ↔ (k = i ∨ k = j)) → i ≠ j →
      (∀ α ∈ rootFinset .E6, (∀ k : Fin Tag.E6.rank, k ≠ i → k ≠ j → α k = 0) →
        (α j = 1 ∨ α j = -1) ∨ (α = Pi.single i 1 ∨ α = -Pi.single i 1)) →
      (∀ α ∈ S, e6T3W • α ∈ S) → (w • ·) '' S = parabolicRoots Tag.E6 J →
      ∃ e ∈ E, e ∉ Subgroup.zpowers y ∧
        rootSpan Tag.E6 L S ≤ Subgroup.centralizer {psiT g0 c e} := by
    intro i j J S hJ hij hcases hvS' hwS
    have hβroot : IsRoot Tag.E6 (w⁻¹ • (Pi.single i 1 : Fin Tag.E6.rank → ℤ)) :=
      IsRoot.smul (isRoot_single Tag.E6 i) w⁻¹
    obtain ⟨⟨e, he⟩, hey, hχe⟩ := exists_mem_ker_not_mem_zpowers hE hEc
      (cubeChar g0 c hET (w⁻¹ • (Pi.single i 1 : Fin Tag.E6.rank → ℤ))) hy
    obtain ⟨b, hb⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup (hET e he)
    have hbβ := (cubeChar_eq_one_iff hET hβroot ⟨e, he⟩ hb).1 hχe
    have hbT : rootDiagUnit Tag.E6 b ∈ twistedTorusOf (tw6N L) (twistE6 L Fr) := by
      rw [← hb]
      exact hT e he
    have hsub := subset_rootCharKernel_of_block hFr hvS' hJ hij hcases hwS hbT hbβ
    refine ⟨e, he, hey, ?_⟩
    rw [hb]
    exact CFSG.LieType.Chevalley.rootSpan_le_centralizer b hsub
  obtain ⟨e₁, he₁, he₁y, hc₁⟩ := hblock 0 2 support13 S₁ (fun k => Iff.rfl) (by decide)
    support13_root_cases hvS₁ hw₁
  obtain ⟨e₂, he₂, he₂y, hc₂⟩ := hblock 4 5 support56 S₂ (fun k => Iff.rfl) (by decide)
    support56_root_cases hvS₂ hw₂
  have : Module.Finite (fixSubfield σ) K := Module.Finite.of_finite
  have : Algebra.IsAlgebraic (fixSubfield σ) K := Algebra.IsAlgebraic.of_finite _ K
  have : IsAlgClosure (fixSubfield σ) L := IsAlgClosure.ofAlgebraic (fixSubfield σ) K L
  have : Finite (fixSubfield σ) := inferInstance
  have hkc : Nat.card (fixSubfield σ) = ℓ ^ f := card_fixSubfield_twisted hℓ hf hK σ hσ
  have hp7 : 7 ≤ p := (e6Six_data hpF.out hp3 hpq).2.2.2.2.1
  have hq3 : 3 ≤ ℓ ^ f := by
    by_contra hlt
    have hq2 : 2 ≤ ℓ ^ f := Nat.one_lt_pow (by omega) hℓ.one_lt
    have h2 : ℓ ^ f = 2 := by omega
    rw [h2] at hpq
    norm_num at hpq
    have := Int.le_of_dvd (by norm_num) hpq
    omega
  have hroots₁ : ∀ α ∈ S₁, IsRoot Tag.E6 α := by
    rintro _ ⟨β, hβ, rfl⟩
    exact IsRoot.smul hβ.1 w⁻¹
  have hroots₂ : ∀ α ∈ S₂, IsRoot Tag.E6 α := by
    rintro _ ⟨β, hβ, rfl⟩
    exact IsRoot.smul hβ.1 w⁻¹
  obtain ⟨-, hfin₁, hq₁, -⟩ := tw6_A2_layer_gen (Fr := Fr) hf hkc hq3 hFr hroots₁ hvS₁ hw₁
  obtain ⟨-, hfin₂, hq₂, -⟩ := tw6_A2_layer_gen₂ (Fr := Fr) hf hkc hq3 hFr hroots₂ hvS₂ hw₂
  have hyo' : orderOf y = p := hyo
  obtain ⟨ι', KL, ψ, -, hψ, hspan, hfix, -⟩ := tw6_perx K hf hK σ hσ hpF.out hp3 hpq L hg0C hg0
    hperf hyo' c (hT y hy)
  have hkC : k ∈ Subgroup.centralizer ({y} : Set (twistedE6RootGroup K σ)) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact hk
  have hψk : psiT g0 c k ∈ torusGroup Tag.E6 L ⊔ rootSpan Tag.E6 L (S₁ ∪ S₂) := by
    have h := hspan ⟨k, hkC⟩
    rw [hψ] at h
    change psiT g0 c k ∈ torusGroup Tag.E6 L ⊔ rootSpan Tag.E6 L Sx at h
    rw [hSx] at h
    exact h
  have hθk : tw6Theta L Fr (psiT g0 c k) = psiT g0 c k := by
    have h := hfix ⟨k, hkC⟩
    rw [hψ] at h
    rw [tw6Theta_apply]
    exact h
  obtain ⟨t, htH, htθ, a₁, ha₁S, ha₁θ, a₂, ha₂S, ha₂θ, hdec⟩ := hsplit _ hψk hθk
  obtain ⟨b, hb⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup (hET y hy)
  have hcy : rootSpan Tag.E6 L Sx ≤ Subgroup.centralizer {psiT g0 c y} := by
    rw [hb]
    refine CFSG.LieType.Chevalley.rootSpan_le_centralizer b ?_
    rw [hSxdef, hb, torusRootKernel_rootDiagUnit]
  have hland : ∀ (S : Set (Fin Tag.E6.rank → ℤ)), S ⊆ Sx →
      Finite ↥(rootSpan Tag.E6 L S ⊓ (tw6Theta L Fr).eqLocus (MonoidHom.id _)) →
      CFSG.IsQuasisimple ↥(rootSpan Tag.E6 L S ⊓ (tw6Theta L Fr).eqLocus (MonoidHom.id _)) →
      ∀ a ∈ rootSpan Tag.E6 L S, tw6Theta L Fr a = a →
        ∃ x : twistedE6RootGroup K σ, psiT g0 c x = a ∧ x * y = y * x := by
    intro S hS hfinS hqS a haS haθ
    have hperfS := Subgroup.isPerfect_iff.1 hqS.1
    have hadjS : rootSpan Tag.E6 L S ⊓ (tw6Theta L Fr).eqLocus (MonoidHom.id _) ≤
        adjointGroup Tag.E6 L := fun u hu => rootSpan_le_adjointGroup L S hu.1
    have hfixS : ∀ u ∈ rootSpan Tag.E6 L S ⊓ (tw6Theta L Fr).eqLocus (MonoidHom.id _),
        tw6N L * twistE6 L Fr u * (tw6N L)⁻¹ = u := fun u hu => by
      rw [← tw6Theta_apply]
      exact hu.2
    obtain ⟨x, hx⟩ := exists_psiT_eq_of_mem hg0C hg0 hperf c hfinS hperfS hadjS hfixS
      (u := a) ⟨haS, haθ⟩
    refine ⟨x, hx, ?_⟩
    have hca : a ∈ Subgroup.centralizer {psiT g0 c y} :=
      hcy (CFSG.LieType.Chevalley.rootSpan_mono hS haS)
    have hc := Subgroup.mem_centralizer_singleton_iff.1 hca
    rw [← hx] at hc
    exact commute_of_psiT_commute hc
  have hS₁x : S₁ ⊆ Sx := by rw [hSx]; exact Set.subset_union_left
  have hS₂x : S₂ ⊆ Sx := by rw [hSx]; exact Set.subset_union_right
  obtain ⟨x₁, hx₁, hx₁y⟩ := hland S₁ hS₁x hfin₁ hq₁ a₁ ha₁S ha₁θ
  obtain ⟨x₂, hx₂, hx₂y⟩ := hland S₂ hS₂x hfin₂ hq₂ a₂ ha₂S ha₂θ
  set k₀ := k * x₂⁻¹ * x₁⁻¹ with hk₀
  have hψk₀ : psiT g0 c k₀ = t := by
    rw [hk₀, psiT_mul, psiT_mul, psiT_inv, psiT_inv, hx₁, hx₂, hdec]
    group
  have hk₀y : k₀ * y = y * k₀ :=
    (((show Commute k y from hk).mul_left (show Commute x₂ y from hx₂y).inv_left).mul_left
      (show Commute x₁ y from hx₁y).inv_left).eq
  have hk₀e : k₀ * e₁ = e₁ * k₀ :=
    commute_of_psiT_commute (by rw [hψk₀]; exact torusGroup_comm htH (hET e₁ he₁))
  have hx₁e : x₁ * e₁ = e₁ * x₁ := by
    have h := Subgroup.mem_centralizer_singleton_iff.1 (hc₁ ha₁S)
    rw [← hx₁] at h
    exact commute_of_psiT_commute h
  have hx₂e : x₂ * e₂ = e₂ * x₂ := by
    have h := Subgroup.mem_centralizer_singleton_iff.1 (hc₂ ha₂S)
    rw [← hx₂] at h
    exact commute_of_psiT_commute h
  have hkeq : k = k₀ * x₁ * x₂ := by rw [hk₀]; group
  rw [hkeq]
  exact mul_mem (mul_mem
    (mem_hyperClosure_of_commute_pair hE hEc hy he₁ hy1 he₁y hk₀y hk₀e)
    (mem_hyperClosure_of_commute_pair hE hEc hy he₁ hy1 he₁y hx₁y hx₁e))
    (mem_hyperClosure_of_commute_pair hE hEc hy he₂ hy1 he₂y hx₂y hx₂e)

end CFSG.HardMathSupport.Lang.TwE6Step3
