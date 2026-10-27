module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeF4CubeHyperGen
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeF4CubeHyperDefs
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.SeitzExcOpenRest8b

public noncomputable section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeF4Close

open Matrix CFSG.Open TauCeti CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.SeitzGeneration CFSG.LieType.SeitzGeneration.ExcHigh
  CFSG.LieType.SeitzGeneration.ExcHighThree CFSG.RankThree.PartOne.KE CFSG.RankThree.PartOne.KF4
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Foote.Coordinator.SplitFrame
  CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.DetectF4
open scoped MatrixGroups

set_option linter.unusedSectionVars false

section Pairs

variable {G : Type*} [Group G] {K : Type*} [Field K]

@[expose] def frameActPairs (ψ : SL(3, K) →* G) : Subgroup (G × GL (Fin 3) K) where
  carrier := {p | ∀ s, p.1 * ψ s * p.1⁻¹ = ψ (E6Three.conjSL p.2 s)}
  one_mem' := by
    show ∀ s, (1 : G × GL (Fin 3) K).1 * ψ s * (1 : G × GL (Fin 3) K).1⁻¹ =
      ψ (E6Three.conjSL (1 : G × GL (Fin 3) K).2 s)
    intro s
    rw [Prod.fst_one, Prod.snd_one, map_one, MulAut.one_apply, one_mul, inv_one, mul_one]
  mul_mem' := by
    intro p q hp hq
    have hp' : ∀ s, p.1 * ψ s * p.1⁻¹ = ψ (E6Three.conjSL p.2 s) := hp
    have hq' : ∀ s, q.1 * ψ s * q.1⁻¹ = ψ (E6Three.conjSL q.2 s) := hq
    show ∀ s, (p * q).1 * ψ s * (p * q).1⁻¹ = ψ (E6Three.conjSL (p * q).2 s)
    intro s
    rw [Prod.fst_mul, Prod.snd_mul, map_mul, MulAut.mul_apply, ← hp', ← hq']
    group
  inv_mem' := by
    intro p hp
    have hp' : ∀ s, p.1 * ψ s * p.1⁻¹ = ψ (E6Three.conjSL p.2 s) := hp
    show ∀ s, p⁻¹.1 * ψ s * p⁻¹.1⁻¹ = ψ (E6Three.conjSL p⁻¹.2 s)
    intro s
    have h1 := hp' (E6Three.conjSL p.2⁻¹ s)
    have h2 : E6Three.conjSL p.2 (E6Three.conjSL p.2⁻¹ s) = s := by
      rw [← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one, MulAut.one_apply]
    rw [h2] at h1
    rw [Prod.fst_inv, Prod.snd_inv, inv_inv, ← h1]
    group

theorem mem_frameActPairs {ψ : SL(3, K) →* G} {p : G × GL (Fin 3) K} :
    p ∈ frameActPairs ψ ↔ ∀ s, p.1 * ψ s * p.1⁻¹ = ψ (E6Three.conjSL p.2 s) :=
  Iff.rfl

theorem toGL_mem_frameActPairs (ψ : SL(3, K) →* G) (a : SL(3, K)) :
    (ψ a, SpecialLinearGroup.toGL a) ∈ frameActPairs ψ :=
  mem_frameActPairs.2 fun s => by
    dsimp only
    rw [E6Three.conjSL_toGL, MulAut.conj_apply, map_mul, map_mul, map_inv]

theorem one_mem_frameActPairs_of_commute {ψ : SL(3, K) →* G} {g : G}
    (h : ∀ s, Commute g (ψ s)) : (g, (1 : GL (Fin 3) K)) ∈ frameActPairs ψ :=
  mem_frameActPairs.2 fun s => by
    dsimp only
    rw [map_one, MulAut.one_apply]
    exact mul_inv_eq_iff_eq_mul.2 (h s).eq

theorem scalar_mem_frameActPairs (ψ : SL(3, K) →* G) (u : Kˣ) :
    ((1 : G), GeneralLinearGroup.scalar (Fin 3) u) ∈ frameActPairs ψ :=
  mem_frameActPairs.2 fun s => by
    dsimp only
    rw [E6Three.conjSL_scalar, MulAut.one_apply, one_mul, inv_one, mul_one]

theorem mul_pow_mem_frameActPairs {ψ : SL(3, K) →* G} {m m' : G} {γ γ' : GL (Fin 3) K}
    (h : (m, γ) ∈ frameActPairs ψ) (h' : (m', γ') ∈ frameActPairs ψ) (k : ℕ) :
    (m * m' ^ k, γ * γ' ^ k) ∈ frameActPairs ψ := by
  have h1 := pow_mem h' k
  rw [Prod.pow_mk] at h1
  have h2 := mul_mem h h1
  rw [Prod.mk_mul_mk] at h2
  exact h2

theorem conj_mem_frameActPairs {ψ : SL(3, K) →* G} {k m : G} {δ γ : GL (Fin 3) K}
    (hk : (k, δ) ∈ frameActPairs ψ) (hm : (m, γ) ∈ frameActPairs ψ) :
    (k * m * k⁻¹, δ * γ * δ⁻¹) ∈ frameActPairs ψ := by
  have h1 := mul_mem hk hm
  rw [Prod.mk_mul_mk] at h1
  have h2 := mul_mem h1 (inv_mem hk)
  rw [Prod.inv_mk, Prod.mk_mul_mk] at h2
  exact h2

theorem exists_smul_of_mem_frameActPairs {ψ : SL(3, K) →* G} (hψ : Function.Injective ψ)
    {m : G} {γ γ' : GL (Fin 3) K} (h : (m, γ) ∈ frameActPairs ψ)
    (h' : (m, γ') ∈ frameActPairs ψ) :
    ∃ c : K, (γ' : Matrix (Fin 3) (Fin 3) K) = c • (γ : Matrix (Fin 3) (Fin 3) K) := by
  have hfix : ∀ s, E6Three.conjSL (γ⁻¹ * γ') s = s := by
    intro s
    have h1 : E6Three.conjSL γ' s = E6Three.conjSL γ s :=
      hψ (((mem_frameActPairs.1 h') s).symm.trans ((mem_frameActPairs.1 h) s))
    rw [map_mul, MulAut.mul_apply, h1, ← MulAut.mul_apply, ← map_mul, inv_mul_cancel, map_one,
      MulAut.one_apply]
  have hcomm : ∀ t : Matrix.TransvectionStruct (Fin 3) K,
      Commute t.toMatrix ((γ⁻¹ * γ' : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := fun t =>
    (E6Three.conjSL_apply_eq_self_iff.1 (hfix t.toSpecialLinearGroup)).symm
  obtain ⟨c, hc⟩ := Matrix.mem_range_scalar_of_commute_transvectionStruct hcomm
  refine ⟨c, ?_⟩
  have h2 : (γ' : Matrix (Fin 3) (Fin 3) K) =
      (γ : Matrix (Fin 3) (Fin 3) K) * ((γ⁻¹ * γ' : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
    rw [← Units.val_mul, mul_inv_cancel_left]
  rw [h2, ← hc, Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal, Matrix.mul_smul,
    Matrix.mul_one]

theorem exists_pow_three_eq_smul_of_mem_frameActPairs {ψ : SL(3, K) →* G}
    (hψ : Function.Injective ψ) {m : G} {γ : GL (Fin 3) K} (h : (m, γ) ∈ frameActPairs ψ)
    (hm : m ^ 3 = 1) : ∃ c : K, (γ : Matrix (Fin 3) (Fin 3) K) ^ 3 = c • 1 := by
  have h3 : ((1 : G), γ ^ 3) ∈ frameActPairs ψ := by
    have := pow_mem h 3
    rwa [Prod.pow_mk, hm] at this
  have h1 : ((1 : G), (1 : GL (Fin 3) K)) ∈ frameActPairs ψ := one_mem _
  obtain ⟨c, hc⟩ := exists_smul_of_mem_frameActPairs hψ h1 h3
  refine ⟨c, ?_⟩
  rw [← Units.val_pow_eq_pow_val, hc, Units.val_one]

theorem exists_toGL_eq_mul_scalar {γ : GL (Fin 3) K} {μ : Kˣ}
    (h : μ ^ 3 = GeneralLinearGroup.det γ) :
    ∃ M : SL(3, K), SpecialLinearGroup.toGL M = γ * GeneralLinearGroup.scalar (Fin 3) μ⁻¹ := by
  have hu : GeneralLinearGroup.det (γ * GeneralLinearGroup.scalar (Fin 3) μ⁻¹) = 1 := by
    rw [map_mul, GeneralLinearGroup.det_scalar, Fintype.card_fin, ← h, inv_pow, mul_inv_cancel]
  have hdet : ((γ * GeneralLinearGroup.scalar (Fin 3) μ⁻¹ : GL (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K).det = 1 := by
    rw [← GeneralLinearGroup.val_det_apply, hu, Units.val_one]
  exact ⟨⟨_, hdet⟩, Units.ext rfl⟩

open scoped Pointwise in
private theorem exists_mul_of_mem_sup_of_le_normalizer {H N : Subgroup G}
    (hLE : N ≤ Subgroup.normalizer (H : Set G)) {g : G} (hg : g ∈ H ⊔ N) :
    ∃ x ∈ H, ∃ t ∈ N, g = x * t := by
  have h : g ∈ (H : Set G) * (N : Set G) := by
    rw [← Subgroup.coe_mul_of_right_le_normalizer_left H N hLE]
    exact hg
  obtain ⟨x, hx, t, ht, hxt⟩ := Set.mem_mul.1 h
  exact ⟨x, hx, t, ht, hxt.symm⟩

end Pairs

section Det

variable {G : Type*} [Group G] {K : Type*} [Field K]

@[expose] def frameDetPair : G × (GL (Fin 3) K × GL (Fin 3) K) →* Kˣ × Kˣ :=
  ((GeneralLinearGroup.det : GL (Fin 3) K →* Kˣ).prodMap GeneralLinearGroup.det).comp
    (MonoidHom.snd _ _)

@[expose] def frameActTriples (ψA ψB : SL(3, K) →* G) :
    Subgroup (G × (GL (Fin 3) K × GL (Fin 3) K)) :=
  (frameActPairs ψA).comap ((MonoidHom.id G).prodMap (MonoidHom.fst _ _)) ⊓
    (frameActPairs ψB).comap ((MonoidHom.id G).prodMap (MonoidHom.snd _ _))

@[expose] def frameDetSub (ψA ψB : SL(3, K) →* G) (Q : Subgroup (Kˣ × Kˣ)) : Subgroup G :=
  (frameActTriples ψA ψB ⊓ Q.comap frameDetPair).map (MonoidHom.fst _ _)

theorem mem_frameDetSub {ψA ψB : SL(3, K) →* G} {Q : Subgroup (Kˣ × Kˣ)} {m : G} :
    m ∈ frameDetSub ψA ψB Q ↔ ∃ γA γB : GL (Fin 3) K, (m, γA) ∈ frameActPairs ψA ∧
      (m, γB) ∈ frameActPairs ψB ∧
        (GeneralLinearGroup.det γA, GeneralLinearGroup.det γB) ∈ Q := by
  constructor
  · rintro ⟨⟨m', γA, γB⟩, ⟨⟨hA, hB⟩, hQ⟩, rfl⟩
    exact ⟨γA, γB, hA, hB, hQ⟩
  · rintro ⟨γA, γB, hA, hB, hQ⟩
    exact ⟨(m, γA, γB), ⟨⟨hA, hB⟩, hQ⟩, rfl⟩

end Det

section Diagonal

variable {K : Type} [Field K]

theorem det_diagGL3_eq_prod (d : Fin 3 → Kˣ) :
    GeneralLinearGroup.det (diagGL3 d) = ∏ j, d j := by
  apply Units.ext
  rw [GeneralLinearGroup.val_det_apply, Units.coe_prod]
  exact Matrix.det_diagonal

theorem offDiag_eq_zero_of_mul_diagGL3 {a : SL(3, K)} {d : Fin 3 → Kˣ}
    {D : Matrix (Fin 3) (Fin 3) K} {c : K} (hD : ∀ i j, i ≠ j → D i j = 0)
    (h : ((SpecialLinearGroup.toGL a * diagGL3 d : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      c • D) :
    ∀ i j, i ≠ j → (a : Matrix (Fin 3) (Fin 3) K) i j = 0 := by
  intro i j hij
  have h1 := congrFun (congrFun h i) j
  have h2 : ((SpecialLinearGroup.toGL a * diagGL3 d : GL (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K) i j = (a : Matrix (Fin 3) (Fin 3) K) i j * (d j : K) := by
    rw [Units.val_mul, SpecialLinearGroup.coe_GL_coe_matrix]
    exact Matrix.mul_diagonal _ _ _ _
  rw [h2, Matrix.smul_apply, hD i j hij, smul_zero] at h1
  exact (mul_eq_zero.1 h1).resolve_right (d j).ne_zero

end Diagonal

section Torus


theorem rootDiagUnit_mem_frameActPairs {τ : Tag} {K : Type} [Field K]
    {ρ : SL(3, K) →* ModGL τ K} {σ : Fin 3 → Fin 3 → Fin τ.rank → ℤ} (hfr : IsA2Frame ρ σ)
    (b : Fin τ.rank → Kˣ) :
    (rootDiagUnit τ b, diagGL3 fun j => rootChar b (σ j 0)) ∈ frameActPairs ρ :=
  mem_frameActPairs.2 fun s => by
    dsimp only
    rw [E6Three.conjSL_diagGL3]
    exact hfr.torus b s

end Torus

section Datum


theorem exists_langPlaneData_w_one {τ : Tag} {K : Type} [Field K] [Finite K]
    {A : Subgroup (adjointGroup τ K)} (c : adjointGroup τ K)
    (hc : ∀ x ∈ A, ((c * x * c⁻¹ : adjointGroup τ K) : ModGL τ K) ∈ torusGroup τ K) :
    ∃ D : LangPlaneData τ K A, D.w = 1 := by
  classical
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨f, hℓ, hf⟩ := FiniteField.card K (ringChar K)
  have : Fact (ringChar K).Prime := ⟨hℓ⟩
  have : CharP K (ringChar K) := ringChar.charP K
  have : CharP (AlgebraicClosure K) (ringChar K) :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective _
  obtain ⟨Fr, hFrdef⟩ : ∃ Fr : AlgebraicClosure K →+* AlgebraicClosure K,
      Fr = iterateFrobenius (AlgebraicClosure K) (ringChar K) f := ⟨_, rfl⟩
  have hFr : ∀ a : AlgebraicClosure K, Fr a = a ^ Nat.card K := fun a => by
    rw [hFrdef, iterateFrobenius_def, Nat.card_eq_fintype_card, hf]
  have hcomp : Fr.comp (algebraMap K (AlgebraicClosure K)) = algebraMap K (AlgebraicClosure K) := by
    refine RingHom.ext fun a => ?_
    rw [RingHom.comp_apply, hFr, ← map_pow, Nat.card_eq_fintype_card, FiniteField.pow_card]
  have hFix : ∀ y : ModGL τ K,
      Units.map (entrywiseHom Fr) (baseChangeGL (algebraMap K (AlgebraicClosure K)) y) =
        baseChangeGL (algebraMap K (AlgebraicClosure K)) y := fun y => by
    rw [units_map_entrywiseHom_eq_baseChangeGL, baseChangeGL_baseChangeGL, hcomp]
  refine ⟨⟨1, Fr, hFr, 1, one_mem _, ?_, c, ?_⟩, rfl⟩
  · rw [map_one, canonicalRep_one, one_mul]
  · intro x hx
    refine Subgroup.mem_map.2 ⟨baseChangeGL (algebraMap K (AlgebraicClosure K))
      ((c * x * c⁻¹ : adjointGroup τ K) : ModGL τ K), ?_, ?_⟩
    · rw [mem_twistedTorusOf, canonicalRep_one, one_mul, inv_one, mul_one, hFix]
      exact ⟨CFSG.RankThree.Classical2.baseChangeGL_mem_torusGroup _ (hc x hx), rfl⟩
    · rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, one_mul, inv_one, mul_one]

end Datum

section Lattice

theorem frameSum_check : ∀ a ∈ f4LongList, ∀ b ∈ f4LongList, a - b ∈ f4LongList →
    ∀ c ∈ f4ShortList, ∀ d ∈ f4ShortList, c - d ∈ f4ShortList →
      (∀ i, (c + d - (a + b)) i % 3 = 0) ∨ (∀ i, (c + d + (a + b)) i % 3 = 0) := by
  decide +kernel

theorem exists_frameSum_rel {σA σB : Fin 3 → Fin 3 → Fin Tag.F4.rank → ℤ}
    (hnA : ∀ i j, σA j i = -σA i j) (haA : ∀ i j k, σA i j + σA j k = σA i k)
    (hnB : ∀ i j, σB j i = -σB i j) (haB : ∀ i j k, σB i j + σB j k = σB i k)
    (hSA : {r | ∃ i j : Fin 3, i ≠ j ∧ r = σA i j} = S1set)
    (hSB : {r | ∃ i j : Fin 3, i ≠ j ∧ r = σB i j} = S2set) :
    ∃ n : ℤ, ∃ w : Fin Tag.F4.rank → ℤ, ∑ j, σB j 0 + n • ∑ j, σA j 0 = (3 : ℤ) • w := by
  have hmA : ∀ i j : Fin 3, i ≠ j → σA i j ∈ f4LongList := fun i j hij => by
    have h : σA i j ∈ {r | ∃ i j : Fin 3, i ≠ j ∧ r = σA i j} := ⟨i, j, hij, rfl⟩
    rw [hSA] at h
    exact h
  have hmB : ∀ i j : Fin 3, i ≠ j → σB i j ∈ f4ShortList := fun i j hij => by
    have h : σB i j ∈ {r | ∃ i j : Fin 3, i ≠ j ∧ r = σB i j} := ⟨i, j, hij, rfl⟩
    rw [hSB] at h
    exact h
  have hsum : ∀ σ : Fin 3 → Fin 3 → Fin Tag.F4.rank → ℤ, (∀ i j, σ j i = -σ i j) →
      ∑ j, σ j 0 = σ 1 0 + σ 2 0 := by
    intro σ hn
    have h0 : σ 0 0 = 0 := by
      funext l
      have := congrFun (hn 0 0) l
      simp only [Pi.neg_apply] at this
      simp only [Pi.zero_apply]
      omega
    rw [Fin.sum_univ_three, h0, zero_add]
  have hsub : ∀ σ : Fin 3 → Fin 3 → Fin Tag.F4.rank → ℤ, (∀ i j k, σ i j + σ j k = σ i k) →
      σ 1 0 - σ 2 0 = σ 1 2 := by
    intro σ ha
    rw [← ha 1 2 0]
    abel
  have h := frameSum_check _ (hmA 1 0 (by decide)) _ (hmA 2 0 (by decide))
    (by rw [hsub σA haA]; exact hmA 1 2 (by decide)) _ (hmB 1 0 (by decide)) _
    (hmB 2 0 (by decide)) (by rw [hsub σB haB]; exact hmB 1 2 (by decide))
  rw [hsum σA hnA, hsum σB hnB]
  rcases h with h | h
  · refine ⟨-1, fun l => (σB 1 0 + σB 2 0 - (σA 1 0 + σA 2 0)) l / 3, ?_⟩
    funext l
    have := h l
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at this ⊢
    omega
  · refine ⟨1, fun l => (σB 1 0 + σB 2 0 + (σA 1 0 + σA 2 0)) l / 3, ?_⟩
    funext l
    have := h l
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at this ⊢
    omega

end Lattice

section Core


variable {K : Type} [Field K]

private theorem rootCharKernel_mulSingle_one' {ω : Kˣ} (hω : orderOf ω = 3) :
    rootCharKernel (Pi.mulSingle (1 : Fin Tag.F4.rank) ω) = cosetRoots Tag.F4 1 3 := by
  have hchar : ∀ α : Fin Tag.F4.rank → ℤ,
      rootChar (Pi.mulSingle (1 : Fin Tag.F4.rank) ω) α = ω ^ (α 1) := by
    intro α
    unfold rootChar
    rw [Finset.prod_eq_single (1 : Fin Tag.F4.rank)]
    · simp
    · intro j _ hj
      simp [Pi.mulSingle_eq_of_ne hj]
    · intro h
      exact absurd (Finset.mem_univ _) h
  ext α
  simp only [rootCharKernel, cosetRoots, Set.mem_setOf_eq, hchar]
  rw [← orderOf_dvd_iff_zpow_eq_one, hω]

private theorem toralRootGroup_mulSingle_one' {ω : Kˣ} (hω : orderOf ω = 3) :
    toralRootGroup Tag.F4 K (Pi.mulSingle (1 : Fin Tag.F4.rank) ω) =
      torusGroup Tag.F4 K ⊔ XS K := by
  rw [toralRootGroup, rootCharKernel_mulSingle_one' hω]

private theorem xs_le_centralizer_zSplit' {ω : Kˣ} (hω : orderOf ω = 3) :
    XS K ≤ Subgroup.centralizer
      ({rootDiagUnit Tag.F4 (Pi.mulSingle (1 : Fin Tag.F4.rank) ω)} : Set (ModGL Tag.F4 K)) := by
  refine ExcHighThree.rootSpan_le_centralizer_rootDiagUnit _ fun α hα => ?_
  rw [← rootCharKernel_mulSingle_one' hω] at hα
  exact hα

theorem exists_conj_torus_of_zSplit_mem [Finite K] (hK : Nat.card K % 3 = 1) {ω : Kˣ}
    (hω : orderOf ω = 3) {E : Subgroup (adjointGroup Tag.F4 K)} (hE : IsElemAbelian 3 E)
    (hc : Nat.card E = 3 ^ 3) (hz : zSplit K ω ∈ E) :
    ∃ x ∈ E, x ∉ Subgroup.zpowers (zSplit K ω) ∧ ∃ k : adjointGroup Tag.F4 K,
      k * zSplit K ω * k⁻¹ = zSplit K ω ∧
        ((k * x * k⁻¹ : adjointGroup Tag.F4 K) : ModGL Tag.F4 K) ∈ torusGroup Tag.F4 K := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Finite E := Nat.finite_of_card_ne_zero (by rw [hc]; norm_num)
  obtain ⟨ψA, ψB, σA, σB, hA, hB, hcomm, hSA, hSB⟩ := exists_splitFrame_F4' K
  have hrA : ψA.range = X1 K := by rw [hA.range, hSA]
  have hrB : ψB.range = X2 K := by rw [hB.range, hSB]
  have hMeq := toralRootGroup_mulSingle_one' (K := K) hω
  have h3a : ∀ i, (Pi.mulSingle (1 : Fin Tag.F4.rank) ω : Fin Tag.F4.rank → Kˣ) i ^ 3 = 1 := by
    intro i
    by_cases hi : i = 1
    · subst hi
      rw [Pi.mulSingle_eq_same, ← hω]
      exact pow_orderOf_eq_one ω
    · rw [Pi.mulSingle_eq_of_ne hi, one_pow]
  have hTC := CFSG.HardMathSupport.Timmesfeld.Steinberg.toralCentralizer_eq_toralRootGroup_F4_three
    K _ h3a
  have hcent : ∀ x ∈ E, (x : ModGL Tag.F4 K) ∈ torusGroup Tag.F4 K ⊔ XS K := by
    intro x hx
    rw [← hMeq, ← hTC, mem_toralCentralizer]
    refine ⟨x.2, ?_⟩
    have hzx : zSplit K ω * x = x * zSplit K ω :=
      congrArg Subtype.val (hE.1.is_comm.comm (⟨zSplit K ω, hz⟩ : E) ⟨x, hx⟩)
    have hzx' := congrArg Subtype.val hzx
    simp only [Subgroup.coe_mul] at hzx'
    change rootDiagUnit Tag.F4 (Pi.mulSingle (1 : Fin Tag.F4.rank) ω) * (x : ModGL Tag.F4 K) *
      (rootDiagUnit Tag.F4 (Pi.mulSingle (1 : Fin Tag.F4.rank) ω))⁻¹ = x
    exact mul_inv_eq_of_eq_mul hzx'
  obtain ⟨n, w, hnw⟩ := exists_frameSum_rel hA.neg hA.add hB.neg hB.add hSA hSB
  obtain ⟨C, hC⟩ : ∃ C : Subgroup Kˣ, ∀ v : Kˣ, v ∈ C ↔ ∃ u : Kˣ, u ^ 3 = v :=
    ⟨(powMonoidHom 3 : Kˣ →* Kˣ).range, fun v => Iff.rfl⟩
  obtain ⟨Q, hQ⟩ : ∃ Q : Subgroup (Kˣ × Kˣ), ∀ a b : Kˣ, (a, b) ∈ Q ↔ b * a ^ n ∈ C :=
    ⟨C.comap (MonoidHom.snd Kˣ Kˣ * (zpowGroupHom n).comp (MonoidHom.fst Kˣ Kˣ)),
      fun a b => Iff.rfl⟩
  have hMR : torusGroup Tag.F4 K ⊔ XS K ≤ frameDetSub ψA ψB Q := by
    rw [XS_eq, ← hrA, ← hrB]
    refine sup_le (fun t ht => ?_) (sup_le ?_ ?_)
    · obtain ⟨β, rfl⟩ :=
        CFSG.LieType.SeitzGeneration.ExcHighThree.exists_rootDiagUnit_of_mem_torusGroup ht
      refine mem_frameDetSub.2 ⟨_, _, rootDiagUnit_mem_frameActPairs hA β,
        rootDiagUnit_mem_frameActPairs hB β, ?_⟩
      have e : ∀ σ : Fin 3 → Fin 3 → Fin Tag.F4.rank → ℤ,
          GeneralLinearGroup.det (diagGL3 fun j => rootChar β (σ j 0)) =
            rootChar β (∑ j, σ j 0) := fun σ => by
        rw [det_diagGL3_eq_prod, rootChar_sum]
      rw [hQ, e σA, e σB, ← rootChar_zsmul, ← rootChar_add, hnw, rootChar_zsmul]
      exact (hC _).2 ⟨rootChar β w, (zpow_ofNat _ 3).symm⟩
    · rintro _ ⟨a, rfl⟩
      refine mem_frameDetSub.2 ⟨_, 1, toGL_mem_frameActPairs ψA a,
        one_mem_frameActPairs_of_commute fun s => hcomm a s, ?_⟩
      rw [SpecialLinearGroup.coeToGL_det, map_one]
      exact one_mem Q
    · rintro _ ⟨b, rfl⟩
      refine mem_frameDetSub.2 ⟨1, _, one_mem_frameActPairs_of_commute fun s => (hcomm s b).symm,
        toGL_mem_frameActPairs ψB b, ?_⟩
      rw [SpecialLinearGroup.coeToGL_det, map_one]
      exact one_mem Q
  obtain ⟨S, hS⟩ : ∃ S : Subgroup (ModGL Tag.F4 K), ∀ m, m ∈ S ↔ ∃ γA γB : GL (Fin 3) K,
      (m, γA) ∈ frameActPairs ψA ∧ (m, γB) ∈ frameActPairs ψB ∧
        GeneralLinearGroup.det γA ∈ C ∧ GeneralLinearGroup.det γB ∈ C :=
    ⟨frameDetSub ψA ψB (C.prod C), fun m => by
      rw [mem_frameDetSub]
      simp only [Subgroup.mem_prod]⟩
  obtain ⟨S', hS'⟩ : ∃ S' : Subgroup (adjointGroup Tag.F4 K),
      ∀ m, m ∈ S' ↔ (m : ModGL Tag.F4 K) ∈ S :=
    ⟨S.comap (adjointGroup Tag.F4 K).subtype, fun m => Iff.rfl⟩
  have hcard : 9 ≤ Nat.card ↥(E ⊓ S') := by
    by_cases hall : E ≤ S'
    · rw [inf_of_le_left hall, hc]
      norm_num
    obtain ⟨u, huE, huS⟩ := SetLike.not_le_iff_exists.1 hall
    obtain ⟨γA, γB, hγA, hγB, hγQ⟩ := mem_frameDetSub.1 (hMR (hcent u huE))
    have hγQ' := (hQ _ _).1 hγQ
    have hnc : ¬ ∃ v : Kˣ, v ^ 3 = GeneralLinearGroup.det γA := by
      intro hv
      have hvC : GeneralLinearGroup.det γA ∈ C := (hC _).2 hv
      exact huS ((hS' u).2 ((hS _).2 ⟨γA, γB, hγA, hγB, hvC,
        (Subgroup.mul_mem_cancel_right C (zpow_mem hvC n)).1 hγQ'⟩))
    have h := card_le_three_mul_inf_of_mul_pow_mem (S := S') huE (hE.2 u huE) fun y hy => by
      obtain ⟨γA', γB', hγA', hγB', hγQy⟩ := mem_frameDetSub.1 (hMR (hcent y hy))
      obtain ⟨k, v, hv⟩ :=
        SeitzOuterCube.Exc.TOdd.exists_cube_mul_pow (v := GeneralLinearGroup.det γA') hnc
      have hQk := mul_mem hγQy (pow_mem hγQ k)
      rw [Prod.pow_mk, Prod.mk_mul_mk, hQ] at hQk
      have hAC : GeneralLinearGroup.det γA' * GeneralLinearGroup.det γA ^ k ∈ C :=
        (hC _).2 ⟨v, hv⟩
      refine ⟨k, (hS' _).2 ?_⟩
      rw [Subgroup.coe_mul, Subgroup.coe_pow]
      refine (hS _).2 ⟨γA' * γA ^ k, γB' * γB ^ k, mul_pow_mem_frameActPairs hγA' hγA k,
        mul_pow_mem_frameActPairs hγB' hγB k, ?_, ?_⟩
      · rw [map_mul, map_pow]
        exact hAC
      · rw [map_mul, map_pow]
        exact (Subgroup.mul_mem_cancel_right C (zpow_mem hAC n)).1 hQk
    have h27 : (3 : ℕ) ^ 3 = 27 := by norm_num
    rw [hc, h27] at h
    omega
  have hz3 : zSplit K ω ^ 3 = 1 := hE.2 _ hz
  have hzo : orderOf (zSplit K ω) ∣ 3 := orderOf_dvd_of_pow_eq_one hz3
  haveI : Finite (Subgroup.zpowers (zSplit K ω)) := Nat.finite_of_card_ne_zero (by
    rw [Nat.card_zpowers]
    exact (Nat.pos_of_dvd_of_pos hzo (by norm_num)).ne')
  have hzc : Nat.card (Subgroup.zpowers (zSplit K ω)) ≤ 3 := by
    rw [Nat.card_zpowers]
    exact Nat.le_of_dvd (by norm_num) hzo
  have hnle : ¬ E ⊓ S' ≤ Subgroup.zpowers (zSplit K ω) := fun hle => by
    have h93 : 9 ≤ 3 := hcard.trans ((Subgroup.card_le_of_le hle).trans hzc)
    omega
  obtain ⟨x, hxES, hxz⟩ := SetLike.not_le_iff_exists.1 hnle
  obtain ⟨hxE, hxS⟩ := Subgroup.mem_inf.1 hxES
  obtain ⟨γA, γB, hγA, hγB, hdA, hdB⟩ := (hS _).1 ((hS' x).1 hxS)
  obtain ⟨μA, hμA⟩ := (hC _).1 hdA
  obtain ⟨μB, hμB⟩ := (hC _).1 hdB
  obtain ⟨ω', hω'⟩ := E6Three.exists_isPrimitiveRoot_three (K := K) (by omega)
  have hx3 : (x : ModGL Tag.F4 K) ^ 3 = 1 := by
    rw [← Subgroup.coe_pow, hE.2 x hxE, Subgroup.coe_one]
  obtain ⟨MA, hMA⟩ := exists_toGL_eq_mul_scalar (γ := γA) hμA
  obtain ⟨MB, hMB⟩ := exists_toGL_eq_mul_scalar (γ := γB) hμB
  have hxA : ((x : ModGL Tag.F4 K), SpecialLinearGroup.toGL MA) ∈ frameActPairs ψA := by
    rw [hMA]
    have := mul_mem hγA (scalar_mem_frameActPairs ψA μA⁻¹)
    rwa [Prod.mk_mul_mk, mul_one] at this
  have hxB : ((x : ModGL Tag.F4 K), SpecialLinearGroup.toGL MB) ∈ frameActPairs ψB := by
    rw [hMB]
    have := mul_mem hγB (scalar_mem_frameActPairs ψB μB⁻¹)
    rwa [Prod.mk_mul_mk, mul_one] at this
  obtain ⟨ζA, hζA⟩ := exists_pow_three_eq_smul_of_mem_frameActPairs hA.injective hxA hx3
  obtain ⟨ζB, hζB⟩ := exists_pow_three_eq_smul_of_mem_frameActPairs hB.injective hxB hx3
  rw [SpecialLinearGroup.coe_GL_coe_matrix] at hζA hζB
  obtain ⟨PA, hPA⟩ := exists_conj_diag_of_pow_three_eq_smul hω' MA hζA
  obtain ⟨PB, hPB⟩ := exists_conj_diag_of_pow_three_eq_smul hω' MB hζB
  have hXSadj : XS K ≤ adjointGroup Tag.F4 K := rootSpan_le_adjointGroup K _
  have hkXS : ψA PA * ψB PB ∈ XS K := by
    refine mul_mem (X1_le_XS K ?_) (X2_le_XS K ?_)
    · rw [← hrA]
      exact ⟨PA, rfl⟩
    · rw [← hrB]
      exact ⟨PB, rfl⟩
  obtain ⟨k, hk⟩ : ∃ k : adjointGroup Tag.F4 K, (k : ModGL Tag.F4 K) = ψA PA * ψB PB :=
    ⟨⟨_, hXSadj hkXS⟩, rfl⟩
  have hkA : ((k : ModGL Tag.F4 K), SpecialLinearGroup.toGL PA) ∈ frameActPairs ψA := by
    have h1 := mul_mem (toGL_mem_frameActPairs ψA PA)
      (one_mem_frameActPairs_of_commute fun s => (hcomm s PB).symm :
        (ψB PB, (1 : GL (Fin 3) K)) ∈ frameActPairs ψA)
    rw [Prod.mk_mul_mk, mul_one] at h1
    rw [hk]
    exact h1
  have hkB : ((k : ModGL Tag.F4 K), SpecialLinearGroup.toGL PB) ∈ frameActPairs ψB := by
    have h1 := mul_mem (one_mem_frameActPairs_of_commute fun s => hcomm PA s :
        (ψA PA, (1 : GL (Fin 3) K)) ∈ frameActPairs ψB) (toGL_mem_frameActPairs ψB PB)
    rw [Prod.mk_mul_mk, one_mul] at h1
    rw [hk]
    exact h1
  obtain ⟨y, hy⟩ : ∃ y : ModGL Tag.F4 K,
      y = (k : ModGL Tag.F4 K) * x * (k : ModGL Tag.F4 K)⁻¹ := ⟨_, rfl⟩
  have hyA : (y, SpecialLinearGroup.toGL (PA * MA * PA⁻¹)) ∈ frameActPairs ψA := by
    rw [hy, map_mul, map_mul, map_inv]
    exact conj_mem_frameActPairs hkA hxA
  have hyB : (y, SpecialLinearGroup.toGL (PB * MB * PB⁻¹)) ∈ frameActPairs ψB := by
    rw [hy, map_mul, map_mul, map_inv]
    exact conj_mem_frameActPairs hkB hxB
  have hkM : (k : ModGL Tag.F4 K) ∈ torusGroup Tag.F4 K ⊔ XS K := by
    rw [hk]
    exact Subgroup.mem_sup_right hkXS
  have hyM : y ∈ XS K ⊔ torusGroup Tag.F4 K := by
    rw [sup_comm, hy]
    exact mul_mem (mul_mem hkM (hcent x hxE)) (inv_mem hkM)
  have hTN : torusGroup Tag.F4 K ≤ Subgroup.normalizer (XS K : Set (ModGL Tag.F4 K)) :=
    CFSG.RankThree.PartOne.KE.torusGroup_le_normalizer_rootSpan fun α hα => hα.1
  have hX2N : X2 K ≤ Subgroup.normalizer (X1 K : Set (ModGL Tag.F4 K)) := fun b hb =>
    Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.2 fun a ha =>
      X1_X2_commute K a ha b hb)
  obtain ⟨s, hs, t, ht, hst⟩ := exists_mul_of_mem_sup_of_le_normalizer hTN hyM
  rw [XS_eq] at hs
  obtain ⟨a', ha', b', hb', hab⟩ := exists_mul_of_mem_sup_of_le_normalizer hX2N hs
  rw [← hrA] at ha'
  rw [← hrB] at hb'
  obtain ⟨a, rfl⟩ := ha'
  obtain ⟨b, rfl⟩ := hb'
  obtain ⟨β, rfl⟩ :=
    CFSG.LieType.SeitzGeneration.ExcHighThree.exists_rootDiagUnit_of_mem_torusGroup ht
  subst hab
  have hdA : (y, SpecialLinearGroup.toGL a * diagGL3 fun j => rootChar β (σA j 0)) ∈
      frameActPairs ψA := by
    have h1 := mul_mem (toGL_mem_frameActPairs ψA a)
      (one_mem_frameActPairs_of_commute fun s => (hcomm s b).symm :
        (ψB b, (1 : GL (Fin 3) K)) ∈ frameActPairs ψA)
    rw [Prod.mk_mul_mk, mul_one] at h1
    have h2 := mul_mem h1 (rootDiagUnit_mem_frameActPairs hA β)
    rw [Prod.mk_mul_mk] at h2
    rw [hst]
    exact h2
  have hdB : (y, SpecialLinearGroup.toGL b * diagGL3 fun j => rootChar β (σB j 0)) ∈
      frameActPairs ψB := by
    have h1 := mul_mem (one_mem_frameActPairs_of_commute fun s => hcomm a s :
        (ψA a, (1 : GL (Fin 3) K)) ∈ frameActPairs ψB) (toGL_mem_frameActPairs ψB b)
    rw [Prod.mk_mul_mk, one_mul] at h1
    have h2 := mul_mem h1 (rootDiagUnit_mem_frameActPairs hB β)
    rw [Prod.mk_mul_mk] at h2
    rw [hst]
    exact h2
  obtain ⟨cA, hcA⟩ := exists_smul_of_mem_frameActPairs hA.injective hyA hdA
  obtain ⟨cB, hcB⟩ := exists_smul_of_mem_frameActPairs hB.injective hyB hdB
  have hψa : ψA a ∈ torusGroup Tag.F4 K := hA.diag a (offDiag_eq_zero_of_mul_diagGL3
    (fun i j hij => by rw [SpecialLinearGroup.coe_GL_coe_matrix]; exact hPA i j hij) hcA)
  have hψb : ψB b ∈ torusGroup Tag.F4 K := hB.diag b (offDiag_eq_zero_of_mul_diagGL3
    (fun i j hij => by rw [SpecialLinearGroup.coe_GL_coe_matrix]; exact hPB i j hij) hcB)
  refine ⟨x, hxE, hxz, k, ?_, ?_⟩
  · apply Subtype.ext
    have hkz := Subgroup.mem_centralizer_singleton_iff.1 (xs_le_centralizer_zSplit' hω hkXS)
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, hk]
    exact mul_inv_eq_of_eq_mul hkz
  · rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, ← hy, hst]
    exact mul_mem (mul_mem hψa hψb) (CFSG.RankThree.Chevalley.F4_rootDiagUnit_mem_torusGroup β)

end Core

section Main


theorem f4NonToralSplitHyperplane_holds : F4NonToralSplitHyperplane := by
  intro K _ _ hK hs E₀ hE₀ hc hN hD
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨ω, hω⟩ : ∃ ω : Kˣ, orderOf ω = 3 := by
    have h3' : 3 ∣ Nat.card Kˣ := by rw [Nat.card_units]; omega
    exact exists_prime_orderOf_dvd_card' 3 h3'
  obtain ⟨P, hPE, hPc, D, hreg⟩ := f4NonToralRegularPlane_of_killedPlaneWeyl
    f4ThreeKilledPlaneWeyl_holds K (by omega) hs E₀ hE₀ hc hN hD
  have hPexp : ∀ x ∈ P, x ^ 3 = 1 := fun x hx => hE₀.2 x (hPE hx)
  obtain ⟨e, heP, he1⟩ : ∃ e ∈ P, e ≠ 1 := by
    by_contra h
    have hbot : P = ⊥ := (Subgroup.eq_bot_iff_forall P).2 fun x hx => by
      by_contra hx1
      exact h ⟨x, hx, hx1⟩
    rw [hbot, Subgroup.card_bot] at hPc
    norm_num at hPc
  obtain ⟨g, hg⟩ := f4PureSplit_holds K hK ω hω P hPexp hPc D hreg e heP he1
  have hE₁ : IsElemAbelian 3 (E₀.map (MulAut.conj g).toMonoidHom) := hE₀.map _
  have hc₁ : Nat.card (E₀.map (MulAut.conj g).toMonoidHom) = 3 ^ 3 := by
    rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, hc]
  have hz : zSplit K ω ∈ E₀.map (MulAut.conj g).toMonoidHom :=
    Subgroup.mem_map.2 ⟨e, hPE heP, by rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, hg]⟩
  obtain ⟨x, hxE, hxz, k, hkz, hkx⟩ := exists_conj_torus_of_zSplit_mem hK hω hE₁ hc₁ hz
  obtain ⟨x₀, hx₀, rfl⟩ := Subgroup.mem_map.1 hxE
  have hx₀e : x₀ ∉ Subgroup.zpowers e := by
    intro hmem
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.1 hmem
    apply hxz
    refine Subgroup.mem_zpowers_iff.2 ⟨m, ?_⟩
    rw [← hm, map_zpow, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, hg]
  refine ⟨Subgroup.closure {e, x₀}, (Subgroup.closure_le E₀).2
    (Set.insert_subset_iff.2 ⟨hPE heP, Set.singleton_subset_iff.2 hx₀⟩),
    relIndex_closure_pair_of_not_mem Nat.prime_three hE₀ hc (hPE heP) hx₀ he1 hx₀e, ?_⟩
  refine exists_langPlaneData_w_one (k * g) fun f hf => ?_
  have hle : Subgroup.closure ({e, x₀} : Set (adjointGroup .F4 K)) ≤
      (torusGroup .F4 K).comap ((adjointGroup .F4 K).subtype.comp
        (MulAut.conj (k * g)).toMonoidHom) := by
    refine (Subgroup.closure_le _).2 (Set.insert_subset_iff.2 ⟨?_, Set.singleton_subset_iff.2 ?_⟩)
    · show (((k * g) * e * (k * g)⁻¹ : adjointGroup .F4 K) : ModGL .F4 K) ∈ torusGroup .F4 K
      rw [show (k * g) * e * (k * g)⁻¹ = k * (g * e * g⁻¹) * k⁻¹ by group, hg, hkz]
      exact CFSG.RankThree.Chevalley.F4_rootDiagUnit_mem_torusGroup
        (Pi.mulSingle (1 : Fin Tag.F4.rank) ω)
    · show (((k * g) * x₀ * (k * g)⁻¹ : adjointGroup .F4 K) : ModGL .F4 K) ∈ torusGroup .F4 K
      rw [show (k * g) * x₀ * (k * g)⁻¹ = k * (g * x₀ * g⁻¹) * k⁻¹ by group]
      exact hkx
  exact hle hf

end Main

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeF4Close

end
