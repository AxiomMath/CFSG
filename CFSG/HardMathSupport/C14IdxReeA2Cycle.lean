module

public import CFSG.HardMathSupport.C14IdxReeTwistSq
public import CFSG.RankThree.PartOne.TCX.Ree.Perm
public import CFSG.HardMathSupport.C14IdxA2Cycle

public section

namespace CFSG.HardMathSupport.C14Idx

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.LieType.AlgebraicGroups CFSG.RankThree.PartOne.RF4 CFSG.RankThree.PartOne.KLR
  CFSG.RankThree.PartOne.TCX.Ree CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.Torality CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial CFSG.SeitzReduction
open CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three.KSGen (coordTuple)


private theorem twistMap_mem_rootSpan {L : Type}
    [Field L] [CharP L 2] {a₀ : ℕ} {F : MulAut (adjointGroup ReeTag.F4.tag L)}
    (hF : IsReeFrob a₀ F) {w : WeylGroup ReeTag.F4.tag}
    {θ : (Fin ReeTag.F4.tag.rank → ℤ) → Fin ReeTag.F4.tag.rank → ℤ}
    (hθ : ∀ β, θ β = w • ReeTag.F4.dualRoot β)
    {R₀ : Set (Fin ReeTag.F4.tag.rank → ℤ)} (hR₀root : ∀ γ ∈ R₀, IsRoot ReeTag.F4.tag γ)
    {x : ModGL ReeTag.F4.tag L} (hx : x ∈ rootSpan ReeTag.F4.tag L R₀) :
    twistMap F (canonicalRep (coxeterSystem ReeTag.F4.tag) L w) x ∈
      rootSpan ReeTag.F4.tag L (Set.image θ R₀) := by
  have hxadj : x ∈ adjointGroup ReeTag.F4.tag L :=
    CFSG.LieType.Chevalley.rootSpan_le_adjointGroup L R₀ hx
  have h1 : Fext F x ∈ rootSpan ReeTag.F4.tag L (Set.image ReeTag.F4.dualRoot R₀) := by
    rw [Fext_of_mem F hxadj]
    exact hF.mem_rootSpan hR₀root (g := ⟨x, hxadj⟩) hx
  have h2 := CFSG.HardMathSupport.Lang.TwE6Step3.canonicalRep_conj_mem_rootSpan
    (τ := ReeTag.F4.tag) w (S := Set.image ReeTag.F4.dualRoot R₀)
    (S' := Set.image θ R₀) (fun γ hγ => by
      obtain ⟨δ, hδ, rfl⟩ := hγ
      exact ⟨ReeTag.isRoot_dualRoot (hR₀root δ hδ), ⟨δ, hδ, hθ δ⟩⟩) h1
  simpa [twistMap] using h2

private theorem twistMap_pow {L : Type} [Field L]
    {F : MulAut (adjointGroup ReeTag.F4.tag L)} (n : ModGL ReeTag.F4.tag L)
    {x : ModGL ReeTag.F4.tag L} (hx : x ∈ adjointGroup ReeTag.F4.tag L) (k : ℕ) :
    twistMap F n (x ^ k) = (twistMap F n x) ^ k := by
  induction k with
  | zero => rw [pow_zero, pow_zero, twistMap_one]
  | succ k ih =>
    rw [pow_succ, pow_succ, twistMap_mul n (pow_mem hx k) hx, ih]

private theorem norm_mem_closure_of_mul {G : Type*} [Group G] {H T : Subgroup G}
    {s : Set G} {N : G → G} (hs : s ⊆ H) (hN1 : N 1 = 1)
    (hNmul : ∀ x ∈ H, ∀ y ∈ H, N (x * y) = N x * N y)
    (hNs : ∀ x ∈ s, N x ∈ T) {x : G} (hx : x ∈ Subgroup.closure s) : N x ∈ T := by
  have hH : Subgroup.closure s ≤ H := (Subgroup.closure_le (K := H)).2 hs
  refine Subgroup.closure_induction (p := fun x _ => N x ∈ T) ?_ ?_ ?_ ?_ hx
  · intro x hx
    exact hNs x hx
  · rw [hN1]
    exact T.one_mem
  · intro x y hx hy ihx ihy
    rw [hNmul x (hH hx) y (hH hy)]
    exact T.mul_mem ihx ihy
  · intro x hx ihx
    have hxH : x ∈ H := hH hx
    have h1 : N x⁻¹ * N x = 1 := by
      rw [← hNmul x⁻¹ (H.inv_mem hxH) x hxH, inv_mul_cancel, hN1]
    have h2 : N x⁻¹ = (N x)⁻¹ := eq_inv_of_mul_eq_one_left h1
    rw [h2]
    exact T.inv_mem ihx

theorem rootDiagUnit_coordTuple_mem_closure_of_reeA2Cycle
    {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] {a₀ : ℕ}
    {F : MulAut (adjointGroup ReeTag.F4.tag L)} (hF : IsReeFrob a₀ F)
    {w : WeylGroup ReeTag.F4.tag} {θ : (Fin ReeTag.F4.tag.rank → ℤ) → Fin ReeTag.F4.tag.rank → ℤ}
    (hθ : ∀ β, θ β = w • ReeTag.F4.dualRoot β) {α : Fin ReeTag.F4.tag.rank → ℤ}
    (hαβ : OddDerivPair ReeTag.F4.tag α (θ^[2] α)) (hθ4 : θ^[4] α = α)
    (hcomm : ∀ γ ∈ a2PairRoots α (θ^[2] α), ∀ δ ∈ a2PairRoots α (θ^[2] α), ∀ s t : L,
      Commute (pinnedX ReeTag.F4.tag L γ s) (pinnedX ReeTag.F4.tag L (θ δ) t))
    {O : Finset (Fin ReeTag.F4.tag.rank → ℤ)} (hO : O = (Finset.range 4).image fun i => θ^[i] α)
    (hOcard : O.card = 4) (c : (Fin ReeTag.F4.tag.rank → ℤ) → Lˣ)
    (hc : ∀ γ ∈ O, c (θ γ) = c γ ^ rootExp a₀ γ) :
    rootDiagUnit ReeTag.F4.tag (coordTuple O c) ∈ Subgroup.closure
      {y : ModGL ReeTag.F4.tag L | y ∈ rootSpan ReeTag.F4.tag L
          {γ | ∃ i < 2, ∃ δ ∈ a2PairRoots α (θ^[2] α), θ^[i] δ = γ} ∧
        y ∈ twistedFixed F (canonicalRep (coxeterSystem ReeTag.F4.tag) L w) ∧
          ∃ j : ℕ, y ^ 2 ^ j = 1} := by
  classical
  let β : Fin ReeTag.F4.tag.rank → ℤ := θ^[2] α
  let R₀ : Set (Fin ReeTag.F4.tag.rank → ℤ) := a2PairRoots α β
  let e : ℕ := 2 * a₀ + 1
  let u : WeylGroup ReeTag.F4.tag := w * ReeTag.F4.weylPerm w
  let n : ModGL ReeTag.F4.tag L := canonicalRep (coxeterSystem ReeTag.F4.tag) L w
  let Q : ModGL ReeTag.F4.tag L := canonicalRep (coxeterSystem ReeTag.F4.tag) L u
  let θ₂ : (Fin ReeTag.F4.tag.rank → ℤ) ≃+ (Fin ReeTag.F4.tag.rank → ℤ) :=
    DistribMulAction.toAddEquiv (Fin ReeTag.F4.tag.rank → ℤ) u
  let O₂ : Finset (Fin ReeTag.F4.tag.rank → ℤ) := {α, β}
  have n_mem : n ∈ adjointGroup ReeTag.F4.tag L := canonicalRep_mem_adjointGroup _ L w
  have hb : oddDerivPairB ReeTag.F4.tag α (θ^[2] α) = true := oddDerivPairB_iff.mpr hαβ
  simp only [oddDerivPairB, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at hb
  have hαroot : IsRoot ReeTag.F4.tag α := RootOps.isRootB_iff.mp hb.1.1.1.1.1.1.1
  have hβroot : IsRoot ReeTag.F4.tag β := RootOps.isRootB_iff.mp hb.1.1.1.1.1.1.2
  have hsum : IsRoot ReeTag.F4.tag (α + β) := RootOps.isRootB_iff.mp hb.1.1.1.2
  have hθroot : ∀ γ, IsRoot ReeTag.F4.tag γ → IsRoot ReeTag.F4.tag (θ γ) := by
    intro γ hγ
    rw [hθ γ]
    exact IsRoot.smul (ReeTag.isRoot_dualRoot hγ) w
  have hθθ : ∀ {γ : Fin ReeTag.F4.tag.rank → ℤ}, IsRoot ReeTag.F4.tag γ →
      θ (θ γ) = u • γ := by
    intro γ hγ
    rw [hθ (θ γ), hθ γ, ReeTag.dualRoot_smul w (ReeTag.isRoot_dualRoot hγ),
      ← mul_smul, ReeTag.dualRoot_dualRoot hγ]
  have hθ₂apply : ∀ v, θ₂ v = u • v := fun v =>
    DistribMulAction.toAddEquiv_apply (Fin ReeTag.F4.tag.rank → ℤ) u v
  have hθ₂α : θ₂ α = β := by rw [hθ₂apply]; exact (hθθ hαroot).symm
  have hθ₂β : θ₂ β = α := by
    rw [hθ₂apply, ← hθθ hβroot]
    change θ (θ (θ (θ α))) = α
    simpa [Function.iterate_succ_apply', Function.iterate_succ_apply] using hθ4
  have hθ₂sq : (θ₂)^[2] α = α := by
    rw [show (2 : ℕ) = 1 + 1 by norm_num, Function.iterate_add_apply,
      Function.iterate_one, hθ₂α, hθ₂β]
  have hO_mem : ∀ i, i < 4 → θ^[i] α ∈ O := by
    intro i hi
    rw [hO]
    exact Finset.mem_image.2 ⟨i, Finset.mem_range.2 hi, rfl⟩
  have hαO : α ∈ O := by simpa using hO_mem 0 (by norm_num)
  have hβO : β ∈ O := by simpa [β] using hO_mem 2 (by norm_num)
  have hinj : Set.InjOn (fun j : ℕ => θ^[j] α) (Finset.range 4) := by
    rw [← Finset.card_image_iff, ← hO, hOcard, Finset.card_range]
  have hαneβ : α ≠ β := by
    intro h
    have h0 : (0 : ℕ) ∈ Finset.range 4 := by norm_num
    have h2 : (2 : ℕ) ∈ Finset.range 4 := by norm_num
    have hz : θ^[0] α = θ^[2] α := by simpa [β] using h
    exact absurd (hinj h0 h2 hz) (by omega)
  have hOroot : ∀ γ ∈ O, IsRoot ReeTag.F4.tag γ := by
    intro γ hγ
    rw [hO] at hγ
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hγ
    have hi' : i < 4 := Finset.mem_range.1 hi
    interval_cases i
    · simpa using hαroot
    · simpa using hθroot α hαroot
    · simpa [β] using hβroot
    · simpa [β, Function.iterate_succ_apply'] using hθroot β hβroot
  have hθO : ∀ γ ∈ O, θ γ ∈ O := by
    intro γ hγ
    rw [hO] at hγ ⊢
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hγ
    have hi' : i < 4 := Finset.mem_range.1 hi
    by_cases h3 : i = 3
    · refine Finset.mem_image.2 ⟨0, by norm_num, ?_⟩
      rw [h3, ← Function.iterate_succ_apply' θ 3 α]
      simpa using hθ4.symm
    · refine Finset.mem_image.2 ⟨i + 1, Finset.mem_range.2 (by omega), ?_⟩
      rw [Function.iterate_succ_apply']
  have hrootExp_θ : ∀ {γ : Fin ReeTag.F4.tag.rank → ℤ}, IsRoot ReeTag.F4.tag γ →
      rootExp a₀ (θ γ) = rootExp a₀ (ReeTag.F4.dualRoot γ) := by
    intro γ hγ
    rw [hθ γ, CFSG.RankThree.PartOne.TCX.Ree.rootExp_smul]
  have hc_double : ∀ γ ∈ O, c (θ (θ γ)) = c γ ^ 2 ^ e := by
    intro γ hγ
    have hγroot : IsRoot ReeTag.F4.tag γ := hOroot γ hγ
    have hθγO : θ γ ∈ O := hθO γ hγ
    calc c (θ (θ γ)) = c (θ γ) ^ rootExp a₀ (θ γ) := hc _ hθγO
      _ = (c γ ^ rootExp a₀ γ) ^ rootExp a₀ (θ γ) := by rw [hc _ hγ]
      _ = c γ ^ (rootExp a₀ γ * rootExp a₀ (θ γ)) := by rw [← pow_mul]
      _ = c γ ^ 2 ^ e := by
        congr 1
        rw [hrootExp_θ hγroot, rootExp_mul_rootExp_dualRoot hγroot]
  have hO₂eq : O₂ = (Finset.range 2).image fun i => (θ₂)^[i] α := by
    ext γ
    simp only [O₂, Finset.mem_insert, Finset.mem_singleton, Finset.mem_image,
      Finset.mem_range]
    constructor
    · rintro (rfl | rfl)
      · exact ⟨0, by omega, by simp⟩
      · exact ⟨1, by omega, by simpa using hθ₂α⟩
    · rintro ⟨i, hi, rfl⟩
      interval_cases i
      · simp
      · rw [Function.iterate_one, hθ₂α]
        simp
  have hO₂card : O₂.card = 2 := Finset.card_pair hαneβ
  have hO₂sub : O₂ ⊆ O := by
    intro x hx
    simp only [O₂, Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with hx | hx
    · rw [hx]; exact hαO
    · rw [hx]; exact hβO
  have hc₂ : ∀ γ ∈ O₂, c (θ₂ γ) = c γ ^ 2 ^ e := by
    intro γ hγ
    have hγO : γ ∈ O := hO₂sub hγ
    have hγroot : IsRoot ReeTag.F4.tag γ := hOroot γ hγO
    have h : θ₂ γ = θ (θ γ) := (hθθ hγroot).symm
    rw [h]
    exact hc_double γ hγO
  have hA2₁ : rootDiagUnit ReeTag.F4.tag (coordTuple O₂ c) ∈ Subgroup.closure
      {x : ModGL ReeTag.F4.tag L |
        x ∈ rootSpan ReeTag.F4.tag L
          {γ | ∃ i < 1, ∃ δ ∈ a2PairRoots α ((⇑θ₂)^[1] α), (⇑θ₂)^[i] δ = γ} ∧
          frobTwistGL ReeTag.F4.tag L 2 e Q x = x ∧ ∃ j : ℕ, x ^ 2 ^ j = 1} := by
    exact rootDiagUnit_coordTuple_mem_closure_of_a2Cycle (e := e) (Q := Q) (θ := θ₂)
      (k := 1) (α := α) (O := O₂) (c := c) (he := by omega) (hk := by norm_num)
      (hθ := fun x y => by rw [hθ₂apply, hθ₂apply, iform_smul])
      (hθΦ := fun γ hγ => by rw [hθ₂apply]; exact IsRoot.smul hγ u)
      (hQX := fun γ hγ x => by
        show Q * pinnedX ReeTag.F4.tag L γ x * Q⁻¹ = pinnedX ReeTag.F4.tag L (θ₂ γ) x
        rw [hθ₂apply]
        exact canonicalRep_conj_pinnedX u hγ x)
      (hQT := fun t => ⟨weylTuple u t, canonicalRep_conj_rootDiagUnit u t⟩)
      (hαβ := by simpa only [Function.iterate_one, hθ₂α] using hαβ)
      (hθk := by simpa using hθ₂sq)
      (hcomm := fun i hi => by omega)
      (hO := by simpa using hO₂eq)
      (hOcard := by simpa using hO₂card)
      (hc := hc₂)
  have hA2 : rootDiagUnit ReeTag.F4.tag (coordTuple O₂ c) ∈ Subgroup.closure
      {x : ModGL ReeTag.F4.tag L | x ∈ rootSpan ReeTag.F4.tag L R₀ ∧
        frobTwistGL ReeTag.F4.tag L 2 e Q x = x ∧ ∃ j : ℕ, x ^ 2 ^ j = 1} := by
    refine Subgroup.closure_mono ?_ hA2₁
    rintro x ⟨hx, hfix, hj⟩
    refine ⟨?_, hfix, hj⟩
    refine rootSpan_mono ?_ hx
    rintro γ ⟨i, hi, δ, hδ, hθi⟩
    have hi0 : i = 0 := by omega
    subst i
    rw [Function.iterate_zero_apply] at hθi
    have hδ' : γ ∈ a2PairRoots α ((⇑θ₂)^[1] α) := by
      rwa [hθi] at hδ
    simpa [R₀, β, Function.iterate_one, hθ₂α] using hδ'
  set H : Subgroup (ModGL ReeTag.F4.tag L) := rootSpan ReeTag.F4.tag L R₀ with hH
  set K : Subgroup (ModGL ReeTag.F4.tag L) := rootSpan ReeTag.F4.tag L (Set.image θ R₀) with hK
  set T : Subgroup (ModGL ReeTag.F4.tag L) := Subgroup.closure
    {y : ModGL ReeTag.F4.tag L | y ∈ rootSpan ReeTag.F4.tag L
        {γ | ∃ i < 2, ∃ δ ∈ a2PairRoots α (θ^[2] α), θ^[i] δ = γ} ∧
      y ∈ twistedFixed F (canonicalRep (coxeterSystem ReeTag.F4.tag) L w) ∧
        ∃ j : ℕ, y ^ 2 ^ j = 1} with hT
  set S : Set (ModGL ReeTag.F4.tag L) :=
    {x | x ∈ H ∧ frobTwistGL ReeTag.F4.tag L 2 e Q x = x ∧ ∃ j : ℕ, x ^ 2 ^ j = 1} with hS
  have hR₀root : ∀ γ ∈ R₀, IsRoot ReeTag.F4.tag γ := by
    intro γ hγ
    change γ = α ∨ γ = β ∨ γ = α + β ∨ γ = -α ∨ γ = -β ∨ γ = -(α + β) at hγ
    rcases hγ with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hαroot
    · exact hβroot
    · exact hsum
    · exact IsRoot.neg hαroot
    · exact IsRoot.neg hβroot
    · exact IsRoot.neg hsum
  have hHadj : H ≤ adjointGroup ReeTag.F4.tag L := by
    rw [hH]
    exact CFSG.LieType.Chevalley.rootSpan_le_adjointGroup L R₀
  have hσ_mul : ∀ x ∈ H, ∀ y ∈ H,
      twistMap F n (x * y) = twistMap F n x * twistMap F n y :=
    fun x hx y hy => twistMap_mul n (hHadj hx) (hHadj hy)
  have hσ_image : ∀ x ∈ H, twistMap F n x ∈ K := by
    intro x hx
    have hx' : x ∈ rootSpan ReeTag.F4.tag L R₀ := by simpa [hH] using hx
    exact twistMap_mem_rootSpan hF hθ hR₀root hx'
  have hcomm_span : ∀ x ∈ H, ∀ y ∈ K, Commute x y := by
    intro x hx y hy
    refine CFSG.HardMathSupport.Lang.TwE6Step3.rootSpan_commute (A := R₀)
      (B := Set.image θ R₀) (K := L) ?_ hx hy
    intro γ hγ δ hδ x' hx' y' hy'
    obtain ⟨s, rfl⟩ := mem_rootSubgroup.1 hx'
    obtain ⟨t, hty⟩ := mem_rootSubgroup.1 hy'
    subst hty
    obtain ⟨δ₀, hδ₀, rfl⟩ := hδ
    exact hcomm γ hγ δ₀ hδ₀ s t
  have hN_mul : ∀ x ∈ H, ∀ y ∈ H,
      x * y * twistMap F n (x * y) = (x * twistMap F n x) * (y * twistMap F n y) := by
    intro x hx y hy
    rw [hσ_mul x hx y hy]
    have hcy := hcomm_span y hy (twistMap F n x) (hσ_image x hx)
    calc x * y * (twistMap F n x * twistMap F n y)
        = x * (y * twistMap F n x) * twistMap F n y := by group
      _ = x * (twistMap F n x * y) * twistMap F n y := by rw [hcy.eq]
      _ = (x * twistMap F n x) * (y * twistMap F n y) := by group
  have hN_fixed : ∀ x ∈ H, frobTwistGL ReeTag.F4.tag L 2 e Q x = x →
      twistMap F n (x * twistMap F n x) = x * twistMap F n x := by
    intro x hx hfix
    calc twistMap F n (x * twistMap F n x)
        = twistMap F n x * twistMap F n (twistMap F n x) :=
          twistMap_mul n (hHadj hx) (twistMap_mem_adjoint n_mem (hHadj hx))
      _ = twistMap F n x * frobTwistGL ReeTag.F4.tag L 2 e Q x := by
          rw [reeTwistMap_sq hF w (hHadj hx)]
      _ = twistMap F n x * x := by rw [hfix]
      _ = x * twistMap F n x := (hcomm_span x hx _ (hσ_image x hx)).eq.symm
  have hNs : ∀ x ∈ S, x * twistMap F n x ∈ T := by
    intro x hx
    rw [hS] at hx
    obtain ⟨hxH, hxfix, j, hxj⟩ := hx
    have hxadj : x ∈ adjointGroup ReeTag.F4.tag L := hHadj hxH
    have hσxK : twistMap F n x ∈ K := hσ_image x hxH
    have hsub : R₀ ∪ Set.image θ R₀ ⊆
        {γ | ∃ i < 2, ∃ δ ∈ a2PairRoots α (θ^[2] α), θ^[i] δ = γ} := by
      rintro γ (hγ | ⟨δ, hδ, rfl⟩)
      · exact ⟨0, by norm_num, γ, hγ, by simp⟩
      · exact ⟨1, by norm_num, δ, hδ, by simp⟩
    have hmem : x * twistMap F n x ∈ rootSpan ReeTag.F4.tag L
        {γ | ∃ i < 2, ∃ δ ∈ a2PairRoots α (θ^[2] α), θ^[i] δ = γ} :=
      rootSpan_mono hsub (Subgroup.mul_mem _
        (rootSpan_mono (fun γ hγ => Or.inl hγ) hxH)
        (rootSpan_mono (fun γ hγ => Or.inr hγ) hσxK))
    rw [hT]
    refine Subgroup.subset_closure ⟨hmem, ?_, ?_⟩
    · rw [mem_twistedFixed]
      exact ⟨mul_mem hxadj (twistMap_mem_adjoint n_mem hxadj),
        hN_fixed x hxH hxfix⟩
    · have hcomm_xσ : Commute x (twistMap F n x) := hcomm_span x hxH _ hσxK
      refine ⟨j, ?_⟩
      rw [hcomm_xσ.mul_pow, hxj]
      rw [show twistMap F n x ^ 2 ^ j = 1 by
        rw [← twistMap_pow n hxadj (2 ^ j), hxj, twistMap_one]]
      rw [one_mul]
  have hN_mem : (fun x => x * twistMap F n x) (rootDiagUnit ReeTag.F4.tag (coordTuple O₂ c)) ∈ T :=
    norm_mem_closure_of_mul (H := H) (T := T) (s := S)
      (fun x hx => by rw [hS] at hx; exact hx.1) (by rw [twistMap_one, mul_one])
      hN_mul hNs (by simpa [hH, hS] using hA2)
  have hO₂image : O₂.image θ = {θ α, θ β} := by
    rw [show O₂ = {α, β} from rfl, Finset.image_insert, Finset.image_singleton]
  have hθne : θ α ≠ θ β := by
    intro h
    apply hαneβ
    have h1 : w • ReeTag.F4.dualRoot α = w • ReeTag.F4.dualRoot β := by
      rw [← hθ α, ← hθ β]
      exact h
    have h3 := congrArg ReeTag.F4.dualRoot (MulAction.injective w h1)
    rwa [ReeTag.dualRoot_dualRoot hαroot, ReeTag.dualRoot_dualRoot hβroot] at h3
  let bα : Fin ReeTag.F4.tag.rank → Lˣ := fun i => c α ^ corootPair α (Pi.single i 1)
  let bβ : Fin ReeTag.F4.tag.rank → Lˣ := fun i => c β ^ corootPair β (Pi.single i 1)
  have hbαadj : rootDiagUnit ReeTag.F4.tag bα ∈ adjointGroup ReeTag.F4.tag L :=
    CFSG.LieType.AlgebraicGroups.torusGroup_le_adjointGroup
      (rootDiagUnit_mem_torusGroup bα)
  have hbβadj : rootDiagUnit ReeTag.F4.tag bβ ∈ adjointGroup ReeTag.F4.tag L :=
    CFSG.LieType.AlgebraicGroups.torusGroup_le_adjointGroup
      (rootDiagUnit_mem_torusGroup bβ)
  have hσd₂ : twistMap F n (rootDiagUnit ReeTag.F4.tag (coordTuple O₂ c)) =
      rootDiagUnit ReeTag.F4.tag (coordTuple (O₂.image θ) c) := by
    rw [show O₂ = {α, β} from rfl,
      CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three.KSGen.coordTuple_eq_prod,
      Finset.prod_pair hαneβ, rootDiagUnit_mul,
      twistMap_mul n hbαadj hbβadj,
      twistMap_rootDiagUnit_single hF hθ hαroot (c α),
      twistMap_rootDiagUnit_single hF hθ hβroot (c β),
      ← hc α hαO, ← hc β hβO, hO₂image,
      CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three.KSGen.coordTuple_eq_prod,
      Finset.prod_pair hθne, rootDiagUnit_mul]
  have hOunion : O = O₂ ∪ O₂.image θ := by
    rw [hO, hO₂image]
    ext x
    simp only [O₂, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton,
      Finset.mem_image, Finset.mem_range]
    constructor
    · rintro ⟨i, hi, rfl⟩
      interval_cases i <;> simp [β, Function.iterate_succ_apply']
    · rintro ((rfl | rfl) | rfl | rfl)
      · exact ⟨0, by norm_num, rfl⟩
      · exact ⟨2, by norm_num, by simp [β]⟩
      · exact ⟨1, by norm_num, rfl⟩
      · exact ⟨3, by norm_num, by simp [β, Function.iterate_succ_apply']⟩
  have hcardimg : (O₂.image θ).card = 2 := by
    rw [hO₂image]
    exact Finset.card_pair hθne
  have hdisj : Disjoint O₂ (O₂.image θ) := by
    rw [Finset.disjoint_iff_inter_eq_empty, ← Finset.card_eq_zero]
    have h := Finset.card_union_add_card_inter O₂ (O₂.image θ)
    rw [← hOunion, hOcard, hO₂card, hcardimg] at h
    omega
  have hcoordO : coordTuple O c = coordTuple O₂ c * coordTuple (O₂.image θ) c := by
    rw [hOunion]
    funext i
    simp only [CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three.KSGen.coordTuple,
      Pi.mul_apply, Finset.prod_union hdisj]
  have hfinal : rootDiagUnit ReeTag.F4.tag (coordTuple O₂ c) *
      twistMap F n (rootDiagUnit ReeTag.F4.tag (coordTuple O₂ c)) =
      rootDiagUnit ReeTag.F4.tag (coordTuple O c) := by
    rw [hσd₂, ← rootDiagUnit_mul, hcoordO]
  rw [← hfinal]
  exact hN_mem

end CFSG.HardMathSupport.C14Idx
