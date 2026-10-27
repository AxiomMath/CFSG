module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowX2E6TUnit
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwCompSU
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.SplitLineFix
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.Subnormal
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.AlgebraicZMod
public import CFSG.Monster.B.TwoA.Census.PermClasses

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie.X2E6.T

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
open CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
open CFSG.GF2Type.SmithTypeE CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.LieType.AlgebraicGroups CFSG.RankThree.PartOne.KE
open scoped MatrixGroups Matrix

section Algebra

theorem open_isQuasisimple_of_native {Q : Type*} [Group Q] (h : CFSG.IsQuasisimple Q) :
    CFSG.Open.IsQuasisimple Q :=
  ⟨h.1.commutator_eq_top, h.2.1⟩

theorem mem_centralizer_singleton_of_conj_eq {G : Type*} [Group G] {d x : G}
    (h : d * x * d⁻¹ = x) : x ∈ Subgroup.centralizer ({d} : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro g hg
  rw [Set.mem_singleton_iff] at hg
  subst hg
  calc g * x = (g * x * g⁻¹) * g := by group
    _ = x * g := by rw [h]

theorem conj_eq_of_mem_centralizer_singleton {G : Type*} [Group G] {d x : G}
    (h : x ∈ Subgroup.centralizer ({d} : Set G)) : d * x * d⁻¹ = x := by
  rw [Subgroup.mem_centralizer_iff] at h
  have := h d (Set.mem_singleton d)
  calc d * x * d⁻¹ = (d * x) * d⁻¹ := rfl
    _ = (x * d) * d⁻¹ := by rw [this]
    _ = x := by group

end Algebra

section Injective

variable
  {τ : Tag} {L : Type} [Field L] {ν : ℕ}
  {ρ : SL(ν, L) →* ModGL τ L} {σ : Fin ν → Fin ν → Fin τ.rank → ℤ}

theorem frame_injective_of_card_four [CharP L 2] (h : IsSLFrame ρ σ) (hν : ν = 4) :
    Function.Injective ρ := by
  classical
  subst hν
  rw [injective_iff_map_eq_one]
  intro X hX
  have hker : X ∈ ρ.ker := hX
  obtain ⟨s, hs4, hs⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1
    (CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three.KSGen.frame_ker_le_center
      (by norm_num) h hker)
  have hs4' : s ^ 4 = 1 := by simpa using hs4
  have h2 : (2 : L) = 0 := CharP.cast_eq_zero L 2
  have h5 : (s - 1) ^ 4 = 0 := by
    linear_combination hs4' + (-2 * s ^ 3 + 3 * s ^ 2 - 2 * s + 1) * h2
  have hs1 : s = 1 := sub_eq_zero.1 (pow_eq_zero_iff (by norm_num)|>.1 h5)
  subst hs1
  apply Subtype.ext
  rw [← hs]
  simp

end Injective

section Lang

variable
  {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ}
  (S : LangSetup τ L p₀) {ν : ℕ} {ψ : SL(ν, L) →* ModGL τ L}
  {σ : Fin ν → Fin ν → Fin τ.rank → ℤ}

theorem rationalRoots_eq_frameRoots (hρ : ∀ γ, IsRoot τ γ → S.ρ γ = -γ) {a : Fin τ.rank → Lˣ}
    (i : KernelComponent (rootCharHom a)) (h : IsSLFrame ψ σ)
    (hΨ : componentRoots (rootCharHom a) i = frameRoots σ) :
    rationalRoots S.ρ (rootCharHom a) i = frameRoots σ := by
  ext γ
  constructor
  · rintro ⟨n, δ, hδ, rfl⟩
    rw [hΨ] at hδ
    induction n with
    | zero => exact hδ
    | succ n ih =>
      rw [Function.iterate_succ_apply']
      have hr := h.frameRoots_isRoot _ ih
      rw [hρ _ hr]
      obtain ⟨i, j, hij, hij'⟩ := ih
      exact ⟨j, i, hij.symm, by rw [hij']; exact (h.neg i j).symm⟩
  · intro hγ
    exact ⟨0, γ, by rw [hΨ]; exact hγ, rfl⟩

theorem step_unitary_shape (hq2 : S.D.q = 2) (hρ : ∀ γ, IsRoot τ γ → S.ρ γ = -γ)
    {m : ℕ} (h : IsSLFrame ψ σ) (e : Fin m → Fin ν) (he : Function.Injective e) :
    ∃ Fr : L →+* L, (∀ c, Fr c = c ^ 2 ^ 1) ∧ ∀ i j, i ≠ j → ∃ b : Lˣ, ∀ c : L,
      S.D.step (pinnedX τ L (σ (e i) (e j)) c) =
        pinnedX τ L (σ (e j) (e i)) ((b : L) * Fr c) := by
  obtain ⟨Fr, hFr, -⟩ := S.D.steinberg
  refine ⟨Fr, fun c => by rw [hFr c, hq2, pow_one], fun i j hij => ?_⟩
  have hr := h.isRoot (e i) (e j) (he.ne hij)
  obtain ⟨μ, hμ0, hμ⟩ := step_pinnedX S hr
  refine ⟨Units.mk0 μ hμ0, fun c => ?_⟩
  rw [hμ c, hρ _ hr, h.neg (e i) (e j), Units.val_mk0, hFr c]

theorem le_rationalComponent_of_perfect {χ : Multiplicative (Fin τ.rank → ℤ) →* Lˣ}
    (i : KernelComponent χ) (h : IsSLFrame ψ σ)
    (hR : rationalRoots S.ρ χ i = frameRoots σ) {M : Subgroup (ModGL τ L)} (hMψ : M ≤ ψ.range)
    (hMf : M ≤ S.D.step.eqLocus (MonoidHom.id _)) (hperf : ⁅M, M⁆ = M) :
    M ≤ rationalComponent S.ρ S.Γ χ i := by
  have hMm : M ≤ S.D.model := fun x hx =>
    Subgroup.mem_inf.2 ⟨h.range_le_adjointGroup (hMψ hx), hMf hx⟩
  have hMΓ : M ≤ S.Γ := by
    rw [← hperf]
    exact Subgroup.commutator_mono hMm hMm
  have hMR : M ≤ rationalSpan S.ρ S.Γ χ i := by
    refine le_inf ?_ hMΓ
    rw [hR, ← h.range]
    exact hMψ
  rw [← hperf]
  exact Subgroup.commutator_mono hMR hMR

theorem rationalComponent_le {χ : Multiplicative (Fin τ.rank → ℤ) →* Lˣ}
    (i : KernelComponent χ) (h : IsSLFrame ψ σ)
    (hR : rationalRoots S.ρ χ i = frameRoots σ) :
    rationalComponent S.ρ S.Γ χ i ≤ ψ.range ⊓ S.D.step.eqLocus (MonoidHom.id _) := by
  have h1 : rationalComponent S.ρ S.Γ χ i ≤ rationalSpan S.ρ S.Γ χ i :=
    Subgroup.commutator_le_self _
  have h2 : rationalSpan S.ρ S.Γ χ i ≤ ψ.range := by
    refine inf_le_left.trans ?_
    rw [hR, ← h.range]
  have h3 : rationalSpan S.ρ S.Γ χ i ≤ S.D.model := by
    refine inf_le_right.trans ?_
    exact commutator_le_self_of_subgroup S.D.model
  refine le_inf (h1.trans h2) (h1.trans (h3.trans inf_le_right))

theorem componentOrbitLength_eq_one_frame (hρ : ∀ γ, IsRoot τ γ → S.ρ γ = -γ) {a : Fin τ.rank → Lˣ}
    (i : KernelComponent (rootCharHom a)) (h : IsSLFrame ψ σ)
    (hΨ : componentRoots (rootCharHom a) i = frameRoots σ) :
    componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) = 1 := by
  have h1 : (S.ρ : (Fin τ.rank → ℤ) → _)^[1] '' componentRoots (rootCharHom a) i =
      componentRoots (rootCharHom a) i := by
    rw [hΨ]
    ext γ
    simp only [Function.iterate_one, Set.mem_image]
    constructor
    · rintro ⟨δ, ⟨i, j, hij, rfl⟩, rfl⟩
      rw [hρ _ (h.isRoot i j hij), ← h.neg]
      exact ⟨j, i, hij.symm, rfl⟩
    · rintro ⟨i, j, hij, rfl⟩
      refine ⟨σ j i, ⟨j, i, hij.symm, rfl⟩, ?_⟩
      rw [hρ _ (h.isRoot j i hij.symm), h.neg j i]
  unfold componentOrbitLength
  apply le_antisymm
  · refine Nat.sInf_le ?_
    exact ⟨Nat.one_pos, h1⟩
  · exact (Nat.sInf_mem (s := {s : ℕ | 0 < s ∧ (S.ρ : (Fin τ.rank → ℤ) → _)^[s] '' componentRoots (rootCharHom a) i = componentRoots (rootCharHom a) i}) ⟨1, Nat.one_pos, h1⟩).1

theorem conj_block_mem_of_centralizes (h : IsSLFrame ψ σ) (hν : 3 ≤ ν) (b : Fin τ.rank → Lˣ)
    (k₀ : Fin ν) (X : Finset (Fin ν)) (hX : ∀ k, k ∈ X ↔ rootChar b (σ k k₀) = 1)
    (h2 : ν < 2 * X.card) {m : ℕ} (e : Fin m → Fin ν) (he : Function.Injective e)
    (hXe : ∀ k, k ∈ X ↔ ∃ a, e a = k) {Y : SL(ν, L)}
    (hY : ψ Y ∈ Subgroup.centralizer ({rootDiagUnit τ b} : Set (ModGL τ L))) {Z : SL(ν, L)}
    (hZ : Z ∈ (slEmbed e he).range) : Y * Z * Y⁻¹ ∈ (slEmbed e he).range := by
  classical
  have hconj := conj_eq_of_mem_centralizer_singleton hY
  have htor := h.torus k₀ b Y
  rw [hconj] at htor
  have hker : conjDiagn (fun i => rootChar b (σ i k₀)) Y * Y⁻¹ ∈ ψ.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, ← htor, mul_inv_cancel]
  have hcent := CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three.KSGen.frame_ker_le_center
    hν h hker
  have hzero := commute_diag_of_center (D := fun i => rootChar b (σ i k₀)) X (d₀ := 1) hX h2 hcent
  have hp : projDiag L X * (Y : Matrix (Fin ν) (Fin ν) L) =
      (Y : Matrix (Fin ν) (Fin ν) L) * projDiag L X := by
    ext k l
    unfold projDiag
    rw [Matrix.diagonal_mul, Matrix.mul_diagonal]
    by_cases hk : k ∈ X <;> by_cases hl : l ∈ X
    · simp [hk, hl]
    · have := hzero k l (by rw [(hX k).1 hk]; exact fun hh => hl ((hX l).2 hh.symm))
      simp [hk, hl, this]
    · have := hzero k l (by rw [(hX l).1 hl]; exact fun hh => hk ((hX k).2 hh))
      simp [hk, hl, this]
    · simp [hk, hl]
  exact conj_mem_range_slEmbed e he hXe hp hZ

theorem block_component (hq2 : S.D.q = 2) (hAlg : S.IsAlgebraic)
    (hρ : ∀ γ, IsRoot τ γ → S.ρ γ = -γ) {a b : Fin τ.rank → Lˣ}
    (haT : rootDiagUnit τ a ∈ S.D.torus) (i : KernelComponent (rootCharHom a)) (hν : 3 ≤ ν)
    (h : IsSLFrame ψ σ) (hΨ : componentRoots (rootCharHom a) i = frameRoots σ)
    {ω : L} (hω3 : ω ^ 3 = 1) (hω1 : ω ≠ 1) (k₀ : Fin ν) (X : Finset (Fin ν))
    (hX : ∀ k, k ∈ X ↔ rootChar b (σ k k₀) = 1) (h4 : 4 ≤ X.card) (h2 : ν < 2 * X.card) :
    ∃ J : Subgroup (ModGL τ L),
      CFSG.Open.IsSubnormal J (S.Γ ⊓ Subgroup.centralizer ({rootDiagUnit τ a} : Set (ModGL τ L)) ⊓
        Subgroup.centralizer ({rootDiagUnit τ b} : Set (ModGL τ L))) ∧
      CFSG.Open.IsQuasisimple ↥J ∧ 3 ∣ Nat.card (↥J ⧸ Subgroup.center ↥J) := by
  classical
  obtain ⟨hch, halg⟩ := S.exists_charP_isAlgebraic_zmod hAlg (l := 2) (f := 1) Nat.prime_two
    one_pos (by rw [hq2]; norm_num)
  haveI := hch
  letI := ZMod.algebra L 2
  haveI : IsAlgClosure (ZMod 2) L := ⟨inferInstance, halg⟩
  have hk : Nat.card (ZMod 2) = 2 ^ 1 := by simp
  have hstepinj := splitLine_step_injective S
  set K := rationalComponent S.ρ S.Γ (rootCharHom a) i with hK
  have hR := rationalRoots_eq_frameRoots S hρ i h hΨ
  have hKle := rationalComponent_le S i h hR
  obtain ⟨hKNa, hKsub⟩ := langSubnormal_of_mem_torus S haT i
  have hKsub' : CFSG.Open.IsSubnormal K
      (S.Γ ⊓ Subgroup.centralizer ({rootDiagUnit τ a} : Set (ModGL τ L))) :=
    (CFSG.Open.IsSubnormal.iff_subgroupOf hKNa).2 hKsub
  have hKb := hKsub'.inf (Subgroup.centralizer ({rootDiagUnit τ b} : Set (ModGL τ L)))
  by_cases hXu : X = Finset.univ
  ·
    subst hXu
    have hν4 : 4 ≤ ν := by simpa using h4
    have hb : ∀ a' c', rootChar b (σ a' c') = 1 := by
      intro a' c'
      rw [rootChar_sigma h b a' c' k₀, (hX a').1 (Finset.mem_univ _),
        (hX c').1 (Finset.mem_univ _)]
      simp
    have hKC : K ≤ Subgroup.centralizer ({rootDiagUnit τ b} : Set (ModGL τ L)) := by
      intro y hy
      obtain ⟨⟨A, rfl⟩, -⟩ := hKle hy
      exact mem_centralizer_singleton_of_conj_eq (commute_frame h (by omega) b hb A)
    have hs1 := componentOrbitLength_eq_one_frame S hρ i h hΨ
    have hKq : CFSG.IsQuasisimple ↥K := by
      have hneq : (ν, S.D.q ^ componentOrbitLength S.ρ (componentRoots (rootCharHom a) i)) ≠
          (3, 2) := by
        intro hcon
        have h3 : ν = 3 := congrArg Prod.fst hcon
        omega
      refine (rationalComponent_of_unitary_frame_T S haT i hν h hΨ (Equiv.refl (Fin ν))
        (fun a' b' hab => ?_)).1 hneq
      rw [hs1, Function.iterate_one, hρ _ (h.isRoot a' b' hab)]
      exact (h.neg a' b').symm
    let e₄ : Fin 4 → Fin ν := fun a' => ⟨a', by omega⟩
    have he₄ : Function.Injective e₄ := fun a' b' hab => Fin.ext (by simpa [e₄] using hab)
    have hinj₄ : Function.Injective (ψ.comp (slEmbed e₄ he₄)) := by
      by_cases hν' : ν = 4
      · exact (frame_injective_of_card_four h hν').comp (slEmbed_injective he₄)
      · have hl : ∀ a', e₄ a' ≠ (⟨4, by omega⟩ : Fin ν) := by
          intro a' hc
          have := congrArg Fin.val hc
          have h5 := a'.2
          simp only [e₄] at this
          omega
        exact block_injective h hν e₄ he₄ hl
    obtain ⟨Fr, hFr, hshape⟩ := step_unitary_shape S hq2 hρ h e₄ he₄
    obtain ⟨-, hqs₄, hcard₄, -, x, hx1, hx3⟩ := block_unitary_facts h hν e₄ he₄ hinj₄ le_rfl hk
      Fr hFr S.D.step hstepinj hshape hω3 hω1
    have hperf₄ : ⁅blockFix ψ e₄ he₄ S.D.step, blockFix ψ e₄ he₄ S.D.step⁆ =
        blockFix ψ e₄ he₄ S.D.step := Subgroup.isPerfect_iff.mp hqs₄.1
    have hM₄ψ : blockFix ψ e₄ he₄ S.D.step ≤ ψ.range := by
      intro y hy
      obtain ⟨⟨A, rfl⟩, -⟩ := hy
      exact ⟨slEmbed e₄ he₄ A, rfl⟩
    have hM₄K : blockFix ψ e₄ he₄ S.D.step ≤ K :=
      le_rationalComponent_of_perfect S i h hR hM₄ψ inf_le_right hperf₄
    have hcenter : Subgroup.center ↥(blockFix ψ e₄ he₄ S.D.step) = ⊥ := by
      rw [← Subgroup.card_eq_one, hcard₄]
      norm_num
    let xK : ↥K := ⟨(x : ModGL τ L), hM₄K x.2⟩
    have hxK3 : xK ^ 3 = 1 := by
      apply Subtype.ext
      exact congrArg (fun z : ↥(blockFix ψ e₄ he₄ S.D.step) => (z : ModGL τ L)) hx3
    have hxKc : xK ∉ Subgroup.center ↥K := by
      intro hc
      apply hx1
      have hxc : x ∈ Subgroup.center ↥(blockFix ψ e₄ he₄ S.D.step) := by
        rw [Subgroup.mem_center_iff]
        intro w
        have h1 := Subgroup.mem_center_iff.1 hc ⟨(w : ModGL τ L), hM₄K w.2⟩
        apply Subtype.ext
        exact congrArg (fun z : ↥K => (z : ModGL τ L)) h1
      rw [hcenter] at hxc
      exact Subgroup.mem_bot.1 hxc
    refine ⟨K, ?_, open_isQuasisimple_of_native hKq,
      three_dvd_quot_center_of_noncentral hxK3 hxKc⟩
    rw [inf_eq_left.2 hKC] at hKb
    exact hKb
  ·
    obtain ⟨l, hl⟩ : ∃ l, l ∉ X := by
      by_contra hno
      push Not at hno
      exact hXu (Finset.eq_univ_iff_forall.2 hno)
    let e : Fin X.card → Fin ν := fun a' => ((X.equivFin.symm a' : {x // x ∈ X}) : Fin ν)
    have he : Function.Injective e := Subtype.val_injective.comp X.equivFin.symm.injective
    have hXe : ∀ k, k ∈ X ↔ ∃ a', e a' = k := by
      intro k
      constructor
      · intro hk'
        exact ⟨X.equivFin ⟨k, hk'⟩, by simp [e]⟩
      · rintro ⟨a', rfl⟩
        exact (X.equivFin.symm a').2
    have hel : ∀ a', e a' ≠ l := fun a' hc => hl (hc ▸ (X.equivFin.symm a').2)
    have hinj := block_injective h hν e he hel
    obtain ⟨Fr, hFr, hshape⟩ := step_unitary_shape S hq2 hρ h e he
    obtain ⟨-, hqs, -, h3, -⟩ := block_unitary_facts h hν e he hinj h4 hk Fr hFr S.D.step hstepinj
      hshape hω3 hω1
    have hperf : ⁅blockFix ψ e he S.D.step, blockFix ψ e he S.D.step⁆ =
        blockFix ψ e he S.D.step := Subgroup.isPerfect_iff.mp hqs.1
    have hMψ : blockFix ψ e he S.D.step ≤ ψ.range := by
      intro y hy
      obtain ⟨⟨A, rfl⟩, -⟩ := hy
      exact ⟨slEmbed e he A, rfl⟩
    have hMK : blockFix ψ e he S.D.step ≤ K :=
      le_rationalComponent_of_perfect S i h hR hMψ inf_le_right hperf
    have hb : ∀ a' c', rootChar b (σ (e a') (e c')) = 1 := by
      intro a' c'
      have h1 := (hX (e a')).1 ((hXe (e a')).2 ⟨a', rfl⟩)
      have h2' := (hX (e c')).1 ((hXe (e c')).2 ⟨c', rfl⟩)
      rw [rootChar_sigma h b (e a') (e c') k₀, h1, h2']
      simp
    have hMC : blockFix ψ e he S.D.step ≤
        Subgroup.centralizer ({rootDiagUnit τ b} : Set (ModGL τ L)) := by
      intro y hy
      obtain ⟨⟨A, rfl⟩, -⟩ := hy
      exact mem_centralizer_singleton_of_conj_eq (commute_block h e he (by omega) b hb A)
    have hMKC : blockFix ψ e he S.D.step ≤
        K ⊓ Subgroup.centralizer ({rootDiagUnit τ b} : Set (ModGL τ L)) := le_inf hMK hMC
    have hnormal : ((blockFix ψ e he S.D.step).subgroupOf
        (K ⊓ Subgroup.centralizer ({rootDiagUnit τ b} : Set (ModGL τ L)))).Normal := by
      rw [Subgroup.normal_subgroupOf_iff hMKC]
      intro x y hx hy
      obtain ⟨hyK, hyC⟩ := Subgroup.mem_inf.1 hy
      obtain ⟨⟨Y, rfl⟩, hyf⟩ := hKle hyK
      obtain ⟨⟨A, rfl⟩, hxf⟩ := hx
      have hZ : slEmbed e he A ∈ (slEmbed e he).range := ⟨A, rfl⟩
      obtain ⟨A', hA'⟩ := conj_block_mem_of_centralizes h hν b k₀ X hX h2 e he hXe hyC hZ
      refine ⟨⟨A', ?_⟩, ?_⟩
      · show ψ (slEmbed e he A') = _
        rw [hA', map_mul, map_mul, map_inv]
        rfl
      · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hyf hxf) (Subgroup.inv_mem _ hyf)
    exact ⟨blockFix ψ e he S.D.step, CFSG.Open.IsSubnormal.step hMKC hnormal hKb,
      open_isQuasisimple_of_native hqs, h3⟩

end Lang

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie.X2E6.T

end
