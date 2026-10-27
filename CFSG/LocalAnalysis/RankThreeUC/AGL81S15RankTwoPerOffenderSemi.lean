module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RankTwoPerOffenderNat

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open Matrix

private lemma semi_rho_comm {G : Type*} [Group G] {V : Type*} [AddCommGroup V]
    [Module (ZMod 2) V] {ρ : Representation (ZMod 2) G V} {c l : G} (hcl : c * l = l * c)
    (y : V) : ρ c (ρ l y) = ρ l (ρ c y) := by
  have h : (ρ c : V →ₗ[ZMod 2] V) * ρ l = ρ l * ρ c := by
    rw [← map_mul, hcl, map_mul]
  simpa only [Module.End.mul_apply] using congrArg (fun f : V →ₗ[ZMod 2] V => f y) h

private lemma semi_rho_conj {G : Type*} [Group G] {V : Type*} [AddCommGroup V]
    [Module (ZMod 2) V] {ρ : Representation (ZMod 2) G V} (g l : G) (x : V) :
    ρ l (ρ g x) = ρ g (ρ (g⁻¹ * l * g) x) := by
  have h : (ρ l : V →ₗ[ZMod 2] V) * ρ g = ρ g * ρ (g⁻¹ * l * g) := by
    rw [← map_mul, ← map_mul]
    exact congrArg ρ (by group)
  simpa only [Module.End.mul_apply] using congrArg (fun f : V →ₗ[ZMod 2] V => f x) h

private lemma semi_rho_conj' {G : Type*} [Group G] {V : Type*} [AddCommGroup V]
    [Module (ZMod 2) V] {ρ : Representation (ZMod 2) G V} (g l : G) (x : V) :
    ρ g (ρ l x) = ρ (g * l * g⁻¹) (ρ g x) := by
  have h : (ρ g : V →ₗ[ZMod 2] V) * ρ l = ρ (g * l * g⁻¹) * ρ g := by
    rw [← map_mul, ← map_mul]
    exact congrArg ρ (by group)
  simpa only [Module.End.mul_apply] using congrArg (fun f : V →ₗ[ZMod 2] V => f x) h

private theorem NatQuot.rho_eq_of_commute_of_quot_trivial {G : Type*} [Group G] {V : Type*}
    [AddCommGroup V] [Module (ZMod 2) V] {ρ : Representation (ZMod 2) G V} {L : Subgroup G}
    {F : Type*} [Field F] {r : ℕ} (N : NatQuot ρ L F r)
    (hIcomm : ∀ v ∈ N.I, v ∈ Submodule.span (ZMod 2)
      {w | ∃ l ∈ L, ∃ x ∈ N.I, w = ρ l x - x})
    (c : G) (hc : ∀ l ∈ L, c * l = l * c) (hcI : ∀ v ∈ N.I, ρ c v ∈ N.I)
    (hcπ : ∀ v : ↥N.I, N.π ⟨ρ c v, hcI v v.2⟩ = N.π v) : ∀ v ∈ N.I, ρ c v = v := by
  intro v hv
  have hgen : ∀ (l : G) (hl : l ∈ L) (x : V) (hx : x ∈ N.I),
      ρ c (ρ l x - x) = ρ l x - x := by
    intro l hl x hx
    have hdx : ρ l (ρ c x - x) = ρ c x - x := by
      have hker : N.π (⟨ρ c x, hcI x hx⟩ - ⟨x, hx⟩) = 0 := by
        rw [map_sub, hcπ ⟨x, hx⟩, sub_self]
      have := (N.ker_iff (⟨ρ c x, hcI x hx⟩ - ⟨x, hx⟩)).mp hker l hl
      simpa using this
    have hcommx : ρ c (ρ l x) = ρ l (ρ c x) := semi_rho_comm (hc l hl) x
    calc ρ c (ρ l x - x)
        = ρ c (ρ l x) - ρ c x := map_sub (ρ c) _ _
      _ = ρ l (ρ c x) - ρ c x := by rw [hcommx]
      _ = ρ l (ρ c x - x) + ρ l x - ρ c x := by rw [map_sub]; abel
      _ = (ρ c x - x) + ρ l x - ρ c x := by rw [hdx]
      _ = ρ l x - x := by abel
  refine Submodule.span_induction (p := fun x _ => ρ c x = x) ?_ ?_ ?_ ?_ (hIcomm v hv)
  · intro w hw
    rcases hw with ⟨l, hl, x, hx, rfl⟩
    exact hgen l hl x hx
  · simp
  · intro x y hx hy hpx hpy
    rw [map_add, hpx, hpy]
  · intro a x hx hpx
    rw [map_smul, hpx]

private theorem NatQuot.exists_psi {G : Type*} [Group G] {V : Type*} [AddCommGroup V]
    [Module (ZMod 2) V] {ρ : Representation (ZMod 2) G V} {L : Subgroup G} {F : Type*} [Field F]
    {r : ℕ} (N : NatQuot ρ L F r) {g : G} (hgN : ∀ l ∈ L, g * l * g⁻¹ ∈ L)
    (hgN' : ∀ l ∈ L, g⁻¹ * l * g ∈ L) (hgI : ∀ v ∈ N.I, ρ g v ∈ N.I)
    (hg2 : ∀ v ∈ N.I, ρ g (ρ g v) = v) :
    ∃ T : (Fin r → F) ≃+ (Fin r → F),
      (∀ v : ↥N.I, N.π ⟨ρ g v, hgI v v.2⟩ = T (N.π v)) ∧ (∀ u, T (T u) = u) ∧
      (∀ (l : ↥L) (u : Fin r → F), T ((N.Mat l : Matrix (Fin r) (Fin r) F) *ᵥ u) =
        (N.Mat ⟨g * l * g⁻¹, hgN l l.2⟩ : Matrix (Fin r) (Fin r) F) *ᵥ T u) := by
  let ρgI : ↥N.I →+ ↥N.I :=
    { toFun := fun x => ⟨ρ g (x : V), hgI x x.2⟩
      map_zero' := by
        apply Subtype.ext
        simp
      map_add' := by
        intro x y
        apply Subtype.ext
        simp only [Submodule.coe_add]
        exact map_add (ρ g) (x : V) (y : V) }
  have hφ : N.π.ker ≤ (N.π.comp ρgI).ker := by
    intro x hx
    rw [AddMonoidHom.mem_ker] at hx ⊢
    change N.π (ρgI x) = 0
    apply (N.ker_iff (ρgI x)).mpr
    intro l hl
    change ρ l (ρ g (x : V)) = ρ g (x : V)
    rw [semi_rho_conj g l (x : V)]
    rw [(N.ker_iff x).mp hx (g⁻¹ * l * g) (hgN' l hl)]
  let ψ : (Fin r → F) →+ (Fin r → F) := (N.π.liftOfSurjective N.surj) ⟨N.π.comp ρgI, hφ⟩
  have hψ : ∀ x : ↥N.I, ψ (N.π x) = N.π ⟨ρ g (x : V), hgI x x.2⟩ := by
    intro x
    exact AddMonoidHom.liftOfRightInverse_comp_apply N.π (Function.surjInv N.surj)
      (Function.rightInverse_surjInv N.surj) ⟨N.π.comp ρgI, hφ⟩ x
  have hψ2 : ∀ u : Fin r → F, ψ (ψ u) = u := by
    intro u
    obtain ⟨x, rfl⟩ := N.surj u
    rw [hψ, hψ]
    apply congrArg N.π
    apply Subtype.ext
    exact hg2 x x.2
  have hψcomm : ∀ (l : ↥L) (u : Fin r → F),
      ψ ((N.Mat l : Matrix (Fin r) (Fin r) F) *ᵥ u) =
        (N.Mat ⟨g * (l : G) * g⁻¹, hgN (l : G) l.2⟩ :
          Matrix (Fin r) (Fin r) F) *ᵥ ψ u := by
    intro l u
    obtain ⟨x, rfl⟩ := N.surj u
    rw [← N.equiv l x, hψ, hψ,
      ← N.equiv ⟨g * (l : G) * g⁻¹, hgN (l : G) l.2⟩ ⟨ρ g x, hgI x x.2⟩]
    apply congrArg N.π
    apply Subtype.ext
    exact semi_rho_conj' g (l : G) (x : V)
  let T : (Fin r → F) ≃+ (Fin r → F) :=
    { toFun := ψ, invFun := ψ, left_inv := hψ2, right_inv := hψ2, map_add' := ψ.map_add }
  exact ⟨T, fun v => (hψ v).symm, fun u => hψ2 u, fun l u => hψcomm l u⟩

theorem NatQuot.exists_semilinear_psi {G : Type*} [Group G] {V : Type*} [AddCommGroup V]
    [Module (ZMod 2) V] {ρ : Representation (ZMod 2) G V} {L : Subgroup G} {F : Type*} [Field F]
    [Finite F] {r : ℕ} (N : NatQuot ρ L F r) (hS : NatSchur N.Mat) {g : G}
    (hgN : ∀ l ∈ L, g * l * g⁻¹ ∈ L) (hgN' : ∀ l ∈ L, g⁻¹ * l * g ∈ L)
    (hgI : ∀ v ∈ N.I, ρ g v ∈ N.I) (hg2 : ∀ v ∈ N.I, ρ g (ρ g v) = v) :
    ∃ (T : (Fin r → F) ≃+ (Fin r → F)) (σ : F ≃+* F),
      (∀ v : ↥N.I, N.π ⟨ρ g v, hgI v v.2⟩ = T (N.π v)) ∧ (∀ u, T (T u) = u) ∧
      (∀ (c : F) (u : Fin r → F), T (c • u) = σ c • T u) := by
  obtain ⟨T, hT1, hT2, hT3raw⟩ := N.exists_psi hgN hgN' hgI hg2
  by_cases hr : r = 0
  · refine ⟨T, RingEquiv.refl F, hT1, hT2, ?_⟩
    intro c u
    have : Subsingleton (Fin r → F) := by
      rw [hr]
      exact ⟨fun f g => funext fun i => i.elim0⟩
    exact Subsingleton.elim _ _
  · let φ : ↥L → ↥L := fun l => ⟨g * (l : G) * g⁻¹, hgN (l : G) l.2⟩
    have hT3 : ∀ (l : ↥L) (u : Fin r → F),
        T ((N.Mat l : Matrix (Fin r) (Fin r) F) *ᵥ u) =
          (N.Mat (φ l) : Matrix (Fin r) (Fin r) F) *ᵥ T u :=
      fun l u => hT3raw l u
    have hφφ : ∀ l : ↥L, N.Mat (φ (φ l)) = N.Mat l := by
      intro l
      apply Units.ext
      rw [Matrix.ext_iff_mulVec]
      intro w
      calc (N.Mat (φ (φ l)) : Matrix (Fin r) (Fin r) F) *ᵥ w
          = (N.Mat (φ (φ l)) : Matrix (Fin r) (Fin r) F) *ᵥ T (T w) := by rw [hT2 w]
        _ = T ((N.Mat (φ l) : Matrix (Fin r) (Fin r) F) *ᵥ T w) := by
              rw [← hT3 (φ l) (T w)]
        _ = T (T ((N.Mat l : Matrix (Fin r) (Fin r) F) *ᵥ w)) := by rw [← hT3 l w]
        _ = (N.Mat l : Matrix (Fin r) (Fin r) F) *ᵥ w := hT2 _
    let δ : F → ((Fin r → F) →+ (Fin r → F)) := fun c =>
      { toFun := fun u => T (c • T u)
        map_zero' := by simp
        map_add' := by
          intro u v
          rw [T.map_add, smul_add, T.map_add] }
    have hδcomm : ∀ (c : F), ∀ (l : ↥L) (u : Fin r → F),
        δ c ((N.Mat l : Matrix (Fin r) (Fin r) F) *ᵥ u) =
          (N.Mat l : Matrix (Fin r) (Fin r) F) *ᵥ δ c u := by
      intro c l u
      change T (c • T ((N.Mat l : Matrix (Fin r) (Fin r) F) *ᵥ u)) =
        (N.Mat l : Matrix (Fin r) (Fin r) F) *ᵥ T (c • T u)
      rw [hT3 l u]
      rw [← Matrix.mulVec_smul]
      rw [hT3 (φ l) (c • T u)]
      rw [hφφ l]
    let σs : F → F := fun c => (hS (δ c) (hδcomm c)).choose
    have hσs : ∀ c u, δ c u = σs c • u := fun c => (hS (δ c) (hδcomm c)).choose_spec
    have hσs' : ∀ c w, T (c • T w) = σs c • w := fun c w => hσs c w
    have hsem : ∀ (c : F) (u : Fin r → F), T (c • u) = σs c • T u := by
      intro c u
      have h1 : δ c (T u) = T (c • u) := by
        change T (c • T (T u)) = T (c • u)
        rw [hT2 u]
      rw [← h1, hσs c (T u)]
    let i0 : Fin r := ⟨0, Nat.pos_of_ne_zero hr⟩
    let u0 : Fin r → F := Pi.single i0 1
    have htest : ∀ {a b : F}, a • u0 = b • u0 → a = b := by
      intro a b h
      have h' := congrFun h i0
      simpa [u0, Pi.smul_apply, Pi.single_eq_same, smul_eq_mul] using h'
    have hσ0 : σs 0 = 0 := by
      apply htest
      rw [← hσs' 0 u0]
      simp
    have hσ1 : σs 1 = 1 := by
      apply htest
      rw [← hσs' 1 u0]
      simp only [one_smul]
      exact hT2 u0
    have hσadd : ∀ a b : F, σs (a + b) = σs a + σs b := by
      intro a b
      apply htest
      rw [← hσs' (a + b) u0]
      have hR : (σs a + σs b) • u0 = σs a • u0 + σs b • u0 := add_smul _ _ _
      rw [hR, add_smul, ← hσs' a u0, ← hσs' b u0, T.map_add]
    have hσmul : ∀ a b : F, σs (a * b) = σs a * σs b := by
      intro a b
      apply htest
      rw [← hσs' (a * b) u0]
      have hb : T (b • T u0) = σs b • u0 := hσs' b u0
      calc T ((a * b) • T u0)
          = T (a • (b • T u0)) := by rw [mul_smul]
        _ = T (a • T (T (b • T u0))) := by
              conv_lhs => rw [← hT2 (b • T u0)]
        _ = σs a • T (b • T u0) := hσs' a (T (b • T u0))
        _ = σs a • (σs b • u0) := by rw [hb]
        _ = (σs a * σs b) • u0 := by rw [smul_smul]
    have hσinj : Function.Injective σs := by
      intro c d hcd
      have h1 : c • u0 = d • u0 := by
        apply T.injective
        rw [hsem c u0, hsem d u0, hcd]
      exact htest h1
    let σhom : F →+* F :=
      { toFun := σs
        map_one' := hσ1
        map_mul' := hσmul
        map_zero' := hσ0
        map_add' := hσadd }
    let σ : F ≃+* F := RingEquiv.ofBijective σhom hσinj.bijective_of_finite
    exact ⟨T, σ, hT1, hT2, fun c u => hsem c u⟩

theorem NatQuot.acts_as_L_of_linear {G : Type*} [Group G] {V : Type*} [AddCommGroup V]
    [Module (ZMod 2) V] {ρ : Representation (ZMod 2) G V} {L : Subgroup G} {F : Type*} [Field F]
    {r : ℕ} (N : NatQuot ρ L F r) (hO : NatOut N.Mat)
    (hIcomm : ∀ v ∈ N.I, v ∈ Submodule.span (ZMod 2)
      {w | ∃ l ∈ L, ∃ x ∈ N.I, w = ρ l x - x})
    {g : G} (hgN : ∀ l ∈ L, g * l * g⁻¹ ∈ L)
    (hgI : ∀ v ∈ N.I, ρ g v ∈ N.I) (hg2 : ∀ v ∈ N.I, ρ g (ρ g v) = v)
    (T : (Fin r → F) ≃+ (Fin r → F))
    (hTπ : ∀ v : ↥N.I, N.π ⟨ρ g v, hgI v v.2⟩ = T (N.π v))
    (hTlin : ∀ (c : F) (u : Fin r → F), T (c • u) = c • T u) :
    ∃ l₀ ∈ L, (∀ v ∈ N.I, ρ g v = ρ l₀ v) ∧ ∀ x ∈ L, g * x * g⁻¹ = l₀ * x * l₀⁻¹ := by
  have hinter : ∀ (l : ↥L) (u : Fin r → F),
      T ((N.Mat l : Matrix (Fin r) (Fin r) F) *ᵥ u) =
        (N.Mat ⟨g * (l : G) * g⁻¹, hgN (l : G) l.2⟩ :
          Matrix (Fin r) (Fin r) F) *ᵥ T u := by
    intro l u
    obtain ⟨v, rfl⟩ := N.surj u
    rw [← N.equiv l v, ← hTπ ⟨ρ l v, N.inv l l.2 v v.2⟩, ← hTπ v,
      ← N.equiv ⟨g * (l : G) * g⁻¹, hgN (l : G) l.2⟩ ⟨ρ g v, hgI v v.2⟩]
    apply congrArg N.π
    apply Subtype.ext
    exact semi_rho_conj' g (l : G) (v : V)
  let Tlin : (Fin r → F) →ₗ[F] (Fin r → F) :=
    { toFun := T, map_add' := T.map_add, map_smul' := hTlin }
  let M : Matrix (Fin r) (Fin r) F := LinearMap.toMatrix' Tlin
  have hM : ∀ u, M *ᵥ u = T u := fun u => LinearMap.toMatrix'_mulVec Tlin u
  have hT2 : ∀ u, T (T u) = u := by
    intro u
    obtain ⟨v, rfl⟩ := N.surj u
    rw [← hTπ v, ← hTπ ⟨ρ g v, hgI v v.2⟩]
    apply congrArg N.π
    apply Subtype.ext
    exact hg2 v v.2
  have hMM : M * M = 1 := by
    rw [Matrix.ext_iff_mulVec]
    intro u
    rw [← Matrix.mulVec_mulVec, hM (M *ᵥ u), hM u, hT2 u, Matrix.one_mulVec]
  let M' : Matrix.GeneralLinearGroup (Fin r) F := ⟨M, M, hMM, hMM⟩
  have hM'M' : M' * M' = 1 := by
    apply Units.ext
    simpa [M'] using hMM
  have hM'inv : M'⁻¹ = M' := by
    have h : M' * M' = M' * M'⁻¹ := by rw [hM'M', mul_inv_cancel]
    exact (mul_left_cancel h).symm
  have hcommM : ∀ l : ↥L,
      M * (N.Mat l : Matrix (Fin r) (Fin r) F) =
        (N.Mat ⟨g * (l : G) * g⁻¹, hgN (l : G) l.2⟩ :
          Matrix (Fin r) (Fin r) F) * M := by
    intro l
    rw [Matrix.ext_iff_mulVec]
    intro u
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hM (N.Mat l *ᵥ u), hM u, hinter l u]
  have hcommM_gl : ∀ l : ↥L,
      M' * N.Mat l = N.Mat ⟨g * (l : G) * g⁻¹, hgN (l : G) l.2⟩ * M' := by
    intro l
    apply Units.ext
    simpa only [Units.val_mul, M'] using hcommM l
  have hgl : ∀ l : ↥L,
      N.Mat ⟨g * (l : G) * g⁻¹, hgN (l : G) l.2⟩ = M' * N.Mat l * M'⁻¹ := by
    intro l
    rw [hcommM_gl l]
    group
  obtain ⟨l0, hl0⟩ := hO M' hM'M' (fun l => ⟨⟨g * (l : G) * g⁻¹, hgN (l : G) l.2⟩, hgl l⟩)
  have hconj : ∀ x : ↥L, (⟨g * (x : G) * g⁻¹, hgN (x : G) x.2⟩ : ↥L) = l0 * x * l0⁻¹ := by
    intro x
    apply N.mat_inj
    have h1 : N.Mat (l0 * x * l0⁻¹) = M' * N.Mat x * M'⁻¹ := by
      simp only [map_mul, map_inv, hl0]
    exact (hgl x).trans h1.symm
  let c : G := (l0 : G)⁻¹ * g
  have hc : ∀ l ∈ L, c * l = l * c := by
    intro l hl
    have hgl' : g * l * g⁻¹ = (l0 : G) * l * (l0 : G)⁻¹ := by
      have h := congrArg Subtype.val (hconj ⟨l, hl⟩)
      simpa using h
    show ((l0 : G)⁻¹ * g) * l = l * ((l0 : G)⁻¹ * g)
    calc ((l0 : G)⁻¹ * g) * l
        = (l0 : G)⁻¹ * (g * l * g⁻¹) * g := by group
      _ = (l0 : G)⁻¹ * ((l0 : G) * l * (l0 : G)⁻¹) * g := by rw [hgl']
      _ = l * ((l0 : G)⁻¹ * g) := by group
  have hcI : ∀ v ∈ N.I, ρ c v ∈ N.I := by
    intro v hv
    have h2 : (l0 : G)⁻¹ ∈ L := L.inv_mem l0.2
    have h3 : ρ ((l0 : G)⁻¹) (ρ g v) ∈ N.I := N.inv ((l0 : G)⁻¹) h2 (ρ g v) (hgI v hv)
    simpa [c, map_mul, Module.End.mul_apply] using h3
  have hcπ : ∀ v : ↥N.I, N.π ⟨ρ c (v : V), hcI v v.2⟩ = N.π v := by
    intro v
    have hρc : ρ c (v : V) = ρ ((l0 : G)⁻¹) (ρ g (v : V)) := by
      simp only [c, map_mul, Module.End.mul_apply]
    have h1 : N.π ⟨ρ c (v : V), hcI v v.2⟩ =
        N.π ⟨ρ ((l0 : G)⁻¹) (ρ g (v : V)),
          N.inv ((l0 : G)⁻¹) (L.inv_mem l0.2) (ρ g (v : V)) (hgI v v.2)⟩ := by
      apply congrArg N.π
      apply Subtype.ext
      exact hρc
    rw [h1, N.equiv ⟨(l0 : G)⁻¹, L.inv_mem l0.2⟩ ⟨ρ g (v : V), hgI v v.2⟩]
    rw [hTπ v]
    have hinv : N.Mat ⟨(l0 : G)⁻¹, L.inv_mem l0.2⟩ = (N.Mat l0)⁻¹ := by
      have heq : (⟨(l0 : G)⁻¹, L.inv_mem l0.2⟩ : ↥L) = l0⁻¹ := by
        apply Subtype.ext
        rfl
      rw [heq, map_inv]
    rw [hinv, hl0, hM'inv]
    change M *ᵥ T (N.π v) = N.π v
    rw [hM (T (N.π v)), hT2 (N.π v)]
  have hcA : ∀ v ∈ N.I, ρ c v = v :=
    N.rho_eq_of_commute_of_quot_trivial hIcomm c hc hcI hcπ
  refine ⟨(l0 : G), l0.2, ?_, ?_⟩
  · intro v hv
    have hcv : ρ c v = v := hcA v hv
    have hg_eq : g = (l0 : G) * c := by simp [c]
    calc ρ g v = ρ ((l0 : G) * c) v := by rw [hg_eq]
      _ = ρ (l0 : G) (ρ c v) := by simp only [map_mul, Module.End.mul_apply]
      _ = ρ (l0 : G) v := by rw [hcv]
  · intro x hx
    have h := congrArg Subtype.val (hconj ⟨x, hx⟩)
    simpa using h

end CFSG.LocalAnalysis.RankThreeUC.S15

end
