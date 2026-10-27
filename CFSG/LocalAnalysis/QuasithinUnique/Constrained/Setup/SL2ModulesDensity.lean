module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesTensor
public import Mathlib.RingTheory.LittleWedderburn

public section

namespace CFSG.QuasithinUnique.Setup.SL2Modules

section Density

variable {k₀ : Type*} [Field k₀] {G : Type*} [Monoid G] {W : Type*} [AddCommGroup W] [Module k₀ W]
  (ρ : Representation k₀ G W)

abbrev spanAlg : Subalgebra k₀ (Module.End k₀ W) := Algebra.adjoin k₀ (Set.range ρ)

theorem isSimpleModule_spanAlg (hρ : ρ.IsIrreducible) : IsSimpleModule (spanAlg ρ) W := by
  obtain ⟨hnt, hirr⟩ := (isIrreducible_iff ρ).mp hρ
  rw [isSimpleModule_iff]
  have : Nontrivial (Submodule (spanAlg ρ) W) := by
    obtain ⟨x, y, hxy⟩ := hnt
    exact ⟨⊥, ⊤, fun h => hxy (by
      have h1 : x - y ∈ (⊥ : Submodule (spanAlg ρ) W) := h ▸ Submodule.mem_top
      exact sub_eq_zero.mp ((Submodule.mem_bot _).mp h1))⟩
  refine ⟨fun N => ?_⟩
  let N' : Submodule k₀ W := N.restrictScalars k₀
  have hinv : ∀ g, ∀ u ∈ N', ρ g u ∈ N' := by
    intro g u hu
    have : ρ g u = (⟨ρ g, Algebra.subset_adjoin ⟨g, rfl⟩⟩ : spanAlg ρ) • u := rfl
    rw [this]
    exact N.smul_mem _ hu
  rcases hirr N' hinv with h | h
  · left
    exact (Submodule.restrictScalars_eq_bot_iff k₀ (spanAlg ρ) W).mp h
  · right
    exact (Submodule.restrictScalars_eq_top_iff k₀ (spanAlg ρ) W).mp h


abbrev EndRing : Type _ := Module.End (spanAlg ρ) W

theorem mem_endRing_iff (φ : Module.End k₀ W) :
    (∃ ψ : EndRing ρ, (ψ : W → W) = φ) ↔ ∀ g v, φ (ρ g v) = ρ g (φ v) := by
  constructor
  · rintro ⟨ψ, hψ⟩ g v
    have := ψ.map_smul (⟨ρ g, Algebra.subset_adjoin ⟨g, rfl⟩⟩ : spanAlg ρ) v
    rw [← hψ]
    exact this
  · intro h
    have hc : ∀ r ∈ spanAlg ρ, ∀ v, φ (r v) = r (φ v) := by
      intro r hr
      induction hr using Algebra.adjoin_induction with
      | mem x hx => obtain ⟨g, rfl⟩ := hx; exact fun v => h g v
      | algebraMap c => intro v; simp
      | add x y _ _ hx hy => intro v; simp [hx v, hy v]
      | mul x y _ _ hx hy => intro v; simp [hx (y v), hy v]
    refine ⟨{ toFun := φ, map_add' := φ.map_add, map_smul' := fun r v => hc r r.2 v }, rfl⟩

variable [Fact ρ.IsIrreducible]

instance : IsSimpleModule (spanAlg ρ) W := isSimpleModule_spanAlg ρ Fact.out

noncomputable instance : DecidableEq (EndRing ρ) := Classical.decEq _

omit [Fact ρ.IsIrreducible] in
theorem finite_endRing [Finite W] : Finite (EndRing ρ) :=
  Finite.of_injective (fun f : EndRing ρ => (f : W → W)) DFunLike.coe_injective

noncomputable instance endRingField [Finite W] : Field (EndRing ρ) :=
  haveI := finite_endRing ρ
  littleWedderburn (EndRing ρ)


set_option synthInstance.maxHeartbeats 200000 in
theorem density_surjective [Finite W] (φ : Module.End (EndRing ρ) W) :
    ∃ r : spanAlg ρ, ∀ w, φ w = (r : Module.End k₀ W) w := by
  have := finite_endRing ρ
  have : Module.Finite (EndRing ρ) W := Module.Finite.of_finite
  obtain ⟨r, hr⟩ := Module.Finite.toModuleEnd_moduleEnd_surjective (R := spanAlg ρ) (M := W) φ
  exact ⟨r, fun w => (congrArg (fun f : Module.End (EndRing ρ) W => f w) hr).symm⟩

omit [Fact ρ.IsIrreducible] in
@[expose] noncomputable def repD : G →* Module.End (EndRing ρ) W where
  toFun g :=
    { toFun := fun w => ρ g w
      map_add' := fun x y => map_add (ρ g) x y
      map_smul' := fun d w => by
        have := d.map_smul (⟨ρ g, Algebra.subset_adjoin ⟨g, rfl⟩⟩ : spanAlg ρ) w
        exact this.symm }
  map_one' := by
    apply LinearMap.ext
    intro w
    simp
  map_mul' g h := by
    apply LinearMap.ext
    intro w
    simp

omit [Fact ρ.IsIrreducible] in
theorem repD_apply (g : G) (w : W) : repD ρ g w = ρ g w := rfl

variable {ρ} [Finite W]

@[expose] noncomputable def matRep {m : ℕ} (b : Module.Basis (Fin m) (EndRing ρ) W) :
    G →* Matrix (Fin m) (Fin m) (EndRing ρ) where
  toFun g := LinearMap.toMatrix b b (repD ρ g)
  map_one' := by simp
  map_mul' g h := by simp [LinearMap.toMatrix_mul]

@[expose] noncomputable def matRepE {m : ℕ} (b : Module.Basis (Fin m) (EndRing ρ) W)
    {E : Type*} [Field E] (ι : EndRing ρ →+* E) : Representation E G (Fin m → E) where
  toFun g := Matrix.toLin' ((matRep b g).map ι)
  map_one' := by simp; rfl
  map_mul' g h := by
    rw [map_mul, Matrix.map_mul, Matrix.toLin'_mul]; rfl

theorem matRepE_apply {m : ℕ} (b : Module.Basis (Fin m) (EndRing ρ) W) {E : Type*} [Field E]
    (ι : EndRing ρ →+* E) (g : G) (x : Fin m → E) :
    matRepE b ι g x = ((matRep b g).map ι).mulVec x := by
  simp [matRepE, Matrix.toLin'_apply]


omit [Fact ρ.IsIrreducible] [Finite W] in
@[expose] def actD (r : spanAlg ρ) : Module.End (EndRing ρ) W where
  toFun w := (r : Module.End k₀ W) w
  map_add' x y := map_add (r : Module.End k₀ W) x y
  map_smul' d w := (d.map_smul r w).symm

omit [Fact ρ.IsIrreducible] [Finite W] in
theorem actD_apply (r : spanAlg ρ) (w : W) : actD r w = (r : Module.End k₀ W) w := rfl

omit [Fact ρ.IsIrreducible] [Finite W] in
theorem actD_add (r s : spanAlg ρ) : actD (r + s) = actD r + actD s := rfl

omit [Fact ρ.IsIrreducible] [Finite W] in
theorem actD_mul (r s : spanAlg ρ) : actD (r * s) = actD r * actD s := rfl

omit [Fact ρ.IsIrreducible] [Finite W] in
theorem actD_gen (g : G) : actD (⟨ρ g, Algebra.subset_adjoin ⟨g, rfl⟩⟩ : spanAlg ρ) = repD ρ g := rfl

set_option synthInstance.maxHeartbeats 400000 in
theorem actD_algebraMap (c : k₀) : actD (algebraMap k₀ (spanAlg ρ) c) =
    algebraMap (EndRing ρ) (Module.End (EndRing ρ) W) (algebraMap k₀ (EndRing ρ) c) := by
  apply LinearMap.ext
  intro w
  rfl

set_option synthInstance.maxHeartbeats 400000 in
theorem matRepE_isIrreducible {m : ℕ} (b : Module.Basis (Fin m) (EndRing ρ) W)
    {E : Type*} [Field E] (ι : EndRing ρ →+* E) : (matRepE b ι).IsIrreducible := by
  obtain ⟨hnt, -⟩ := (isIrreducible_iff ρ).mp Fact.out
  rw [isIrreducible_iff]
  have hm : 0 < m := by
    have : 0 < Module.finrank (EndRing ρ) W := Module.finrank_pos
    rwa [Module.finrank_eq_card_basis b, Fintype.card_fin] at this
  refine ⟨⟨fun _ => 0, fun _ => 1, fun h => one_ne_zero (congrFun h ⟨0, hm⟩).symm⟩, fun N₀ hinv => ?_⟩
  by_cases hbot : N₀ = ⊥
  · exact Or.inl hbot
  right
  obtain ⟨v, hvN, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hbot
  have hinv' : ∀ g, ∀ x ∈ N₀, ((matRep b g).map ι).mulVec x ∈ N₀ := fun g x hx => by
    have := hinv g x hx
    rwa [matRepE_apply] at this
  have hclaim : ∀ r : Module.End k₀ W, ∀ hr : r ∈ spanAlg ρ, ∀ x ∈ N₀,
      ((LinearMap.toMatrix b b (actD ⟨r, hr⟩)).map ι).mulVec x ∈ N₀ := by
    intro r hr
    induction hr using Algebra.adjoin_induction with
    | mem y hy =>
      obtain ⟨g, rfl⟩ := hy
      intro x hx
      have := hinv' g x hx
      simpa [matRep, actD_gen] using this
    | algebraMap c =>
      intro x hx
      have h1 : actD (⟨algebraMap k₀ (Module.End k₀ W) c, Subalgebra.algebraMap_mem _ c⟩ : spanAlg ρ) =
          algebraMap (EndRing ρ) (Module.End (EndRing ρ) W) (algebraMap k₀ (EndRing ρ) c) :=
        actD_algebraMap c
      rw [h1, LinearMap.toMatrix_algebraMap]
      simp only [Matrix.scalar_apply]
      have h2 : ((Matrix.diagonal fun _ => algebraMap k₀ (EndRing ρ) c).map ι).mulVec x =
          (ι (algebraMap k₀ (EndRing ρ) c)) • x := by
        rw [Matrix.diagonal_map (map_zero ι)]
        funext i
        simp [Matrix.mulVec_diagonal]
      rw [h2]
      exact N₀.smul_mem _ hx
    | add x y hx hy ihx ihy =>
      intro z hz
      have h1 : actD (⟨x + y, add_mem hx hy⟩ : spanAlg ρ) =
          actD (⟨x, hx⟩ : spanAlg ρ) + actD (⟨y, hy⟩ : spanAlg ρ) := rfl
      rw [h1, map_add, Matrix.map_add _ (fun a b => map_add ι a b), Matrix.add_mulVec]
      exact N₀.add_mem (ihx z hz) (ihy z hz)
    | mul x y hx hy ihx ihy =>
      intro z hz
      have h1 : actD (⟨x * y, mul_mem hx hy⟩ : spanAlg ρ) =
          actD (⟨x, hx⟩ : spanAlg ρ) * actD (⟨y, hy⟩ : spanAlg ρ) := rfl
      rw [h1, LinearMap.toMatrix_mul, Matrix.map_mul, ← Matrix.mulVec_mulVec]
      exact ihx _ (ihy z hz)
  have hY : ∀ Y : Matrix (Fin m) (Fin m) (EndRing ρ), ∀ x ∈ N₀, (Y.map ι).mulVec x ∈ N₀ := by
    intro Y x hx
    obtain ⟨r, hr⟩ := density_surjective (ρ := ρ) ((LinearMap.toMatrix b b).symm Y)
    have h1 : (LinearMap.toMatrix b b).symm Y = actD r := LinearMap.ext fun w => hr w
    have h2 : Y = LinearMap.toMatrix b b (actD r) := by
      rw [← h1]; simp
    rw [h2]
    exact hclaim r r.2 x hx
  obtain ⟨j, hj⟩ : ∃ j, v j ≠ 0 := by
    by_contra hc
    push Not at hc
    exact hv0 (funext hc)
  have hbasis : ∀ i, (Pi.single i 1 : Fin m → E) ∈ N₀ := by
    intro i
    have h1 := hY (Matrix.single i j 1) v hvN
    have h2 : ((Matrix.single i j (1 : EndRing ρ)).map ι).mulVec v = Pi.single i (v j) := by
      rw [Matrix.map_single, map_one, Matrix.single_mulVec, one_mul]
      rfl
    rw [h2] at h1
    have h3 : (Pi.single i (1 : E) : Fin m → E) = (v j)⁻¹ • Pi.single i (v j) := by
      funext l
      by_cases hl : l = i
      · subst hl; simp [hj]
      · simp [hl]
    rw [h3]
    exact N₀.smul_mem _ h1
  rw [eq_top_iff]
  intro y _
  have : y = ∑ i, y i • (Pi.single i 1 : Fin m → E) := by
    funext l; simp [Finset.sum_apply, Pi.single_apply]
  rw [this]
  exact N₀.sum_mem fun i _ => N₀.smul_mem _ (hbasis i)


omit [Fact ρ.IsIrreducible] [Finite W] in
theorem natCard_endRing :
    Nat.card (EndRing ρ) =
      Nat.card {φ : Module.End k₀ W // ∀ g v, φ (ρ g v) = ρ g (φ v)} := by
  let f : EndRing ρ → {φ : Module.End k₀ W // ∀ g v, φ (ρ g v) = ρ g (φ v)} := fun ψ =>
    ⟨ψ.restrictScalars k₀, fun g v => by
      have := ψ.map_smul (⟨ρ g, Algebra.subset_adjoin ⟨g, rfl⟩⟩ : spanAlg ρ) v
      exact this⟩
  have hf : Function.Bijective f := by
    constructor
    · intro ψ ψ' h
      apply LinearMap.ext
      intro w
      exact congrArg (fun φ : {φ : Module.End k₀ W // ∀ g v, φ (ρ g v) = ρ g (φ v)} => φ.1 w) h
    · rintro ⟨φ, hφ⟩
      obtain ⟨ψ, hψ⟩ := (mem_endRing_iff ρ φ).mpr hφ
      refine ⟨ψ, Subtype.ext (LinearMap.ext fun w => ?_)⟩
      exact congrFun hψ w
  exact Nat.card_congr (Equiv.ofBijective f hf)

theorem natCard_eq_pow_finrank :
    Nat.card W = Nat.card (EndRing ρ) ^ Module.finrank (EndRing ρ) W := by
  have : Module.Finite (EndRing ρ) W := Module.Finite.of_finite
  exact Module.natCard_eq_pow_finrank

end Density

end CFSG.QuasithinUnique.Setup.SL2Modules
