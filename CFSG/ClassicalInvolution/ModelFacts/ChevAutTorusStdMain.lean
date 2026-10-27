module

public import CFSG.ClassicalInvolution.ModelFacts.ChevAutTorusMain
public import CFSG.ClassicalInvolution.ModelFacts.ChevAutTorusStdTheta
public import CFSG.ClassicalInvolution.ModelFacts.ChevAutTorusStdDiag

public section

namespace CFSG.ClassicalInvolution.ModelFacts.ChevAut

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Universal
  CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Minuscule CFSG.LieType.RootSystem
  CFSG.ClassicalInvolution.ModelFacts

section Chain

variable {r : ℕ} {A : Matrix (Fin r) (Fin r) ℤ}

@[expose] def reflFun (A : Matrix (Fin r) (Fin r) ℤ) (i : Fin r) (v : Fin r → ℤ) : Fin r → ℤ :=
  fun l => v l - (∑ j, A i j * v j) * (if l = i then 1 else 0)

theorem reflection_eq_reflFun (A : Matrix (Fin r) (Fin r) ℤ) (i : Fin r) (v : Fin r → ℤ) :
    reflection A i v = reflFun A i v := by
  funext l
  simp [reflection_apply, reflFun, Pi.single_apply]

theorem mem_roots_of_chain (hA : TauCeti.IsFiniteType A) (L : List (Fin r)) :
    ∀ γ : Fin r → ℤ, L.foldl (fun v i => reflFun A i v) γ ∈ roots hA ∅ → γ ∈ roots hA ∅ := by
  induction L with
  | nil => exact fun γ h => h
  | cons i L ih =>
    intro γ h
    have h1 := ih _ h
    have h2 : reflection A i (reflFun A i γ) ∈ roots hA ∅ := by
      have := weylAction_mem_roots hA
        ((coxeterMatrix hA).toCoxeterSystem.simple i) h1
      rwa [weylAction_simple] at this
    have h3 : reflection A i (reflFun A i γ) = γ := by
      rw [← reflection_eq_reflFun]
      have := congrArg (fun f : Module.End ℤ (Fin r → ℤ) => f γ)
        (reflection_mul_self (hA.apply_self i))
      simpa using this
    rwa [h3] at h2

end Chain

section Highest

@[expose] def θE6 : Fin 6 → ℤ := ![1, 2, 2, 3, 2, 1]
@[expose] def θE7 : Fin 7 → ℤ := ![2, 2, 3, 4, 3, 2, 1]
@[expose] def θE8 : Fin 8 → ℤ := ![2, 3, 4, 6, 5, 4, 3, 2]

theorem θE6_pair : ∀ j : Fin 6, pair (Tag.cartan .E6) θE6 j = if j = 1 then 1 else 0 := by
  intro j
  fin_cases j <;> decide

theorem θE7_pair : ∀ j : Fin 7, pair (Tag.cartan .E7) θE7 j = if j = 0 then 1 else 0 := by
  intro j
  fin_cases j <;> decide

theorem θE8_pair : ∀ j : Fin 8, pair (Tag.cartan .E8) θE8 j = if j = 7 then 1 else 0 := by
  intro j
  fin_cases j <;> decide

theorem θE6_chain : ([1, 3, 2, 0, 4, 3, 1, 2, 3, 4] : List (Fin 6)).foldl
    (fun v i => reflFun (Tag.cartan .E6) i v) θE6 = (Pi.single 5 1 : Fin 6 → ℤ) := by
  funext j
  fin_cases j <;> decide

theorem θE7_chain : ([0, 2, 3, 1, 4, 3, 2, 0, 5, 4, 3, 1, 2, 3, 4, 5] : List (Fin 7)).foldl
    (fun v i => reflFun (Tag.cartan .E7) i v) θE7 = (Pi.single 6 1 : Fin 7 → ℤ) := by
  funext j
  fin_cases j <;> decide

theorem θE8_chain : ([7, 6, 5, 4, 3, 1, 2, 0, 3, 2, 4, 3, 1, 5, 4, 3, 2, 0, 6, 5, 4, 3, 1, 2, 3, 4,
    5, 6] : List (Fin 8)).foldl (fun v i => reflFun (Tag.cartan .E8) i v) θE8 =
    (Pi.single 7 1 : Fin 8 → ℤ) := by
  funext j
  fin_cases j <;> decide

end Highest


section Toral

variable {K : Type} [Group K] {D : UniversalRootDatum K} {F : Type} [Field F]
  {x : (Fin D.rank → ℤ) → F → K} {n : Fin D.rank → K} {H : Fin D.rank → Subgroup K}

@[expose] def LiftsToNormalFormStd (D : UniversalRootDatum K) (x : (Fin D.rank → ℤ) → F → K)
    (ν : Fin D.rank) : Prop :=
  ∀ {X : Type} [Group X] (f : K →* X), Function.Surjective f → f.ker ≤ Subgroup.center K →
    ∀ σ : X ≃* X, ∃ (α : K ≃* K) (g : K) (a : Fin D.rank → Fˣ) (φ : F ≃+* F)
      (π : Equiv.Perm (Fin D.rank)), (∀ y, f (α y) = σ (f y)) ∧
      NormalForm x α.toMonoidHom g a φ π ∧ (∀ j l, D.cartan (π j) (π l) = D.cartan j l) ∧
      π ν = ν

theorem exists_diag_of_central_quotient_std [Finite F] {p : ℕ} [Fact p.Prime] [CharP F p]
    (hS : TorusSetup D x n H) (ν : Fin D.rank) (hlift : LiftsToNormalFormStd D x ν)
    (hp2 : p ≠ 2) (hq : 5 ≤ Nat.card F) (hr : 0 < D.rank)
    (hlong : ∀ k, IsLongest D.isFiniteType ∅ (Pi.single k 1))
    (hnb : ∀ k, ∃ j, j ≠ ν ∧ D.cartan j k = -1)
    (hAij : ∀ i j, i ≠ j → D.cartan i j = 0 ∨ D.cartan i j = -1)
    (θ : Fin D.rank → ℤ) (hθr : θ ∈ D.roots) (hθ1 : ∀ j, pair D.cartan θ j = if j = ν then 1 else 0)
    (hθ2 : θ ν = 2) {X : Type} [Group X] (f : K →* X) (hf : Function.Surjective f)
    (hker : f.ker ≤ Subgroup.center K) (σ : X ≃* X)
    (H2 : ∀ j, j ≠ ν → ∀ s, σ (f (torusGen x j s)) = f (torusGen x j s))
    (H1 : ∀ y ∈ D.rootGroup θ ⊔ D.rootGroup (-θ), σ (f y) = f y) :
    ∃ (α : K ≃* K) (b : Fin D.rank → Fˣ), (∀ y, f (α y) = σ (f y)) ∧
      ∀ γ ∈ D.roots, ∀ c, α (x γ c) = x γ ((diagChar b γ : F) * c) := by
  obtain ⟨α, g, a, φ, π, hαθ, hN, hπ, hπν⟩ := hlift f hf hker σ
  have hZ2 : ∀ j, j ≠ ν → ∀ s, torusGen x j s ∈ Zfix α.toMonoidHom := fun j hj s =>
    mem_Zfix.2 (mul_inv_mem_center_of_fix f hker σ α.toMonoidHom hαθ (H2 j hj s))
  have hZ1 : ∀ y ∈ D.rootGroup θ ⊔ D.rootGroup (-θ), y ∈ Zfix α.toMonoidHom := fun y hy =>
    mem_Zfix.2 (mul_inv_mem_center_of_fix f hker σ α.toMonoidHom hαθ (H1 y hy))
  have hfix : ∀ i s, α.toMonoidHom (torusGen x i (s ^ (if i = ν then 2 else 1))) *
      (torusGen x i (s ^ (if i = ν then 2 else 1)))⁻¹ ∈ Subgroup.center K := by
    intro i s
    by_cases hi : i = ν
    · subst hi
      simpa using mem_Zfix.1 (torusGen_sq_mem_Zfix hS hlong i θ hθr hθ2 α hZ2 hZ1 s)
    · simpa [hi] using mem_Zfix.1 (hZ2 i hi s)
  obtain ⟨b, hb⟩ := exists_diag_of_fixes_subtorus hS hp2 hq hr hlong ν hnb hAij hπ hπν θ hθ1 hθ2
    (fun i => if i = ν then 2 else 1) (fun j => rfl) hN hfix
  exact ⟨α, b, hαθ, hb⟩

end Toral


section Preserve

variable {K : Type} [Group K] {D : UniversalRootDatum K} {F : Type} [Field F]
  {x : (Fin D.rank → ℤ) → F → K} {n : Fin D.rank → K} {H : Fin D.rank → Subgroup K}

theorem diag_preserves_rankOne (hS : TorusSetup D x n H) {α : K →* K} {b : Fin D.rank → Fˣ}
    (hb : ∀ γ ∈ D.roots, ∀ c, α (x γ c) = x γ ((diagChar b γ : F) * c)) {γ : Fin D.rank → ℤ}
    (hγ : γ ∈ D.roots) :
    ∀ s ∈ D.rootGroup γ ⊔ D.rootGroup (-γ), α s ∈ D.rootGroup γ ⊔ D.rootGroup (-γ) := by
  obtain ⟨C, O, hE⟩ := hS.chev
  have hneg : -γ ∈ D.roots := CFSG.LieType.Steinberg.OfCartan.neg_mem_roots D.isFiniteType hγ
  have hle : (D.rootGroup γ ⊔ D.rootGroup (-γ)) ≤
      (D.rootGroup γ ⊔ D.rootGroup (-γ)).comap α := by
    refine sup_le (fun g hg => ?_) (fun g hg => ?_)
    · obtain ⟨c, rfl⟩ := ((hE.param γ hγ).1 g).1 hg
      exact Subgroup.mem_sup_left (by
        rw [hb γ hγ c]
        exact ((hE.param γ hγ).1 _).2 ⟨_, rfl⟩)
    · obtain ⟨c, rfl⟩ := ((hE.param (-γ) hneg).1 g).1 hg
      exact Subgroup.mem_sup_right (by
        rw [hb (-γ) hneg c]
        exact ((hE.param (-γ) hneg).1 _).2 ⟨_, rfl⟩)
  exact fun s hs => hle hs

end Preserve

section Ambient

variable {K : Type} [Group K] {D : UniversalRootDatum K} {F : Type} [Field F] [Finite F]
  {p : ℕ} [Fact p.Prime] [CharP F p] {x : (Fin D.rank → ℤ) → F → K} {n : Fin D.rank → K}
  {H : Fin D.rank → Subgroup K}

theorem toral_ambient_std (hS : TorusSetup D x n H) (ν : Fin D.rank)
    (hlift : LiftsToNormalFormStd D x ν) (hp2 : p ≠ 2) (hq : 5 ≤ Nat.card F) (hr : 0 < D.rank)
    (hlong : ∀ k, IsLongest D.isFiniteType ∅ (Pi.single k 1))
    (hnb : ∀ k, ∃ j, j ≠ ν ∧ D.cartan j k = -1)
    (hAij : ∀ i j, i ≠ j → D.cartan i j = 0 ∨ D.cartan i j = -1)
    (θ : Fin D.rank → ℤ) (hθr : θ ∈ D.roots) (hθ1 : ∀ j, pair D.cartan θ j = if j = ν then 1 else 0)
    (hθ2 : θ ν = 2) (hC : ∀ N : Subgroup K, N ≤ Subgroup.center K → ¬ p ∣ Nat.card N)
    {Y : Type} [Group Y] (ψ : K →* Y) (hψ : ψ.ker ≤ Subgroup.center K) (σ : Y ≃* Y)
    (hσ2 : ∀ y, σ (σ y) = y) (hσr : ∀ k, σ (ψ k) ∈ ψ.range) (k₀ : K)
    (H2 : ∀ j, j ≠ ν → ∀ s,
      σ (ψ (k₀ * torusGen x j s * k₀⁻¹)) = ψ (k₀ * torusGen x j s * k₀⁻¹))
    (H1 : ∀ y ∈ D.rootGroup θ ⊔ D.rootGroup (-θ),
      σ (ψ (k₀ * y * k₀⁻¹)) = ψ (k₀ * y * k₀⁻¹)) :
    ∃ v : Fin D.rank → ZMod 2, ∀ γ ∈ D.roots,
      (∀ y ∈ ((D.rootGroup γ ⊔ D.rootGroup (-γ)).map (MulAut.conj k₀).toMonoidHom).map ψ,
          σ y ∈ ((D.rootGroup γ ⊔ D.rootGroup (-γ)).map (MulAut.conj k₀).toMonoidHom).map ψ) ∧
      ((∀ y ∈ ((D.rootGroup γ ⊔ D.rootGroup (-γ)).map (MulAut.conj k₀).toMonoidHom).map ψ,
          σ y = y) ↔ ∑ i, (γ i : ZMod 2) * v i = 0) := by
  set θ₁ : K →* Y := ψ.comp (MulAut.conj k₀).toMonoidHom with hθ₁
  have hθ₁ap : ∀ k, θ₁ k = ψ (k₀ * k * k₀⁻¹) := fun k => rfl
  have hrange : ∀ k, ψ k ∈ θ₁.range := fun k => ⟨k₀⁻¹ * k * k₀, by
    rw [hθ₁ap]
    congr 1
    group⟩
  have hσR : ∀ r ∈ θ₁.range, σ r ∈ θ₁.range := by
    rintro r ⟨k, rfl⟩
    obtain ⟨k', hk'⟩ := hσr (k₀ * k * k₀⁻¹)
    rw [hθ₁ap, ← hk']
    exact hrange k'
  let σR : θ₁.range ≃* θ₁.range :=
    { toFun := fun r => ⟨σ r, hσR r r.2⟩
      invFun := fun r => ⟨σ r, hσR r r.2⟩
      left_inv := fun r => Subtype.ext (hσ2 r)
      right_inv := fun r => Subtype.ext (hσ2 r)
      map_mul' := fun a b => Subtype.ext (map_mul σ (a : Y) (b : Y)) }
  have hkerθ : θ₁.rangeRestrict.ker ≤ Subgroup.center K := by
    intro y hy
    have h1 : θ₁ y = 1 := congrArg Subtype.val (MonoidHom.mem_ker.1 hy)
    have hz : k₀ * y * k₀⁻¹ ∈ Subgroup.center K := hψ (MonoidHom.mem_ker.2 (by rwa [hθ₁ap] at h1))
    have hy' : y = k₀ * y * k₀⁻¹ := by
      have := Subgroup.mem_center_iff.1 hz k₀⁻¹
      calc y = k₀⁻¹ * (k₀ * y * k₀⁻¹) * k₀ := by group
        _ = (k₀ * y * k₀⁻¹) * k₀⁻¹ * k₀ := by rw [this]
        _ = k₀ * y * k₀⁻¹ := by group
    rw [hy']
    exact hz
  obtain ⟨α, b, hαθ, hb⟩ := exists_diag_of_central_quotient_std hS ν hlift hp2 hq hr hlong hnb hAij
    θ hθr hθ1 hθ2 θ₁.rangeRestrict θ₁.rangeRestrict_surjective hkerθ σR
    (fun j hj s => Subtype.ext (H2 j hj s)) (fun y hy => Subtype.ext (H1 y hy))
  obtain ⟨v, hv⟩ := fixes_iff_charOf hS hp2 θ₁.rangeRestrict hkerθ (hC _ hkerθ) σR
    (fun r => Subtype.ext (hσ2 r)) α.toMonoidHom hαθ b hb
  refine ⟨v, fun γ hγ => ⟨?_, ?_⟩⟩
  · intro y hy
    obtain ⟨_, ⟨s, hs, rfl⟩, rfl⟩ := hy
    exact ⟨_, ⟨α s, diag_preserves_rankOne hS (α := α.toMonoidHom) hb hγ s hs, rfl⟩,
      congrArg Subtype.val (hαθ s)⟩
  · rw [← hv γ hγ]
    constructor
    · intro h y hy
      obtain ⟨s, hs, rfl⟩ := hy
      exact Subtype.ext (h _ ⟨_, ⟨s, hs, rfl⟩, rfl⟩)
    · intro h y hy
      obtain ⟨_, ⟨s, hs, rfl⟩, rfl⟩ := hy
      exact congrArg Subtype.val (h _ ⟨s, hs, rfl⟩)

end Ambient


section Families

open CFSG.ClassicalInvolution.RouteD (charOf)
open CFSG.ClassicalInvolution.Generic (conjSub)

theorem cartanE6_nb' : ∀ k : Fin 6, ∃ j : Fin 6, j ≠ 1 ∧ Tag.cartan .E6 j k = -1 := by decide
theorem cartanE7_nb' : ∀ k : Fin 7, ∃ j : Fin 7, j ≠ 0 ∧ Tag.cartan .E7 j k = -1 := by decide
theorem cartanE8_nb' : ∀ k : Fin 8, ∃ j : Fin 8, j ≠ 7 ∧ Tag.cartan .E8 j k = -1 := by decide

theorem exactPerm_E6_one (ε : ℕ) (hε : ε < 2) :
    exactPerm Tag.E6 ε (⟨1, by decide⟩ : Fin Tag.E6.rank) = ⟨1, by decide⟩ := by
  interval_cases ε <;> decide

variable (F : Type) [Field F] [Finite F]

theorem liftsToNormalFormStd_E6 {p : ℕ} [Fact p.Prime] [CharP F p] :
    LiftsToNormalFormStd (e6Datum F) (e6Data_valid.xm F) (1 : Fin 6) := by
  intro X _ f hf hker σ
  obtain ⟨α, g, a, φ, ε, hαθ, h⟩ := excAut_E6 (p := p) f hf hker σ
  exact ⟨α, g, a, φ, exactPerm Tag.E6 ε, hαθ, ⟨fun i c => (h i c).1, fun i c => (h i c).2⟩,
    fun j l => cartan_exactPerm_E6 ε ε.isLt j l, exactPerm_E6_one ε ε.isLt⟩

theorem liftsToNormalFormStd_E7 {p : ℕ} [Fact p.Prime] [CharP F p] :
    LiftsToNormalFormStd (e7Datum F) (e7Data_valid.xm F) (0 : Fin 7) := by
  intro X _ f hf hker σ
  obtain ⟨α, g, a, φ, ε, hαθ, h⟩ := excAut_E7 (p := p) f hf hker σ
  exact ⟨α, g, a, φ, exactPerm Tag.E7 ε, hαθ, ⟨fun i c => (h i c).1, fun i c => (h i c).2⟩,
    fun j l => rfl, rfl⟩

theorem liftsToNormalFormStd_E8 {p : ℕ} [Fact p.Prime] [CharP F p] :
    LiftsToNormalFormStd (Adjoint.e8Datum F) (Adjoint.e8Par F) (7 : Fin 8) := by
  intro X _ f hf hker σ
  obtain ⟨α, g, a, φ, ε, hαθ, h⟩ := excAut_E8 (p := p) f hf hker σ
  exact ⟨α, g, a, φ, exactPerm Tag.E8 ε, hαθ, ⟨fun i c => (h i c).1, fun i c => (h i c).2⟩,
    fun j l => rfl, rfl⟩

omit [Finite F] in
theorem θE6_mem_roots : θE6 ∈ (e6Datum F).roots := by
  refine mem_roots_of_chain (e6Datum F).isFiniteType
    ([1, 3, 2, 0, 4, 3, 1, 2, 3, 4] : List (Fin 6)) θE6 ?_
  have h : ([1, 3, 2, 0, 4, 3, 1, 2, 3, 4] : List (Fin 6)).foldl
      (fun v i => reflFun (e6Datum F).cartan i v) θE6 = (Pi.single 5 1 : Fin 6 → ℤ) := θE6_chain
  rw [h]
  exact (RootSystem.ofCartan (e6Datum F).isFiniteType (e6Datum F).divisible).single_mem (5 : Fin 6)

omit [Finite F] in
theorem θE7_mem_roots : θE7 ∈ (e7Datum F).roots := by
  refine mem_roots_of_chain (e7Datum F).isFiniteType
    ([0, 2, 3, 1, 4, 3, 2, 0, 5, 4, 3, 1, 2, 3, 4, 5] : List (Fin 7)) θE7 ?_
  have h : ([0, 2, 3, 1, 4, 3, 2, 0, 5, 4, 3, 1, 2, 3, 4, 5] : List (Fin 7)).foldl
      (fun v i => reflFun (e7Datum F).cartan i v) θE7 = (Pi.single 6 1 : Fin 7 → ℤ) := θE7_chain
  rw [h]
  exact (RootSystem.ofCartan (e7Datum F).isFiniteType (e7Datum F).divisible).single_mem (6 : Fin 7)

omit [Finite F] in
theorem θE8_mem_roots : θE8 ∈ (Adjoint.e8Datum F).roots := by
  refine mem_roots_of_chain (Adjoint.e8Datum F).isFiniteType
    ([7, 6, 5, 4, 3, 1, 2, 0, 3, 2, 4, 3, 1, 5, 4, 3, 2, 0, 6, 5, 4, 3, 1, 2, 3, 4, 5, 6] :
      List (Fin 8)) θE8 ?_
  have h : ([7, 6, 5, 4, 3, 1, 2, 0, 3, 2, 4, 3, 1, 5, 4, 3, 2, 0, 6, 5, 4, 3, 1, 2, 3, 4, 5, 6] :
      List (Fin 8)).foldl (fun v i => reflFun (Adjoint.e8Datum F).cartan i v) θE8 =
      (Pi.single 7 1 : Fin 8 → ℤ) := θE8_chain
  rw [h]
  exact (RootSystem.ofCartan (Adjoint.e8Datum F).isFiniteType
    (Adjoint.e8Datum F).divisible).single_mem (7 : Fin 8)

theorem toral_std_E6 {p : ℕ} [Fact p.Prime] [CharP F p] (hp2 : p ≠ 2) (hq : 5 ≤ Nat.card F)
    {Y : Type} [Group Y] (ψ : ↥(e6Data_valid.minGroup F) →* Y)
    (hψ : ψ.ker ≤ Subgroup.center ↥(e6Data_valid.minGroup F)) (σ : Y ≃* Y)
    (hσ2 : ∀ y, σ (σ y) = y) (hσr : ∀ k, σ (ψ k) ∈ ψ.range) (k₀ : ↥(e6Data_valid.minGroup F))
    (H2 : ∀ j : Fin 6, j ≠ 1 → ∀ h ∈ e6Data_valid.torus F j,
      σ (ψ (k₀ * h * k₀⁻¹)) = ψ (k₀ * h * k₀⁻¹))
    (H1 : ∀ y ∈ (e6Datum F).rootGroup θE6 ⊔ (e6Datum F).rootGroup (-θE6),
      σ (ψ (k₀ * y * k₀⁻¹)) = ψ (k₀ * y * k₀⁻¹)) :
    ∃ v : Fin Tag.E6.rank → ZMod 2, ∀ γ ∈ (e6Datum F).roots,
      (∀ y ∈ (conjSub k₀ ((e6Datum F).rootGroup γ ⊔ (e6Datum F).rootGroup (-γ))).map ψ,
          σ y ∈ (conjSub k₀ ((e6Datum F).rootGroup γ ⊔ (e6Datum F).rootGroup (-γ))).map ψ) ∧
      ((∀ y ∈ (conjSub k₀ ((e6Datum F).rootGroup γ ⊔ (e6Datum F).rootGroup (-γ))).map ψ,
          σ y = y) ↔ charOf v γ = 0) := by
  have hS := torusSetup_E6 F
  have hfin := finite_minGroup e6Data_valid F
  exact toral_ambient_std (p := p) hS (1 : Fin 6) (liftsToNormalFormStd_E6 F) hp2 hq
    (by show 0 < 6; norm_num) (fun k => isLongest_single_E6 rfl _ k) cartanE6_nb'
    cartanE6_offDiag θE6 (θE6_mem_roots F) θE6_pair (by decide) (hC_E6 F) ψ hψ σ hσ2 hσr k₀
    (fun j hj s => H2 j hj _ ((hS.H_iff j _).2 ⟨s, rfl⟩)) H1

theorem toral_std_E7 {p : ℕ} [Fact p.Prime] [CharP F p] (hp2 : p ≠ 2) (hq : 5 ≤ Nat.card F)
    {Y : Type} [Group Y] (ψ : ↥(e7Data_valid.minGroup F) →* Y)
    (hψ : ψ.ker ≤ Subgroup.center ↥(e7Data_valid.minGroup F)) (σ : Y ≃* Y)
    (hσ2 : ∀ y, σ (σ y) = y) (hσr : ∀ k, σ (ψ k) ∈ ψ.range) (k₀ : ↥(e7Data_valid.minGroup F))
    (H2 : ∀ j : Fin 7, j ≠ 0 → ∀ h ∈ e7Data_valid.torus F j,
      σ (ψ (k₀ * h * k₀⁻¹)) = ψ (k₀ * h * k₀⁻¹))
    (H1 : ∀ y ∈ (e7Datum F).rootGroup θE7 ⊔ (e7Datum F).rootGroup (-θE7),
      σ (ψ (k₀ * y * k₀⁻¹)) = ψ (k₀ * y * k₀⁻¹)) :
    ∃ v : Fin Tag.E7.rank → ZMod 2, ∀ γ ∈ (e7Datum F).roots,
      (∀ y ∈ (conjSub k₀ ((e7Datum F).rootGroup γ ⊔ (e7Datum F).rootGroup (-γ))).map ψ,
          σ y ∈ (conjSub k₀ ((e7Datum F).rootGroup γ ⊔ (e7Datum F).rootGroup (-γ))).map ψ) ∧
      ((∀ y ∈ (conjSub k₀ ((e7Datum F).rootGroup γ ⊔ (e7Datum F).rootGroup (-γ))).map ψ,
          σ y = y) ↔ charOf v γ = 0) := by
  have hS := torusSetup_E7 F
  have hfin := finite_minGroup e7Data_valid F
  exact toral_ambient_std (p := p) hS (0 : Fin 7) (liftsToNormalFormStd_E7 F) hp2 hq
    (by show 0 < 7; norm_num) (fun k => isLongest_single_E7 rfl _ k) cartanE7_nb'
    cartanE7_offDiag θE7 (θE7_mem_roots F) θE7_pair (by decide) (hC_E7 F) ψ hψ σ hσ2 hσr k₀
    (fun j hj s => H2 j hj _ ((hS.H_iff j _).2 ⟨s, rfl⟩)) H1

theorem toral_std_E8 {p : ℕ} [Fact p.Prime] [CharP F p] (hp2 : p ≠ 2) (hq : 5 ≤ Nat.card F)
    {Y : Type} [Group Y] (ψ : ↥(adjointGroup Tag.E8 F) →* Y)
    (hψ : ψ.ker ≤ Subgroup.center ↥(adjointGroup Tag.E8 F)) (σ : Y ≃* Y)
    (hσ2 : ∀ y, σ (σ y) = y) (hσr : ∀ k, σ (ψ k) ∈ ψ.range) (k₀ : ↥(adjointGroup Tag.E8 F))
    (H2 : ∀ j : Fin 8, j ≠ 7 → ∀ h ∈ Adjoint.torus (τ := Tag.E8) F j,
      σ (ψ (k₀ * h * k₀⁻¹)) = ψ (k₀ * h * k₀⁻¹))
    (H1 : ∀ y ∈ (Adjoint.e8Datum F).rootGroup θE8 ⊔ (Adjoint.e8Datum F).rootGroup (-θE8),
      σ (ψ (k₀ * y * k₀⁻¹)) = ψ (k₀ * y * k₀⁻¹)) :
    ∃ v : Fin Tag.E8.rank → ZMod 2, ∀ γ ∈ (Adjoint.e8Datum F).roots,
      (∀ y ∈ (conjSub k₀ ((Adjoint.e8Datum F).rootGroup γ ⊔
          (Adjoint.e8Datum F).rootGroup (-γ))).map ψ,
        σ y ∈ (conjSub k₀ ((Adjoint.e8Datum F).rootGroup γ ⊔
          (Adjoint.e8Datum F).rootGroup (-γ))).map ψ) ∧
      ((∀ y ∈ (conjSub k₀ ((Adjoint.e8Datum F).rootGroup γ ⊔
          (Adjoint.e8Datum F).rootGroup (-γ))).map ψ, σ y = y) ↔ charOf v γ = 0) := by
  have hS := torusSetup_E8 F
  exact toral_ambient_std (p := p) hS (7 : Fin 8) (liftsToNormalFormStd_E8 F) hp2 hq
    (by show 0 < 8; norm_num) (fun k => isLongest_single_E8 rfl _ k) cartanE8_nb'
    cartanE8_offDiag θE8 (θE8_mem_roots F) θE8_pair (by decide) (hC_E8 F) ψ hψ σ hσ2 hσr k₀
    (fun j hj s => H2 j hj _ ((hS.H_iff j _).2 ⟨s, rfl⟩)) H1

end Families

end CFSG.ClassicalInvolution.ModelFacts.ChevAut
