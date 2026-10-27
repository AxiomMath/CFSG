module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk111cDDim
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk111cDDesc

public section

namespace CFSG.GH74.GLS.Stage4.Rest

open scoped TensorProduct MonoidAlgebra

section End1

variable {F G : Type} [Field F] [Group G] {M : Type} [AddCommGroup M] [Module F M]
  [Module (MonoidAlgebra F G) M] [IsScalarTower F (MonoidAlgebra F G) M]

theorem finrank_end_eq_one [Nontrivial M]
    (h : ∀ φ : Module.End (MonoidAlgebra F G) M, ∃ c : F, ∀ x, φ x = c • x) :
    Module.finrank F (Module.End (MonoidAlgebra F G) M) = 1 := by
  rw [finrank_eq_one_iff_of_nonzero' (1 : Module.End (MonoidAlgebra F G) M) one_ne_zero]
  intro φ
  obtain ⟨c, hc⟩ := h φ
  exact ⟨c, by ext x; simp [hc]⟩

noncomputable def endConj {M M' : Type} [AddCommMonoid M] [Module F M]
    [Module (MonoidAlgebra F G) M] [IsScalarTower F (MonoidAlgebra F G) M]
    [AddCommMonoid M'] [Module F M'] [Module (MonoidAlgebra F G) M']
    [IsScalarTower F (MonoidAlgebra F G) M'] (e : M ≃ₗ[MonoidAlgebra F G] M') :
    Module.End (MonoidAlgebra F G) M ≃ₗ[F] Module.End (MonoidAlgebra F G) M' where
  toFun φ := e.toLinearMap ∘ₗ φ ∘ₗ e.symm.toLinearMap
  invFun ψ := e.symm.toLinearMap ∘ₗ ψ ∘ₗ e.toLinearMap
  map_add' φ φ' := by ext x; simp
  map_smul' c φ := by
    ext x
    simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply, LinearMap.smul_apply,
      RingHom.id_apply]
    exact e.toLinearMap.map_smul_of_tower c _
  left_inv φ := by ext x; simp
  right_inv ψ := by ext x; simp

end End1

section End2

variable {p n : ℕ} [Fact p.Prime] {F : Type} [Field F] [Finite F] [Algebra (ZMod p) F] [CharP F p]
  {W : Type} [AddCommGroup W] [Module (ZMod p) W] [Module.Finite (ZMod p) W]
  (σ : Representation (ZMod p) (SLm F) W)

omit [CharP F p] [Algebra (ZMod p) F] [Module.Finite (ZMod p) W] [Module (ZMod p) W] [AddCommGroup W] [Fact p.Prime] in
theorem stRep_end_scalar (hS : Mix11cSteinberg) (hp2 : p ≠ 2) (hn : 0 < n) (hF : Nat.card F = p ^ n)
    [Fact p.Prime] {B : ℕ} (hB : B < p ^ n)
    (φ : Module.End (MonoidAlgebra F (SLm F)) (stRep F B).asModule) :
    ∃ c : F, ∀ x, φ x = c • x := by
  have h := ((hS p n Fact.out hp2 hn F hF).1 B hB).2.2.2.1
  let φ' : Module.End (MonoidAlgebra F (SLm F)) (steinbergRep F F B).asModule :=
    (stEquiv F B).symm.toLinearMap ∘ₗ φ ∘ₗ (stEquiv F B).toLinearMap
  obtain ⟨c, hc⟩ := h φ'
  refine ⟨c, fun x => ?_⟩
  have h1 := hc ((stEquiv F B).symm x)
  have h2 : (stEquiv F B).symm (φ x) = c • (stEquiv F B).symm x := by
    simpa [φ'] using h1
  have h3 : (stEquiv F B).symm (φ x) = (stEquiv F B).symm (c • x) := by
    rw [h2]
    exact ((stEquiv F B).symm.toLinearMap.map_smul_of_tower c x).symm
  exact (stEquiv F B).symm.injective h3

omit [Module.Finite (ZMod p) W] in
theorem end_scalar_orbSub (hS : Mix11cSteinberg) (hp2 : p ≠ 2) (hn : 0 < n) (hF : Nat.card F = p ^ n)
    {N : Submodule (MonoidAlgebra F (SLm F)) (repXT σ).asModule} {A : ℕ} (hA : A < p ^ n)
    (ι : ↥N ≃ₗ[MonoidAlgebra F (SLm F)] (stRep F A).asModule) (j : ℕ)
    (φ : Module.End (MonoidAlgebra F (SLm F)) ↥(orbSub σ N j)) :
    ∃ c : F, ∀ x, φ x = c • x := by
  obtain ⟨hlt, ⟨e⟩⟩ := orbSub_label σ hS hp2 hn hF N hA ι j
  let ψ : Module.End (MonoidAlgebra F (SLm F)) (stRep F ((rot p n)^[j] A)).asModule :=
    e.toLinearMap ∘ₗ φ ∘ₗ e.symm.toLinearMap
  obtain ⟨c, hc⟩ := stRep_end_scalar hS hp2 hn hF hlt ψ
  refine ⟨c, fun x => ?_⟩
  have h1 := hc (e x)
  have h2 : e (φ x) = c • e x := by simpa [ψ] using h1
  have h3 : e (φ x) = e (c • x) := by
    rw [h2]
    exact (e.toLinearMap.map_smul_of_tower c x).symm
  exact e.injective h3

theorem isoC_eq_orbSub_of_one (hS : Mix11cSteinberg) (hp2 : p ≠ 2) (hn : 0 < n)
    (hF : Nat.card F = p ^ n)
    {N : Submodule (MonoidAlgebra F (SLm F)) (repXT σ).asModule} {A : ℕ} (hA : A < p ^ n)
    (ι : ↥N ≃ₗ[MonoidAlgebra F (SLm F)] (stRep F A).asModule)
    (hc : Module.finrank F ↥(isoC σ A) = Module.finrank F (stRep F A).asModule) (j : ℕ) :
    isoC σ ((rot p n)^[j] A) = orbSub σ N j := by
  have hle := orbSub_le_isoC σ hS hp2 hn hF hA ι j
  have hfN : Module.finrank F ↥N = Module.finrank F (stRep F A).asModule :=
    (ι.restrictScalars F).finrank_eq
  have hfj : ∀ j, Module.finrank F ↥(orbSub σ N j) = Module.finrank F ↥N := by
    intro j
    induction j with
    | zero => rfl
    | succ j ih => rw [orbSub_succ, finrank_map_phi, ih]
  have hfI := finrank_isoC_orbit σ hS hp2 hn hF hA j
  have hdim : Module.finrank F ↥(orbSub σ N j) = Module.finrank F ↥(isoC σ ((rot p n)^[j] A)) := by
    rw [hfj, hfI, hc, hfN]
  have heq : (orbSub σ N j).restrictScalars F = (isoC σ ((rot p n)^[j] A)).restrictScalars F :=
    Submodule.eq_of_le_of_finrank_eq (Submodule.restrictScalars_mono F hle) hdim
  exact (Submodule.restrictScalars_injective F _ _ heq).symm

omit [Module.Finite (ZMod p) W] in
theorem isSemisimple_of_orbit {N : Submodule (MonoidAlgebra F (SLm F)) (repXT σ).asModule}
    (hsimple : ∀ j, IsSimpleModule (MonoidAlgebra F (SLm F)) ↥(orbSub σ N j))
    (htop : ⨆ j, orbSub σ N j = ⊤) :
    IsSemisimpleModule (MonoidAlgebra F (SLm F)) (repXT σ).asModule := by
  apply IsSemisimpleModule.of_sSup_simples_eq_top
  rw [eq_top_iff, ← htop]
  exact iSup_le fun j => le_sSup (hsimple j)

omit [Module.Finite (ZMod p) W] in
theorem natCard_components (hS : Mix11cSteinberg) (hp2 : p ≠ 2) (hn : 0 < n)
    (hF : Nat.card F = p ^ n)
    {N : Submodule (MonoidAlgebra F (SLm F)) (repXT σ).asModule} {A : ℕ} (hA : A < p ^ n)
    (ι : ↥N ≃ₗ[MonoidAlgebra F (SLm F)] (stRep F A).asModule)
    (hsimple : ∀ j, IsSimpleModule (MonoidAlgebra F (SLm F)) ↥(orbSub σ N j))
    (htop : ⨆ j, orbSub σ N j = ⊤) :
    Nat.card ↥(isotypicComponents (MonoidAlgebra F (SLm F)) (repXT σ).asModule) =
      rotPeriod p n A := by
  classical
  obtain ⟨hcomp, hmem⟩ := isotypic_eq_orbit σ hS hp2 hn hF hA ι hsimple htop
  have hp : 1 < p := Nat.Prime.one_lt Fact.out
  have hr : 0 < rotPeriod p n A := mix11cD_rotPeriod_pos hp hn hA
  let g : Fin (rotPeriod p n A) →
      ↥(isotypicComponents (MonoidAlgebra F (SLm F)) (repXT σ).asModule) :=
    fun j => ⟨isoC σ ((rot p n)^[j.1] A), hmem j.1⟩
  have hginj : Function.Injective g := by
    intro j k hjk
    exact Fin.ext (isoC_orbit_injOn σ hS hp2 hn hF hA ι hsimple j.2 k.2 (congrArg Subtype.val hjk))
  have hgsurj : Function.Surjective g := by
    intro c
    obtain ⟨j, hj⟩ := hcomp c.1 c.2
    refine ⟨⟨j % rotPeriod p n A, Nat.mod_lt _ hr⟩, Subtype.ext ?_⟩
    simp only [g]
    have hj' : (rot p n)^[j % rotPeriod p n A] A = (rot p n)^[j] A :=
      Function.iterate_mod_minimalPeriod_eq
    rw [hj, hj']
  rw [← Nat.card_eq_of_bijective g ⟨hginj, hgsurj⟩]
  simp

omit [Module.Finite (ZMod p) W] in
theorem finrank_end_orbSub (hS : Mix11cSteinberg) (hp2 : p ≠ 2) (hn : 0 < n)
    (hF : Nat.card F = p ^ n)
    {N : Submodule (MonoidAlgebra F (SLm F)) (repXT σ).asModule} {A : ℕ} (hA : A < p ^ n)
    (ι : ↥N ≃ₗ[MonoidAlgebra F (SLm F)] (stRep F A).asModule)
    (hsimple : ∀ j, IsSimpleModule (MonoidAlgebra F (SLm F)) ↥(orbSub σ N j)) (j : ℕ) :
    Module.finrank F (Module.End (MonoidAlgebra F (SLm F)) ↥(orbSub σ N j)) = 1 := by
  have := hsimple j
  have : Nontrivial ↥(orbSub σ N j) :=
    IsSimpleModule.nontrivial (MonoidAlgebra F (SLm F)) ↥(orbSub σ N j)
  exact finrank_end_eq_one (end_scalar_orbSub σ hS hp2 hn hF hA ι j)

theorem finrank_end_X (hS : Mix11cSteinberg) (hp2 : p ≠ 2) (hn : 0 < n) (hF : Nat.card F = p ^ n)
    {N : Submodule (MonoidAlgebra F (SLm F)) (repXT σ).asModule} {A : ℕ} (hA : A < p ^ n)
    (ι : ↥N ≃ₗ[MonoidAlgebra F (SLm F)] (stRep F A).asModule)
    (hsimple : ∀ j, IsSimpleModule (MonoidAlgebra F (SLm F)) ↥(orbSub σ N j))
    (htop : ⨆ j, orbSub σ N j = ⊤)
    (hc : Module.finrank F ↥(isoC σ A) = Module.finrank F (stRep F A).asModule) :
    Module.finrank F (Module.End (MonoidAlgebra F (SLm F)) (repXT σ).asModule) =
      rotPeriod p n A := by
  classical
  have hsemi := isSemisimple_of_orbit σ hsimple htop
  obtain ⟨hcomp, -⟩ := isotypic_eq_orbit σ hS hp2 hn hF hA ι hsimple htop
  have : Finite ↥(isotypicComponents (MonoidAlgebra F (SLm F)) (repXT σ).asModule) :=
    inferInstance
  have := Fintype.ofFinite ↥(isotypicComponents (MonoidAlgebra F (SLm F)) (repXT σ).asModule)
  have hone : ∀ c : ↥(isotypicComponents (MonoidAlgebra F (SLm F)) (repXT σ).asModule),
      Module.finrank F (Module.End (MonoidAlgebra F (SLm F)) ↥c.1) = 1 := by
    intro c
    obtain ⟨j, hj⟩ := hcomp c.1 c.2
    have hj' : c.1 = orbSub σ N j :=
      hj.trans (isoC_eq_orbSub_of_one σ hS hp2 hn hF hA ι hc j)
    rw [hj']
    exact finrank_end_orbSub σ hS hp2 hn hF hA ι hsimple j
  have : ∀ c : ↥(isotypicComponents (MonoidAlgebra F (SLm F)) (repXT σ).asModule),
      Module.Free F (Module.End (MonoidAlgebra F (SLm F)) ↥c.1) := fun c =>
    @Module.Free.of_divisionRing F (Module.End (MonoidAlgebra F (SLm F)) ↥c.1) _
      LinearMap.addCommGroup LinearMap.module
  have : ∀ c : ↥(isotypicComponents (MonoidAlgebra F (SLm F)) (repXT σ).asModule),
      Module.Finite F (Module.End (MonoidAlgebra F (SLm F)) ↥c.1) :=
    fun c => Module.finite_of_finrank_pos (by rw [hone c]; exact one_pos)
  let e := IsSemisimpleModule.endAlgEquiv (R₀ := F) (MonoidAlgebra F (SLm F))
    (repXT σ).asModule
  rw [e.toLinearEquiv.finrank_eq, Module.finrank_pi_fintype]
  simp only [hone, Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one]
  rw [Fintype.card_eq_nat_card]
  exact natCard_components σ hS hp2 hn hF hA ι hsimple htop

theorem natCard_end_of_one (hS : Mix11cSteinberg) (hp2 : p ≠ 2) (hn : 0 < n)
    (hF : Nat.card F = p ^ n)
    {N : Submodule (MonoidAlgebra F (SLm F)) (repXT σ).asModule} {A : ℕ} (hA : A < p ^ n)
    (ι : ↥N ≃ₗ[MonoidAlgebra F (SLm F)] (stRep F A).asModule)
    (hsimple : ∀ j, IsSimpleModule (MonoidAlgebra F (SLm F)) ↥(orbSub σ N j))
    (htop : ⨆ j, orbSub σ N j = ⊤)
    (hc : Module.finrank F ↥(isoC σ A) = Module.finrank F (stRep F A).asModule) :
    Nat.card (Module.End (MonoidAlgebra (ZMod p) (SLm F)) σ.asModule) =
      p ^ rotPeriod p n A := by
  rw [natCard_end_eq_pow_finrank_extendScalars σ]
  congr 1
  have h : Module.finrank F (Module.End (MonoidAlgebra F (SLm F))
        (CFSG.Theory.Representation.extendScalars F σ).asModule) =
      Module.finrank F (Module.End (MonoidAlgebra F (SLm F)) (repXT σ).asModule) :=
    (endConj (xEquiv σ)).finrank_eq
  rw [h]
  exact finrank_end_X σ hS hp2 hn hF hA ι hsimple htop hc

end End2

end CFSG.GH74.GLS.Stage4.Rest
