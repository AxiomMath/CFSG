module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7bTwist

public section

namespace CFSG.QuasithinUnique.Setup.X7b

open scoped MonoidAlgebra
open CFSG.Semidihedral.Principal Representation

section FixedCodim

variable (k : Type) [Field k] {R : Type} [Ring R] [Algebra k R]
  {M : Type} [AddCommGroup M] [Module k M] [Module R M] [IsScalarTower k R M]

@[expose] def fixedSpace (S : Set R) : Submodule k M where
  carrier := {m | ∀ r ∈ S, r • m = m}
  add_mem' := fun {a b} ha hb r hr => by rw [smul_add, ha r hr, hb r hr]
  zero_mem' := fun r _ => by simp
  smul_mem' := fun c m hm r hr => by
    rw [smul_comm, hm r hr]

@[expose] noncomputable def fixedCodim (S : Set R) (M : Type) [AddCommGroup M] [Module k M]
    [Module R M] [IsScalarTower k R M] : ℕ :=
  Module.finrank k M - Module.finrank k (fixedSpace k S : Submodule k M)

theorem mem_fixedSpace {S : Set R} {m : M} :
    m ∈ (fixedSpace k S : Submodule k M) ↔ ∀ r ∈ S, r • m = m :=
  Iff.rfl

theorem finrank_fixedSpace_le [Module.Finite k M] (S : Set R) (N : Submodule R M) :
    Module.finrank k (fixedSpace k S : Submodule k M) ≤
      Module.finrank k (fixedSpace k S : Submodule k N) +
        Module.finrank k (fixedSpace k S : Submodule k (M ⧸ N)) := by
  have : Module.Finite k (M ⧸ N) :=
    Module.Finite.of_surjective (N.mkQ.restrictScalars k) N.mkQ_surjective
  have : Module.Finite k N :=
    Module.Finite.of_injective (N.subtype.restrictScalars k) N.injective_subtype
  have hres : ∀ m ∈ (fixedSpace k S : Submodule k M),
      (N.mkQ.restrictScalars k) m ∈ (fixedSpace k S : Submodule k (M ⧸ N)) := by
    intro m hm r hr
    show r • N.mkQ m = N.mkQ m
    rw [← map_smul, hm r hr]
  let L := (N.mkQ.restrictScalars k).restrict hres
  have hi : ∀ n ∈ (fixedSpace k S : Submodule k N), (N.subtype.restrictScalars k) n ∈
      (fixedSpace k S : Submodule k M) := by
    intro n hn r hr
    show r • (n : M) = (n : M)
    rw [← Submodule.coe_smul, hn r hr]
  let i := (N.subtype.restrictScalars k).restrict hi
  have hinj : Function.Injective i := by
    intro a b hab
    exact Subtype.ext (Subtype.ext
      (congrArg (fun x : (fixedSpace k S : Submodule k M) => (x : M)) hab))
  have hrange : LinearMap.range i = LinearMap.ker L := by
    ext ⟨m, hm⟩
    simp only [LinearMap.mem_range, LinearMap.mem_ker]
    constructor
    · rintro ⟨⟨n, hn⟩, h⟩
      apply Subtype.ext
      have : (n : M) = m :=
        congrArg (fun x : (fixedSpace k S : Submodule k M) => (x : M)) h
      show N.mkQ m = 0
      rw [← this]
      exact (Submodule.Quotient.mk_eq_zero N).mpr n.2
    · intro h
      have h0 : N.mkQ m = 0 := congrArg Subtype.val h
      have hmN : m ∈ N := (Submodule.Quotient.mk_eq_zero N).mp h0
      refine ⟨⟨⟨m, hmN⟩, fun r hr => ?_⟩, rfl⟩
      apply Subtype.ext
      exact hm r hr
  have h1 := LinearMap.finrank_range_add_finrank_ker L
  have h2 : Module.finrank k (LinearMap.range i) =
      Module.finrank k (fixedSpace k S : Submodule k N) :=
    LinearMap.finrank_range_of_inj hinj
  have h3 : Module.finrank k (LinearMap.range L) ≤
      Module.finrank k (fixedSpace k S : Submodule k (M ⧸ N)) := Submodule.finrank_le _
  rw [hrange] at h2
  omega

theorem finrank_eq_add_quotient [Module.Finite k M] (N : Submodule R M) :
    Module.finrank k M = Module.finrank k N + Module.finrank k (M ⧸ N) := by
  have h1 := Submodule.finrank_quotient_add_finrank (N.restrictScalars k)
  have h2 : Module.finrank k (M ⧸ N.restrictScalars k) = Module.finrank k (M ⧸ N) :=
    (Submodule.Quotient.restrictScalarsEquiv k N).finrank_eq
  have h3 : Module.finrank k (N.restrictScalars k) = Module.finrank k N := rfl
  omega

theorem fixedCodim_sub_quot [Module.Finite k M] (S : Set R) (N : Submodule R M) :
    fixedCodim k S N + fixedCodim k S (M ⧸ N) ≤ fixedCodim k S M := by
  have : Module.Finite k (M ⧸ N) :=
    Module.Finite.of_surjective (N.mkQ.restrictScalars k) N.mkQ_surjective
  have : Module.Finite k N :=
    Module.Finite.of_injective (N.subtype.restrictScalars k) N.injective_subtype
  unfold fixedCodim
  have h1 := finrank_fixedSpace_le k S N
  have h2 := finrank_eq_add_quotient k N
  have h3 : Module.finrank k (fixedSpace k S : Submodule k N) ≤ Module.finrank k N :=
    Submodule.finrank_le _
  have h4 : Module.finrank k (fixedSpace k S : Submodule k (M ⧸ N)) ≤
      Module.finrank k (M ⧸ N) := Submodule.finrank_le _
  omega

theorem fixedCodim_congr {M' : Type} [AddCommGroup M'] [Module k M'] [Module R M']
    [IsScalarTower k R M'] (S : Set R) (e : M ≃ₗ[R] M') :
    fixedCodim k S M = fixedCodim k S M' := by
  unfold fixedCodim
  have hmap : (fixedSpace k S : Submodule k M).map (e.restrictScalars k).toLinearMap =
      (fixedSpace k S : Submodule k M') := by
    ext m'
    simp only [Submodule.mem_map, mem_fixedSpace]
    constructor
    · rintro ⟨m, hm, rfl⟩ r hr
      show r • e m = e m
      rw [← map_smul, hm r hr]
    · intro hm'
      refine ⟨e.symm m', fun r hr => ?_, by simp⟩
      apply e.injective
      rw [map_smul, LinearEquiv.apply_symm_apply, hm' r hr]
  have e1 : Module.finrank k M = Module.finrank k M' := (e.restrictScalars k).finrank_eq
  have e2 : Module.finrank k (fixedSpace k S : Submodule k M) =
      Module.finrank k (fixedSpace k S : Submodule k M') :=
    LinearEquiv.finrank_eq (LinearEquiv.ofSubmodules (e.restrictScalars k) _ _ hmap)
  rw [e1, e2]

theorem fin_telescope_le {n : ℕ} (f : Fin (n + 1) → ℕ) (a : Fin n → ℕ)
    (h : ∀ i : Fin n, f i.castSucc + a i ≤ f i.succ) : f 0 + ∑ i, a i ≤ f (Fin.last n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    show f 0 + ∑ i : Fin (n + 1), a i ≤ f (Fin.last (n + 1))
    have h' := ih (fun i => f i.castSucc) (fun i => a i.castSucc) fun i => by
      have := h i.castSucc
      rw [Fin.succ_castSucc] at this
      exact this
    rw [Fin.castSucc_zero] at h'
    rw [Fin.sum_univ_castSucc, ← add_assoc]
    have := h (Fin.last n)
    rw [Fin.succ_last] at this
    have this' : f (Fin.last n).castSucc + a (Fin.last n) ≤ f (Fin.last (n + 1)) := this
    omega

theorem sum_fixedCodim_factor_le [Module.Finite k M] (S : Set R)
    (s : CompositionSeries (Submodule R M)) (h₁ : s.head = ⊥) (h₂ : s.last = ⊤) :
    ∑ i : Fin s.length,
      fixedCodim k S (↥(s i.succ) ⧸ (s i.castSucc).comap (s i.succ).subtype) ≤
        fixedCodim k S M := by
  let c : Fin (s.length + 1) → ℕ := fun j => fixedCodim k S ↥(s j)
  have hstep : ∀ i : Fin s.length, c i.castSucc +
      fixedCodim k S (↥(s i.succ) ⧸ (s i.castSucc).comap (s i.succ).subtype) ≤ c i.succ := by
    intro i
    have hle : s i.castSucc ≤ s i.succ := (s.lt_succ i).le
    have : Module.Finite k (s i.succ) :=
      Module.Finite.of_injective ((s i.succ).subtype.restrictScalars k)
        (s i.succ).injective_subtype
    have h1 := fixedCodim_sub_quot k S ((s i.castSucc).comap (s i.succ).subtype)
    have h2 : fixedCodim k S ↥((s i.castSucc).comap (s i.succ).subtype) = c i.castSucc :=
      fixedCodim_congr k S (Submodule.comapSubtypeEquivOfLe hle)
    rw [h2] at h1
    exact h1
  have h := fin_telescope_le c _ hstep
  have h0 : c 0 = 0 := by
    have hb : s 0 = ⊥ := h₁
    have : Subsingleton ↥(s 0) := by rw [hb]; infer_instance
    show fixedCodim k S ↥(s 0) = 0
    unfold fixedCodim
    simp [Module.finrank_zero_of_subsingleton]
  have hl : c (Fin.last s.length) = fixedCodim k S M := by
    have ht : s (Fin.last s.length) = ⊤ := h₂
    have key : ∀ T : Submodule R M, T = ⊤ → fixedCodim k S ↥T = fixedCodim k S M := by
      rintro T rfl
      exact fixedCodim_congr k S Submodule.topEquiv
    exact key _ ht
  omega

end FixedCodim

section RepLevel

variable {k G : Type} [Field k] [Group G] {V : Type} [AddCommGroup V] [Module k V]

@[expose] def repFixedSpace (ρ : Representation k G V) (A : Set G) : Submodule k V where
  carrier := {v | ∀ a ∈ A, ρ a v = v}
  add_mem' := fun {x y} hx hy a ha => by rw [map_add, hx a ha, hy a ha]
  zero_mem' := fun a _ => map_zero _
  smul_mem' := fun c v hv a ha => by rw [map_smul, hv a ha]

theorem mem_repFixedSpace {ρ : Representation k G V} {A : Set G} {v : V} :
    v ∈ repFixedSpace ρ A ↔ ∀ a ∈ A, ρ a v = v :=
  Iff.rfl

theorem fixedCodim_asModule [Module.Finite k V] (ρ : Representation k G V) (A : Set G) :
    fixedCodim k ((MonoidAlgebra.of k G) '' A) ρ.asModule =
      Module.finrank k V - Module.finrank k (repFixedSpace ρ A) := by
  unfold fixedCodim
  have hmap : (fixedSpace k ((MonoidAlgebra.of k G) '' A) :
      Submodule k ρ.asModule).map ρ.asModuleEquiv.toLinearMap = repFixedSpace ρ A := by
    ext v
    simp only [Submodule.mem_map, mem_fixedSpace, Set.forall_mem_image, mem_repFixedSpace]
    constructor
    · rintro ⟨m, hm, rfl⟩ a ha
      have h2 := congrArg ρ.asModuleEquiv (hm ha)
      rw [Representation.asModuleEquiv_map_smul, Representation.asAlgebraHom_of] at h2
      exact h2
    · intro hv
      refine ⟨ρ.asModuleEquiv.symm v, fun a ha => ?_, by simp⟩
      rw [← Representation.asModuleEquiv_symm_map_rho, hv a ha]
  have e1 : Module.finrank k ρ.asModule = Module.finrank k V := ρ.asModuleEquiv.finrank_eq
  have e2 : Module.finrank k (fixedSpace k ((MonoidAlgebra.of k G) '' A) :
      Submodule k ρ.asModule) = Module.finrank k (repFixedSpace ρ A) :=
    LinearEquiv.finrank_eq (LinearEquiv.ofSubmodules ρ.asModuleEquiv _ _ hmap)
  rw [e1, e2]

variable {ι : Type} [Fintype ι] [DecidableEq ι]

@[expose] noncomputable def toMatRep (ρ : Representation k G V) (b : Module.Basis ι k V) :
    G →* Matrix ι ι k where
  toFun g := LinearMap.toMatrix b b (ρ g)
  map_one' := by simp
  map_mul' g h := by simp [LinearMap.toMatrix_mul]

@[expose] noncomputable def matRepEquiv (ρ : Representation k G V) (b : Module.Basis ι k V) :
    Representation.Equiv ρ (CFSG.QuasithinUnique.Setup.X7.matRep (toMatRep ρ b)) :=
  Representation.Equiv.mk b.equivFun (fun g => by
    refine LinearMap.ext fun v => ?_
    show b.equivFun (ρ g v) = (LinearMap.toMatrix b b (ρ g)).mulVec (b.equivFun v)
    ext i
    have := congrFun (LinearMap.toMatrix_mulVec_repr b b (ρ g) v) i
    simpa using this.symm)

end RepLevel

section Main

open CFSG.QuasithinUnique.Setup.X7 (matRep matMap MatIso)

theorem finite_module_composition_multisets_and_fixed_codimension
    {k G : Type} [Field k] [Group G] {V : Type} [AddCommGroup V] [Module k V] [Module.Finite k V]
    (ρ : Representation k G V) :
    (∃ s : CompositionSeries (Submodule k[G] ρ.asModule), s.head = ⊥ ∧ s.last = ⊤) ∧
    (∀ s₁ s₂ : CompositionSeries (Submodule k[G] ρ.asModule), s₁.head = ⊥ → s₁.last = ⊤ →
      s₂.head = ⊥ → s₂.last = ⊤ → s₁.Equivalent s₂) ∧
    (∀ s : CompositionSeries (Submodule k[G] ρ.asModule), s.head = ⊥ → s.last = ⊤ →
      ∀ {E : Type} [AddCommGroup E] [Module k E] (σ : Representation k G E),
        repMultiplicity ρ σ = factorCount k[G] s σ.asModule) ∧
    (∀ (W : Subrepresentation ρ) {E : Type} [AddCommGroup E] [Module k E]
      (σ : Representation k G E),
      repMultiplicity ρ σ = repMultiplicity W.toRepresentation σ + repMultiplicity W.quotient σ) ∧
    (∀ (A : Set G) (s : CompositionSeries (Submodule k[G] ρ.asModule)), s.head = ⊥ →
      s.last = ⊤ → ∑ i : Fin s.length, fixedCodim k ((MonoidAlgebra.of k G) '' A)
          (↥(s i.succ) ⧸ (s i.castSucc).comap (s i.succ).subtype) ≤
        Module.finrank k V - Module.finrank k (repFixedSpace ρ A)) ∧
    (∀ (α : G ≃* G) {E : Type} [AddCommGroup E] [Module k E] (σ : Representation k G E),
      repMultiplicity (ρ.comp α.toMonoidHom) (σ.comp α.toMonoidHom) = repMultiplicity ρ σ) ∧
    (∀ {k' : Type} [Field k'] (τ : k ≃+* k') {ι κ E : Type} [Fintype ι] [DecidableEq ι]
      [Fintype κ] [DecidableEq κ] [AddCommGroup E] [Module k E] (b : Module.Basis ι k V)
      (c : Module.Basis κ k E) (σ : Representation k G E),
      repMultiplicity (matRep (matMap (τ : k →+* k') (toMatRep ρ b)))
        (matRep (matMap (τ : k →+* k') (toMatRep σ c))) = repMultiplicity ρ σ) ∧
    (∀ {k' : Type} [Field k'] (τ : k ≃+* k') {ι ι' : Type} [Fintype ι] [DecidableEq ι]
      [Fintype ι'] [DecidableEq ι'] (b : Module.Basis ι k V) (b' : Module.Basis ι' k V),
      Nonempty (Representation.Equiv (matRep (matMap (τ : k →+* k') (toMatRep ρ b)))
        (matRep (matMap (τ : k →+* k') (toMatRep ρ b'))))) := by
  have hN : IsNoetherian k[G] ρ.asModule := isNoetherian_of_finiteDimensional k
  have hA : IsArtinian k[G] ρ.asModule := isArtinian_of_finiteDimensional k
  refine ⟨exists_compositionSeries_of_isNoetherian_isArtinian k[G] ρ.asModule,
    fun s₁ s₂ h1 h2 h3 h4 => CompositionSeries.jordan_holder s₁ s₂ (h1.trans h3.symm)
      (h2.trans h4.symm),
    fun s h1 h2 {E} _ _ σ => compositionMultiplicity_eq_factorCount s h1 h2 σ.asModule,
    fun W {E} _ _ σ => repMultiplicity_sub_quot ρ W σ,
    fun A s h1 h2 => ?_,
    fun α {E} _ _ σ => repMultiplicity_comp_surjective α.toMonoidHom α.surjective ρ σ,
    fun {k'} _ τ {ι κ E} _ _ _ _ _ _ b c σ => ?_,
    fun {k'} _ τ {ι ι'} _ _ _ _ b b' => ?_⟩
  · rw [← fixedCodim_asModule ρ A]
    exact sum_fixedCodim_factor_le k _ s h1 h2
  · calc repMultiplicity (matRep (matMap (τ : k →+* k') (toMatRep ρ b)))
          (matRep (matMap (τ : k →+* k') (toMatRep σ c)))
        = repMultiplicity (matRep (toMatRep ρ b)) (matRep (toMatRep σ c)) :=
          repMultiplicity_matMap τ _ _
      _ = repMultiplicity ρ (matRep (toMatRep σ c)) :=
          (repMultiplicity_congr_left (matRepEquiv ρ b) _).symm
      _ = repMultiplicity ρ σ := (repMultiplicity_congr_right ρ (matRepEquiv σ c)).symm
  · obtain ⟨P, Q, h⟩ := MatIso.exists_of_equiv ((matRepEquiv ρ b).symm.trans (matRepEquiv ρ b'))
    exact (h.map (τ : k →+* k')).equiv

end Main

section Family

open scoped Classical

variable {k G : Type} [Field k] [Group G]

theorem sum_repMultiplicity_mul_fixedCodim_le {V : Type} [AddCommGroup V] [Module k V]
    [Module.Finite k V] (ρ : Representation k G V) (A : Set G) {ι : Type} [Fintype ι]
    (E : ι → Type) [∀ t, AddCommGroup (E t)] [∀ t, Module k (E t)] [∀ t, Module.Finite k (E t)]
    (S : ∀ t, Representation k G (E t)) (hne : ∀ t t', Nonempty ((S t).Equiv (S t')) → t = t') :
    ∑ t, repMultiplicity ρ (S t) *
        (Module.finrank k (E t) - Module.finrank k (repFixedSpace (S t) A)) ≤
      Module.finrank k V - Module.finrank k (repFixedSpace ρ A) := by
  have hN : IsNoetherian k[G] ρ.asModule := isNoetherian_of_finiteDimensional k
  have hA : IsArtinian k[G] ρ.asModule := isArtinian_of_finiteDimensional k
  obtain ⟨s, hs1, hs2⟩ := exists_compositionSeries_of_isNoetherian_isArtinian k[G] ρ.asModule
  have hser := sum_fixedCodim_factor_le k ((MonoidAlgebra.of k G) '' A) s hs1 hs2
  rw [fixedCodim_asModule ρ A] at hser
  refine le_trans ?_ hser
  have hc : ∀ t, fixedCodim k ((MonoidAlgebra.of k G) '' A) (S t).asModule =
      Module.finrank k (E t) - Module.finrank k (repFixedSpace (S t) A) :=
    fun t => fixedCodim_asModule (S t) A
  simp only [repMultiplicity]
  simp only [compositionMultiplicity_eq_factorCount s hs1 hs2, factorCount]
  simp only [Finset.card_filter, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_le_sum fun i _ => ?_
  have hiso : ∀ t t', SubquotientIso k[G] (S t).asModule (s i.castSucc, s i.succ) →
      SubquotientIso k[G] (S t').asModule (s i.castSucc, s i.succ) → t = t' := by
    rintro t t' ⟨e⟩ ⟨e'⟩
    exact hne t t' ⟨equivOfAsModuleEquiv (e.symm.trans e')⟩
  by_cases hex : ∃ t, SubquotientIso k[G] (S t).asModule (s i.castSucc, s i.succ)
  · obtain ⟨t₀, ht₀⟩ := hex
    obtain ⟨e₀⟩ := ht₀
    have hcod : fixedCodim k ((MonoidAlgebra.of k G) '' A)
        (↥(s i.succ) ⧸ (s i.castSucc).comap (s i.succ).subtype) =
        fixedCodim k ((MonoidAlgebra.of k G) '' A) (S t₀).asModule :=
      fixedCodim_congr k _ e₀
    rw [hcod, hc t₀]
    refine le_of_eq ?_
    rw [Finset.sum_eq_single t₀]
    · simp [show SubquotientIso k[G] (S t₀).asModule (s i.castSucc, s i.succ) from ⟨e₀⟩]
    · intro t _ ht
      by_cases h : SubquotientIso k[G] (S t).asModule (s i.castSucc, s i.succ)
      · exact absurd (hiso t t₀ h ⟨e₀⟩) ht
      · simp [h]
    · intro h
      exact absurd (Finset.mem_univ t₀) h
  · refine le_trans (le_of_eq ?_) (Nat.zero_le _)
    refine Finset.sum_eq_zero fun t _ => ?_
    have h : ¬ SubquotientIso k[G] (S t).asModule (s i.castSucc, s i.succ) :=
      fun h => hex ⟨t, h⟩
    simp [h]

end Family

end CFSG.QuasithinUnique.Setup.X7b
