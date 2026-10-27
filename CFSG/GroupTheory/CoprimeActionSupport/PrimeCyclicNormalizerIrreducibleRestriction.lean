module

public import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
public import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
public import Mathlib.RepresentationTheory.Irreducible
public import Mathlib.RepresentationTheory.Maschke
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleModule.Isotypic
public import Mathlib.RingTheory.SimpleRing.Principal
public import CFSG.GroupTheory.CoprimeActionSupport.OrbitSums

public section

open scoped MonoidAlgebra

namespace CFSG.GroupTheory.CoprimeActionSupport.PrimeCyclicNormalizerIrreducibleRestriction

noncomputable section Abstract

variable {F : Type*} [Field F] {E : Type*} [Group E]
  {M : Type*} [AddCommGroup M] [Module F M] [Module F[E] M] [IsScalarTower F F[E] M]

@[expose] def Norm (E : Type*) [Group E] {M : Type*} [AddCommGroup M] [Module F M] [Module F[E] M]
    (g : M ≃ₗ[F] M) : Prop :=
  ∃ β : MulAut E, ∀ e m, g (MonoidAlgebra.of F E e • m) = MonoidAlgebra.of F E (β e) • g m

theorem Norm.one : Norm (F := F) E (M := M) 1 := ⟨1, fun e m => rfl⟩

theorem Norm.mul {g h : M ≃ₗ[F] M} (hg : Norm (F := F) E g) (hh : Norm (F := F) E h) :
    Norm (F := F) E (g * h) := by
  obtain ⟨β, hβ⟩ := hg
  obtain ⟨γ, hγ⟩ := hh
  refine ⟨β * γ, fun e m => ?_⟩
  rw [LinearEquiv.mul_apply, hγ, hβ]
  rfl

theorem Norm.inv {g : M ≃ₗ[F] M} (hg : Norm (F := F) E g) : Norm (F := F) E g⁻¹ := by
  obtain ⟨β, hβ⟩ := hg
  refine ⟨β⁻¹, fun e m => ?_⟩
  have := hβ (β⁻¹ e) (g⁻¹ m)
  simp at this
  simp [← this]

theorem Norm.pow {g : M ≃ₗ[F] M} (hg : Norm (F := F) E g) (n : ℕ) : Norm (F := F) E (g ^ n) := by
  induction n with
  | zero => simpa using Norm.one
  | succ n ih => rw [pow_succ]; exact Norm.mul ih hg

theorem Norm.smul {g : M ≃ₗ[F] M} (h : Norm (F := F) E g) :
    ∃ τ : F[E] →ₐ[F] F[E], ∀ x m, g (x • m) = τ x • g m := by
  obtain ⟨β, hβ⟩ := h
  refine ⟨(MonoidAlgebra.domCongr F F (β : E ≃* E) : F[E] →ₐ[F] F[E]), ?_⟩
  intro x
  induction x using MonoidAlgebra.induction_on with
  | of e => intro m; simpa using hβ e m
  | add x y hx hy => intro m; simp [add_smul, hx, hy]
  | smul c x hx => intro m; simp [smul_assoc, hx]

theorem Norm.pair {g : M ≃ₗ[F] M} (hg : Norm (F := F) E g) :
    ∃ τ : F[E] →ₐ[F] F[E], (∀ x m, g⁻¹ (x • m) = τ x • g⁻¹ m) ∧ ∀ x n, g (τ x • n) = x • g n := by
  obtain ⟨τ, hτ⟩ := Norm.smul (Norm.inv hg)
  refine ⟨τ, hτ, fun x n => ?_⟩
  have := hτ x (g n)
  simp only [LinearEquiv.coe_inv, LinearEquiv.symm_apply_apply] at this
  exact (by simpa using congrArg g this : x • g n = g (τ x • n)).symm

@[expose] def tw (g : M ≃ₗ[F] M) (hg : Norm (F := F) E g) (S : Submodule F[E] M) : Submodule F[E] M where
  carrier := g '' S
  add_mem' := by
    rintro _ _ ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
    exact ⟨a + b, S.add_mem ha hb, map_add _ _ _⟩
  zero_mem' := ⟨0, S.zero_mem, map_zero _⟩
  smul_mem' := by
    rintro x _ ⟨a, ha, rfl⟩
    obtain ⟨τ, hτ⟩ := Norm.smul (Norm.inv hg)
    refine ⟨τ x • a, S.smul_mem _ ha, ?_⟩
    have := hτ x (g a)
    simp only [LinearEquiv.coe_inv, LinearEquiv.symm_apply_apply] at this
    exact (by simpa using congrArg g this : x • g a = g (τ x • a)).symm

theorem mem_tw {g : M ≃ₗ[F] M} (hg : Norm (F := F) E g) {S : Submodule F[E] M} {m : M} :
    m ∈ tw g hg S ↔ g⁻¹ m ∈ S := by
  constructor
  · rintro ⟨a, ha, rfl⟩
    simpa using ha
  · intro h
    exact ⟨_, h, by simp⟩

theorem tw_le_iff {g : M ≃ₗ[F] M} (hg : Norm (F := F) E g) {S S' : Submodule F[E] M} :
    tw g hg S ≤ tw g hg S' ↔ S ≤ S' := by
  constructor
  · intro h a ha
    have := h ⟨a, ha, rfl⟩
    simpa [mem_tw] using this
  · rintro h m hm
    rw [mem_tw] at hm ⊢
    exact h hm

theorem tw_tw {g h : M ≃ₗ[F] M} (hg : Norm (F := F) E g) (hh : Norm (F := F) E h)
    (hgh : Norm (F := F) E (g * h)) (S : Submodule F[E] M) :
    tw g hg (tw h hh S) = tw (g * h) hgh S := by
  ext m
  simp [mem_tw]

theorem tw_one (h1 : Norm (F := F) E (1 : M ≃ₗ[F] M)) (S : Submodule F[E] M) : tw 1 h1 S = S := by
  ext m
  simp [mem_tw]

theorem tw_bot {g : M ≃ₗ[F] M} (hg : Norm (F := F) E g) : tw g hg ⊥ = ⊥ := by
  ext m
  simp [mem_tw]

theorem tw_tw_inv {g : M ≃ₗ[F] M} (hg : Norm (F := F) E g) (S : Submodule F[E] M) :
    tw g hg (tw g⁻¹ (Norm.inv hg) S) = S := by
  ext m
  simp [mem_tw]

theorem tw_isAtom {g : M ≃ₗ[F] M} (hg : Norm (F := F) E g) {S : Submodule F[E] M}
    (hS : IsAtom S) : IsAtom (tw g hg S) := by
  refine ⟨?_, fun b hb => ?_⟩
  · intro h
    apply hS.1
    have : tw g hg S ≤ tw g hg ⊥ := by rw [tw_bot]; exact h.le
    exact le_bot_iff.1 ((tw_le_iff hg).1 this)
  · have h1 : tw g⁻¹ (Norm.inv hg) b < S := by
      refine lt_of_le_of_ne ?_ ?_
      · have h3 : tw g hg (tw g⁻¹ (Norm.inv hg) b) ≤ tw g hg S := by
          rw [tw_tw_inv]; exact hb.le
        exact (tw_le_iff hg).1 h3
      · intro h
        have := congrArg (tw g hg) h
        rw [tw_tw_inv] at this
        exact hb.ne this
    have := hS.2 _ h1
    have h4 := tw_tw_inv hg b
    rw [this, tw_bot] at h4
    exact h4.symm

@[expose] def twMap {g : M ≃ₗ[F] M} (hg : Norm (F := F) E g) {S S2 : Submodule F[E] M}
    (ψ : S →ₗ[F[E]] S2) : tw g hg S →ₗ[F[E]] tw g hg S2 :=
  let pre : tw g hg S → S := fun y => ⟨g⁻¹ y, (mem_tw hg).1 y.2⟩
  have hadd : ∀ y z, pre (y + z) = pre y + pre z := fun y z => Subtype.ext (by simp [pre])
  have hsmul : ∀ (x : F[E]) y, ∃ τ : F[E] →ₐ[F] F[E], pre (x • y) = τ x • pre y ∧
      ∀ n, g (τ x • n) = x • g n := by
    intro x y
    obtain ⟨τ, hτ⟩ := Norm.smul (Norm.inv hg)
    refine ⟨τ, Subtype.ext (by simp [pre, hτ]), fun n => ?_⟩
    have := hτ x (g n)
    simp only [LinearEquiv.coe_inv, LinearEquiv.symm_apply_apply] at this
    exact (by simpa using congrArg g this : x • g n = g (τ x • n)).symm
  { toFun := fun y => ⟨g (ψ (pre y)), (mem_tw hg).2 (by simp)⟩
    map_add' := fun y z => by
      apply Subtype.ext
      simp [hadd]
    map_smul' := fun x y => by
      apply Subtype.ext
      obtain ⟨τ, hτ, hτ'⟩ := hsmul x y
      simp only [hτ, map_smul, RingHom.id_apply, Submodule.coe_smul_of_tower]
      exact hτ' _ }

@[expose] def twEquiv {g : M ≃ₗ[F] M} (hg : Norm (F := F) E g) {S S2 : Submodule F[E] M}
    (ψ : S ≃ₗ[F[E]] S2) : tw g hg S ≃ₗ[F[E]] tw g hg S2 :=
  LinearEquiv.ofLinear (twMap hg ψ.toLinearMap) (twMap hg ψ.symm.toLinearMap)
    (by ext y; simp [twMap]) (by ext y; simp [twMap])

theorem caseA [IsAlgClosed F] [FiniteDimensional F M] {T : M ≃ₗ[F] M} (hT : Norm (F := F) E T)
    (S : Submodule F[E] M) [IsSimpleModule F[E] S] (ψ : S ≃ₗ[F[E]] tw T hT S)
    (hjoint : ∀ N : Submodule F[E] M, (∀ m ∈ N, T m ∈ N) → N = ⊥ ∨ N = ⊤) :
    IsSimpleModule F[E] M := by
  let ψF : S →ₗ[F] M := ((tw T hT S).subtype.restrictScalars F) ∘ₗ (ψ.toLinearMap.restrictScalars F)
  have hψF : ∀ s, ψF s = (ψ s : M) := fun s => rfl
  let Aₗ : S →ₗ[F] S := LinearMap.codRestrict (S.restrictScalars F) (T.symm.toLinearMap ∘ₗ ψF)
    (fun s => by
      have := (mem_tw hT).1 (ψ s).2
      simpa [hψF] using this)
  have hA : ∀ s, (Aₗ s : M) = T⁻¹ (ψ s) := fun s => rfl
  let Θ : Module.End F (S →ₗ[F] M) :=
    { toFun := fun f => T.toLinearMap ∘ₗ f ∘ₗ Aₗ
      map_add' := fun f g => by ext; simp
      map_smul' := fun c f => by ext; simp }
  let U : Submodule F (S →ₗ[F] M) :=
    { carrier := {f | ∀ (x : F[E]) (s : S), f (x • s) = x • f s}
      add_mem' := fun {f g} hf hg x s => by simp [hf x s, hg x s]
      zero_mem' := fun x s => by simp
      smul_mem' := fun c f hf x s => by simp [hf x s, smul_comm c x] }
  have hU : ∀ f ∈ U, Θ f ∈ U := by
    intro f hf x s
    obtain ⟨τ, hτ1, hτ2⟩ := (Norm.pair hT)
    have e : Aₗ (x • s) = τ x • Aₗ s := by
      apply Subtype.ext
      simp [hA, hτ1]
    show T (f (Aₗ (x • s))) = x • T (f (Aₗ s))
    rw [e, hf, ← hτ2]
  have hι : (S.subtype.restrictScalars F) ∈ U := fun x s => rfl
  have hUnt : Nontrivial U := by
    haveI := IsSimpleModule.nontrivial F[E] S
    obtain ⟨s, hs⟩ := exists_ne (0 : S)
    refine ⟨⟨⟨_, hι⟩, 0, fun h => hs ?_⟩⟩
    have := congrArg (fun u : U => (u : S →ₗ[F] M) s) h
    simpa using this
  haveI : FiniteDimensional F S :=
    Module.Finite.of_injective (S.subtype.restrictScalars F) Subtype.val_injective
  have hfd : FiniteDimensional F U := inferInstance
  let Θ' : Module.End F U := Θ.restrict hU
  obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue Θ'
  obtain ⟨v, hv⟩ := hc.exists_hasEigenvector
  have hv0 : v ≠ 0 := hv.2
  have hvc : Θ' v = c • v := hv.apply_eq_smul
  have hvs : ∀ s, T (v.1 (Aₗ s)) = c • v.1 s := by
    intro s
    have := congrArg (fun u : U => (u : S →ₗ[F] M) s) hvc
    simpa [Θ', Θ] using this
  let fR : S →ₗ[F[E]] M :=
    { toFun := v.1
      map_add' := map_add v.1
      map_smul' := fun x s => v.2 x s }
  have hAsurj : ∀ s' : S, ∃ s, Aₗ s = s' := by
    intro s'
    obtain ⟨s, hs⟩ := ψ.surjective ⟨T s', ⟨s', s'.2, rfl⟩⟩
    refine ⟨s, Subtype.ext ?_⟩
    rw [hA, hs]
    simp
  have hN : ∀ m ∈ LinearMap.range fR, T m ∈ LinearMap.range fR := by
    rintro _ ⟨s', rfl⟩
    obtain ⟨s, rfl⟩ := hAsurj s'
    refine ⟨c • s, ?_⟩
    show v.1 (c • s) = T (v.1 (Aₗ s))
    rw [hvs, map_smul]
  have hf0 : fR ≠ 0 := by
    intro h
    apply hv0
    apply Subtype.ext
    apply LinearMap.ext
    intro s
    exact congrArg (fun f : S →ₗ[F[E]] M => f s) h
  rcases hjoint _ hN with h | h
  · exact absurd (LinearMap.range_eq_bot.1 h) hf0
  · have hsurj : Function.Surjective fR := LinearMap.range_eq_top.1 h
    have hinj : Function.Injective fR := (LinearMap.injective_or_eq_zero fR).resolve_right hf0
    exact IsSimpleModule.congr (LinearEquiv.ofBijective fR ⟨hinj, hsurj⟩).symm

theorem tw_congr {g g' : M ≃ₗ[F] M} (hg : Norm (F := F) E g) (hg' : Norm (F := F) E g')
    (h : g = g') (S : Submodule F[E] M) : tw g hg S = tw g' hg' S := by
  subst h; rfl

theorem iSupIndep_of_noniso {R : Type*} [Ring R] {N : Type*} [AddCommGroup N] [Module R N]
    {ι : Type*} {W : ι → Submodule R N} (hs : ∀ i, IsSimpleModule R (W i))
    (hne : ∀ i j, i ≠ j → IsEmpty (W i ≃ₗ[R] W j)) : iSupIndep W := by
  let C : ι → isotypicComponents R N := fun i =>
    ⟨isotypicComponent R N (W i), W i, hs i, rfl⟩
  have hinj : Function.Injective C := by
    intro i j hij
    by_contra hne'
    have hij' : isotypicComponent R N (W i) = isotypicComponent R N (W j) :=
      congrArg Subtype.val hij
    haveI := hs i
    haveI := hs j
    have hle : W i ≤ isotypicComponent R N (W j) := hij' ▸ (W i).le_isotypicComponent
    obtain ⟨e⟩ := isIsotypicOfType_submodule_iff.mp
      (IsIsotypicOfType.isotypicComponent R N (W j)) (W i) hle
    exact (hne i j hne').false e
  have h1 : iSupIndep (fun c : isotypicComponents R N => (c : Submodule R N)) :=
    (sSupIndep_iff _).1 (sSupIndep_isotypicComponents R N)
  exact (h1.comp hinj).mono (fun i => (W i).le_isotypicComponent)

theorem iSupIndep_restrictScalars {ι : Type*} {W : ι → Submodule F[E] M} (h : iSupIndep W) :
    iSupIndep (fun i => (W i).restrictScalars F) := by
  rw [iSupIndep_def] at h ⊢
  intro i
  have e : ⨆ j, ⨆ (_ : j ≠ i), (W j).restrictScalars F =
      (⨆ j, ⨆ (_ : j ≠ i), W j).restrictScalars F :=
    (map_iSup₂ (Submodule.restrictScalarsLatticeHom F F[E] M) _).symm
  rw [e]
  have := h i
  rw [Submodule.disjoint_def] at this ⊢
  exact this

open scoped Fin.NatCast in
theorem abstract_simple [IsAlgClosed F] [FiniteDimensional F M] [IsSemisimpleModule F[E] M]
    [Nontrivial M] {r : ℕ} (hr : r.Prime) (T : M ≃ₗ[F] M) (hT : T ^ r = 1)
    (hTn : Norm (F := F) E T) (hfix : ∀ m, T m = m → m = 0)
    (hjoint : ∀ N : Submodule F[E] M, (∀ m ∈ N, T m ∈ N) → N = ⊥ ∨ N = ⊤) :
    IsSimpleModule F[E] M := by
  haveI : NeZero r := ⟨hr.ne_zero⟩
  have htop : (⊤ : Submodule F[E] M) ≠ ⊥ := top_ne_bot
  obtain ⟨S, -, hS⟩ :=
    (IsSemisimpleModule.eq_bot_or_exists_simple_le (⊤ : Submodule F[E] M)).resolve_left htop
  by_cases hA : Nonempty (S ≃ₗ[F[E]] tw T hTn S)
  · obtain ⟨ψ⟩ := hA
    exact caseA hTn S ψ hjoint
  exfalso
  have key : ∀ a b : ℕ, tw (T ^ a) (Norm.pow hTn a) (tw (T ^ b) (Norm.pow hTn b) S) =
      tw (T ^ (a + b)) (Norm.pow hTn _) S := fun a b => by
    rw [tw_tw _ _ (Norm.mul (Norm.pow hTn a) (Norm.pow hTn b))]
    exact tw_congr _ _ (by rw [pow_add]) S
  have hP : ∀ k : ℕ, ¬ r ∣ k → IsEmpty (S ≃ₗ[F[E]] tw (T ^ k) (Norm.pow hTn k) S) := by
    intro k hk
    refine ⟨fun e => hA ?_⟩
    have hn : ∀ n : ℕ, Nonempty (S ≃ₗ[F[E]] tw (T ^ (k * n)) (Norm.pow hTn _) S) := by
      intro n
      induction n with
      | zero =>
        have : tw (T ^ (k * 0)) (Norm.pow hTn _) S = S :=
          (tw_congr _ Norm.one (by simp) S).trans (tw_one _ S)
        exact ⟨LinearEquiv.ofEq _ _ this.symm⟩
      | succ n ih =>
        obtain ⟨en⟩ := ih
        have h1 := key k (k * n)
        have h2 : tw (T ^ (k + k * n)) (Norm.pow hTn _) S = tw (T ^ (k * (n + 1))) (Norm.pow hTn _) S :=
          tw_congr _ _ (by congr 1; ring) S
        exact ⟨(e.trans (twEquiv (Norm.pow hTn k) en)).trans (LinearEquiv.ofEq _ _ (h1.trans h2))⟩
    have hcop : Nat.Coprime k r := ((Nat.Prime.coprime_iff_not_dvd hr).2 hk).symm
    obtain ⟨m, -, hm⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop hr.one_lt
    obtain ⟨em⟩ := hn m
    have : tw (T ^ (k * m)) (Norm.pow hTn _) S = tw T hTn S :=
      tw_congr _ _ (by rw [pow_eq_pow_mod _ hT, hm, pow_one]) S
    exact ⟨em.trans (LinearEquiv.ofEq _ _ this)⟩
  let W : Fin r → Submodule F[E] M := fun i => tw (T ^ (i : ℕ)) (Norm.pow hTn _) S
  have hWs : ∀ i, IsSimpleModule F[E] (W i) := fun i =>
    isSimpleModule_iff_isAtom.2 (tw_isAtom _ (isSimpleModule_iff_isAtom.1 hS))
  have hWne : ∀ i j, i ≠ j → IsEmpty (W i ≃ₗ[F[E]] W j) := by
    intro i j hij
    refine ⟨fun e => ?_⟩
    have hi : (i : ℕ) < r := i.2
    have hj : (j : ℕ) < r := j.2
    have hijn : (i : ℕ) ≠ j := fun h => hij (Fin.ext h)
    have e1 := twEquiv (Norm.pow hTn (r - i)) e
    have eq1 : tw (T ^ (r - (i : ℕ))) (Norm.pow hTn _) (W i) = S := by
      refine (key _ _).trans ?_
      refine (tw_congr _ Norm.one ?_ S).trans (tw_one _ S)
      rw [Nat.sub_add_cancel hi.le, hT]
    have eq2 : tw (T ^ (r - (i : ℕ))) (Norm.pow hTn _) (W j) =
        tw (T ^ (r - (i : ℕ) + j)) (Norm.pow hTn _) S := key _ _
    have hnd : ¬ r ∣ r - (i : ℕ) + j := by
      rintro ⟨c, hc⟩
      have : c < 2 := by
        by_contra h
        have h' : 2 ≤ c := by omega
        have := Nat.mul_le_mul_left r h'
        omega
      interval_cases c <;> omega
    exact (hP _ hnd).false
      ((LinearEquiv.ofEq _ _ eq1.symm).trans (e1.trans (LinearEquiv.ofEq _ _ eq2)))
  have hind : iSupIndep W := iSupIndep_of_noniso hWs hWne
  have hmap : ∀ i : Fin r, ∀ v ∈ (W i).restrictScalars F, T v ∈ (W (i + 1)).restrictScalars F := by
    intro i v hv
    change T v ∈ W (i + 1)
    change v ∈ W i at hv
    rw [mem_tw] at hv ⊢
    have hval : ((i + 1 : Fin r) : ℕ) = ((i : ℕ) + 1) % r := by
      rw [Fin.val_add, Fin.val_one']
      simp [Nat.add_mod]
    have hpow : T ^ ((i + 1 : Fin r) : ℕ) = T ^ ((i : ℕ) + 1) := by
      rw [hval, ← pow_eq_pow_mod _ hT]
    have hpow' : ∀ x : M, ((T ^ ((i : ℕ) + 1))⁻¹) (T x) = ((T ^ (i : ℕ))⁻¹) x := by
      intro x
      rw [pow_succ', mul_inv_rev]
      simp [LinearEquiv.mul_apply]
    rw [hpow, hpow']
    exact hv
  have h0 : (W 0).restrictScalars F ≠ ⊥ := by
    intro h
    haveI := IsSimpleModule.nontrivial F[E] S
    obtain ⟨s, hs⟩ := exists_ne (0 : S)
    have hmem : (s : M) ∈ (W 0).restrictScalars F := by
      change (s : M) ∈ W 0
      simp only [W, mem_tw]
      simpa using s.2
    rw [h] at hmem
    exact hs (Subtype.ext (by simpa using hmem))
  obtain ⟨v, hv0, hv⟩ :=
    CFSG.GroupTheory.CoprimeActionSupport.OrbitSums.exists_fixed r T hT
      (fun i => (W i).restrictScalars F) (iSupIndep_restrictScalars hind) hmap h0
  exact hv0 (hfix v hv)

end Abstract

section Final

open scoped MonoidAlgebra

theorem restriction_irreducible {F : Type*} [Field F] [IsAlgClosed F]
    {E : Type*} [Group E] [Finite E]
    {V : Type*} [AddCommGroup V] [Module F V] [FiniteDimensional F V] [Nontrivial V]
    (σ : Representation F E V) {r : ℕ} (hr : r.Prime) (hrF : (r : F) ≠ 0)
    (hcard : (Nat.card E : F) ≠ 0)
    (T : V ≃ₗ[F] V) (hT : T ^ r = 1)
    (hfix : LinearMap.ker ((T : V →ₗ[F] V) - LinearMap.id) = ⊥)
    (α : MulAut E) (hα : α ^ r = 1)
    (hcov : ∀ e : E, (T : V →ₗ[F] V) * σ e = σ (α e) * (T : V →ₗ[F] V))
    (hjoint : ∀ W : Submodule F V, (∀ e : E, W ≤ W.comap (σ e)) →
      W ≤ W.comap (T : V →ₗ[F] V) → W = ⊥ ∨ W = ⊤) :
    σ.IsIrreducible := by
  haveI : NeZero (Nat.card E : F) := ⟨hcard⟩
  haveI : IsSemisimpleModule F[E] σ.asModule :=
    (Representation.isSemisimpleRepresentation_iff_isSemisimpleModule_asModule σ).1 inferInstance
  haveI : Nontrivial σ.asModule := σ.asModuleEquiv.toEquiv.nontrivial
  let ι := σ.asModuleEquiv
  let T' : σ.asModule ≃ₗ[F] σ.asModule := ι.trans (T.trans ι.symm)
  have hT'apply : ∀ m, ι (T' m) = T (ι m) := fun m => by simp [T']
  have hsmul : ∀ (e : E) (m : σ.asModule), ι (MonoidAlgebra.of F E e • m) = σ e (ι m) := by
    intro e m
    rw [Representation.asModuleEquiv_map_smul, Representation.asAlgebraHom_of]
  have hTn : Norm (F := F) E T' := by
    refine ⟨α, fun e m => ?_⟩
    apply ι.injective
    rw [hT'apply, hsmul, hsmul, hT'apply]
    exact congrArg (fun f : V →ₗ[F] V => f (ι m)) (hcov e)
  have hpow : ∀ n : ℕ, ∀ m, ι ((T' ^ n) m) = (T ^ n) (ι m) := by
    intro n
    induction n with
    | zero => intro m; simp
    | succ n ih => intro m; rw [pow_succ, pow_succ, LinearEquiv.mul_apply, LinearEquiv.mul_apply, ih, hT'apply]
  have hT'r : T' ^ r = 1 := by
    ext m
    apply ι.injective
    rw [hpow, hT]
    rfl
  have hfix' : ∀ m, T' m = m → m = 0 := by
    intro m hm
    have : ι m ∈ LinearMap.ker ((T : V →ₗ[F] V) - LinearMap.id) := by
      have := congrArg ι hm
      rw [hT'apply] at this
      simp [this]
    rw [hfix] at this
    exact ι.injective (by simpa using this)
  have hjoint' : ∀ N : Submodule F[E] σ.asModule, (∀ m ∈ N, T' m ∈ N) → N = ⊥ ∨ N = ⊤ := by
    intro N hN
    let W : Submodule F V := Submodule.map (ι : σ.asModule →ₗ[F] V) (N.restrictScalars F)
    have h1 : ∀ e : E, W ≤ W.comap (σ e) := by
      rintro e _ ⟨n, hn, rfl⟩
      exact ⟨MonoidAlgebra.of F E e • n, N.smul_mem _ hn, hsmul e n⟩
    have h2 : W ≤ W.comap (T : V →ₗ[F] V) := by
      rintro _ ⟨n, hn, rfl⟩
      exact ⟨T' n, hN n hn, hT'apply n⟩
    rcases hjoint W h1 h2 with h | h
    · left
      rw [eq_bot_iff]
      intro n hn
      have : ι n ∈ W := ⟨n, hn, rfl⟩
      rw [h] at this
      have : ι n = 0 := by simpa using this
      simpa using ι.injective (this.trans (map_zero ι).symm)
    · right
      rw [eq_top_iff]
      intro n _
      have : ι n ∈ W := by rw [h]; trivial
      obtain ⟨n', hn', hnn⟩ := this
      have := ι.injective hnn
      rw [← this]
      exact hn'
  have := abstract_simple hr T' hT'r hTn hfix' hjoint'
  exact (Representation.irreducible_iff_isSimpleModule_asModule σ).2 this

end Final

end CFSG.GroupTheory.CoprimeActionSupport.PrimeCyclicNormalizerIrreducibleRestriction
