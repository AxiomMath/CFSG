module

public import CFSG.HardMathSupport.GuralnickMalle.ElemAbelianTwoCor

public section

namespace CFSG.HardMathSupport.GuralnickMalle

open Module
open scoped TensorProduct

variable {K : Type*} [Field K] [CharP K 2]

@[expose] def augDualSet {V : Type*} [AddCommGroup V] [Module K V] {r : ℕ}
    (T : Fin r → V ≃ₗ[K] V) : Set (Module.Dual K V) :=
  ⋃ i : Fin r, (LinearMap.range
    ((T i).dualMap - 1 : Module.Dual K V →ₗ[K] Module.Dual K V) : Set (Module.Dual K V))

@[expose] noncomputable def augDual {V : Type*} [AddCommGroup V] [Module K V] {r : ℕ}
    (T : Fin r → V ≃ₗ[K] V) : Submodule K (Module.Dual K V) :=
  Submodule.span K (augDualSet T)

abbrev head {V : Type*} [AddCommGroup V] [Module K V] {r : ℕ}
    (T : Fin r → V ≃ₗ[K] V) : Type _ :=
  Module.Dual K V ⧸ augDual T

theorem dualAnnihilator_augDual_eq_map_iterFixed {V : Type*} [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] {r : ℕ} (T : Fin r → V ≃ₗ[K] V) :
    (augDual T).dualAnnihilator =
      (iterFixed T r).map (Module.Dual.eval K V) := by
  classical
  ext g
  set v : V := (Module.evalEquiv K V).symm g with hv
  have hg_eval : Module.Dual.eval K V v = g := by
    rw [← Module.evalEquiv_apply, LinearEquiv.apply_symm_apply]
  rw [Submodule.mem_map]
  constructor
  · intro hg
    refine ⟨v, ?_, hg_eval⟩
    rw [mem_iterFixed]
    intro i _
    rw [← sub_eq_zero]
    refine (Module.forall_dual_apply_eq_zero_iff K (T i v - v)).mp ?_
    intro φ
    have hmem : ((T i).dualMap : Module.Dual K V →ₗ[K] Module.Dual K V) φ - φ ∈
        augDual T := by
      rw [augDual]
      exact Submodule.subset_span (Set.mem_iUnion.mpr ⟨i, Set.mem_range_self φ⟩)
    have h0 : g (((T i).dualMap : Module.Dual K V →ₗ[K] Module.Dual K V) φ - φ) = 0 :=
      (Submodule.mem_dualAnnihilator g).mp hg _ hmem
    have hval : g (((T i).dualMap : Module.Dual K V →ₗ[K] Module.Dual K V) φ - φ) =
        φ (T i v) - φ v := by
      rw [← hg_eval]
      simp [LinearMap.sub_apply]
    have hzero : φ (T i v) - φ v = 0 := by
      rw [← hval]
      exact h0
    simpa [map_sub, sub_eq_zero] using hzero
  · rintro ⟨u, hu, rfl⟩
    rw [Submodule.mem_dualAnnihilator]
    intro ψ hψ
    have hs : augDualSet T ⊆ LinearMap.ker (Module.Dual.eval K V u) := by
      rintro ψ hψ
      simp only [augDualSet, Set.mem_iUnion, Set.mem_range] at hψ
      obtain ⟨i, φ, rfl⟩ := hψ
      have hu' : T i u = u := (mem_iterFixed.mp hu) i i.2
      simp [LinearMap.sub_apply, hu']
    rw [augDual] at hψ
    have hle : Submodule.span K (augDualSet T) ≤ LinearMap.ker (Module.Dual.eval K V u) :=
      Submodule.span_le.mpr hs
    simpa using hle hψ

theorem finrank_head_eq_fixed {V : Type*} [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] {r : ℕ} (T : Fin r → V ≃ₗ[K] V) :
    Module.finrank K (head T) = Module.finrank K (iterFixed T r) := by
  have hq : Module.finrank K (head T) =
      Module.finrank K (augDual T).dualAnnihilator :=
    LinearEquiv.finrank_eq (Subspace.quotEquivAnnihilator (augDual T))
  rw [hq, dualAnnihilator_augDual_eq_map_iterFixed]
  exact (LinearEquiv.finrank_eq
    (Submodule.equivMapOfInjective (Module.Dual.eval K V) (Module.eval_apply_injective K)
      (iterFixed T r))).symm

variable {V W : Type*} [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]

@[expose] noncomputable def contractionBilin :
    V →ₗ[K] W →ₗ[K] (Module.Dual K V →ₗ[K] W) where
  toFun v :=
    { toFun := fun w =>
        { toFun := fun φ => φ v • w
          map_add' := fun φ ψ => by
            change (φ + ψ) v • w = φ v • w + ψ v • w
            rw [LinearMap.add_apply, add_smul]
          map_smul' := fun a φ => by
            change (a • φ) v • w = a • (φ v • w)
            rw [LinearMap.smul_apply]
            exact smul_assoc a (φ v) w }
      map_add' := fun w₁ w₂ => by
        apply LinearMap.ext
        intro φ
        change φ v • (w₁ + w₂) = φ v • w₁ + φ v • w₂
        rw [smul_add]
      map_smul' := fun a w => by
        apply LinearMap.ext
        intro φ
        change φ v • (a • w) = a • (φ v • w)
        exact smul_comm (φ v) a w }
  map_add' := fun v₁ v₂ => by
    apply LinearMap.ext
    intro w
    apply LinearMap.ext
    intro φ
    change (φ (v₁ + v₂)) • w = φ v₁ • w + φ v₂ • w
    rw [map_add, add_smul]
  map_smul' := fun a v => by
    apply LinearMap.ext
    intro w
    apply LinearMap.ext
    intro φ
    change (φ (a • v)) • w = a • (φ v • w)
    rw [map_smul]
    exact smul_assoc a (φ v) w

@[expose] noncomputable def contract :
    V ⊗[K] W →ₗ[K] (Module.Dual K V →ₗ[K] W) :=
  TensorProduct.lift contractionBilin

@[simp]
theorem contract_tmul (v : V) (w : W) (φ : Module.Dual K V) :
    contract (v ⊗ₜ[K] w) φ = φ v • w := by
  rw [contract, TensorProduct.lift.tmul]
  rfl

theorem contract_map (T : V ≃ₗ[K] V) (S : W ≃ₗ[K] W) (t : V ⊗[K] W)
    (φ : Module.Dual K V) :
    contract (TensorProduct.map (T : V →ₗ[K] V) (S : W →ₗ[K] W) t) φ =
      S (contract t (T.dualMap φ)) := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul v w =>
    simp [TensorProduct.map_tmul]
  | add x y hx hy =>
    simp only [map_add, LinearMap.add_apply, hx, hy]

theorem repr_tensorProduct_eq_dualDistrib {ι κ : Type*} (b : Basis ι K V)
    (c : Basis κ K W) (t : V ⊗[K] W) (i : ι) (j : κ) :
    (b.tensorProduct c).repr t (i, j) =
      TensorProduct.dualDistrib K V W (b.coord i ⊗ₜ[K] c.coord j) t := by
  classical
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul m n =>
    simp [Basis.tensorProduct_repr_tmul_apply, TensorProduct.dualDistrib_apply, mul_comm]
  | add x y hx hy => simp only [map_add, Finsupp.add_apply, hx, hy]

theorem coord_contract_eq_dualDistrib {κ : Type*} (c : Basis κ K W)
    (t : V ⊗[K] W) (φ : Module.Dual K V) (j : κ) :
    c.coord j (contract t φ) =
      TensorProduct.dualDistrib K V W (φ ⊗ₜ[K] c.coord j) t := by
  classical
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul m n =>
    simp [contract_tmul, TensorProduct.dualDistrib_apply, smul_eq_mul, mul_comm]
  | add x y hx hy => simp only [map_add, LinearMap.add_apply, hx, hy]

theorem contract_eq_zero_iff [FiniteDimensional K V] [FiniteDimensional K W]
    (t : V ⊗[K] W) : contract t = 0 ↔ t = 0 := by
  classical
  constructor
  · intro ht
    let b : Basis (Fin (Module.finrank K V)) K V := Module.finBasis K V
    let c : Basis (Fin (Module.finrank K W)) K W := Module.finBasis K W
    have hcontract : ∀ φ : Module.Dual K V, contract t φ = 0 := by
      intro φ
      have := congrArg (fun f : Module.Dual K V →ₗ[K] W => f φ) ht
      simpa using this
    have hcoord : ∀ (p : Fin (Module.finrank K V) × Fin (Module.finrank K W)),
        (b.tensorProduct c).coord p t = 0 := by
      rintro ⟨i, j⟩
      calc
        (b.tensorProduct c).coord (i, j) t
            = TensorProduct.dualDistrib K V W
                (b.coord i ⊗ₜ[K] c.coord j) t := by
              rw [Basis.coord_apply]
              exact repr_tensorProduct_eq_dualDistrib b c t i j
        _ = c.coord j (contract t (b.coord i)) :=
              (coord_contract_eq_dualDistrib c t (b.coord i) j).symm
        _ = 0 := by
              rw [hcontract (b.coord i)]
              exact map_zero _
    exact (b.tensorProduct c).forall_coord_eq_zero_iff.mp hcoord
  · intro ht
    rw [ht, map_zero]

theorem contract_injective [FiniteDimensional K V] [FiniteDimensional K W] :
    Function.Injective (contract (K := K) (V := V) (W := W)) := by
  intro t u h
  have hsub : t - u = 0 := (contract_eq_zero_iff (t - u)).mp (by
    rw [map_sub, h, sub_self])
  exact sub_eq_zero.mp hsub


noncomputable def equivariantHom {r : ℕ} (T : Fin r → V ≃ₗ[K] V)
    (S : Fin r → W ≃ₗ[K] W) : Submodule K (Module.Dual K V →ₗ[K] W) :=
  ⨅ i, LinearMap.ker
    (LinearMap.lcomp K W ((T i).dualMap : Module.Dual K V →ₗ[K] Module.Dual K V)
      - LinearMap.compRight K (S i : W →ₗ[K] W))

theorem mem_equivariantHom {r : ℕ} {T : Fin r → V ≃ₗ[K] V}
    {S : Fin r → W ≃ₗ[K] W} {f : Module.Dual K V →ₗ[K] W} :
    f ∈ equivariantHom T S ↔
      ∀ i, f.comp ((T i).dualMap : Module.Dual K V →ₗ[K] Module.Dual K V) =
        (S i : W →ₗ[K] W).comp f := by
  simp [equivariantHom, LinearMap.lcomp_apply', LinearMap.compRight_apply, sub_eq_zero]

theorem comp_self_of_mul_eq_one (S : W ≃ₗ[K] W) (hS : S * S = 1) :
    (S : W →ₗ[K] W).comp (S : W →ₗ[K] W) = 1 := by
  have h := congrArg (fun e : W ≃ₗ[K] W => (e : W →ₗ[K] W)) hS
  simpa [LinearEquiv.mul_eq_trans, Module.End.mul_eq_comp, Module.End.one_eq_id] using h

theorem quotientMap_comp_self (L : Submodule K W) (S : W ≃ₗ[K] W)
    (hL : ∀ x ∈ L, S x ∈ L) (hS : S * S = 1) :
    (L.mapQ L (S : W →ₗ[K] W) (fun x hx => hL x hx)).comp
      (L.mapQ L (S : W →ₗ[K] W) (fun x hx => hL x hx)) = 1 := by
  apply LinearMap.ext
  intro x
  induction x using Quotient.inductionOn with
  | _ x =>
    change L.mapQ L (S : W →ₗ[K] W) (fun x hx => hL x hx)
        (L.mapQ L (S : W →ₗ[K] W) (fun x hx => hL x hx)
          (Submodule.Quotient.mk x)) =
      (1 : (W ⧸ L) →ₗ[K] (W ⧸ L)) (Submodule.Quotient.mk x)
    rw [Submodule.mapQ_apply, Submodule.mapQ_apply]
    have hfun : S (S x) = x := by
      have h := comp_self_of_mul_eq_one S hS
      exact congrFun (congrArg DFunLike.coe h) x
    change Submodule.Quotient.mk (S (S x)) =
      (1 : (W ⧸ L) →ₗ[K] (W ⧸ L)) (Submodule.Quotient.mk x)
    rw [hfun]
    rfl

noncomputable def quotientInv (L : Submodule K W) (S : W ≃ₗ[K] W)
    (hL : ∀ x ∈ L, S x ∈ L) (hS : S * S = 1) : (W ⧸ L) ≃ₗ[K] (W ⧸ L) :=
  LinearEquiv.ofLinearMap (L.mapQ L (S : W →ₗ[K] W) (fun x hx => hL x hx))
    (L.mapQ L (S : W →ₗ[K] W) (fun x hx => hL x hx))
    (quotientMap_comp_self L S hL hS) (quotientMap_comp_self L S hL hS)

@[simp]
theorem quotientInv_apply_mk (L : Submodule K W) (S : W ≃ₗ[K] W)
    (hL : ∀ x ∈ L, S x ∈ L) (hS : S * S = 1) (x : W) :
    quotientInv L S hL hS (Submodule.Quotient.mk x) = Submodule.Quotient.mk (S x) := by
  simp [quotientInv, Submodule.mapQ_apply]

theorem quotientInv_mul_self (L : Submodule K W) (S : W ≃ₗ[K] W)
    (hL : ∀ x ∈ L, S x ∈ L) (hS : S * S = 1) :
    quotientInv L S hL hS * quotientInv L S hL hS = 1 := by
  apply LinearEquiv.ext
  intro x
  induction x using Quotient.inductionOn with
  | _ x =>
    rw [LinearEquiv.mul_eq_trans, LinearEquiv.trans_apply]
    change quotientInv L S hL hS (quotientInv L S hL hS (Submodule.Quotient.mk x)) =
      Submodule.Quotient.mk x
    rw [quotientInv_apply_mk, quotientInv_apply_mk]
    have hfun : S (S x) = x := by
      have h := comp_self_of_mul_eq_one S hS
      exact congrFun (congrArg DFunLike.coe h) x
    rw [hfun]

theorem quotientInv_comm (L : Submodule K W) (S S' : W ≃ₗ[K] W)
    (hL : ∀ x ∈ L, S x ∈ L) (hL' : ∀ x ∈ L, S' x ∈ L)
    (hS : S * S = 1) (hS' : S' * S' = 1) (hcomm : S * S' = S' * S) :
    quotientInv L S hL hS * quotientInv L S' hL' hS' =
      quotientInv L S' hL' hS' * quotientInv L S hL hS := by
  apply LinearEquiv.ext
  intro x
  induction x using Quotient.inductionOn with
  | _ x =>
    rw [LinearEquiv.mul_eq_trans, LinearEquiv.trans_apply]
    change quotientInv L S hL hS (quotientInv L S' hL' hS' (Submodule.Quotient.mk x)) =
      quotientInv L S' hL' hS' (quotientInv L S hL hS (Submodule.Quotient.mk x))
    rw [quotientInv_apply_mk, quotientInv_apply_mk, quotientInv_apply_mk, quotientInv_apply_mk]
    have hfun : S (S' x) = S' (S x) := by
      have h := congrArg (fun e : W ≃ₗ[K] W => (e : W →ₗ[K] W)) hcomm
      have hx := congrFun (congrArg DFunLike.coe h) x
      simpa [LinearEquiv.mul_eq_trans, LinearEquiv.trans_apply] using hx
    rw [hfun]


theorem finrank_le_two_pow_mul_iterFixed {W : Type*} [AddCommGroup W] [Module K W]
    [FiniteDimensional K W] :
    ∀ (r : ℕ) (S : Fin r → W ≃ₗ[K] W),
      (∀ i, S i * S i = 1) → (∀ i j, S i * S j = S j * S i) →
      Module.finrank K W ≤ 2 ^ r * Module.finrank K (iterFixed S r) := by
  intro r
  induction r with
  | zero =>
    intro S hS2 hSc
    rw [iterFixed_zero S, finrank_top, pow_zero, one_mul]
  | succ r ih =>
    intro S hS2 hSc
    let S' : Fin r → W ≃ₗ[K] W := fun j => S (Fin.castSucc j)
    have h1 := ih S' (fun i => hS2 (Fin.castSucc i)) (fun i j => hSc _ _)
    have hcast : iterFixed S' r = iterFixed S r :=
      iterFixed_castSucc (T := S) (i := r) le_rfl
    rw [hcast] at h1
    have h2 := finrank_iterFixed_le_two_mul_succ (T := S) hS2 hSc
      (i := r) (Nat.lt_succ_self r)
    calc
      Module.finrank K W ≤ 2 ^ r * Module.finrank K (iterFixed S r) := h1
      _ ≤ 2 ^ r * (2 * Module.finrank K (iterFixed S (r + 1))) :=
          Nat.mul_le_mul_left _ h2
      _ = 2 ^ (r + 1) * Module.finrank K (iterFixed S (r + 1)) := by
          rw [pow_succ]
          ring

theorem exists_fixed_ne_zero {W : Type*} [AddCommGroup W] [Module K W]
    [FiniteDimensional K W] {r : ℕ} (S : Fin r → W ≃ₗ[K] W)
    (hS2 : ∀ i, S i * S i = 1) (hSc : ∀ i j, S i * S j = S j * S i)
    (hW : 0 < Module.finrank K W) :
    ∃ w : W, w ≠ 0 ∧ ∀ i, S i w = w := by
  have hle := finrank_le_two_pow_mul_iterFixed r S hS2 hSc
  have hpos : 0 < Module.finrank K (iterFixed S r) := by
    by_contra h
    have hzero : Module.finrank K (iterFixed S r) = 0 := Nat.eq_zero_of_not_pos h
    rw [hzero, mul_zero] at hle
    omega
  haveI : Nontrivial ↥(iterFixed S r) := Module.nontrivial_of_finrank_pos hpos
  obtain ⟨w, hw⟩ := exists_ne (0 : ↥(iterFixed S r))
  refine ⟨(w : W), ?_, ?_⟩
  · intro hw0
    exact hw (Subtype.ext hw0)
  · intro i
    exact (mem_iterFixed.mp w.2) i i.2

@[expose] noncomputable def mapsKillingAug {V : Type*} [AddCommGroup V] [Module K V] {r : ℕ}
    (T : Fin r → V ≃ₗ[K] V) (W : Type*) [AddCommGroup W] [Module K W] :
    Submodule K (Module.Dual K V →ₗ[K] W) :=
  LinearMap.ker (LinearMap.lcomp K W (augDual T).subtype)

theorem mem_mapsKillingAug {V : Type*} [AddCommGroup V] [Module K V] {r : ℕ}
    {T : Fin r → V ≃ₗ[K] V} {W : Type*} [AddCommGroup W] [Module K W]
    {g : Module.Dual K V →ₗ[K] W} :
    g ∈ mapsKillingAug T W ↔ augDual T ≤ LinearMap.ker g := by
  rw [mapsKillingAug, LinearMap.mem_ker]
  constructor
  · intro h x hx
    have := congrFun (congrArg DFunLike.coe h) ⟨x, hx⟩
    simpa using this
  · intro h
    ext ⟨x, hx⟩
    simpa using h hx

noncomputable def mapsKillingAugEquiv {V : Type*} [AddCommGroup V] [Module K V] {r : ℕ}
    (T : Fin r → V ≃ₗ[K] V) (W : Type*) [AddCommGroup W] [Module K W] :
    ↥(mapsKillingAug T W) ≃ₗ[K] (head T →ₗ[K] W) :=
  LinearEquiv.ofLinearMap
    { toFun := fun g => (augDual T).liftQ g.1 (mem_mapsKillingAug.mp g.2)
      map_add' := by
        intro g h
        ext x
        simp [Submodule.liftQ_apply]
      map_smul' := by
        intro a g
        ext x
        simp [Submodule.liftQ_apply] }
    { toFun := fun h => ⟨h.comp (augDual T).mkQ, by
        rw [mem_mapsKillingAug]
        intro x hx
        rw [LinearMap.mem_ker, LinearMap.comp_apply, Submodule.mkQ_apply,
          show (Submodule.Quotient.mk x : head T) = 0 from
            (Submodule.Quotient.mk_eq_zero (p := augDual T)).mpr hx, map_zero]⟩
      map_add' := by
        intro h₁ h₂
        ext x
        simp
      map_smul' := by
        intro a h
        ext x
        simp }
    (by
      apply LinearMap.ext
      intro h
      apply LinearMap.ext
      intro x
      induction x using Quotient.inductionOn with
      | _ x => rfl)
    (by
      apply LinearMap.ext
      intro g
      apply Subtype.ext
      change ((augDual T).liftQ g.1 (mem_mapsKillingAug.mp g.2)).comp (augDual T).mkQ = g.1
      exact Submodule.liftQ_mkQ (p := augDual T) g.1 (mem_mapsKillingAug.mp g.2))

theorem finrank_maps_killing_augDual {V : Type*} [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] {r : ℕ} (T : Fin r → V ≃ₗ[K] V) (W : Type*)
    [AddCommGroup W] [Module K W] [FiniteDimensional K W] :
    Module.finrank K ↥(mapsKillingAug T W) =
      Module.finrank K (iterFixed T r) * Module.finrank K W := by
  rw [LinearEquiv.finrank_eq (mapsKillingAugEquiv T W), Module.finrank_linearMap,
    finrank_head_eq_fixed]

theorem contract_mem_equivariantHom {V W : Type*} [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] :
    ∀ (r : ℕ) (T : Fin r → V ≃ₗ[K] V) (S : Fin r → W ≃ₗ[K] W),
      (∀ i, S i * S i = 1) → ∀ t : V ⊗[K] W, t ∈ tensorFixed T S →
      contract t ∈ equivariantHom T S := by
  intro r
  induction r with
  | zero =>
    intro T S hS2 t ht
    rw [mem_equivariantHom]
    intro i
    exact Fin.elim0 i
  | succ r ih =>
    intro T S hS2 t ht
    have ht' : t ∈ tensorFixed (fun j : Fin r => T (Fin.castSucc j))
        (fun j : Fin r => S (Fin.castSucc j)) := by
      rw [tensorFixed_castSucc T S] at ht
      exact ht.1
    have htlast : t ∈ LinearMap.ker
        (TensorProduct.map (T (Fin.last r) : V →ₗ[K] V)
          (S (Fin.last r) : W →ₗ[K] W) - 1) := by
      rw [tensorFixed_castSucc T S] at ht
      exact ht.2
    rw [mem_equivariantHom]
    intro i
    rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
    · exact (mem_equivariantHom.mp
        (ih (fun j : Fin r => T (Fin.castSucc j))
          (fun j : Fin r => S (Fin.castSucc j))
          (fun j => hS2 (Fin.castSucc j)) t ht')) j
    · apply LinearMap.ext
      intro φ
      have hfix : TensorProduct.map (T (Fin.last r) : V →ₗ[K] V)
          (S (Fin.last r) : W →ₗ[K] W) t = t := by
        simpa [LinearMap.sub_apply, sub_eq_zero] using htlast
      have hnat := contract_map (T (Fin.last r)) (S (Fin.last r)) t φ
      rw [hfix] at hnat
      have hcomp : (S (Fin.last r) : W →ₗ[K] W).comp
          (S (Fin.last r) : W →ₗ[K] W) = 1 :=
        comp_self_of_mul_eq_one (S (Fin.last r)) (hS2 (Fin.last r))
      have hSS : S (Fin.last r) (S (Fin.last r)
          (contract t ((T (Fin.last r)).dualMap φ))) =
          contract t ((T (Fin.last r)).dualMap φ) := by
        have := congrFun (congrArg DFunLike.coe hcomp)
          (contract t ((T (Fin.last r)).dualMap φ))
        simpa using this
      have h2 : S (Fin.last r) (S (Fin.last r)
          (contract t ((T (Fin.last r)).dualMap φ))) =
          S (Fin.last r) (contract t φ) := by
        rw [hnat]
      calc
        contract t ((T (Fin.last r)).dualMap φ) =
            S (Fin.last r) (S (Fin.last r)
              (contract t ((T (Fin.last r)).dualMap φ))) := hSS.symm
        _ = S (Fin.last r) (contract t φ) := h2



theorem kills_augDual_of_mem_equivariantHom {V W : Type*} [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] {r : ℕ} (T : Fin r → V ≃ₗ[K] V)
    (S : Fin r → W ≃ₗ[K] W) (L : Submodule K W)
    {f : Module.Dual K V →ₗ[K] W} (hf : f ∈ equivariantHom T S)
    (hLfix : ∀ i, ∀ x ∈ L, S i x = x) (himg : ∀ φ : Module.Dual K V, f φ ∈ L) :
    augDual T ≤ LinearMap.ker f := by
  rw [augDual]
  apply Submodule.span_le.mpr
  rintro ψ hψ
  simp only [augDualSet, Set.mem_iUnion, Set.mem_range] at hψ
  obtain ⟨i, φ, rfl⟩ := hψ
  change f ((T i).dualMap φ - φ) = 0
  have hf_i : f ((T i).dualMap φ) = S i (f φ) := by
    simpa [LinearMap.comp_apply] using
      congrFun (congrArg DFunLike.coe (mem_equivariantHom.mp hf i)) φ
  rw [map_sub, hf_i]
  exact sub_eq_zero.mpr (hLfix i (f φ) (himg φ))

theorem finrank_equivariantHom_le {V : Type*} [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] {r : ℕ} (T : Fin r → V ≃ₗ[K] V) :
    ∀ (n : ℕ) (W : Type*) [AddCommGroup W] [Module K W] [FiniteDimensional K W],
      Module.finrank K W = n →
      ∀ (S : Fin r → W ≃ₗ[K] W), (∀ i, S i * S i = 1) →
        (∀ i j, S i * S j = S j * S i) →
        Module.finrank K (equivariantHom T S) ≤
          Module.finrank K (iterFixed T r) * Module.finrank K W := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro W _ _ _ hWdim S hS2 hSc
    by_cases hn : n = 0
    · have hWzero : Module.finrank K W = 0 := by omega
      haveI : Subsingleton W := Module.finrank_zero_iff.mp hWzero
      haveI : Subsingleton (Module.Dual K V →ₗ[K] W) := by infer_instance
      have hzero : Module.finrank K ↥(equivariantHom T S) = 0 :=
        Module.finrank_zero_of_subsingleton
      rw [hzero, hWzero, mul_zero]
    · have hWpos : 0 < Module.finrank K W := by omega
      obtain ⟨w0, hw0ne, hw0fix⟩ := exists_fixed_ne_zero S hS2 hSc hWpos
      let L : Submodule K W := Submodule.span K {w0}
      have hL : ∀ i, ∀ x ∈ L, S i x ∈ L := by
        intro i x hx
        rw [Submodule.mem_span_singleton] at hx ⊢
        obtain ⟨a, rfl⟩ := hx
        rw [map_smul, hw0fix i]
        exact ⟨a, rfl⟩
      have hLfix : ∀ i, ∀ x ∈ L, S i x = x := by
        intro i x hx
        rw [Submodule.mem_span_singleton] at hx
        obtain ⟨a, rfl⟩ := hx
        rw [map_smul, hw0fix i]
      let Q : Type _ := W ⧸ L
      let S' : Fin r → Q ≃ₗ[K] Q := fun i => quotientInv L (S i) (hL i) (hS2 i)
      have hS'2 : ∀ i, S' i * S' i = 1 := fun i =>
        quotientInv_mul_self L (S i) (hL i) (hS2 i)
      have hS'c : ∀ i j, S' i * S' j = S' j * S' i := fun i j =>
        quotientInv_comm L (S i) (S j) (hL i) (hL j) (hS2 i) (hS2 j) (hSc i j)
      have hLdim : Module.finrank K L = 1 := finrank_span_singleton hw0ne
      have hQdim : Module.finrank K Q = n - 1 := by
        change Module.finrank K (W ⧸ L) = n - 1
        have h := Submodule.finrank_quotient_add_finrank L
        have hW' : Module.finrank K W = n := hWdim
        omega
      have hIH := ih (n - 1) (by omega) Q hQdim S' hS'2 hS'c
      let post : (Module.Dual K V →ₗ[K] W) →ₗ[K] (Module.Dual K V →ₗ[K] Q) :=
        LinearMap.compRight K L.mkQ
      have hpost_mem : ∀ f ∈ equivariantHom T S, post f ∈ equivariantHom T S' := by
        intro f hf
        rw [mem_equivariantHom] at hf ⊢
        intro i
        apply LinearMap.ext
        intro φ
        have hf_i : f ((T i).dualMap φ) = S i (f φ) := by
          simpa [LinearMap.comp_apply] using
            congrFun (congrArg DFunLike.coe (hf i)) φ
        calc
          L.mkQ (f ((T i).dualMap φ)) = L.mkQ (S i (f φ)) := by
            rw [hf_i]
          _ = S' i (L.mkQ (f φ)) :=
            (quotientInv_apply_mk L (S i) (hL i) (hS2 i) (f φ)).symm
      let postEq : ↥(equivariantHom T S) →ₗ[K] ↥(equivariantHom T S') :=
        { toFun := fun f => ⟨post f.1, hpost_mem f.1 f.2⟩
          map_add' := by
            intro f g
            apply Subtype.ext
            apply LinearMap.ext
            intro φ
            simp [post]
          map_smul' := by
            intro a f
            apply Subtype.ext
            apply LinearMap.ext
            intro φ
            simp [post] }
      have hker_le : Module.finrank K ↥(LinearMap.ker postEq) ≤
          Module.finrank K (iterFixed T r) := by
        let proj : ↥(LinearMap.ker postEq) →ₗ[K] (Module.Dual K V →ₗ[K] W) :=
          { toFun := fun f => f.1.1
            map_add' := by intro f g; rfl
            map_smul' := by intro a f; rfl }
        have himgOf : ∀ f : ↥(LinearMap.ker postEq), ∀ φ : Module.Dual K V,
            proj f φ ∈ L := by
          intro f φ
          have hfker : postEq f.1 = 0 := LinearMap.mem_ker.mp f.2
          have hf2 : ((postEq f.1 : ↥(equivariantHom T S')) :
              Module.Dual K V →ₗ[K] Q) = 0 := by
            have := Subtype.ext_iff.mp hfker
            simpa using this
          have h0 : L.mkQ (f.1.1 φ) = 0 := by
            have h := congrFun (congrArg DFunLike.coe hf2) φ
            change (post f.1.1) φ = 0 at h
            simpa only [post, proj, LinearMap.compRight_apply, LinearMap.comp_apply,
              LinearMap.zero_apply] using h
          rw [Submodule.mkQ_apply] at h0
          have hmem : f.1.1 φ ∈ L :=
            (Submodule.Quotient.mk_eq_zero (p := L)).mp h0
          simpa [proj] using hmem
        let projL : ↥(LinearMap.ker postEq) →ₗ[K] (Module.Dual K V →ₗ[K] L) :=
          { toFun := fun f => LinearMap.codRestrict L (proj f) (himgOf f)
            map_add' := by
              intro f g
              apply LinearMap.ext
              intro φ
              apply Subtype.ext
              simp [proj]
            map_smul' := by
              intro a f
              apply LinearMap.ext
              intro φ
              apply Subtype.ext
              simp [proj] }
        let kerMap : ↥(LinearMap.ker postEq) →ₗ[K] ↥(mapsKillingAug T L) :=
          projL.codRestrict (mapsKillingAug T L) (fun f =>
            mem_mapsKillingAug.mpr (by
              have hkill := kills_augDual_of_mem_equivariantHom T S L f.1.2 hLfix
                (fun φ => by simpa [proj] using himgOf f φ)
              simpa [projL, proj] using hkill))
        have hkerMap_inj : Function.Injective kerMap := by
          intro f g hfg
          apply Subtype.ext
          apply Subtype.ext
          ext φ
          have h1 := congrArg
            (fun x : ↥(mapsKillingAug T L) => (x : Module.Dual K V →ₗ[K] L)) hfg
          have h' := congrFun (congrArg DFunLike.coe h1) φ
          have h'' := congrArg Subtype.val h'
          change (proj f) φ = (proj g) φ at h''
          simpa [proj] using h''
        have hfin : Module.finrank K ↥(LinearMap.ker postEq) ≤
            Module.finrank K ↥(mapsKillingAug T L) :=
          LinearMap.finrank_le_finrank_of_injective hkerMap_inj
        rw [finrank_maps_killing_augDual T L, hLdim, mul_one] at hfin
        exact hfin
      have hrange_le : Module.finrank K ↥(LinearMap.range postEq) ≤
          Module.finrank K ↥(equivariantHom T S') := by
        have hle := Submodule.finrank_mono
          (show LinearMap.range postEq ≤ (⊤ : Submodule K ↥(equivariantHom T S')) from le_top)
        simpa using hle
      have hrank := LinearMap.finrank_range_add_finrank_ker (K := K)
        (V := ↥(equivariantHom T S)) (V₂ := ↥(equivariantHom T S')) postEq
      have hIH' : Module.finrank K ↥(equivariantHom T S') ≤
          Module.finrank K (iterFixed T r) * (n - 1) := by
        rwa [hQdim] at hIH
      calc
        Module.finrank K ↥(equivariantHom T S)
            = Module.finrank K ↥(LinearMap.range postEq) +
                Module.finrank K ↥(LinearMap.ker postEq) := by omega
        _ ≤ Module.finrank K ↥(equivariantHom T S') +
              Module.finrank K (iterFixed T r) :=
            Nat.add_le_add hrange_le hker_le
        _ ≤ Module.finrank K (iterFixed T r) * (n - 1) +
              Module.finrank K (iterFixed T r) :=
            Nat.add_le_add hIH' (le_refl _)
        _ = Module.finrank K (iterFixed T r) * n := by
            have hn1 : n = (n - 1) + 1 :=
              (Nat.succ_pred_eq_of_pos (by omega)).symm
            conv_rhs => rw [hn1]
            rw [Nat.mul_add, Nat.mul_one]
        _ = Module.finrank K (iterFixed T r) * Module.finrank K W := by
            rw [hWdim]


theorem finrank_tensorFixed_le_equivariantHom {V W : Type*} [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] [AddCommGroup W] [Module K W] [FiniteDimensional K W]
    {r : ℕ} (T : Fin r → V ≃ₗ[K] V) (S : Fin r → W ≃ₗ[K] W)
    (hS2 : ∀ i, S i * S i = 1) :
    Module.finrank K (tensorFixed T S) ≤
      Module.finrank K (equivariantHom T S) := by
  let f : ↥(tensorFixed T S) →ₗ[K] ↥(equivariantHom T S) :=
    { toFun := fun t => ⟨contract t.1,
        contract_mem_equivariantHom r T S hS2 t.1 t.2⟩
      map_add' := by
        intro t u
        apply Subtype.ext
        change contract (t.1 + u.1) = contract t.1 + contract u.1
        rw [map_add]
      map_smul' := by
        intro a t
        apply Subtype.ext
        change contract (a • t.1) = a • contract t.1
        rw [map_smul] }
  have hf : Function.Injective f := by
    intro t u htu
    apply Subtype.ext
    apply contract_injective
    have h := congrArg
      (fun x : ↥(equivariantHom T S) => (x : Module.Dual K V →ₗ[K] W)) htu
    simpa [f] using h
  exact LinearMap.finrank_le_finrank_of_injective hf

theorem finrank_fixed_tensor_le_zm_elemAbelian {K V W : Type*} [Field K] [CharP K 2]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    [AddCommGroup W] [Module K W] [FiniteDimensional K W]
    {r : ℕ} (T : Fin r → V ≃ₗ[K] V) (S : Fin r → W ≃ₗ[K] W)
    (hT2 : ∀ i, T i * T i = 1) (hTc : ∀ i j, T i * T j = T j * T i)
    (hS2 : ∀ i, S i * S i = 1) (hSc : ∀ i j, S i * S j = S j * S i) :
    Module.finrank K (tensorFixed T S) ≤
      Module.finrank K (iterFixed T r) * Module.finrank K W :=
  (finrank_tensorFixed_le_equivariantHom T S hS2).trans
    (finrank_equivariantHom_le T (Module.finrank K W) W rfl S hS2 hSc)


end CFSG.HardMathSupport.GuralnickMalle
