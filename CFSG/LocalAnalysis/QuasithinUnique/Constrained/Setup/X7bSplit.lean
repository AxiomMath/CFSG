module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7bSquare
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7bDistinct
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesFaithful

public section

namespace CFSG.QuasithinUnique.Setup.X7b

open scoped MonoidAlgebra TensorProduct
open CFSG.Semidihedral.Principal Representation Matrix
open CFSG.ComponentClassification.UnbalancedCatalog.SpChain

section Bridge

open CFSG.QuasithinUnique.Setup.X7 (matRep MatIso matIso_of_reindex)

variable {k G : Type} [Field k] [Group G] {ι₁ ι₂ : Type} [Fintype ι₁] [Fintype ι₂]
  [DecidableEq ι₁] [DecidableEq ι₂]

@[expose] def kronRep (R₁ : G →* Matrix ι₁ ι₁ k) (R₂ : G →* Matrix ι₂ ι₂ k) :
    G →* Matrix (ι₁ × ι₂) (ι₁ × ι₂) k where
  toFun g := Matrix.kroneckerMap (· * ·) (R₁ g) (R₂ g)
  map_one' := by
    rw [map_one, map_one]
    exact Matrix.one_kronecker_one
  map_mul' g h := by
    rw [map_mul, map_mul]
    exact Matrix.mul_kronecker_mul _ _ _ _

@[expose] noncomputable def tprodCoord : ((ι₁ → k) ⊗[k] (ι₂ → k)) ≃ₗ[k] (ι₁ × ι₂ → k) :=
  ((Pi.basisFun k ι₁).tensorProduct (Pi.basisFun k ι₂)).equivFun

omit [DecidableEq ι₁] [DecidableEq ι₂] in
theorem tprodCoord_tmul (x : ι₁ → k) (y : ι₂ → k) (a : ι₁) (b : ι₂) :
    tprodCoord (x ⊗ₜ[k] y) (a, b) = x a * y b := by
  simp [tprodCoord, Module.Basis.equivFun_apply, Module.Basis.tensorProduct_repr_tmul_apply,
    mul_comm]

@[expose] noncomputable def tprodKronEquiv (R₁ : G →* Matrix ι₁ ι₁ k) (R₂ : G →* Matrix ι₂ ι₂ k) :
    Representation.Equiv (tprod (matRep R₁) (matRep R₂)) (matRep (kronRep R₁ R₂)) :=
  Representation.Equiv.mk tprodCoord (fun g => by
    refine TensorProduct.ext' fun x y => ?_
    ext ⟨a, b⟩
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, tprod_apply, TensorProduct.map_tmul,
      tprodCoord_tmul, CFSG.QuasithinUnique.Setup.X7.matRep_apply, kronRep, MonoidHom.coe_mk,
      OneHom.coe_mk, Matrix.mulVec, dotProduct, Matrix.kroneckerMap_apply, Fintype.sum_prod_type]
    rw [Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun a' _ => Finset.sum_congr rfl fun b' _ => ?_
    ring)

theorem tprodKron_nonempty (R₁ : G →* Matrix ι₁ ι₁ k) (R₂ : G →* Matrix ι₂ ι₂ k) :
    Nonempty (Representation.Equiv (tprod (matRep R₁) (matRep R₂)) (matRep (kronRep R₁ R₂))) :=
  ⟨tprodKronEquiv R₁ R₂⟩

end Bridge

section Insert

open CFSG.QuasithinUnique.Setup.X7 (matRep MatIso matIso_of_reindex)

variable {F : Type} [Field F] [CharP F 2] [Finite F] (k : Type) [Field k] [Algebra F k]

def extZero (S : Finset ℕ) (x : ↥S → Fin 4) : ℕ → Fin 4 := fun j =>
  if h : j ∈ S then x ⟨j, h⟩ else 0

theorem tensorRepS_apply_ext (S : Finset ℕ) (g : antiSp F) (x' x : ↥S → Fin 4) :
    tensorRepS k S g x' x = ∏ j ∈ S, natRepS k j g (extZero S x' j) (extZero S x j) := by
  rw [tensorRepS_apply, ← Finset.prod_coe_sort S]
  refine Finset.prod_congr rfl fun j _ => ?_
  simp [extZero, j.2]

@[expose] def insertSplit (A : Finset ℕ) {i : ℕ} (hi : i ∉ A) :
    (↥(insert i A) → Fin 4) ≃ (↥A → Fin 4) × Fin 4 where
  toFun x := (fun j => x ⟨j.1, Finset.mem_insert_of_mem j.2⟩, x ⟨i, Finset.mem_insert_self i A⟩)
  invFun y := fun j => if h : j.1 = i then y.2 else
    y.1 ⟨j.1, (Finset.mem_insert.mp j.2).resolve_left h⟩
  left_inv x := by
    funext j
    by_cases h : j.1 = i
    · have : j = ⟨i, Finset.mem_insert_self i A⟩ := Subtype.ext h
      subst this
      simp
    · simp [h]
  right_inv y := by
    refine Prod.ext (funext fun j => ?_) ?_
    · have h : j.1 ≠ i := fun h => hi (h ▸ j.2)
      simp [h]
    · simp

theorem tensorRepS_insert_apply {A : Finset ℕ} {i : ℕ} (hi : i ∉ A) (g : antiSp F)
    (x' x : ↥(insert i A) → Fin 4) :
    tensorRepS k (insert i A) g x' x =
      tensorRepS k A g (insertSplit A hi x').1 (insertSplit A hi x).1 *
        natRepS k i g (insertSplit A hi x').2 (insertSplit A hi x).2 := by
  rw [tensorRepS_apply_ext, tensorRepS_apply_ext, Finset.prod_insert hi, mul_comm]
  congr 1
  · refine Finset.prod_congr rfl fun j hj => ?_
    have hj' : j ∈ insert i A := Finset.mem_insert_of_mem hj
    simp [extZero, insertSplit, hj, hj']
  · simp [extZero, insertSplit]

theorem tensorInsert_nonempty {A : Finset ℕ} {i : ℕ} (hi : i ∉ A) :
    Nonempty (Representation.Equiv
      (tprod (matRep (tensorRepS (F := F) k A)) (matRep (natRepS (F := F) k i)))
      (matRep (tensorRepS (F := F) k (insert i A)))) := by
  obtain ⟨e₂⟩ := (matIso_of_reindex (R := kronRep (tensorRepS (F := F) k A) (natRepS (F := F) k i))
    (R' := tensorRepS (F := F) k (insert i A)) (insertSplit A hi).symm (fun g x' x => by
      rw [tensorRepS_insert_apply k hi]
      simp [kronRep, Equiv.apply_symm_apply])).equiv
  exact ⟨(tprodKronEquiv _ _).trans e₂⟩

end Insert

section Pow

open CFSG.QuasithinUnique.Setup.X7 (matRep MatIso matIso_of_reindex)
open CFSG.QuasithinUnique.Setup.X7a (kron kron_apply kron_mul kron_one)
open CFSG.QuasithinUnique.Setup.SL2Modules (powMat powMat_mul)

variable {F : Type} [Field F] [CharP F 2] [Finite F] (k : Type) [Field k] [Algebra F k]

theorem powMat_eq_kron {d : ℕ} (B : Matrix (Fin d) (Fin d) k) (m : ℕ) :
    powMat B m = kron (fun _ : Fin m => B) := rfl

@[expose] noncomputable def powRep (m : ℕ) :
    antiSp F →* Matrix (Fin m → Fin 4) (Fin m → Fin 4) k where
  toFun g := powMat (natRepS k 0 g) m
  map_one' := by
    rw [map_one, powMat_eq_kron]
    exact kron_one
  map_mul' g h := by
    rw [map_mul, powMat_mul]

theorem powRep_succ_nonempty (m : ℕ) :
    Nonempty (Representation.Equiv
      (tprod (matRep (powRep (F := F) k m)) (matRep (natRepS (F := F) k 0)))
      (matRep (powRep (F := F) k (m + 1)))) := by
  let e : ((Fin m → Fin 4) × Fin 4) ≃ (Fin (m + 1) → Fin 4) :=
    { toFun := fun y => Fin.snoc y.1 y.2
      invFun := fun x => (Fin.init x, x (Fin.last m))
      left_inv := fun y => by simp
      right_inv := fun x => by simp }
  obtain ⟨e₂⟩ := (matIso_of_reindex (R := kronRep (powRep (F := F) k m) (natRepS (F := F) k 0))
    (R' := powRep (F := F) k (m + 1)) e (fun g x' x => by
      simp only [powRep, kronRep, MonoidHom.coe_mk, OneHom.coe_mk, powMat, Matrix.kroneckerMap_apply,
        e, Equiv.coe_fn_mk, Fin.prod_univ_castSucc, Fin.snoc_castSucc, Fin.snoc_last])).equiv
  exact ⟨(tprodKronEquiv _ _).trans e₂⟩

theorem powRep_zero_nonempty :
    Nonempty (Representation.Equiv (matRep (powRep (F := F) k 0))
      (matRep (tensorRepS (F := F) k (∅ : Finset ℕ)))) := by
  have hu1 : Unique (Fin 0 → Fin 4) := Pi.uniqueOfIsEmpty _
  have hu2 : Unique (↥(∅ : Finset ℕ) → Fin 4) := Pi.uniqueOfIsEmpty _
  exact (matIso_of_reindex (R := powRep (F := F) k 0) (R' := tensorRepS (F := F) k ∅)
    (Equiv.ofUnique _ _) (fun g x' x => by
      have h1 : Equiv.ofUnique (Fin 0 → Fin 4) (↥(∅ : Finset ℕ) → Fin 4) x' =
        Equiv.ofUnique (Fin 0 → Fin 4) (↥(∅ : Finset ℕ) → Fin 4) x :=
          Subsingleton.elim _ _
      have := Fintype.ofFinite F
      rw [h1, tensorRepS_empty, Matrix.one_apply_eq]
      simp [powRep, powMat])).equiv

end Pow

section OnlyT

open CFSG.QuasithinUnique.Setup.X7 (matRep)

variable {F : Type} [Field F] [CharP F 2] [Fintype F] (k : Type) [Field k] [Algebra F k]
  [CharP k 2] (f : ℕ)

@[expose] def OnlyT {V : Type} [AddCommGroup V] [Module k V]
    (ρ : Representation k (antiSp F) V) : Prop :=
  ∀ (E : Type) [AddCommGroup E] [Module k E] [Module.Finite k E]
    (σ : Representation k (antiSp F) E), σ.IsIrreducible → 0 < repMultiplicity ρ σ →
      ∃ A : Finset ℕ, A ⊆ Finset.range (2 * f) ∧
        Nonempty (Representation.Equiv (matRep (tensorRepS (F := F) k A)) σ)

variable {k f}

omit [CharP k 2] in
theorem OnlyT.congr {V V' : Type} [AddCommGroup V] [Module k V] [AddCommGroup V'] [Module k V']
    {ρ : Representation k (antiSp F) V} {ρ' : Representation k (antiSp F) V'}
    (e : Representation.Equiv ρ ρ') (h : OnlyT (F := F) k f ρ) : OnlyT (F := F) k f ρ' := by
  intro E _ _ _ σ hσ hpos
  exact h _ σ hσ (by rwa [repMultiplicity_congr_left e σ])

omit [CharP k 2] in
theorem OnlyT.of_subsingleton {V : Type} [AddCommGroup V] [Module k V] [Subsingleton V]
    (ρ : Representation k (antiSp F) V) : OnlyT (F := F) k f ρ := by
  intro E _ _ _ σ hσ hpos
  exfalso
  have : Subsingleton (Representation.asModule ρ) := inferInstanceAs (Subsingleton V)
  unfold repMultiplicity at hpos
  rw [compositionMultiplicity_of_subsingleton] at hpos
  exact lt_irrefl _ hpos

theorem onlyT_T (hF : Fintype.card F = 2 ^ f) {A : Finset ℕ} (hA : A ⊆ Finset.range (2 * f)) :
    OnlyT (F := F) k f (matRep (tensorRepS (F := F) k A)) := by
  intro E _ _ _ σ hσ hpos
  rw [repMultiplicity_of_isIrreducible (tensorRepS_fixed_irreducible k hF hA).2 σ] at hpos
  by_cases h : Nonempty (Representation.Equiv (matRep (tensorRepS (F := F) k A)) σ)
  · exact ⟨A, hA, h⟩
  · simp [h] at hpos

omit [CharP k 2] in
theorem OnlyT.sub_quot {V : Type} [AddCommGroup V] [Module k V] [Module.Finite k V]
    {ρ : Representation k (antiSp F) V} (h : OnlyT (F := F) k f ρ) (W : Subrepresentation ρ) :
    OnlyT (F := F) k f W.toRepresentation ∧ OnlyT (F := F) k f W.quotient := by
  constructor
  · intro E _ _ _ σ hσ hpos
    apply h _ σ hσ
    rw [repMultiplicity_sub_quot ρ W σ]
    omega
  · intro E _ _ _ σ hσ hpos
    apply h _ σ hσ
    rw [repMultiplicity_sub_quot ρ W σ]
    omega

omit [CharP k 2] in
theorem OnlyT.of_sub_quot {V : Type} [AddCommGroup V] [Module k V] [Module.Finite k V]
    {ρ : Representation k (antiSp F) V} (W : Subrepresentation ρ)
    (h1 : OnlyT (F := F) k f W.toRepresentation) (h2 : OnlyT (F := F) k f W.quotient) :
    OnlyT (F := F) k f ρ := by
  intro E _ _ _ σ hσ hpos
  rw [repMultiplicity_sub_quot ρ W σ] at hpos
  by_cases ha : 0 < repMultiplicity W.toRepresentation σ
  · exact h1 _ σ hσ ha
  · exact h2 _ σ hσ (by omega)

omit [CharP k 2] in
theorem OnlyT.of_flag {V : Type} [AddCommGroup V] [Module k V] [Module.Finite k V]
    {ρ : Representation k (antiSp F) V} (L : List (FRep k (antiSp F))) (hL : FlagTop ρ L)
    (h : ∀ Q ∈ L, OnlyT (F := F) k f Q.ρ) : OnlyT (F := F) k f ρ := by
  intro E _ _ _ σ hσ hpos
  rw [FlagTop.mult L ρ hL σ] at hpos
  have : ∃ Q ∈ L, 0 < repMultiplicity Q.ρ σ := by
    by_contra hcon
    push Not at hcon
    have : (L.map fun Q => repMultiplicity Q.ρ σ).sum = 0 := by
      apply List.sum_eq_zero
      intro a ha
      obtain ⟨Q, hQ, rfl⟩ := List.mem_map.mp ha
      exact Nat.le_zero.mp (hcon Q hQ)
    omega
  obtain ⟨Q, hQ, hpos'⟩ := this
  exact h Q hQ _ σ hσ hpos'

omit [CharP F 2] [Fintype F] [Algebra F k] [CharP k 2] in
theorem repMultiplicity_tprod_sub_quot {V : Type} [AddCommGroup V] [Module k V] [Module.Finite k V]
    {ρ : Representation k (antiSp F) V} (W : Subrepresentation ρ) {X : Type} [AddCommGroup X]
    [Module k X] [Module.Finite k X] (τ : Representation k (antiSp F) X) {E : Type}
    [AddCommGroup E] [Module k E] (σ : Representation k (antiSp F) E) :
    repMultiplicity (tprod ρ τ) σ = repMultiplicity (tprod W.toRepresentation τ) σ +
      repMultiplicity (tprod W.quotient τ) σ := by
  have : Module.Finite k (W.toSubmodule ⊗[k] X) := inferInstance
  have : Module.Finite k ((V ⧸ W.toSubmodule) ⊗[k] X) := inferInstance
  refine repMultiplicity_eq_add_of_exact (IntertwiningMap.rTensor τ (subIncl ρ W))
    (IntertwiningMap.rTensor τ (quotProj ρ W)) ?_ ?_ ?_ σ
  · exact Module.Flat.rTensor_preserves_injective_linearMap (M := X) (subIncl ρ W).toLinearMap
      W.toSubmodule.injective_subtype
  · exact LinearMap.rTensor_surjective X W.toSubmodule.mkQ_surjective
  · exact Module.Flat.rTensor_exact X (LinearMap.exact_subtype_mkQ W.toSubmodule)

@[expose] noncomputable def equivRTensor {V V' X : Type} [AddCommGroup V] [Module k V]
    [AddCommGroup V'] [Module k V'] [AddCommGroup X] [Module k X]
    {ρ : Representation k (antiSp F) V} {ρ' : Representation k (antiSp F) V'}
    (e : Representation.Equiv ρ ρ') (τ : Representation k (antiSp F) X) :
    Representation.Equiv (tprod ρ τ) (tprod ρ' τ) :=
  Representation.Equiv.mk (LinearEquiv.rTensor X e.toLinearEquiv) (fun g => by
    refine TensorProduct.ext' fun v w => ?_
    simp only [LinearMap.comp_apply, tprod_apply, TensorProduct.map_tmul, LinearEquiv.coe_coe,
      LinearEquiv.rTensor_tmul]
    have h : e.toLinearEquiv (ρ g v) = ρ' g (e.toLinearEquiv v) :=
      IntertwiningMap.isIntertwining ρ ρ' e.toIntertwiningMap g v
    rw [h])

omit [CharP k 2] in
theorem natRepS_add_mul (hF : Fintype.card F = 2 ^ f) (j q : ℕ) (g : antiSp F) :
    natRepS (F := F) k (j + 2 * f * q) g = natRepS (F := F) k j g := by
  induction q with
  | zero => simp
  | succ q ih =>
    rw [show j + 2 * f * (q + 1) = (j + 2 * f * q) + 2 * f by ring, natRepS_add_two_mul k hF, ih]

omit [CharP k 2] in
theorem natRepS_mod (hF : Fintype.card F = 2 ^ f) (i : ℕ) (g : antiSp F) :
    natRepS (F := F) k i g = natRepS (F := F) k (i % (2 * f)) g := by
  conv_lhs => rw [← Nat.mod_add_div i (2 * f)]
  exact natRepS_add_mul (k := k) hF _ _ g

theorem onlyT_tprod_T (hF : Fintype.card F = 2 ^ f) (hf : 1 ≤ f) :
    ∀ (n : ℕ) (B : Finset ℕ), B ⊆ Finset.range (2 * f) → B.card = n → ∀ i : ℕ,
      OnlyT (F := F) k f
        (tprod (matRep (tensorRepS (F := F) k B)) (matRep (natRepS (F := F) k i))) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro B hB hcard i
    have hlt : i % (2 * f) < 2 * f := Nat.mod_lt _ (by omega)
    have main : ∀ j : ℕ, j < 2 * f → OnlyT (F := F) k f
        (tprod (matRep (tensorRepS (F := F) k B)) (matRep (natRepS (F := F) k j))) := by
      intro j hlt
      by_cases hmem : j ∈ B
      ·
        set B' := B.erase j with hB'def
        have hB' : insert j B' = B := Finset.insert_erase hmem
        have hnot : j ∉ B' := Finset.notMem_erase j B
        have hB'sub : B' ⊆ Finset.range (2 * f) := (Finset.erase_subset j B).trans hB
        have hcard' : B'.card < n := by
          have hc : B'.card = B.card - 1 := Finset.card_erase_of_mem hmem
          have h1 : 0 < B.card := Finset.card_pos.mpr ⟨j, hmem⟩
          omega
        obtain ⟨eA⟩ := tensorInsert_nonempty (F := F) k hnot
        rw [hB'] at eA
        let N := matRep (natRepS (F := F) k j)
        let T' := matRep (tensorRepS (F := F) k B')
        let X : FRep k (antiSp F) := ⟨(B' → Fin 4) → k, T'⟩
        have hflag := FlagTop.tensor _ (tprod N N) (fundamental_tensor_square_filtration (F := F) k j) X
        have hT' : OnlyT (F := F) k f T' := onlyT_T (k := k) hF hB'sub
        refine OnlyT.congr ((Representation.TensorProduct.comm (tprod N N) T').trans
          ((Representation.TensorProduct.assoc T' N N).symm.trans (equivRTensor eA N)))
          (OnlyT.of_flag _ hflag ?_)
        intro Q hQ
        simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hQ
        rcases hQ with rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · exact OnlyT.congr (Representation.TensorProduct.lid k T').symm hT'
        · exact OnlyT.congr (Representation.TensorProduct.comm T' _)
            (ih _ hcard' B' hB'sub rfl (j + 1))
        · exact OnlyT.congr (Representation.TensorProduct.lid k T').symm hT'
        · exact OnlyT.congr (Representation.TensorProduct.comm T' _)
            (ih _ hcard' B' hB'sub rfl (j + 2))
        · exact OnlyT.congr (Representation.TensorProduct.lid k T').symm hT'
        · exact OnlyT.congr (Representation.TensorProduct.comm T' _)
            (ih _ hcard' B' hB'sub rfl (j + 1))
        · exact OnlyT.congr (Representation.TensorProduct.lid k T').symm hT'
      · obtain ⟨e⟩ := tensorInsert_nonempty (F := F) k hmem
        exact OnlyT.congr e.symm
          (onlyT_T (k := k) hF (Finset.insert_subset (Finset.mem_range.mpr hlt) hB))
    have e : Representation.Equiv
        (tprod (matRep (tensorRepS (F := F) k B)) (matRep (natRepS (F := F) k (i % (2 * f)))))
        (tprod (matRep (tensorRepS (F := F) k B)) (matRep (natRepS (F := F) k i))) :=
      Representation.Equiv.mk (LinearEquiv.refl k _) (fun g => by
        have h : matRep (natRepS (F := F) k i) g = matRep (natRepS (F := F) k (i % (2 * f))) g := by
          show Matrix.mulVecLin _ = Matrix.mulVecLin _
          rw [natRepS_mod (k := k) hF i g]
        simp only [tprod_apply, h]
        rfl)
    have hmain : OnlyT (F := F) k f
        (tprod (matRep (tensorRepS (F := F) k B)) (matRep (natRepS (F := F) k (i % (2 * f))))) :=
      main (i % (2 * f)) hlt
    exact OnlyT.congr e hmain

theorem onlyT_tprod_N (hF : Fintype.card F = 2 ^ f) (hf : 1 ≤ f) {V : Type} [AddCommGroup V]
    [Module k V] [Module.Finite k V] (ρ : Representation k (antiSp F) V)
    (hρ : OnlyT (F := F) k f ρ) (i : ℕ) :
    OnlyT (F := F) k f (tprod ρ (matRep (natRepS (F := F) k i))) := by
  have key := rep_induction (k := k) (G := antiSp F)
    (fun {V} _ _ _ ρ => OnlyT (F := F) k f ρ → ∀ i : ℕ,
      OnlyT (F := F) k f (tprod ρ (matRep (natRepS (F := F) k i))))
    (fun {V} _ _ _ ρ hsub _ i => by
      have h1 : Subsingleton V := hsub
      have : Subsingleton (V ⊗[k] (Fin 4 → k)) := by
        refine subsingleton_of_forall_eq 0 fun t => ?_
        induction t using TensorProduct.inductionOn with
        | tmul m n => rw [Subsingleton.elim m 0, TensorProduct.zero_tmul]
        | add x y hx hy => rw [hx, hy, add_zero]
      exact OnlyT.of_subsingleton _)
    (fun {V} _ _ _ ρ hirr hρ i => by
      have hpos : 0 < repMultiplicity ρ ρ := by
        rw [repMultiplicity_of_isIrreducible hirr ρ]
        have : Nonempty (Representation.Equiv ρ ρ) := ⟨Representation.Equiv.refl ρ⟩
        simp [this]
      obtain ⟨B, hB, ⟨e⟩⟩ := hρ V ρ hirr hpos
      exact OnlyT.congr (equivRTensor e _) (onlyT_tprod_T hF hf B.card B hB rfl i))
    (fun {V} _ _ _ ρ W hW1 hW2 hρ i => by
      obtain ⟨h1, h2⟩ := hρ.sub_quot W
      have hA := hW1 h1 i
      have hB := hW2 h2 i
      intro E _ _ _ σ hσ hpos
      rw [repMultiplicity_tprod_sub_quot W (matRep (natRepS (F := F) k i)) σ] at hpos
      by_cases ha : 0 < repMultiplicity (tprod W.toRepresentation
          (matRep (natRepS (F := F) k i))) σ
      · exact hA E σ hσ ha
      · exact hB E σ hσ (by omega))
  exact key _ ρ rfl hρ i

theorem onlyT_powRep (hF : Fintype.card F = 2 ^ f) (hf : 1 ≤ f) (m : ℕ) :
    OnlyT (F := F) k f (matRep (powRep (F := F) k m)) := by
  induction m with
  | zero =>
    exact OnlyT.congr (powRep_zero_nonempty (F := F) k).some.symm
      (onlyT_T (k := k) hF (Finset.empty_subset _))
  | succ m ih =>
    exact OnlyT.congr (powRep_succ_nonempty (F := F) k m).some
      (onlyT_tprod_N hF hf _ ih 0)

omit [CharP k 2] in
theorem natRepS_zero_injective : Function.Injective (natRepS (F := F) k 0) := by
  intro g h hgh
  have h1 : (glMat (g : GL (Fin 4) F)).map (algebraMap F k) =
      (glMat (h : GL (Fin 4) F)).map (algebraMap F k) := by
    simpa [natRepS_apply] using hgh
  have h2 : glMat (g : GL (Fin 4) F) = glMat (h : GL (Fin 4) F) := by
    ext i j
    exact (algebraMap F k).injective (congrFun (congrFun h1 i) j)
  exact Subtype.ext (Units.ext h2)

theorem exists_T_equiv (hF : Fintype.card F = 2 ^ f) (hf : 1 ≤ f) {E : Type} [AddCommGroup E]
    [Module k E] [Module.Finite k E] (σ : Representation k (antiSp F) E)
    (hσ : σ.IsIrreducible) :
    ∃ A : Finset ℕ, A ⊆ Finset.range (2 * f) ∧
      Nonempty (Representation.Equiv (matRep (tensorRepS (F := F) k A)) σ) := by
  classical
  obtain ⟨m, -, φ, hφ, hcomm⟩ := CFSG.QuasithinUnique.Setup.SL2Modules.faithful_tensor_power
    (by norm_num : 0 < 4) (natRepS (F := F) k 0) (natRepS_zero_injective (k := k)) σ hσ
  let Φ : IntertwiningMap (matRep (powRep (F := F) k m)) σ :=
    ⟨φ, fun g => by
      refine LinearMap.ext fun v => ?_
      exact hcomm g v⟩
  have hex : Function.Exact (subIncl (matRep (powRep (F := F) k m))
      (IntertwiningMap.ker (matRep (powRep (F := F) k m)) σ Φ)) Φ := by
    intro y
    constructor
    · intro hy
      exact ⟨⟨y, hy⟩, rfl⟩
    · rintro ⟨⟨z, hz⟩, rfl⟩
      exact hz
  have hpos : 0 < repMultiplicity (matRep (powRep (F := F) k m)) σ := by
    rw [repMultiplicity_eq_add_of_exact (subIncl _
      (IntertwiningMap.ker (matRep (powRep (F := F) k m)) σ Φ)) Φ
      (IntertwiningMap.ker (matRep (powRep (F := F) k m)) σ Φ).toSubmodule.injective_subtype hφ hex σ,
      repMultiplicity_of_isIrreducible hσ σ]
    have : Nonempty (Representation.Equiv σ σ) := ⟨Representation.Equiv.refl σ⟩
    simp [this]
  exact onlyT_powRep hF hf m E σ hσ hpos

omit [CharP F 2] [Fintype F] [Algebra F k] [CharP k 2] in
theorem finrank_eq_one_of_trivial {E : Type} [AddCommGroup E] [Module k E]
    (σ : Representation k (antiSp F) E) (hσ : σ.IsIrreducible) (htriv : ∀ g v, σ g v = v) :
    Module.finrank k E = 1 := by
  have : IsSimpleOrder (Subrepresentation σ) := hσ
  have hne : ∃ v : E, v ≠ 0 := by
    by_contra h
    push Not at h
    apply (bot_ne_top : (⊥ : Subrepresentation σ) ≠ ⊤)
    apply Subrepresentation.toSubmodule_injective
    ext x
    simp [h x]
  obtain ⟨v, hv⟩ := hne
  let S : Subrepresentation σ := ⟨Submodule.span k {v}, fun g w hw => by rw [htriv]; exact hw⟩
  rcases eq_bot_or_eq_top S with h | h
  · exfalso
    have : v ∈ S.toSubmodule := Submodule.mem_span_singleton_self v
    rw [h] at this
    exact hv ((Submodule.mem_bot k).mp this)
  · have h' : Submodule.span k {v} = ⊤ := congrArg Subrepresentation.toSubmodule h
    rw [← finrank_top k E, ← h']
    exact finrank_span_singleton hv

theorem split_simple_module_production (hF : Fintype.card F = 2 ^ f) (hf : 1 ≤ f) {E : Type}
    [AddCommGroup E] [Module k E] [Module.Finite k E] (σ : Representation k (antiSp F) E)
    (hσ : σ.IsIrreducible) :
    (∃! A : Finset ℕ, A ⊆ Finset.range (2 * f) ∧
        Nonempty (Representation.Equiv (matRep (tensorRepS (F := F) k A)) σ)) ∧
      ∀ A : Finset ℕ, A ⊆ Finset.range (2 * f) →
        Nonempty (Representation.Equiv (matRep (tensorRepS (F := F) k A)) σ) →
          Module.finrank k E = 4 ^ A.card ∧ (A = ∅ ↔ ∀ g v, σ g v = v) := by
  refine ⟨?_, fun A hA ⟨e⟩ => ?_⟩
  · obtain ⟨A, hA, he⟩ := exists_T_equiv (k := k) hF hf σ hσ
    refine ⟨A, ⟨hA, he⟩, fun B ⟨hB, ⟨e'⟩⟩ => ?_⟩
    obtain ⟨e⟩ := he
    exact ((tensorRepS_absolutely_irreducible_and_distinct (k := k) hF hf).2 B hB A hA
      ⟨e'.trans e.symm⟩)
  · have hdim : Module.finrank k E = 4 ^ A.card := by
      rw [← e.toLinearEquiv.finrank_eq, finrank_tensorRepS]
    refine ⟨hdim, ⟨fun hA0 g v => ?_, fun htriv => ?_⟩⟩
    · subst hA0
      have h1 : ∀ w, e (matRep (tensorRepS (F := F) k ∅) g w) = σ g (e w) := fun w =>
        IntertwiningMap.isIntertwining _ _ e.toIntertwiningMap g w
      have h2 : matRep (tensorRepS (F := F) k ∅) g = LinearMap.id := by
        refine LinearMap.ext fun w => ?_
        rw [CFSG.QuasithinUnique.Setup.X7.matRep_apply, tensorRepS_empty]
        simp
      have := h1 (e.symm v)
      rw [h2] at this
      simpa using this.symm
    · have h1 := finrank_eq_one_of_trivial (k := k) σ hσ htriv
      rw [hdim] at h1
      have : A.card = 0 := by
        rcases Nat.pow_eq_one.mp h1 with h | h
        · omega
        · exact h
      exact Finset.card_eq_zero.mp this

end OnlyT

end CFSG.QuasithinUnique.Setup.X7b
