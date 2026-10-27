module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7aSquare
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7aIrred
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7bSplit

public section

namespace CFSG.QuasithinUnique.Setup.X7a

open scoped MatrixGroups Matrix TensorProduct

open CFSG.Semidihedral.Principal

section Tprod

variable {G : Type} [Group G] {k : Type} [Field k]

@[expose] noncomputable def eqR {V V' X : Type} [AddCommGroup V] [Module k V] [AddCommGroup V']
    [Module k V'] [AddCommGroup X] [Module k X] {ρ : Representation k G V}
    {ρ' : Representation k G V'} (e : Representation.Equiv ρ ρ') (τ : Representation k G X) :
    Representation.Equiv (Representation.tprod ρ τ) (Representation.tprod ρ' τ) :=
  Representation.Equiv.mk (LinearEquiv.rTensor X e.toLinearEquiv) (fun g => by
    refine TensorProduct.ext' fun v w => ?_
    simp only [LinearMap.comp_apply, Representation.tprod_apply, TensorProduct.map_tmul,
      LinearEquiv.coe_coe, LinearEquiv.rTensor_tmul]
    have h : e.toLinearEquiv (ρ g v) = ρ' g (e.toLinearEquiv v) :=
      Representation.IntertwiningMap.isIntertwining ρ ρ' e.toIntertwiningMap g v
    rw [h])

@[expose] noncomputable def eqL {V V' X : Type} [AddCommGroup V] [Module k V] [AddCommGroup V']
    [Module k V'] [AddCommGroup X] [Module k X] {σ : Representation k G V}
    {σ' : Representation k G V'} (ρ : Representation k G X) (e : Representation.Equiv σ σ') :
    Representation.Equiv (Representation.tprod ρ σ) (Representation.tprod ρ σ') :=
  (Representation.TensorProduct.comm ρ σ).trans
    ((eqR e ρ).trans (Representation.TensorProduct.comm σ' ρ))

@[expose] noncomputable def swapMid {V₁ V₂ V₃ V₄ : Type} [AddCommGroup V₁] [Module k V₁]
    [AddCommGroup V₂] [Module k V₂] [AddCommGroup V₃] [Module k V₃] [AddCommGroup V₄]
    [Module k V₄] (ρ : Representation k G V₁) (σ : Representation k G V₂)
    (τ : Representation k G V₃) (υ : Representation k G V₄) :
    Representation.Equiv (Representation.tprod (Representation.tprod ρ σ) (Representation.tprod τ υ))
      (Representation.tprod (Representation.tprod ρ τ) (Representation.tprod σ υ)) :=
  ((((Representation.TensorProduct.assoc ρ σ (Representation.tprod τ υ)).trans
    (eqL ρ (Representation.TensorProduct.assoc σ τ υ).symm)).trans
    (eqL ρ (eqR (Representation.TensorProduct.comm σ τ) υ))).trans
    (eqL ρ (Representation.TensorProduct.assoc τ σ υ))).trans
    (Representation.TensorProduct.assoc ρ τ (Representation.tprod σ υ)).symm

end Tprod

section OnlyT

open CFSG.QuasithinUnique.Setup.X7 (matRep matRep_apply)
open CFSG.QuasithinUnique.Setup.X7b (FRep FlagTop subIncl quotProj repMultiplicity_sub_quot)

variable {F : Type} [Field F] [CharP F 2] [Fintype F] (k : Type) [Field k] [Algebra F k]
  [CharP k 2] (f : ℕ)

@[expose] def OnlyT3 {V : Type} [AddCommGroup V] [Module k V]
    (ρ : Representation k SL(3, F) V) : Prop :=
  ∀ (E : Type) [AddCommGroup E] [Module k E] [Module.Finite k E]
    (σ : Representation k SL(3, F) E), σ.IsIrreducible → 0 < repMultiplicity ρ σ →
      ∃ a b : Fin f → Bool,
        Nonempty (Representation.Equiv (matRep (tensorRep (F := F) k a b)) σ)

variable {k f}

omit [CharP F 2] [Fintype F] in
theorem OnlyT3.congr {V V' : Type} [AddCommGroup V] [Module k V] [AddCommGroup V']
    [Module k V'] {ρ : Representation k SL(3, F) V} {ρ' : Representation k SL(3, F) V'}
    (e : Representation.Equiv ρ ρ') (h : OnlyT3 (F := F) k f ρ) : OnlyT3 (F := F) k f ρ' := by
  intro E _ _ _ σ hσ hpos
  exact h _ σ hσ (by rwa [repMultiplicity_congr_left e σ])

omit [CharP F 2] [Fintype F] in
theorem OnlyT3.of_subsingleton {V : Type} [AddCommGroup V] [Module k V] [Subsingleton V]
    (ρ : Representation k SL(3, F) V) : OnlyT3 (F := F) k f ρ := by
  intro E _ _ _ σ hσ hpos
  exfalso
  have : Subsingleton (Representation.asModule ρ) := inferInstanceAs (Subsingleton V)
  unfold repMultiplicity at hpos
  rw [compositionMultiplicity_of_subsingleton] at hpos
  exact lt_irrefl _ hpos

theorem onlyT3_T (hF : Fintype.card F = 2 ^ f) (a b : Fin f → Bool) :
    OnlyT3 (F := F) k f (matRep (tensorRep (F := F) k a b)) := by
  intro E _ _ _ σ hσ hpos
  rw [repMultiplicity_of_isIrreducible (tensorRep_fixed_irreducible k hF a b).2 σ] at hpos
  by_cases h : Nonempty (Representation.Equiv (matRep (tensorRep (F := F) k a b)) σ)
  · exact ⟨a, b, h⟩
  · simp [h] at hpos

omit [CharP F 2] [Fintype F] in
theorem OnlyT3.sub_quot {V : Type} [AddCommGroup V] [Module k V] [Module.Finite k V]
    {ρ : Representation k SL(3, F) V} (h : OnlyT3 (F := F) k f ρ) (W : Subrepresentation ρ) :
    OnlyT3 (F := F) k f W.toRepresentation ∧ OnlyT3 (F := F) k f W.quotient := by
  constructor
  · intro E _ _ _ σ hσ hpos
    apply h _ σ hσ
    rw [repMultiplicity_sub_quot ρ W σ]
    omega
  · intro E _ _ _ σ hσ hpos
    apply h _ σ hσ
    rw [repMultiplicity_sub_quot ρ W σ]
    omega

omit [CharP F 2] [Fintype F] in
theorem OnlyT3.of_sub_quot {V : Type} [AddCommGroup V] [Module k V] [Module.Finite k V]
    {ρ : Representation k SL(3, F) V} (W : Subrepresentation ρ)
    (h1 : OnlyT3 (F := F) k f W.toRepresentation) (h2 : OnlyT3 (F := F) k f W.quotient) :
    OnlyT3 (F := F) k f ρ := by
  intro E _ _ _ σ hσ hpos
  rw [repMultiplicity_sub_quot ρ W σ] at hpos
  by_cases ha : 0 < repMultiplicity W.toRepresentation σ
  · exact h1 _ σ hσ ha
  · exact h2 _ σ hσ (by omega)

omit [CharP F 2] [Fintype F] in
theorem OnlyT3.of_flag {V : Type} [AddCommGroup V] [Module k V] [Module.Finite k V]
    {ρ : Representation k SL(3, F) V} (L : List (FRep k SL(3, F))) (hL : FlagTop ρ L)
    (h : ∀ Q ∈ L, OnlyT3 (F := F) k f Q.ρ) : OnlyT3 (F := F) k f ρ := by
  intro E _ _ _ σ hσ hpos
  rw [CFSG.QuasithinUnique.Setup.X7b.FlagTop.mult L ρ hL σ] at hpos
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

omit [CharP F 2] [Fintype F] in
theorem OnlyT3.of_mem_flag {V : Type} [AddCommGroup V] [Module k V] [Module.Finite k V]
    {ρ : Representation k SL(3, F) V} (L : List (FRep k SL(3, F))) (hL : FlagTop ρ L)
    (h : OnlyT3 (F := F) k f ρ) : ∀ Q ∈ L, OnlyT3 (F := F) k f Q.ρ := by
  intro Q hQ E _ _ _ σ hσ hpos
  apply h _ σ hσ
  rw [CFSG.QuasithinUnique.Setup.X7b.FlagTop.mult L ρ hL σ]
  have hle : repMultiplicity Q.ρ σ ≤ (L.map fun Q => repMultiplicity Q.ρ σ).sum :=
    List.single_le_sum (fun x _ => Nat.zero_le x) _ (List.mem_map.mpr ⟨Q, hQ, rfl⟩)
  omega

omit [CharP F 2] [Fintype F] in
theorem OnlyT3.of_mem_flag_tensor {V : Type} [AddCommGroup V] [Module k V] [Module.Finite k V]
    {ρ : Representation k SL(3, F) V} (L : List (FRep k SL(3, F))) (hL : FlagTop ρ L)
    (X : FRep k SL(3, F)) (h : OnlyT3 (F := F) k f (Representation.tprod ρ X.ρ)) :
    ∀ Q ∈ L, OnlyT3 (F := F) k f (Representation.tprod Q.ρ X.ρ) := by
  have hT := CFSG.QuasithinUnique.Setup.X7b.FlagTop.tensor L ρ hL X
  intro Q hQ
  exact OnlyT3.of_mem_flag _ hT h _ (List.mem_map.mpr ⟨Q, hQ, rfl⟩)

omit [CharP F 2] [Fintype F] in
theorem OnlyT3.of_flag_tensor {V : Type} [AddCommGroup V] [Module k V] [Module.Finite k V]
    {ρ : Representation k SL(3, F) V} (L : List (FRep k SL(3, F))) (hL : FlagTop ρ L)
    (X : FRep k SL(3, F)) (h : ∀ Q ∈ L, OnlyT3 (F := F) k f (Representation.tprod Q.ρ X.ρ)) :
    OnlyT3 (F := F) k f (Representation.tprod ρ X.ρ) := by
  have hT := CFSG.QuasithinUnique.Setup.X7b.FlagTop.tensor L ρ hL X
  refine OnlyT3.of_flag _ hT ?_
  intro Q hQ
  obtain ⟨Q', hQ', rfl⟩ := List.mem_map.mp hQ
  exact h Q' hQ'

end OnlyT

section Split

open CFSG.QuasithinUnique.Setup.X7 (matRep matRep_apply matIso_of_reindex)
open CFSG.QuasithinUnique.Setup.X7b (kronRep tprodKronEquiv)

variable {F : Type} [Field F] [CharP F 2] (k : Type) [Field k] [Algebra F k] [CharP k 2] {f : ℕ}

@[expose] def restRep (p : Fin f) (τ' : {j : Fin f // j ≠ p} → Bool × Bool) :
    SL(3, F) →* Matrix (∀ j : {j : Fin f // j ≠ p}, Fin (locDim (τ' j).1 (τ' j).2))
      (∀ j : {j : Fin f // j ≠ p}, Fin (locDim (τ' j).1 (τ' j).2)) k :=
  tensorRepGen k τ' (fun j => (j : ℕ))

@[expose] def splitIdx (p : Fin f) (a b : Fin f → Bool) :
    TIdx f a b ≃ (∀ j : {j : Fin f // j ≠ p}, Fin (locDim (a j) (b j))) ×
      Fin (locDim (a p) (b p)) :=
  (Equiv.piSplitAt p _).trans (Equiv.prodComm _ _)

omit [CharP F 2] in
theorem tensorRep_split_aux (a b : Fin f → Bool) (p : Fin f) :
    Nonempty (Representation.Equiv (matRep (tensorRep (F := F) k a b))
      (Representation.tprod (matRep (restRep (F := F) k p (fun j => (a j, b j))))
        (matRep (locRep (F := F) k (a p) (b p) (p : ℕ))))) := by
  have hh : ∀ (g : SL(3, F)) (x' x : TIdx f a b),
      kronRep (restRep (F := F) k p (fun j => (a j, b j)))
        (locRep (F := F) k (a p) (b p) (p : ℕ)) g (splitIdx p a b x') (splitIdx p a b x) =
        tensorRep (F := F) k a b g x' x := by
    intro g x' x
    simp only [kronRep, MonoidHom.coe_mk, OneHom.coe_mk, Matrix.kroneckerMap_apply]
    show restRep (F := F) k p (fun j => (a j, b j)) g (fun j => x' j) (fun j => x j) *
      locRep (F := F) k (a p) (b p) (p : ℕ) g (x' p) (x p) =
        tensorRepGen (F := F) k (fun i : Fin f => (a i, b i)) (fun i => (i : ℕ)) g x' x
    rw [restRep, tensorRepGen_apply, tensorRepGen_apply,
      Fintype.prod_eq_mul_prod_subtype_ne _ p, mul_comm]
  obtain ⟨e₂⟩ := (matIso_of_reindex (R := tensorRep (F := F) k a b)
    (R' := kronRep (restRep (F := F) k p (fun j => (a j, b j)))
      (locRep (F := F) k (a p) (b p) (p : ℕ)))
    (splitIdx p a b) hh).equiv
  exact ⟨e₂.trans (tprodKronEquiv _ _).symm⟩

end Split

section Combinatorics

@[expose] def wt (ℓ : Bool × Bool) : ℕ := (if ℓ.1 then 1 else 0) + (if ℓ.2 then 1 else 0)

variable {f : ℕ}

@[expose] def meas (a b : Fin f → Bool) : ℕ := ∑ j, wt (a j, b j)

@[expose] def insArr (p : Fin f) (τ' : {j : Fin f // j ≠ p} → Bool × Bool) (ℓ : Bool × Bool) :
    (Fin f → Bool) × (Fin f → Bool) :=
  (fun j => if h : j = p then ℓ.1 else (τ' ⟨j, h⟩).1,
    fun j => if h : j = p then ℓ.2 else (τ' ⟨j, h⟩).2)

theorem insArr_fst_at (p : Fin f) (τ' : {j : Fin f // j ≠ p} → Bool × Bool) (ℓ : Bool × Bool) :
    (insArr p τ' ℓ).1 p = ℓ.1 := by
  simp [insArr]

theorem insArr_snd_at (p : Fin f) (τ' : {j : Fin f // j ≠ p} → Bool × Bool) (ℓ : Bool × Bool) :
    (insArr p τ' ℓ).2 p = ℓ.2 := by
  simp [insArr]

theorem insArr_off (p : Fin f) (τ' : {j : Fin f // j ≠ p} → Bool × Bool) (ℓ : Bool × Bool)
    (j : {j : Fin f // j ≠ p}) :
    ((insArr p τ' ℓ).1 j, (insArr p τ' ℓ).2 j) = τ' j := by
  simp [insArr, j.2]

theorem insArr_restrict (a b : Fin f → Bool) (p : Fin f) :
    insArr p (fun j => (a j, b j)) (a p, b p) = (a, b) := by
  refine Prod.ext (funext fun j => ?_) (funext fun j => ?_)
  · by_cases h : j = p
    · subst h
      simp [insArr]
    · simp [insArr, h]
  · by_cases h : j = p
    · subst h
      simp [insArr]
    · simp [insArr, h]

theorem meas_insArr (p : Fin f) (τ' : {j : Fin f // j ≠ p} → Bool × Bool) (ℓ : Bool × Bool) :
    meas (insArr p τ' ℓ).1 (insArr p τ' ℓ).2 = wt ℓ + ∑ j : {j : Fin f // j ≠ p}, wt (τ' j) := by
  rw [meas, Fintype.sum_eq_add_sum_subtype_ne _ p]
  congr 1
  · rw [insArr_fst_at, insArr_snd_at]
  · refine Finset.sum_congr rfl fun j _ => ?_
    rw [insArr_off]

end Combinatorics

section Unit

open CFSG.QuasithinUnique.Setup.X7 (matRep matRep_apply)

variable {G : Type} [Group G] {k : Type} [Field k]

@[expose] noncomputable def unitEquiv :
    Representation.Equiv (matRep (1 : G →* Matrix (Fin 1) (Fin 1) k))
      (Representation.trivial k G k) :=
  Representation.Equiv.mk (LinearEquiv.funUnique (Fin 1) k k) (fun g => by
    refine LinearMap.ext fun v => ?_
    simp [matRep_apply])

@[expose] noncomputable def unitRid {V : Type} [AddCommGroup V] [Module k V]
    (ρ : Representation k G V) :
    Representation.Equiv (Representation.tprod ρ (matRep (1 : G →* Matrix (Fin 1) (Fin 1) k))) ρ :=
  (eqL ρ unitEquiv).trans (Representation.TensorProduct.rid k ρ)

@[expose] noncomputable def unitLid {V : Type} [AddCommGroup V] [Module k V]
    (ρ : Representation k G V) :
    Representation.Equiv (Representation.tprod (matRep (1 : G →* Matrix (Fin 1) (Fin 1) k)) ρ) ρ :=
  (eqR unitEquiv ρ).trans (Representation.TensorProduct.lid k ρ)

end Unit

section Letters

open CFSG.QuasithinUnique.Setup.X7 (matRep matRep_apply)
open CFSG.QuasithinUnique.Setup.X7b (FRep FlagTop)

variable {F : Type} [Field F] [CharP F 2] [Fintype F] (k : Type) [Field k] [Algebra F k]
  [CharP k 2] {f : ℕ}

@[expose] noncomputable def locFRep (ℓ : Bool × Bool) (i : ℕ) : FRep k SL(3, F) :=
  ⟨Fin (locDim ℓ.1 ℓ.2) → k, matRep (locRep k ℓ.1 ℓ.2 i)⟩

omit [CharP F 2] [Fintype F] in
theorem sq_flag_loc (δ : Bool) (i : ℕ) :
    FlagTop (Representation.tprod (matRep (locRep (F := F) k (!δ) δ i))
        (matRep (locRep (F := F) k (!δ) δ i)))
      [locFRep k (δ, !δ) i, locFRep k (!δ, δ) (i + 1), locFRep k (δ, !δ) i] := by
  cases δ
  · exact natRep_square_filtration k i
  · exact dualRep_square_filtration k i

omit [CharP F 2] [Fintype F] in
theorem tr_flag_loc (δ : Bool) (i : ℕ) :
    FlagTop (Representation.tprod (matRep (locRep (F := F) k δ (!δ) i))
        (matRep (locRep (F := F) k (!δ) δ i)))
      [unitFRep k, locFRep k (true, true) i] := by
  cases δ
  · exact trace_flag_dual_nat k i
  · exact trace_flag_nat_dual k i

omit [CharP F 2] [Fintype F] in
theorem tr_flag_loc' (δ : Bool) (i : ℕ) :
    FlagTop (Representation.tprod (matRep (locRep (F := F) k (!δ) δ i))
        (matRep (locRep (F := F) k δ (!δ) i)))
      [unitFRep k, locFRep k (true, true) i] := by
  cases δ
  · exact trace_flag_nat_dual k i
  · exact trace_flag_dual_nat k i

omit [CharP F 2] [Fintype F] in
theorem tensorRep_split (a b : Fin f → Bool) (p : Fin f) (α β : Bool)
    (τ' : {j : Fin f // j ≠ p} → Bool × Bool) (ha : a p = α) (hb : b p = β)
    (hτ : ∀ j : {j : Fin f // j ≠ p}, (a j, b j) = τ' j) :
    Nonempty (Representation.Equiv (matRep (tensorRep (F := F) k a b))
      (Representation.tprod (matRep (restRep (F := F) k p τ'))
        (matRep (locRep (F := F) k α β (p : ℕ))))) := by
  subst ha hb
  have h : τ' = fun j : {j : Fin f // j ≠ p} => (a j, b j) := funext fun j => (hτ j).symm
  subst h
  exact tensorRep_split_aux k a b p

variable (p : Fin f) (τ' : {j : Fin f // j ≠ p} → Bool × Bool)

@[expose] noncomputable def TT (ℓ : Bool × Bool) :
    Representation k SL(3, F) (TIdx f (insArr p τ' ℓ).1 (insArr p τ' ℓ).2 → k) :=
  matRep (tensorRep (F := F) k (insArr p τ' ℓ).1 (insArr p τ' ℓ).2)

omit [CharP F 2] [Fintype F] in
theorem TT_equiv (ℓ : Bool × Bool) :
    Nonempty (Representation.Equiv (TT (F := F) k p τ' ℓ)
      (Representation.tprod (matRep (restRep (F := F) k p τ'))
        (matRep (locRep (F := F) k ℓ.1 ℓ.2 (p : ℕ))))) :=
  tensorRep_split k _ _ p ℓ.1 ℓ.2 τ' (insArr_fst_at p τ' ℓ) (insArr_snd_at p τ' ℓ)
    (insArr_off p τ' ℓ)

variable (hF : Fintype.card F = 2 ^ f)

include hF in
theorem onlyT3_TT (ℓ : Bool × Bool) : OnlyT3 (F := F) k f (TT (F := F) k p τ' ℓ) :=
  onlyT3_T hF _ _

include hF in
theorem onlyT3_rest_loc (ℓ : Bool × Bool) :
    OnlyT3 (F := F) k f (Representation.tprod (matRep (restRep (F := F) k p τ'))
      (matRep (locRep (F := F) k ℓ.1 ℓ.2 (p : ℕ)))) :=
  OnlyT3.congr (TT_equiv k p τ' ℓ).some (onlyT3_TT k p τ' hF ℓ)

include hF in
theorem onlyT3_loc_rest (ℓ : Bool × Bool) :
    OnlyT3 (F := F) k f (Representation.tprod (matRep (locRep (F := F) k ℓ.1 ℓ.2 (p : ℕ)))
      (matRep (restRep (F := F) k p τ'))) :=
  OnlyT3.congr (Representation.TensorProduct.comm _ _) (onlyT3_rest_loc k p τ' hF ℓ)

omit [Fintype F] in
noncomputable def TT_zero :
    Representation.Equiv (TT (F := F) k p τ' (false, false)) (matRep (restRep (F := F) k p τ')) :=
  (TT_equiv k p τ' (false, false)).some.trans (unitRid _)

omit [CharP F 2] [Fintype F] in
theorem onlyT3_swap_rest {V : Type} [AddCommGroup V] [Module k V] (Y : Representation k SL(3, F) V)
    (ℓ : Bool × Bool)
    (h : OnlyT3 (F := F) k f (Representation.tprod (TT (F := F) k p τ' ℓ) Y)) :
    OnlyT3 (F := F) k f (Representation.tprod Y
      (Representation.tprod (matRep (locRep (F := F) k ℓ.1 ℓ.2 (p : ℕ)))
        (matRep (restRep (F := F) k p τ')))) :=
  OnlyT3.congr (((eqR (TT_equiv k p τ' ℓ).some Y).trans
    (eqR (Representation.TensorProduct.comm _ _) Y)).trans (Representation.TensorProduct.comm _ _)) h

omit [CharP F 2] [Fintype F] in
theorem onlyT3_swap_rest0 {V : Type} [AddCommGroup V] [Module k V] (Y : Representation k SL(3, F) V)
    (h : OnlyT3 (F := F) k f (Representation.tprod (TT (F := F) k p τ' (false, false)) Y)) :
    OnlyT3 (F := F) k f (Representation.tprod Y (matRep (restRep (F := F) k p τ'))) :=
  OnlyT3.congr ((eqR (TT_zero k p τ') Y).trans (Representation.TensorProduct.comm _ _)) h

include hF in
theorem caseZero (δ : Bool) :
    OnlyT3 (F := F) k f (Representation.tprod (TT (F := F) k p τ' (false, false))
      (matRep (locRep (F := F) k (!δ) δ (p : ℕ)))) :=
  OnlyT3.congr (eqR (TT_zero k p τ') _).symm (onlyT3_rest_loc k p τ' hF (!δ, δ))

end Letters

section Cases

open CFSG.QuasithinUnique.Setup.X7 (matRep matRep_apply)
open CFSG.QuasithinUnique.Setup.X7b (FRep FlagTop)

variable {F : Type} [Field F] [CharP F 2] [Fintype F] (k : Type) [Field k] [Algebra F k]
  [CharP k 2] {f : ℕ} (hF : Fintype.card F = 2 ^ f) (p : Fin f)
  (τ' : {j : Fin f // j ≠ p} → Bool × Bool)

@[expose] noncomputable def restFRep : FRep k SL(3, F) :=
  ⟨(∀ j : {j : Fin f // j ≠ p}, Fin (locDim (τ' j).1 (τ' j).2)) → k, matRep (restRep k p τ')⟩

omit [CharP F 2] [Fintype F] in
theorem OnlyT3.of_swapMid {V₁ V₂ V₃ V₄ : Type} [AddCommGroup V₁] [Module k V₁] [AddCommGroup V₂]
    [Module k V₂] [AddCommGroup V₃] [Module k V₃] [AddCommGroup V₄] [Module k V₄]
    (ρ : Representation k SL(3, F) V₁) (σ : Representation k SL(3, F) V₂)
    (τ : Representation k SL(3, F) V₃) (υ : Representation k SL(3, F) V₄)
    (h : OnlyT3 (F := F) k f (Representation.tprod (Representation.tprod ρ τ)
      (Representation.tprod σ υ))) :
    OnlyT3 (F := F) k f (Representation.tprod (Representation.tprod ρ σ)
      (Representation.tprod τ υ)) :=
  OnlyT3.congr (swapMid ρ σ τ υ).symm h

include hF in
theorem caseSame (δ : Bool)
    (ih : ∀ m : Bool × Bool, m.1 ≠ m.2 → ∀ i' : ℕ,
      OnlyT3 (F := F) k f (Representation.tprod (TT (F := F) k p τ' (false, false))
        (matRep (locRep (F := F) k m.1 m.2 i')))) :
    OnlyT3 (F := F) k f (Representation.tprod (TT (F := F) k p τ' (!δ, δ))
      (matRep (locRep (F := F) k (!δ) δ (p : ℕ)))) := by
  have hfl := OnlyT3.of_flag_tensor (k := k) (f := f) _ (sq_flag_loc k δ p) (restFRep k p τ') (by
    intro Q hQ
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hQ
    rcases hQ with rfl | rfl | rfl
    · exact onlyT3_loc_rest k p τ' hF (δ, !δ)
    · exact onlyT3_swap_rest0 k p τ' _ (ih (!δ, δ) (by cases δ <;> simp) (p + 1))
    · exact onlyT3_loc_rest k p τ' hF (δ, !δ))
  have e := ((eqR (TT_equiv k p τ' (!δ, δ)).some (matRep (locRep (F := F) k (!δ) δ (p : ℕ)))).trans
      (Representation.TensorProduct.assoc _ _ _)).trans (Representation.TensorProduct.comm _ _)
  exact OnlyT3.congr e.symm hfl

include hF in
theorem caseOpp (δ : Bool) :
    OnlyT3 (F := F) k f (Representation.tprod (TT (F := F) k p τ' (δ, !δ))
      (matRep (locRep (F := F) k (!δ) δ (p : ℕ)))) := by
  have hfl := OnlyT3.of_flag_tensor (k := k) (f := f) _ (tr_flag_loc k δ p) (restFRep k p τ') (by
    intro Q hQ
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hQ
    rcases hQ with rfl | rfl
    · exact onlyT3_loc_rest k p τ' hF (false, false)
    · exact onlyT3_loc_rest k p τ' hF (true, true))
  have e := ((eqR (TT_equiv k p τ' (δ, !δ)).some (matRep (locRep (F := F) k (!δ) δ (p : ℕ)))).trans
      (Representation.TensorProduct.assoc _ _ _)).trans (Representation.TensorProduct.comm _ _)
  exact OnlyT3.congr e.symm hfl

omit [CharP F 2] [Fintype F] hF in
theorem caseQ (δ : Bool)
    (ih : ∀ m : Bool × Bool, m.1 ≠ m.2 → ∀ i' : ℕ,
      OnlyT3 (F := F) k f (Representation.tprod (TT (F := F) k p τ' (δ, !δ))
        (matRep (locRep (F := F) k m.1 m.2 i')))) :
    OnlyT3 (F := F) k f (Representation.tprod (TT (F := F) k p τ' (true, true))
      (matRep (locRep (F := F) k (!δ) δ (p : ℕ)))) := by
  have hbig0 := OnlyT3.of_flag_tensor (k := k) (f := f) _ (sq_flag_loc k δ p)
    (⟨_, Representation.tprod (matRep (locRep (F := F) k δ (!δ) (p : ℕ)))
        (matRep (restRep (F := F) k p τ'))⟩ : FRep k SL(3, F)) (by
    intro Y hY
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hY
    rcases hY with rfl | rfl | rfl
    · exact onlyT3_swap_rest k p τ' _ (δ, !δ) (ih (δ, !δ) (by cases δ <;> simp) p)
    · exact onlyT3_swap_rest k p τ' _ (δ, !δ) (ih (!δ, δ) (by cases δ <;> simp) (p + 1))
    · exact onlyT3_swap_rest k p τ' _ (δ, !δ) (ih (δ, !δ) (by cases δ <;> simp) p))
  have hbal := OnlyT3.of_swapMid (F := F) (k := k) (f := f)
    (matRep (locRep (F := F) k (!δ) δ (p : ℕ))) (matRep (locRep (F := F) k δ (!δ) (p : ℕ)))
    (matRep (locRep (F := F) k (!δ) δ (p : ℕ))) (matRep (restRep (F := F) k p τ')) hbig0
  have h2 := OnlyT3.of_mem_flag_tensor _ (tr_flag_loc' k δ p)
    (⟨_, Representation.tprod (matRep (locRep (F := F) k (!δ) δ (p : ℕ)))
        (matRep (restRep (F := F) k p τ'))⟩ : FRep k SL(3, F)) hbal
  have hQ := h2 (locFRep k (true, true) p) (by simp)
  have e := ((((eqR (TT_equiv k p τ' (true, true)).some
      (matRep (locRep (F := F) k (!δ) δ (p : ℕ)))).trans
      (Representation.TensorProduct.assoc _ _ _)).trans (Representation.TensorProduct.comm _ _)).trans
      (Representation.TensorProduct.assoc _ _ _))
  exact OnlyT3.congr e.symm hQ

end Cases



section Induction

open CFSG.QuasithinUnique.Setup.X7 (matRep)

variable {F : Type} [Field F] [CharP F 2] [Fintype F] (k : Type) [Field k] [Algebra F k]
  [CharP k 2] {f : ℕ}

theorem onlyT3_tprod_T (hF : Fintype.card F = 2 ^ f) (hf : 1 ≤ f) :
    ∀ (n : ℕ) (a b : Fin f → Bool), meas a b = n → ∀ m : Bool × Bool, m.1 ≠ m.2 → ∀ i : ℕ,
      OnlyT3 (F := F) k f (Representation.tprod (matRep (tensorRep (F := F) k a b))
        (matRep (locRep (F := F) k m.1 m.2 i))) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro a b hn m hm i
  obtain ⟨p, hp⟩ : ∃ p : Fin f, (p : ℕ) = i % f := ⟨⟨i % f, Nat.mod_lt _ (by omega)⟩, rfl⟩
  have hlet : locRep (F := F) k m.1 m.2 i = locRep k m.1 m.2 (p : ℕ) :=
    MonoidHom.ext fun g => by rw [hp]; exact locRep_mod k hF m.1 m.2 i g
  rw [hlet]
  obtain ⟨τ', ℓ₀, ha, hb⟩ : ∃ (τ' : {j : Fin f // j ≠ p} → Bool × Bool) (ℓ₀ : Bool × Bool),
      a = (insArr p τ' ℓ₀).1 ∧ b = (insArr p τ' ℓ₀).2 :=
    ⟨fun j => (a j, b j), (a p, b p), by rw [insArr_restrict]; exact ⟨rfl, rfl⟩⟩
  subst ha
  subst hb
  have hmeas := meas_insArr p τ' ℓ₀
  have ihℓ : ∀ ℓ' : Bool × Bool, wt ℓ' < wt ℓ₀ → ∀ m' : Bool × Bool, m'.1 ≠ m'.2 → ∀ i' : ℕ,
      OnlyT3 (F := F) k f (Representation.tprod (TT (F := F) k p τ' ℓ')
        (matRep (locRep (F := F) k m'.1 m'.2 i'))) := fun ℓ' hℓ m' hm' i' =>
    ih (meas (insArr p τ' ℓ').1 (insArr p τ' ℓ').2) (by rw [meas_insArr]; omega) _ _ rfl m' hm' i'
  obtain ⟨δ, rfl⟩ : ∃ δ : Bool, m = (!δ, δ) :=
    ⟨m.2, by rcases m with ⟨x, y⟩; cases x <;> cases y <;> simp_all⟩
  rcases ℓ₀ with ⟨u, v⟩
  cases δ <;> cases u <;> cases v
  · exact caseZero k p τ' hF false
  · exact caseOpp k hF p τ' false
  · exact caseSame k hF p τ' false (ihℓ (false, false) (by decide))
  · exact caseQ k p τ' false (ihℓ (false, true) (by decide))
  · exact caseZero k p τ' hF true
  · exact caseSame k hF p τ' true (ihℓ (false, false) (by decide))
  · exact caseOpp k hF p τ' true
  · exact caseQ k p τ' true (ihℓ (true, false) (by decide))

end Induction

section Exhaust

open CFSG.QuasithinUnique.Setup.X7 (matRep matRep_apply matIso_of_reindex)
open CFSG.QuasithinUnique.Setup.X7b (subIncl quotProj rep_induction kronRep tprodKronEquiv)
open CFSG.QuasithinUnique.Setup.SL2Modules (powMat powMat_mul)

theorem repMultiplicity_tprod_sub_quot' {G : Type} [Group G] {k : Type} [Field k] {V : Type}
    [AddCommGroup V] [Module k V] [Module.Finite k V] {ρ : Representation k G V}
    (W : Subrepresentation ρ) {X : Type} [AddCommGroup X] [Module k X] [Module.Finite k X]
    (τ : Representation k G X) {E : Type} [AddCommGroup E] [Module k E]
    (σ : Representation k G E) :
    repMultiplicity (Representation.tprod ρ τ) σ =
      repMultiplicity (Representation.tprod W.toRepresentation τ) σ +
        repMultiplicity (Representation.tprod W.quotient τ) σ := by
  have : Module.Finite k (W.toSubmodule ⊗[k] X) := inferInstance
  have : Module.Finite k ((V ⧸ W.toSubmodule) ⊗[k] X) := inferInstance
  refine repMultiplicity_eq_add_of_exact
    (Representation.IntertwiningMap.rTensor τ (subIncl ρ W))
    (Representation.IntertwiningMap.rTensor τ (quotProj ρ W)) ?_ ?_ ?_ σ
  · exact Module.Flat.rTensor_preserves_injective_linearMap (M := X) (subIncl ρ W).toLinearMap
      W.toSubmodule.injective_subtype
  · exact LinearMap.rTensor_surjective X W.toSubmodule.mkQ_surjective
  · exact Module.Flat.rTensor_exact X (LinearMap.exact_subtype_mkQ W.toSubmodule)

variable {F : Type} [Field F] [CharP F 2] [Fintype F] (k : Type) [Field k] [Algebra F k]
  [CharP k 2] {f : ℕ}

theorem onlyT3_tprod_letter (hF : Fintype.card F = 2 ^ f) (hf : 1 ≤ f) {V : Type}
    [AddCommGroup V] [Module k V] [Module.Finite k V] (ρ : Representation k SL(3, F) V)
    (hρ : OnlyT3 (F := F) k f ρ) (m : Bool × Bool) (hm : m.1 ≠ m.2) (i : ℕ) :
    OnlyT3 (F := F) k f (Representation.tprod ρ (matRep (locRep (F := F) k m.1 m.2 i))) := by
  have key := rep_induction (k := k) (G := SL(3, F))
    (fun {V} _ _ _ ρ => OnlyT3 (F := F) k f ρ → OnlyT3 (F := F) k f
      (Representation.tprod ρ (matRep (locRep (F := F) k m.1 m.2 i))))
    (fun {V} _ _ _ ρ hsub _ => by
      have h1 : Subsingleton V := hsub
      have : Subsingleton (V ⊗[k] (Fin (locDim m.1 m.2) → k)) := by
        refine subsingleton_of_forall_eq 0 fun t => ?_
        induction t using TensorProduct.inductionOn with
        | tmul m n => rw [Subsingleton.elim m 0, TensorProduct.zero_tmul]
        | add x y hx hy => rw [hx, hy, add_zero]
      exact OnlyT3.of_subsingleton _)
    (fun {V} _ _ _ ρ hirr hρ => by
      have hpos : 0 < repMultiplicity ρ ρ := by
        rw [repMultiplicity_of_isIrreducible hirr ρ]
        have : Nonempty (Representation.Equiv ρ ρ) := ⟨Representation.Equiv.refl ρ⟩
        simp [this]
      obtain ⟨a, b, ⟨e⟩⟩ := hρ V ρ hirr hpos
      exact OnlyT3.congr (eqR e _) (onlyT3_tprod_T k hF hf _ a b rfl m hm i))
    (fun {V} _ _ _ ρ W hW1 hW2 hρ => by
      obtain ⟨h1, h2⟩ := hρ.sub_quot W
      have hA := hW1 h1
      have hB := hW2 h2
      intro E _ _ _ σ hσ hpos
      rw [repMultiplicity_tprod_sub_quot' W (matRep (locRep (F := F) k m.1 m.2 i)) σ] at hpos
      by_cases ha : 0 < repMultiplicity (Representation.tprod W.toRepresentation
          (matRep (locRep (F := F) k m.1 m.2 i))) σ
      · exact hA E σ hσ ha
      · exact hB E σ hσ (by omega))
  exact key _ ρ rfl hρ

@[expose] noncomputable def powRep3 (m : ℕ) :
    SL(3, F) →* Matrix (Fin m → Fin 3) (Fin m → Fin 3) k where
  toFun g := powMat (natRep k 0 g) m
  map_one' := by
    rw [map_one, CFSG.QuasithinUnique.Setup.X7b.powMat_eq_kron]
    exact kron_one
  map_mul' g h := by
    rw [map_mul, powMat_mul]

omit [CharP F 2] [Fintype F] in
theorem powRep3_succ_nonempty (m : ℕ) :
    Nonempty (Representation.Equiv
      (Representation.tprod (matRep (powRep3 (F := F) k m)) (matRep (natRep (F := F) k 0)))
      (matRep (powRep3 (F := F) k (m + 1)))) := by
  let e : ((Fin m → Fin 3) × Fin 3) ≃ (Fin (m + 1) → Fin 3) :=
    { toFun := fun y => Fin.snoc y.1 y.2
      invFun := fun x => (Fin.init x, x (Fin.last m))
      left_inv := fun y => by simp
      right_inv := fun x => by simp }
  obtain ⟨e₂⟩ := (matIso_of_reindex (R := kronRep (powRep3 (F := F) k m) (natRep (F := F) k 0))
    (R' := powRep3 (F := F) k (m + 1)) e (fun g x' x => by
      simp only [powRep3, kronRep, MonoidHom.coe_mk, OneHom.coe_mk, powMat,
        Matrix.kroneckerMap_apply, e, Equiv.coe_fn_mk, Fin.prod_univ_castSucc, Fin.snoc_castSucc,
        Fin.snoc_last])).equiv
  exact ⟨(tprodKronEquiv _ _).trans e₂⟩

omit [CharP F 2] [Fintype F] in
theorem powRep3_zero_nonempty :
    Nonempty (Representation.Equiv (matRep (powRep3 (F := F) k 0))
      (matRep (tensorRep (F := F) k (zeros f) (zeros f)))) := by
  have hu1 : Unique (Fin 0 → Fin 3) := Pi.uniqueOfIsEmpty _
  have hu : ∀ i : Fin f, Unique (Fin (locDim (zeros f i) (zeros f i))) := fun i =>
    inferInstanceAs (Unique (Fin 1))
  have hu2 : Unique (TIdx f (zeros f) (zeros f)) := Pi.unique
  exact (matIso_of_reindex (R := powRep3 (F := F) k 0)
    (R' := tensorRep (F := F) k (zeros f) (zeros f)) (Equiv.ofUnique _ _) (fun g x' x => by
      have h1 : Equiv.ofUnique (Fin 0 → Fin 3) (TIdx f (zeros f) (zeros f)) x' =
          Equiv.ofUnique (Fin 0 → Fin 3) (TIdx f (zeros f) (zeros f)) x := Subsingleton.elim _ _
      rw [h1]
      have h2 : ∀ (i : Fin f) (a : Fin (locDim (zeros f i) (zeros f i))),
          locRep (F := F) k (zeros f i) (zeros f i) (i : ℕ) g a a = 1 := fun i a => by
        show (1 : SL(3, F) →* Matrix (Fin 1) (Fin 1) k) g a a = 1
        rw [MonoidHom.one_apply]
        exact Matrix.one_apply_eq (n := Fin 1) a
      simp only [tensorRep, tensorRepGen_apply]
      rw [Finset.prod_congr rfl fun i _ => h2 i _]
      simp [powRep3, CFSG.QuasithinUnique.Setup.X7b.powMat_eq_kron, kron_apply])).equiv

omit [CharP F 2] [Fintype F] in
theorem natRep_zero_injective : Function.Injective (natRep (F := F) k 0) := by
  intro g h hgh
  have h1 : ∀ a b, frK k 0 (g a b) = frK k 0 (h a b) := fun a b => by
    have := congrFun (congrFun hgh a) b
    simpa [natRep_apply, twistMat_apply] using this
  have h2 : ∀ a b, (g : Matrix (Fin 3) (Fin 3) F) a b = (h : Matrix (Fin 3) (Fin 3) F) a b := by
    intro a b
    have := h1 a b
    simp only [frK_apply, pow_zero, pow_one] at this
    exact (algebraMap F k).injective this
  exact Subtype.ext (Matrix.ext h2)

theorem onlyT3_powRep3 (hF : Fintype.card F = 2 ^ f) (hf : 1 ≤ f) (m : ℕ) :
    OnlyT3 (F := F) k f (matRep (powRep3 (F := F) k m)) := by
  induction m with
  | zero =>
    exact OnlyT3.congr (powRep3_zero_nonempty (F := F) (f := f) k).some.symm
      (onlyT3_T hF (zeros f) (zeros f))
  | succ m ih =>
    exact OnlyT3.congr (powRep3_succ_nonempty (F := F) k m).some
      (onlyT3_tprod_letter k hF hf _ ih (true, false) (by decide) 0)

theorem exists_T3_equiv (hF : Fintype.card F = 2 ^ f) (hf : 1 ≤ f) {E : Type} [AddCommGroup E]
    [Module k E] [Module.Finite k E] (σ : Representation k SL(3, F) E) (hσ : σ.IsIrreducible) :
    ∃ a b : Fin f → Bool,
      Nonempty (Representation.Equiv (matRep (tensorRep (F := F) k a b)) σ) := by
  classical
  obtain ⟨m, -, φ, hφ, hcomm⟩ := CFSG.QuasithinUnique.Setup.SL2Modules.faithful_tensor_power
    (by norm_num : 0 < 3) (natRep (F := F) k 0) (natRep_zero_injective (F := F) k) σ hσ
  let Φ : Representation.IntertwiningMap (matRep (powRep3 (F := F) k m)) σ :=
    ⟨φ, fun g => by
      refine LinearMap.ext fun v => ?_
      exact hcomm g v⟩
  have hex : Function.Exact (subIncl (matRep (powRep3 (F := F) k m))
      (Representation.IntertwiningMap.ker (matRep (powRep3 (F := F) k m)) σ Φ)) Φ := by
    intro y
    constructor
    · intro hy
      exact ⟨⟨y, hy⟩, rfl⟩
    · rintro ⟨⟨z, hz⟩, rfl⟩
      exact hz
  have hpos : 0 < repMultiplicity (matRep (powRep3 (F := F) k m)) σ := by
    rw [repMultiplicity_eq_add_of_exact (subIncl _
      (Representation.IntertwiningMap.ker (matRep (powRep3 (F := F) k m)) σ Φ)) Φ
      (Representation.IntertwiningMap.ker (matRep (powRep3 (F := F) k m)) σ Φ).toSubmodule.injective_subtype
      hφ hex σ, repMultiplicity_of_isIrreducible hσ σ]
    have : Nonempty (Representation.Equiv σ σ) := ⟨Representation.Equiv.refl σ⟩
    simp [this]
  exact onlyT3_powRep3 k hF hf m E σ hσ hpos

end Exhaust

end CFSG.QuasithinUnique.Setup.X7a
