module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7aWords
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7aNodes
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7aDistinct
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7bComp

public section

namespace CFSG.QuasithinUnique.Setup.X7a

open scoped MatrixGroups Matrix

section TensorTwist

variable {F : Type} [Field F] [CharP F 2] [Finite F]

@[expose] noncomputable def frobPowEquiv (F : Type) [Field F] [CharP F 2] [Finite F] :
    ℕ → (F ≃+* F)
  | 0 => RingEquiv.refl F
  | j + 1 => (frobPowEquiv F j).trans (frobeniusEquiv F 2)

theorem frobPowEquiv_apply (j : ℕ) (x : F) : frobPowEquiv F j x = x ^ 2 ^ j := by
  induction j with
  | zero => simp [frobPowEquiv]
  | succ j ih =>
    show frobeniusEquiv F 2 (frobPowEquiv F j x) = x ^ 2 ^ (j + 1)
    rw [ih, frobeniusEquiv_def, ← pow_mul, pow_succ]

variable (k : Type) [Field k] [Algebra F k] [CharP k 2]

omit [CharP F 2] [Finite F] in
theorem adjRep_succ_sq (i : ℕ) (g : SL(3, F)) (r s : Fin 8) :
    adjRep k (i + 1) g r s = adjRep k i g r s ^ 2 := by
  let sq : k →+* k := iterateFrobenius k 2 1
  have hsq : ∀ x, sq x = x ^ 2 := fun x => by simp [sq, frobenius_def]
  have hMsq : ∀ M : Matrix (Fin 3) (Fin 3) k, sq.mapMatrix M = M.map (fun x => x ^ 2) :=
    fun M => by
      ext a b
      simp [hsq]
  have hX : (Xm (Pi.single s (1 : k)) : Matrix (Fin 3) (Fin 3) k).map (fun x => x ^ 2) =
      Xm (Pi.single s (1 : k)) := by
    ext a b
    fin_cases a <;> fin_cases b <;> fin_cases s <;> simp [Xm]
  have hc : conjMat k (i + 1) g (Xm (Pi.single s (1 : k))) =
      sq.mapMatrix (conjMat k i g (Xm (Pi.single s (1 : k)))) := by
    rw [conjMat, conjMat, map_mul, map_mul, hMsq, hMsq, hMsq, hX, ← twistMat_succ k i g,
      ← twistMat_succ k i g⁻¹]
  rw [adjRep_apply, adjRep_apply, hc]
  fin_cases r <;> simp [co, hMsq]

omit [CharP F 2] [Finite F] in
theorem locRep_succ_sq (a b : Bool) (i : ℕ) (g : SL(3, F)) (r s : Fin (locDim a b)) :
    locRep k a b (i + 1) g r s = locRep k a b i g r s ^ 2 := by
  cases a <;> cases b
  · rw [locRep_ff, locRep_ff, MonoidHom.one_apply]
    obtain rfl := fin_locDim_ff r s
    simp [Matrix.one_apply_eq]
  · show dualRep k (i + 1) g r s = (dualRep k i g r s) ^ 2
    rw [← frobMat3_dualRep, frobMat3_apply]
    rfl
  · show natRep k (i + 1) g r s = (natRep k i g r s) ^ 2
    rw [← frobMat3_natRep, frobMat3_apply]
    rfl
  · exact adjRep_succ_sq k i g r s

omit [CharP F 2] [Finite F] in
theorem tensorRepGen_succ_sq {ι : Type} [Fintype ι] [DecidableEq ι] (τ : ι → Bool × Bool)
    (e : ι → ℕ) (g : SL(3, F)) (x' x : ∀ i, Fin (locDim (τ i).1 (τ i).2)) :
    tensorRepGen k τ (fun i => e i + 1) g x' x = (tensorRepGen k τ e g x' x) ^ 2 := by
  rw [tensorRepGen_apply, tensorRepGen_apply, ← Finset.prod_pow]
  exact Finset.prod_congr rfl fun i _ => locRep_succ_sq k _ _ (e i) g _ _

variable {f : ℕ}

omit [Finite F] in
theorem tensorRep_comp_frobSL_eq (a b : Fin f → Bool) :
    (tensorRep (F := F) k a b).comp (frobSL F) =
      tensorRepGen k (fun i : Fin f => (a i, b i)) (fun i => (i : ℕ) + 1) := by
  ext g : 1
  show kron _ = kron _
  congr 1
  funext i
  exact locRep_frobSL k _ _ (i : ℕ) g

theorem matMap_frob_tensorRep (a b : Fin f → Bool) :
    CFSG.QuasithinUnique.Setup.X7.matMap (frobeniusEquiv F 2 : F →+* F)
        (tensorRep (F := F) F a b) = (tensorRep (F := F) F a b).comp (frobSL F) := by
  rw [tensorRep_comp_frobSL_eq]
  refine MonoidHom.ext fun g => ?_
  ext x' x
  simp only [CFSG.QuasithinUnique.Setup.X7.matMap_apply, Matrix.map_apply]
  have := tensorRepGen_succ_sq (F := F) F (fun i : Fin f => (a i, b i)) (fun i => (i : ℕ)) g x' x
  rw [this]
  rfl

theorem matMap_comp_ringHom {k₁ k₂ k₃ : Type} [Field k₁] [Field k₂] [Field k₃] {G : Type}
    [Group G] {κ : Type} [Fintype κ] [DecidableEq κ] (θ₁ : k₁ →+* k₂) (θ₂ : k₂ →+* k₃)
    (R : G →* Matrix κ κ k₁) :
    CFSG.QuasithinUnique.Setup.X7.matMap (θ₂.comp θ₁) R =
      CFSG.QuasithinUnique.Setup.X7.matMap θ₂ (CFSG.QuasithinUnique.Setup.X7.matMap θ₁ R) := by
  refine MonoidHom.ext fun g => ?_
  simp [CFSG.QuasithinUnique.Setup.X7.matMap_apply, Matrix.map_map]

theorem matMap_frobPowEquiv_tensorRep (j : ℕ) (a b : Fin f → Bool) :
    CFSG.QuasithinUnique.Setup.X7.matMap (frobPowEquiv F j : F →+* F)
        (tensorRep (F := F) F a b) = (tensorRep (F := F) F a b).comp (frobPow F j) := by
  induction j with
  | zero =>
    refine MonoidHom.ext fun g => ?_
    ext x' x
    simp [frobPowEquiv, frobPow, CFSG.QuasithinUnique.Setup.X7.matMap_apply]
  | succ j ih =>
    have e1 : ((frobPowEquiv F (j + 1) : F ≃+* F) : F →+* F) =
        (frobeniusEquiv F 2 : F →+* F).comp (frobPowEquiv F j : F →+* F) := rfl
    rw [e1, matMap_comp_ringHom, ih]
    refine MonoidHom.ext fun g => ?_
    ext x' x
    have h := congrArg (fun R => R (frobPow F j g) x' x) (matMap_frob_tensorRep (F := F) a b)
    simp only [CFSG.QuasithinUnique.Setup.X7.matMap_apply, Matrix.map_apply,
      MonoidHom.comp_apply] at h ⊢
    exact h

end TensorTwist

section Descent

open CFSG.QuasithinUnique.Setup.X7 (matRep matRep_apply matMap matMap_apply)

variable {F : Type} [Field F] [CharP F 2] [Fintype F] {f : ℕ}

theorem trace_exists (hF : Fintype.card F = 2 ^ f) : ∃ b : F, ∑ j ∈ Finset.range f, b ^ 2 ^ j ≠ 0 := by
  let _ : Algebra (ZMod 2) F := ZMod.algebra F 2
  have hfin : Module.Finite (ZMod 2) F := Module.Finite.of_finite
  obtain ⟨b, hb⟩ := Algebra.trace_surjective (ZMod 2) F (1 : ZMod 2)
  refine ⟨b, ?_⟩
  have h1 := FiniteField.algebraMap_trace_eq_sum_pow (ZMod 2) F b
  have hcard : Nat.card (ZMod 2) = 2 := Nat.card_zmod 2
  have hrank : Module.finrank (ZMod 2) F = f := by
    have := Module.card_eq_pow_finrank (K := ZMod 2) (V := F)
    rw [hF, ZMod.card] at this
    exact (Nat.pow_right_injective (le_refl 2) this).symm
  rw [hcard, hrank, hb] at h1
  rw [← h1]
  simp

theorem trace_sq (hF : Fintype.card F = 2 ^ f) (x : F) :
    (∑ j ∈ Finset.range f, x ^ 2 ^ j) ^ 2 = ∑ j ∈ Finset.range f, x ^ 2 ^ j := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [sum_pow_char 2]
  have h1 : ∀ j : ℕ, (x ^ 2 ^ j) ^ 2 = x ^ 2 ^ (j + 1) := fun j => by
    rw [← pow_mul, pow_succ]
  simp_rw [h1]
  have h2 := Finset.sum_range_succ (fun j => x ^ 2 ^ j) f
  have h3 := Finset.sum_range_succ' (fun j => x ^ 2 ^ j) f
  have h4 : x ^ 2 ^ f = x := by
    rw [← hF, FiniteField.pow_card]
  rw [h2] at h3
  simp only [pow_zero, pow_one, h4] at h3
  exact (add_right_cancel h3).symm

theorem descent {n : ℕ} {G : Type} [Group G] (hF : Fintype.card F = 2 ^ f)
    (ρ₀ : G →* Matrix (Fin n) (Fin n) (ZMod 2))
    (hirr : ∀ N : Submodule (ZMod 2) (Fin n → ZMod 2),
      (∀ g, ∀ v ∈ N, (ρ₀ g).mulVec v ∈ N) → N = ⊥ ∨ N = ⊤)
    (M : Submodule F (Fin n → F))
    (hG : ∀ g, ∀ v ∈ M, ((ρ₀ g).map (ZMod.castHom (dvd_refl 2) F)).mulVec v ∈ M)
    (hΦ : ∀ v ∈ M, (fun i => v i ^ 2) ∈ M) (hM : M ≠ ⊥) : M = ⊤ := by
  classical
  set φ : ZMod 2 →+* F := ZMod.castHom (dvd_refl 2) F with hφ
  obtain ⟨v, hvM, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hM
  obtain ⟨i₀, hi₀⟩ : ∃ i₀, v i₀ ≠ 0 := by
    by_contra h
    push Not at h
    exact hv0 (funext h)
  obtain ⟨b, hb⟩ := trace_exists hF
  set lam : F := b / v i₀ with hlam
  have hw : ∀ j : ℕ, (fun i => (lam * v i) ^ 2 ^ j) ∈ M := by
    intro j
    induction j with
    | zero =>
      have : (fun i => (lam * v i) ^ 2 ^ 0) = lam • v := by
        funext i
        simp
      rw [this]
      exact M.smul_mem lam hvM
    | succ j ih =>
      have := hΦ _ ih
      convert this using 1
      funext i
      rw [← pow_mul, pow_succ]
  set u : Fin n → F := fun i => ∑ j ∈ Finset.range f, (lam * v i) ^ 2 ^ j with hu
  have huM : u ∈ M := by
    have : u = ∑ j ∈ Finset.range f, (fun i => (lam * v i) ^ 2 ^ j) := by
      funext i
      simp [hu, Finset.sum_apply]
    rw [this]
    exact Submodule.sum_mem _ fun j _ => hw j
  have hu0 : u i₀ ≠ 0 := by
    have : lam * v i₀ = b := by
      rw [hlam, div_mul_cancel₀ _ hi₀]
    simpa [hu, this] using hb
  have hu2 : ∀ i, u i ^ 2 = u i := fun i => trace_sq hF _
  let y : Fin n → ZMod 2 := fun i => if u i = 0 then 0 else 1
  have hy : (fun i => φ (y i)) = u := by
    funext i
    by_cases h : u i = 0
    · simp [y, h]
    · have h1 : u i = 1 := by
        have : u i * (u i - 1) = 0 := by
          rw [mul_sub, mul_one, ← sq, hu2, sub_self]
        rcases mul_eq_zero.mp this with h2 | h2
        · exact absurd h2 h
        · exact sub_eq_zero.mp h2
      simp [y, h1]
  let M₀ : Submodule (ZMod 2) (Fin n → ZMod 2) :=
    { carrier := {y | (fun i => φ (y i)) ∈ M}
      add_mem' := fun {a b} ha hb' => by
        show (fun i => φ ((a + b) i)) ∈ M
        have h1 : (fun i => φ ((a + b) i)) = (fun i => φ (a i)) + (fun i => φ (b i)) := by
          funext i
          simp
        rw [h1]
        exact M.add_mem ha hb'
      zero_mem' := by
        show (fun i => φ ((0 : Fin n → ZMod 2) i)) ∈ M
        have h1 : (fun i => φ ((0 : Fin n → ZMod 2) i)) = 0 := by
          funext i
          simp
        rw [h1]
        exact M.zero_mem
      smul_mem' := fun c a ha => by
        show (fun i => φ ((c • a) i)) ∈ M
        have h1 : (fun i => φ ((c • a) i)) = φ c • (fun i => φ (a i)) := by
          funext i
          simp
        rw [h1]
        exact M.smul_mem (φ c) ha }
  have hM₀G : ∀ g, ∀ w ∈ M₀, (ρ₀ g).mulVec w ∈ M₀ := by
    intro g w hw'
    show (fun i => φ (((ρ₀ g).mulVec w) i)) ∈ M
    have h1 : (fun i => φ (((ρ₀ g).mulVec w) i)) = ((ρ₀ g).map φ).mulVec (fun i => φ (w i)) := by
      funext i
      simp [Matrix.mulVec, dotProduct, map_sum]
    rw [h1]
    exact hG g _ hw'
  rcases hirr M₀ hM₀G with h0 | h1
  · exfalso
    have hyM₀ : y ∈ M₀ := by
      show (fun i => φ (y i)) ∈ M
      rw [hy]
      exact huM
    rw [h0] at hyM₀
    have : y = 0 := (Submodule.mem_bot _).mp hyM₀
    apply hu0
    rw [← hy]
    simp [this]
  · rw [eq_top_iff]
    intro w _
    have hbasis : ∀ i : Fin n, (Pi.single i (1 : F) : Fin n → F) ∈ M := by
      intro i
      have : (Pi.single i (1 : ZMod 2) : Fin n → ZMod 2) ∈ M₀ := by rw [h1]; exact Submodule.mem_top
      have h2 : (fun j => φ ((Pi.single i (1 : ZMod 2) : Fin n → ZMod 2) j)) =
          (Pi.single i (1 : F) : Fin n → F) := by
        funext j
        by_cases hij : j = i
        · subst hij
          simp
        · simp [hij]
      rw [← h2]
      exact this
    have : w = ∑ i, w i • (Pi.single i (1 : F) : Fin n → F) := by
      funext j
      simp [Finset.sum_apply, Pi.single_apply]
    rw [this]
    exact Submodule.sum_mem _ fun i _ => M.smul_mem _ (hbasis i)

end Descent

section Atoms

open scoped MonoidAlgebra
open CFSG.Semidihedral.Principal

variable {k G : Type} [Field k] [Group G] {V : Type} [AddCommGroup V] [Module k V]

theorem exists_atom_subrep [Module.Finite k V] (ρ : Representation k G V) [Nontrivial V] :
    ∃ U : Subrepresentation ρ, IsAtom U := by
  have hA : IsArtinian k[G] ρ.asModule := isArtinian_of_finiteDimensional k
  have : Nontrivial ρ.asModule :=
    (Equiv.nontrivial_congr ρ.asModuleEquiv.toEquiv).mpr inferInstance
  have : Nontrivial (Submodule k[G] ρ.asModule) :=
    (Submodule.nontrivial_iff k[G]).mpr inferInstance
  obtain ⟨N, hN, -⟩ := (IsAtomic.eq_bot_or_exists_atom_le (⊤ : Submodule k[G] ρ.asModule)).resolve_left
    top_ne_bot
  exact ⟨Subrepresentation.subrepresentationSubmoduleOrderIso.symm N,
    (OrderIso.isAtom_iff _ _).mpr hN⟩

theorem isIrreducible_of_atom (ρ : Representation k G V) (U : Subrepresentation ρ)
    (hU : IsAtom U) : U.toRepresentation.IsIrreducible := by
  refine { exists_pair_ne := ⟨⊥, ⊤, ?_⟩, eq_bot_or_eq_top := fun S => ?_ }
  · intro h
    apply hU.1
    apply Subrepresentation.toSubmodule_injective
    show U.toSubmodule = ⊥
    rw [eq_bot_iff]
    intro u hu
    have h1 : (⟨u, hu⟩ : U.toSubmodule) ∈ (⊤ : Subrepresentation U.toRepresentation).toSubmodule :=
      Submodule.mem_top
    rw [← h] at h1
    have h2 : (⟨u, hu⟩ : U.toSubmodule) ∈ (⊥ : Subrepresentation U.toRepresentation).toSubmodule :=
      h1
    have h3 : (⟨u, hu⟩ : U.toSubmodule) = 0 := (Submodule.mem_bot k).mp h2
    have := congrArg Subtype.val h3
    simpa using this
  · let S' : Subrepresentation ρ :=
      ⟨S.toSubmodule.map U.toSubmodule.subtype, fun g v hv => by
        obtain ⟨w, hw, rfl⟩ := hv
        exact ⟨U.toRepresentation g w, S.apply_mem_toSubmodule g hw, rfl⟩⟩
    have hS'le : S' ≤ U := by
      rintro _ ⟨w, -, rfl⟩
      exact w.2
    rcases hU.le_iff.mp hS'le with h | h
    · left
      apply Subrepresentation.toSubmodule_injective
      show S.toSubmodule = ⊥
      rw [eq_bot_iff]
      intro w hw
      have h1 : (w : V) ∈ S'.toSubmodule := ⟨w, hw, rfl⟩
      rw [h] at h1
      have h2 : (w : V) = 0 := (Submodule.mem_bot k).mp h1
      exact (Submodule.mem_bot k).mpr (Subtype.ext h2)
    · right
      apply Subrepresentation.toSubmodule_injective
      show S.toSubmodule = ⊤
      rw [eq_top_iff]
      intro w _
      have h1 : (w : V) ∈ S'.toSubmodule := by
        have h' : S'.toSubmodule = U.toSubmodule := congrArg Subrepresentation.toSubmodule h
        have hxU : (w : V) ∈ U.toSubmodule := w.2
        obtain ⟨x, hx⟩ : ∃ x : V, x = (w : V) := ⟨_, rfl⟩
        rw [← hx] at hxU ⊢
        rw [h']
        exact hxU
      obtain ⟨w', hw', hw'e⟩ := h1
      have : w' = w := Subtype.ext hw'e
      rw [← this]
      exact hw'

end Atoms

section Quotient

variable {k G : Type} [Field k] [Group G]

theorem exists_iso_of_surj_onto_irred {V E : Type} [AddCommGroup V] [Module k V] [AddCommGroup E]
    [Module k E] {ρ : Representation k G V} {σ : Representation k G E} (hσ : σ.IsIrreducible)
    (π : Representation.IntertwiningMap ρ σ) (hπ : Function.Surjective π)
    (M : ℕ → Subrepresentation ρ) (hM : ∀ j, (M j).toRepresentation.IsIrreducible)
    (hsup : ⨆ j, (M j).toSubmodule = ⊤) :
    ∃ j, Nonempty (Representation.Equiv (M j).toRepresentation σ) := by
  by_contra hcon
  push Not at hcon
  have hzero : ∀ j, ∀ v ∈ (M j).toSubmodule, π v = 0 := by
    intro j v hv
    have hirr := hM j
    let f : Representation.IntertwiningMap (M j).toRepresentation σ :=
      π.comp (CFSG.QuasithinUnique.Setup.X7b.subIncl ρ (M j))
    have := hσ
    rcases hirr.bijective_or_eq_zero f with hb | h0
    · exact ((hcon j).false (f.ofBijective hb)).elim
    · have := congrArg (fun F => F ⟨v, hv⟩) h0
      simpa [f, CFSG.QuasithinUnique.Setup.X7b.subIncl] using this
  have hker : ∀ v, π v = 0 := by
    intro v
    have hv : v ∈ ⨆ j, (M j).toSubmodule := by rw [hsup]; exact Submodule.mem_top
    exact Submodule.iSup_induction (fun j => (M j).toSubmodule) (motive := fun v => π v = 0) hv
      (fun j v hv => hzero j v hv) (map_zero _) (fun x y hx hy => by rw [map_add, hx, hy, add_zero])
  obtain ⟨hnt, -⟩ := (CFSG.QuasithinUnique.Setup.X7.isIrreducible_iff σ).mp hσ
  obtain ⟨e₁, e₂, he⟩ := exists_pair_ne E
  obtain ⟨v₁, rfl⟩ := hπ e₁
  obtain ⟨v₂, rfl⟩ := hπ e₂
  exact he (by rw [hker, hker])

end Quotient

section DualMap

open CFSG.QuasithinUnique.Setup.X7 (matRep matRep_apply MatIso dualMat dualMat_apply)
open CFSG.QuasithinUnique.Setup.X7b (toMatRep matRepEquiv)

variable {F : Type} [Field F] [CharP F 2] [Fintype F] {f n : ℕ}

omit [Fintype F] in
theorem exists_dual_surjection (PF : SL(3, F) →* Matrix (Fin n) (Fin n) F)
    {P Q : Matrix (Fin n) (Fin n) F} (hP : MatIso PF (dualMat PF) P Q)
    (W : Subrepresentation (matRep PF)) (a b : Fin f → Bool)
    (eW : Representation.Equiv (matRep (tensorRep (F := F) F a b)) W.toRepresentation) :
    ∃ π : Representation.IntertwiningMap (matRep PF) (matRep (tensorRep (F := F) F b a)),
      Function.Surjective π := by
  classical
  let m := Module.finrank F W.toSubmodule
  let bw : Module.Basis (Fin m) F W.toSubmodule := Module.finBasis F W.toSubmodule
  let Rw := toMatRep W.toRepresentation bw
  let B : Matrix (Fin n) (Fin m) F := Matrix.of fun i l => (bw l : Fin n → F) i
  have hB : ∀ g, PF g * B = B * Rw g := by
    intro g
    ext i l
    have h1 : (PF g * B) i l = ((W.toRepresentation g (bw l) : W.toSubmodule) : Fin n → F) i := by
      show (PF g).mulVec (bw l : Fin n → F) i = _
      rfl
    have h2 : (W.toRepresentation g (bw l)) = ∑ l', Rw g l' l • bw l' := by
      conv_lhs => rw [← bw.sum_repr (W.toRepresentation g (bw l))]
      refine Finset.sum_congr rfl fun l' _ => ?_
      simp [Rw, toMatRep, LinearMap.toMatrix_apply]
    rw [h1, h2]
    simp [Matrix.mul_apply, B, mul_comm]
  obtain ⟨P₁, Q₁, h₁⟩ := MatIso.exists_of_equiv
    (eW.trans (matRepEquiv W.toRepresentation bw))
  obtain ⟨P₃, Q₃, h₄⟩ : ∃ (P₃ : Matrix (TIdx f b a) (Fin m) F) (Q₃ : Matrix (Fin m) (TIdx f b a) F),
      MatIso (dualMat Rw) (tensorRep (F := F) F b a) P₃ Q₃ :=
    ⟨_, _, h₁.dual.trans (tensorRep_dual_iso (F := F) F a b)⟩
  have hcomm : ∀ g, P₃ * Bᵀ * P * PF g = tensorRep (F := F) F b a g * (P₃ * Bᵀ * P) := by
    intro g
    calc P₃ * Bᵀ * P * PF g = P₃ * Bᵀ * (P * PF g) := by rw [Matrix.mul_assoc _ P (PF g)]
      _ = P₃ * Bᵀ * (dualMat PF g * P) := by rw [hP.comm g]
      _ = P₃ * (Bᵀ * (PF g⁻¹)ᵀ) * P := by simp [dualMat_apply, Matrix.mul_assoc]
      _ = P₃ * (PF g⁻¹ * B)ᵀ * P := by rw [Matrix.transpose_mul]
      _ = P₃ * (B * Rw g⁻¹)ᵀ * P := by rw [hB g⁻¹]
      _ = P₃ * ((Rw g⁻¹)ᵀ * Bᵀ) * P := by rw [Matrix.transpose_mul]
      _ = (P₃ * dualMat Rw g) * Bᵀ * P := by simp [dualMat_apply, Matrix.mul_assoc]
      _ = tensorRep (F := F) F b a g * P₃ * Bᵀ * P := by rw [h₄.comm g]
      _ = tensorRep (F := F) F b a g * (P₃ * Bᵀ * P) := by simp [Matrix.mul_assoc]
  have hBinj : Function.Injective (Matrix.mulVecLin B) := by
    intro c c' hcc
    have hB' : ∀ c : Fin m → F, B.mulVec c = ((bw.equivFun.symm c : W.toSubmodule) : Fin n → F) := by
      intro c
      funext i
      simp [Matrix.mulVec, dotProduct, B, Module.Basis.equivFun_symm_apply, Finset.sum_apply, mul_comm]
    have h1 : bw.equivFun.symm c = bw.equivFun.symm c' :=
      Subtype.ext (by rw [← hB', ← hB']; exact hcc)
    exact bw.equivFun.symm.injective h1
  have hBt : Function.Surjective (Matrix.mulVecLin Bᵀ) := by
    have hr : B.rank = m := by
      rw [Matrix.rank, LinearMap.finrank_range_of_inj hBinj, Module.finrank_fintype_fun_eq_card,
        Fintype.card_fin]
    have hrt : Bᵀ.rank = m := by rw [Matrix.rank_transpose, hr]
    rw [← LinearMap.range_eq_top]
    refine Submodule.eq_top_of_finrank_eq ?_
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fin]
    exact hrt
  have hP₃ : Function.Surjective (Matrix.mulVecLin P₃) := fun y =>
    ⟨Q₃.mulVec y, by simp [Matrix.mulVec_mulVec, h₄.mul_inv]⟩
  have hPs : Function.Surjective (Matrix.mulVecLin P) := fun y =>
    ⟨Q.mulVec y, by simp [Matrix.mulVec_mulVec, hP.mul_inv]⟩
  refine ⟨⟨Matrix.mulVecLin (P₃ * Bᵀ * P), fun g => ?_⟩, ?_⟩
  · refine LinearMap.ext fun v => ?_
    simp only [LinearMap.comp_apply, Matrix.mulVecLin_apply, matRep_apply, Matrix.mulVec_mulVec,
      hcomm g]
  · show Function.Surjective (Matrix.mulVecLin (P₃ * Bᵀ * P))
    rw [Matrix.mulVecLin_mul, Matrix.mulVecLin_mul]
    exact hP₃.comp (hBt.comp hPs)

end DualMap

section Orbit

open CFSG.Semidihedral.Principal
open CFSG.QuasithinUnique.Setup.X7 (matRep matRep_apply matMap matMap_apply MatIso dualMat)
open CFSG.QuasithinUnique.Setup.X7b (TwistEquiv matRepTwist)

variable {F : Type} [Field F] [CharP F 2] [Fintype F] {f n : ℕ}

omit [Fintype F] in
theorem tensorRep_zeros_apply (g : SL(3, F)) :
    tensorRep (F := F) F (zeros f) (zeros f) g = 1 := by
  show kron (fun i : Fin f => locRep (F := F) F (zeros f i) (zeros f i) (i : ℕ) g) = 1
  have : (fun i : Fin f => locRep (F := F) F (zeros f i) (zeros f i) (i : ℕ) g) =
      fun i : Fin f => (1 : Matrix (Fin (locDim (zeros f i) (zeros f i)))
        (Fin (locDim (zeros f i) (zeros f i))) F) := by
    funext i
    exact MonoidHom.one_apply (M := SL(3, F)) (N := Matrix (Fin 1) (Fin 1) F) g
  rw [this]
  exact kron_one

theorem shiftBits_iterate_zeros (j : ℕ) : (shiftBits f)^[j] (zeros f) = zeros f :=
  Function.iterate_fixed rfl j

theorem exists_orbit_label (hF : Fintype.card F = 2 ^ f) (hf : 1 ≤ f)
    (ρ₀ : SL(3, F) →* Matrix (Fin n) (Fin n) (ZMod 2))
    (hirr : ∀ N : Submodule (ZMod 2) (Fin n → ZMod 2),
      (∀ g, ∀ v ∈ N, (ρ₀ g).mulVec v ∈ N) → N = ⊥ ∨ N = ⊤)
    (hnt : ∃ g, ρ₀ g ≠ 1) {P Q : Matrix (Fin n) (Fin n) F}
    (hP : MatIso (matMap (ZMod.castHom (dvd_refl 2) F) ρ₀)
      (dualMat (matMap (ZMod.castHom (dvd_refl 2) F) ρ₀)) P Q) :
    ∃ a b : Fin f → Bool, (a ≠ zeros f ∨ b ≠ zeros f) ∧
      (∀ j : ℕ, 0 < repMultiplicity (matRep (matMap (ZMod.castHom (dvd_refl 2) F) ρ₀))
        (matRep (tensorRep (F := F) F ((shiftBits f)^[j] a) ((shiftBits f)^[j] b)))) ∧
      ∃ j₀ : ℕ, (shiftBits f)^[j₀] a = b ∧ (shiftBits f)^[j₀] b = a := by
  classical
  set φ : ZMod 2 →+* F := ZMod.castHom (dvd_refl 2) F with hφ
  set PF := matMap φ ρ₀ with hPF
  have hτ : ∀ j : ℕ, matMap (frobPowEquiv F j : F →+* F) PF = PF := by
    intro j
    rw [hPF, ← matMap_comp_ringHom]
    congr 1
    exact RingHom.ext_zmod _ _
  let Ψ : ∀ j : ℕ, TwistEquiv (frobPowEquiv F j) (matRep PF) (matRep PF) := fun j =>
    { e := (matRepTwist (frobPowEquiv F j) PF).e
      comm := fun g v => by
        have hent : ∀ i' j', (frobPowEquiv F j) (PF g i' j') = PF g i' j' := fun i' j' =>
          congrFun (congrFun (congrArg (fun R => R g) (hτ j)) i') j'
        funext i
        show frobPowEquiv F j ((PF g).mulVec v i) =
          (PF g).mulVec (fun i' => frobPowEquiv F j (v i')) i
        simp [Matrix.mulVec, dotProduct, map_sum, hent] }
  have hΨ : ∀ (j : ℕ) (w : Fin n → F) (i : Fin n), (Ψ j).e w i = w i ^ 2 ^ j := fun j w i =>
    frobPowEquiv_apply j (w i)
  have hn : 0 < n := by
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h
      obtain ⟨g, hg⟩ := hnt
      exact absurd (Subsingleton.elim _ _) hg
    · exact h
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  obtain ⟨W, hW⟩ := exists_atom_subrep (matRep PF)
  have hWirr := isIrreducible_of_atom (matRep PF) W hW
  obtain ⟨a, b, ⟨eW⟩⟩ := exists_T3_equiv F hF hf W.toRepresentation hWirr
  let Wj : ℕ → Subrepresentation (matRep PF) := fun j => (Ψ j).mapSub W
  have hWj : ∀ j, (Wj j).toRepresentation.IsIrreducible := fun j =>
    ((Ψ j).sub W).isIrreducible hWirr
  have heq : ∀ j : ℕ, Nonempty (Representation.Equiv (Wj j).toRepresentation
      (matRep (tensorRep (F := F) F ((shiftBits f)^[j] a) ((shiftBits f)^[j] b)))) := by
    intro j
    have h1 := ((Ψ j).sub W).nonempty_equiv_iff
      (matRepTwist (frobPowEquiv F j) (tensorRep (F := F) F a b))
    have h2 : Nonempty (Representation.Equiv (Wj j).toRepresentation
        (matRep (CFSG.QuasithinUnique.Setup.X7.matMap (frobPowEquiv F j : F →+* F)
          (tensorRep (F := F) F a b)))) := h1.mpr ⟨eW.symm⟩
    rw [matMap_frobPowEquiv_tensorRep] at h2
    obtain ⟨P', Q', hM⟩ := tensorRep_comp_frobPow F hF j a b
    exact ⟨h2.some.trans hM.equiv.some⟩
  have hmult : ∀ j : ℕ, 0 < repMultiplicity (matRep PF)
      (matRep (tensorRep (F := F) F ((shiftBits f)^[j] a) ((shiftBits f)^[j] b))) := by
    intro j
    obtain ⟨e⟩ := heq j
    have h1 := CFSG.QuasithinUnique.Setup.X7b.repMultiplicity_sub_quot (matRep PF) (Wj j)
      (matRep (tensorRep (F := F) F ((shiftBits f)^[j] a) ((shiftBits f)^[j] b)))
    have h2 : repMultiplicity (Wj j).toRepresentation
        (matRep (tensorRep (F := F) F ((shiftBits f)^[j] a) ((shiftBits f)^[j] b))) = 1 := by
      rw [repMultiplicity_congr_left e, repMultiplicity_of_isIrreducible
        ((tensorRep_absolutely_irreducible_and_distinct F hF hf).1 _ _).1]
      have hrefl : Nonempty (Representation.Equiv
          (matRep (tensorRep (F := F) F ((shiftBits f)^[j] a) ((shiftBits f)^[j] b)))
          (matRep (tensorRep (F := F) F ((shiftBits f)^[j] a) ((shiftBits f)^[j] b)))) :=
        ⟨Representation.Equiv.refl _⟩
      simp [hrefl]
    omega
  let M : Submodule F (Fin n → F) := ⨆ j, (Wj j).toSubmodule
  have hG : ∀ g, ∀ v ∈ M, ((ρ₀ g).map φ).mulVec v ∈ M := by
    intro g v hv
    refine Submodule.iSup_induction (fun j => (Wj j).toSubmodule)
      (motive := fun v => ((ρ₀ g).map φ).mulVec v ∈ M) hv
      (fun j v hv => Submodule.mem_iSup_of_mem j ((Wj j).apply_mem_toSubmodule g hv))
      (by simp) (fun x y hx hy => by rw [Matrix.mulVec_add]; exact M.add_mem hx hy)
  have hΦ : ∀ v ∈ M, (fun i => v i ^ 2) ∈ M := by
    intro v hv
    refine Submodule.iSup_induction (fun j => (Wj j).toSubmodule)
      (motive := fun v => (fun i => v i ^ 2) ∈ M) hv ?_ ?_ ?_
    · intro j v hv
      obtain ⟨w, hw, rfl⟩ := hv
      have h1 : (fun i => ((Ψ j).e w) i ^ 2) = (Ψ (j + 1)).e w := by
        funext i
        rw [hΨ, hΨ, ← pow_mul, pow_succ]
      show (fun i => ((Ψ j).e w) i ^ 2) ∈ M
      rw [h1]
      exact Submodule.mem_iSup_of_mem (j + 1) (Submodule.mem_map_of_mem hw)
    · have : (fun i : Fin n => (0 : Fin n → F) i ^ 2) = 0 := by
        funext i
        simp
      rw [this]
      exact M.zero_mem
    · intro x y hx hy
      have : (fun i => (x + y) i ^ 2) = (fun i => x i ^ 2) + (fun i => y i ^ 2) := by
        funext i
        simp [CharTwo.add_sq]
      rw [this]
      exact M.add_mem hx hy
  have hWne : W.toSubmodule ≠ ⊥ := fun h => hW.1 (Subrepresentation.toSubmodule_injective h)
  have hMne : M ≠ ⊥ := by
    obtain ⟨w, hwW, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hWne
    have hmem : (Ψ 0).e w ∈ M :=
      Submodule.mem_iSup_of_mem 0 (Submodule.mem_map_of_mem hwW)
    have hne : (Ψ 0).e w ≠ 0 := fun h => hw0 ((Ψ 0).e.injective (by rw [h, map_zero]))
    exact fun h => hne ((Submodule.mem_bot F).mp (h ▸ hmem))
  have hMtop : M = ⊤ := descent hF ρ₀ hirr M hG hΦ hMne
  obtain ⟨π, hπ⟩ := exists_dual_surjection PF hP W a b eW
  obtain ⟨j₀, ⟨e₀⟩⟩ := exists_iso_of_surj_onto_irred
    ((tensorRep_absolutely_irreducible_and_distinct F hF hf).1 b a).1 π hπ Wj hWj hMtop
  obtain ⟨e₁⟩ := heq j₀
  have hlast := (tensorRep_absolutely_irreducible_and_distinct F hF hf).2 _ _ _ _
    ⟨e₁.symm.trans e₀⟩
  have hne : a ≠ zeros f ∨ b ≠ zeros f := by
    by_contra hcon
    push Not at hcon
    obtain ⟨rfl, rfl⟩ := hcon
    have htriv : ∀ j, ∀ v ∈ (Wj j).toSubmodule, ∀ g, matRep PF g v = v := by
      intro j v hv g
      obtain ⟨e⟩ := heq j
      rw [shiftBits_iterate_zeros] at e
      let v' : (Wj j).toSubmodule := ⟨v, hv⟩
      have h1 := Representation.IntertwiningMap.isIntertwining _ _ e.toIntertwiningMap g v'
      rw [matRep_apply, tensorRep_zeros_apply, Matrix.one_mulVec] at h1
      have h2 : (Wj j).toRepresentation g v' = v' := e.toLinearEquiv.injective h1
      exact congrArg Subtype.val h2
    have hall : ∀ g, ∀ v : Fin n → F, matRep PF g v = v := by
      intro g v
      have hv : v ∈ M := by rw [hMtop]; exact Submodule.mem_top
      exact Submodule.iSup_induction (fun j => (Wj j).toSubmodule)
        (motive := fun v => matRep PF g v = v) hv (fun j v hv => htriv j v hv g)
        (by simp) (fun x y hx hy => by rw [map_add, hx, hy])
    obtain ⟨g, hg⟩ := hnt
    apply hg
    have h1 : PF g = 1 := by
      ext i j
      have := congrFun (hall g (Pi.single j 1)) i
      simpa [matRep_apply, Matrix.mulVec_single_one, Matrix.one_apply, Pi.single_apply,
        eq_comm] using this
    have h2 : (ρ₀ g).map φ = (1 : Matrix (Fin n) (Fin n) (ZMod 2)).map φ := by
      rw [Matrix.map_one φ (map_zero φ) (map_one φ)]
      exact h1
    exact Matrix.map_injective φ.injective h2
  exact ⟨a, b, hne, hmult, j₀, hlast.1, hlast.2⟩

end Orbit

end CFSG.QuasithinUnique.Setup.X7a
