module

public import Mathlib.RepresentationTheory.Irreducible

public section

namespace CFSG.CharacterTheory.SteinbergBY

open Module
open scoped Matrix

section Norton

variable {K G V : Type*} [Field K] [Group G] [AddCommGroup V] [Module K V]

theorem isIrreducible_of_norton [FiniteDimensional K V] [Nontrivial V] (ρ : Representation K G V)
    (A : V →ₗ[K] V) (hAU : ∀ U : Subrepresentation ρ, ∀ u ∈ U, A u ∈ U)
    (hspin : ∀ v : V, A v = 0 → v ≠ 0 → ∀ U : Subrepresentation ρ, v ∈ U → U = ⊤)
    (w : V →ₗ[K] K) (hw : w ∘ₗ A = 0)
    (hsep : ∀ x : V, (∀ g, w (ρ g x) = 0) → x = 0) : ρ.IsIrreducible := by
  have hbt : (⊥ : Subrepresentation ρ) ≠ ⊤ := by
    intro h
    obtain ⟨v, hv⟩ := exists_ne (0 : V)
    have hvtop : v ∈ (⊤ : Subrepresentation ρ) := Submodule.mem_top
    rw [← h] at hvtop
    exact hv ((Submodule.mem_bot K).mp hvtop)
  have : Nontrivial (Subrepresentation ρ) := ⟨⟨⊥, ⊤, hbt⟩⟩
  refine ⟨fun U => ?_⟩
  by_cases hk : ∃ u ∈ U, u ≠ 0 ∧ A u = 0
  · obtain ⟨u, huU, hu0, hAu⟩ := hk
    exact Or.inr (hspin u hAu hu0 U huU)
  · push Not at hk
    left
    set f : U.toSubmodule →ₗ[K] U.toSubmodule :=
      A.restrict fun u hu => hAU U u hu with hfdef
    have hfinj : Function.Injective f := by
      rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
      intro x hx
      by_contra hx0
      apply hk x.1 x.2 (fun h => hx0 (Subtype.ext h))
      exact congrArg Subtype.val hx
    have hfsurj : Function.Surjective f := LinearMap.surjective_of_injective hfinj
    have hwU : ∀ u ∈ U, w u = 0 := by
      intro u hu
      obtain ⟨u', hu'⟩ := hfsurj ⟨u, hu⟩
      have h1 : A u'.1 = u := congrArg Subtype.val hu'
      rw [← h1]
      exact LinearMap.congr_fun hw u'.1
    ext x
    constructor
    · intro hx
      have h0 : x = 0 := hsep x fun g => hwU _ (U.apply_mem_toSubmodule g hx)
      rw [h0]
      exact Submodule.zero_mem _
    · intro hx
      have h0 : x = 0 := (Submodule.mem_bot K).mp hx
      rw [h0]
      exact Submodule.zero_mem _

end Norton

section Certificate

variable {F K G : Type*} [Field F] [Field K] [Group G] (φ : F →+* K) {n : ℕ}

@[expose] noncomputable def matrixBaseChange (M : G →* Matrix (Fin n) (Fin n) F) :
    Representation K G (Fin n → K) :=
  (Matrix.toLinAlgEquiv' : Matrix (Fin n) (Fin n) K ≃ₐ[K] Module.End K (Fin n → K)).toMonoidHom.comp
    ((φ.mapMatrix : Matrix (Fin n) (Fin n) F →+* Matrix (Fin n) (Fin n) K).toMonoidHom.comp M)

theorem matrixBaseChange_apply (M : G →* Matrix (Fin n) (Fin n) F) (g : G) (x : Fin n → K) :
    matrixBaseChange φ M g x = (M g).map φ *ᵥ x := rfl

theorem matrixBaseChange_comp {E : Type*} [Field E] (ψ : E →+* F)
    (M : G →* Matrix (Fin n) (Fin n) E) :
    matrixBaseChange φ ((ψ.mapMatrix : Matrix (Fin n) (Fin n) E →+* _).toMonoidHom.comp M) =
      matrixBaseChange (φ.comp ψ) M :=
  rfl

theorem list_sum_map_mulVec_mem (M : G →* Matrix (Fin n) (Fin n) F) (l : List (G × F))
    (U : Subrepresentation (matrixBaseChange φ M)) {u : Fin n → K} (hu : u ∈ U) :
    ((l.map fun p => p.2 • M p.1).sum.map φ) *ᵥ u ∈ U := by
  induction l with
  | nil =>
    rw [List.map_nil, List.sum_nil, Matrix.map_zero φ φ.map_zero, Matrix.zero_mulVec]
    exact Submodule.zero_mem _
  | cons p l ih =>
    rw [List.map_cons, List.sum_cons, Matrix.map_add φ φ.map_add, Matrix.add_mulVec]
    refine Submodule.add_mem _ ?_ ih
    have h1 : (p.2 • M p.1).map φ *ᵥ u = φ p.2 • matrixBaseChange φ M p.1 u := by
      rw [matrixBaseChange_apply, ← Matrix.smul_mulVec]
      congr 1
      ext i j
      simp [map_mul]
    rw [h1]
    exact Submodule.smul_mem _ _ (U.apply_mem_toSubmodule p.1 hu)

theorem isIrreducible_matrixBaseChange_of_cert [NeZero n] (M : G →* Matrix (Fin n) (Fin n) F)
    (l : List (G × F)) (Q Qi R : Matrix (Fin n) (Fin n) F) (hQ : Qi * Q = 1)
    (hR : R * (l.map fun p => p.2 • M p.1).sum * Q =
      Matrix.diagonal fun j : Fin n => if j = 0 then 0 else 1)
    (S Si : Matrix (Fin n) (Fin n) F) (hS : ∀ j, ∃ g, ∀ i, S i j = (M g *ᵥ fun l => Q l 0) i)
    (hSi : Si * S = 1)
    (w : Fin n → F) (hwA : w ᵥ* (l.map fun p => p.2 • M p.1).sum = 0)
    (T Ti : Matrix (Fin n) (Fin n) F) (hT : ∀ i, ∃ g, ∀ j, T i j = (w ᵥ* M g) j)
    (hTi : Ti * T = 1) : (matrixBaseChange φ M).IsIrreducible := by
  classical
  set ρ := matrixBaseChange φ M with hρ
  set A := (l.map fun p => p.2 • M p.1).sum with hAdef
  set v : Fin n → F := fun l => Q l 0 with hv
  choose h hh using hS
  choose kk hkk using hT
  set vK : Fin n → K := φ ∘ v with hvK
  have hQQi : Q * Qi = 1 := mul_eq_one_comm.mp hQ
  have hSSi : S * Si = 1 := mul_eq_one_comm.mp hSi
  have hkerK : ∀ x : Fin n → K, A.map φ *ᵥ x = 0 → ∃ t : K, x = t • vK := by
    intro x hx
    set y := Qi.map φ *ᵥ x with hy
    have hxy : x = Q.map φ *ᵥ y := by
      rw [hy, Matrix.mulVec_mulVec, ← Matrix.map_mul, hQQi, Matrix.map_one φ φ.map_zero φ.map_one,
        Matrix.one_mulVec]
    have hD : (Matrix.diagonal fun j : Fin n => if j = 0 then (0 : K) else 1) *ᵥ y = 0 := by
      have h1 : (R * A * Q).map φ =
          Matrix.diagonal fun j : Fin n => if j = 0 then (0 : K) else 1 := by
        rw [hR]
        ext i j
        by_cases hij : i = j
        · subst hij
          by_cases hi : i = 0 <;> simp [hi]
        · simp [hij]
      rw [← h1, Matrix.map_mul, Matrix.map_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
        ← hxy, hx, Matrix.mulVec_zero]
    have hy0 : ∀ j, j ≠ 0 → y j = 0 := by
      intro j hj
      have := congrFun hD j
      simpa [Matrix.mulVec_diagonal, hj] using this
    refine ⟨y 0, ?_⟩
    rw [hxy]
    funext i
    simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul, hvK, Function.comp_apply]
    rw [Finset.sum_eq_single 0 (fun j _ hj => by rw [hy0 j hj, mul_zero])
      (fun h => absurd (Finset.mem_univ 0) h)]
    rw [Matrix.map_apply, mul_comm]
  have hspinv : ∀ U : Subrepresentation ρ, vK ∈ U → U = ⊤ := by
    intro U hvU
    have hcol : ∀ j, (fun i => S.map φ i j) ∈ U := by
      intro j
      have h1 : (fun i => S.map φ i j) = ρ (h j) vK := by
        funext i
        rw [Matrix.map_apply, hh, RingHom.map_mulVec, matrixBaseChange_apply]
      rw [h1]
      exact U.apply_mem_toSubmodule (h j) hvU
    have hbasis : ∀ i, (Pi.single i (1 : K) : Fin n → K) ∈ U := by
      intro i
      have h2 : (Pi.single i (1 : K) : Fin n → K) =
          ∑ j, Si.map φ j i • (fun l => S.map φ l j) := by
        funext l
        have h3 := congrFun (congrFun (congrArg (Matrix.map · φ) hSSi) l) i
        simp only [Matrix.map_mul, Matrix.map_one φ φ.map_zero φ.map_one] at h3
        rw [Finset.sum_apply]
        simp only [Pi.smul_apply, smul_eq_mul]
        rw [Matrix.mul_apply] at h3
        rw [Pi.single_apply, ← Matrix.one_apply, ← h3]
        exact Finset.sum_congr rfl fun j _ => mul_comm _ _
      rw [h2]
      exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (hcol j)
    refine eq_top_iff.mpr fun x _ => ?_
    have hx : x = ∑ i, x i • (Pi.single i (1 : K) : Fin n → K) := by
      funext l
      simp [Finset.sum_apply, Pi.single_apply]
    rw [hx]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hbasis i)
  set wK : (Fin n → K) →ₗ[K] K :=
    { toFun := fun x => (φ ∘ w) ⬝ᵥ x
      map_add' := fun x y => dotProduct_add _ _ _
      map_smul' := fun t x => by rw [dotProduct_smul, RingHom.id_apply, smul_eq_mul] } with hwK
  have hwK0 : wK ∘ₗ Matrix.toLin' (A.map φ) = 0 := by
    refine LinearMap.ext fun x => ?_
    rw [LinearMap.comp_apply, Matrix.toLin'_apply, LinearMap.zero_apply]
    change (φ ∘ w) ⬝ᵥ (A.map φ *ᵥ x) = 0
    rw [Matrix.dotProduct_mulVec]
    have h1 : (φ ∘ w) ᵥ* A.map φ = 0 := by
      funext j
      rw [← RingHom.map_vecMul, hwA, Pi.zero_apply, map_zero, Pi.zero_apply]
    rw [h1, zero_dotProduct]
  have hsep : ∀ x : Fin n → K, (∀ g, wK (ρ g x) = 0) → x = 0 := by
    intro x hx
    have hTx : T.map φ *ᵥ x = 0 := by
      funext i
      have h1 := hx (kk i)
      change (φ ∘ w) ⬝ᵥ ((M (kk i)).map φ *ᵥ x) = 0 at h1
      rw [Matrix.dotProduct_mulVec] at h1
      rw [Pi.zero_apply, ← h1]
      simp only [Matrix.mulVec, dotProduct]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Matrix.map_apply, hkk, RingHom.map_vecMul]
    have hTiT : (Ti * T).map φ = 1 := by
      rw [hTi, Matrix.map_one φ φ.map_zero φ.map_one]
    calc x = (Ti * T).map φ *ᵥ x := by rw [hTiT, Matrix.one_mulVec]
      _ = Ti.map φ *ᵥ (T.map φ *ᵥ x) := by rw [Matrix.map_mul, Matrix.mulVec_mulVec]
      _ = 0 := by rw [hTx, Matrix.mulVec_zero]
  have hAU : ∀ U : Subrepresentation ρ, ∀ u ∈ U, Matrix.toLin' (A.map φ) u ∈ U := by
    intro U u hu
    rw [Matrix.toLin'_apply]
    exact list_sum_map_mulVec_mem φ M l U hu
  refine isIrreducible_of_norton ρ _ hAU (fun x hx hx0 U hxU => ?_) wK hwK0 hsep
  rw [Matrix.toLin'_apply] at hx
  obtain ⟨t, rfl⟩ := hkerK x hx
  have ht : t ≠ 0 := fun h => hx0 (by rw [h, zero_smul])
  apply hspinv U
  have := U.toSubmodule.smul_mem t⁻¹ hxU
  rwa [smul_smul, inv_mul_cancel₀ ht, one_smul] at this

end Certificate

section Tables

variable {α : Type*} {m n : ℕ}

@[expose] def tab (A : Matrix (Fin m) (Fin n) α) : Vector (Vector α n) m :=
  Vector.ofFn fun i => Vector.ofFn fun j => A i j

@[expose] def untab (t : Vector (Vector α n) m) : Matrix (Fin m) (Fin n) α :=
  Matrix.of fun i j => t[i][j]

@[simp] theorem untab_tab (A : Matrix (Fin m) (Fin n) α) : untab (tab A) = A := by
  ext i j
  simp [tab, untab]

theorem untab_apply (t : Vector (Vector α n) m) (i : Fin m) (j : Fin n) :
    untab t i j = t[i][j] := rfl

end Tables

section CheckedCertificate

variable {F K G : Type*} [Field F] [Field K] [Group G] {n : ℕ}

structure NortonData (G F : Type*) (n : ℕ) where
  terms : List (G × F)
  Q : Vector (Vector F n) n
  Qi : Vector (Vector F n) n
  R : Vector (Vector F n) n
  S : Vector (Vector F n) n
  Si : Vector (Vector F n) n
  spin : Vector G n
  w : Vector F n
  T : Vector (Vector F n) n
  Ti : Vector (Vector F n) n
  dual : Vector G n

@[expose] def sumTerms (l : List (F × Vector (Vector F n) n)) : Vector (Vector F n) n :=
  tab (l.map fun q => q.1 • untab q.2).sum

@[expose] def NortonData.checkWith [DecidableEq F] [NeZero n] (d : NortonData G F n)
    (A : Vector (Vector F n) n) (spinM dualM : Vector (Vector (Vector F n) n) n) : Bool :=
  decide (untab d.Qi * untab d.Q = 1) &&
  decide (untab (tab (untab d.R * untab A)) * untab d.Q =
    Matrix.diagonal fun j : Fin n => if j = 0 then 0 else 1) &&
  decide (∀ j i : Fin n, d.S[i][j] = (untab spinM[j] *ᵥ fun l => d.Q[l][(0 : Fin n)]) i) &&
  decide (untab d.Si * untab d.S = 1) &&
  decide ((fun l => d.w[l]) ᵥ* untab A = 0) &&
  decide (∀ i j : Fin n, d.T[i][j] = ((fun l => d.w[l]) ᵥ* untab dualM[i]) j) &&
  decide (untab d.Ti * untab d.T = 1)

@[expose] def NortonData.check [DecidableEq F] [NeZero n] (Mt : G → Vector (Vector F n) n)
    (d : NortonData G F n) : Bool :=
  d.checkWith (sumTerms (d.terms.map fun p => (p.2, Mt p.1))) (d.spin.map Mt) (d.dual.map Mt)

theorem NortonData.isIrreducible_of_check [DecidableEq F] [NeZero n] (φ : F →+* K)
    (M : G →* Matrix (Fin n) (Fin n) F) (Mt : G → Vector (Vector F n) n)
    (hMt : ∀ g, untab (Mt g) = M g) (d : NortonData G F n) (h : d.check Mt = true) :
    (matrixBaseChange φ M).IsIrreducible := by
  simp only [NortonData.check, NortonData.checkWith, untab_tab, Bool.and_eq_true,
    decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨hQ, hR⟩, hS⟩, hSi⟩, hw⟩, hT⟩, hTi⟩ := h
  have hsum : ((d.terms.map fun p => (p.2, Mt p.1)).map fun q => q.1 • untab q.2) =
      d.terms.map fun p => p.2 • M p.1 := by
    rw [List.map_map]
    exact List.map_congr_left fun p _ => by simp [hMt]
  simp only [sumTerms, untab_tab] at hR hw
  rw [hsum] at hR hw
  refine isIrreducible_matrixBaseChange_of_cert φ M d.terms (untab d.Q) (untab d.Qi)
    (untab d.R) hQ hR (untab d.S) (untab d.Si) (fun j => ⟨d.spin[j], fun i => ?_⟩) hSi
    (fun l => d.w[l]) hw (untab d.T) (untab d.Ti) (fun i => ⟨d.dual[i], fun j => ?_⟩) hTi
  · have h2 : (d.spin.map Mt)[j] = Mt d.spin[j] := by simp
    rw [untab_apply, hS j i, h2, hMt]
    rfl
  · have h2 : (d.dual.map Mt)[i] = Mt d.dual[i] := by simp
    rw [untab_apply, hT i j, h2, hMt]

end CheckedCertificate

end CFSG.CharacterTheory.SteinbergBY
