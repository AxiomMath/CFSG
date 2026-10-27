module

public import CFSG.HardMathSupport.U4FF.ClassTmodIrr
public import CFSG.HardMathSupport.U4FF.Omega2Defs

public section

namespace CFSG.HardMathSupport.U4FF

open Matrix
open scoped MatrixGroups
open CFSG.LieType.Universal.Unitary (antidiag)

section KronSingle

variable {k : Type*} [Field k] {ι : Type*} [Fintype ι] [DecidableEq ι]
  (κ : ι → Type*) [∀ i, Fintype (κ i)] [∀ i, DecidableEq (κ i)]

theorem kronDep_single (i₀ : ι) (z : (i : ι) → Matrix (κ i) (κ i) k)
    (hz : ∀ i, i ≠ i₀ → Subsingleton (κ i) ∧ z i = 1) (x y : (i : ι) → κ i) :
    kronDep κ z x y = z i₀ (x i₀) (y i₀) := by
  rw [kronDep_apply, Finset.prod_eq_single i₀]
  · intro i _ hi
    obtain ⟨hs, h1⟩ := hz i hi
    rw [h1, Subsingleton.elim (x i) (y i), Matrix.one_apply_eq]
  · intro h
    exact absurd (Finset.mem_univ i₀) h

@[expose] noncomputable def singleEquiv (i₀ : ι) [∀ i, Nonempty (κ i)]
    (hs : ∀ i, i ≠ i₀ → Subsingleton (κ i)) : ((i : ι) → κ i) ≃ κ i₀ where
  toFun x := x i₀
  invFun y := fun i => if h : i = i₀ then h ▸ y else Classical.arbitrary (κ i)
  left_inv x := by
    funext i
    by_cases h : i = i₀
    · subst h
      simp
    · haveI := hs i h
      simp only [h, dite_false]
      exact Subsingleton.elim _ _
  right_inv y := by
    simp

theorem singleEquiv_symm_apply (i₀ : ι) [∀ i, Nonempty (κ i)]
    (hs : ∀ i, i ≠ i₀ → Subsingleton (κ i)) (y : κ i₀) :
    (singleEquiv κ i₀ hs).symm y i₀ = y := by
  have := (singleEquiv κ i₀ hs).apply_symm_apply y
  exact this

end KronSingle

section Ambient

variable {k : Type*} [Field k]

local instance uniqueFinSingleton (K : FK) : Unique (Fin ([K] : List FK).length) :=
  inferInstanceAs (Unique (Fin 1))

@[expose] noncomputable def ambSigma (K : FK) : Fin (ambDim [K]) ≃ Fin K.dim :=
  (ambEq [K]).symm.trans
    (Equiv.piUnique (fun i : Fin ([K] : List FK).length => Fin (([K] : List FK).get i).dim))

theorem ambRepF_single (K : FK) (g : SL(4, k)) (c d : Fin (ambDim [K])) :
    ambRepF k [K] g c d = repK k K g (ambSigma K c) (ambSigma K d) := by
  rw [ambRepF_apply, Matrix.submatrix_apply, ambRep_apply, kronDep_apply, Fintype.prod_unique]
  rfl

end Ambient

section IsoCore

variable {k : Type*} [Field k]

theorem iso_core {N : ℕ} {G : Type*} (Bm Pm : Matrix (Fin N) (Fin N) k) (hPB : Pm * Bm = 1)
    (σ : Fin N ≃ Fin N) (X L Amb : G → Matrix (Fin N) (Fin N) k)
    (hAmb : ∀ g c d, Amb g c d = X g (σ c) (σ d)) (hcomm : ∀ g, Amb g * Bm = Bm * L g) :
    ∃ B : GL (Fin N) k, ∀ g, (B : Matrix (Fin N) (Fin N) k) * L g =
      X g * (B : Matrix (Fin N) (Fin N) k) := by
  classical
  have hBP : Bm * Pm = 1 := mul_eq_one_comm.mp hPB
  set B' : Matrix (Fin N) (Fin N) k := Bm.submatrix σ.symm id with hB'
  have hQ : B' * Pm.submatrix id σ.symm = 1 := by
    ext x x'
    have := congrFun (congrFun hBP (σ.symm x)) (σ.symm x')
    simp only [Matrix.mul_apply, Matrix.submatrix_apply, id, Matrix.one_apply, hB'] at this ⊢
    rw [this]
    simp [σ.symm.injective.eq_iff]
  have hdet : IsUnit B'.det := Matrix.isUnit_det_of_right_inverse hQ
  refine ⟨Matrix.GeneralLinearGroup.mk'' B' hdet, fun g => ?_⟩
  show B' * L g = X g * B'
  ext x y
  have h := congrFun (congrFun (hcomm g) (σ.symm x)) y
  simp only [Matrix.mul_apply, hAmb, Equiv.apply_symm_apply] at h
  simp only [hB', Matrix.mul_apply, Matrix.submatrix_apply, id]
  rw [← h]
  exact (Fintype.sum_equiv σ.symm _ _ fun c => by simp).symm

end IsoCore

section LocIso

variable {k : Type*} [Field k] [CharP k 2]

theorem sq_z_zero {N : ℕ} {k₀ : Type*} [Field k₀] (Pm B : Matrix (Fin N) (Fin N) k₀)
    (z : Fin N → k₀) (h : Pm * B = 1) (hz : Pm *ᵥ z = 0) : z = 0 := by
  have hBP : B * Pm = 1 := mul_eq_one_comm.mp h
  calc z = (B * Pm) *ᵥ z := by rw [hBP, Matrix.one_mulVec]
    _ = B *ᵥ (Pm *ᵥ z) := by rw [Matrix.mulVec_mulVec]
    _ = 0 := by rw [hz, Matrix.mulVec_zero]

theorem amb_comm_of_z_zero {fs : List FK} (S : LocSpec fs) (hz : S.z = 0) (g : SL(4, k)) :
    ambRepF k fs g * S.Bk k = S.Bk k * S.locMat k g := by
  have hzk : S.zk k = 0 := by
    funext x
    show f2 k (S.z x) = 0
    rw [hz]
    simp
  have h := S.amb_B k g
  rw [hzk] at h
  rw [h]
  ext x y
  simp [Matrix.vecMulVec_apply]

@[expose] noncomputable def locRN (k : Type*) [Field k] [CharP k 2] :
    SL(4, k) →* Matrix (Fin 4) (Fin 4) k := locR true false false k

@[expose] noncomputable def locRS (k : Type*) [Field k] [CharP k 2] :
    SL(4, k) →* Matrix (Fin 4) (Fin 4) k := locR false false true k

@[expose] noncomputable def locRW (k : Type*) [Field k] [CharP k 2] :
    SL(4, k) →* Matrix (Fin 6) (Fin 6) k := locR false true false k

theorem locR_N_iso : ∃ B : GL (Fin 4) k, ∀ g : SL(4, k),
    (B : Matrix (Fin 4) (Fin 4) k) * locRN k g = (g : Matrix (Fin 4) (Fin 4) k) * B := by
  set S := locSpec true false false (locValid true false false).1 with hS
  have hz : S.z = 0 := sq_z_zero S.Pm S.B S.z S.pm_B S.pm_z
  exact iso_core (G := SL(4, k)) (S.Bk k) (S.Pmk k) (S.Pmk_Bk k) (ambSigma FK.N)
    (fun g : SL(4, k) => (g : Matrix (Fin 4) (Fin 4) k)) (fun g : SL(4, k) => locRN k g)
    (fun g : SL(4, k) => (ambRepF k (fsOf true false false) g : Matrix (Fin 4) (Fin 4) k))
    (fun g c d => ambRepF_single FK.N g c d) (amb_comm_of_z_zero S hz)

theorem locR_S_iso : ∃ B : GL (Fin 4) k, ∀ g : SL(4, k),
    (B : Matrix (Fin 4) (Fin 4) k) * locRS k g = repS k g * B := by
  set S := locSpec false false true (locValid false false true).1 with hS
  have hz : S.z = 0 := sq_z_zero S.Pm S.B S.z S.pm_B S.pm_z
  exact iso_core (G := SL(4, k)) (S.Bk k) (S.Pmk k) (S.Pmk_Bk k) (ambSigma FK.S)
    (fun g : SL(4, k) => repS k g) (fun g : SL(4, k) => locRS k g)
    (fun g : SL(4, k) => (ambRepF k (fsOf false false true) g : Matrix (Fin 4) (Fin 4) k))
    (fun g c d => ambRepF_single FK.S g c d) (amb_comm_of_z_zero S hz)

theorem locR_W_iso : ∃ B : GL (Fin 6) k, ∀ g : SL(4, k),
    (B : Matrix (Fin 6) (Fin 6) k) * locRW k g = compound2 (g : Matrix (Fin 4) (Fin 4) k) * B := by
  set S := locSpec false true false (locValid false true false).1 with hS
  have hz : S.z = 0 := sq_z_zero S.Pm S.B S.z S.pm_B S.pm_z
  exact iso_core (G := SL(4, k)) (S.Bk k) (S.Pmk k) (S.Pmk_Bk k) (ambSigma FK.W)
    (fun g : SL(4, k) => compound2 (g : Matrix (Fin 4) (Fin 4) k))
    (fun g : SL(4, k) => locRW k g)
    (fun g : SL(4, k) => (ambRepF k (fsOf false true false) g : Matrix (Fin 6) (Fin 6) k))
    (fun g c d => ambRepF_single FK.W g c d) (amb_comm_of_z_zero S hz)

end LocIso

section TmodSingle

variable {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}
  {E : Type} [Field E] [CharP E 2] [Algebra K E]

theorem locR_zero_of (a b c : Bool) (ha : a = false) (hb : b = false) (hc : c = false)
    {k : Type*} [Field k] [CharP k 2] (g : SL(4, k)) : locR a b c k g = 1 := by
  subst ha hb hc
  exact locR_000 g

theorem Tmod_single (l : Lbl n) (i₀ : Fin n) (hz : ∀ i, i ≠ i₀ → l.ZeroAt i) (a b c : Bool)
    (ha : l.a i₀ = a) (hb : l.b i₀ = b) (hc : l.c i₀ = c) :
    ∃ e : TIdx l ≃ Fin (locM a b c), ∀ g : SU4 K n,
      Matrix.reindex e e (Tmod K l E g) = locR a b c E (twistHom n (frobTw K E i₀) g) := by
  subst ha hb hc
  have hs : ∀ i, i ≠ i₀ → Subsingleton (Fin (locM (l.a i) (l.b i) (l.c i))) := by
    intro i hi
    obtain ⟨h1, h2, h3⟩ := hz i hi
    rw [h1, h2, h3]
    exact inferInstanceAs (Subsingleton (Fin 1))
  refine ⟨singleEquiv (fun i : Fin n => Fin (locM (l.a i) (l.b i) (l.c i))) i₀ hs, fun g => ?_⟩
  ext x y
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply]
  rw [Tmod_eq, TmodΦ_apply,
    kronDep_single (fun i : Fin n => Fin (locM (l.a i) (l.b i) (l.c i))) i₀ _ (fun i hi =>
      ⟨hs i hi, by
        obtain ⟨h1, h2, h3⟩ := hz i hi
        exact locR_zero_of _ _ _ h1 h2 h3 _⟩),
    singleEquiv_symm_apply, singleEquiv_symm_apply]

theorem Tmod_single_N (l : Lbl n) (i₀ : Fin n) (hz : ∀ i, i ≠ i₀ → l.ZeroAt i)
    (ha : l.a i₀ = true) (hb : l.b i₀ = false) (hc : l.c i₀ = false) :
    ∃ (e : TIdx l ≃ Fin 4) (P : GL (Fin 4) E), ∀ g : SU4 K n,
      (P : Matrix (Fin 4) (Fin 4) E) * Matrix.reindex e e (Tmod K l E g) =
        (((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).map (frobTw K E i₀)) *
          (P : Matrix (Fin 4) (Fin 4) E) := by
  obtain ⟨e₀, he₀⟩ := Tmod_single (K := K) (E := E) l i₀ hz true false false ha hb hc
  obtain ⟨B, hB⟩ := locR_N_iso (k := E)
  let e : TIdx l ≃ Fin 4 := e₀
  have he : ∀ g : SU4 K n, Matrix.reindex e e (Tmod K l E g) =
      locRN E (twistHom n (frobTw K E i₀) g) := fun g => he₀ g
  refine ⟨e, B, fun g => ?_⟩
  rw [he, hB]
  rfl

theorem repS_twist (i₀ : ℕ) (g : SU4 K n) :
    repS E (twistHom n (frobTw K E i₀) g) =
      (antidiag 4 : Matrix (Fin 4) (Fin 4) E) *
        (((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).map (frobTw K E (i₀ + n))) *
          antidiag 4 := by
  ext i j
  rw [J_mul_mul_J_apply]
  have h1 : ((((twistHom n (frobTw K E i₀) g)⁻¹ : SL(4, E)) : Matrix (Fin 4) (Fin 4) E)) =
      (((((g⁻¹ : SU4 K n) : GL (Fin 4) K)) : Matrix (Fin 4) (Fin 4) K)).map (frobTw K E i₀) := by
    rw [← map_inv]
    rfl
  show ((((twistHom n (frobTw K E i₀) g)⁻¹ : SL(4, E)) : Matrix (Fin 4) (Fin 4) E)ᵀ) i j = _
  rw [Matrix.transpose_apply, h1, Matrix.map_apply, su_inv_apply, Matrix.map_apply,
    frobTw_apply, frobTw_apply, map_pow, ← map_pow, ← pow_mul, ← pow_add, add_comm]

theorem Tmod_single_S (l : Lbl n) (i₀ : Fin n) (hz : ∀ i, i ≠ i₀ → l.ZeroAt i)
    (ha : l.a i₀ = false) (hb : l.b i₀ = false) (hc : l.c i₀ = true) :
    ∃ (e : TIdx l ≃ Fin 4) (P : GL (Fin 4) E), ∀ g : SU4 K n,
      (P : Matrix (Fin 4) (Fin 4) E) * Matrix.reindex e e (Tmod K l E g) =
        (((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).map (frobTw K E (i₀ + n))) *
          (P : Matrix (Fin 4) (Fin 4) E) := by
  obtain ⟨e₀, he₀⟩ := Tmod_single (K := K) (E := E) l i₀ hz false false true ha hb hc
  obtain ⟨B, hB⟩ := locR_S_iso (k := E)
  let e : TIdx l ≃ Fin 4 := e₀
  have he : ∀ g : SU4 K n, Matrix.reindex e e (Tmod K l E g) =
      locRS E (twistHom n (frobTw K E i₀) g) := fun g => he₀ g
  refine ⟨e, jGL E * B, fun g => ?_⟩
  have hJ : (antidiag 4 : Matrix (Fin 4) (Fin 4) E) * antidiag 4 = 1 := J_mul_J
  have h2 := hB (twistHom n (frobTw K E i₀) g)
  rw [repS_twist] at h2
  have hP : ((jGL E * B : GL (Fin 4) E) : Matrix (Fin 4) (Fin 4) E) =
      antidiag 4 * (B : Matrix (Fin 4) (Fin 4) E) := rfl
  rw [hP, he]
  rw [Matrix.mul_assoc, h2]
  calc (antidiag 4 : Matrix (Fin 4) (Fin 4) E) *
        ((antidiag 4 : Matrix (Fin 4) (Fin 4) E) *
          (((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).map (frobTw K E (i₀ + n))) *
            antidiag 4 * (B : Matrix (Fin 4) (Fin 4) E))
      = ((antidiag 4 : Matrix (Fin 4) (Fin 4) E) * antidiag 4) *
          (((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).map (frobTw K E (i₀ + n))) *
            (antidiag 4 * (B : Matrix (Fin 4) (Fin 4) E)) := by
        simp only [Matrix.mul_assoc]
    _ = _ := by rw [hJ, Matrix.one_mul]

theorem Tmod_single_O (l : Lbl n) (i₀ : Fin n) (hz : ∀ i, i ≠ i₀ → l.ZeroAt i)
    (ha : l.a i₀ = false) (hb : l.b i₀ = true) (hc : l.c i₀ = false) :
    ∃ (e : TIdx l ≃ Fin 6) (P : GL (Fin 6) E), ∀ g : SU4 K n,
      (P : Matrix (Fin 6) (Fin 6) E) * Matrix.reindex e e (Tmod K l E g) =
        comp2 (((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).map (frobTw K E i₀)) *
          (P : Matrix (Fin 6) (Fin 6) E) := by
  obtain ⟨e₀, he₀⟩ := Tmod_single (K := K) (E := E) l i₀ hz false true false ha hb hc
  obtain ⟨B, hB⟩ := locR_W_iso (k := E)
  let e : TIdx l ≃ Fin 6 := e₀
  have he : ∀ g : SU4 K n, Matrix.reindex e e (Tmod K l E g) =
      locRW E (twistHom n (frobTw K E i₀) g) := fun g => he₀ g
  refine ⟨e, B, fun g => ?_⟩
  rw [he, hB]
  rfl

end TmodSingle

end CFSG.HardMathSupport.U4FF
