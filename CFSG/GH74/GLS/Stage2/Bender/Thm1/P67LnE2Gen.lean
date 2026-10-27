module

public import CFSG.GH74.GLS.Stage2.OddAut.BlockTorus
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67LnToral

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1.Ln.E2

open Module Matrix CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.GH74.GLS.Stage2.Signalizer.Odd87 CFSG.GH74.GLS.Stage2.OddAut.BlockTorus

section Ops

variable (K : Type) [Field K] [Finite K] (p : ℕ) [Fact p.Prime] [CharP K p] (s : ℕ)

@[expose] noncomputable def Dl (φ : Module.End K (Lq K p)) : Module.End K (Em K p s) :=
  (φ.prodMap LinearMap.id).prodMap LinearMap.id

@[expose] noncomputable def Dr (ψ : Module.End K (Lq K p)) : Module.End K (Em K p s) :=
  (LinearMap.id.prodMap ψ).prodMap LinearMap.id

@[expose] noncomputable def upN (φ : Module.End K (Lq K p)) : Module.End K (Em K p s) :=
  (LinearMap.inl K (Lq K p × Lq K p) (Fin s → K)) ∘ₗ (LinearMap.inl K (Lq K p) (Lq K p)) ∘ₗ φ ∘ₗ
    (LinearMap.snd K (Lq K p) (Lq K p)) ∘ₗ (LinearMap.fst K (Lq K p × Lq K p) (Fin s → K))

@[expose] noncomputable def loN (ψ : Module.End K (Lq K p)) : Module.End K (Em K p s) :=
  (LinearMap.inl K (Lq K p × Lq K p) (Fin s → K)) ∘ₗ (LinearMap.inr K (Lq K p) (Lq K p)) ∘ₗ ψ ∘ₗ
    (LinearMap.fst K (Lq K p) (Lq K p)) ∘ₗ (LinearMap.fst K (Lq K p × Lq K p) (Fin s → K))

variable {K p s}

theorem Dl_apply (φ : Module.End K (Lq K p)) (x y : Lq K p) (z : Fin s → K) :
    Dl K p s φ ((x, y), z) = ((φ x, y), z) := rfl

theorem Dr_apply (ψ : Module.End K (Lq K p)) (x y : Lq K p) (z : Fin s → K) :
    Dr K p s ψ ((x, y), z) = ((x, ψ y), z) := rfl

theorem upN_apply (φ : Module.End K (Lq K p)) (x y : Lq K p) (z : Fin s → K) :
    upN K p s φ ((x, y), z) = ((φ y, 0), 0) := rfl

theorem loN_apply (ψ : Module.End K (Lq K p)) (x y : Lq K p) (z : Fin s → K) :
    loN K p s ψ ((x, y), z) = ((0, ψ x), 0) := rfl

theorem Dl_mul (φ φ' : Module.End K (Lq K p)) : Dl K p s φ * Dl K p s φ' = Dl K p s (φ * φ') := by
  refine LinearMap.ext fun ⟨⟨x, y⟩, z⟩ => ?_
  simp [Dl_apply]

theorem Dr_mul (ψ ψ' : Module.End K (Lq K p)) : Dr K p s ψ * Dr K p s ψ' = Dr K p s (ψ * ψ') := by
  refine LinearMap.ext fun ⟨⟨x, y⟩, z⟩ => ?_
  simp [Dr_apply]

theorem Dl_one : Dl K p s (1 : Module.End K (Lq K p)) = 1 := by
  refine LinearMap.ext fun ⟨⟨x, y⟩, z⟩ => ?_
  simp [Dl_apply]

theorem Dr_one : Dr K p s (1 : Module.End K (Lq K p)) = 1 := by
  refine LinearMap.ext fun ⟨⟨x, y⟩, z⟩ => ?_
  simp [Dr_apply]

theorem upN_mul_upN (φ φ' : Module.End K (Lq K p)) : upN K p s φ * upN K p s φ' = 0 := by
  refine LinearMap.ext fun ⟨⟨x, y⟩, z⟩ => ?_
  simp [upN_apply]

theorem loN_mul_loN (ψ ψ' : Module.End K (Lq K p)) : loN K p s ψ * loN K p s ψ' = 0 := by
  refine LinearMap.ext fun ⟨⟨x, y⟩, z⟩ => ?_
  simp [loN_apply]

theorem Dl_mul_upN (P φ : Module.End K (Lq K p)) : Dl K p s P * upN K p s φ = upN K p s (P * φ) := by
  refine LinearMap.ext fun ⟨⟨x, y⟩, z⟩ => ?_
  simp [Dl_apply, upN_apply]

theorem upN_mul_Dl (P φ : Module.End K (Lq K p)) : upN K p s φ * Dl K p s P = upN K p s φ := by
  refine LinearMap.ext fun ⟨⟨x, y⟩, z⟩ => ?_
  simp [Dl_apply, upN_apply]

theorem upN_add (φ φ' : Module.End K (Lq K p)) : upN K p s (φ + φ') = upN K p s φ + upN K p s φ' := by
  refine LinearMap.ext fun ⟨⟨x, y⟩, z⟩ => ?_
  simp [upN_apply]

theorem loN_add (ψ ψ' : Module.End K (Lq K p)) : loN K p s (ψ + ψ') = loN K p s ψ + loN K p s ψ' := by
  refine LinearMap.ext fun ⟨⟨x, y⟩, z⟩ => ?_
  simp [loN_apply]

theorem Dr_mul_loN (Q ψ : Module.End K (Lq K p)) : Dr K p s Q * loN K p s ψ = loN K p s (Q * ψ) := by
  refine LinearMap.ext fun ⟨⟨x, y⟩, z⟩ => ?_
  simp [Dr_apply, loN_apply]

theorem loN_mul_Dr (Q ψ : Module.End K (Lq K p)) : loN K p s ψ * Dr K p s Q = loN K p s ψ := by
  refine LinearMap.ext fun ⟨⟨x, y⟩, z⟩ => ?_
  simp [Dr_apply, loN_apply]

end Ops

section Units

variable (K : Type) [Field K] [Finite K] (p : ℕ) [Fact p.Prime] [CharP K p] (s : ℕ)

omit [Fact p.Prime] [Finite K] in
theorem det_one_add_of_sq_zero {M : Type*} [AddCommGroup M] [Module K M] [Module.Finite K M]
    [Module.Free K M] (q : ℕ) [Fact q.Prime] [CharP K q] (N : Module.End K M) (hN : N * N = 0) :
    LinearMap.det (1 + N) = 1 := by
  have hpow : ∀ k : ℕ, (1 + N) ^ k = 1 + k • N := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ, ih]
      have : (1 + k • N) * (1 + N) = 1 + N + k • N + k • (N * N) := by
        simp only [mul_add, add_mul, one_mul, mul_one, smul_mul_assoc]
        abel
      rw [this, hN, smul_zero, add_zero, succ_nsmul]
      abel
  have h1 : (1 + N) ^ q = 1 := by
    rw [hpow, ← Nat.cast_smul_eq_nsmul K, CharP.cast_eq_zero, zero_smul, add_zero]
  have h2 : (LinearMap.det (1 + N)) ^ q = 1 := by
    rw [← map_pow, h1, map_one]
  have h3 : (LinearMap.det (1 + N) - 1) ^ q = 0 := by
    rw [sub_pow_char, h2, one_pow, sub_self]
  exact sub_eq_zero.mp ((pow_eq_zero_iff (Fact.out : q.Prime).ne_zero).mp h3)

end Units

section Span

variable (K : Type) [Field K] [Finite K] (p : ℕ) [Fact p.Prime] [CharP K p]

theorem span_of_SL (S : AddSubgroup (Module.End K (Lq K p)))
    (hS : ∀ P : (Module.End K (Lq K p))ˣ, LinearMap.det (P : Module.End K (Lq K p)) = 1 →
      (P : Module.End K (Lq K p)) ∈ S) : S = ⊤ := by
  classical
  let Ψ := LinearMap.toMatrixAlgEquiv (bLq K p)
  have hSL : ∀ M : Matrix (Fin 2) (Fin 2) K, M.det = 1 → Ψ.symm M ∈ S := by
    intro M hM
    have hdet : LinearMap.det (Ψ.symm M) = 1 := by
      have h := LinearMap.det_toMatrix (bLq K p) (Ψ.symm M)
      have h2 : LinearMap.toMatrix (bLq K p) (bLq K p) (Ψ.symm M) = M := Ψ.apply_symm_apply M
      rw [h2] at h
      rw [← h, hM]
    refine hS ⟨Ψ.symm M, Ψ.symm M.adjugate, ?_, ?_⟩ hdet
    · rw [← map_mul, Matrix.mul_adjugate, hM, one_smul, map_one]
    · rw [← map_mul, Matrix.adjugate_mul, hM, one_smul, map_one]
  rw [eq_top_iff]
  intro φ _
  obtain ⟨a, b, c, d, hM⟩ : ∃ a b c d : K, Ψ φ = !![a, b; c, d] :=
    ⟨Ψ φ 0 0, Ψ φ 0 1, Ψ φ 1 0, Ψ φ 1 1, Matrix.eta_fin_two _⟩
  have hφ : φ = Ψ.symm !![a, b; c, d] := by rw [← hM]; simp
  have e1 : (!![a, b; c, d] : Matrix (Fin 2) (Fin 2) K) =
      !![a, 1; -1, 0] + !![0, -1; 1, 0] + (!![1, b; 0, 1] - 1) + (!![1, 0; c, 1] - 1) +
        (!![0, 1; -1, d] + !![0, -1; 1, 0]) := by
    ext i j; fin_cases i <;> fin_cases j <;> simp
  rw [hφ, e1]
  have h1 : (!![a, 1; -1, 0] : Matrix (Fin 2) (Fin 2) K).det = 1 := by simp [Matrix.det_fin_two]
  have h2 : (!![0, -1; 1, 0] : Matrix (Fin 2) (Fin 2) K).det = 1 := by simp [Matrix.det_fin_two]
  have h3 : (!![1, b; 0, 1] : Matrix (Fin 2) (Fin 2) K).det = 1 := by simp [Matrix.det_fin_two]
  have h4 : (!![1, 0; c, 1] : Matrix (Fin 2) (Fin 2) K).det = 1 := by simp [Matrix.det_fin_two]
  have h5 : (!![0, 1; -1, d] : Matrix (Fin 2) (Fin 2) K).det = 1 := by simp [Matrix.det_fin_two]
  simp only [map_add, map_sub, map_one]
  exact S.add_mem (S.add_mem (S.add_mem (S.add_mem (hSL _ h1) (hSL _ h2))
    (S.sub_mem (hSL _ h3) (by simpa using S.zero_mem |> fun _ => hS 1 (by simp)))) 
    (S.sub_mem (hSL _ h4) (hS 1 (by simp)))) (S.add_mem (hSL _ h5) (hSL _ h2))

end Span

section Elem

variable (K : Type) [Field K] [Finite K] (p : ℕ) [Fact p.Prime] [CharP K p] (s : ℕ)

@[expose] def oneAddU {A : Type*} [Ring A] (N : A) (hN : N * N = 0) : Aˣ where
  val := 1 + N
  inv := 1 - N
  val_inv := by
    calc (1 + N) * (1 - N) = 1 - N * N := by noncomm_ring
      _ = 1 := by rw [hN, sub_zero]
  inv_val := by
    calc (1 - N) * (1 + N) = 1 - N * N := by noncomm_ring
      _ = 1 := by rw [hN, sub_zero]

theorem det_dl (P : Module.End K (Lq K p)) :
    LinearMap.det (Dl K p s P) = LinearMap.det P := by
  unfold Dl
  rw [LinearMap.det_prodMap, LinearMap.det_prodMap]
  simp

theorem det_dr (Q : Module.End K (Lq K p)) :
    LinearMap.det (Dr K p s Q) = LinearMap.det Q := by
  unfold Dr
  rw [LinearMap.det_prodMap, LinearMap.det_prodMap]
  simp

@[expose] noncomputable def oneAddSL (N : Module.End K (Em K p s)) (hN : N * N = 0) : SLE K p s :=
  ⟨oneAddU N hN, det_one_add_of_sq_zero K p N hN⟩

@[expose] noncomputable def upSL (φ : Module.End K (Lq K p)) : SLE K p s :=
  oneAddSL K p s (upN K p s φ) (upN_mul_upN φ φ)

@[expose] noncomputable def loSL (ψ : Module.End K (Lq K p)) : SLE K p s :=
  oneAddSL K p s (loN K p s ψ) (loN_mul_loN ψ ψ)

@[expose] noncomputable def dlSL (P : (Module.End K (Lq K p))ˣ)
    (hP : LinearMap.det (P : Module.End K (Lq K p)) = 1) : SLE K p s :=
  ⟨⟨Dl K p s (P : Module.End K (Lq K p)), Dl K p s ((P⁻¹ : (Module.End K (Lq K p))ˣ) :
      Module.End K (Lq K p)), by rw [Dl_mul, Units.mul_inv, Dl_one],
    by rw [Dl_mul, Units.inv_mul, Dl_one]⟩, by
    rw [mem_SLE]
    show LinearMap.det (Dl K p s (P : Module.End K (Lq K p))) = 1
    rw [det_dl, hP]⟩

@[expose] noncomputable def drSL (Q : (Module.End K (Lq K p))ˣ)
    (hQ : LinearMap.det (Q : Module.End K (Lq K p)) = 1) : SLE K p s :=
  ⟨⟨Dr K p s (Q : Module.End K (Lq K p)), Dr K p s ((Q⁻¹ : (Module.End K (Lq K p))ˣ) :
      Module.End K (Lq K p)), by rw [Dr_mul, Units.mul_inv, Dr_one],
    by rw [Dr_mul, Units.inv_mul, Dr_one]⟩, by
    rw [mem_SLE]
    show LinearMap.det (Dr K p s (Q : Module.End K (Lq K p))) = 1
    rw [det_dr, hQ]⟩

theorem upN_zero : upN K p s (0 : Module.End K (Lq K p)) = 0 := by
  refine LinearMap.ext fun ⟨⟨x, y⟩, z⟩ => ?_
  simp [upN_apply]

theorem loN_zero : loN K p s (0 : Module.End K (Lq K p)) = 0 := by
  refine LinearMap.ext fun ⟨⟨x, y⟩, z⟩ => ?_
  simp [loN_apply]

theorem upSL_add (φ φ' : Module.End K (Lq K p)) :
    upSL K p s (φ + φ') = upSL K p s φ * upSL K p s φ' := by
  apply Subtype.ext
  apply Units.ext
  show 1 + upN K p s (φ + φ') = (1 + upN K p s φ) * (1 + upN K p s φ')
  rw [upN_add, mul_add, add_mul, add_mul, one_mul, mul_one, upN_mul_upN, add_zero]
  abel

theorem upSL_zero : upSL K p s (0 : Module.End K (Lq K p)) = 1 := by
  apply Subtype.ext
  apply Units.ext
  show 1 + upN K p s 0 = 1
  rw [upN_zero, add_zero]

theorem upSL_neg (φ : Module.End K (Lq K p)) : upSL K p s (-φ) = (upSL K p s φ)⁻¹ := by
  have h := upSL_add K p s φ (-φ)
  rw [add_neg_cancel, upSL_zero] at h
  exact (inv_eq_of_mul_eq_one_right h.symm).symm

theorem loSL_add (ψ ψ' : Module.End K (Lq K p)) :
    loSL K p s (ψ + ψ') = loSL K p s ψ * loSL K p s ψ' := by
  apply Subtype.ext
  apply Units.ext
  show 1 + loN K p s (ψ + ψ') = (1 + loN K p s ψ) * (1 + loN K p s ψ')
  rw [loN_add, mul_add, add_mul, add_mul, one_mul, mul_one, loN_mul_loN, add_zero]
  abel

theorem loSL_zero : loSL K p s (0 : Module.End K (Lq K p)) = 1 := by
  apply Subtype.ext
  apply Units.ext
  show 1 + loN K p s 0 = 1
  rw [loN_zero, add_zero]

theorem loSL_neg (ψ : Module.End K (Lq K p)) : loSL K p s (-ψ) = (loSL K p s ψ)⁻¹ := by
  have h := loSL_add K p s ψ (-ψ)
  rw [add_neg_cancel, loSL_zero] at h
  exact (inv_eq_of_mul_eq_one_right h.symm).symm

theorem dlSL_conj_upSL (P : (Module.End K (Lq K p))ˣ)
    (hP : LinearMap.det (P : Module.End K (Lq K p)) = 1) (φ : Module.End K (Lq K p)) :
    dlSL K p s P hP * upSL K p s φ * (dlSL K p s P hP)⁻¹ =
      upSL K p s ((P : Module.End K (Lq K p)) * φ) := by
  apply Subtype.ext
  apply Units.ext
  show Dl K p s (P : Module.End K (Lq K p)) * (1 + upN K p s φ) *
    Dl K p s ((P⁻¹ : (Module.End K (Lq K p))ˣ) : Module.End K (Lq K p)) =
    1 + upN K p s ((P : Module.End K (Lq K p)) * φ)
  rw [mul_add, mul_one, Dl_mul_upN, add_mul, Dl_mul, Units.mul_inv, Dl_one, upN_mul_Dl]

theorem drSL_conj_loSL (Q : (Module.End K (Lq K p))ˣ)
    (hQ : LinearMap.det (Q : Module.End K (Lq K p)) = 1) (ψ : Module.End K (Lq K p)) :
    drSL K p s Q hQ * loSL K p s ψ * (drSL K p s Q hQ)⁻¹ =
      loSL K p s ((Q : Module.End K (Lq K p)) * ψ) := by
  apply Subtype.ext
  apply Units.ext
  show Dr K p s (Q : Module.End K (Lq K p)) * (1 + loN K p s ψ) *
    Dr K p s ((Q⁻¹ : (Module.End K (Lq K p))ˣ) : Module.End K (Lq K p)) =
    1 + loN K p s ((Q : Module.End K (Lq K p)) * ψ)
  rw [mul_add, mul_one, Dr_mul_loN, add_mul, Dr_mul, Units.mul_inv, Dr_one, loN_mul_Dr]

theorem up_all (T' : Subgroup (SLE K p s))
    (hDl : ∀ (P : (Module.End K (Lq K p))ˣ) (hP : LinearMap.det (P : Module.End K (Lq K p)) = 1),
      dlSL K p s P hP ∈ T')
    (hUp : upSL K p s (1 : Module.End K (Lq K p)) ∈ T') : ∀ φ, upSL K p s φ ∈ T' := by
  let S : AddSubgroup (Module.End K (Lq K p)) :=
    { carrier := {φ | upSL K p s φ ∈ T'}
      zero_mem' := by
        show upSL K p s 0 ∈ T'
        rw [upSL_zero]; exact T'.one_mem
      add_mem' := fun {a b} ha hb => by
        show upSL K p s (a + b) ∈ T'
        rw [upSL_add]; exact T'.mul_mem ha hb
      neg_mem' := fun {a} ha => by
        show upSL K p s (-a) ∈ T'
        rw [upSL_neg]; exact T'.inv_mem ha }
  have hS : S = ⊤ := span_of_SL K p S (fun P hP => by
    have h := T'.mul_mem (T'.mul_mem (hDl P hP) hUp) (T'.inv_mem (hDl P hP))
    rw [dlSL_conj_upSL, mul_one] at h
    exact h)
  intro φ
  have : φ ∈ S := hS ▸ AddSubgroup.mem_top φ
  exact this

theorem lo_all (T' : Subgroup (SLE K p s))
    (hDr : ∀ (Q : (Module.End K (Lq K p))ˣ) (hQ : LinearMap.det (Q : Module.End K (Lq K p)) = 1),
      drSL K p s Q hQ ∈ T')
    (hLo : loSL K p s (1 : Module.End K (Lq K p)) ∈ T') : ∀ ψ, loSL K p s ψ ∈ T' := by
  let S : AddSubgroup (Module.End K (Lq K p)) :=
    { carrier := {ψ | loSL K p s ψ ∈ T'}
      zero_mem' := by
        show loSL K p s 0 ∈ T'
        rw [loSL_zero]; exact T'.one_mem
      add_mem' := fun {a b} ha hb => by
        show loSL K p s (a + b) ∈ T'
        rw [loSL_add]; exact T'.mul_mem ha hb
      neg_mem' := fun {a} ha => by
        show loSL K p s (-a) ∈ T'
        rw [loSL_neg]; exact T'.inv_mem ha }
  have hS : S = ⊤ := span_of_SL K p S (fun Q hQ => by
    have h := T'.mul_mem (T'.mul_mem (hDr Q hQ) hLo) (T'.inv_mem (hDr Q hQ))
    rw [drSL_conj_loSL, mul_one] at h
    exact h)
  intro ψ
  have : ψ ∈ S := hS ▸ AddSubgroup.mem_top ψ
  exact this

end Elem

section ElemMat

variable (K : Type) [Field K] [Finite K] (p : ℕ) [Fact p.Prime] [CharP K p] (s : ℕ)

@[expose] noncomputable def eL (α β : Fin 2) : Module.End K (Lq K p) :=
  ((bLq K p).coord β).smulRight (bLq K p α)

@[expose] noncomputable def NB (a b : (Fin 2 ⊕ Fin 2) ⊕ Fin s) : Module.End K (Em K p s) :=
  ((Bs K p s).coord b).smulRight ((Bs K p s) a)

variable {K p s}

theorem Bs_ll (α : Fin 2) : Bs K p s (Sum.inl (Sum.inl α)) = ((bLq K p α, 0), 0) := by
  simp [Bs]

theorem Bs_lr (α : Fin 2) : Bs K p s (Sum.inl (Sum.inr α)) = ((0, bLq K p α), 0) := by
  simp [Bs]

theorem coord_ll (β : Fin 2) (x y : Lq K p) (z : Fin s → K) :
    (Bs K p s).coord (Sum.inl (Sum.inl β)) ((x, y), z) = (bLq K p).coord β x := by
  simp [Bs, Module.Basis.coord_apply]

theorem coord_lr (β : Fin 2) (x y : Lq K p) (z : Fin s → K) :
    (Bs K p s).coord (Sum.inl (Sum.inr β)) ((x, y), z) = (bLq K p).coord β y := by
  simp [Bs, Module.Basis.coord_apply]

theorem Bs_repr_ll (β : Fin 2) (x y : Lq K p) (z : Fin s → K) :
    (Bs K p s).repr ((x, y), z) (Sum.inl (Sum.inl β)) = (bLq K p).repr x β := by
  simp [Bs]

theorem Bs_repr_lr (β : Fin 2) (x y : Lq K p) (z : Fin s → K) :
    (Bs K p s).repr ((x, y), z) (Sum.inl (Sum.inr β)) = (bLq K p).repr y β := by
  simp [Bs]

theorem NB_mul_NB_self {a b : (Fin 2 ⊕ Fin 2) ⊕ Fin s} (hab : a ≠ b) :
    NB K p s a b * NB K p s a b = 0 := by
  refine LinearMap.ext fun v => ?_
  simp [NB, Module.Basis.coord_apply, Module.Basis.repr_self, hab.symm]

theorem eL_mul_eL_self {α β : Fin 2} (h : α ≠ β) : eL K p α β * eL K p α β = 0 := by
  refine LinearMap.ext fun v => ?_
  simp [eL, Module.Basis.coord_apply, Module.Basis.repr_self, h.symm]

end ElemMat

section Gen4

variable (K : Type) [Field K] [Finite K] (p : ℕ) [Fact p.Prime] [CharP K p] (s : ℕ)

@[expose] noncomputable def elemSL (a b : (Fin 2 ⊕ Fin 2) ⊕ Fin s) (hab : a ≠ b) (t : K) : SLE K p s :=
  oneAddSL K p s (t • NB K p s a b) (by
    rw [smul_mul_assoc, mul_smul_comm, NB_mul_NB_self hab, smul_zero, smul_zero])

theorem toSL_elemSL (a b : (Fin 2 ⊕ Fin 2) ⊕ Fin s) (hab : a ≠ b) (t : K) :
    toSL K p s (elemSL K p s a b hab t) =
      Matrix.SpecialLinearGroup.transvection ((eSum s).injective.ne hab) t := by
  apply Subtype.ext
  apply (ΦA K p s).injective
  rw [ΦA_toSL, CFSG.LinearGroups.coe_transvection, map_add, map_one, ΦA_single']
  rfl

theorem rootElt_eq_rho (g : GL (Fin (4 + s)) K) (a b : (Fin 2 ⊕ Fin 2) ⊕ Fin s) (hab : a ≠ b)
    (t : K) :
    CFSG.GH74.GLS.Stage2.Bender.Thm1.Ln.rootElt g ((eSum s).injective.ne hab) t =
      rho K p s g (elemSL K p s a b hab t) := by
  unfold CFSG.GH74.GLS.Stage2.Bender.Thm1.Ln.rootElt rho
  simp [toSL_elemSL]

theorem elem_mem_zero (T' : Subgroup (SLE K p 0))
    (hDl : ∀ (P : (Module.End K (Lq K p))ˣ) (hP : LinearMap.det (P : Module.End K (Lq K p)) = 1),
      dlSL K p 0 P hP ∈ T')
    (hDr : ∀ (Q : (Module.End K (Lq K p))ˣ) (hQ : LinearMap.det (Q : Module.End K (Lq K p)) = 1),
      drSL K p 0 Q hQ ∈ T')
    (hUp : upSL K p 0 (1 : Module.End K (Lq K p)) ∈ T')
    (hLo : loSL K p 0 (1 : Module.End K (Lq K p)) ∈ T')
    (a b : (Fin 2 ⊕ Fin 2) ⊕ Fin 0) (hab : a ≠ b) (t : K) : elemSL K p 0 a b hab t ∈ T' := by
  rcases a with (α | α) | c
  · rcases b with (β | β) | c'
    · have hαβ : α ≠ β := fun h => hab (by rw [h])
      have h0 : (t • eL K p α β) * (t • eL K p α β) = 0 := by
        rw [smul_mul_assoc, mul_smul_comm, eL_mul_eL_self hαβ, smul_zero, smul_zero]
      have hdet : LinearMap.det ((oneAddU (t • eL K p α β) h0 : (Module.End K (Lq K p))ˣ) :
          Module.End K (Lq K p)) = 1 := det_one_add_of_sq_zero K p _ h0
      have : elemSL K p 0 (Sum.inl (Sum.inl α)) (Sum.inl (Sum.inl β)) hab t =
          dlSL K p 0 (oneAddU (t • eL K p α β) h0) hdet := by
        apply Subtype.ext
        apply Units.ext
        refine LinearMap.ext fun ⟨⟨x, y⟩, z⟩ => ?_
        simp [elemSL, oneAddSL, oneAddU, dlSL, NB, Bs_repr_ll, Bs_ll, eL, Dl_apply]
        try exact Subsingleton.elim _ _
      rw [this]
      exact hDl _ _
    · have : elemSL K p 0 (Sum.inl (Sum.inl α)) (Sum.inl (Sum.inr β)) hab t =
          upSL K p 0 (t • eL K p α β) := by
        apply Subtype.ext
        apply Units.ext
        refine LinearMap.ext fun ⟨⟨x, y⟩, z⟩ => ?_
        simp [elemSL, oneAddSL, oneAddU, upSL, NB, Bs_repr_lr, Bs_ll, eL, upN_apply]
      rw [this]
      exact up_all K p 0 T' hDl hUp _
    · exact c'.elim0
  · rcases b with (β | β) | c'
    · have : elemSL K p 0 (Sum.inl (Sum.inr α)) (Sum.inl (Sum.inl β)) hab t =
          loSL K p 0 (t • eL K p α β) := by
        apply Subtype.ext
        apply Units.ext
        refine LinearMap.ext fun ⟨⟨x, y⟩, z⟩ => ?_
        simp [elemSL, oneAddSL, oneAddU, loSL, NB, Bs_repr_ll, Bs_lr, eL, loN_apply]
      rw [this]
      exact lo_all K p 0 T' hDr hLo _
    · have hαβ : α ≠ β := fun h => hab (by rw [h])
      have h0 : (t • eL K p α β) * (t • eL K p α β) = 0 := by
        rw [smul_mul_assoc, mul_smul_comm, eL_mul_eL_self hαβ, smul_zero, smul_zero]
      have hdet : LinearMap.det ((oneAddU (t • eL K p α β) h0 : (Module.End K (Lq K p))ˣ) :
          Module.End K (Lq K p)) = 1 := det_one_add_of_sq_zero K p _ h0
      have : elemSL K p 0 (Sum.inl (Sum.inr α)) (Sum.inl (Sum.inr β)) hab t =
          drSL K p 0 (oneAddU (t • eL K p α β) h0) hdet := by
        apply Subtype.ext
        apply Units.ext
        refine LinearMap.ext fun ⟨⟨x, y⟩, z⟩ => ?_
        simp [elemSL, oneAddSL, oneAddU, drSL, NB, Bs_repr_lr, Bs_lr, eL, Dr_apply]
        try exact Subsingleton.elim _ _
      rw [this]
      exact hDr _ _
    · exact c'.elim0
  · exact c.elim0

theorem torHom_val (u w : (Lq K p)ˣ) :
    ((torHom K p s (u, w) : (Module.End K (Em K p s))ˣ) : Module.End K (Em K p s)) =
      torEnd K p s u w := rfl

theorem torEnd_comm_Dl (w : Lq K p) (P : Module.End K (Lq K p)) :
    torEnd K p s 1 w * Dl K p s P = Dl K p s P * torEnd K p s 1 w := by
  refine LinearMap.ext fun ⟨⟨x, y⟩, z⟩ => ?_
  simp [torEnd_apply, Dl_apply]

theorem torEnd_comm_Dr (u : Lq K p) (Q : Module.End K (Lq K p)) :
    torEnd K p s u 1 * Dr K p s Q = Dr K p s Q * torEnd K p s u 1 := by
  refine LinearMap.ext fun ⟨⟨x, y⟩, z⟩ => ?_
  simp [torEnd_apply, Dr_apply]

theorem torEnd_comm_up (u : Lq K p) :
    torEnd K p s u u * (1 + upN K p s (1 : Module.End K (Lq K p))) =
      (1 + upN K p s (1 : Module.End K (Lq K p))) * torEnd K p s u u := by
  refine LinearMap.ext fun ⟨⟨x, y⟩, z⟩ => ?_
  simp [torEnd_apply, upN_apply, mul_add]

theorem torEnd_comm_lo (u : Lq K p) :
    torEnd K p s u u * (1 + loN K p s (1 : Module.End K (Lq K p))) =
      (1 + loN K p s (1 : Module.End K (Lq K p))) * torEnd K p s u u := by
  refine LinearMap.ext fun ⟨⟨x, y⟩, z⟩ => ?_
  simp [torEnd_apply, loN_apply, mul_add]

theorem gen4 (g xa xb x1 : GL (Fin (4 + 0)) K) (ζ : (Lq K p)ˣ)
    (ha : Φ K p 0 (g⁻¹ * xa * g) = torHom K p 0 (ζ, 1))
    (hb : Φ K p 0 (g⁻¹ * xb * g) = torHom K p 0 (1, ζ))
    (h1 : Φ K p 0 (g⁻¹ * x1 * g) = torHom K p 0 (ζ, ζ))
    (T : Subgroup (projectiveSL (4 + 0) K))
    (hTa : fixSub (conjAut (4 + 0) K xa) ≤ T) (hTb : fixSub (conjAut (4 + 0) K xb) ≤ T)
    (hT1 : fixSub (conjAut (4 + 0) K x1) ≤ T) : T = ⊤ := by
  apply CFSG.GH74.GLS.Stage2.Bender.Thm1.Ln.eq_top_of_rootElt_mem g T
  intro i j hij t
  obtain ⟨a, rfl⟩ := (eSum 0).surjective i
  obtain ⟨b, rfl⟩ := (eSum 0).surjective j
  have hab : a ≠ b := fun h => hij (by rw [h])
  have hDl : ∀ (P : (Module.End K (Lq K p))ˣ) (hP : LinearMap.det (P : Module.End K (Lq K p)) = 1),
      dlSL K p 0 P hP ∈ T.comap (rho K p 0 g) := fun P hP => by
    apply hTb
    apply rho_mem_fixSub K p 0 g xb
    rw [hb, torHom_val, Units.val_one]
    exact torEnd_comm_Dl K p 0 _ _
  have hDr : ∀ (Q : (Module.End K (Lq K p))ˣ) (hQ : LinearMap.det (Q : Module.End K (Lq K p)) = 1),
      drSL K p 0 Q hQ ∈ T.comap (rho K p 0 g) := fun Q hQ => by
    apply hTa
    apply rho_mem_fixSub K p 0 g xa
    rw [ha, torHom_val, Units.val_one]
    exact torEnd_comm_Dr K p 0 _ _
  have hUp : upSL K p 0 (1 : Module.End K (Lq K p)) ∈ T.comap (rho K p 0 g) := by
    apply hT1
    apply rho_mem_fixSub K p 0 g x1
    rw [h1, torHom_val]
    exact torEnd_comm_up K p 0 _
  have hLo : loSL K p 0 (1 : Module.End K (Lq K p)) ∈ T.comap (rho K p 0 g) := by
    apply hT1
    apply rho_mem_fixSub K p 0 g x1
    rw [h1, torHom_val]
    exact torEnd_comm_lo K p 0 _
  rw [rootElt_eq_rho K p 0 g a b hab t]
  exact elem_mem_zero K p (T.comap (rho K p 0 g)) hDl hDr hUp hLo a b hab t

end Gen4

end CFSG.GH74.GLS.Stage2.Bender.Thm1.Ln.E2
