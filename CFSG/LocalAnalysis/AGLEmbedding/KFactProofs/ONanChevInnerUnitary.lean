module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanChevInnerPacked
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanChevInnerProj
import all CFSG.Fischer.F4

public section

namespace CFSG.AGLEmbedding

open CFSG.Fischer CFSG.LieType.BorelTits CFSG.LieType.Universal.Unitary
  CFSG.ClassicalGroups.Unitary CFSG.ClassicalGroups.UnitaryFlag
  CFSG.LocalAnalysis.ComponentInitial Matrix

instance decidableEntryZero {n : ℕ} (X : Matrix (Fin n) (Fin n) F4) (a b : Fin n) :
    Decidable (X a b = 0) :=
  inferInstanceAs (Decidable ((X a b : F4) = 0))

@[expose] def omg : F4 := ⟨2⟩

@[expose] def omg2 : F4 := ⟨3⟩

@[expose] def ωpow (k : ZMod 3) : F4 := omg ^ k.val

@[expose] def ex {n : ℕ} (v : Fin 4 → ZMod 3) (i : Fin n) : ZMod 3 :=
  if h : i.val < 4 then v ⟨i.val, h⟩ else if i.val = 4 then 2 * (v 0 + v 1 + v 2 + v 3) else 0

@[expose] def Dm {n : ℕ} (v : Fin 4 → ZMod 3) : Matrix (Fin n) (Fin n) F4 :=
  Matrix.diagonal fun i => ωpow (ex v i)

@[expose] def Pm (n i j : ℕ) : Matrix (Fin n) (Fin n) F4 :=
  Matrix.of fun a b => if b.val = i then (if a.val = j then 1 else 0)
    else if b.val = j then (if a.val = i then 1 else 0) else if a = b then 1 else 0

@[expose] def tau (k : Fin 4) (v : Fin 4 → ZMod 3) : Fin 4 → ZMod 3 :=
  if k.val < 3 then v ∘ Equiv.swap k (k + 1) else ![v 0, v 1, v 2, 2 * (v 0 + v 1 + v 2 + v 3)]

@[expose] def tvMatF {n : ℕ} (a : Fin n → F4) : Matrix (Fin n) (Fin n) F4 :=
  1 + Matrix.vecMulVec a (fun i => a i ^ 2)

@[expose] def pairV (n i j : ℕ) : Fin n → F4 := fun a => if a.val = i ∨ a.val = j then 1 else 0

structure UnitaryData (n : ℕ) where
  phi : (Fin 2 → ZMod 3) → (Fin 4 → ZMod 3)
  X : Matrix (Fin n) (Fin n) F4
  steps : List (ℕ × ℕ)

namespace UnitaryData

variable {n : ℕ} (d : UnitaryData n)

@[expose] def mats : List (Matrix (Fin n) (Fin n) F4) :=
  [Dm (Pi.single 0 1), Dm (Pi.single 1 1), Dm (Pi.single 2 1), Dm (Pi.single 3 1), Pm n 0 1,
    Pm n 1 2, Pm n 2 3, Pm n 3 4, d.X]

@[expose] def bfsOk : Bool :=
  match bfsAux (fun g c => applyP n (colsOf (d.mats.getD g 1)) c) d.steps
    (1 <<< codeOf (pairV n 0 1)) with
  | none => false
  | some m => decide (CompleteMaskP n m)

@[expose] def Ok : Prop :=
  (∀ v : Fin 4 → ZMod 3, ∏ i : Fin n, ωpow (ex v i) = 1) ∧
  IsSU d.X ∧
  (∀ i j : Fin 5, i ≠ j →
    Pm n i.val j.val = tvMatF (pairV n i.val j.val) ∧
      hermF (pairV n i.val j.val) (pairV n i.val j.val) = 0) ∧
  (∀ v : Fin 4 → ZMod 3, (∀ i j : Fin n, ωpow (ex v i) = ωpow (ex v j)) → v = 0) ∧
  (∀ i j : Fin 4, i ≠ j → ∀ a b : Fin n, Pm n i.val j.val a b ≠ 0 →
    ωpow (ex (Pi.single i 1) b) = ωpow (ex (Pi.single j 1) a) ∧
      ωpow (ex (Pi.single j 1) b) = ωpow (ex (Pi.single i 1) a)) ∧
  (∀ k : Fin 4, ∀ v : Fin 4 → ZMod 3, ∀ a b : Fin n, Pm n k.val (k.val + 1) a b ≠ 0 →
    ωpow (ex v b) = ωpow (ex (tau k v) a)) ∧
  (∀ k : Fin 4, Pm n k.val (k.val + 1) * Pm n k.val (k.val + 1) = 1) ∧
  (∀ a b : Fin 2 → ZMod 3, d.phi (a + b) = d.phi a + d.phi b) ∧
  (∀ a : Fin 2 → ZMod 3, d.phi a = 0 → a = 0) ∧
  (∀ a : Fin 2 → ZMod 3, ∀ i j : Fin n, d.X i j ≠ 0 →
    ωpow (ex (d.phi a) j) = ωpow (ex (d.phi a) i)) ∧ d.bfsOk = true

set_option synthInstance.maxSize 20000 in
instance : Decidable d.Ok := by
  unfold Ok
  infer_instance

end UnitaryData

section Lemmas

variable {n : ℕ}

theorem ωpow_ne_zero (k : ZMod 3) : ωpow k ≠ 0 := by
  revert k
  decide +kernel

theorem ωpow_add (a b : ZMod 3) : ωpow (a + b) = ωpow a * ωpow b := by
  revert a b
  decide +kernel

theorem ωpow_zero : ωpow 0 = 1 := by decide +kernel

theorem ex_add (v w : Fin 4 → ZMod 3) (i : Fin n) : ex (v + w) i = ex v i + ex w i := by
  unfold ex
  split_ifs with h1 h2
  · rfl
  · simp only [Pi.add_apply]
    ring
  · simp

theorem ex_zero (i : Fin n) : ex (0 : Fin 4 → ZMod 3) i = 0 := by
  unfold ex
  split_ifs <;> simp

theorem Dm_zero : (Dm (0 : Fin 4 → ZMod 3) : Matrix (Fin n) (Fin n) F4) = 1 := by
  unfold Dm
  simp only [ex_zero, ωpow_zero]
  exact Matrix.diagonal_one

theorem Dm_add (v w : Fin 4 → ZMod 3) :
    (Dm (v + w) : Matrix (Fin n) (Fin n) F4) = Dm v * Dm w := by
  unfold Dm
  rw [Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  rw [ex_add, ωpow_add]

theorem isSU_diagonal {d : Fin n → F4} (h0 : ∀ i, d i ≠ 0) (hprod : ∏ i, d i = 1) :
    IsSU (Matrix.diagonal d) := by
  refine ⟨by rw [Matrix.det_diagonal]; exact hprod, ?_⟩
  have : conjTrF (Matrix.diagonal d) = Matrix.diagonal (fun i => d i ^ 2) := by
    ext i j
    simp only [conjTrF, Matrix.of_apply, Matrix.diagonal_apply]
    split_ifs with h1 h2 h2
    · rw [h1]
    · exact absurd h1.symm h2
    · exact absurd h2.symm h1
    · rfl
  rw [this, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext i
  exact norm_one4 _ (h0 i)

theorem Dm_isSU (hprod : ∀ v : Fin 4 → ZMod 3, ∏ i : Fin n, ωpow (ex v i) = 1)
    (v : Fin 4 → ZMod 3) : IsSU (Dm v : Matrix (Fin n) (Fin n) F4) :=
  isSU_diagonal (fun _ => ωpow_ne_zero _) (hprod v)

theorem tvMat_conj4 (a : Fin n → F4) : tvMat conj4 a 1 = tvMatF a := by
  simp only [tvMat, tvMatF, conj4_apply, one_smul]

theorem isSU_tvMatF {a : Fin n → F4} (ha : hermF a a = 0) : IsSU (tvMatF a) := by
  have ha' : herm conj4 a a = 0 := by rw [herm_conj4]; exact ha
  have hc : (1 : F4) + conj4 1 = 0 := by
    rw [map_one]
    decide +kernel
  refine ⟨?_, ?_⟩
  · rw [← tvMat_conj4]
    exact tvMat_det ha' 1
  · have := conjTr_mul_self_of_isometry conj4
      (tvMat_isometry isUnitaryInvolution_conj4.invol ha' hc)
    rwa [tvMat_conj4, conjTr_conj4] at this

theorem tvMatF_mulVec (a v : Fin n → F4) :
    tvMatF a *ᵥ v = v + (1 * herm conj4 a v) • a := by
  rw [← tvMat_conj4]
  exact tvMat_mulVec a 1 v

theorem Pm_mul_diagonal {i j : ℕ} {d d' : Fin n → F4}
    (h : ∀ a b, Pm n i j a b ≠ 0 → d b = d' a) :
    Pm n i j * Matrix.diagonal d = Matrix.diagonal d' * Pm n i j := by
  ext a b
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  by_cases hab : Pm n i j a b = 0
  · rw [hab, zero_mul, mul_zero]
  · rw [h a b hab, mul_comm]

theorem mul_diagonal_comm {X : Matrix (Fin n) (Fin n) F4} {d : Fin n → F4}
    (h : ∀ i j, X i j ≠ 0 → d j = d i) : X * Matrix.diagonal d = Matrix.diagonal d * X := by
  ext a b
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  by_cases hab : X a b = 0
  · rw [hab, zero_mul, mul_zero]
  · rw [h a b hab, mul_comm]

theorem suOf_mul_eq {A B C D : Matrix (Fin n) (Fin n) F4} (hA : IsSU A) (hB : IsSU B)
    (hC : IsSU C) (hD : IsSU D) (h : A * B = C * D) :
    suOf A * suOf B = suOf C * suOf D := by
  apply ext_smul
  intro v
  rw [mul_smul, mul_smul, suOf_smul hA, suOf_smul hB, suOf_smul hC, suOf_smul hD,
    Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, h]

theorem suOf_mul_of_eq {A B C : Matrix (Fin n) (Fin n) F4} (hA : IsSU A) (hB : IsSU B)
    (hC : IsSU C) (h : A * B = C) : suOf A * suOf B = suOf C := by
  have := suOf_mul_eq hA hB hC isSU_one (C := C) (D := 1) (by rw [h, Matrix.mul_one])
  rwa [suOf_one, mul_one] at this

theorem suOf_val {M : Matrix (Fin n) (Fin n) F4} (h : IsSU M) :
    ((suOf M : SUid conj4 n) : GL (Fin n) F4).val = M := by
  classical
  simp only [suOf, h, dite_true]
  rfl

end Lemmas

namespace UnitaryData

section Construction

variable {n : ℕ} {d : UnitaryData n}

theorem Ok.su_dm (h : d.Ok) (v : Fin 4 → ZMod 3) : IsSU (Dm v : Matrix (Fin n) (Fin n) F4) :=
  Dm_isSU h.1 v

theorem Ok.su_X (h : d.Ok) : IsSU d.X := h.2.1

theorem Ok.pm_eq (h : d.Ok) {i j : ℕ} (hi : i < 5) (hj : j < 5) (hij : i ≠ j) :
    Pm n i j = tvMatF (pairV n i j) ∧ hermF (pairV n i j) (pairV n i j) = 0 :=
  h.2.2.1 ⟨i, hi⟩ ⟨j, hj⟩ (fun h' => hij (congrArg Fin.val h'))

theorem Ok.su_pm (h : d.Ok) {i j : ℕ} (hi : i < 5) (hj : j < 5) (hij : i ≠ j) :
    IsSU (Pm n i j) := by
  obtain ⟨h1, h2⟩ := h.pm_eq hi hj hij
  rw [h1]
  exact isSU_tvMatF h2

@[expose] noncomputable def theta (h : d.Ok) : Multiplicative (Fin 4 → ZMod 3) →* SUid conj4 n where
  toFun a := suOf (Dm (Multiplicative.toAdd a))
  map_one' := by
    show suOf (Dm (0 : Fin 4 → ZMod 3)) = 1
    rw [Dm_zero, suOf_one]
  map_mul' a b := by
    show suOf (Dm (Multiplicative.toAdd a + Multiplicative.toAdd b)) =
      suOf (Dm (Multiplicative.toAdd a)) * suOf (Dm (Multiplicative.toAdd b))
    rw [Dm_add]
    exact (suOf_mul_of_eq (h.su_dm _) (h.su_dm _) (by rw [← Dm_add]; exact h.su_dm _) rfl).symm

theorem theta_apply (h : d.Ok) (v : Fin 4 → ZMod 3) :
    theta h (Multiplicative.ofAdd v) = suOf (Dm v) := rfl

@[expose] noncomputable def phiHom (h : d.Ok) :
    Multiplicative (Fin 2 → ZMod 3) →* Multiplicative (Fin 4 → ZMod 3) where
  toFun a := Multiplicative.ofAdd (d.phi (Multiplicative.toAdd a))
  map_one' := by
    have h0 : d.phi 0 = 0 := by
      have := h.2.2.2.2.2.2.2.1 0 0
      simpa using this
    show Multiplicative.ofAdd (d.phi 0) = 1
    rw [h0]
    rfl
  map_mul' a b := by
    show Multiplicative.ofAdd (d.phi (Multiplicative.toAdd a + Multiplicative.toAdd b)) =
      Multiplicative.ofAdd (d.phi (Multiplicative.toAdd a)) *
        Multiplicative.ofAdd (d.phi (Multiplicative.toAdd b))
    rw [h.2.2.2.2.2.2.2.1]
    rfl

theorem phiHom_injective (h : d.Ok) : Function.Injective (phiHom h) := by
  rw [injective_iff_map_eq_one]
  intro a ha
  have h1 : d.phi (Multiplicative.toAdd a) = 0 := by
    have := congrArg Multiplicative.toAdd ha
    exact this
  have := h.2.2.2.2.2.2.2.2.1 _ h1
  apply Multiplicative.toAdd.injective
  exact this

theorem theta_phi (h : d.Ok) (a : Multiplicative (Fin 2 → ZMod 3)) :
    ((theta h).comp (phiHom h)) a = suOf (Dm (d.phi (Multiplicative.toAdd a))) := rfl

theorem swap_conj₁ (h : d.Ok) {i j : Fin 4} (hij : i ≠ j) :
    suOf (Pm n i.val j.val) * theta h (Multiplicative.ofAdd (Pi.single i 1)) *
      (suOf (Pm n i.val j.val))⁻¹ = theta h (Multiplicative.ofAdd (Pi.single j 1)) := by
  rw [mul_inv_eq_iff_eq_mul]
  have hne : i.val ≠ j.val := fun h' => hij (Fin.ext h')
  have hP := h.su_pm (n := n) (i := i.val) (j := j.val) (by omega) (by omega) hne
  have hmat : Pm n i.val j.val * Dm (Pi.single i 1) = Dm (Pi.single j 1) * Pm n i.val j.val :=
    Pm_mul_diagonal fun a b hab => (h.2.2.2.2.1 i j hij a b hab).1
  exact suOf_mul_eq hP (h.su_dm _) (h.su_dm _) hP hmat

theorem swap_conj₂ (h : d.Ok) {i j : Fin 4} (hij : i ≠ j) :
    suOf (Pm n i.val j.val) * theta h (Multiplicative.ofAdd (Pi.single j 1)) *
      (suOf (Pm n i.val j.val))⁻¹ = theta h (Multiplicative.ofAdd (Pi.single i 1)) := by
  rw [mul_inv_eq_iff_eq_mul]
  have hne : i.val ≠ j.val := fun h' => hij (Fin.ext h')
  have hP := h.su_pm (n := n) (i := i.val) (j := j.val) (by omega) (by omega) hne
  have hmat : Pm n i.val j.val * Dm (Pi.single j 1) = Dm (Pi.single i 1) * Pm n i.val j.val :=
    Pm_mul_diagonal fun a b hab => (h.2.2.2.2.1 i j hij a b hab).2
  exact suOf_mul_eq hP (h.su_dm _) (h.su_dm _) hP hmat

theorem pm_mem_normalizer (h : d.Ok) (k : Fin 4) :
    suOf (Pm n k.val (k.val + 1)) ∈ Subgroup.normalizer ((theta h).range : Set (SUid conj4 n)) := by
  have hP := h.su_pm (n := n) (i := k.val) (j := k.val + 1) (by omega) (by omega) (by omega)
  refine mem_normalizer_of_involution _ ?_ ?_
  · have := suOf_mul_of_eq hP hP isSU_one (h.2.2.2.2.2.2.1 k)
    rwa [suOf_one] at this
  · rintro _ ⟨a, rfl⟩
    refine ⟨Multiplicative.ofAdd (tau k (Multiplicative.toAdd a)), ?_⟩
    symm
    rw [mul_inv_eq_iff_eq_mul]
    exact suOf_mul_eq hP (h.su_dm _) (h.su_dm _) hP
      (Pm_mul_diagonal fun a' b hab => h.2.2.2.2.2.1 k _ a' b hab)

theorem X_mem_normalizer (h : d.Ok) :
    suOf d.X ∈ Subgroup.normalizer
      (((theta h).comp (phiHom h)).range : Set (SUid conj4 n)) := by
  refine mem_normalizer_of_forall_commute _ ?_
  rintro _ ⟨a, rfl⟩
  have hmat : d.X * Dm (d.phi (Multiplicative.toAdd a)) =
      Dm (d.phi (Multiplicative.toAdd a)) * d.X :=
    mul_diagonal_comm fun i j hij => h.2.2.2.2.2.2.2.2.2.1 _ i j hij
  exact suOf_mul_eq h.su_X (h.su_dm _) (h.su_dm _) h.su_X hmat

theorem mats_su (h : d.Ok) : ∀ A ∈ d.mats, IsSU A := by
  intro A hA
  simp only [mats, List.mem_cons, List.mem_nil_iff, or_false] at hA
  rcases hA with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact h.su_dm _
  · exact h.su_dm _
  · exact h.su_dm _
  · exact h.su_dm _
  · exact h.su_pm (by norm_num) (by norm_num) (by norm_num)
  · exact h.su_pm (by norm_num) (by norm_num) (by norm_num)
  · exact h.su_pm (by norm_num) (by norm_num) (by norm_num)
  · exact h.su_pm (by norm_num) (by norm_num) (by norm_num)
  · exact h.su_X

theorem bfs_exists (h : d.bfsOk = true) :
    ∃ mask, bfsAux (fun g c => applyP n (colsOf (d.mats.getD g 1)) c) d.steps
      (1 <<< codeOf (pairV n 0 1)) = some mask ∧ CompleteMaskP n mask := by
  unfold bfsOk at h
  split at h
  · exact absurd h (by simp)
  · rename_i m hm
    exact ⟨m, hm, of_decide_eq_true h⟩

end Construction

end UnitaryData

theorem unitaryFieldData_F4 : UnitaryFieldData 2 1 F4 :=
  ⟨Nat.prime_two, le_rfl, by rw [Nat.card_eq_fintype_card, F4.card]; norm_num⟩

@[expose] noncomputable def projU (n : ℕ) : SUid conj4 n →* unitaryPSU unitaryFieldData_F4 n :=
  (unitaryProj unitaryFieldData_F4 n).comp (Subgroup.inclusion (SUid_eq_statedSU card_F4 n).le)

theorem projU_surjective (n : ℕ) : Function.Surjective (projU n) := by
  intro y
  obtain ⟨x, rfl⟩ := unitaryProj_surjective unitaryFieldData_F4 n y
  exact ⟨⟨(x : GL (Fin n) F4), (SUid_eq_statedSU card_F4 n).ge x.2⟩, rfl⟩

namespace UnitaryData

variable {n : ℕ} {d : UnitaryData n}

theorem projU_theta_injective (h : d.Ok) : Function.Injective ((projU n).comp (theta h)) := by
  rw [injective_iff_map_eq_one]
  intro a ha
  have hmem : Subgroup.inclusion (SUid_eq_statedSU card_F4 n).le (theta h a) ∈
      unitaryScalars unitaryFieldData_F4 n := by
    rw [← ker_unitaryProj unitaryFieldData_F4 n]
    exact ha
  obtain ⟨c, -, -, hc⟩ := mem_unitaryScalars.mp hmem
  have hent : ∀ i : Fin n, ωpow (ex (Multiplicative.toAdd a) i) = (c : F4) := fun i => by
    have h1 := congrArg (fun g : GL (Fin n) F4 => (g : Matrix (Fin n) (Fin n) F4) i i) hc
    simp only [Subgroup.coe_inclusion] at h1
    have h2 : (((theta h a : SUid conj4 n) : GL (Fin n) F4) : Matrix (Fin n) (Fin n) F4) =
        Dm (Multiplicative.toAdd a) := suOf_val (h.su_dm _)
    rw [h2] at h1
    simpa [Dm, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply] using h1
  have hv := h.2.2.2.1 (Multiplicative.toAdd a) fun i j => (hent i).trans (hent j).symm
  apply Multiplicative.toAdd.injective
  exact hv

theorem liftableNormalizerGen_of_ok (hn : 5 ≤ n) (h : d.Ok) :
    LiftableNormalizerGen (unitaryPSU unitaryFieldData_F4 n) := by
  refine liftableNormalizerGen_of_proj_swaps (projU n) (projU_surjective n) (theta h)
    (projU_theta_injective h) (fun i j => suOf (Pm n i.val j.val))
    (fun i j hij => swap_conj₁ h hij) (fun i j hij => swap_conj₂ h hij) (phiHom h)
    (phiHom_injective h) ?_
  set M : Subgroup (SUid conj4 n) := Subgroup.closure {x | ∃ A ∈ d.mats, x = suOf A} with hM
  have hmats : ∀ A ∈ d.mats, IsSU A ∧ suOf A ∈ M := fun A hA =>
    ⟨mats_su h A hA, Subgroup.subset_closure ⟨A, hA, rfl⟩⟩
  have hstart : InM M (pairV n 0 1) := by
    refine ⟨suOf (Pm n 0 1), Subgroup.subset_closure ⟨Pm n 0 1, ?_, rfl⟩, fun v => ?_⟩
    · simp [mats]
    · obtain ⟨h1, -⟩ := h.pm_eq (n := n) (i := 0) (j := 1) (by norm_num) (by norm_num)
        (by norm_num)
      rw [suOf_smul (h.su_pm (by norm_num) (by norm_num) (by norm_num)), h1, tvMatF_mulVec]
  obtain ⟨mask, hmask, hcomplete⟩ := bfs_exists h.2.2.2.2.2.2.2.2.2.2
  have hMtop : M = ⊤ :=
    eq_top_of_bfsP (by omega) (by omega) M d.mats hmats hstart d.steps hmask hcomplete
  have hMle : M ≤ Subgroup.normalizer ((theta h).range : Set (SUid conj4 n)) ⊔
      Subgroup.normalizer (((theta h).comp (phiHom h)).range : Set (SUid conj4 n)) := by
    rw [hM, Subgroup.closure_le]
    rintro _ ⟨A, hA, rfl⟩
    simp only [mats, List.mem_cons, List.mem_nil_iff, or_false] at hA
    have hN₁ : ∀ x ∈ (theta h).range, x ∈ Subgroup.normalizer ((theta h).range : Set _) ⊔
        Subgroup.normalizer (((theta h).comp (phiHom h)).range : Set _) := fun x hx =>
      Subgroup.mem_sup_left (Subgroup.le_normalizer hx)
    have hP : ∀ k : Fin 4, suOf (Pm n k.val (k.val + 1)) ∈
        Subgroup.normalizer ((theta h).range : Set _) ⊔
        Subgroup.normalizer (((theta h).comp (phiHom h)).range : Set _) := fun k =>
      Subgroup.mem_sup_left (pm_mem_normalizer h k)
    rcases hA with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hN₁ _ ⟨Multiplicative.ofAdd (Pi.single 0 1), rfl⟩
    · exact hN₁ _ ⟨Multiplicative.ofAdd (Pi.single 1 1), rfl⟩
    · exact hN₁ _ ⟨Multiplicative.ofAdd (Pi.single 2 1), rfl⟩
    · exact hN₁ _ ⟨Multiplicative.ofAdd (Pi.single 3 1), rfl⟩
    · exact hP 0
    · exact hP 1
    · exact hP 2
    · exact hP 3
    · exact Subgroup.mem_sup_right (X_mem_normalizer h)
  rw [← hMtop]
  exact hMle

end UnitaryData

end CFSG.AGLEmbedding
