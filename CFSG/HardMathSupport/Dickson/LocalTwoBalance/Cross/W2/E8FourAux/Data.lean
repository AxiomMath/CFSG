module

public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.E8FourAux.Expo
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerE8Five

public section

namespace CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Lattice
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.LieType.SeitzGeneration
open scoped Matrix

abbrev V8 : Type := Fin Tag.E8.rank → ℤ

@[expose] def M0 : Matrix (Fin Tag.E8.rank) (Fin Tag.E8.rank) ℤ := toMat Tag.E8.rank e8FourMat

@[expose] def zWord : List (Fin Tag.E8.rank) :=
  [7, 6, 5, 4, 3, 2, 1, 3, 4, 5, 6, 7, 6, 2, 3, 4, 5, 1, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6, 5, 4, 3, 0,
    2, 1, 3, 4, 5, 0, 2, 1, 3, 4, 2, 1, 3, 2, 0]

@[expose] def zMat : List (List ℤ) :=
  [[-2, 0, 1, 0, 0, 0, 0, 1], [-3, 0, 1, 0, 0, 0, 0, 2], [-4, 1, 1, 0, 0, 0, 0, 2],
    [-6, 1, 2, -1, 1, 0, 0, 3], [-5, 1, 2, -1, 0, 1, 0, 2], [-4, 1, 2, -1, 0, 0, 1, 1],
    [-3, 1, 2, -1, 0, 0, 0, 1], [-2, 0, 1, 0, 0, 0, 0, 0]]

@[expose] def Mz : Matrix (Fin Tag.E8.rank) (Fin Tag.E8.rank) ℤ := toMat Tag.E8.rank zMat

@[expose] noncomputable def z0 : WeylGroup Tag.E8 := (coxeterSystem Tag.E8).wordProd zWord

@[expose] def inE (r : ℤ) (e : V8) : Prop := ∀ j, (5 : ℤ) ∣ (∑ i, e i * M0 i j) - r * e j

@[expose] def fixZ (e : V8) : Prop := ∀ j, (5 : ℤ) ∣ (∑ i, e i * Mz i j) - e j

@[expose] def rootsV : List V8 := Tag.E8.artifactRoots.map (toVec Tag.E8.rank)

section Weyl


theorem mem_rootsV_iff {v : V8} : v ∈ rootsV ↔ IsRoot Tag.E8 v := by
  rw [isRoot_iff_exists_mem, rootsV, List.mem_map]
  constructor
  · rintro ⟨l, hl, rfl⟩
    exact ⟨l, hl, rfl⟩
  · rintro ⟨l, hl, rfl⟩
    exact ⟨l, hl, rfl⟩

private theorem wordProd_smul_wordMat (l : List (Fin Tag.E8.rank)) (u : V8) :
    (coxeterSystem Tag.E8).wordProd l • u = wordMat Tag.E8 l *ᵥ u := by
  induction l with
  | nil => rw [CoxeterSystem.wordProd_nil, one_smul, wordMat_nil, Matrix.one_mulVec]
  | cons i l ih =>
    rw [CoxeterSystem.wordProd_cons, mul_smul, ih, simple_smul, wordMat_cons,
      ← Matrix.mulVec_mulVec, reflMat_mulVec]

private theorem wordMat_zWord : wordMat Tag.E8 zWord = Mz :=
  wordMat_eq_toMat Tag.E8 _ (by decide +kernel)

theorem w0_smul (u : V8) : e8PhiFourWeyl • u = M0 *ᵥ u := by
  show (coxeterSystem Tag.E8).wordProd e8FourWord • u = _
  rw [wordProd_smul_wordMat, e8Four_wordMat]
  rfl

theorem z0_smul (u : V8) : z0 • u = Mz *ᵥ u := by
  rw [z0, wordProd_smul_wordMat, wordMat_zWord]

theorem w0_mul_z0 : e8PhiFourWeyl * z0 = z0 * e8PhiFourWeyl := by
  refine FaithfulSMul.eq_of_smul_eq_smul (α := V8) fun v => ?_
  have h : M0 * Mz = Mz * M0 := by
    rw [M0, Mz, ← toMat_lmul, ← toMat_lmul]
    exact congrArg (toMat Tag.E8.rank) (by decide +kernel)
  rw [mul_smul, mul_smul, z0_smul, w0_smul, w0_smul, z0_smul, Matrix.mulVec_mulVec,
    Matrix.mulVec_mulVec, h]

private theorem z0_pow_smul (n : ℕ) (u : V8) : (z0 ^ n) • u = (Mz ^ n) *ᵥ u := by
  induction n generalizing u with
  | zero => rw [pow_zero, one_smul, pow_zero, Matrix.one_mulVec]
  | succ n ih => rw [pow_succ, mul_smul, z0_smul, ih, Matrix.mulVec_mulVec, pow_succ]

theorem z0_pow_five : z0 ^ 5 = 1 := by
  have h : Mz ^ 5 = 1 := by
    rw [Mz, ← toMat_lpow, ← toMat_lid]
    exact congrArg (toMat Tag.E8.rank) (by decide +kernel)
  refine FaithfulSMul.eq_of_smul_eq_smul (α := V8) fun v => ?_
  rw [z0_pow_smul, h, one_smul, Matrix.one_mulVec]

theorem z0_ne_one : z0 ≠ 1 := by
  intro h
  have h1 := z0_smul (Pi.single 0 1)
  rw [h, one_smul, Matrix.mulVec_single_one] at h1
  have h2 := congrFun h1 0
  simp [Mz, toMat, lget, zMat] at h2

end Weyl

structure StarData where
  r : ℤ
  e : V8
  x : V8
  b : Fin 4 → V8
  g : Fin Tag.E8.rank → V8
  m : Fin Tag.E8.rank → Fin Tag.E8.rank → ℤ

structure StarData.Valid (D : StarData) : Prop where
  r_cases : D.r = 2 ∨ D.r = 3
  inE_e : inE D.r D.e
  fixZ_e : fixZ D.e
  e_ne : ∃ i, ¬ (5 : ℤ) ∣ D.e i
  inE_x : inE D.r D.x
  inE_b : ∀ s, inE D.r (D.b s)
  x_reg : ∀ v ∈ rootsV, (5 : ℤ) ∣ dotE D.e v → ¬ (5 : ℤ) ∣ dotE D.x v
  b_ne : ∀ v ∈ rootsV, ∃ s, ¬ (5 : ℤ) ∣ dotE (D.b s) v
  b_inj : ∀ v ∈ rootsV, ∀ v' ∈ rootsV,
    (∀ s, (5 : ℤ) ∣ dotE (D.b s) v - dotE (D.b s) v') → v = v'
  g_mem : ∀ j, D.g j ∈ rootsV ∧ (5 : ℤ) ∣ dotE D.e (D.g j)
  mg : ∀ i k, ∑ j, D.m i j * D.g j k = if i = k then 5 else 0
  adj : D.r = 3 → ∀ v ∈ rootsV, (5 : ℤ) ∣ dotE D.e v → ∃ v' ∈ rootsV, (5 : ℤ) ∣ dotE D.e v' ∧
    v' ≠ v ∧ v' ≠ -v ∧ CFSG.LieType.Steinberg.Adjoint.iform (τ := Tag.E8) v v' ≠ 0
  fix : ∀ e', inE D.r e' → fixZ e' → ∃ k : ℤ, ∀ i, (5 : ℤ) ∣ e' i - k * D.e i
  z_move : ∃ s, ¬ fixZ (D.b s)

@[expose] def starData2 : StarData where
  r := 2
  e := ![2, 3, 1, 3, 3, 3, 3, 1]
  x := ![1, 3, 0, 4, 0, 0, 1, 1]
  b := ![![0, 0, 0, 0, 1, 0, 0, 0], ![1, 0, 2, 0, 0, 1, 0, 0], ![4, 0, 0, 2, 0, 0, 1, 0], ![2, 3, 0, 2, 0, 0, 0, 1]]
  g := ![![-1, -1, -1, -2, -1, 0, 0, 0], ![-1, -1, -2, -3, -2, -1, 0, 0], ![0, -1, 0, -1, -1, -1, -1, 0], ![1, 1, 2, 3, 2, 2, 2, 1], ![0, 1, 1, 1, 1, 0, 0, 0], ![-1, -1, -1, -2, -2, -1, -1, -1], ![-2, -2, -3, -4, -3, -3, -2, -1], ![0, -1, -1, -2, -1, -1, -1, -1]]
  m := ![![-3, 2, 1, -1, -2, -1, -2, 2], ![-2, 3, -1, -4, 2, 1, -3, -2], ![1, 1, 3, 2, 4, 2, -1, 1], ![-2, -2, -1, 1, -3, 1, 2, -2], ![3, -2, -1, 1, 2, -4, 2, 3], ![3, -2, -1, -4, -3, 1, -3, -2], ![-2, 3, -1, 6, 2, 1, 2, 3], ![1, 1, 3, -3, -1, -3, -1, -4]]

@[expose] def starData3 : StarData where
  r := 3
  e := ![4, 2, 3, 1, 1, 1, 1, 1]
  x := ![4, 4, 0, 4, 0, 0, 1, 2]
  b := ![![1, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 3, 0, 0, 1, 0, 0], ![2, 0, 0, 3, 0, 0, 1, 0], ![1, 2, 0, 3, 0, 0, 0, 1]]
  g := ![![-2, -2, -3, -4, -4, -3, -2, -1], ![0, -1, 0, -1, -1, -1, 0, 0], ![0, 0, 0, -1, -1, -1, -1, -1], ![-2, -3, -4, -6, -5, -4, -3, -1], ![-1, -2, -2, -4, -3, -2, -1, -1], ![-1, -2, -2, -3, -3, -2, -2, -1], ![-1, -1, -1, -2, -1, -1, -1, -1], ![0, 1, 1, 1, 1, 1, 1, 1]]
  m := ![![-3, -1, 1, 2, 2, -1, -4, -3], ![1, -3, 3, 1, 1, -3, -2, 1], ![-1, 3, 2, -1, -1, 3, 2, 4], ![3, 1, -1, -2, -2, 1, -1, -2], ![-2, 1, -1, 3, -2, -4, 4, -2], ![-2, -4, -1, -2, 3, 6, -1, 3], ![3, 1, -1, -2, 3, -4, -1, -2], ![-2, 1, -1, 3, -2, 1, -1, 3]]

private theorem b_inj_of_nodup (b : Fin 4 → V8)
    (h : (rootsV.map fun v => dotE (b 0) v % 5 + 5 * (dotE (b 1) v % 5) +
      25 * (dotE (b 2) v % 5) + 125 * (dotE (b 3) v % 5)).Nodup) :
    ∀ v ∈ rootsV, ∀ v' ∈ rootsV, (∀ s, (5 : ℤ) ∣ dotE (b s) v - dotE (b s) v') → v = v' := by
  intro v hv v' hv' hd
  refine List.inj_on_of_nodup_map h hv hv' ?_
  have h0 := hd 0
  have h1 := hd 1
  have h2 := hd 2
  have h3 := hd 3
  omega

private theorem dvd_vecMul_of_cert {A₁ A₂ L₁ L₂ N : Matrix (Fin Tag.E8.rank) (Fin Tag.E8.rank) ℤ}
    (hN : ∀ i k, (5 : ℤ) ∣ (A₁ * L₁ + A₂ * L₂ - N) i k) {f : V8}
    (h₁ : ∀ j, (5 : ℤ) ∣ (f ᵥ* A₁) j) (h₂ : ∀ j, (5 : ℤ) ∣ (f ᵥ* A₂) j) :
    ∀ k, (5 : ℤ) ∣ (f ᵥ* N) k := by
  have hdv : ∀ (v : V8) (L : Matrix (Fin Tag.E8.rank) (Fin Tag.E8.rank) ℤ),
      (∀ j, (5 : ℤ) ∣ v j) → ∀ k, (5 : ℤ) ∣ (v ᵥ* L) k := fun v L hv k => by
    simp only [Matrix.vecMul, dotProduct]
    exact Finset.dvd_sum fun j _ => (hv j).mul_right _
  have hdv' : ∀ (v : V8) (L : Matrix (Fin Tag.E8.rank) (Fin Tag.E8.rank) ℤ),
      (∀ i k, (5 : ℤ) ∣ L i k) → ∀ k, (5 : ℤ) ∣ (v ᵥ* L) k := fun v L hL k => by
    simp only [Matrix.vecMul, dotProduct]
    exact Finset.dvd_sum fun j _ => (hL j k).mul_left _
  intro k
  have h : f ᵥ* N = (f ᵥ* A₁) ᵥ* L₁ + (f ᵥ* A₂) ᵥ* L₂ - f ᵥ* (A₁ * L₁ + A₂ * L₂ - N) := by
    rw [Matrix.vecMul_vecMul, Matrix.vecMul_vecMul, ← Matrix.vecMul_add,
      ← Matrix.vecMul_sub, sub_sub_cancel]
  rw [h, Pi.sub_apply, Pi.add_apply]
  exact dvd_sub (dvd_add (hdv _ _ h₁ k) (hdv _ _ h₂ k)) (hdv' _ _ hN k)

private def certN (c : V8) : Matrix (Fin Tag.E8.rank) (Fin Tag.E8.rank) ℤ :=
  1 - Matrix.vecMulVec (Pi.single 7 1 : V8) c

private theorem fix_of_cert {r : ℤ} {c : V8}
    {L₁ L₂ : Matrix (Fin Tag.E8.rank) (Fin Tag.E8.rank) ℤ}
    (hcert : ((M0 - Matrix.diagonal fun _ => r) * L₁ + (Mz - 1) * L₂ - certN c :
        Matrix (Fin Tag.E8.rank) (Fin Tag.E8.rank) ℤ).map (· % 5) = 0) :
    ∀ e', inE r e' → fixZ e' → ∃ k : ℤ, ∀ i, (5 : ℤ) ∣ e' i - k * c i := by
  intro e' h₁ h₂
  refine ⟨e' 7, fun i => ?_⟩
  have key := dvd_vecMul_of_cert
    (fun i k => Int.dvd_of_emod_eq_zero (congrFun (congrFun hcert i) k)) (f := e')
    (fun j => ?_) (fun j => ?_) i
  · rw [certN, Matrix.vecMul_sub, Matrix.vecMul_one, Matrix.vecMul_vecMulVec] at key
    simpa [dotProduct, Pi.single_apply, mul_comm] using key
  · have e1 : (e' ᵥ* (M0 - Matrix.diagonal fun _ => r)) j = (∑ i, e' i * M0 i j) - r * e' j := by
      rw [Matrix.vecMul_sub, Pi.sub_apply, Matrix.vecMul_diagonal, mul_comm]
      rfl
    rw [e1]
    exact h₁ j
  · have e1 : (e' ᵥ* (Mz - 1)) j = (∑ i, e' i * Mz i j) - e' j := by
      rw [Matrix.vecMul_sub, Pi.sub_apply, Matrix.vecMul_one]
      rfl
    rw [e1]
    exact h₂ j

private theorem starData2_fix : ∀ e', inE starData2.r e' → fixZ e' →
    ∃ k : ℤ, ∀ i, (5 : ℤ) ∣ e' i - k * starData2.e i :=
  fix_of_cert (r := 2) (c := starData2.e)
    (L₁ := toMat Tag.E8.rank
      [[0, 0, 0, 2, 2, 0, 1, 0], [1, 2, 1, 1, 4, 3, 3, 0], [4, 0, 2, 3, 1, 0, 4, 0],
       [3, 0, 4, 4, 4, 2, 1, 0]])
    (L₂ := toMat Tag.E8.rank
      [[4, 0, 2, 4, 1, 1, 2, 0], [4, 0, 3, 0, 4, 4, 0, 0], [3, 0, 1, 0, 1, 3, 0, 0]])
    (by unfold M0 Mz certN starData2 e8FourMat zMat; decide +kernel)

private theorem starData3_fix : ∀ e', inE starData3.r e' → fixZ e' →
    ∃ k : ℤ, ∀ i, (5 : ℤ) ∣ e' i - k * starData3.e i :=
  fix_of_cert (r := 3) (c := starData3.e)
    (L₁ := toMat Tag.E8.rank
      [[3, 0, 4, 1, 3, 3, 4, 0], [2, 3, 3, 0, 1, 1, 3, 0], [1, 0, 3, 4, 1, 0, 2, 0],
       [0, 0, 0, 0, 0, 0, 0, 0], [3, 0, 4, 4, 1, 3, 3, 0]])
    (L₂ := toMat Tag.E8.rank
      [[1, 0, 3, 0, 1, 1, 0, 0], [1, 0, 4, 2, 3, 3, 4, 0], [1, 0, 0, 1, 2, 0, 2, 0]])
    (by unfold M0 Mz certN starData3 e8FourMat zMat; decide +kernel)

theorem starData2_valid : starData2.Valid where
  r_cases := Or.inl rfl
  inE_e := by unfold inE starData2; decide +kernel
  fixZ_e := by unfold fixZ starData2; decide +kernel
  e_ne := ⟨0, by unfold starData2; decide +kernel⟩
  inE_x := by unfold inE starData2; decide +kernel
  inE_b := by unfold inE starData2; decide +kernel
  x_reg := by unfold rootsV dotE starData2; decide +kernel
  b_ne := by unfold rootsV dotE starData2; decide +kernel
  b_inj := b_inj_of_nodup _ (by unfold rootsV dotE starData2; decide +kernel)
  g_mem := by unfold rootsV dotE starData2; decide +kernel
  mg := by unfold starData2; decide +kernel
  adj := fun h => absurd h (by decide)
  fix := starData2_fix
  z_move := by unfold fixZ starData2; decide +kernel

theorem starData3_valid : starData3.Valid where
  r_cases := Or.inr rfl
  inE_e := by unfold inE starData3; decide +kernel
  fixZ_e := by unfold fixZ starData3; decide +kernel
  e_ne := ⟨0, by unfold starData3; decide +kernel⟩
  inE_x := by unfold inE starData3; decide +kernel
  inE_b := by unfold inE starData3; decide +kernel
  x_reg := by unfold rootsV dotE starData3; decide +kernel
  b_ne := by unfold rootsV dotE starData3; decide +kernel
  b_inj := b_inj_of_nodup _ (by unfold rootsV dotE starData3; decide +kernel)
  g_mem := by unfold rootsV dotE starData3; decide +kernel
  mg := by unfold starData3; decide +kernel
  adj := fun _ => by
    unfold rootsV dotE starData3 CFSG.LieType.Steinberg.Adjoint.iform
    decide +kernel
  fix := starData3_fix
  z_move := by unfold fixZ starData3; decide +kernel

end CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2
