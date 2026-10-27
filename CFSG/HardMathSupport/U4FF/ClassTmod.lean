module

public import CFSG.HardMathSupport.U4FF.ClassLocUse

public section

namespace CFSG.HardMathSupport.U4FF

open Matrix
open scoped MatrixGroups
open CFSG.LieType.Universal.Unitary (SU)
open CFSG.LieType.BorelTits (unitaryInvolution)


abbrev TIdx {n : ℕ} (l : Lbl n) : Type := (i : Fin n) → Fin (locM (l.a i) (l.b i) (l.c i))

@[expose] def rhoL (n : ℕ) : Lbl n := ⟨fun _ => true, fun _ => true, fun _ => true⟩

@[expose] noncomputable def frobTw (K : Type) [Field K] [CharP K 2] (k : Type*) [Field k]
    [Algebra K k] (i : ℕ) : K →+* k :=
  (algebraMap K k).comp (iterateFrobenius K 2 i)

theorem frobTw_apply (K : Type) [Field K] [CharP K 2] (k : Type*) [Field k] [Algebra K k] (i : ℕ)
    (x : K) : frobTw K k i x = algebraMap K k (x ^ 2 ^ i) := by
  simp [frobTw, iterateFrobenius_def]

section Tmod

variable {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ} {k : Type*} [Field k] [CharP k 2]

@[expose] noncomputable def TmodΦ (l : Lbl n) (φ : Fin n → K →+* k) :
    SU4 K n →* Matrix (TIdx l) (TIdx l) k where
  toFun g := kronDep (fun i : Fin n => Fin (locM (l.a i) (l.b i) (l.c i)))
    (fun i => locR (l.a i) (l.b i) (l.c i) k (twistHom n (φ i) g))
  map_one' := by
    simp only [map_one]
    exact kronDep_one
  map_mul' g h := by
    simp only [map_mul]
    exact kronDep_mul _ _

@[expose] noncomputable def hwv (l : Lbl n) (k : Type*) [Field k] [CharP k 2] : TIdx l → k :=
  pureTensor (fun i : Fin n => Fin (locM (l.a i) (l.b i) (l.c i)))
    (fun i => ylocC (l.a i) (l.b i) (l.c i) k)

theorem TmodΦ_apply (l : Lbl n) (φ : Fin n → K →+* k) (g : SU4 K n) :
    TmodΦ l φ g = kronDep (fun i : Fin n => Fin (locM (l.a i) (l.b i) (l.c i)))
      (fun i => locR (l.a i) (l.b i) (l.c i) k (twistHom n (φ i) g)) := rfl

theorem hwv_ne_zero (l : Lbl n) : hwv l k ≠ 0 :=
  pureTensor_ne_zero _ fun _ => ylocC_ne_zero

theorem TmodΦ_upper_fix (hK : Nat.card K = (2 ^ n) ^ 2) (l : Lbl n) (φ : Fin n → K →+* k)
    {u : SU4 K n} (hu : u ∈ UpperU K n) : TmodΦ l φ u *ᵥ hwv l k = hwv l k := by
  rw [TmodΦ_apply, hwv, kronDep_mulVec_pure]
  congr 1
  funext i
  exact locR_upT_fix (twistHom_mem_UpT hK (φ i) hu)

theorem TmodΦ_diag (l : Lbl n) (φ : Fin n → K →+* k) {h : SU4 K n}
    (hd : ∀ i j, i ≠ j → ((h : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) i j = 0) :
    TmodΦ l φ h *ᵥ hwv l k = (∏ i : Fin n, wtLoc (l.a i) (l.b i) (l.c i)
      (fun j => φ i (((h : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) j j))) • hwv l k := by
  rw [TmodΦ_apply, hwv, kronDep_mulVec_pure]
  have : ∀ i : Fin n, locR (l.a i) (l.b i) (l.c i) k (twistHom n (φ i) h) *ᵥ
      ylocC (l.a i) (l.b i) (l.c i) k = wtLoc (l.a i) (l.b i) (l.c i)
        (fun j => φ i (((h : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) j j)) •
          ylocC (l.a i) (l.b i) (l.c i) k := fun i =>
    locR_diag _ _ (twistHom_diag (φ i) hd)
  simp only [this]
  exact pureTensor_smul_prod _ _

@[expose] noncomputable def PiTot (l : Lbl n) (k : Type*) [Field k] [CharP k 2] :
    Matrix (TIdx l) (TIdx (rhoL n)) k :=
  kronRect (fun i : Fin n => Fin (locM (l.a i) (l.b i) (l.c i)))
    (fun _ : Fin n => Fin (locM true true true)) (fun i => picK (l.a i) (l.b i) (l.c i) k)

@[expose] noncomputable def PirTot (l : Lbl n) (k : Type*) [Field k] [CharP k 2] :
    Matrix (TIdx (rhoL n)) (TIdx l) k :=
  kronRect (fun _ : Fin n => Fin (locM true true true))
    (fun i : Fin n => Fin (locM (l.a i) (l.b i) (l.c i))) (fun i => pirK (l.a i) (l.b i) (l.c i) k)

@[expose] noncomputable def IotaTot (l : Lbl n) (k : Type*) [Field k] [CharP k 2] :
    Matrix (TIdx (rhoL n)) (TIdx l) k :=
  kronRect (fun _ : Fin n => Fin (locM true true true))
    (fun i : Fin n => Fin (locM (l.a i) (l.b i) (l.c i))) (fun i => iocK (l.a i) (l.b i) (l.c i) k)

@[expose] noncomputable def IolTot (l : Lbl n) (k : Type*) [Field k] [CharP k 2] :
    Matrix (TIdx l) (TIdx (rhoL n)) k :=
  kronRect (fun i : Fin n => Fin (locM (l.a i) (l.b i) (l.c i)))
    (fun _ : Fin n => Fin (locM true true true)) (fun i => iolK (l.a i) (l.b i) (l.c i) k)

theorem PiTot_mul_PirTot (l : Lbl n) : PiTot l k * PirTot l k = 1 :=
  kronRect_mul_eq_one _ _ fun _ => picK_mul_pirK

theorem IolTot_mul_IotaTot (l : Lbl n) : IolTot l k * IotaTot l k = 1 :=
  kronRect_mul_eq_one _ _ fun _ => iolK_mul_iocK

theorem PiTot_hwv (l : Lbl n) : PiTot l k *ᵥ hwv (rhoL n) k = hwv l k := by
  have h := kronRect_mulVec_pure (κ := fun i : Fin n => Fin (locM (l.a i) (l.b i) (l.c i)))
    (μ := fun _ : Fin n => Fin (locM true true true))
    (fun i => picK (l.a i) (l.b i) (l.c i) k) (fun _ => ylocC true true true k)
  have h2 : (fun i : Fin n => picK (l.a i) (l.b i) (l.c i) k *ᵥ ylocC true true true k) =
      fun i => ylocC (l.a i) (l.b i) (l.c i) k := funext fun i => picK_ylocC
  rw [h2] at h
  exact h

theorem PiTot_equiv (hK : Nat.card K = (2 ^ n) ^ 2) (l : Lbl n) (φ : Fin n → K →+* k)
    {u : SU4 K n} (hu : u ∈ LowerU K n) :
    PiTot l k * TmodΦ (rhoL n) φ u = TmodΦ l φ u * PiTot l k := by
  rw [TmodΦ_apply, TmodΦ_apply]
  exact kronRect_equivariant _ _ _ fun i => picK_equiv (twistHom_mem_LowT hK (φ i) hu)

theorem IotaTot_equiv (hK : Nat.card K = (2 ^ n) ^ 2) (l : Lbl n) (φ : Fin n → K →+* k)
    {u : SU4 K n} (hu : u ∈ LowerU K n) :
    IotaTot l k * TmodΦ l φ u = TmodΦ (rhoL n) φ u * IotaTot l k := by
  rw [TmodΦ_apply, TmodΦ_apply]
  exact kronRect_equivariant _ _ _ fun i => iocK_equiv (twistHom_mem_LowT hK (φ i) hu)

end Tmod

end CFSG.HardMathSupport.U4FF
