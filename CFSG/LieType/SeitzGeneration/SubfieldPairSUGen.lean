module

public import CFSG.LieType.SeitzGeneration.SubfieldPairSUFrame
public import CFSG.ClassicalGroups.Unitary.Generation

public section

namespace CFSG.LieType.SeitzGeneration.SUPair

open Matrix CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary

variable {K : Type*} [Field K] {σ : K ≃+* K} {n : ℕ}

variable (σ) in
@[expose] def ratTv (k : Subfield K) (n : ℕ) : Set (SUid σ n) :=
  {t | ∃ (a : Fin n → K) (c : K), IsRat k a ∧ herm σ a a = 0 ∧ c ∈ k ∧ c + σ c = 0 ∧
    ∀ v, t • v = v + (c * herm σ a v) • a}

@[expose] def subGL (k : Subfield K) (n : ℕ) : GL (Fin n) k →* GL (Fin n) K :=
  Units.map (RingHom.mapMatrix k.subtype).toMonoidHom

theorem coe_subGL (k : Subfield K) (g : GL (Fin n) k) :
    ((subGL k n g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      (g : Matrix (Fin n) (Fin n) k).map k.subtype :=
  rfl

section Subfield

variable {k : Subfield K} (σk : k ≃+* k) (hσk : ∀ x : k, ((σk x : k) : K) = σ (x : K))

include hσk in
theorem map_conjTr (M : Matrix (Fin n) (Fin n) k) :
    (conjTr σk M).map k.subtype = conjTr σ (M.map k.subtype) := by
  ext i j
  simp [conjTr, hσk]

include hσk in
theorem subGL_mem_SUid {g : GL (Fin n) k} (hg : g ∈ SUid σk n) : subGL k n g ∈ SUid σ n := by
  obtain ⟨h1, h2⟩ := hg
  refine ⟨?_, ?_⟩
  · rw [coe_subGL]
    change (k.subtype.mapMatrix (g : Matrix (Fin n) (Fin n) k)).det = 1
    rw [← RingHom.map_det, h1, map_one]
  · rw [coe_subGL, ← map_conjTr σk hσk, ← Matrix.map_mul, h2]
    simp

variable (n) in
@[expose] def subSU : SUid σk n →* SUid σ n :=
  ((subGL k n).comp (SUid σk n).subtype).codRestrict _ fun g => subGL_mem_SUid σk hσk g.2

theorem coe_subSU (g : SUid σk n) :
    (((subSU n σk hσk g : SUid σ n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      ((g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k).map k.subtype :=
  rfl

end Subfield

section Range

variable {k : Subfield K} (σk : k ≃+* k) (hσk : ∀ x : k, ((σk x : k) : K) = σ (x : K))
  (hk : ∀ x ∈ k, σ x ∈ k)

include hσk hk in
theorem exists_subSU_eq {g : SUid σ n} (hg : g ∈ ratSU σ k hk n) :
    ∃ x : SUid σk n, subSU n σk hσk x = g := by
  let M : Matrix (Fin n) (Fin n) k := fun i j =>
    ⟨((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) i j, hg i j⟩
  have hMg : M.map k.subtype = ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := rfl
  have hdet : M.det = 1 := by
    apply k.subtype.injective
    rw [map_one, RingHom.map_det]
    change (M.map k.subtype).det = 1
    rw [hMg]
    exact g.2.1
  have hcon : conjTr σk M * M = 1 := by
    refine Matrix.map_injective (f := k.subtype) k.subtype.injective ?_
    show (conjTr σk M * M).map k.subtype = (1 : Matrix (Fin n) (Fin n) k).map k.subtype
    rw [Matrix.map_mul, map_conjTr σk hσk, hMg, g.2.2]
    simp
  have hiso : ∀ x y, herm σk (M *ᵥ x) (M *ᵥ y) = herm σk x y := by
    intro x y
    rw [herm_mulVec, hcon, one_mulVec]
  refine ⟨mkSU σk M hdet hiso, ?_⟩
  apply Subtype.ext
  apply Units.ext
  exact hMg

end Range

section Generation

variable {k : Subfield K} (σk : k ≃+* k) (hσk : ∀ x : k, ((σk x : k) : K) = σ (x : K))

include hσk in
theorem herm_subtype (a b : Fin n → k) :
    herm σ (fun i => (a i : K)) (fun i => (b i : K)) = ((herm σk a b : k) : K) := by
  show _ = k.subtype (herm σk a b)
  simp only [herm, map_sum, map_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [hσk]

include hσk in
theorem map_tvMat (a : Fin n → k) (c : k) :
    (tvMat σk a c).map k.subtype = tvMat σ (fun i => (a i : K)) (c : K) := by
  ext i j
  simp [tvMat, vecMulVec_apply, hσk, Matrix.one_apply]
  split_ifs <;> simp

include hσk in
theorem subSU_mem_ratTv {x : SUid σk n} (hx : x ∈ tvSet σk n) :
    subSU n σk hσk x ∈ ratTv σ k n := by
  obtain ⟨a, c, ha, hc, hact⟩ := hx
  have hxM : ((x : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) = tvMat σk a c := by
    refine Matrix.ext_of_mulVec_single fun i => ?_
    rw [tvMat_mulVec]
    exact hact _
  have hM : (((subSU n σk hσk x : SUid σ n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      tvMat σ (fun i => (a i : K)) (c : K) := by
    rw [coe_subSU, hxM, map_tvMat σk hσk]
  refine ⟨fun i => (a i : K), (c : K), fun i => (a i).2, ?_, c.2, ?_, fun v => ?_⟩
  · rw [herm_subtype σk hσk, ha, Subfield.coe_zero]
  · have := congrArg (fun z : k => (z : K)) hc
    simpa [hσk] using this
  · rw [smul_def, hM, tvMat_mulVec]

variable (hk : ∀ x ∈ k, σ x ∈ k)

include hσk hk in
theorem ratSU_le_closure_ratTv (hU : IsUnitaryInvolution σk) (hn : 2 ≤ n)
    (h3 : n = 3 → ∃ s : k, s ≠ 0 ∧ σk s * s ≠ 1) :
    ratSU σ k hk n ≤ Subgroup.closure (ratTv σ k n) := by
  intro g hg
  obtain ⟨x, rfl⟩ := exists_subSU_eq σk hσk hk hg
  clear hg
  have hx : x ∈ Subgroup.closure (tvSet σk n) := by
    have := T_eq_top hU hn h3
    have hxT : x ∈ T σk n := by rw [this]; trivial
    exact hxT
  induction hx using Subgroup.closure_induction with
  | mem y hy => exact Subgroup.subset_closure (subSU_mem_ratTv σk hσk hy)
  | one => rw [map_one]; exact Subgroup.one_mem _
  | mul a b _ _ ha hb => rw [map_mul]; exact Subgroup.mul_mem _ ha hb
  | inv a _ ha => rw [map_inv]; exact Subgroup.inv_mem _ ha

end Generation

end CFSG.LieType.SeitzGeneration.SUPair
