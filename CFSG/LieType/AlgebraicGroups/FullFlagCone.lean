module

public import CFSG.LinearAlgebra.ExteriorIncidence
public import CFSG.LieType.AlgebraicGroups.ClosedOrbitFixed

public noncomputable section

open scoped TensorProduct

namespace CFSG.LieType.AlgebraicGroups.ClosedCone

universe u w

variable {k V : Type u} [Field k] [AddCommGroup V] [Module k V]

@[expose, reducible] def flagModule (k V : Type u) [Field k] [AddCommGroup V] [Module k V] :
    ℕ → ModuleCat k
  | 0 => ModuleCat.of k k
  | r + 1 => ModuleCat.of k (flagModule k V r ⊗[k] (⋀[k]^(r + 1) V))

abbrev FlagTensor (k V : Type u) [Field k] [AddCommGroup V] [Module k V] (r : ℕ) : Type u :=
  flagModule k V r

instance flagTensorFiniteDimensional [FiniteDimensional k V] :
    (r : ℕ) → FiniteDimensional k (FlagTensor k V r)
  | 0 => inferInstance
  | r + 1 => by
    let := flagTensorFiniteDimensional r
    exact inferInstanceAs (FiniteDimensional k
      (FlagTensor k V r ⊗[k] (⋀[k]^(r + 1) V)))

variable {I : Type w} [Fintype I]

@[expose] def lastIncidence (b : Module.Basis I k V) (r : ℕ) :
    FlagTensor k V (r + 2) →ₗ[k]
      FlagTensor k V r ⊗[k] (ExteriorAlgebra k V ⊗[k] ExteriorAlgebra k V) :=
  (TensorProduct.map (LinearMap.id : FlagTensor k V r →ₗ[k] FlagTensor k V r)
    ((CFSG.LinearAlgebra.ExteriorIncidence.incidence b).comp
      (TensorProduct.map (⋀[k]^(r + 1) V).subtype (⋀[k]^(r + 2) V).subtype))).comp
    (TensorProduct.assoc k (FlagTensor k V r) (⋀[k]^(r + 1) V)
      (⋀[k]^(r + 2) V)).toLinearMap

theorem lastIncidence_tmul_tmul (b : Module.Basis I k V) (r : ℕ)
    (w : FlagTensor k V r) (p : ⋀[k]^(r + 1) V) (q : ⋀[k]^(r + 2) V) :
    lastIncidence b r ((w ⊗ₜ[k] p) ⊗ₜ[k] q) =
      w ⊗ₜ[k] CFSG.LinearAlgebra.ExteriorIncidence.incidence b
        ((p : ExteriorAlgebra k V) ⊗ₜ[k] (q : ExteriorAlgebra k V)) := by
  unfold lastIncidence
  rw [LinearMap.comp_apply]
  change (TensorProduct.map LinearMap.id
    ((CFSG.LinearAlgebra.ExteriorIncidence.incidence b).comp
      (TensorProduct.map (⋀[k]^(r + 1) V).subtype (⋀[k]^(r + 2) V).subtype)))
      ((TensorProduct.assoc k (FlagTensor k V r) (⋀[k]^(r + 1) V) (⋀[k]^(r + 2) V))
        ((w ⊗ₜ[k] p) ⊗ₜ[k] q)) = _
  rw [TensorProduct.assoc_tmul, TensorProduct.map_tmul]
  simp [TensorProduct.map_tmul]

@[expose] def flagCone (b : Module.Basis I k V) : (r : ℕ) → Set (FlagTensor k V r)
  | 0 => Set.univ
  | 1 => tensorCone k (⋀[k]^1 V) (Set.univ : Set k)
  | r + 2 => tensorCone k (⋀[k]^(r + 2) V) (flagCone b (r + 1)) ∩
      (LinearMap.ker (lastIncidence b r) : Set (FlagTensor k V (r + 2)))

theorem zero_mem_flagCone (b : Module.Basis I k V) (r : ℕ) :
    (0 : FlagTensor k V r) ∈ flagCone b r := by
  induction r using Nat.strong_induction_on with
  | h r ih =>
    cases r with
    | zero => trivial
    | succ r =>
      cases r with
      | zero => exact ⟨0, trivial, 0, by simp⟩
      | succ r =>
        refine ⟨⟨0, ih (r + 1) (by omega), 0, by simp⟩, ?_⟩
        simp

theorem isCone_flagCone (b : Module.Basis I k V) (r : ℕ) :
    IsCone k (flagCone b r) := by
  induction r using Nat.strong_induction_on with
  | h r ih =>
    cases r with
    | zero => intro c w hw; trivial
    | succ r =>
      cases r with
      | zero =>
        rintro c _ ⟨w, hw, q, rfl⟩
        exact ⟨c • w, trivial, q, by
          simpa only [smul_eq_mul] using TensorProduct.smul_tmul' c w q⟩
      | succ r =>
        intro c z hz
        obtain ⟨⟨w, hw, q, heq⟩, hker⟩ := hz
        refine ⟨⟨c • w, ih (r + 1) (by omega) c w hw, q, ?_⟩, ?_⟩
        · rw [heq, TensorProduct.smul_tmul']
        · exact (LinearMap.ker (lastIncidence b r)).smul_mem c hker

theorem isZariskiClosed_flagCone [FiniteDimensional k V] (b : Module.Basis I k V) (r : ℕ) :
    IsZariskiClosed k (flagCone b r) := by
  have h0 : IsZariskiClosed k (Set.univ : Set k) := by
    simpa using isZariskiClosed_submodule (⊤ : Submodule k k)
  induction r using Nat.strong_induction_on with
  | h r ih =>
    cases r with
    | zero => exact h0
    | succ r =>
      cases r with
      | zero =>
        exact isZariskiClosed_tensorCone h0 (fun _ _ _ => trivial) (by trivial)
      | succ r =>
        exact (isZariskiClosed_tensorCone (ih (r + 1) (by omega))
          (isCone_flagCone b (r + 1)) (zero_mem_flagCone b (r + 1))).inter
          (isZariskiClosed_submodule (LinearMap.ker (lastIncidence b r)))

private theorem pureTensor_ne_zero {W E : Type u} [AddCommGroup W] [Module k W]
    [AddCommGroup E] [Module k E] (w : W) (e : E) (hw : w ≠ 0) (he : e ≠ 0) :
    w ⊗ₜ[k] e ≠ 0 := by
  have hW : LinearIndependent k (fun _ : Unit => w) :=
    (linearIndependent_subsingleton_index_iff _).mpr (fun _ => hw)
  have hE : LinearIndependent k (fun _ : Unit => e) :=
    (linearIndependent_subsingleton_index_iff _).mpr (fun _ => he)
  exact (hW.tmul_of_isDomain hE).ne_zero ((), ())

def firstIndices (d r : ℕ) : Finset (Fin d) := Finset.univ.filter fun i => i.val < r

@[simp] theorem mem_firstIndices {d r : ℕ} (i : Fin d) :
    i ∈ firstIndices d r ↔ i.val < r := by
  simp [firstIndices]

theorem firstIndices_mono (d : ℕ) {r s : ℕ} (h : r ≤ s) :
    firstIndices d r ⊆ firstIndices d s := by
  intro i hi
  exact mem_firstIndices i |>.mpr (lt_of_lt_of_le ((mem_firstIndices i).mp hi) h)

theorem card_firstIndices {d r : ℕ} (hr : r ≤ d) : (firstIndices d r).card = r := by
  classical
  calc
    (firstIndices d r).card = (Finset.univ : Finset (Fin r)).card := by
      refine Finset.card_bij
        (fun i hi => (⟨i.val, (mem_firstIndices i).mp hi⟩ : Fin r)) ?_ ?_ ?_
      · intro i hi
        exact Finset.mem_univ _
      · intro i hi j hj hij
        exact Fin.ext (congrArg (fun x : Fin r => x.val) hij)
      · intro j hj
        refine ⟨Fin.castLE hr j, ?_, ?_⟩
        · exact (mem_firstIndices _).mpr j.isLt
        · exact Fin.ext rfl
    _ = r := by simp

def initialWedge {d : ℕ} (b : Module.Basis (Fin d) k V) (r : ℕ) (hr : r ≤ d) :
    ⋀[k]^r V :=
  b.exteriorPower r ⟨firstIndices d r, card_firstIndices hr⟩

theorem initialWedge_coe {d : ℕ} (b : Module.Basis (Fin d) k V) (r : ℕ) (hr : r ≤ d) :
    (initialWedge b r hr : ExteriorAlgebra k V) = b.ExteriorAlgebra (firstIndices d r) :=
  (ExteriorAlgebra.basis_eq_coe_basis b ⟨firstIndices d r, card_firstIndices hr⟩).symm

theorem initialWedge_ne_zero {d : ℕ} (b : Module.Basis (Fin d) k V) (r : ℕ) (hr : r ≤ d) :
    initialWedge b r hr ≠ 0 :=
  (b.exteriorPower r).ne_zero _

@[expose] def basisFlagTensor {d : ℕ} (b : Module.Basis (Fin d) k V) :
    (r : ℕ) → (hr : r ≤ d) → FlagTensor k V r
  | 0, _ => 1
  | r + 1, hr => basisFlagTensor b r (Nat.le_trans (Nat.le_succ r) hr) ⊗ₜ[k]
      initialWedge b (r + 1) hr

theorem basisFlagTensor_ne_zero {d : ℕ} (b : Module.Basis (Fin d) k V) (r : ℕ) (hr : r ≤ d) :
    basisFlagTensor b r hr ≠ 0 := by
  induction r with
  | zero => exact one_ne_zero
  | succ r ih =>
    exact pureTensor_ne_zero _ _ (ih _) (initialWedge_ne_zero b (r + 1) hr)

theorem basisFlagTensor_mem_flagCone {d : ℕ} (b : Module.Basis (Fin d) k V) (r : ℕ) (hr : r ≤ d) :
    basisFlagTensor b r hr ∈ flagCone b r := by
  induction r using Nat.strong_induction_on with
  | h r ih =>
    cases r with
    | zero => trivial
    | succ r =>
      cases r with
      | zero => exact ⟨1, trivial, initialWedge b 1 hr, rfl⟩
      | succ r =>
        refine ⟨⟨basisFlagTensor b (r + 1) _, ih (r + 1) (by omega) _,
          initialWedge b (r + 2) hr, rfl⟩, ?_⟩
        have hinc : CFSG.LinearAlgebra.ExteriorIncidence.incidence b
            ((initialWedge b (r + 1) (by omega) : ExteriorAlgebra k V) ⊗ₜ[k]
              (initialWedge b (r + 2) hr : ExteriorAlgebra k V)) = 0 := by
          rw [initialWedge_coe, initialWedge_coe]
          apply (CFSG.LinearAlgebra.ExteriorIncidence.incidence_basis_tmul_eq_zero_iff _ _ _).mpr
          intro i hi
          have hi' := firstIndices_mono d (Nat.le_succ (r + 1)) hi
          simp [TauCeti.ExteriorAlgebra.ι_mul_basis, hi']
        change lastIncidence b r (basisFlagTensor b (r + 2) hr) = 0
        rw [basisFlagTensor, basisFlagTensor, lastIncidence_tmul_tmul, hinc,
          TensorProduct.tmul_zero]

theorem exists_ne_zero_mem_flagCone [FiniteDimensional k V] :
    ∃ w ∈ flagCone (Module.finBasis k V) (Module.finrank k V), w ≠ 0 := by
  let b := Module.finBasis k V
  exact ⟨basisFlagTensor b _ le_rfl, basisFlagTensor_mem_flagCone b _ le_rfl, basisFlagTensor_ne_zero b _ le_rfl⟩

theorem lastIncidence_eq {J : Type*} [Fintype J]
    (b : Module.Basis I k V) (c : Module.Basis J k V) (r : ℕ) :
    lastIncidence b r = lastIncidence c r := by
  simp only [lastIncidence, CFSG.LinearAlgebra.ExteriorIncidence.incidence_eq b c]

@[expose] def flagMap (f : V →ₗ[k] V) :
    (r : ℕ) → FlagTensor k V r →ₗ[k] FlagTensor k V r
  | 0 => LinearMap.id
  | r + 1 => TensorProduct.map (flagMap f r) (exteriorPower.map (r + 1) f)

theorem flagMap_tmul (f : V →ₗ[k] V) (r : ℕ) (w : FlagTensor k V r)
    (p : ⋀[k]^(r + 1) V) :
    flagMap f (r + 1) (w ⊗ₜ[k] p) =
      flagMap f r w ⊗ₜ[k] exteriorPower.map (r + 1) f p := by
  exact TensorProduct.map_tmul _ _ _ _

theorem lastIncidence_flagMap [LinearOrder I] (b : Module.Basis I k V) (e : V ≃ₗ[k] V) (r : ℕ)
    (z : FlagTensor k V (r + 2)) :
    lastIncidence (b.map e) r (flagMap e.toLinearMap (r + 2) z) =
      TensorProduct.map (flagMap e.toLinearMap r)
        (TensorProduct.map (ExteriorAlgebra.map e.toLinearMap).toLinearMap
          (ExteriorAlgebra.map e.toLinearMap).toLinearMap) (lastIncidence b r z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul w q =>
    induction w using TensorProduct.induction_on with
    | zero => simp [flagMap]
    | tmul w p =>
      have h := CFSG.LinearAlgebra.ExteriorIncidence.incidence_map b e
        ((p : ExteriorAlgebra k V) ⊗ₜ[k] (q : ExteriorAlgebra k V))
      rw [flagMap_tmul, flagMap_tmul, lastIncidence_tmul_tmul, lastIncidence_tmul_tmul,
        TensorProduct.map_tmul]
      simpa only [exteriorPower.coe_map, TensorProduct.map_tmul, AlgHom.toLinearMap_apply] using
        congrArg (fun x => flagMap e.toLinearMap r w ⊗ₜ[k] x) h
    | add w w' hw hw' =>
      simp only [TensorProduct.add_tmul, map_add, hw, hw']
  | add z z' hz hz' => simp only [map_add, hz, hz']

theorem flagMap_mem_flagCone [LinearOrder I] (b : Module.Basis I k V) (e : V ≃ₗ[k] V) (r : ℕ)
    {z : FlagTensor k V r} (hz : z ∈ flagCone b r) :
    flagMap e.toLinearMap r z ∈ flagCone b r := by
  induction r using Nat.strong_induction_on with
  | h r ih =>
    cases r with
    | zero => trivial
    | succ r =>
      cases r with
      | zero =>
        obtain ⟨w, hw, q, rfl⟩ := hz
        exact ⟨flagMap e.toLinearMap 0 w, trivial, exteriorPower.map 1 e.toLinearMap q,
          flagMap_tmul _ _ _ _⟩
      | succ r =>
        obtain ⟨⟨w, hw, q, rfl⟩, hker⟩ := hz
        refine ⟨⟨flagMap e.toLinearMap (r + 1) w, ih (r + 1) (by omega) hw,
          exteriorPower.map (r + 2) e.toLinearMap q, flagMap_tmul _ _ _ _⟩, ?_⟩
        change lastIncidence b r
          (flagMap e.toLinearMap (r + 2) (w ⊗ₜ[k] q)) = 0
        rw [lastIncidence_eq b (b.map e), lastIncidence_flagMap,
          LinearMap.mem_ker.mp hker, map_zero]

end CFSG.LieType.AlgebraicGroups.ClosedCone
