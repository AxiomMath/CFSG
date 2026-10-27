module

public import CFSG.ClassicalInvolution.Q3.Q3ZFraFrame
public import CFSG.ClassicalInvolution.Generic.Frame

public section

namespace CFSG.ClassicalInvolution.Q3.Q3V.Frame

open Matrix CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Models.SymplecticPairs (planeGroup IsHyperbolicPlane orthSet form
  form_add_left form_smul_left form_add_right form_smul_right mem_orthSet_span_pair mem_fixing)
open CFSG.LieType.Universal.Symplectic.SpExtras (mat)
open scoped commutatorElement

section Vector

variable {K : Type} [Field K] {n : ℕ}

theorem exists_ne_zero_orth (hn : 3 ≤ n) {P P' : Submodule K (Fin n ⊕ Fin n → K)}
    (hP : IsHyperbolicPlane P) (hP' : IsHyperbolicPlane P') :
    ∃ v : Fin n ⊕ Fin n → K, v ≠ 0 ∧ v ∈ orthSet (P : Set (Fin n ⊕ Fin n → K)) ∧
      v ∈ orthSet (P' : Set (Fin n ⊕ Fin n → K)) := by
  obtain ⟨u₁, w₁, -, rfl⟩ := hP
  obtain ⟨u₂, w₂, -, rfl⟩ := hP'
  let f : (Fin n ⊕ Fin n → K) →ₗ[K] (Fin 4 → K) :=
    { toFun := fun v => ![form v u₁, form v w₁, form v u₂, form v w₂]
      map_add' := fun v v' => by
        ext i
        fin_cases i <;> simp [form_add_left]
      map_smul' := fun c v => by
        ext i
        fin_cases i <;> simp [form_smul_left] }
  have hker : LinearMap.ker f ≠ ⊥ := LinearMap.ker_ne_bot_of_finrank_lt (by
    simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin]
    omega)
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
  have hfv : ∀ i, f v i = 0 := fun i => congrFun (LinearMap.mem_ker.1 hv) i
  exact ⟨v, hv0, mem_orthSet_span_pair.2 ⟨hfv 0, hfv 1⟩, mem_orthSet_span_pair.2 ⟨hfv 2, hfv 3⟩⟩

end Vector

section Commutator

variable {K : Type} [Field K] {n : ℕ}

theorem mul_comm_of_commutator_mem_center (hn : 3 ≤ n) (h2 : (2 : K) ≠ 0)
    {P P' : Submodule K (Fin n ⊕ Fin n → K)} (hP : IsHyperbolicPlane P)
    (hP' : IsHyperbolicPlane P') {x y : StatedSp n K} (hx : x ∈ planeGroup P)
    (hy : y ∈ planeGroup P') (hc : x * y * x⁻¹ * y⁻¹ ∈ Subgroup.center (StatedSp n K)) :
    x * y = y * x := by
  obtain ⟨v, hv0, hvP, hvP'⟩ := exists_ne_zero_orth hn hP hP'
  have hfixP : ∀ z ∈ planeGroup P, mat n K z *ᵥ v = v := fun z hz => mem_fixing.1 hz v hvP
  have hfixP' : ∀ z ∈ planeGroup P', mat n K z *ᵥ v = v := fun z hz => mem_fixing.1 hz v hvP'
  have hcv : mat n K (x * y * x⁻¹ * y⁻¹) *ᵥ v = v := by
    simp only [map_mul, ← Matrix.mulVec_mulVec]
    rw [hfixP' y⁻¹ (inv_mem hy), hfixP x⁻¹ (inv_mem hx), hfixP' y hy, hfixP x hx]
  rcases (Q3Z.mem_center_iff_negOne (by omega : 1 ≤ n)).1 hc with h | h
  · have h1 : ⁅x, y⁆ = 1 := by
      rw [commutatorElement_def]
      exact h
    exact commutatorElement_eq_one_iff_mul_comm.1 h1
  · exfalso
    rw [h, Q3Z.mat_negOne, Matrix.neg_mulVec, Matrix.one_mulVec] at hcv
    apply hv0
    funext t
    have h1 := congrFun hcv t
    simp only [Pi.neg_apply] at h1
    have h3 : (2 : K) * v t = 0 := by linear_combination -h1
    exact (mul_eq_zero.1 h3).resolve_left h2

theorem isHyperbolicPlane_map (g : StatedSp n K) {P : Submodule K (Fin n ⊕ Fin n → K)}
    (hP : IsHyperbolicPlane P) :
    IsHyperbolicPlane (P.map (Matrix.mulVecLin (mat n K g))) := by
  obtain ⟨u, w, huw, rfl⟩ := hP
  refine ⟨mat n K g *ᵥ u, mat n K g *ᵥ w, ?_, ?_⟩
  · rw [Models.SymplecticPairs.form_mulVec]
    exact huw
  · rw [Submodule.map_span]
    simp [Set.image_insert_eq]

end Commutator

section Criterion

variable {m : ℕ} {G : Type} [Group G]

theorem commutes_map_planeGroup_iff (hm : 3 ≤ m) {Θ : StatedSp m (GaloisField 3 1) →* G}
    (hker : Θ.ker ≤ Subgroup.center (StatedSp m (GaloisField 3 1)))
    {P P' : Submodule (GaloisField 3 1) (Fin m ⊕ Fin m → GaloisField 3 1)}
    (hP : IsHyperbolicPlane P) (hP' : IsHyperbolicPlane P') :
    Commutes ((planeGroup P).map Θ) ((planeGroup P').map Θ) ↔
      ∀ u ∈ P, ∀ v ∈ P', form u v = 0 := by
  rw [← Q3Z.commute_planeGroup_iff Q3Z.gf3_two_ne_zero (by omega) hP hP']
  constructor
  · intro h x hx y hy
    have hxy : Θ (x * y * x⁻¹ * y⁻¹) = 1 := by
      have h1 := h _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, h1]
      group
    exact mul_comm_of_commutator_mem_center hm Q3Z.gf3_two_ne_zero hP hP' hx hy
      (hker (MonoidHom.mem_ker.2 hxy))
  · rintro h _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [← map_mul, ← map_mul, h x hx y hy]

end Criterion

end CFSG.ClassicalInvolution.Q3.Q3V.Frame
