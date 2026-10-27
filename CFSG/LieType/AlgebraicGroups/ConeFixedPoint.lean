module

public import CFSG.LieType.AlgebraicGroups.ClosedConeFinite
public import TauCeti.Algebra.AlgebraicGroup.Solvable.LieKolchin
public import Mathlib.RingTheory.HopfAlgebra.GroupLike

public noncomputable section

open WithConv TauCeti.Comodule

namespace CFSG.LieType.AlgebraicGroups.ClosedCone

universe u v w

variable {k : Type u} [Field k] {H : Type v} [CommRing H] [HopfAlgebra k H]
variable {M : Type w} [AddCommGroup M] [Module k M] [TauCeti.Comodule k H M]

@[expose] def basisFlag {n : ℕ} (b : Module.Basis (Fin n) k M) (j : ℕ) : Submodule k M :=
  ⨅ (i : Fin n) (_ : j ≤ i.val), LinearMap.ker (b.coord i)

theorem mem_basisFlag {n : ℕ} {b : Module.Basis (Fin n) k M} {j : ℕ} {v : M} :
    v ∈ basisFlag b j ↔ ∀ i : Fin n, j ≤ i.val → b.coord i v = 0 := by
  simp [basisFlag, Submodule.mem_iInf]

theorem coord_basePointsRepresentation {n : ℕ} (b : Module.Basis (Fin n) k M)
    (g : WithConv (H →ₐ[k] k)) (v : M) (i : Fin n) :
    b.coord i (basePointsRepresentation (H := H) M g v) =
      ∑ l, b.coord l v * g.ofConv (coefficientMatrix (C := H) b i l) := by
  conv_lhs => rw [← b.sum_repr v]
  rw [map_sum, map_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [map_smul, map_smul, smul_eq_mul, coefficientMatrix_apply, apply_matrixCoefficient]
  simp only [Module.Basis.coord_apply]

theorem basePointsRepresentation_mem_basisFlag {n : ℕ} {b : Module.Basis (Fin n) k M}
    (htri : (coefficientMatrix (C := H) b).IsUpperTriangular) (g : WithConv (H →ₐ[k] k))
    {j : ℕ} {v : M} (hv : v ∈ basisFlag b j) :
    basePointsRepresentation (H := H) M g v ∈ basisFlag b j := by
  rw [mem_basisFlag] at hv ⊢
  intro i hi
  rw [coord_basePointsRepresentation]
  refine Finset.sum_eq_zero fun l _ => ?_
  by_cases hl : j ≤ l.val
  · rw [hv l hl, zero_mul]
  · have hli : l < i := by
      rw [Fin.lt_iff_val_lt_val]
      omega
    rw [htri hli, map_zero, mul_zero]

theorem coord_basePointsRepresentation_of_mem_basisFlag {n : ℕ} {b : Module.Basis (Fin n) k M}
    (htri : (coefficientMatrix (C := H) b).IsUpperTriangular) (g : WithConv (H →ₐ[k] k))
    {i : Fin n} {v : M} (hv : v ∈ basisFlag b (i.val + 1)) :
    b.coord i (basePointsRepresentation (H := H) M g v) =
      g.ofConv (coefficientMatrix (C := H) b i i) * b.coord i v := by
  rw [coord_basePointsRepresentation, Finset.sum_eq_single i]
  · ring
  · intro l _ hli
    rcases lt_or_gt_of_ne hli with h | h
    · rw [htri h, map_zero, mul_zero]
    · rw [(mem_basisFlag.mp hv) l (by rw [Fin.lt_iff_val_lt_val] at h; omega), zero_mul]
  · simp

theorem basePointsRepresentation_eq_smul_of_finite [IsAlgClosed k] [Algebra.FiniteType k H]
    [IsDomain H] {χ : H} (hχ : IsGroupLikeElem k χ) {A : Set M} (hA : A.Finite)
    (hact : ∀ g : WithConv (H →ₐ[k] k), ∀ v ∈ A,
      (g.ofConv χ)⁻¹ • basePointsRepresentation (H := H) M g v ∈ A)
    {a : M} (ha : a ∈ A) (g : WithConv (H →ₐ[k] k)) :
    basePointsRepresentation (H := H) M g a = g.ofConv χ • a := by
  classical
  have hχu : ∀ q : WithConv (H →ₐ[k] k), q.ofConv χ ≠ 0 := fun q =>
    (hχ.isUnit.map q.ofConv).ne_zero
  have hsep : ∀ a' : M, a' ≠ a → ∃ ψ : Module.Dual k M, ψ a ≠ ψ a' := by
    intro a' h
    by_contra hcon
    simp only [ne_eq, not_exists, not_not] at hcon
    refine h (sub_eq_zero.mp ?_).symm
    exact (Module.forall_dual_apply_eq_zero_iff k (a - a')).mp fun ψ => by
      rw [map_sub, hcon ψ, sub_self]
  choose! ψ hψ using hsep
  let S := hA.toFinset.erase a
  let h₁ : H := ∏ a' ∈ S, (matrixCoefficient (C := H) (ψ a') a - ψ a' a' • χ)
  have hval : ∀ (q : WithConv (H →ₐ[k] k)) (θ : Module.Dual k M) (c : k),
      q.ofConv (matrixCoefficient (C := H) θ a - c • χ) =
        θ (basePointsRepresentation (H := H) M q a) - c * q.ofConv χ := by
    intro q θ c
    rw [map_sub, apply_matrixCoefficient, map_smul, smul_eq_mul]
  have key : ∀ θ : Module.Dual k M, h₁ * (matrixCoefficient (C := H) θ a - θ a • χ) = 0 := by
    intro θ
    apply TauCeti.eq_of_forall_algHom_apply_eq (k := k) (K := k)
    intro q
    rw [map_mul, map_zero]
    let q' : WithConv (H →ₐ[k] k) := toConv q
    change q'.ofConv h₁ * q'.ofConv _ = 0
    by_cases hqa : (q'.ofConv χ)⁻¹ • basePointsRepresentation (H := H) M q' a = a
    · refine mul_eq_zero_of_right _ ?_
      have hq : basePointsRepresentation (H := H) M q' a = q'.ofConv χ • a := by
        rw [← hqa, smul_smul, mul_inv_cancel₀ (hχu q'), one_smul, hqa]
      rw [hval, hq, map_smul, smul_eq_mul, mul_comm, sub_self]
    · refine mul_eq_zero_of_left ?_ _
      have hmem : (q'.ofConv χ)⁻¹ • basePointsRepresentation (H := H) M q' a ∈ S :=
        Finset.mem_erase.mpr ⟨hqa, hA.mem_toFinset.mpr (hact q' a ha)⟩
      rw [map_prod]
      refine Finset.prod_eq_zero hmem ?_
      set a' := (q'.ofConv χ)⁻¹ • basePointsRepresentation (H := H) M q' a
      have hq : basePointsRepresentation (H := H) M q' a = q'.ofConv χ • a' := by
        rw [smul_smul, mul_inv_cancel₀ (hχu q'), one_smul]
      rw [hval, hq, map_smul, smul_eq_mul, mul_comm, sub_self]
  have hε : ∀ (θ : Module.Dual k M) (c : k),
      Bialgebra.counitAlgHom k H (matrixCoefficient (C := H) θ a - c • χ) = θ a - c := by
    intro θ c
    rw [map_sub, map_smul, Bialgebra.counitAlgHom_apply, Bialgebra.counitAlgHom_apply,
      counit_matrixCoefficient, hχ.counit_eq_one, smul_eq_mul, mul_one]
  have h₁ne : h₁ ≠ 0 := by
    intro h0
    have h := congrArg (Bialgebra.counitAlgHom k H) h0
    rw [map_prod, map_zero] at h
    obtain ⟨a', ha', h'⟩ := Finset.prod_eq_zero_iff.mp h
    rw [hε, sub_eq_zero] at h'
    exact hψ a' (Finset.ne_of_mem_erase ha') h'
  refine sub_eq_zero.mp ((Module.forall_dual_apply_eq_zero_iff k
    (basePointsRepresentation (H := H) M g a - g.ofConv χ • a)).mp fun θ => ?_)
  have h2 := (mul_eq_zero.mp (key θ)).resolve_left h₁ne
  have h3 := congrArg g.ofConv h2
  rw [hval, map_zero, sub_eq_zero] at h3
  rw [map_sub, h3, map_smul, smul_eq_mul, mul_comm, sub_self]

theorem exists_ne_zero_mem_forall_eq_smul [IsAlgClosed k] [Algebra.FiniteType k H] [IsDomain H]
    [Group.IsSolvable (WithConv (H →ₐ[k] k))] [FiniteDimensional k M] {C : Set M}
    (hC : IsZariskiClosed k C) (hcone : IsCone k C)
    (hG : ∀ g : WithConv (H →ₐ[k] k), ∀ v ∈ C,
      basePointsRepresentation (H := H) M g v ∈ C)
    (hne : ∃ v ∈ C, v ≠ 0) :
    ∃ v ∈ C, v ≠ 0 ∧ ∃ χ : H, IsGroupLikeElem k χ ∧ ∀ g : WithConv (H →ₐ[k] k),
      basePointsRepresentation (H := H) M g v = g.ofConv χ • v := by
  classical
  have : ConnectedSpace (PrimeSpectrum H) :=
    connectedSpace_iff_univ.mpr (IrreducibleSpace.isIrreducible_univ _).isConnected
  obtain ⟨n, b, htri, hdiag⟩ :=
    exists_basis_coefficientMatrix_isUpperTriangular_of_isSolvable (k := k) (H := H) (M := M)
  have hex : ∃ j, ∃ v ∈ C, v ∈ basisFlag b j ∧ v ≠ 0 := by
    obtain ⟨v, hv, hv0⟩ := hne
    exact ⟨n, v, hv, mem_basisFlag.mpr fun i hi => absurd i.isLt (by omega), hv0⟩
  obtain ⟨v₀, hv₀C, hv₀F, hv₀⟩ := Nat.find_spec hex
  have hj₀pos : Nat.find hex ≠ 0 := by
    intro h
    rw [h] at hv₀F
    exact hv₀ (b.ext_elem fun i => by simpa using (mem_basisFlag.mp hv₀F) i (Nat.zero_le _))
  have hj₀n : Nat.find hex ≤ n := Nat.find_min' hex
    ⟨v₀, hv₀C, mem_basisFlag.mpr fun i hi => absurd i.isLt (by omega), hv₀⟩
  let i₀ : Fin n := ⟨Nat.find hex - 1, by omega⟩
  have hi₀ : i₀.val + 1 = Nat.find hex := by
    simp only [i₀]
    omega
  let C' := C ∩ (basisFlag b (Nat.find hex) : Set M)
  have hC' : IsZariskiClosed k C' := hC.inter (isZariskiClosed_submodule _)
  have hcone' : IsCone k C' := fun c v hv => ⟨hcone c v hv.1, (basisFlag b _).smul_mem c hv.2⟩
  have hφ : ∀ v ∈ C', b.coord i₀ v = 0 → v = 0 := by
    intro v hv hv0
    by_contra hne0
    have hmem : v ∈ basisFlag b (Nat.find hex - 1) := mem_basisFlag.mpr fun i hi => by
      rcases eq_or_lt_of_le hi with h | h
      · have hii : i = i₀ := Fin.ext (by simp only [i₀]; omega)
        rw [hii]
        exact hv0
      · exact (mem_basisFlag.mp hv.2) i (by omega)
    exact Nat.find_min hex (show Nat.find hex - 1 < Nat.find hex by omega) ⟨v, hv.1, hmem, hne0⟩
  have hfin := finite_setOf_mem_and_eq_one hC' hcone' (b.coord i₀) hφ
  have hv₀φ : b.coord i₀ v₀ ≠ 0 := fun h => hv₀ (hφ v₀ ⟨hv₀C, hv₀F⟩ h)
  let χ := coefficientMatrix (C := H) b i₀ i₀
  have hχ : IsGroupLikeElem k χ := hdiag i₀
  have hχu : ∀ g : WithConv (H →ₐ[k] k), g.ofConv χ ≠ 0 := fun g =>
    (hχ.isUnit.map g.ofConv).ne_zero
  have hact : ∀ g : WithConv (H →ₐ[k] k), ∀ v ∈ {v | v ∈ C' ∧ b.coord i₀ v = 1},
      (g.ofConv χ)⁻¹ • basePointsRepresentation (H := H) M g v ∈
        {v | v ∈ C' ∧ b.coord i₀ v = 1} := by
    intro g v hv
    refine ⟨hcone' _ _ ⟨hG g v hv.1.1, basePointsRepresentation_mem_basisFlag htri g hv.1.2⟩, ?_⟩
    rw [map_smul, coord_basePointsRepresentation_of_mem_basisFlag htri g (hi₀ ▸ hv.1.2), hv.2,
      smul_eq_mul, mul_one, inv_mul_cancel₀ (hχu g)]
  let a := (b.coord i₀ v₀)⁻¹ • v₀
  have ha : a ∈ {v | v ∈ C' ∧ b.coord i₀ v = 1} := by
    refine ⟨hcone' _ _ ⟨hv₀C, hv₀F⟩, ?_⟩
    rw [map_smul, smul_eq_mul, inv_mul_cancel₀ hv₀φ]
  refine ⟨a, ha.1.1, fun h => ?_, χ, hχ,
    basePointsRepresentation_eq_smul_of_finite hχ hfin hact ha⟩
  have h1 := ha.2
  rw [h, map_zero] at h1
  exact zero_ne_one h1

end CFSG.LieType.AlgebraicGroups.ClosedCone
