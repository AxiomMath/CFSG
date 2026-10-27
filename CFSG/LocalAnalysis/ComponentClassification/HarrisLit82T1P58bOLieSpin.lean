module

public import CFSG.LieType.Universal.Spin.Action
public import TauCeti.LinearAlgebra.CliffordAlgebra.VolumeElement

public section

namespace CFSG.ComponentClassification.HarrisLit.T1.P58b.OLie

open CliffordAlgebra QuadraticMap CFSG.LieType.Universal.Spin

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

theorem spinAction_spinAction {s : spinGroup Q} (hs : s * s = 1) (v : V) :
    spinAction Q s (spinAction Q s v) = v := by
  have h := congrArg (fun x => spinAction Q x v) hs
  simp only [map_mul, LinearEquiv.mul_apply, map_one] at h
  exact h

theorem spinAction_eq_neg {s : spinGroup Q} {w : V}
    (hw : w ∈ LinearMap.ker ((spinAction Q s : V →ₗ[K] V) + LinearMap.id)) :
    spinAction Q s w = -w := by
  rw [LinearMap.mem_ker, LinearMap.add_apply, LinearMap.id_apply] at hw
  exact eq_neg_of_add_eq_zero_left hw

theorem polar_eq_zero_of_mem_ker (h2 : (2 : K) ≠ 0) {s : spinGroup Q} {w v : V}
    (hw : w ∈ LinearMap.ker ((spinAction Q s : V →ₗ[K] V) + LinearMap.id))
    (hv : spinAction Q s v = v) : polar Q w v = 0 := by
  have h := polar_spinAction Q s w v
  rw [spinAction_eq_neg hw, hv, polar_neg_left] at h
  have h' : (2 : K) * polar Q w v = 0 := by linear_combination -h
  exact (mul_eq_zero.1 h').resolve_left h2

theorem sub_mem_ker {s : spinGroup Q} (hs : s * s = 1) (u : V) :
    u - spinAction Q s u ∈ LinearMap.ker ((spinAction Q s : V →ₗ[K] V) + LinearMap.id) := by
  rw [LinearMap.mem_ker, LinearMap.add_apply, LinearMap.id_apply, LinearEquiv.coe_coe, map_sub,
    spinAction_spinAction hs]
  abel

theorem spinAction_add_self {s : spinGroup Q} (hs : s * s = 1) (u : V) :
    spinAction Q s (u + spinAction Q s u) = u + spinAction Q s u := by
  rw [map_add, spinAction_spinAction hs, add_comm]

theorem eq_zero_of_polar_ker (h2 : (2 : K) ≠ 0) (hQ : (polarBilin Q).Nondegenerate)
    {s : spinGroup Q} (hs : s * s = 1) {w : V}
    (hw : w ∈ LinearMap.ker ((spinAction Q s : V →ₗ[K] V) + LinearMap.id))
    (h : ∀ w' ∈ LinearMap.ker ((spinAction Q s : V →ₗ[K] V) + LinearMap.id),
      polar Q w w' = 0) : w = 0 := by
  refine hQ.1 w fun u => ?_
  change polar Q w u = 0
  have h1 := h _ (sub_mem_ker hs u)
  have h3 := polar_eq_zero_of_mem_ker h2 hw (spinAction_add_self hs u)
  have hsum : (u - spinAction Q s u) + (u + spinAction Q s u) = (2 : K) • u := by
    rw [two_smul]
    abel
  have h4 : polar Q w ((2 : K) • u) = 0 := by
    rw [← hsum, polar_add_right, h1, h3, add_zero]
  rw [polar_smul_right, smul_eq_mul] at h4
  exact (mul_eq_zero.1 h4).resolve_left h2

theorem involute_mul_ι_eq (h2 : (2 : K) ≠ 0) {s : spinGroup Q} (hs : s * s = 1) {l : List V}
    (hpair : l.Pairwise Q.IsOrtho)
    (hmem : ∀ x ∈ l, x ∈ LinearMap.ker ((spinAction Q s : V →ₗ[K] V) + LinearMap.id))
    (hspan : ∀ w ∈ LinearMap.ker ((spinAction Q s : V →ₗ[K] V) + LinearMap.id),
      w ∈ Submodule.span K {x : V | x ∈ l}) (u : V) :
    involute (l.map (ι Q)).prod * ι Q u = ι Q (spinAction Q s u) * (l.map (ι Q)).prod := by
  have : Invertible (2 : K) := invertibleOfNonzero h2
  have hinv : involute (l.map (ι Q)).prod = (-1 : K) ^ l.length • (l.map (ι Q)).prod :=
    involute_prod_map_ι l
  have hkeyW : ∀ w ∈ LinearMap.ker ((spinAction Q s : V →ₗ[K] V) + LinearMap.id),
      involute (l.map (ι Q)).prod * ι Q w = ι Q (spinAction Q s w) * (l.map (ι Q)).prod := by
    intro w hw
    rw [spinAction_eq_neg hw, map_neg, hinv, smul_mul_assoc,
      prod_map_ι_mul_ι_of_mem_span hpair (hspan w hw), smul_smul]
    rcases l with _ | ⟨a, l'⟩
    · have hw0 : w = 0 := by simpa using hspan w hw
      simp [hw0]
    · have hsign : (-1 : K) ^ (a :: l').length * (-1) ^ ((a :: l').length - 1) = -1 := by
        rw [List.length_cons, Nat.add_sub_cancel, pow_succ, mul_comm, ← mul_assoc, ← pow_add,
          ← two_mul, pow_mul, neg_one_sq, one_pow, one_mul]
      rw [hsign, neg_one_smul, neg_mul]
  have hkeyF : ∀ v, spinAction Q s v = v →
      involute (l.map (ι Q)).prod * ι Q v = ι Q (spinAction Q s v) * (l.map (ι Q)).prod := by
    intro v hv
    have horth : ∀ x ∈ l, Q.IsOrtho x v := fun x hx =>
      (isOrtho_polarBilin).1 (polar_eq_zero_of_mem_ker h2 (hmem x hx) hv)
    rw [hv, hinv, smul_mul_assoc, prod_map_ι_mul_ι_of_forall_isOrtho horth, smul_smul, ← pow_add,
      ← two_mul, pow_mul, neg_one_sq, one_pow, one_smul]
  have hW := Submodule.smul_mem _ (⅟(2 : K)) (sub_mem_ker hs u)
  have hF : spinAction Q s (⅟(2 : K) • (u + spinAction Q s u)) =
      ⅟(2 : K) • (u + spinAction Q s u) := by
    rw [map_smul, spinAction_add_self hs]
  have hu : u = ⅟(2 : K) • (u - spinAction Q s u) + ⅟(2 : K) • (u + spinAction Q s u) := by
    rw [← smul_add, sub_add_add_cancel, ← two_smul K u, smul_smul, invOf_mul_self, one_smul]
  conv_lhs => rw [hu]
  rw [map_add, mul_add, hkeyW _ hW, hkeyF _ hF, ← add_mul, ← map_add, ← map_add, ← hu]

variable [FiniteDimensional K V]

theorem even_choose_finrank_ker (h2 : (2 : K) ≠ 0) (hQ : (polarBilin Q).Nondegenerate)
    (s : spinGroup Q) (hs : s * s = 1) :
    Even ((Module.finrank K (LinearMap.ker
      ((spinAction Q s : V →ₗ[K] V) + LinearMap.id))).choose 2) := by
  have : Invertible (2 : K) := invertibleOfNonzero h2
  set W := LinearMap.ker ((spinAction Q s : V →ₗ[K] V) + LinearMap.id) with hWdef
  set Q' : QuadraticForm K W := Q.comp W.subtype with hQ'
  have hsymm : (polarBilin Q').IsSymm := ⟨fun x y => polar_comm Q' x y⟩
  obtain ⟨b, hb⟩ := LinearMap.BilinForm.exists_orthogonal_basis hsymm
  have hsep : (polarBilin Q').SeparatingLeft := by
    intro x hx
    apply Subtype.ext
    exact eq_zero_of_polar_ker h2 hQ hs x.2 fun w' hw' => hx ⟨w', hw'⟩
  have hb0 : ∀ i, Q (b i : V) ≠ 0 := by
    intro i h0
    apply hb.not_isOrtho_basis_self_of_separatingLeft hsep i
    change polar Q (b i : V) (b i : V) = 0
    rw [polar_self, h0, smul_zero]
  set l : List V := List.ofFn fun i => (b i : V) with hl
  have hlen : l.length = Module.finrank K W := by rw [hl, List.length_ofFn]
  have hmem : ∀ x ∈ l, x ∈ W := by
    intro x hx
    obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hx
    exact (b i).2
  have hpair : l.Pairwise Q.IsOrtho := by
    rw [hl, List.pairwise_ofFn]
    intro i j hij
    exact (isOrtho_polarBilin).1 (hb hij.ne)
  have hspan : ∀ w ∈ W, w ∈ Submodule.span K {x : V | x ∈ l} := by
    intro w hw
    have hrepr : (∑ i, ((b.repr ⟨w, hw⟩ i • b i : W) : V)) = w := by
      rw [← Submodule.coe_sum, b.sum_repr]
    rw [← hrepr]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [Submodule.coe_smul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (List.mem_ofFn.2 ⟨i, rfl⟩))
  set y := (l.map (ι Q)).prod with hy
  have hyu : IsUnit y := by
    apply isUnit_prod_map_ι
    rw [isUnit_iff_ne_zero]
    refine List.prod_ne_zero fun h => ?_
    obtain ⟨x, hx, hx0⟩ := List.mem_map.1 h
    obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hx
    exact hb0 i hx0
  have hkey : ∀ u, involute y * ι Q u = ι Q (spinAction Q s u) * y :=
    involute_mul_ι_eq h2 hs hpair hmem hspan
  set Y := hyu.unit with hY
  have hYv : (Y : CliffordAlgebra Q) = y := hyu.unit_spec
  set x := ((Y⁻¹ : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) * s with hx
  have hxv : ∀ v, involute x * ι Q v = ι Q v * x := by
    intro v
    have hs' : (s : CliffordAlgebra Q) * ι Q v = ι Q (spinAction Q s v) * s := by
      rw [ι_spinAction, mul_assoc _ _ (s : CliffordAlgebra Q), coe_inv_mul_coe, mul_one]
    have hinvY : involute ((Y⁻¹ : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) * involute y = 1 := by
      rw [← map_mul, ← hYv, Units.inv_mul, map_one]
    have hg : ι Q (spinAction Q s v) =
        involute y * ι Q v * ((Y⁻¹ : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) := by
      rw [hkey v, mul_assoc, ← hYv, Units.mul_inv, mul_one]
    rw [hx, map_mul, spinGroup.involute_eq s.2, mul_assoc, hs', hg, ← mul_assoc, ← mul_assoc,
      ← mul_assoc, hinvY, one_mul, mul_assoc]
  obtain ⟨r, hr⟩ :=
    exists_eq_algebraMap_of_involute_mul_ι_eq_ι_mul Q ((nondegenerate_polar_iff).1 hQ) x hxv
  have hsr : (s : CliffordAlgebra Q) = r • y := by
    have hsx : (s : CliffordAlgebra Q) = y * x := by
      rw [hx, ← mul_assoc, ← hYv, Units.mul_inv, one_mul]
    rw [hsx, hr, ← Algebra.commutes, ← Algebra.smul_def]
  have hrev : reverse (s : CliffordAlgebra Q) =
      (-1 : K) ^ (Module.finrank K W).choose 2 • (s : CliffordAlgebra Q) := by
    rw [hsr, map_smul, hy, reverse_prod_map_ι_of_pairwise_isOrtho hpair, hlen, smul_comm]
  have hstar : star (s : CliffordAlgebra Q) * s = 1 := spinGroup.star_mul_self_of_mem s.2
  rw [star_def, spinGroup.involute_eq s.2, hrev, smul_mul_assoc] at hstar
  have hss : (s : CliffordAlgebra Q) * s = 1 := by
    have h1 := congrArg Subtype.val hs
    simpa using h1
  rw [hss, Algebra.smul_def, mul_one] at hstar
  have hK : (-1 : K) ^ (Module.finrank K W).choose 2 = 1 := by
    apply algebraMap_injective' Q
    rw [hstar, map_one]
  have hne : (-1 : K) ≠ 1 := fun h => h2 (by linear_combination -h)
  exact (neg_one_pow_eq_one_iff_even hne).1 hK

end CFSG.ComponentClassification.HarrisLit.T1.P58b.OLie
