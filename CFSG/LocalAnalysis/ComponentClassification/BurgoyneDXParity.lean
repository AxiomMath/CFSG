module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneDXSpin
public import TauCeti.LinearAlgebra.CliffordAlgebra.VolumeElement

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.DX

open CliffordAlgebra QuadraticMap CFSG.LieType.Universal.Spin

section Clifford

variable {F : Type} [Field F] {V : Type} [AddCommGroup V] [Module F V] [FiniteDimensional F V]
  {Q : QuadraticForm F V}

omit [FiniteDimensional F V] in
theorem ι_spinAction_star (x : spinGroup Q) (v : V) :
    ι Q (spinAction Q x v) = x * ι Q v * star (x : CliffordAlgebra Q) := by
  rw [ι_spinAction, ← spinGroup.star_eq_inv, spinGroup.coe_star]

variable [Invertible (2 : F)]

theorem mul_self_eq_of_prod (hQ : Q.Nondegenerate) (x : spinGroup Q) {l : List V}
    (hl : l.Pairwise Q.IsOrtho) (hQl : IsUnit (l.map Q).prod) (hev : Even l.length)
    (hconj : ∀ w, (l.map (ι Q)).prod * ι Q w = ι Q (spinAction Q x w) * (l.map (ι Q)).prod) :
    (x : CliffordAlgebra Q) * x = algebraMap F _ ((-1 : F) ^ l.length.choose 2) := by
  set P := (l.map (ι Q)).prod with hP
  set X : CliffordAlgebra Q := ↑x with hX
  have hsX : star X * X = 1 := spinGroup.star_mul_self_of_mem x.2
  have hXs : X * star X = 1 := spinGroup.mul_star_self_of_mem x.2
  set y := star X * P with hy
  have hinvP : involute P = P := by
    rw [hP, involute_prod_map_ι, hev.neg_one_pow, one_smul]
  have hinvy : involute y = y := by
    rw [hy, map_mul, hinvP, spinGroup.involute_eq (spinGroup.star_mem x.2)]
  have hcomm : ∀ w, involute y * ι Q w = ι Q w * y := by
    intro w
    rw [hinvy, hy, mul_assoc, hconj, ι_spinAction_star]
    calc star X * (X * ι Q w * star X * P) = (star X * X) * ι Q w * (star X * P) := by
          simp only [mul_assoc]
      _ = ι Q w * (star X * P) := by rw [hsX, one_mul]
  obtain ⟨r, hr⟩ := exists_eq_algebraMap_of_involute_mul_ι_eq_ι_mul Q hQ y hcomm
  have hPx : P = X * algebraMap F _ r := by
    rw [← hr, hy, ← mul_assoc, hXs, one_mul]
  have hrevX : reverse X * X = 1 := by
    have h := hsX
    rwa [star_def, spinGroup.involute_eq x.2] at h
  have h1 : reverse P * P = algebraMap F _ (r * r) := by
    rw [hPx, reverse.map_mul, reverse.commutes]
    calc algebraMap F _ r * reverse X * (X * algebraMap F _ r)
        = algebraMap F _ r * (reverse X * X) * algebraMap F _ r := by simp only [mul_assoc]
      _ = algebraMap F _ (r * r) := by rw [hrevX, mul_one, ← map_mul]
  have hsign : ((-1 : F) ^ l.length.choose 2) * ((-1 : F) ^ l.length.choose 2) = 1 := by
    rw [← mul_pow, neg_one_mul, neg_neg, one_pow]
  have h2 : reverse P * P = algebraMap F _ ((l.map Q).prod) := by
    rw [reverse_prod_map_ι_of_pairwise_isOrtho hl, smul_mul_assoc, prod_map_ι_sq_scalar hl,
      Algebra.smul_def, ← map_mul, ← mul_assoc, hsign, one_mul]
  have hr2 : r * r = (l.map Q).prod := algebraMap_injective' Q (h1.symm.trans h2)
  have hr0 : r * r ≠ 0 := by
    rw [hr2]
    exact hQl.ne_zero
  have hPx' : P = r • X := by rw [hPx, ← Algebra.commutes, ← Algebra.smul_def]
  have e : (r * r) • (X * X) = algebraMap F _ ((-1 : F) ^ l.length.choose 2 * (r * r)) := by
    rw [← smul_mul_smul_comm, ← hPx', prod_map_ι_sq_scalar hl, hr2]
  calc X * X = (r * r)⁻¹ • ((r * r) • (X * X)) := by
        rw [smul_smul, inv_mul_cancel₀ hr0, one_smul]
    _ = algebraMap F _ ((-1 : F) ^ l.length.choose 2) := by
        rw [e, Algebra.smul_def, ← map_mul, mul_left_comm, inv_mul_cancel₀ hr0, mul_one]

theorem spin_mul_self_eq (hQ : Q.Nondegenerate) (hrad : ∀ v, (∀ w, polar Q v w = 0) → v = 0)
    (x : spinGroup Q) (hx : ∀ v, spinAction Q x (spinAction Q x v) = v) {m : ℕ}
    (hm : Module.finrank F (LinearMap.ker ((spinAction Q x : V →ₗ[F] V) + LinearMap.id)) = m)
    (hev : Even m) : (x : CliffordAlgebra Q) * x = algebraMap F _ ((-1 : F) ^ m.choose 2) := by
  set u : V →ₗ[F] V := (spinAction Q x : V →ₗ[F] V) with hu
  set U := LinearMap.ker (u + LinearMap.id) with hU
  have huU : ∀ w ∈ U, u w = -w := by
    intro w hw
    have h := LinearMap.mem_ker.mp hw
    rw [LinearMap.add_apply, LinearMap.id_apply] at h
    exact eq_neg_of_add_eq_zero_left h
  have hiso : ∀ v w, polar Q (u v) (u w) = polar Q v w := by
    intro v w
    simp only [polar, hu, LinearEquiv.coe_coe, ← map_add, map_spinAction]
  set B : LinearMap.BilinForm F U := ((associatedHom F) Q).domRestrict₁₂ U U with hB
  have hBs : LinearMap.IsSymm B := (QuadraticForm.associated_isSymm F Q).domRestrict U
  obtain ⟨b, hb⟩ := LinearMap.BilinForm.exists_orthogonal_basis hBs
  set l : List V := List.ofFn fun i => (b i : V) with hl
  have hlen : l.length = m := by rw [hl, List.length_ofFn, hm]
  have h2i : (⅟(2 : F)) ≠ 0 := by
    intro h
    have h' := mul_invOf_self (2 : F)
    rw [h, mul_zero] at h'
    exact zero_ne_one h'
  have hpolar : ∀ a c : U, B a c = 0 ↔ polar Q (a : V) (c : V) = 0 := by
    intro a c
    have e : B a c = ⅟(2 : F) * polar Q (a : V) (c : V) := by
      rw [hB, LinearMap.domRestrict₁₂_apply, associated_apply]
      rfl
    rw [e, mul_eq_zero, or_iff_right h2i]
  have hortho : l.Pairwise Q.IsOrtho := by
    rw [hl, List.pairwise_ofFn]
    intro i j hij
    rw [QuadraticMap.isOrtho_def]
    have := (hpolar (b i) (b j)).mp (hb hij.ne)
    rw [polar] at this
    linear_combination this
  have horthUW : ∀ a ∈ U, ∀ w, u w = w → polar Q a w = 0 := by
    intro a ha w hw
    have h := hiso a w
    rw [huU a ha, hw, polar_neg_left] at h
    have h2' : (2 : F) ≠ 0 := two_ne_zero
    have : 2 * polar Q a w = 0 := by linear_combination -h
    exact (mul_eq_zero.mp this).resolve_left h2'
  have hsplit : ∀ w, ⅟(2 : F) • (w - u w) ∈ U ∧ u (⅟(2 : F) • (w + u w)) = ⅟(2 : F) • (w + u w) ∧
      w = ⅟(2 : F) • (w + u w) + ⅟(2 : F) • (w - u w) := by
    intro w
    have huu : u (u w) = w := hx w
    refine ⟨?_, ?_, ?_⟩
    · rw [LinearMap.mem_ker, LinearMap.add_apply, LinearMap.id_apply, map_smul, map_sub, huu,
        ← smul_add]
      simp
    · rw [map_smul, map_add, huu, add_comm]
    · rw [← smul_add, show w + u w + (w - u w) = (2 : F) • w by rw [two_smul]; abel, smul_smul,
        invOf_mul_self, one_smul]
  have hQb : ∀ i, Q (b i : V) ≠ 0 := by
    intro i hi
    apply b.ne_zero i
    apply Subtype.ext
    apply hrad
    intro w
    obtain ⟨hU', hW', hw⟩ := hsplit w
    rw [hw, polar_add_right]
    have h1 : polar Q (b i : V) (⅟(2 : F) • (w + u w)) = 0 := horthUW _ (b i).2 _ hW'
    have h2 : polar Q (b i : V) (⅟(2 : F) • (w - u w)) = 0 := by
      set c : U := ⟨_, hU'⟩
      have hc : B (b i) c = 0 := by
        have : ∀ j, B (b i) (b j) = 0 := by
          intro j
          by_cases hij : i = j
          · subst hij
            rw [hB, LinearMap.domRestrict₁₂_apply, associated_eq_self_apply]
            exact hi
          · exact hb hij
        have hspan : c ∈ Submodule.span F (Set.range b) := by
          rw [b.span_eq]
          exact Submodule.mem_top
        refine Submodule.span_induction (fun y hy => ?_) ?_ (fun y z _ _ hy hz => ?_)
          (fun a y _ hy => ?_) hspan
        · obtain ⟨j, rfl⟩ := hy
          exact this j
        · exact map_zero _
        · rw [map_add, hy, hz, add_zero]
        · rw [map_smul, hy, smul_zero]
      exact (hpolar (b i) c).mp hc
    rw [h1, h2, add_zero]
  have hunit : IsUnit (l.map Q).prod := by
    refine List.prod_isUnit fun z hz => ?_
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hz
    rw [hl, List.mem_ofFn] at hv
    obtain ⟨i, rfl⟩ := hv
    exact isUnit_iff_ne_zero.mpr (hQb i)
  have hspanU : ∀ w ∈ U, w ∈ Submodule.span F {z : V | z ∈ l} := by
    intro w hw
    have hw' : (⟨w, hw⟩ : U) ∈ Submodule.span F (Set.range b) := by
      rw [b.span_eq]
      exact Submodule.mem_top
    have hmap := Submodule.mem_map_of_mem (f := U.subtype) hw'
    rw [Submodule.map_span] at hmap
    refine Submodule.span_mono ?_ hmap
    rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
    change (b i : V) ∈ l
    rw [hl, List.mem_ofFn]
    exact ⟨i, rfl⟩
  have hevl : Even l.length := hlen ▸ hev
  have hm1 : 0 < l.length → (-1 : F) ^ (l.length - 1) = -1 := by
    intro hpos
    obtain ⟨k, hk⟩ := hevl
    have : l.length - 1 = 2 * (k - 1) + 1 := by omega
    rw [this, pow_succ, pow_mul, neg_one_sq, one_pow, one_mul]
  refine (mul_self_eq_of_prod hQ x hortho hunit hevl ?_).trans (by rw [hlen])
  intro w
  obtain ⟨hU', hW', hw⟩ := hsplit w
  rw [hw, map_add, map_add, map_add, mul_add, add_mul]
  congr 1
  ·
    rw [prod_map_ι_mul_ι_of_forall_isOrtho, hevl.neg_one_pow, one_smul]
    · change _ = ι Q (u _) * _
      rw [hW']
    · intro z hz
      rw [hl, List.mem_ofFn] at hz
      obtain ⟨i, rfl⟩ := hz
      rw [QuadraticMap.isOrtho_def]
      have := horthUW _ (b i).2 _ hW'
      rw [polar] at this
      linear_combination this
  ·
    rcases Nat.eq_zero_or_pos l.length with h0 | hpos
    · have hnil : l = [] := List.eq_nil_of_length_eq_zero h0
      have h0' := hspanU _ hU'
      rw [hnil] at h0'
      simp only [List.not_mem_nil, Set.ofPred_false, Submodule.span_empty,
        Submodule.mem_bot] at h0'
      change _ = ι Q (u _) * _
      simp only [h0', map_zero, mul_zero, zero_mul]
    rw [prod_map_ι_mul_ι_of_mem_span hortho (hspanU _ hU'), hm1 hpos, neg_one_smul]
    change _ = ι Q (u _) * _
    rw [huU _ hU', map_neg, neg_mul]

end Clifford

section Sp8

open Module Matrix CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear

variable {F : Type} [Field F]

theorem mem_ker_reindex_add_id_iff {σ ι : Type} [Fintype σ] [Fintype ι] [DecidableEq σ]
    [DecidableEq ι] (e : σ ≃ ι) (M : Matrix σ σ F) (v : ι → F) :
    v ∈ LinearMap.ker (Matrix.toLin' (Matrix.reindex e e M) + LinearMap.id) ↔
      v ∘ e ∈ LinearMap.ker (Matrix.toLin' M + LinearMap.id) := by
  rw [LinearMap.mem_ker, LinearMap.mem_ker, LinearMap.add_apply, LinearMap.add_apply,
    LinearMap.id_apply, LinearMap.id_apply, Matrix.toLin'_apply, Matrix.toLin'_apply,
    Matrix.reindex_apply, Matrix.submatrix_mulVec_equiv]
  simp only [Equiv.symm_symm]
  constructor
  · intro h
    ext k
    have := congrFun h (e k)
    simpa using this
  · intro h
    ext i
    have := congrFun h (e.symm i)
    simpa using this

theorem finrank_ker_reindex_add_id {σ ι : Type} [Fintype σ] [Fintype ι] [DecidableEq σ]
    [DecidableEq ι] (e : σ ≃ ι) (M : Matrix σ σ F) :
    finrank F (LinearMap.ker (Matrix.toLin' (Matrix.reindex e e M) + LinearMap.id)) =
      finrank F (LinearMap.ker (Matrix.toLin' M + LinearMap.id)) := by
  set φ : (ι → F) ≃ₗ[F] (σ → F) := LinearEquiv.funCongrLeft F F e with hφ
  have h : (LinearMap.ker (Matrix.toLin' (Matrix.reindex e e M) + LinearMap.id)).map
      φ.toLinearMap = LinearMap.ker (Matrix.toLin' M + LinearMap.id) := by
    ext w
    rw [Submodule.mem_map]
    constructor
    · rintro ⟨v, hv, rfl⟩
      exact (mem_ker_reindex_add_id_iff e M v).1 hv
    · intro hw
      refine ⟨w ∘ e.symm, ?_, ?_⟩
      · rw [mem_ker_reindex_add_id_iff]
        have : w ∘ e.symm ∘ e = w := by
          ext k
          simp
        rw [Function.comp_assoc, this]
        exact hw
      · ext k
        simp [hφ, LinearEquiv.funCongrLeft_apply]
  rw [← h, LinearEquiv.finrank_map_eq]

theorem neg_one_pow_choose_two_of_even {m : ℕ} (hm : Even m) :
    (-1 : F) ^ m.choose 2 = (-1) ^ (m / 2) := by
  obtain ⟨k, rfl⟩ := hm
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp
  have hc : (k + k).choose 2 = k * (2 * k - 1) := by
    rw [Nat.choose_two_right]
    have : k + k - 1 = 2 * k - 1 := by omega
    rw [this, show k + k = 2 * k by ring, Nat.mul_assoc, Nat.mul_div_cancel_left _ two_pos]
  rw [hc, show (k + k) / 2 = k by omega, pow_mul]
  rcases neg_one_pow_eq_or F k with h | h
  · rw [h, one_pow]
  · rw [h]
    have ho : Odd (2 * k - 1) := ⟨k - 1, by omega⟩
    exact ho.neg_one_pow

variable {p : ℕ} [CharP F p]

theorem mul_self_eq_negOne8_iff (hp2 : p ≠ 2) (x : Sp8 F) (hx : spinM F (x * x) = 1) {m : ℕ}
    (hm : finrank F (LinearMap.ker (Matrix.toLin'
      (((spinM F x : matrixDerived (Q8 F)) : GL (Fin (2 * 4)) F) :
        Matrix (Fin (2 * 4)) (Fin (2 * 4)) F) + LinearMap.id)) = m) (hev : Even m) :
    x * x = negOne8 F ↔ m % 4 = 2 := by
  have h2 : (2 : F) ≠ 0 := two_ne_zero8 F hp2
  have : Invertible (2 : F) := invertibleOfNonzero h2
  have hvalGL : ((spinM F x : matrixDerived (Q8 F)) : GL (Fin (2 * 4)) F) =
      CatalogueBOrthogonalPointData.reindexMatrixEquiv
        (CatalogueBOrthogonalPointData.plusIndexEquiv 4) (spinMatrix (quadPlus 4 F) x) :=
    CatalogueBOrthogonalPointReindexCovariance.statedDerivedReindexEquiv_val _ _ _ _
  have hval : (((spinM F x : matrixDerived (Q8 F)) : GL (Fin (2 * 4)) F) :
      Matrix (Fin (2 * 4)) (Fin (2 * 4)) F) =
      Matrix.reindex (CatalogueBOrthogonalPointData.plusIndexEquiv 4)
        (CatalogueBOrthogonalPointData.plusIndexEquiv 4)
        (spinMatrix (quadPlus 4 F) x : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) F) := by
    rw [hvalGL]
    rfl
  rw [hval, finrank_ker_reindex_add_id, coe_spinMatrix, Matrix.toLin'_toMatrix'] at hm
  have hxx : ∀ v, spinAction (quadPlus 4 F) x (spinAction (quadPlus 4 F) x v) = v := by
    intro v
    have hk : x * x ∈ (spinM F).ker := hx
    rcases (mem_ker_spinM_iff F _).1 hk with h | h
    · rw [← LinearEquiv.mul_apply, ← map_mul, h, map_one]
      rfl
    · rw [← LinearEquiv.mul_apply, ← map_mul, h]
      have hneg : negOne8 F ∈ (spinMatrix (quadPlus 4 F)).ker :=
        CFSG.LieType.Steinberg.CentralExt.SpinPlusClosed.negOne_mem_ker (by norm_num)
      have hm1 := congrArg
        (fun g : GL (Fin 4 ⊕ Fin 4) F => (↑g : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) F) *ᵥ v)
        (MonoidHom.mem_ker.mp hneg)
      simp only [spinMatrix_mulVec, Units.val_one, Matrix.one_mulVec] at hm1
      exact hm1
  have hsq := spin_mul_self_eq (nondegenerate_quadPlus 4 F)
    (fun v hv => (nondegenerate_polarBilin_quadPlus 4 F).1 v fun w => by simpa using hv w)
    x hxx hm hev
  rw [neg_one_pow_choose_two_of_even hev] at hsq
  have hcoe : ((x * x : Sp8 F) : CliffordAlgebra (quadPlus 4 F)) =
      algebraMap F _ ((-1 : F) ^ (m / 2)) := by
    rw [Submonoid.coe_mul, hsq]
  have hneg1 : (-1 : F) ≠ 1 := by
    intro h
    apply h2
    linear_combination -h
  constructor
  · intro h
    rw [h, spinGroup.coe_negOne, ← map_one (algebraMap F (CliffordAlgebra (quadPlus 4 F))),
      ← map_neg] at hcoe
    have hc := algebraMap_injective' (quadPlus 4 F) hcoe.symm
    rcases Nat.even_or_odd (m / 2) with he | ho
    · rw [he.neg_one_pow] at hc
      exact absurd hc.symm hneg1
    · obtain ⟨k, hk⟩ := hev
      obtain ⟨j, hj⟩ := ho
      omega
  · intro h4
    apply Subtype.ext
    rw [hcoe, spinGroup.coe_negOne]
    have ho : Odd (m / 2) := by
      refine ⟨(m / 2 - 1) / 2, ?_⟩
      omega
    rw [ho.neg_one_pow, map_neg, map_one]

end Sp8

end CFSG.ComponentClassification.Burgoyne.DX
