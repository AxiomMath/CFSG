module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267ClsCompFam
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165Lin5
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBUnitaryAllDimensions
import CFSG.LocalAnalysis.ComponentClassification.OddSelectorOrthogonal
import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofQ81P2L33OCOmTools

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S267.Cls

open Matrix Module CFSG.ComponentClassification

variable {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K] {σ : K →+* K}

section Derived

variable {G : Type*} [Group G]

theorem commutator_eq_of_perfect {H N : Subgroup G} (hHN : ⁅H, H⁆ ≤ N) (hNH : N ≤ H)
    (hN : commutator N = ⊤) : ⁅H, H⁆ = N := by
  refine le_antisymm hHN ?_
  calc N = ⁅N, N⁆ := by
        rw [← Subgroup.map_subtype_commutator, hN, ← MonoidHom.range_eq_map,
          Subgroup.range_subtype]
    _ ≤ ⁅H, H⁆ := Subgroup.commutator_mono hNH hNH

end Derived

section Transfer

variable {β : (ι → K) →ₗ[K] (ι → K) →ₛₗ[σ] K} {U W : Submodule K (ι → K)}

theorem isQuasisimple_blkI_of_le (hUW : IsCompl U W)
    (horth : ∀ u ∈ U, ∀ w ∈ W, β u w = 0 ∧ β w u = 0) {N : Subgroup (U ≃ₗ[K] U)}
    (hHN : ⁅isomU β U, isomU β U⁆ ≤ N) (hNH : N ≤ isomU β U) (hN : CFSG.Open.IsQuasisimple N) :
    CFSG.Open.IsQuasisimple (blkI β U W) :=
  CFSG.Open.IsQuasisimple.of_mulEquiv
    ((blkIEquiv hUW horth).trans (MulEquiv.subgroupCongr (commutator_eq_of_perfect hHN hNH hN.1)))
    hN

theorem dvd_card_blkI_of_mem (hUW : IsCompl U W)
    (horth : ∀ u ∈ U, ∀ w ∈ W, β u w = 0 ∧ β w u = 0) {p : ℕ} {y : U ≃ₗ[K] U}
    (hy : y ∈ ⁅isomU β U, isomU β U⁆) (hyp : orderOf y = p) : p ∣ Nat.card (blkI β U W) := by
  have h := orderOf_dvd_natCard ((blkIEquiv hUW horth).symm ⟨y, hy⟩)
  rwa [MulEquiv.orderOf_eq, Subgroup.orderOf_mk, hyp] at h

theorem orderOf_blkSubEquiv (hUW : IsCompl U W)
    (horth : ∀ u ∈ U, ∀ w ∈ W, β u w = 0 ∧ β w u = 0) {x : GL ι K} (hx : x ∈ blkSub β U W) :
    orderOf ((blkSubEquiv hUW horth ⟨x, hx⟩ : isomU β U) : U ≃ₗ[K] U) = orderOf x := by
  rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq, Subgroup.orderOf_mk]

omit [DecidableEq ι] in
theorem commutator_le_ker_det (H : Subgroup (U ≃ₗ[K] U)) :
    ⁅H, H⁆ ≤ (LinearEquiv.det : (U ≃ₗ[K] U) →* Kˣ).ker := by
  rw [Subgroup.commutator_le]
  intro a _ b _
  rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
  exact mul_comm _ _

end Transfer

section Toral

variable {n : ℕ}

@[expose] noncomputable def torHom (i j : Fin n) : Kˣ →* GL (Fin n) K :=
  (Units.map (Matrix.diagonalRingHom (Fin n) K).toMonoidHom).comp
    (MulEquiv.piUnits.symm.toMonoidHom.comp
      (MonoidHom.mulSingle (fun _ => Kˣ) i *
        (MonoidHom.mulSingle (fun _ => Kˣ) j).comp invMonoidHom))

theorem torHom_val (i j : Fin n) (ζ : Kˣ) :
    (torHom i j ζ : Matrix (Fin n) (Fin n) K) =
      Matrix.diagonal fun k =>
        (((Pi.mulSingle i ζ : Fin n → Kˣ) k * (Pi.mulSingle j ζ⁻¹ : Fin n → Kˣ) k : Kˣ) : K) :=
  rfl

theorem det_torHom (i j : Fin n) (ζ : Kˣ) : (torHom i j ζ : Matrix (Fin n) (Fin n) K).det = 1 := by
  rw [torHom_val, Matrix.det_diagonal, ← Units.coe_prod, Finset.prod_mul_distrib,
    Finset.prod_pi_mulSingle', Finset.prod_pi_mulSingle']
  simp

theorem torHom_ne_one {i j : Fin n} (hij : i ≠ j) {ζ : Kˣ} (hζ : ζ ≠ 1) : torHom i j ζ ≠ 1 := by
  intro h
  have h1 := congrArg (fun A : GL (Fin n) K => (A : Matrix (Fin n) (Fin n) K) i i) h
  simp only [torHom_val, Matrix.diagonal_apply_eq, Units.val_one, Matrix.one_apply_eq,
    Pi.mulSingle_eq_same, Pi.mulSingle_eq_of_ne hij, mul_one] at h1
  exact hζ (Units.ext h1)

theorem orderOf_torHom {i j : Fin n} (hij : i ≠ j) {p : ℕ} (hp : p.Prime) {ζ : Kˣ}
    (hζ : orderOf ζ = p) : orderOf (torHom i j ζ) = p := by
  have hd : orderOf (torHom i j ζ) ∣ p := hζ ▸ orderOf_map_dvd _ ζ
  rcases hp.eq_one_or_self_of_dvd _ hd with h1 | h1
  · refine absurd (orderOf_eq_one_iff.1 h1) (torHom_ne_one hij fun h => ?_)
    rw [h, orderOf_one] at hζ
    exact hp.one_lt.ne hζ
  · exact h1

private theorem det_basisMatrixEquiv_symm {V : Type*} [AddCommGroup V] [Module K V]
    (b : Basis (Fin n) K V) (A : GL (Fin n) K) :
    (LinearEquiv.det ((CatalogueBAlternatingIsometry.basisMatrixEquiv b).symm A) : K) =
      (A : Matrix (Fin n) (Fin n) K).det := by
  rw [LinearEquiv.coe_det, ← LinearMap.det_toMatrix b,
    ← CatalogueBAlternatingIsometry.basisMatrixEquiv_val, MulEquiv.apply_symm_apply]

end Toral

section Linear

theorem isomU_zero (U : Submodule K (ι → K)) :
    isomU (0 : (ι → K) →ₗ[K] (ι → K) →ₛₗ[σ] K) U = ⊤ :=
  eq_top_iff.2 fun _ _ _ _ => rfl

@[expose] noncomputable def slEquivKerDet (U : Submodule K (ι → K)) :
    SpecialLinearGroup K U ≃* (LinearEquiv.det : (U ≃ₗ[K] U) →* Kˣ).ker where
  toFun g := ⟨g.1, g.2⟩
  invFun g := ⟨g.1, g.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

theorem isQuasisimple_ker_det [Finite K] (U : Submodule K (ι → K))
    (hdim : 3 ≤ finrank K U ∨ (finrank K U = 2 ∧ 4 ≤ Nat.card K)) :
    CFSG.Open.IsQuasisimple (LinearEquiv.det : (U ≃ₗ[K] U) →* Kˣ).ker := by
  have hq : CFSG.IsQuasisimple (SpecialLinearGroup K U) := by
    rcases hdim with h3 | ⟨h2, h4⟩
    · exact Y10F.LinEngine.isQuasisimple_specialLinearGroup_of_three_le (finBasis K U) h3
    · exact Y10F.LinEngine.isQuasisimple_specialLinearGroup_of_two
        (finBasisOfFinrankEq K U h2) h4
  exact CFSG.Open.IsQuasisimple.of_mulEquiv (slEquivKerDet U).symm
    ⟨Group.isPerfect_def.1 hq.1, hq.2.1⟩

theorem commutator_isomU_zero [Finite K] (U : Submodule K (ι → K))
    (hdim : 3 ≤ finrank K U ∨ (finrank K U = 2 ∧ 4 ≤ Nat.card K)) :
    ⁅isomU (0 : (ι → K) →ₗ[K] (ι → K) →ₛₗ[σ] K) U,
        isomU (0 : (ι → K) →ₗ[K] (ι → K) →ₛₗ[σ] K) U⁆ =
      (LinearEquiv.det : (U ≃ₗ[K] U) →* Kˣ).ker :=
  commutator_eq_of_perfect (commutator_le_ker_det _) (by rw [isomU_zero]; exact le_top)
    (isQuasisimple_ker_det U hdim).1

theorem isQuasisimple_blkI_zero [Finite K] {U W : Submodule K (ι → K)} (hUW : IsCompl U W)
    (hdim : 3 ≤ finrank K U ∨ (finrank K U = 2 ∧ 4 ≤ Nat.card K)) :
    CFSG.Open.IsQuasisimple (blkI (0 : (ι → K) →ₗ[K] (ι → K) →ₛₗ[σ] K) U W) :=
  isQuasisimple_blkI_of_le hUW (fun _ _ _ _ => ⟨rfl, rfl⟩) (commutator_le_ker_det _)
    (by rw [isomU_zero]; exact le_top) (isQuasisimple_ker_det U hdim)

theorem dvd_card_blkI_zero [Finite K] {U W : Submodule K (ι → K)} (hUW : IsCompl U W)
    (hdim : 3 ≤ finrank K U ∨ (finrank K U = 2 ∧ 4 ≤ Nat.card K)) {p : ℕ} (hp : p.Prime)
    {x : GL ι K} (hx : x ∈ blkSub (0 : (ι → K) →ₗ[K] (ι → K) →ₛₗ[σ] K) U W)
    (hxp : orderOf x = p) :
    p ∣ Nat.card (blkI (0 : (ι → K) →ₗ[K] (ι → K) →ₛₗ[σ] K) U W) := by
  haveI := Fact.mk hp
  have horth : ∀ u ∈ U, ∀ w ∈ W, (0 : (ι → K) →ₗ[K] (ι → K) →ₛₗ[σ] K) u w = 0 ∧
      (0 : (ι → K) →ₗ[K] (ι → K) →ₛₗ[σ] K) w u = 0 := fun _ _ _ _ => ⟨rfl, rfl⟩
  have heq := commutator_isomU_zero (σ := σ) U hdim
  have hyp := (orderOf_blkSubEquiv hUW horth hx).trans hxp
  set y := ((blkSubEquiv hUW horth ⟨x, hx⟩ : isomU _ U) : U ≃ₗ[K] U)
  by_cases hζ : LinearEquiv.det y = 1
  · exact dvd_card_blkI_of_mem hUW horth (heq ▸ MonoidHom.mem_ker.2 hζ) hyp
  · have hζp : LinearEquiv.det y ^ p = 1 := by
      rw [← map_pow, ← hyp, pow_orderOf_eq_one, map_one]
    have hord : orderOf (LinearEquiv.det y) = p := orderOf_eq_prime hζp hζ
    have h2 : 2 ≤ finrank K U := by omega
    let i₀ : Fin (finrank K U) := ⟨0, by omega⟩
    let i₁ : Fin (finrank K U) := ⟨1, by omega⟩
    have hi : i₀ ≠ i₁ := Fin.ne_of_val_ne zero_ne_one
    let e := CatalogueBAlternatingIsometry.basisMatrixEquiv (finBasis K U)
    have ht : e.symm (torHom i₀ i₁ (LinearEquiv.det y)) ∈
        (LinearEquiv.det : (U ≃ₗ[K] U) →* Kˣ).ker := by
      rw [MonoidHom.mem_ker]
      exact Units.ext (by rw [det_basisMatrixEquiv_symm, det_torHom, Units.val_one])
    refine dvd_card_blkI_of_mem hUW horth (heq ▸ ht) ?_
    rw [MulEquiv.orderOf_eq, orderOf_torHom hi hp hord]

end Linear

section Symplectic

@[expose] noncomputable def resBilin (J : Matrix ι ι K) (U : Submodule K (ι → K)) :
    LinearMap.BilinForm K U :=
  (Matrix.toBilin' J).compl₁₂ U.subtype U.subtype

theorem isomU_toBilin'_eq (J : Matrix ι ι K) (U : Submodule K (ι → K)) :
    isomU (Matrix.toBilin' J) U = TauCeti.BilinForm.isometryGroup (resBilin J U) := by
  ext g
  rw [mem_isomU, CatalogueBAlternatingIsometry.mem_isometryGroup_iff]
  rfl

theorem toBilin'_formJ_self {r : ℕ} (x : Fin r ⊕ Fin r → K) :
    Matrix.toBilin' (Matrix.fromBlocks 0 1 (-1) 0 :
      Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) x x = 0 := by
  rw [Matrix.toBilin'_apply', Matrix.fromBlocks_mulVec]
  simp only [dotProduct, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, Matrix.zero_mulVec,
    Matrix.one_mulVec, Matrix.neg_mulVec, zero_add, add_zero, Pi.neg_apply, Function.comp_apply,
    mul_neg, Finset.sum_neg_distrib]
  rw [← sub_eq_add_neg, sub_eq_zero]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

theorem resBilin_isAlt {J : Matrix ι ι K} (hJ : ∀ x, Matrix.toBilin' J x x = 0)
    (U : Submodule K (ι → K)) : (resBilin J U).IsAlt :=
  fun x => hJ x

theorem resBilin_nondegenerate {J : Matrix ι ι K} (hJ : ∀ x, Matrix.toBilin' J x x = 0)
    {U : Submodule K (ι → K)} (hnd : ∀ u ∈ U, (∀ u' ∈ U, Matrix.toBilin' J u u' = 0) → u = 0) :
    (resBilin J U).Nondegenerate := by
  have hJ' : (Matrix.toBilin' J).IsAlt := hJ
  refine ⟨fun x hx => Subtype.ext (hnd x x.2 fun u' hu' => hx ⟨u', hu'⟩),
    fun y hy => Subtype.ext (hnd y y.2 fun u' hu' => ?_)⟩
  have h := hy ⟨u', hu'⟩
  change Matrix.toBilin' J u' y = 0 at h
  rw [← LinearMap.IsAlt.neg hJ' u' y, h, neg_zero]

theorem isQuasisimple_isomU_toBilin' [Finite K] (hodd : Odd (Nat.card K)) {J : Matrix ι ι K}
    (hJ : ∀ x, Matrix.toBilin' J x x = 0) {U : Submodule K (ι → K)}
    (hnd : ∀ u ∈ U, (∀ u' ∈ U, Matrix.toBilin' J u u' = 0) → u = 0)
    (hdim : 2 ≤ finrank K U) (hexc : finrank K U ≠ 2 ∨ Nat.card K ≠ 3) :
    CFSG.Open.IsQuasisimple (isomU (Matrix.toBilin' J) U) := by
  have hq := CatalogueBAlternatingIsometry.isometry_quasisimple (resBilin J U)
    (resBilin_isAlt hJ U) (resBilin_nondegenerate hJ hnd) hdim hodd hexc
  exact CFSG.Open.IsQuasisimple.of_mulEquiv (MulEquiv.subgroupCongr (isomU_toBilin'_eq J U))
    ⟨Group.isPerfect_def.1 hq.1, hq.2.1⟩

theorem isQuasisimple_blkI_toBilin' [Finite K] (hodd : Odd (Nat.card K)) {J : Matrix ι ι K}
    (hJ : ∀ x, Matrix.toBilin' J x x = 0) {U W : Submodule K (ι → K)} (hUW : IsCompl U W)
    (horth : ∀ u ∈ U, ∀ w ∈ W, Matrix.toBilin' J u w = 0 ∧ Matrix.toBilin' J w u = 0)
    (hnd : ∀ u ∈ U, (∀ u' ∈ U, Matrix.toBilin' J u u' = 0) → u = 0)
    (hdim : 2 ≤ finrank K U) (hexc : finrank K U ≠ 2 ∨ Nat.card K ≠ 3) :
    CFSG.Open.IsQuasisimple (blkI (Matrix.toBilin' J) U W) :=
  isQuasisimple_blkI_of_le hUW horth (Subgroup.commutator_le_self _) le_rfl
    (isQuasisimple_isomU_toBilin' hodd hJ hnd hdim hexc)

theorem dvd_card_blkI_toBilin' [Finite K] (hodd : Odd (Nat.card K)) {J : Matrix ι ι K}
    (hJ : ∀ x, Matrix.toBilin' J x x = 0) {U W : Submodule K (ι → K)} (hUW : IsCompl U W)
    (horth : ∀ u ∈ U, ∀ w ∈ W, Matrix.toBilin' J u w = 0 ∧ Matrix.toBilin' J w u = 0)
    (hnd : ∀ u ∈ U, (∀ u' ∈ U, Matrix.toBilin' J u u' = 0) → u = 0)
    (hdim : 2 ≤ finrank K U) (hexc : finrank K U ≠ 2 ∨ Nat.card K ≠ 3) {p : ℕ} {x : GL ι K}
    (hx : x ∈ blkSub (Matrix.toBilin' J) U W) (hxp : orderOf x = p) :
    p ∣ Nat.card (blkI (Matrix.toBilin' J) U W) := by
  have heq := commutator_eq_of_perfect (Subgroup.commutator_le_self _) le_rfl
    (isQuasisimple_isomU_toBilin' hodd hJ hnd hdim hexc).1
  have key : ∀ y ∈ isomU (Matrix.toBilin' J) U,
      y ∈ ⁅isomU (Matrix.toBilin' J) U, isomU (Matrix.toBilin' J) U⁆ := fun y hy => by
    rw [heq]
    exact hy
  exact dvd_card_blkI_of_mem hUW horth (key _ (blkSubEquiv hUW horth ⟨x, hx⟩).2)
    ((orderOf_blkSubEquiv hUW horth hx).trans hxp)

end Symplectic

section Orthogonal

theorem polar_comp_subtype (Q : QuadraticForm K (ι → K)) (U : Submodule K (ι → K)) (x y : U) :
    QuadraticMap.polar (Q.comp U.subtype) x y = QuadraticMap.polar Q x y := by
  simp only [QuadraticMap.polar, QuadraticMap.comp_apply, Submodule.subtype_apply,
    Submodule.coe_add]

theorem isomU_polarBilin_eq (h2 : (2 : K) ≠ 0) (Q : QuadraticForm K (ι → K))
    (U : Submodule K (ι → K)) :
    isomU (QuadraticMap.polarBilin Q) U =
      TauCeti.QuadraticMap.orthogonalGroup (Q.comp U.subtype) := by
  ext g
  rw [mem_isomU, TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
  constructor
  · intro hg m
    have h := hg m m
    simp only [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_self] at h
    have h' : (2 : K) * Q (g m : ι → K) = 2 * Q (m : ι → K) := by
      simpa [two_mul] using h
    exact mul_left_cancel₀ h2 h'
  · intro hg x y
    rw [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polarBilin_apply_apply,
      ← polar_comp_subtype, ← polar_comp_subtype]
    simp only [QuadraticMap.polar]
    rw [← map_add g x y, hg, hg, hg]

theorem polarBilin_comp_nondegenerate (Q : QuadraticForm K (ι → K)) {U : Submodule K (ι → K)}
    (hnd : ∀ u ∈ U, (∀ u' ∈ U, QuadraticMap.polarBilin Q u u' = 0) → u = 0) :
    (Q.comp U.subtype).polarBilin.Nondegenerate := by
  refine ⟨fun x hx => Subtype.ext (hnd x x.2 fun u' hu' => ?_),
    fun y hy => Subtype.ext (hnd y y.2 fun u' hu' => ?_)⟩
  · have h := hx ⟨u', hu'⟩
    rwa [QuadraticMap.polarBilin_apply_apply, polar_comp_subtype] at h
  · have h := hy ⟨u', hu'⟩
    rwa [QuadraticMap.polarBilin_apply_apply, polar_comp_subtype, QuadraticMap.polar_comm] at h

theorem isQuasisimple_commutator_orthogonalGroup [Finite K] (hodd : Odd (Nat.card K))
    (Q : QuadraticForm K (ι → K)) {U : Submodule K (ι → K)}
    (hnd : ∀ u ∈ U, (∀ u' ∈ U, QuadraticMap.polarBilin Q u u' = 0) → u = 0)
    (hdim : 5 ≤ finrank K U ∨ (finrank K U = 4 ∧
      ∀ S : Submodule K (ι → K), S ≤ U → finrank K S = 2 → ∃ x ∈ S, Q x ≠ 0)) :
    CFSG.Open.IsQuasisimple
      (commutator (TauCeti.QuadraticMap.orthogonalGroup (Q.comp U.subtype))) := by
  have hQ := polarBilin_comp_nondegenerate Q hnd
  suffices hq : CFSG.IsQuasisimple
      (commutator (TauCeti.QuadraticMap.orthogonalGroup (Q.comp U.subtype))) from
    ⟨Group.isPerfect_def.1 hq.1, hq.2.1⟩
  rcases hdim with h5 | ⟨h4, hts⟩
  · exact OddSelector.commutator_orthogonalGroup_quasisimple hodd _ hQ h5
  · have hns : ¬ ∃ S : Submodule K U, finrank K S = 2 ∧ ∀ x ∈ S, (Q.comp U.subtype) x = 0 := by
      rintro ⟨S, hS2, hSQ⟩
      obtain ⟨x, hx, hQx⟩ := hts (S.map U.subtype) (Submodule.map_subtype_le U S)
        (by rw [Submodule.finrank_map_subtype_eq]; exact hS2)
      obtain ⟨y, hy, rfl⟩ := hx
      exact hQx (hSQ y hy)
    obtain ⟨-, -, -, -, h4', -, -⟩ :=
      ComponentInitial.orthogonal_low_dimensional_fixed_derived_component_coverage
        (Q.comp U.subtype) hQ (Or.inl ⟨hodd, Or.inr (Or.inl h4)⟩)
    obtain ⟨-, -, -, -, -, -, -, -, hq⟩ := h4' hodd h4 hns
    exact hq

theorem isQuasisimple_blkI_polarBilin [Finite K] (hodd : Odd (Nat.card K))
    (Q : QuadraticForm K (ι → K)) {U W : Submodule K (ι → K)} (hUW : IsCompl U W)
    (horth : ∀ u ∈ U, ∀ w ∈ W,
      QuadraticMap.polarBilin Q u w = 0 ∧ QuadraticMap.polarBilin Q w u = 0)
    (hnd : ∀ u ∈ U, (∀ u' ∈ U, QuadraticMap.polarBilin Q u u' = 0) → u = 0)
    (hdim : 5 ≤ finrank K U ∨ (finrank K U = 4 ∧
      ∀ S : Submodule K (ι → K), S ≤ U → finrank K S = 2 → ∃ x ∈ S, Q x ≠ 0)) :
    CFSG.Open.IsQuasisimple (blkI (QuadraticMap.polarBilin Q) U W) := by
  have hO := isomU_polarBilin_eq (CatalogueBOddQuadratic.two_ne_zero_of_odd_card hodd) Q U
  have heq : ⁅isomU (QuadraticMap.polarBilin Q) U, isomU (QuadraticMap.polarBilin Q) U⁆ =
      ⁅TauCeti.QuadraticMap.orthogonalGroup (Q.comp U.subtype),
        TauCeti.QuadraticMap.orthogonalGroup (Q.comp U.subtype)⁆ := by
    rw [hO]
  have hq := isQuasisimple_commutator_orthogonalGroup hodd Q hnd hdim
  exact CFSG.Open.IsQuasisimple.of_mulEquiv ((blkIEquiv hUW horth).trans
    ((MulEquiv.subgroupCongr heq).trans
      ((MulEquiv.subgroupCongr (Subgroup.map_subtype_commutator _).symm).trans
        (Subgroup.equivMapOfInjective _ _ (Subgroup.subtype_injective _)).symm))) hq

theorem dvd_card_blkI_polarBilin [Finite K] (hodd : Odd (Nat.card K))
    (Q : QuadraticForm K (ι → K)) {U W : Submodule K (ι → K)} (hUW : IsCompl U W)
    (horth : ∀ u ∈ U, ∀ w ∈ W,
      QuadraticMap.polarBilin Q u w = 0 ∧ QuadraticMap.polarBilin Q w u = 0)
    (hnd : ∀ u ∈ U, (∀ u' ∈ U, QuadraticMap.polarBilin Q u u' = 0) → u = 0) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) {x : GL ι K} (hx : x ∈ blkSub (QuadraticMap.polarBilin Q) U W)
    (hxp : orderOf x = p) : p ∣ Nat.card (blkI (QuadraticMap.polarBilin Q) U W) := by
  have hO := isomU_polarBilin_eq (CatalogueBOddQuadratic.two_ne_zero_of_odd_card hodd) Q U
  have hyp := (orderOf_blkSubEquiv hUW horth hx).trans hxp
  have key : ∀ y ∈ isomU (QuadraticMap.polarBilin Q) U, orderOf y = p →
      y ∈ ⁅isomU (QuadraticMap.polarBilin Q) U, isomU (QuadraticMap.polarBilin Q) U⁆ := by
    intro y hy hyp
    rw [hO] at hy ⊢
    exact HarrisLit.L33.OC.mem_omega_of_odd (CatalogueBOddQuadratic.char_ne_two_of_odd_card hodd)
      (polarBilin_comp_nondegenerate Q hnd) hy (hyp ▸ hp.odd_of_ne_two hp2)
  exact dvd_card_blkI_of_mem hUW horth (key _ (blkSubEquiv hUW horth ⟨x, hx⟩).2 hyp) hyp

end Orthogonal

section Unitary

theorem unitForm_swap (hσσ : ∀ c, σ (σ c) = c) (x y : ι → K) :
    σ (unitForm σ x y) = unitForm σ y x := by
  simp only [unitForm_apply, dotProduct, Function.comp_apply, map_sum, map_mul, hσσ]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

@[expose] noncomputable def unitFormU (τ : K →+* K) (hτ : ∀ c, τ c = σ c)
    (U : Submodule K (ι → K)) : U →ₛₗ[τ] U →ₗ[K] K :=
  LinearMap.mk₂'ₛₗ τ (RingHom.id K) (fun x y => unitForm σ (y : ι → K) (x : ι → K))
    (fun x x' y => by rw [Submodule.coe_add, map_add])
    (fun c x y => by rw [Submodule.coe_smul, map_smulₛₗ, hτ])
    (fun x y y' => by rw [Submodule.coe_add, map_add, LinearMap.add_apply])
    (fun c x y => by rw [Submodule.coe_smul, map_smul, LinearMap.smul_apply, RingHom.id_apply])

theorem unitFormU_apply (τ : K →+* K) (hτ : ∀ c, τ c = σ c) (U : Submodule K (ι → K))
    (x y : U) : unitFormU τ hτ U x y = unitForm σ (y : ι → K) (x : ι → K) :=
  rfl

theorem unitFormU_isSymm (τ : K →+* K) (hτ : ∀ c, τ c = σ c) (hσσ : ∀ c, σ (σ c) = c)
    (U : Submodule K (ι → K)) : (unitFormU τ hτ U).IsSymm :=
  ⟨fun x y => by rw [unitFormU_apply, unitFormU_apply, hτ, unitForm_swap hσσ]⟩

theorem unitFormU_nondegenerate (τ : K →+* K) (hτ : ∀ c, τ c = σ c)
    (hσσ : ∀ c, σ (σ c) = c) {U : Submodule K (ι → K)}
    (hnd : ∀ u ∈ U, (∀ u' ∈ U, unitForm σ u u' = 0) → u = 0) :
    (unitFormU τ hτ U).Nondegenerate := by
  refine ⟨fun x hx => Subtype.ext (hnd x x.2 fun u' hu' => ?_),
    fun y hy => Subtype.ext (hnd y y.2 fun u' hu' => hy ⟨u', hu'⟩)⟩
  rw [← unitForm_swap hσσ u' (x : ι → K)]
  exact (congrArg σ (hx ⟨u', hu'⟩)).trans (map_zero σ)

private theorem isomU_unitForm_eq (τ : K ≃+* K) (hτ : ∀ c, τ.toRingHom c = σ c)
    (U : Submodule K (ι → K)) :
    isomU (unitForm σ) U =
      CatalogueBUnitaryIsometry.isometryGroup (unitFormU τ.toRingHom hτ U) := by
  ext g
  rw [mem_isomU, CatalogueBUnitaryIsometry.mem_isometryGroup_iff]
  exact ⟨fun hg x y => hg y x, fun hg x y => hg y x⟩

private theorem det_conjTr (τ : K ≃+* K) {n : ℕ} (M : Matrix (Fin n) (Fin n) K) :
    (CFSG.LieType.Universal.Unitary.conjTr τ M).det = τ M.det := by
  rw [CFSG.LieType.Universal.Unitary.conjTr, Matrix.det_transpose, RingEquiv.map_det]
  rfl

private theorem torHom_mem_Uid (τ : K ≃+* K) {n : ℕ} (i j : Fin n) {ζ : Kˣ}
    (hζ : τ (ζ : K) * ζ = 1) : torHom i j ζ ∈ CatalogueBUnitaryIsometry.Uid τ n := by
  have h1 : ∀ u : Kˣ, τ (u : K) * u = 1 → ∀ (l k : Fin n),
      τ ((Pi.mulSingle l u : Fin n → Kˣ) k : K) * ((Pi.mulSingle l u : Fin n → Kˣ) k : K) = 1 := by
    intro u hu l k
    by_cases hk : k = l
    · subst hk
      simpa using hu
    · simp [Pi.mulSingle_eq_of_ne hk]
  have hinv : τ ((ζ⁻¹ : Kˣ) : K) * ((ζ⁻¹ : Kˣ) : K) = 1 := by
    rw [Units.val_inv_eq_inv_val, map_inv₀, ← mul_inv, hζ, inv_one]
  rw [CatalogueBUnitaryIsometry.mem_Uid_iff, torHom_val, CFSG.LieType.Universal.Unitary.conjTr,
    Matrix.diagonal_map (map_zero τ), Matrix.diagonal_transpose, Matrix.diagonal_mul_diagonal,
    ← Matrix.diagonal_one]
  congr 1
  funext k
  simp only [Units.val_mul, map_mul]
  rw [mul_mul_mul_comm, h1 ζ hζ i k, h1 ζ⁻¹ hinv j k, one_mul]

theorem isQuasisimple_isomU_inf_ker_det {r f : ℕ}
    (hK : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData r f K) (hr : r ≠ 2)
    {U : Submodule K (ι → K)} (hnd : ∀ u ∈ U, (∀ u' ∈ U, unitForm hK.bar u u' = 0) → u = 0)
    (hdim : 3 ≤ finrank K U ∨ (finrank K U = 2 ∧ r ^ f ≠ 3)) :
    CFSG.Open.IsQuasisimple
      ↥(isomU (unitForm hK.bar) U ⊓ (LinearEquiv.det : (U ≃ₗ[K] U) →* Kˣ).ker) := by
  haveI : Fact r.Prime := ⟨hK.prime⟩
  haveI : Finite K := hK.finite
  have hE : Nat.card K = (r ^ f) ^ 2 := by rw [hK.card, ← pow_mul, mul_comm]
  let τ := CatalogueBUnitaryTwo.unitaryFieldConjugation r f hE
  have hτ : ∀ c, τ.toRingHom c = hK.bar c := fun c => by
    show τ c = hK.bar c
    rw [CatalogueBUnitaryTwo.unitaryFieldConjugation_apply,
      CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData.bar_apply]
  have hsym := unitFormU_isSymm τ.toRingHom hτ hK.bar_bar U
  have hnd' := unitFormU_nondegenerate τ.toRingHom hτ hK.bar_bar hnd
  have hnq : (finrank K U, r ^ f) ≠ (2, 3) := by
    intro h
    have h1 : finrank K U = 2 := congrArg Prod.fst h
    have h2 : r ^ f = 3 := congrArg Prod.snd h
    rcases hdim with h3 | ⟨-, h3⟩
    · omega
    · exact h3 h2
  obtain ⟨-, -, hcase⟩ := CatalogueBUnitaryTwo.odd_unitary_all_dimensional_isometry_p_components
    r f hr hK.one_le hE (unitFormU τ.toRingHom hτ U) hsym hnd' (by omega)
  have hq := (hcase ⟨by omega, hnq⟩).1
  have hH := isomU_unitForm_eq τ hτ U
  have hmap : (CatalogueBUnitaryIsometry.specialIsometry (unitFormU τ.toRingHom hτ U)).map
      (CatalogueBUnitaryIsometry.isometryGroup (unitFormU τ.toRingHom hτ U)).subtype =
      isomU (unitForm hK.bar) U ⊓ (LinearEquiv.det : (U ≃ₗ[K] U) →* Kˣ).ker := by
    rw [hH]
    ext g
    constructor
    · rintro ⟨s, hs, rfl⟩
      exact ⟨s.2, hs⟩
    · rintro ⟨hg, hdet⟩
      exact ⟨⟨g, hg⟩, hdet, rfl⟩
  exact CFSG.Open.IsQuasisimple.of_mulEquiv ((MulEquiv.subgroupCongr hmap.symm).trans
    (Subgroup.equivMapOfInjective _ _ (Subgroup.subtype_injective _)).symm)
    ⟨Group.isPerfect_def.1 hq.1, hq.2.1⟩

theorem commutator_isomU_unitForm {r f : ℕ}
    (hK : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData r f K) (hr : r ≠ 2)
    {U : Submodule K (ι → K)} (hnd : ∀ u ∈ U, (∀ u' ∈ U, unitForm hK.bar u u' = 0) → u = 0)
    (hdim : 3 ≤ finrank K U ∨ (finrank K U = 2 ∧ r ^ f ≠ 3)) :
    ⁅isomU (unitForm hK.bar) U, isomU (unitForm hK.bar) U⁆ =
      isomU (unitForm hK.bar) U ⊓ (LinearEquiv.det : (U ≃ₗ[K] U) →* Kˣ).ker :=
  commutator_eq_of_perfect (le_inf (Subgroup.commutator_le_self _) (commutator_le_ker_det _))
    inf_le_left (isQuasisimple_isomU_inf_ker_det hK hr hnd hdim).1

theorem isQuasisimple_blkI_unitForm {r f : ℕ}
    (hK : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData r f K) (hr : r ≠ 2)
    {U W : Submodule K (ι → K)} (hUW : IsCompl U W)
    (horth : ∀ u ∈ U, ∀ w ∈ W, unitForm hK.bar u w = 0 ∧ unitForm hK.bar w u = 0)
    (hnd : ∀ u ∈ U, (∀ u' ∈ U, unitForm hK.bar u u' = 0) → u = 0)
    (hdim : 3 ≤ finrank K U ∨ (finrank K U = 2 ∧ r ^ f ≠ 3)) :
    CFSG.Open.IsQuasisimple (blkI (unitForm hK.bar) U W) :=
  isQuasisimple_blkI_of_le hUW horth
    (le_inf (Subgroup.commutator_le_self _) (commutator_le_ker_det _)) inf_le_left
    (isQuasisimple_isomU_inf_ker_det hK hr hnd hdim)

theorem dvd_card_blkI_unitForm {r f : ℕ}
    (hK : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData r f K) (hr : r ≠ 2)
    {U W : Submodule K (ι → K)} (hUW : IsCompl U W)
    (horth : ∀ u ∈ U, ∀ w ∈ W, unitForm hK.bar u w = 0 ∧ unitForm hK.bar w u = 0)
    (hnd : ∀ u ∈ U, (∀ u' ∈ U, unitForm hK.bar u u' = 0) → u = 0)
    (hdim : 3 ≤ finrank K U ∨ (finrank K U = 2 ∧ r ^ f ≠ 3)) {p : ℕ} (hp : p.Prime)
    {x : GL ι K} (hx : x ∈ blkSub (unitForm hK.bar) U W) (hxp : orderOf x = p) :
    p ∣ Nat.card (blkI (unitForm hK.bar) U W) := by
  haveI := Fact.mk hp
  have heq := commutator_isomU_unitForm hK hr hnd hdim
  have hyp := (orderOf_blkSubEquiv hUW horth hx).trans hxp
  have hyH := (blkSubEquiv hUW horth ⟨x, hx⟩).2
  set y := ((blkSubEquiv hUW horth ⟨x, hx⟩ : isomU _ U) : U ≃ₗ[K] U)
  by_cases hζ : LinearEquiv.det y = 1
  · exact dvd_card_blkI_of_mem hUW horth (heq ▸ Subgroup.mem_inf.2 ⟨hyH, MonoidHom.mem_ker.2 hζ⟩)
      hyp
  have hζp : LinearEquiv.det y ^ p = 1 := by
    rw [← map_pow, ← hyp, pow_orderOf_eq_one, map_one]
  have hord : orderOf (LinearEquiv.det y) = p := orderOf_eq_prime hζp hζ
  haveI : Fact r.Prime := ⟨hK.prime⟩
  haveI : Finite K := hK.finite
  have hE : Nat.card K = (r ^ f) ^ 2 := by rw [hK.card, ← pow_mul, mul_comm]
  let τ := CatalogueBUnitaryTwo.unitaryFieldConjugation r f hE
  have hτ : ∀ c, τ.toRingHom c = hK.bar c := fun c => by
    show τ c = hK.bar c
    rw [CatalogueBUnitaryTwo.unitaryFieldConjugation_apply,
      CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData.bar_apply]
  obtain ⟨hsigma, hne, -⟩ := CatalogueBUnitaryTwo.unitaryFieldConjugation_data r f hE
  obtain ⟨b, hb⟩ := CatalogueBHermitian.exists_orthonormal_basis (unitFormU τ.toRingHom hτ U)
    (unitFormU_isSymm τ.toRingHom hτ hK.bar_bar U)
    (unitFormU_nondegenerate τ.toRingHom hτ hK.bar_bar hnd) hsigma hne
  have hH := isomU_unitForm_eq τ hτ U
  let e := CatalogueBAlternatingIsometry.basisMatrixEquiv b
  have hyU : e y ∈ CatalogueBUnitaryIsometry.Uid τ (finrank K U) :=
    (CatalogueBUnitaryIsometry.isometry_iff_Uid _ b hb y).1 (hH ▸ hyH)
  have hnorm : τ (LinearEquiv.det y : K) * (LinearEquiv.det y : K) = 1 := by
    have h1 := congrArg Matrix.det ((CatalogueBUnitaryIsometry.mem_Uid_iff τ _ _).1 hyU)
    rw [Matrix.det_mul, det_conjTr, Matrix.det_one,
      CatalogueBAlternatingIsometry.basisMatrixEquiv_val, LinearMap.det_toMatrix,
      ← LinearEquiv.coe_det] at h1
    exact h1
  have h2 : 2 ≤ finrank K U := by omega
  let i₀ : Fin (finrank K U) := ⟨0, by omega⟩
  let i₁ : Fin (finrank K U) := ⟨1, by omega⟩
  have hi : i₀ ≠ i₁ := Fin.ne_of_val_ne zero_ne_one
  have htH : e.symm (torHom i₀ i₁ (LinearEquiv.det y)) ∈ isomU (unitForm hK.bar) U := by
    rw [hH, CatalogueBUnitaryIsometry.isometry_iff_Uid _ b hb, MulEquiv.apply_symm_apply]
    exact torHom_mem_Uid τ i₀ i₁ hnorm
  have htdet : e.symm (torHom i₀ i₁ (LinearEquiv.det y)) ∈
      (LinearEquiv.det : (U ≃ₗ[K] U) →* Kˣ).ker := by
    rw [MonoidHom.mem_ker]
    exact Units.ext (by rw [det_basisMatrixEquiv_symm, det_torHom, Units.val_one])
  refine dvd_card_blkI_of_mem hUW horth (heq ▸ Subgroup.mem_inf.2 ⟨htH, htdet⟩) ?_
  rw [MulEquiv.orderOf_eq, orderOf_torHom hi hp hord]

end Unitary

end CFSG.LocalAnalysis.GLTheoremA.S267.Cls

end
