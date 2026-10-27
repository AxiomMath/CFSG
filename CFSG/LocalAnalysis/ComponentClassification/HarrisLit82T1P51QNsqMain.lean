module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P51QNsq
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBProjectiveQuadraticMatrix
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P51QCov
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P51QLin
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P51QTrv
public import CFSG.RankThree.SteinbergR3ECALinearSplitBlocks

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.T1.P51Q

open CFSG Subgroup Matrix CatalogueBProjectiveQuadratic CatalogueBProjectiveInvolution
  CatalogueBProjectiveCoordinates

variable {K : Type} [Field K] {n : ℕ}

theorem evenCent_nonsq [Finite K] (htwo : (2 : K) ≠ 0) (hodd : Odd (Nat.card K))
    {X : Type} [Group X] (π : Matrix.SpecialLinearGroup (Fin n) K →* X)
    (hπ : Function.Surjective π)
    (hker : ∀ s, π s = 1 ↔ s ∈ center (Matrix.SpecialLinearGroup (Fin n) K))
    (a : Matrix.SpecialLinearGroup (Fin n) K) (lam : Kˣ) (hns : ¬ IsSquare lam.val)
    (hsq : Matrix.SpecialLinearGroup.toGL a ^ 2 = GeneralLinearGroup.scalar (Fin n) lam)
    (hn : 3 ≤ n) : EvenCentComm X (π a) ∧ EvenCentInv X (π a) := by
  have : Fact (¬ IsSquare lam.val) := ⟨hns⟩
  set A := Matrix.SpecialLinearGroup.toGL a with hAdef
  set E := extension lam.val
  have : Finite E := Module.finite_of_finite K
  set m := matrixDimension A lam hsq
  have hnm : n = 2 * m := by
    have := matrixDimension_twice A lam hsq
    rwa [Fintype.card_fin] at this
  have hm : 2 ≤ m := by omega
  have h4 : 4 ≤ Nat.card E := by
    rw [card_quadExt lam.val]
    have h2 : 2 ≤ Nat.card K := Finite.one_lt_card
    have h3 : 3 ≤ Nat.card K := by
      obtain ⟨k, hk⟩ := hodd
      omega
    nlinarith
  set e := matrixCentralizerQuadraticEquiv A lam hsq
  let := matrixModule A lam hsq
  set β := (matrixBasis A lam hsq).equivFun
  set N := (Matrix.SpecialLinearGroup.toGL : Matrix.SpecialLinearGroup (Fin m) E →*
    GL (Fin m) E).range with hNdef
  have hNn : N.Normal := by
    rw [hNdef, Matrix.SpecialLinearGroup.range_toGL_eq_ker_det]
    infer_instance
  have hNq : IsQuasisimple N := LocalCores.isQuasisimple_of_mulEquiv
    (MonoidHom.ofInjective Matrix.SpecialLinearGroup.toGL_injective)
    (RankThree.CALinearPlane.isQuasisimple_SL_of_two_le hm h4)
  have : Group.IsPerfect N := hNq.1
  set M := pullSL A e N
  set 𝓜 : Set (Subgroup (Matrix.SpecialLinearGroup (Fin n) K)) := {M} with h𝓜
  have hscal : ∀ g : Matrix.SpecialLinearGroup (Fin n) K, (∀ x ∈ M, g * x = x * g) →
      ∃ c : E, ∀ v, β ((g : Matrix (Fin n) (Fin n) K) *ᵥ v) = c • β v := by
    intro g hg
    let gA : (Fin m → E) →+ (Fin m → E) :=
      { toFun := fun w => β ((g : Matrix (Fin n) (Fin n) K) *ᵥ β.symm w)
        map_zero' := by simp
        map_add' := fun w w' => by rw [map_add, Matrix.mulVec_add, map_add] }
    have hgA : ∀ w, gA w = β ((g : Matrix (Fin n) (Fin n) K) *ᵥ β.symm w) := fun _ => rfl
    have htr : ∀ i j : Fin m, i ≠ j → ∀ (t : E) (w : Fin m → E),
        gA (transvection i j t *ᵥ w) = transvection i j t *ᵥ gA w := by
      intro i j hij t w
      set T : Matrix.SpecialLinearGroup (Fin m) E :=
        ⟨transvection i j t, det_transvection_of_ne i j hij t⟩
      obtain ⟨x, hx, hxA, hxe⟩ := exists_pullSL_eq e N (x := Matrix.SpecialLinearGroup.toGL T)
        ⟨T, rfl⟩
      have hrel : ∀ v, transvection i j t *ᵥ β v = β ((x : Matrix (Fin n) (Fin n) K) *ᵥ v) := by
        intro v
        have h1 := matrixCentralizerQuadraticEquiv_mulVec A lam hsq ⟨_, hxA⟩ v
        rw [hxe] at h1
        exact h1
      have hgx : (g : Matrix (Fin n) (Fin n) K) * x = x * g := congrArg Subtype.val (hg x hx)
      have h1 := hrel (β.symm w)
      rw [LinearEquiv.apply_symm_apply] at h1
      rw [hgA, hgA, h1, LinearEquiv.symm_apply_apply, Matrix.mulVec_mulVec, hgx,
        ← Matrix.mulVec_mulVec, hrel]
    obtain ⟨c, hc⟩ := transvection_commutant hm gA htr
    refine ⟨c, fun v => ?_⟩
    have := hc (β v)
    rw [hgA, LinearEquiv.symm_apply_apply] at this
    exact this
  have hC : ∀ M' ∈ 𝓜, M' ≤ centralizer ({a} : Set (Matrix.SpecialLinearGroup (Fin n) K)) := by
    rintro M' rfl
    exact pullSL_le_centralizer e N rfl
  have hN : ∀ M' ∈ 𝓜, ∀ x ∈ centralizer ({a} : Set (Matrix.SpecialLinearGroup (Fin n) K)),
      ∀ y ∈ M', x * y * x⁻¹ ∈ M' := by
    rintro M' rfl x hx y hy
    exact conj_mem_pullSL e N rfl hx hy
  have hQ : ∀ M' ∈ 𝓜, IsQuasisimple M' := by
    rintro M' rfl
    exact isQuasisimple_pullSL e N hNq
  have hE : ∀ M' ∈ 𝓜, ∃ y ∈ M', π y ≠ 1 ∧ y ^ 4 = 1 := by
    rintro M' rfl
    obtain ⟨ε, hε⟩ := exists_mul_self_eq_neg_one lam.val hodd
    have hεε : ε * -ε = 1 := by rw [mul_neg, hε, neg_neg]
    have hε2 : ε ^ 2 = -1 := by rw [sq, hε]
    have hε4 : ε ^ 4 = 1 := by
      rw [show ε ^ 4 = (ε ^ 2) ^ 2 by ring, hε2]
      norm_num
    have hε4' : (-ε) ^ 4 = 1 := by rw [neg_pow, hε4]; norm_num
    have htwoE : (2 : E) ≠ 0 := by
      have := (map_ne_zero (algebraMap K E)).mpr htwo
      rwa [map_ofNat] at this
    obtain ⟨y, hy, hyc, hy4⟩ := exists_noncentral_pullSL e N (by omega)
      (x := Matrix.SpecialLinearGroup.toGL (diagSL hm ε (-ε) hεε)) ⟨_, rfl⟩
      (by rw [← map_pow, diagSL_pow_four hm hεε hε4 hε4', map_one]) (fun u h hxe => by
        have h1 : (⟨_, h⟩ : centralizer ({A} : Set (GL (Fin n) K))) =
            ordinaryCentralizerScalar A u := Subtype.ext rfl
        rw [h1, matrixCentralizerQuadraticEquiv_scalar] at hxe
        have h00 := congrArg (fun g : GL (Fin m) E => (g : Matrix (Fin m) (Fin m) E)
          ⟨0, by omega⟩ ⟨0, by omega⟩) hxe
        have h11 := congrArg (fun g : GL (Fin m) E => (g : Matrix (Fin m) (Fin m) E)
          ⟨1, by omega⟩ ⟨1, by omega⟩) hxe
        simp only [Matrix.SpecialLinearGroup.coe_GL_coe_matrix, diagSL_apply_zero,
          diagSL_apply_one, GeneralLinearGroup.coe_scalar, scalar_apply, diagonal_apply_eq]
          at h00 h11
        have h2 : (2 : E) * ε = 0 := by linear_combination h00 - h11
        have hε0 : ε = 0 := (mul_eq_zero.mp h2).resolve_left htwoE
        rw [hε0, mul_zero] at hε
        exact one_ne_zero (neg_eq_zero.mp hε.symm))
    exact ⟨y, hy, fun h => hyc ((hker y).mp h), hy4⟩
  have hcomm : ∀ g h : Matrix.SpecialLinearGroup (Fin n) K, (∀ M' ∈ 𝓜, ∀ x ∈ M', g * x = x * g)
      → (∀ M' ∈ 𝓜, ∀ x ∈ M', h * x = x * h) → g * h = h * g := by
    intro g h hg hh
    obtain ⟨c, hgc⟩ := hscal g (hg M rfl)
    obtain ⟨d, hhc⟩ := hscal h (hh M rfl)
    refine Subtype.ext (Matrix.ext_iff_mulVec.mpr fun v => β.injective ?_)
    change β (((g : Matrix (Fin n) (Fin n) K) * (h : Matrix (Fin n) (Fin n) K)) *ᵥ v) =
      β (((h : Matrix (Fin n) (Fin n) K) * (g : Matrix (Fin n) (Fin n) K)) *ᵥ v)
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hgc, hhc, hhc, hgc, smul_smul,
      smul_smul, mul_comm]
  have hinv : ∀ g : Matrix.SpecialLinearGroup (Fin n) K, (∀ M' ∈ 𝓜, ∀ x ∈ M', g * x = x * g) →
      g * g ∈ center (Matrix.SpecialLinearGroup (Fin n) K) →
      g ∈ center (Matrix.SpecialLinearGroup (Fin n) K) ∨
        g * a⁻¹ ∈ center (Matrix.SpecialLinearGroup (Fin n) K) := by
    intro g hg hgg
    obtain ⟨c, hgc⟩ := hscal g (hg M rfl)
    obtain ⟨ρ, -, hρ⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hgg
    have hsmulK : ∀ (k : K) (v : Fin n → K), β (k • v) = algebraMap K E k • β v := by
      intro k v
      rw [← matrixModule_algebraMap_smul A lam hsq k v, map_smul]
    have hcc : c * c = algebraMap K E ρ := by
      have h1 : (g : Matrix (Fin n) (Fin n) K) * g = scalar (Fin n) ρ := by
        rw [hρ]
        rfl
      set v₀ := β.symm (Pi.single ⟨0, by omega⟩ 1)
      have h2 : β ((g : Matrix (Fin n) (Fin n) K) *ᵥ ((g : Matrix (Fin n) (Fin n) K) *ᵥ v₀)) =
          β (ρ • v₀) := by
        rw [Matrix.mulVec_mulVec, h1, scalar_apply, ← smul_one_eq_diagonal, Matrix.smul_mulVec,
          Matrix.one_mulVec]
      rw [hgc, hgc, smul_smul, hsmulK, LinearEquiv.apply_symm_apply] at h2
      have h3 := congrArg (fun w : Fin m → E => w ⟨0, by omega⟩) h2
      simpa using h3
    rcases quadExt_sq_mem lam.val htwo hcc with ⟨x, hx⟩ | ⟨y, hy⟩
    · left
      refine mem_center_of_mulVec_eq_smul (c := x) fun v => β.injective ?_
      rw [hgc, hsmulK, hx]
    · right
      refine mem_center_of_mulVec_eq_smul (c := y) fun v => β.injective ?_
      have hAw : A.val *ᵥ (((a⁻¹ : Matrix.SpecialLinearGroup (Fin n) K) :
          Matrix (Fin n) (Fin n) K) *ᵥ v) = v := by
        rw [Matrix.mulVec_mulVec]
        have h1 : A.val * ((a⁻¹ : Matrix.SpecialLinearGroup (Fin n) K) :
            Matrix (Fin n) (Fin n) K) = 1 := congrArg Subtype.val (mul_inv_cancel a)
        rw [h1, Matrix.one_mulVec]
      change β (((g : Matrix (Fin n) (Fin n) K) *
        ((a⁻¹ : Matrix.SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K)) *ᵥ v) =
          β (y • v)
      rw [← Matrix.mulVec_mulVec, hgc, hy, mul_smul, ← map_smul,
        matrixModule_root_smul A lam hsq, hAw, hsmulK]
  exact ⟨evenCentComm_of_cover π hπ (fun s h => (hker s).mp h) a 𝓜 hC hN hQ hE hcomm,
    evenCentInv_of_cover π hπ (fun s h => (hker s).mp h) (fun s h => (hker s).mpr h) a 𝓜 hC hN
      hQ hE hinv⟩

end CFSG.ComponentClassification.HarrisLit.T1.P51Q
