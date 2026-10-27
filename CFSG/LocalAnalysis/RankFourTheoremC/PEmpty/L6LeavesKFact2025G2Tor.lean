module

public import CFSG.RankThree.PartOne.S11c.G2Pgl

public section

set_option linter.unusedSectionVars false

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KF2025.G2

open Matrix Matrix.ProjGenLinGroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Adjoint CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.RankThree.Chevalley
  CFSG.RankThree.Classical CFSG.RankThree.PartOne
open scoped MatrixGroups

section Lift

variable {K : Type*} [Field K]

theorem not_commute_of_lifts (hk : ringChar K ≠ 2) {u v : PGL(2, K)} (hu2 : u * u = 1)
    (hv2 : v * v = 1) (hu1 : u ≠ 1) (hv1 : v ≠ 1) (huv : v ≠ u) (hc : u * v = v * u)
    {B G : GL (Fin 2) K} (hB : mk B = u) (hG : mk G = v)
    (hcomm : (G : Matrix (Fin 2) (Fin 2) K) * B = B * G) : False := by
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hk
  have hBt : (B : Matrix (Fin 2) (Fin 2) K).trace = 0 :=
    trace_eq_zero_of_mk_mul_self (by rw [hB]; exact hu2) (by rw [hB]; exact hu1)
  have hGt : (G : Matrix (Fin 2) (Fin 2) K).trace = 0 :=
    trace_eq_zero_of_mk_mul_self (by rw [hG]; exact hv2) (by rw [hG]; exact hv1)
  have hc' : mk B * mk G = mk G * mk B := by rw [hB, hG]; exact hc
  rcases mk_eq_or_anticomm h2 hBt hGt hc' with h | h
  · exact huv (by rw [← hG, h, hB])
  · have e : (B : Matrix (Fin 2) (Fin 2) K) * G = -((B : Matrix (Fin 2) (Fin 2) K) * G) :=
      hcomm.symm.trans h
    have h0 : (2 : K) • ((B : Matrix (Fin 2) (Fin 2) K) * G) = 0 := by
      rw [two_smul]
      nth_rewrite 1 [e]
      simp
    rcases smul_eq_zero.mp h0 with h20 | h00
    · exact h2 h20
    · have : ((B * G : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = 0 := by
        rw [Units.val_mul]
        exact h00
      exact Units.ne_zero _ this

end Lift

section Image

variable {K : Type*} [Field K]

theorem pgl_image_aux2 (hk : ringChar K ≠ 2) {M : Type*} [Group M] {X : Subgroup M} (t₀ : M)
    (π : X →* PGL(2, K))
    (hker : ∀ g : X, (g : M) ^ 2 = 1 → π g = 1 → (g : M) = 1 ∨ (g : M) = t₀)
    {R : Subgroup M} (hR : R ≤ X) [Finite R] [CFSG.IsElementaryAbelian 2 R]
    (h8 : Nat.card R = 8) :
    t₀ ∈ R ∧ Nat.card (π.comp (Subgroup.inclusion hR)).range = 4 ∧
      ∀ z : X, (∀ r ∈ R, (z : M) * r = r * (z : M)) →
        ∃ r : R, π z = π (Subgroup.inclusion hR r) := by
  classical
  let f : R →* PGL(2, K) := π.comp (Subgroup.inclusion hR)
  have : CFSG.IsElementaryAbelian 2 f.range := isElementaryAbelian_range inferInstance f
  obtain ⟨-, hcard4, hcent⟩ :=
    odd_projective_linear_elementary_two_subgroups_and_centralizers K hk f.range
  have hsq : ∀ r : R, (r : M) ^ 2 = 1 := fun r =>
    CFSG.elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := R) (r : M) r.2
  have hker2 : Nat.card f.ker ≤ 2 := by
    let φ : f.ker → Bool := fun x => decide (((x : R) : M) = t₀)
    have hx : ∀ x : f.ker, ((x : R) : M) = 1 ∨ ((x : R) : M) = t₀ := fun x =>
      hker (Subgroup.inclusion hR x) (hsq x) x.2
    have hφ : Function.Injective φ := by
      intro x y hxy
      apply Subtype.ext
      apply Subtype.ext
      by_cases hxt : ((x : R) : M) = t₀
      · have hyt : ((y : R) : M) = t₀ := by
          by_contra hyt
          simp [φ, hxt, hyt] at hxy
        rw [hxt, hyt]
      · have hyt : ¬ ((y : R) : M) = t₀ := by
          intro hyt
          simp [φ, hxt, hyt] at hxy
        rw [(hx x).resolve_right hxt, (hx y).resolve_right hyt]
    calc Nat.card f.ker ≤ Nat.card Bool := Nat.card_le_card_of_injective φ hφ
      _ = 2 := by simp
  have hmul := Subgroup.card_ker_mul_card_range f
  have hrange4 : Nat.card f.range = 4 := by
    have : 8 ≤ 2 * Nat.card f.range := by
      rw [← h8, ← hmul]
      exact Nat.mul_le_mul_right _ hker2
    omega
  refine ⟨?_, hrange4, fun z hz => ?_⟩
  · have hk2 : Nat.card f.ker = 2 := by
      have := hmul
      rw [hrange4, h8] at this
      omega
    haveI : Nontrivial f.ker := Finite.one_lt_card_iff_nontrivial.mp (by omega)
    obtain ⟨x, hx1⟩ := exists_ne (1 : f.ker)
    have hxM := hker (Subgroup.inclusion hR x) (hsq x) x.2
    rcases hxM with h | h
    · exact absurd (Subtype.ext (Subtype.ext h)) hx1
    · rw [← h]
      exact (x : R).2
  · have hz' : π z ∈ Subgroup.centralizer (f.range : Set PGL(2, K)) := by
      rw [Subgroup.mem_centralizer_iff]
      rintro _ ⟨r, rfl⟩
      change π (Subgroup.inclusion hR r) * π z = π z * π (Subgroup.inclusion hR r)
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (hz r r.2).symm
    rw [hcent hrange4] at hz'
    obtain ⟨r, hr⟩ := hz'
    exact ⟨r, hr.symm⟩

end Image

section Toral


variable {K : Type} [Field K] {a : Fin Tag.G2.rank → Kˣ} {α β : Fin Tag.G2.rank → ℤ}

theorem rootSL2_eq_of_mem_center (h : G2SignPair α β) {A : SL2 K}
    (hA : A ∈ Subgroup.center (SL2 K)) : rootSL2 .G2 K α A = rootSL2 .G2 K β A := by
  have hneg := g2_pair_HSL_neg_one (K := K) h
  rcases rootSL2_of_mem_center (τ := .G2) α hA with h1 | h1
  · have : A = 1 := rootSL2_injective_of_field α (by rw [h1, map_one])
    rw [this, map_one, map_one]
  · have : A = HSL (-1) := rootSL2_injective_of_field α h1
    rw [this, hneg]

theorem g2Mul_central (h : G2SignPair α β) {A B : SL2 K} (hA : A ∈ Subgroup.center (SL2 K))
    (hB : B ∈ Subgroup.center (SL2 K)) :
    g2Mul h K (A, B) = 1 ∨ g2Mul h K (A, B) = rootSL2 .G2 K α (HSL (-1)) := by
  have hneg := g2_pair_HSL_neg_one (K := K) h
  rw [g2Mul_apply]
  rcases rootSL2_of_mem_center (τ := .G2) α hA with h1 | h1 <;>
    rcases rootSL2_of_mem_center (τ := .G2) β hB with h2 | h2
  · left
    rw [h1, h2, one_mul]
  · right
    rw [h1, h2, one_mul, hneg]
  · right
    rw [h1, h2, mul_one]
  · left
    rw [h1, h2, ← hneg]
    exact rootSL2_neg_one_sq (τ := .G2) (K := K) (γ := α)

theorem conj_rootSL2_beta (h : G2SignPair α β) (c : Fin Tag.G2.rank → Kˣ) (A B A' : SL2 K) :
    (rootDiagUnit .G2 c * (rootSL2 .G2 K α A * rootSL2 .G2 K β B)) * rootSL2 .G2 K β A' *
        (rootDiagUnit .G2 c * (rootSL2 .G2 K α A * rootSL2 .G2 K β B))⁻¹ =
      rootSL2 .G2 K β (conjSL (diagUnitOne (rootChar c β) *
        Matrix.SpecialLinearGroup.toGL B) A') := by
  obtain ⟨hα, hβ⟩ := g2_pair_isRoot h
  have := conj_rootSL2_decomp hβ (fun A' B' => (g2_pair_commute h B' A').symm) c B A A'
  rwa [← (g2_pair_commute h A B).eq] at this

theorem g2_toral_selfCentralizing (hK : ringChar K ≠ 2) (ha : ∀ i, a i = 1 ∨ a i = -1)
    (h : G2SignPair α β) (hS : (g2Mul h K).range = rootSpan .G2 K (rootCharKernel a))
    {R : Subgroup (ModGL .G2 K)} (hR : R ≤ toralCentralizer .G2 K a) [Finite R]
    [CFSG.IsElementaryAbelian 2 R] (h8 : Nat.card R = 8) :
    ∀ z ∈ toralCentralizer .G2 K a, (∀ r ∈ R, z * r = r * z) → z ∈ R := by
  classical
  obtain ⟨πα, hπα⟩ := exists_pgl_alpha hK ha h hS
  obtain ⟨πβ, hπβ⟩ := exists_pgl_beta hK ha h hS
  have hαS : ∀ (g : toralCentralizer .G2 K a) (A B : SL2 K),
      (g : ModGL .G2 K) = g2Mul h K (A, B) → πα g = toPGL A := fun g A B hg => by
    rw [hπα g 1 A B (by rw [hg, g2Mul_apply, rootDiagUnit_one, one_mul]), rootChar_one',
      diagUnitOne_one, one_mul]
    rfl
  have hβS : ∀ (g : toralCentralizer .G2 K a) (A B : SL2 K),
      (g : ModGL .G2 K) = g2Mul h K (A, B) → πβ g = toPGL B := fun g A B hg => by
    rw [hπβ g 1 A B (by rw [hg, g2Mul_apply, rootDiagUnit_one, one_mul]), rootChar_one',
      diagUnitOne_one, one_mul]
    rfl
  have hkerα : ∀ g : toralCentralizer .G2 K a, (g : ModGL .G2 K) ^ 2 = 1 → πα g = 1 →
      (g : ModGL .G2 K) = 1 ∨ (g : ModGL .G2 K) = rootSL2 .G2 K α (HSL (-1)) := by
    intro g hg2 hg1
    obtain ⟨⟨A, B⟩, hAB⟩ := mem_range_of_pgl_alpha hK ha h hS hπα (g := g)
      ⟨1, by rw [map_one, hg1]⟩
    have hgAB : (g : ModGL .G2 K) = g2Mul h K (A, B) := hAB.symm
    have hA : A ∈ Subgroup.center (SL2 K) :=
      toPGL_eq_one_iff.1 (by rw [← hαS g A B hgAB, hg1])
    rw [hgAB] at hg2 ⊢
    exact involution_of_central_component hK h hg2 (Or.inl hA)
  have hkerβ : ∀ g : toralCentralizer .G2 K a, (g : ModGL .G2 K) ^ 2 = 1 → πβ g = 1 →
      (g : ModGL .G2 K) = 1 ∨ (g : ModGL .G2 K) = rootSL2 .G2 K α (HSL (-1)) := by
    intro g hg2 hg1
    obtain ⟨⟨A, B⟩, hAB⟩ := mem_range_of_pgl_beta hK ha h hS hπβ (g := g)
      ⟨1, by rw [map_one, hg1]⟩
    have hgAB : (g : ModGL .G2 K) = g2Mul h K (A, B) := hAB.symm
    have hB : B ∈ Subgroup.center (SL2 K) :=
      toPGL_eq_one_iff.1 (by rw [← hβS g A B hgAB, hg1])
    rw [hgAB] at hg2 ⊢
    exact involution_of_central_component hK h hg2 (Or.inr hB)
  obtain ⟨ht₀R, -, hexα⟩ := pgl_image_aux2 hK (rootSL2 .G2 K α (HSL (-1))) πα hkerα hR h8
  obtain ⟨-, hcardβ, hexβ⟩ := pgl_image_aux2 hK (rootSL2 .G2 K α (HSL (-1))) πβ hkerβ hR h8
  have hRcomm : ∀ x ∈ R, ∀ y ∈ R, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val ((inferInstance : IsMulCommutative R).is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hRsq : ∀ r : R, Subgroup.inclusion hR r * Subgroup.inclusion hR r = 1 := fun r =>
    Subtype.ext (by
      have := CFSG.elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := R) (r : ModGL .G2 K) r.2
      simpa [pow_two] using this)
  intro z hz hzc
  obtain ⟨r₁, hr₁⟩ := hexα ⟨z, hz⟩ hzc
  have hr₁X : (r₁ : ModGL .G2 K) ∈ toralCentralizer .G2 K a := hR r₁.2
  have hwX : (r₁ : ModGL .G2 K)⁻¹ * z ∈ toralCentralizer .G2 K a :=
    mul_mem (inv_mem hr₁X) hz
  have hzw : z = (r₁ : ModGL .G2 K) * ((r₁ : ModGL .G2 K)⁻¹ * z) := by group
  generalize hw : (r₁ : ModGL .G2 K)⁻¹ * z = w at hwX hzw
  have hwc : ∀ r ∈ R, w * r = r * w := by
    intro r hr
    have hcm : Commute (r₁ : ModGL .G2 K) r := hRcomm _ r₁.2 r hr
    rw [← hw, mul_assoc, hzc r hr, ← mul_assoc, ← mul_assoc, hcm.inv_left.eq]
  have hπαw : πα ⟨w, hwX⟩ = 1 := by
    have : (⟨w, hwX⟩ : toralCentralizer .G2 K a) =
        (Subgroup.inclusion hR r₁)⁻¹ * ⟨z, hz⟩ := Subtype.ext (by simp [hw])
    rw [this, map_mul, map_inv, ← hr₁, inv_mul_cancel]
  obtain ⟨⟨A, B⟩, hAB⟩ := mem_range_of_pgl_alpha hK ha h hS hπα (g := ⟨w, hwX⟩)
    ⟨1, by rw [map_one, hπαw]⟩
  have hgAB : w = g2Mul h K (A, B) := hAB.symm
  have hA : A ∈ Subgroup.center (SL2 K) :=
    toPGL_eq_one_iff.1 (by rw [← hαS ⟨w, hwX⟩ A B hgAB, hπαw])
  have hπβw : πβ ⟨w, hwX⟩ = toPGL B := hβS ⟨w, hwX⟩ A B hgAB
  have hB : toPGL B = 1 := by
    by_contra hne
    obtain ⟨r', hr'⟩ := hexβ ⟨w, hwX⟩ hwc
    have hu2 : toPGL B * toPGL B = 1 := by
      rw [← hπβw, hr', ← map_mul, hRsq, map_one]
    have hex : ∃ r : R, πβ (Subgroup.inclusion hR r) ≠ 1 ∧
        πβ (Subgroup.inclusion hR r) ≠ toPGL B := by
      by_contra hcon
      push Not at hcon
      have hle := (finite_and_card_le_of_forall_mem (πβ.comp (Subgroup.inclusion hR)).range
        {1, toPGL B} (by
          rintro _ ⟨r, rfl⟩
          by_cases hr1 : πβ (Subgroup.inclusion hR r) = 1
          · simp [hr1]
          · simp [hcon r hr1])).2
      have h2 : ({1, toPGL B} : Finset PGL(2, K)).card ≤ 2 := Finset.card_le_two
      omega
    obtain ⟨r, hr1, hru⟩ := hex
    have hrX : (r : ModGL .G2 K) ∈ toralCentralizer .G2 K a := hR r.2
    obtain ⟨c, Ar, Br, hdec⟩ := exists_decomp hK ha h hS hrX
    have hv : πβ (Subgroup.inclusion hR r) = mk (diagUnitOne (rootChar c β) *
        Matrix.SpecialLinearGroup.toGL Br) := hπβ _ c Ar Br hdec
    have hwβ : w = rootSL2 .G2 K β (A * B) := by
      rw [hgAB, g2Mul_apply, rootSL2_eq_of_mem_center h hA, ← map_mul]
    have hconj := conj_rootSL2_beta h c Ar Br (A * B)
    rw [← hdec] at hconj
    have hrw : (r : ModGL .G2 K) * w * (r : ModGL .G2 K)⁻¹ = w := by
      rw [mul_inv_eq_iff_eq_mul]
      exact (hwc r r.2).symm
    rw [hwβ] at hrw
    rw [hrw] at hconj
    have hinj : conjSL (diagUnitOne (rootChar c β) * Matrix.SpecialLinearGroup.toGL Br) (A * B) =
        A * B := (rootSL2_injective_of_field β hconj).symm
    have hmat : ((diagUnitOne (rootChar c β) * Matrix.SpecialLinearGroup.toGL Br :
        GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * ((A * B : SL2 K) : Matrix (Fin 2) (Fin 2) K) =
        ((A * B : SL2 K) : Matrix (Fin 2) (Fin 2) K) *
          ((diagUnitOne (rootChar c β) * Matrix.SpecialLinearGroup.toGL Br :
            GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) := by
      have h1 := congrArg Subtype.val hinj
      rw [coe_conjSL] at h1
      calc _ = (diagUnitOne (rootChar c β) * Matrix.SpecialLinearGroup.toGL Br :
              GL (Fin 2) K) * ((A * B : SL2 K) : Matrix (Fin 2) (Fin 2) K) *
            (↑((diagUnitOne (rootChar c β) * Matrix.SpecialLinearGroup.toGL Br :
              GL (Fin 2) K)⁻¹) * ↑(diagUnitOne (rootChar c β) *
                Matrix.SpecialLinearGroup.toGL Br : GL (Fin 2) K)) := by
            rw [Units.inv_mul, Matrix.mul_one]
        _ = _ := by rw [← Matrix.mul_assoc, h1]
    have hABmk : mk (Matrix.SpecialLinearGroup.toGL (A * B)) = toPGL B := by
      change toPGL (A * B) = toPGL B
      rw [map_mul, toPGL_eq_one_iff.2 hA, one_mul]
    have hvv : πβ (Subgroup.inclusion hR r) * πβ (Subgroup.inclusion hR r) = 1 := by
      rw [← map_mul, hRsq, map_one]
    have hcomm : toPGL B * πβ (Subgroup.inclusion hR r) =
        πβ (Subgroup.inclusion hR r) * toPGL B := by
      rw [← hπβw, ← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (hwc r r.2)
    refine not_commute_of_lifts hK hu2 hvv hne hr1 hru hcomm
      (B := Matrix.SpecialLinearGroup.toGL (A * B))
      (G := diagUnitOne (rootChar c β) * Matrix.SpecialLinearGroup.toGL Br) hABmk hv.symm ?_
    rw [Matrix.SpecialLinearGroup.coe_GL_coe_matrix]
    exact hmat
  have hBc : B ∈ Subgroup.center (SL2 K) := toPGL_eq_one_iff.1 hB
  rcases g2Mul_central h hA hBc with h1 | h1
  · rw [hgAB, h1, mul_one] at hzw
    rw [hzw]
    exact r₁.2
  · rw [hgAB, h1] at hzw
    rw [hzw]
    exact mul_mem r₁.2 ht₀R

end Toral

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KF2025.G2
