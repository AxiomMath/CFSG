module

public import CFSG.ClassicalInvolution.Q3.Q3URPat

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3W

open Matrix CFSG.ClassicalInvolution.Phan CFSG.ClassicalInvolution.Models
  CFSG.ClassicalGroups.Unitary CFSG.ClassicalGroups.UnitaryFlag CFSG.LieType.BorelTits
  CFSG.LieType.Steinberg CFSG.LieType.Universal.Unitary CFSG.LocalAnalysis.ComponentInitial
  CFSG.ClassicalInvolution.ModelFacts.UnitaryAut CFSG.ClassicalInvolution.RouteD Module

section Chart

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p]

theorem unitary_partner_chart_three3 (hK : Nat.card K = (p ^ f) ^ 2) (hp2 : p ≠ 2)
    (hf : 1 ≤ f)
    (hP3 : ∀ l : Su K p f 2, l ^ 3 ∈ ⁅(⊤ : Subgroup (Su K p f 2)), (⊤ : Subgroup (Su K p f 2))⁆)
    (hcen : ∀ x ∈ Subgroup.center (Su K p f (3 + 1)), ¬ 3 ∣ orderOf x)
    {Y : Type} [Group Y] (θ : Su K p f (3 + 1) →* Y)
    (hker : θ.ker ≤ Subgroup.center (Su K p f (3 + 1))) (σ : Y ≃* Y) (hσ : ∀ y, σ (σ y) = y)
    (hstab : ∀ x, σ (θ x) ∈ θ.range)
    (hfix : ∀ A : Su K p f 2, σ (θ (blockEmb2 K p f 3 ⟨2, by omega⟩ A)) =
      θ (blockEmb2 K p f 3 ⟨2, by omega⟩ A))
    (hmove : ∃ A : Su K p f 2, σ (θ (blockEmb2 K p f 3 ⟨0, by omega⟩ A)) ≠
      θ (blockEmb2 K p f 3 ⟨0, by omega⟩ A)) :
    ∃ P : Su K p f 2, ∀ x : Su K p f (3 + 1),
      σ (θ (blockEmb2 K p f 3 ⟨0, by omega⟩ P * x * (blockEmb2 K p f 3 ⟨0, by omega⟩ P)⁻¹)) =
        θ (blockEmb2 K p f 3 ⟨0, by omega⟩ P * conjSign hK (partnerSigns 3 0) x *
          (blockEmb2 K p f 3 ⟨0, by omega⟩ P)⁻¹) := by
  classical
  have h : UnitaryFieldData p f K := ⟨Fact.out, hf, by rw [hK, ← pow_mul, mul_comm]⟩
  have h2 : (2 : K) ≠ 0 := two_ne_zero_of_charP_ne_two hp2
  obtain ⟨α, g, φ, hlift, hmat, hiso, hφ, hsq⟩ :=
    Q3NT.unitaryAutClassification_ambient_of_odd hK hp2 hf (by omega : 3 ≤ 3 + 1) θ hker σ hσ
      hstab
  have hα2 : ∀ A : Su K p f 2, α (blockEmb2 K p f 3 ⟨2, by omega⟩ A) =
      blockEmb2 K p f 3 ⟨2, by omega⟩ A := fun A =>
    DFunLike.congr_fun (lift_comp_eq_of_fixed3 hP3 hker (fun x hx => hcen x (hker hx)) hlift
      (blockEmb2 K p f 3 ⟨2, by omega⟩) hfix) A
  have hφinv : ∀ c, φ (φ c) = c := by
    rcases hφ with h1 | h1
    · subst h1
      intro c
      rfl
    · subst h1
      exact unitaryInvolution_involutive hK
  set σ₀ : K ≃+* K := unitaryInvolution K p f with hσ₀
  set G : Matrix (Fin 4) (Fin 4) K := (g : Matrix (Fin (3 + 1)) (Fin (3 + 1)) K) with hG
  set Gi : Matrix (Fin 4) (Fin 4) K :=
    ((g⁻¹ : GL (Fin (3 + 1)) K) : Matrix (Fin (3 + 1)) (Fin (3 + 1)) K) with hGi
  have hGGi : G * Gi = 1 := by rw [hG, hGi, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hGiG : Gi * G = 1 := by rw [hG, hGi, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  obtain ⟨u, hu1, hu2⟩ := exists_normOne_ne h hp2
  set c : K := ((u : Kˣ) : K) with hc
  have hcinv : (((u : Kˣ)⁻¹ : Kˣ) : K) = c⁻¹ := Units.val_inv_eq_inv_val _
  have hcσ : σ₀ c = c⁻¹ := eq_inv_of_mul_eq_one_left ((mem_normOne _).1 u.2)
  have hu2' : c⁻¹ ≠ c := by rw [← hcinv]; exact hu2
  have hrel : ∀ i j : Fin 4,
      (if i.val = 2 then c else if i.val = 3 then c⁻¹ else 1) * G i j =
        G i j * φ (if j.val = 2 then c else if j.val = 3 then c⁻¹ else 1) := by
    intro i j
    have h1 := hmat (blockEmb2 K p f 3 ⟨2, by omega⟩ (torusTwo σ₀ u))
    rw [hα2 (torusTwo σ₀ u), coe_coe_blockEmb2_torusTwo] at h1
    have h3 := diagonal_relation φ G Gi hGiG _ h1.symm i j
    simpa [hcinv] using h3
  have hoff : ∀ i j : Fin 4, G i j ≠ 0 → (i.val < 2 ∧ j.val < 2) ∨ (2 ≤ i.val ∧ 2 ≤ j.val) := by
    intro i j hne
    rcases hφ with h1 | h1
    · subst h1
      have h3 := hrel i j
      simp only [RingEquiv.refl_apply] at h3
      rcases torus_entry_cases_id (⟨2, by omega⟩ : Fin 3) c hu1 hu2' i j (G i j) hne h3 with
        heq | ⟨h4, h5, h6, h7⟩
      · subst heq
        omega
      · simp only at h4 h5 h6 h7
        omega
    · subst h1
      rcases torus_entry_cases σ₀ (⟨2, by omega⟩ : Fin 3) c hu1 hu2' hcσ i j (G i j) hne
        (hrel i j) with ⟨h4, h5⟩ | ⟨h4, h5⟩ | ⟨h4, h5, h6, h7⟩
      · simp only at h4 h5
        omega
      · simp only at h4 h5
        omega
      · simp only at h4 h5 h6 h7
        omega
  have hz : ∀ i j : Fin 4, ¬ ((i.val < 2 ∧ j.val < 2) ∨ (2 ≤ i.val ∧ 2 ≤ j.val)) → G i j = 0 :=
    fun i j hij => by
      by_contra hne
      exact hij (hoff i j hne)
  have z02 : G 0 2 = 0 := hz 0 2 (by decide)
  have z03 : G 0 3 = 0 := hz 0 3 (by decide)
  have z12 : G 1 2 = 0 := hz 1 2 (by decide)
  have z13 : G 1 3 = 0 := hz 1 3 (by decide)
  have z20 : G 2 0 = 0 := hz 2 0 (by decide)
  have z21 : G 2 1 = 0 := hz 2 1 (by decide)
  have z30 : G 3 0 = 0 := hz 3 0 (by decide)
  have z31 : G 3 1 = 0 := hz 3 1 (by decide)
  obtain ⟨U, hU⟩ : ∃ U : Matrix (Fin 2) (Fin 2) K, U = !![G 0 0, G 0 1; G 1 0, G 1 1] := ⟨_, rfl⟩
  obtain ⟨S, hS⟩ : ∃ S : Matrix (Fin 2) (Fin 2) K, S = !![G 2 2, G 2 3; G 3 2, G 3 3] := ⟨_, rfl⟩
  have hGbd : G = diagBlocks U S := by
    rw [hU, hS]
    exact eq_diagBlocks_of_zero G z02 z03 z12 z13 z20 z21 z30 z31
  have hφ0 : φ 0 = 0 := map_zero φ
  have hmap1 : (1 : Matrix (Fin 2) (Fin 2) K).map φ = 1 :=
    Matrix.map_one _ (map_zero φ) (map_one φ)
  have hfix_of_comm : ∀ y : Su K p f (3 + 1), suMat y * G = G * (suMat y).map φ → α y = y := by
    intro y hy
    apply suMat_injective
    have h1 := hmat y
    change suMat (α y) = G * φ.mapMatrix (suMat y) * Gi at h1
    rw [h1, RingEquiv.mapMatrix_apply, ← hy, Matrix.mul_assoc, hGGi, Matrix.mul_one]
  have hcomm_of_fix : ∀ y : Su K p f (3 + 1), α y = y → suMat y * G = G * (suMat y).map φ := by
    intro y hy
    have h1 := hmat y
    rw [hy] at h1
    change suMat y = G * φ.mapMatrix (suMat y) * Gi at h1
    rw [RingEquiv.mapMatrix_apply] at h1
    calc suMat y * G = (G * (suMat y).map φ * Gi) * G := by rw [← h1]
      _ = G * (suMat y).map φ := by rw [Matrix.mul_assoc, hGiG, Matrix.mul_one]
  have hSfix : ∀ A : Su K p f 2, suMat A * S = S * (suMat A).map φ := by
    intro A
    have h1 := hcomm_of_fix _ (hα2 A)
    rw [suMat_blockEmb2_two_eq_diagBlocks, hGbd, diagBlocks_map φ hφ0, hmap1, diagBlocks_mul,
      diagBlocks_mul] at h1
    exact (diagBlocks_inj h1).2
  have hno0 : (∀ A : Su K p f 2, suMat A * U = U * (suMat A).map φ) → False := by
    intro hall
    obtain ⟨A, hA⟩ := hmove
    apply hA
    have hα0 : α (blockEmb2 K p f 3 ⟨0, by omega⟩ A) = blockEmb2 K p f 3 ⟨0, by omega⟩ A := by
      apply hfix_of_comm
      rw [suMat_blockEmb2_zero_eq_diagBlocks, hGbd, diagBlocks_map φ hφ0, hmap1, diagBlocks_mul,
        diagBlocks_mul, hall A, one_mul, mul_one]
    rw [← hlift, hα0]
  have hiso' : (U.map σ₀)ᵀ * U = 1 ∧ (S.map σ₀)ᵀ * S = 1 := by
    have h1 : diagBlocks ((U.map σ₀)ᵀ * U) ((S.map σ₀)ᵀ * S) = diagBlocks 1 1 := by
      rw [diagBlocks_one, ← diagBlocks_mul, ← diagBlocks_transpose,
        ← diagBlocks_map σ₀ (map_zero σ₀), ← hGbd]
      exact hiso
    exact diagBlocks_inj h1
  obtain ⟨c₂, hc₂⟩ : ∃ c₂ : K, G * φ.mapMatrix G = c₂ • (1 : Matrix (Fin 4) (Fin 4) K) := by
    refine eq_smul_one_of_commute h hp2 (by omega : 3 ≤ 3 + 1) (G * φ.mapMatrix G) fun y hy => ?_
    have hy' : y ∈ SUid (unitaryInvolution K p f) (3 + 1) := by
      rw [SUid_eq_statedSU hK]
      exact hy
    have h1 := DFunLike.congr_fun hsq ⟨y, hy'⟩
    have h2' := congrArg (fun x : Su K p f (3 + 1) =>
      ((x : GL (Fin (3 + 1)) K) : Matrix (Fin (3 + 1)) (Fin (3 + 1)) K)) h1
    simp only [MonoidHom.comp_apply, MonoidHom.id_apply] at h2'
    rw [hmat (α ⟨y, hy'⟩), hmat ⟨y, hy'⟩] at h2'
    exact commute_of_double_conj φ hφinv G Gi (y : Matrix (Fin (3 + 1)) (Fin (3 + 1)) K) hGiG
      h2'.symm
  have hsq' : U * U.map φ = c₂ • 1 ∧ S * S.map φ = c₂ • 1 := by
    have h1 : diagBlocks (U * U.map φ) (S * S.map φ) = diagBlocks (c₂ • 1) (c₂ • 1) := by
      rw [← diagBlocks_smul, diagBlocks_one, ← diagBlocks_mul, ← diagBlocks_map φ hφ0, ← hGbd]
      rw [RingEquiv.mapMatrix_apply] at hc₂
      exact hc₂
    exact diagBlocks_inj h1
  have hw00 : suMat (weylElt K p f) 0 0 = 0 := by
    simp [suMat, CFSG.ClassicalInvolution.Phan.weylElt]
  have hw01 : suMat (weylElt K p f) 0 1 = 1 := by
    simp [suMat, CFSG.ClassicalInvolution.Phan.weylElt]
  have hw10 : suMat (weylElt K p f) 1 0 = -1 := by
    simp [suMat, CFSG.ClassicalInvolution.Phan.weylElt]
  have hw11 : suMat (weylElt K p f) 1 1 = 0 := by
    simp [suMat, CFSG.ClassicalInvolution.Phan.weylElt]
  have hW0 : (suMat (weylElt K p f)).map φ = suMat (weylElt K p f) := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hw00, hw01, hw10, hw11]
  have hSW := hSfix (weylElt K p f)
  rw [hW0] at hSW
  have hS10 : S 1 0 = -S 0 1 := by
    have e := congrFun (congrFun hSW 0) 0
    simp [Matrix.mul_apply, Fin.sum_univ_two, hw00, hw01, hw10] at e
    linear_combination e
  have hS11 : S 1 1 = S 0 0 := by
    have e := congrFun (congrFun hSW 0) 1
    simp [Matrix.mul_apply, Fin.sum_univ_two, hw00, hw01, hw11] at e
    linear_combination e
  rcases hφ with h1 | h1
  ·
    subst h1
    have hmapid : ∀ M : Matrix (Fin 2) (Fin 2) K, M.map (RingEquiv.refl K) = M := fun M => by
      ext i j
      rfl
    have hrefl : ∀ M : Matrix (Fin 4) (Fin 4) K, (RingEquiv.refl K).mapMatrix M = M :=
      fun M => by
        ext a b
        rfl
    have hG23 : G 2 3 = 0 := by
      by_contra hne
      have h3 := hrel 2 3
      simp only [RingEquiv.refl_apply] at h3
      rcases torus_entry_cases_id (⟨2, by omega⟩ : Fin 3) c hu1 hu2' 2 3 (G 2 3) hne h3 with
        heq | ⟨h4, -, -, -⟩
      · exact absurd (congrArg Fin.val heq) (by decide)
      · exact h4 rfl
    have hG32 : G 3 2 = 0 := by
      by_contra hne
      have h3 := hrel 3 2
      simp only [RingEquiv.refl_apply] at h3
      rcases torus_entry_cases_id (⟨2, by omega⟩ : Fin 3) c hu1 hu2' 3 2 (G 3 2) hne h3 with
        heq | ⟨-, h5, -, -⟩
      · exact absurd (congrArg Fin.val heq) (by decide)
      · exact h5 rfl
    have hS01 : S 0 1 = 0 := by rw [hS]; exact hG23
    have hS10' : S 1 0 = 0 := by rw [hS]; exact hG32
    obtain ⟨lam, hlam⟩ : ∃ lam : K, lam = S 0 0 := ⟨_, rfl⟩
    have hSlam : S = lam • (1 : Matrix (Fin 2) (Fin 2) K) := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [hlam, hS01, hS10', hS11]
    have hlam1 : σ₀ lam * lam = 1 := by
      have e := congrFun (congrFun hiso'.2 0) 0
      simpa [Matrix.mul_apply, Fin.sum_univ_two, hS10', ← hlam] using e
    have hlam0 : lam ≠ 0 := fun h0 => by
      rw [h0, mul_zero] at hlam1
      exact zero_ne_one hlam1
    have hc₂lam : c₂ = lam * lam := by
      have e := congrFun (congrFun hsq'.2 0) 0
      rw [hmapid] at e
      simp [Matrix.mul_apply, Fin.sum_univ_two, hS01, hS10', ← hlam] at e
      exact e.symm
    have hU2 : U * U = (lam * lam) • (1 : Matrix (Fin 2) (Fin 2) K) := by
      have e := hsq'.1
      rw [hmapid, hc₂lam] at e
      exact e
    have hne : ∀ μ : K, U ≠ μ • (1 : Matrix (Fin 2) (Fin 2) K) := fun μ hμ => by
      apply hno0
      intro A
      rw [hμ, hmapid, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Matrix.one_mul]
    obtain ⟨P, hP⟩ := exists_su_two_diagonalizer hK hp2 U lam hlam0 hlam1 hU2 hiso'.1
      (hne lam) (hne (-lam))
    set H : Su K p f (3 + 1) := blockEmb2 K p f 3 ⟨0, by omega⟩ P with hH
    set Dm : Matrix (Fin 4) (Fin 4) K := Matrix.diagonal ![-lam, lam, lam, lam] with hDm
    set Dmi : Matrix (Fin 4) (Fin 4) K :=
      Matrix.diagonal ![-lam⁻¹, lam⁻¹, lam⁻¹, lam⁻¹] with hDmi
    have hDDi : Dm * Dmi = 1 := by
      rw [hDm, hDmi, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
      congr 1
      funext i
      fin_cases i <;> simp [hlam0]
    have hDm_bd : Dm = diagBlocks (Matrix.diagonal ![-lam, lam]) (lam • 1) := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [hDm, diagBlocks]
    have hGH : G * suMat H = suMat H * Dm := by
      rw [hGbd, hH, suMat_blockEmb2_zero_eq_diagBlocks, hDm_bd, diagBlocks_mul, diagBlocks_mul, hP,
        hSlam, Matrix.mul_one, Matrix.one_mul]
    have hHHi : suMat H * suMat H⁻¹ = 1 := suMat_mul_suMat_inv H
    have hHiH : suMat H⁻¹ * suMat H = 1 := by rw [← suMat_mul, inv_mul_cancel, suMat_one]
    have hconjsign : ∀ x : Su K p f (3 + 1),
        suMat (conjSign hK (partnerSigns 3 0) x) = Dm * suMat x * Dmi := by
      intro x
      ext i j
      change (((conjSign hK (partnerSigns 3 0) x : Su K p f (3 + 1)) : GL (Fin (3 + 1)) K) :
        Matrix (Fin (3 + 1)) (Fin (3 + 1)) K) i j = _
      rw [coe_coe_conjSign_apply, hDm, hDmi, Matrix.mul_diagonal, Matrix.diagonal_mul]
      fin_cases i <;> fin_cases j <;> simp [signVal, partnerSigns, suMat] <;> field_simp
    have hαx : ∀ x : Su K p f (3 + 1),
        α (H * x * H⁻¹) = H * conjSign hK (partnerSigns 3 0) x * H⁻¹ := by
      intro x
      apply suMat_injective
      have h1 := hmat (H * x * H⁻¹)
      change suMat (α (H * x * H⁻¹)) =
        G * (RingEquiv.refl K).mapMatrix (suMat (H * x * H⁻¹)) * Gi at h1
      rw [h1, hrefl]
      simp only [suMat_mul]
      rw [hconjsign]
      exact conj_chart_eq_of_mul_eq G Gi (suMat H) (suMat H⁻¹) Dm Dmi hGiG hHHi hHiH hDDi hGH
        (suMat x)
    refine ⟨P, fun x => ?_⟩
    rw [← hlift (H * x * H⁻¹), hαx]
  ·
    exfalso
    have h1' : φ = σ₀ := h1
    subst h1'
    have hσ₀inv : ∀ a : K, σ₀ (σ₀ a) = a := hφinv
    have hG22 : G 2 2 = 0 := by
      by_contra hne
      rcases torus_entry_cases σ₀ (⟨2, by omega⟩ : Fin 3) c hu1 hu2' hcσ 2 2 (G 2 2) hne
        (hrel 2 2) with ⟨-, h5⟩ | ⟨h4, -⟩ | ⟨h4, -, -, -⟩
      · simp at h5
      · simp at h4
      · exact h4 rfl
    have hS00 : S 0 0 = 0 := by rw [hS]; exact hG22
    have hS11' : S 1 1 = 0 := by rw [hS11, hS00]
    have hss : σ₀ (S 0 1) * S 0 1 = 1 := by
      have e := congrFun (congrFun hiso'.2 0) 0
      simpa [Matrix.mul_apply, Fin.sum_univ_two, hS00, hS10] using e
    have hs0 : S 0 1 ≠ 0 := fun h0 => by
      rw [h0, mul_zero] at hss
      exact zero_ne_one hss
    have hc₂ : c₂ = -1 := by
      have e := congrFun (congrFun hsq'.2 0) 0
      simp [Matrix.mul_apply, Fin.sum_univ_two, hS00, hS10] at e
      linear_combination (-1 : K) * e - hss
    have hUa : U * U.map σ₀ = (-1 : K) • (1 : Matrix (Fin 2) (Fin 2) K) := by
      have e := hsq'.1
      rw [hc₂] at e
      exact e
    have hUb : (U.map σ₀)ᵀ * U = 1 := hiso'.1
    set V : Matrix (Fin 2) (Fin 2) K := U.map σ₀ with hV
    have hUV : U * (-V) = 1 := by
      rw [Matrix.mul_neg, hUa, neg_smul, one_smul, neg_neg]
    have hVt : Vᵀ = -V := by
      calc Vᵀ = Vᵀ * (U * (-V)) := by rw [hUV, Matrix.mul_one]
        _ = (Vᵀ * U) * (-V) := by rw [Matrix.mul_assoc]
        _ = -V := by rw [hUb, Matrix.one_mul]
    have hdiag0 : ∀ a : K, a = -a → a = 0 := fun a ha => by
      have : (2 : K) * a = 0 := by linear_combination ha
      exact (mul_eq_zero.mp this).resolve_left h2
    have hV00 : V 0 0 = 0 := hdiag0 _ (by simpa using congrFun (congrFun hVt 0) 0)
    have hV11 : V 1 1 = 0 := hdiag0 _ (by simpa using congrFun (congrFun hVt 1) 1)
    have hV10 : V 1 0 = -V 0 1 := by simpa using congrFun (congrFun hVt 0) 1
    have hUV' : ∀ i j, U i j = σ₀ (V i j) := fun i j => (hσ₀inv (U i j)).symm
    have hU00 : U 0 0 = 0 := by rw [hUV' 0 0, hV00, map_zero]
    have hU11 : U 1 1 = 0 := by rw [hUV' 1 1, hV11, map_zero]
    have hU10 : U 1 0 = -U 0 1 := by rw [hUV' 1 0, hV10, map_neg, ← hUV' 0 1]
    obtain ⟨μ, hμ⟩ : ∃ μ : K, U = μ • S := by
      refine ⟨U 0 1 / S 0 1, ?_⟩
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [hU00, hU11, hU10, hS00, hS10, hS11', hs0]
    apply hno0
    intro A
    rw [hμ, Matrix.mul_smul, Matrix.smul_mul, hSfix A]

end Chart

section Mirror

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p]

def swap02 : Equiv.Perm (Fin 4) := Equiv.swap 0 2 * Equiv.swap 1 3

def pair13 : Pair (3 + 1) := ⟨{1, 3}, Finset.card_pair (by decide)⟩

theorem LcU_map_conj_monoSU {n : ℕ} (hn : 0 < n) (τ : Equiv.Perm (Fin n)) (T T' : Pair n)
    (hT : T.1.map τ.toEmbedding = T'.1) :
    (LcU K p f T).map (MulAut.conj (monoSU K p f hn τ)).toMonoidHom = LcU K p f T' := by
  have hg : IsMonomialFor (suMat (monoSU K p f hn τ)) τ := isMonomialFor_monoMat (K := K) τ
  have h1 : suMat (monoSU K p f hn τ) * zMat K n T.1 * suMat (monoSU K p f hn τ)⁻¹ =
      zMat K n T'.1 := by
    rw [hg.mul_zMat_mul_inv (suMat_mul_suMat_inv _) T.1, hT]
  change (longRootGroupSU K p f (zMat K n T.1)).map _ = longRootGroupSU K p f (zMat K n T'.1)
  rw [← longRootGroupSU_conj, h1]

theorem unitary_partner_chart_three3_mirror (hK : Nat.card K = (p ^ f) ^ 2) (hp2 : p ≠ 2)
    (hf : 1 ≤ f)
    (hP3 : ∀ l : Su K p f 2, l ^ 3 ∈ ⁅(⊤ : Subgroup (Su K p f 2)), (⊤ : Subgroup (Su K p f 2))⁆)
    (hcen : ∀ x ∈ Subgroup.center (Su K p f (3 + 1)), ¬ 3 ∣ orderOf x)
    {Y : Type} [Group Y] (θ : Su K p f (3 + 1) →* Y)
    (hker : θ.ker ≤ Subgroup.center (Su K p f (3 + 1))) (σ : Y ≃* Y) (hσ : ∀ y, σ (σ y) = y)
    (hstab : ∀ x, σ (θ x) ∈ θ.range)
    (hfix : ∀ A : Su K p f 2, σ (θ (blockEmb2 K p f 3 ⟨0, by omega⟩ A)) =
      θ (blockEmb2 K p f 3 ⟨0, by omega⟩ A))
    (hmove : ∃ A : Su K p f 2, σ (θ (blockEmb2 K p f 3 ⟨2, by omega⟩ A)) ≠
      θ (blockEmb2 K p f 3 ⟨2, by omega⟩ A)) :
    ∃ P : Su K p f 2, ∀ H₁ ∈ (blockEmb2 K p f 3 ⟨0, by omega⟩).range, ∀ x ∈ LcU K p f pair13,
      σ (θ (blockEmb2 K p f 3 ⟨2, by omega⟩ P * (H₁ * x * H₁⁻¹) *
        (blockEmb2 K p f 3 ⟨2, by omega⟩ P)⁻¹)) =
        θ (blockEmb2 K p f 3 ⟨2, by omega⟩ P * (H₁ * x * H₁⁻¹) *
          (blockEmb2 K p f 3 ⟨2, by omega⟩ P)⁻¹) := by
  classical
  have h2 : (2 : K) ≠ 0 := two_ne_zero_of_charP_ne_two hp2
  set g : Su K p f 4 := monoSU K p f (by norm_num) swap02 with hg
  set ρ : Su K p f 4 →* Su K p f 4 := (MulAut.conj g).toMonoidHom with hρ
  have hρapp : ∀ x, ρ x = g * x * g⁻¹ := fun x => rfl
  have hE0 : (blockEmb2 K p f 3 ⟨0, by omega⟩).range.map ρ =
      (blockEmb2 K p f 3 ⟨2, by omega⟩).range := by
    rw [range_blockEmb2_eq_LcU_nodePair h2 (by norm_num : 0 < 3),
      range_blockEmb2_eq_LcU_nodePair h2 (by norm_num : 2 < 3)]
    exact LcU_map_conj_monoSU (by norm_num) swap02 _ _ (by decide)
  have hE2 : (blockEmb2 K p f 3 ⟨2, by omega⟩).range.map ρ =
      (blockEmb2 K p f 3 ⟨0, by omega⟩).range := by
    rw [range_blockEmb2_eq_LcU_nodePair h2 (by norm_num : 0 < 3),
      range_blockEmb2_eq_LcU_nodePair h2 (by norm_num : 2 < 3)]
    exact LcU_map_conj_monoSU (by norm_num) swap02 _ _ (by decide)
  have hE13 : (LcU K p f pair13).map ρ = LcU K p f pair13 :=
    LcU_map_conj_monoSU (by norm_num) swap02 _ _ (by decide)
  set θ' : Su K p f 4 →* Y := θ.comp ρ with hθ'
  have hker' : θ'.ker ≤ Subgroup.center (Su K p f (3 + 1)) := by
    intro x hx
    have h1 : ρ x ∈ θ.ker := hx
    have h2' := Subgroup.mem_center_iff.mp (hker h1)
    rw [Subgroup.mem_center_iff]
    intro y
    apply (MulAut.conj g).injective
    rw [map_mul, map_mul]
    exact h2' (ρ y)
  have hstab' : ∀ x, σ (θ' x) ∈ θ'.range := by
    intro x
    obtain ⟨w, hw⟩ := hstab (ρ x)
    refine ⟨g⁻¹ * w * g, ?_⟩
    show θ (ρ (g⁻¹ * w * g)) = σ (θ (ρ x))
    have : ρ (g⁻¹ * w * g) = w := by rw [hρapp]; group
    rw [this]
    exact hw
  have hfix' : ∀ A : Su K p f 2, σ (θ' (blockEmb2 K p f 3 ⟨2, by omega⟩ A)) =
      θ' (blockEmb2 K p f 3 ⟨2, by omega⟩ A) := by
    intro A
    have hm : ρ (blockEmb2 K p f 3 ⟨2, by omega⟩ A) ∈
        (blockEmb2 K p f 3 ⟨0, by omega⟩).range := by
      rw [← hE2]
      exact Subgroup.mem_map_of_mem _ ⟨A, rfl⟩
    obtain ⟨A', hA'⟩ := hm
    show σ (θ (ρ _)) = θ (ρ _)
    rw [← hA']
    exact hfix A'
  have hmove' : ∃ A : Su K p f 2, σ (θ' (blockEmb2 K p f 3 ⟨0, by omega⟩ A)) ≠
      θ' (blockEmb2 K p f 3 ⟨0, by omega⟩ A) := by
    obtain ⟨A, hA⟩ := hmove
    have hm : blockEmb2 K p f 3 ⟨2, by omega⟩ A ∈
        (blockEmb2 K p f 3 ⟨0, by omega⟩).range.map ρ := by
      rw [hE0]
      exact ⟨A, rfl⟩
    obtain ⟨y, ⟨A', rfl⟩, hy⟩ := hm
    refine ⟨A', ?_⟩
    show σ (θ (ρ _)) ≠ θ (ρ _)
    rw [hy]
    exact hA
  obtain ⟨P', hP'⟩ := unitary_partner_chart_three3 hK hp2 hf hP3 hcen θ' hker' σ hσ hstab' hfix'
    hmove'
  have hH2 : ρ (blockEmb2 K p f 3 ⟨0, by omega⟩ P') ∈
      (blockEmb2 K p f 3 ⟨2, by omega⟩).range := by
    rw [← hE0]
    exact Subgroup.mem_map_of_mem _ ⟨P', rfl⟩
  obtain ⟨P₂, hP₂⟩ := hH2
  refine ⟨P₂, fun H₁ hH₁ x hx => ?_⟩
  have hH₁' : H₁ ∈ (blockEmb2 K p f 3 ⟨2, by omega⟩).range.map ρ := by
    rw [hE2]
    exact hH₁
  obtain ⟨a, ⟨A, rfl⟩, rfl⟩ := hH₁'
  have hx' : x ∈ (LcU K p f pair13).map ρ := by
    rw [hE13]
    exact hx
  obtain ⟨b, hb, rfl⟩ := hx'
  have hv13 : ∀ a ∈ (pair13 : Pair (3 + 1)).1, ∀ b ∈ (pair13 : Pair (3 + 1)).1,
      partnerSigns 3 0 a = partnerSigns 3 0 b := by
    intro a ha b hb
    simp only [pair13, Finset.mem_insert, Finset.mem_singleton] at ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> simp [partnerSigns]
  have hfixa : conjSign hK (partnerSigns 3 0) (blockEmb2 K p f 3 ⟨2, by omega⟩ A) =
      blockEmb2 K p f 3 ⟨2, by omega⟩ A :=
    conjSign_blockEmb2_of_eq hK _ ⟨2, by omega⟩ (by simp [partnerSigns]) A
  have hfixb : conjSign hK (partnerSigns 3 0) b = b := conjSign_eq_of_const hK h2 _ hv13 hb
  have hfixx : conjSign hK (partnerSigns 3 0)
      (blockEmb2 K p f 3 ⟨2, by omega⟩ A * b * (blockEmb2 K p f 3 ⟨2, by omega⟩ A)⁻¹) =
        blockEmb2 K p f 3 ⟨2, by omega⟩ A * b * (blockEmb2 K p f 3 ⟨2, by omega⟩ A)⁻¹ := by
    rw [map_mul, map_mul, map_inv, hfixa, hfixb]
  have key := hP' (blockEmb2 K p f 3 ⟨2, by omega⟩ A * b *
    (blockEmb2 K p f 3 ⟨2, by omega⟩ A)⁻¹)
  rw [hfixx] at key
  change σ (θ (ρ _)) = θ (ρ _) at key
  have hρe : ρ (blockEmb2 K p f 3 ⟨0, by omega⟩ P' * (blockEmb2 K p f 3 ⟨2, by omega⟩ A * b *
        (blockEmb2 K p f 3 ⟨2, by omega⟩ A)⁻¹) * (blockEmb2 K p f 3 ⟨0, by omega⟩ P')⁻¹) =
      blockEmb2 K p f 3 ⟨2, by omega⟩ P₂ * (ρ (blockEmb2 K p f 3 ⟨2, by omega⟩ A) * ρ b *
        (ρ (blockEmb2 K p f 3 ⟨2, by omega⟩ A))⁻¹) * (blockEmb2 K p f 3 ⟨2, by omega⟩ P₂)⁻¹ := by
    rw [hP₂]
    simp only [map_mul, map_inv]
  rw [hρe] at key
  exact key

end Mirror

section Two

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p]

theorem unitary_two_partner_chart3 (hK : Nat.card K = (p ^ f) ^ 2) (hp2 : p ≠ 2) (hf : 1 ≤ f)
    (hP3 : ∀ l : Su K p f 2, l ^ 3 ∈ ⁅(⊤ : Subgroup (Su K p f 2)), (⊤ : Subgroup (Su K p f 2))⁆)
    (hcen : ∀ x ∈ Subgroup.center (Su K p f (3 + 1)), ¬ 3 ∣ orderOf x)
    {Y : Type} [Group Y] (θ : Su K p f (3 + 1) →* Y)
    (hker : θ.ker ≤ Subgroup.center (Su K p f (3 + 1))) (σ₁ σ₂ : Y ≃* Y)
    (hσ₁ : ∀ y, σ₁ (σ₁ y) = y) (hσ₂ : ∀ y, σ₂ (σ₂ y) = y)
    (hstab₁ : ∀ x, σ₁ (θ x) ∈ θ.range) (hstab₂ : ∀ x, σ₂ (θ x) ∈ θ.range)
    (hfix₁ : ∀ A : Su K p f 2, σ₁ (θ (blockEmb2 K p f 3 ⟨2, by omega⟩ A)) =
      θ (blockEmb2 K p f 3 ⟨2, by omega⟩ A))
    (hmove₁ : ∃ A : Su K p f 2, σ₁ (θ (blockEmb2 K p f 3 ⟨0, by omega⟩ A)) ≠
      θ (blockEmb2 K p f 3 ⟨0, by omega⟩ A))
    (hfix₂ : ∀ A : Su K p f 2, σ₂ (θ (blockEmb2 K p f 3 ⟨0, by omega⟩ A)) =
      θ (blockEmb2 K p f 3 ⟨0, by omega⟩ A))
    (hmove₂ : ∃ A : Su K p f 2, σ₂ (θ (blockEmb2 K p f 3 ⟨2, by omega⟩ A)) ≠
      θ (blockEmb2 K p f 3 ⟨2, by omega⟩ A)) :
    ∃ h : Su K p f (3 + 1), ∀ x ∈ LcU K p f pair13,
      σ₁ (θ (h * x * h⁻¹)) = θ (h * x * h⁻¹) ∧ σ₂ (θ (h * x * h⁻¹)) = θ (h * x * h⁻¹) := by
  classical
  have h2 : (2 : K) ≠ 0 := two_ne_zero_of_charP_ne_two hp2
  obtain ⟨P₁, hP₁⟩ := unitary_partner_chart_three3 hK hp2 hf hP3 hcen θ hker σ₁ hσ₁ hstab₁ hfix₁
    hmove₁
  obtain ⟨P₂, hP₂⟩ := unitary_partner_chart_three3_mirror hK hp2 hf hP3 hcen θ hker σ₂ hσ₂
    hstab₂ hfix₂ hmove₂
  have hcomm : blockEmb2 K p f 3 ⟨0, by omega⟩ P₁ * blockEmb2 K p f 3 ⟨2, by omega⟩ P₂ =
      blockEmb2 K p f 3 ⟨2, by omega⟩ P₂ * blockEmb2 K p f 3 ⟨0, by omega⟩ P₁ :=
    blockEmb2_comm 3 ⟨0, by omega⟩ ⟨2, by omega⟩ (by simp) P₁ P₂
  refine ⟨blockEmb2 K p f 3 ⟨2, by omega⟩ P₂ * blockEmb2 K p f 3 ⟨0, by omega⟩ P₁,
    fun x hx => ⟨?_, ?_⟩⟩
  · have hv13 : ∀ a ∈ (pair13 : Pair (3 + 1)).1, ∀ b ∈ (pair13 : Pair (3 + 1)).1,
        partnerSigns 3 0 a = partnerSigns 3 0 b := by
      intro a ha b hb
      simp only [pair13, Finset.mem_insert, Finset.mem_singleton] at ha hb
      rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> simp [partnerSigns]
    have hfixa : conjSign hK (partnerSigns 3 0) (blockEmb2 K p f 3 ⟨2, by omega⟩ P₂) =
        blockEmb2 K p f 3 ⟨2, by omega⟩ P₂ :=
      conjSign_blockEmb2_of_eq hK _ ⟨2, by omega⟩ (by simp [partnerSigns]) P₂
    have hfixb : conjSign hK (partnerSigns 3 0) x = x := conjSign_eq_of_const hK h2 _ hv13 hx
    have e : blockEmb2 K p f 3 ⟨2, by omega⟩ P₂ * blockEmb2 K p f 3 ⟨0, by omega⟩ P₁ * x *
        (blockEmb2 K p f 3 ⟨2, by omega⟩ P₂ * blockEmb2 K p f 3 ⟨0, by omega⟩ P₁)⁻¹ =
        blockEmb2 K p f 3 ⟨0, by omega⟩ P₁ * (blockEmb2 K p f 3 ⟨2, by omega⟩ P₂ * x *
          (blockEmb2 K p f 3 ⟨2, by omega⟩ P₂)⁻¹) * (blockEmb2 K p f 3 ⟨0, by omega⟩ P₁)⁻¹ := by
      rw [← hcomm]
      group
    have hfixy : conjSign hK (partnerSigns 3 0) (blockEmb2 K p f 3 ⟨2, by omega⟩ P₂ * x *
        (blockEmb2 K p f 3 ⟨2, by omega⟩ P₂)⁻¹) = blockEmb2 K p f 3 ⟨2, by omega⟩ P₂ * x *
          (blockEmb2 K p f 3 ⟨2, by omega⟩ P₂)⁻¹ := by
      rw [map_mul, map_mul, map_inv, hfixa, hfixb]
    rw [e, hP₁, hfixy]
  · have hmem : blockEmb2 K p f 3 ⟨0, by omega⟩ P₁ ∈
        (blockEmb2 K p f 3 ⟨0, by omega⟩).range := ⟨P₁, rfl⟩
    have e : blockEmb2 K p f 3 ⟨2, by omega⟩ P₂ * blockEmb2 K p f 3 ⟨0, by omega⟩ P₁ * x *
        (blockEmb2 K p f 3 ⟨2, by omega⟩ P₂ * blockEmb2 K p f 3 ⟨0, by omega⟩ P₁)⁻¹ =
        blockEmb2 K p f 3 ⟨2, by omega⟩ P₂ * (blockEmb2 K p f 3 ⟨0, by omega⟩ P₁ * x *
          (blockEmb2 K p f 3 ⟨0, by omega⟩ P₁)⁻¹) * (blockEmb2 K p f 3 ⟨2, by omega⟩ P₂)⁻¹ := by
      group
    rw [e]
    exact hP₂ _ hmem x hx

end Two

end CFSG.ClassicalInvolution.Q3.Q3W
