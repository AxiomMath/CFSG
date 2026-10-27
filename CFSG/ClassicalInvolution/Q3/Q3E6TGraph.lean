module

public import CFSG.ClassicalInvolution.Q3.Q3E6TFix
public import CFSG.ClassicalInvolution.Q3.Q3E6TSgn
public import CFSG.ClassicalInvolution.Q3.Q3E6TIsol

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3E6T

open Matrix
open CFSG.Open hiding StatedLieTag StatedLieAdmissible StatedSU
open CFSG.ClassicalGroups.Unitary CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Phan CFSG.ClassicalInvolution.Models CFSG.LieType.Universal.Unitary
  CFSG.ClassicalInvolution.ModelFacts.UnitaryAut CFSG.ClassicalInvolution.RouteD
  CFSG.ClassicalInvolution.RouteD.Gaps CFSG.ClassicalInvolution.RouteD.Exotic
  CFSG.ClassicalInvolution.RouteD.NonClassical CFSG.Assembly.LowTwoRank
  CFSG.ClassicalInvolution.Q3.Q3W CFSG.ClassicalInvolution.Q3.Q3TC Module
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)
open CFSG.LieType.BorelTits (unitaryInvolution unitaryInvolution_apply)
open scoped MatrixGroups

section Matrices

variable {g : GL (Fin 6) (GaloisField 3 2)}
  {α : Su (GaloisField 3 2) 3 1 6 →* Su (GaloisField 3 2) 3 1 6}

theorem sq_scalar_bar3
    (hα : ∀ x : Su (GaloisField 3 2) 3 1 6,
      ((α x : GL (Fin 6) (GaloisField 3 2)) : Matrix (Fin 6) (Fin 6) (GaloisField 3 2)) =
        (g : Matrix (Fin 6) (Fin 6) (GaloisField 3 2)) *
          (unitaryInvolution (GaloisField 3 2) 3 1).mapMatrix
            ((x : GL (Fin 6) (GaloisField 3 2)) : Matrix (Fin 6) (Fin 6) (GaloisField 3 2)) *
          ((g⁻¹ : GL (Fin 6) (GaloisField 3 2)) : Matrix (Fin 6) (Fin 6) (GaloisField 3 2)))
    (hα2 : α.comp α = MonoidHom.id _) :
    ∃ a : GaloisField 3 2, (g : Matrix (Fin 6) (Fin 6) (GaloisField 3 2)) *
      (unitaryInvolution (GaloisField 3 2) 3 1).mapMatrix
        (g : Matrix (Fin 6) (Fin 6) (GaloisField 3 2)) =
        a • (1 : Matrix (Fin 6) (Fin 6) (GaloisField 3 2)) := by
  have hK : Nat.card (GaloisField 3 2) = (3 ^ 1) ^ 2 := card_gf9
  have hσ := isUnitaryInvolution_unitaryInvolution (p := 3) (f := 1) hK
  have hSS : ∀ A : Matrix (Fin 6) (Fin 6) (GaloisField 3 2),
      (unitaryInvolution (GaloisField 3 2) 3 1).mapMatrix
        ((unitaryInvolution (GaloisField 3 2) 3 1).mapMatrix A) = A :=
    fun A => Matrix.ext fun i j => hσ.invol _
  refine eq_smul_one_of_commute (unitaryFieldData_te6 (p := 3) (f := 1) le_rfl)
    (by norm_num : (3 : ℕ) ≠ 2) (by norm_num : 3 ≤ 6) _ ?_
  intro y hy
  set x : Su (GaloisField 3 2) 3 1 6 :=
    (suEquivUnitarySU (GaloisField 3 2) 3 1 hK 6).symm ⟨y, hy⟩ with hx
  have hxy : ((x : GL (Fin 6) (GaloisField 3 2)) : Matrix (Fin 6) (Fin 6)
      (GaloisField 3 2)) = (y : Matrix (Fin 6) (Fin 6) (GaloisField 3 2)) := rfl
  have e0 : α (α x) = x := DFunLike.congr_fun hα2 x
  have e := congrArg (fun z : Su (GaloisField 3 2) 3 1 6 =>
    ((z : GL (Fin 6) (GaloisField 3 2)) : Matrix (Fin 6) (Fin 6) (GaloisField 3 2))) e0
  simp only [hα] at e
  set Gm : Matrix (Fin 6) (Fin 6) (GaloisField 3 2) :=
    ((g : GL (Fin 6) (GaloisField 3 2)) : Matrix (Fin 6) (Fin 6) (GaloisField 3 2)) with hGm
  set Gi : Matrix (Fin 6) (Fin 6) (GaloisField 3 2) :=
    ((g⁻¹ : GL (Fin 6) (GaloisField 3 2)) : Matrix (Fin 6) (Fin 6) (GaloisField 3 2)) with hGi
  have hGiG : Gi * Gm = 1 := by rw [hGi, hGm, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  rw [hxy] at e
  simp only [map_mul, hSS] at e
  set yy : Matrix (Fin 6) (Fin 6) (GaloisField 3 2) :=
    ((y : GL (Fin 6) (GaloisField 3 2)) : Matrix (Fin 6) (Fin 6) (GaloisField 3 2)) with hyy
  have hN : (unitaryInvolution (GaloisField 3 2) 3 1).mapMatrix Gi *
      (unitaryInvolution (GaloisField 3 2) 3 1).mapMatrix Gm = 1 := by
    rw [← map_mul, hGiG, map_one]
  have hM : Gm * (unitaryInvolution (GaloisField 3 2) 3 1).mapMatrix Gm * yy *
      ((unitaryInvolution (GaloisField 3 2) 3 1).mapMatrix Gi * Gi) = yy := by
    simpa only [Matrix.mul_assoc] using e
  have hNM : ((unitaryInvolution (GaloisField 3 2) 3 1).mapMatrix Gi * Gi) *
      (Gm * (unitaryInvolution (GaloisField 3 2) 3 1).mapMatrix Gm) = 1 := by
    calc _ = (unitaryInvolution (GaloisField 3 2) 3 1).mapMatrix Gi * (Gi * Gm) *
            (unitaryInvolution (GaloisField 3 2) 3 1).mapMatrix Gm := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hGiG, Matrix.mul_one, hN]
  calc Gm * (unitaryInvolution (GaloisField 3 2) 3 1).mapMatrix Gm * yy
      = (Gm * (unitaryInvolution (GaloisField 3 2) 3 1).mapMatrix Gm * yy) *
          (((unitaryInvolution (GaloisField 3 2) 3 1).mapMatrix Gi * Gi) *
            (Gm * (unitaryInvolution (GaloisField 3 2) 3 1).mapMatrix Gm)) := by
        rw [hNM, Matrix.mul_one]
    _ = (Gm * (unitaryInvolution (GaloisField 3 2) 3 1).mapMatrix Gm * yy *
          ((unitaryInvolution (GaloisField 3 2) 3 1).mapMatrix Gi * Gi)) *
          (Gm * (unitaryInvolution (GaloisField 3 2) 3 1).mapMatrix Gm) := by
        simp only [Matrix.mul_assoc]
    _ = yy * (Gm * (unitaryInvolution (GaloisField 3 2) 3 1).mapMatrix Gm) := by rw [hM]

end Matrices

section Center

theorem eq_one_of_central_of_mem_planeGroupU3
    {P : Submodule (GaloisField 3 2) (Fin 6 → GaloisField 3 2)}
    (hPnd : Nondeg (unitaryInvolution (GaloisField 3 2) 3 1) P)
    (hP2 : finrank (GaloisField 3 2) P = 2) {ζ : Su (GaloisField 3 2) 3 1 6}
    (hζ : ζ ∈ Subgroup.center (Su (GaloisField 3 2) 3 1 6))
    (hζP : ζ ∈ planeGroupU (GaloisField 3 2) 3 1 P) : ζ = 1 := by
  have hK : Nat.card (GaloisField 3 2) = (3 ^ 1) ^ 2 := card_gf9
  have hσ := isUnitaryInvolution_unitaryInvolution (p := 3) (f := 1) hK
  obtain ⟨a, ha⟩ := eq_smul_one_of_commute (unitaryFieldData_te6 (p := 3) (f := 1) le_rfl)
    (by norm_num : (3 : ℕ) ≠ 2) (by norm_num : 3 ≤ 6) (suMat ζ) (by
      intro y hy
      set x : Su (GaloisField 3 2) 3 1 6 :=
        (suEquivUnitarySU (GaloisField 3 2) 3 1 hK 6).symm ⟨y, hy⟩ with hx
      have hxy : suMat x = (y : Matrix (Fin 6) (Fin 6) (GaloisField 3 2)) := rfl
      have h2 := congrArg suMat (Subgroup.mem_center_iff.mp hζ x)
      rw [suMat_mul, suMat_mul, hxy] at h2
      exact h2.symm)
  have hdim := finrank_add_finrank_herm_perp hσ hPnd
  have hne : perp (unitaryInvolution (GaloisField 3 2) 3 1) P ≠ ⊥ := by
    intro h0
    rw [h0, finrank_bot, hP2] at hdim
    omega
  obtain ⟨w, hwP, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  have hfix : suMat ζ *ᵥ w = w := by
    rw [← suMat_smul]
    exact ((mem_fixingSubgroup_iff _).mp hζP) w hwP
  obtain ⟨i, hi⟩ : ∃ i, w i ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hw0 (funext hcon)
  have ha1 : a = 1 := by
    have := congrFun hfix i
    rw [ha] at this
    simp only [Matrix.smul_mulVec, Matrix.one_mulVec, Pi.smul_apply, smul_eq_mul] at this
    exact mul_right_cancel₀ hi (by rw [this, one_mul])
  apply suMat_injective
  rw [ha, ha1, one_smul, suMat_one]

end Center


section Chart

variable {G : Type} [Group G] [Finite G] {K : Subgroup G} {z : G}

theorem g_commutes_te6Inv3 (c : UCtx3 5 (conjClass3 K) K z) (nd : UNodes3 c)
    {Θ : Su (GaloisField 3 2) 3 1 6 →* G} (hΘ : TE6Chart3 c nd Θ) {N : Subgroup G}
    (hN : N ∈ centralizingMembers (conjClass3 K) {z * nd.w 0}) {v : G}
    (hv : IsClassicalMember3 N v)
    (hNK : ∃ W : Subgroup G, LinearBlockStandardPair (GaloisField 3 1) W K N)
    {g : GL (Fin 6) (GaloisField 3 2)}
    {α : Su (GaloisField 3 2) 3 1 6 →* Su (GaloisField 3 2) 3 1 6}
    (φ : GaloisField 3 2 ≃+* GaloisField 3 2) (hα : ∀ x, Θ (α x) = v * Θ x * v⁻¹)
    (hmat : ∀ x : Su (GaloisField 3 2) 3 1 6,
      ((α x : GL (Fin 6) (GaloisField 3 2)) : Matrix (Fin 6) (Fin 6) (GaloisField 3 2)) =
        (g : Matrix (Fin 6) (Fin 6) (GaloisField 3 2)) *
          φ.mapMatrix ((x : GL (Fin 6) (GaloisField 3 2)) :
            Matrix (Fin 6) (Fin 6) (GaloisField 3 2)) *
          ((g⁻¹ : GL (Fin 6) (GaloisField 3 2)) : Matrix (Fin 6) (Fin 6) (GaloisField 3 2))) :
    (g : Matrix (Fin 6) (Fin 6) (GaloisField 3 2)) * suMat (te6Inv 3 1) =
      suMat (te6Inv 3 1) * (g : Matrix (Fin 6) (Fin 6) (GaloisField 3 2)) := by
  classical
  have hK : Nat.card (GaloisField 3 2) = (3 ^ 1) ^ 2 := card_gf9
  have hvz : v * z * v⁻¹ = z := partner_involution_commutes3 c.hz hv hNK
  have hw0 : Θ (te6Inv 3 1) = nd.w 0 := map_te6Inv_eq3 hΘ
  have hvw : v * nd.w 0 * v⁻¹ = nd.w 0 := by
    have h1 : v * (z * nd.w 0) = (z * nd.w 0) * v :=
      Subgroup.mem_centralizer_singleton_iff.mp (hN.2 hv.mem)
    have h2 : v * z = z * v := by
      have := hvz
      rw [mul_inv_eq_iff_eq_mul] at this
      exact this
    have h3 : z * (v * nd.w 0) = z * (nd.w 0 * v) := by
      calc z * (v * nd.w 0) = (z * v) * nd.w 0 := by rw [mul_assoc]
        _ = (v * z) * nd.w 0 := by rw [h2]
        _ = v * (z * nd.w 0) := by rw [mul_assoc]
        _ = (z * nd.w 0) * v := h1
        _ = z * (nd.w 0 * v) := by rw [mul_assoc]
    rw [mul_left_cancel h3, mul_inv_cancel_right]
  have hfixw : (MulAut.conj v) (Θ (te6Inv 3 1)) = Θ (te6Inv 3 1) := by
    rw [hw0]
    exact hvw
  obtain ⟨u, hu⟩ := lift_matrix_of_fixed (n := 6) hK (by norm_num : 3 ≤ 6) hΘ.ker_le
    (σ := MulAut.conj v) (α := α) (fun x => hα x) (x := te6Inv 3 1) hfixw
  set Gm : Matrix (Fin 6) (Fin 6) (GaloisField 3 2) :=
    ((g : GL (Fin 6) (GaloisField 3 2)) : Matrix (Fin 6) (Fin 6) (GaloisField 3 2)) with hGm
  set Gi : Matrix (Fin 6) (Fin 6) (GaloisField 3 2) :=
    ((g⁻¹ : GL (Fin 6) (GaloisField 3 2)) : Matrix (Fin 6) (Fin 6) (GaloisField 3 2)) with hGi
  set W : Matrix (Fin 6) (Fin 6) (GaloisField 3 2) := suMat (te6Inv 3 1) with hWdef
  have hGiG : Gi * Gm = 1 := by rw [hGi, hGm, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have h1 : Gm * W * Gi = (u : GaloisField 3 2) • W := by
    have := (hmat (te6Inv 3 1)).symm.trans hu
    have e : φ.mapMatrix ((((te6Inv 3 1 : Su (GaloisField 3 2) 3 1 6) :
        GL (Fin 6) (GaloisField 3 2)) : Matrix (Fin 6) (Fin 6) (GaloisField 3 2))) = W :=
      mapMatrix_suMat_te6Inv (p := 3) (f := 1) φ
    rw [e] at this
    exact this
  have htr : Matrix.trace (Gm * W * Gi) = Matrix.trace W := by
    rw [Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc, hGiG, Matrix.mul_one]
  have htr2 : Matrix.trace W = (2 : GaloisField 3 2) := trace_te6Inv
  have hu1 : (u : GaloisField 3 2) = 1 := by
    rw [h1, Matrix.trace_smul, htr2, smul_eq_mul] at htr
    have h3 : ((u : GaloisField 3 2) - 1) * 2 = 0 := by linear_combination htr
    exact sub_eq_zero.mp ((mul_eq_zero.mp h3).resolve_right two_ne_zero_gf9)
  rw [hu1, one_smul] at h1
  calc Gm * W = Gm * W * (Gi * Gm) := by rw [hGiG, Matrix.mul_one]
    _ = (Gm * W * Gi) * Gm := by simp only [Matrix.mul_assoc]
    _ = W * Gm := by rw [h1]

end Chart

section Main

theorem eq_one_of_mk_eq_one_of_sq3 {Y : Type} [Group Y] [Finite Y] {c : Y} (hc : c * c = 1)
    (h : QuotientGroup.mk' (classicalInvolutionOddCore Y) c = 1) : c = 1 := by
  have hcO : c ∈ classicalInvolutionOddCore Y := (QuotientGroup.eq_one_iff c).mp h
  have hord2 : orderOf c ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hc)
  have hodd := CFSG.ComponentClassification.OddCore.odd_card Y
  have hdvd : orderOf (⟨c, hcO⟩ : classicalInvolutionOddCore Y) ∣
      Nat.card (classicalInvolutionOddCore Y) := orderOf_dvd_natCard _
  rw [Subgroup.orderOf_mk] at hdvd
  rcases (Nat.dvd_prime Nat.prime_two).mp hord2 with h | h
  · exact orderOf_eq_one_iff.mp h
  · exfalso
    rw [h] at hdvd
    exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr hdvd)

theorem linear_pair_of_chain3_pOmegaMinus_five
    {R₁ R₂ R₃ : Subgroup (Generic.modelUniv .POmegaMinus 5 3 1 Nat.prime_three).K}
    (h₁ : R₁ ∈ Generic.fundamentalSubgroups .POmegaMinus
      (Generic.modelUniv .POmegaMinus 5 3 1 Nat.prime_three).D)
    (h₂ : R₂ ∈ Generic.fundamentalSubgroups .POmegaMinus
      (Generic.modelUniv .POmegaMinus 5 3 1 Nat.prime_three).D)
    (h₃ : R₃ ∈ Generic.fundamentalSubgroups .POmegaMinus
      (Generic.modelUniv .POmegaMinus 5 3 1 Nat.prime_three).D)
    (hlin : ∃ W, LinearBlockStandardPair (GaloisField 3 1) W R₁ R₂) (h13 : Commutes R₁ R₃)
    (hn32 : ¬ Commutes R₃ R₂) (hne32 : R₃ ≠ R₂)
    {c₂ : (Generic.modelUniv .POmegaMinus 5 3 1 Nat.prime_three).K} (hc₂ : c₂ ∈ R₂)
    (ho₂ : orderOf c₂ = 2) (hnorm : ∀ x ∈ R₃, c₂ * x * c₂⁻¹ ∈ R₃) :
    ∃ W, LinearBlockStandardPair (GaloisField 3 1) W R₂ R₃ := by
  have hadm : StatedLieAdmissible .POmegaMinus 5 3 1 := ⟨Nat.prime_three, le_rfl, by norm_num⟩
  have S := ModelFacts.spinCtx3_pOmegaMinus hadm (by norm_num : 3 ^ 1 = 3)
  have hL := fun {R : Subgroup (Generic.modelUniv .POmegaMinus 5 3 1 Nat.prime_three).K}
    (hR : R ∈ Generic.fundamentalSubgroups .POmegaMinus
      (Generic.modelUniv .POmegaMinus 5 3 1 Nat.prime_three).D) =>
    ModelFacts.fundamentalSubgroups_subset_longest (t := .POmegaMinus) (by decide) (by decide) _ hR
  exact linear_pair_of_chain3 S (hL h₁) (hL h₂) (hL h₃) hlin h13 hn32 hne32 hc₂ ho₂ hnorm

variable {G : Type} [Group G] [Finite G] {K : Subgroup G} {z : G}

theorem te6NotGraphField3_of_productP1 (hP : Q3TC.ProductP1Input3) [IsSimpleGroup G]
    (hnab : ∃ a b : G, a * b ≠ b * a) (hR : RouteD3Setup K z)
    (hsingle : ∀ L ∈ conjClass3 K, ∃ g : G, L = conjSub g K)
    (hshape : LocalShapeC3 1 (CompData.model .PSU 6) (conjClass3 K) z)
    (c : UCtx3 5 (conjClass3 K) K z) (nd : UNodes3 c) {β : Subgroup G}
    (hβ : IsPartnerU3 c nd β) (hn3 : ¬ Commutes β (nd.j 3)) : TE6NotGraphField3 c nd := by
  classical
  have hF1 := te6PartnerIsolated3_of_productP1 hP hnab hR c nd hβ hn3
  obtain ⟨X, hNR, hvisR⟩ := te6_context3 hP hnab hR c nd hβ hn3
  have hadm : StatedLieAdmissible .POmegaMinus 5 3 1 := ⟨Nat.prime_three, le_rfl, by norm_num⟩
  have hfin : Finite (Generic.modelUniv .POmegaMinus 5 3 1 Nat.prime_three).K :=
    ModelFacts.finite_modelUniv (by norm_num) Nat.prime_three trivial hadm
  have hcf := (Q3W.yData3_minus (by norm_num : 4 ≤ 5) hadm).central
  have h0 : 0 < 5 := by norm_num
  have hKx : K ∈ centralizingMembers (conjClass3 K) {z * nd.w 0} :=
    UNodes3.K_mem_centralizingMembers_mul3 c nd h0
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  intro N hN pKN pNJ Θ hΘ v hv α g φ hα hmat hiso hφ hα2
  rcases hφ with rfl | rfl
  · rfl
  exfalso
  obtain ⟨a, ha⟩ := sq_scalar_bar3 hmat hα2
  have hW := g_commutes_te6Inv3 c nd hΘ hN hv pKN _ hα hmat
  rcases mu_eq_one_or_neg_one _ hiso ha with h1 | h1
  ·
    rw [h1, one_smul] at ha
    obtain ⟨P, hPnd, hP2, hPle, hPstab, y, hyS, hαy, hy2, hy4⟩ :=
      exists_stable_aniso_plane_rot (p := 3) (f := 1) le_rfl hp2 (by norm_num) hmat hiso ha hW
    have hRS := planeGroupU_mem card_gf9 hp2 (by norm_num : 2 ≤ 5 + 1) hPnd hP2
    obtain ⟨hLmem, hLK⟩ := hΘ.member _ hRS
    have hw0 : Θ (te6Inv 3 1) = nd.w 0 := map_te6Inv_eq3 hΘ
    have hLvis : (planeGroupU (GaloisField 3 2) 3 1 P).map Θ ∈
        centralizingMembers (conjClass3 K) {z * nd.w 0, z} := by
      rw [centralizingMembers_mul_iff, mem_centralizingMembers_pair]
      refine ⟨hLmem, ?_⟩
      rintro _ ⟨x, hx, rfl⟩
      rw [Subgroup.mem_centralizer_singleton_iff, ← hw0, ← map_mul, ← map_mul]
      have := planeGroupU_le_centralizer hp2 le_rfl hPnd hP2 hPle hx
      rw [Subgroup.mem_centralizer_singleton_iff] at this
      rw [this]
    have hLx : (planeGroupU (GaloisField 3 2) 3 1 P).map Θ ∈
        centralizingMembers (conjClass3 K) {z * nd.w 0} :=
      (mem_centralizingMembers_pair.mp hLvis).1
    have hnc : ¬ Commutes N ((planeGroupU (GaloisField 3 2) 3 1 P).map Θ) :=
      hF1 N hN pKN pNJ _ hLvis hLK
    have hKL : Commutes K ((planeGroupU (GaloisField 3 2) 3 1 P).map Θ) := fun k hk y hy =>
      hΘ.commutes_K_range k hk y (Subgroup.map_le_range Θ _ hy)
    have hnKN : ¬ Commutes K N := by
      obtain ⟨W, hW⟩ := pKN
      exact not_commutes_of_linearBlockStandardPair hW
    obtain ⟨R_K, hR_K, hKimg⟩ := hNR K hKx (not_commutes_self3 c.hz)
    obtain ⟨R_N, hR_N, hNimg⟩ := hNR N hN hnKN
    obtain ⟨R_L, hR_L, hLimg⟩ := hvisR _ hLvis
    have hlin := X.stdPair_model hKx hN hR_K hR_N hKimg hNimg pKN
    have hcKL : Commutes R_K R_L := (X.commutes_iff_fund hKx hLx hR_K hKimg hLimg).mp hKL
    have hcLN : ¬ Commutes R_L R_N := fun h =>
      hnc ((X.commutes_iff_fund hN hLx hR_N hNimg hLimg).mpr (Gaps.commutes_symm h))
    have hneLN : R_L ≠ R_N := by
      intro h
      obtain ⟨W, hW⟩ := hlin
      exact not_commutes_of_linearBlockStandardPair hW (h ▸ hcKL)
    have hvv : v * v = 1 := by
      have := pow_orderOf_eq_one v
      rwa [hv.orderOf_eq_two, pow_two] at this
    have hv' : v⁻¹ = v := inv_eq_of_mul_eq_one_right hvv
    have hvY : v ∈ locLayer (conjClass3 K) (z * nd.w 0) := le_centralizingLayer hN hv.mem
    obtain ⟨r_v, hrv, hψv⟩ := X.exists_involution_of_fund hcf hN hR_N hNimg hv
    have hLnorm : ∀ x ∈ (planeGroupU (GaloisField 3 2) 3 1 P).map Θ,
        v * x * v⁻¹ ∈ (planeGroupU (GaloisField 3 2) 3 1 P).map Θ := by
      rintro _ ⟨y₁, hy₁, rfl⟩
      exact ⟨α y₁, hPstab y₁ hy₁, hα y₁⟩
    have hconjL : conjSub v ((planeGroupU (GaloisField 3 2) 3 1 P).map Θ) =
        (planeGroupU (GaloisField 3 2) 3 1 P).map Θ := by
      ext x
      rw [mem_conjSub_iff, hv']
      constructor
      · intro h
        have h1 := hLnorm _ h
        rw [hv'] at h1
        have : v * (v * x * v) * v = x := by
          calc v * (v * x * v) * v = (v * v) * x * (v * v) := by group
            _ = x := by rw [hvv]; group
        rwa [this] at h1
      · intro h
        have h1 := hLnorm _ h
        rwa [hv'] at h1
    have hnorm := X.normalizes_of_conjSub hR_L hLimg hvY hψv hconjL
    obtain ⟨W₂, hW₂⟩ := linear_pair_of_chain3_pOmegaMinus_five hR_K hR_N hR_L hlin hcKL hcLN
      hneLN hrv.1 hrv.2 hnorm
    have hy₀L : Θ y ∈ (planeGroupU (GaloisField 3 2) 3 1 P).map Θ :=
      Subgroup.mem_map_of_mem Θ hyS
    have hy₀Y : Θ y ∈ locLayer (conjClass3 K) (z * nd.w 0) := le_centralizingLayer hLx hy₀L
    obtain ⟨r, hrL, hψr⟩ : ∃ r ∈ R_L, X.ψ r = locElt (conjClass3 K) (z * nd.w 0) (Θ y) hy₀Y := by
      have : locElt (conjClass3 K) (z * nd.w 0) (Θ y) hy₀Y ∈ R_L.map X.ψ :=
        hLimg ▸ locElt_mem_locImg (le_centralizingLayer hLx) hy₀L
      obtain ⟨r, hr, hrψ⟩ := this
      exact ⟨r, hr, hrψ⟩
    have hvy : v * Θ y = Θ y * v := TE6Chart3.centralizes_of_fixed hα hαy
    have hlc : locElt (conjClass3 K) (z * nd.w 0) v hvY *
        locElt (conjClass3 K) (z * nd.w 0) (Θ y) hy₀Y =
        locElt (conjClass3 K) (z * nd.w 0) (Θ y) hy₀Y *
        locElt (conjClass3 K) (z * nd.w 0) v hvY := by
      unfold locElt
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext hvy
    have hcomm : r * r_v * r⁻¹ * r_v⁻¹ ∈
        Subgroup.center (Generic.modelUniv .POmegaMinus 5 3 1 Nat.prime_three).K := by
      apply X.ker_le
      rw [MonoidHom.mem_ker]
      simp only [map_mul, map_inv, hψr, hψv]
      rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul]
      exact hlc.symm
    have hr2 : r * r = 1 := sq_eq_one_of_comm_pair3 hW₂ hrv.1 hrv.2 hrL hcomm
    have hψ2 : locElt (conjClass3 K) (z * nd.w 0) (Θ y) hy₀Y *
        locElt (conjClass3 K) (z * nd.w 0) (Θ y) hy₀Y = 1 := by
      rw [← hψr, ← map_mul, hr2, map_one]
    have hsq : (⟨Θ y * Θ y, (locLayer _ _).mul_mem hy₀Y hy₀Y⟩ :
        locLayer (conjClass3 K) (z * nd.w 0)) = 1 := by
      refine eq_one_of_mk_eq_one_of_sq3 ?_ ?_
      · apply Subtype.ext
        show Θ y * Θ y * (Θ y * Θ y) = 1
        rw [← map_mul, ← map_mul]
        have : y * y * (y * y) = 1 := by
          have h4 : y ^ 4 = y ^ 2 * y ^ 2 := by rw [← pow_add]
          rw [pow_two] at h4
          rw [← h4]
          exact hy4
        rw [this, map_one]
      · rw [locElt_mul hy₀Y hy₀Y] at hψ2
        exact hψ2
    have hΘy : Θ (y * y) = 1 := by
      rw [map_mul]
      exact congrArg Subtype.val hsq
    have hcen : y * y ∈ Subgroup.center (Su (GaloisField 3 2) 3 1 6) :=
      hΘ.ker_le (MonoidHom.mem_ker.mpr hΘy)
    exact hy2 (eq_one_of_central_of_mem_planeGroupU3 hPnd hP2 hcen
      ((planeGroupU (GaloisField 3 2) 3 1 P).mul_mem hyS hyS))
  ·
    rw [h1] at ha
    have hfix := alpha_fixes_te6Node_of_skew (p := 3) (f := 1) hp2 hmat hiso ha hW
    have hj0 : (te6Node 3 1).map Θ = nd.j 0 := by
      show (LcU (GaloisField 3 2) 3 1 (nodePair 5 0 (by norm_num))).map Θ = nd.j 0
      rw [← range_blockEmb2_eq_LcU_nodePair two_ne_zero_gf9 (by norm_num : 0 < 5)]
      exact hΘ.block ⟨0, by norm_num⟩
    have hMv : nd.j 0 ≤ Subgroup.centralizer ({v} : Set G) := by
      rw [← hj0]
      rintro _ ⟨x, hx, rfl⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (TE6Chart3.centralizes_of_fixed hα (hfix x hx)).symm
    have hcomm := commutes_member_of_centralizes3 c hsingle hshape hN.1 hv pKN
      (nd.mem 0 h0) (nd.commK 0 h0) hMv
    obtain ⟨W', hW'⟩ := pNJ
    exact not_commutes_of_linearBlockStandardPair hW' hcomm

end Main

end CFSG.ClassicalInvolution.Q3.Q3E6T
