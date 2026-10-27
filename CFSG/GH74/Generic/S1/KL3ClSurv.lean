module

public import CFSG.GH74.Generic.S1.KL3SurvDef
public import CFSG.GH74.Generic.S1.KL3Lift
public import CFSG.GH74.Generic.S1.KL3ClCent
public import CFSG.RankThree.PartOne.AUTSL.Interface
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk94G4ExL4

public section

open Subgroup CFSG CFSG.GH74 CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.ComponentClassification.CatalogueBHigherLinearAction (slConjugation slConjugation_matrix)
open CFSG.ComponentClassification.CatalogueBGraphForm (slGraphAut slGraphAut_matrix)
open CFSG.GH74.GLS.IVK.Proofs2.Ivk94
open scoped MatrixGroups Matrix commutatorElement

namespace CFSG.GH74.Generic.S1

theorem kl3cls_lift (hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels)
    {S : Type} [Group S] {K : Type} [Field K] [Finite K] (e : S ≃* LinearFlag.projectiveSL 4 K)
    {F : Type} [Field F] [Finite F] (hF : Nat.card F = 3) (Pb : Subgroup S)
    (ePb : ↥Pb ≃* SL(3, F)) :
    ∃ θ : SL(3, F) →* SL(4, K), Function.Injective θ ∧
      ∀ g, LinearFlag.proj 4 K (θ g) = e ((ePb.symm g : ↥Pb) : S) := by
  let π : SL(4, K) →* S := e.symm.toMonoidHom.comp (LinearFlag.proj 4 K)
  have hπ : Function.Surjective π := fun s => by
    obtain ⟨x, hx⟩ := LinearFlag.proj_surjective 4 K (e s)
    exact ⟨x, by simp [π, hx]⟩
  have hker : π.ker ≤ Subgroup.center SL(4, K) := by
    intro x hx
    have h1 : LinearFlag.proj 4 K x = 1 := by
      have : e.symm (LinearFlag.proj 4 K x) = 1 := hx
      simpa using this
    rw [← LinearFlag.scalars_eq_center]
    exact LinearFlag.proj_eq_one_iff.1 h1
  obtain ⟨θ, hθinj, hθ⟩ := kl3_exists_lift hGA π hπ hker hF Pb ePb
  refine ⟨θ, hθinj, fun g => ?_⟩
  have := congrArg e (hθ g)
  simpa [π] using this

theorem kl3cls_comm_central {Γ : Type*} [Group Γ] (x y z w : Γ) (hz : z ∈ Subgroup.center Γ)
    (hw : w ∈ Subgroup.center Γ) : ⁅x * z, y * w⁆ = ⁅x, y⁆ := by
  have hz' := Subgroup.mem_center_iff.1 hz
  have hw' := Subgroup.mem_center_iff.1 hw
  have h1 : z * (y * w) * z⁻¹ = y * w := by rw [← hz' (y * w), mul_inv_cancel_right]
  have h2 : w * x⁻¹ * w⁻¹ = x⁻¹ := by rw [← hw' x⁻¹, mul_inv_cancel_right]
  simp only [commutatorElement_def]
  calc x * z * (y * w) * (x * z)⁻¹ * (y * w)⁻¹
      = x * (z * (y * w) * z⁻¹) * x⁻¹ * (w⁻¹ * y⁻¹) := by group
    _ = x * (y * w) * x⁻¹ * (w⁻¹ * y⁻¹) := by rw [h1]
    _ = x * y * (w * x⁻¹ * w⁻¹) * y⁻¹ := by group
    _ = x * y * x⁻¹ * y⁻¹ := by rw [h2]

theorem kl3cls_eq_of_central {G Γ : Type*} [Group G] [Group Γ] [Group.IsPerfect G]
    (φ ψ : G →* Γ) (h : ∀ g, ∃ z ∈ Subgroup.center Γ, φ g = ψ g * z) : φ = ψ := by
  have htop : ⁅(⊤ : Subgroup G), (⊤ : Subgroup G)⁆ = ⊤ := Group.IsPerfect.commutator_eq_top
  have hle : (⊤ : Subgroup G) ≤ φ.eqLocus ψ := by
    rw [← htop, Subgroup.commutator_le]
    intro a _ b _
    obtain ⟨za, hza, ha⟩ := h a
    obtain ⟨zb, hzb, hb⟩ := h b
    show φ ⁅a, b⁆ = ψ ⁅a, b⁆
    rw [map_commutatorElement, map_commutatorElement, ha, hb,
      kl3cls_comm_central _ _ _ _ hza hzb]
  ext g
  exact hle (Subgroup.mem_top g)

theorem kl3cls_elems {K : Type*} [Field K] [Finite K] (hK : Nat.card K = 3) (x : K) :
    x = 0 ∨ x = 1 ∨ x = -1 := by
  classical
  have : Fintype K := Fintype.ofFinite K
  have hcard : Fintype.card K = 3 := by rw [← Nat.card_eq_fintype_card]; exact hK
  have hchar : CharP K 3 := charP_of_card_eq_prime_pow (p := 3) (f := 1) (by simpa using hcard)
  have h2 : (2 : K) ≠ 0 := by
    intro h
    have : (3 : ℕ) ∣ 2 := (CharP.cast_eq_zero_iff K 3 2).1 (by exact_mod_cast h)
    omega
  have h10 : (1 : K) ≠ 0 := one_ne_zero
  have h1m : (1 : K) ≠ -1 := by
    intro h
    apply h2
    have : (1 : K) + 1 = 0 := by nth_rewrite 2 [h]; simp
    simpa [one_add_one_eq_two] using this
  have h0m : (0 : K) ≠ -1 := by
    intro h
    exact one_ne_zero (neg_eq_zero.1 h.symm)
  have hs : ({0, 1, -1} : Finset K).card = 3 := by
    rw [Finset.card_insert_of_notMem, Finset.card_pair h1m]
    simp [h10.symm, h0m]
  have huniv : ({0, 1, -1} : Finset K) = Finset.univ :=
    Finset.eq_univ_of_card _ (by rw [hs, hcard])
  have hx : x ∈ ({0, 1, -1} : Finset K) := by rw [huniv]; exact Finset.mem_univ x
  simpa using hx

theorem kl3cls_ringEquiv {K : Type*} [Field K] [Finite K] (hK : Nat.card K = 3) (σ : K ≃+* K) :
    σ = 1 := by
  refine RingEquiv.ext fun x => ?_
  rcases kl3cls_elems hK x with rfl | rfl | rfl <;> simp


theorem kl3cls_alpha_trivial (hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels)
    {S : Type} [Group S] {K : Type} [Field K] [Finite K] (hK : Nat.card K = 3)
    (e : S ≃* LinearFlag.projectiveSL 4 K) {F : Type} [Field F] [Finite F] (hF : Nat.card F = 3)
    (Pb : Subgroup S) (ePb : ↥Pb ≃* SL(3, F)) (α : MulAut S) (hodd : Odd (orderOf α))
    (hfix : ∀ p ∈ Pb, α p = p) : α = 1 := by
  obtain ⟨θ, hθinj, hθ⟩ := kl3cls_lift hGA e hF Pb ePb
  obtain ⟨A, σ, ε, hε, hα⟩ :=
    CFSG.RankThree.PartOne.AUTSL.exists_std_apply_of_mulEquiv (by norm_num : 3 ≤ 4) e α
  have hσ : σ = 1 := kl3cls_ringEquiv hK σ
  have hfa : LinearFlag.fieldAut 4 K σ = 1 := by rw [hσ, map_one]
  have hperf : Group.IsPerfect SL(3, F) := kl3_isPerfect_sl3
  have hfixg : ∀ g : SL(3, F), e (α ((ePb.symm g : ↥Pb) : S)) = LinearFlag.proj 4 K (θ g) := by
    intro g
    rw [hfix _ (ePb.symm g).2, hθ g]
  have hcard4 : Fintype.card (Fin 4) = 4 := Fintype.card_fin 4
  let ρ : SL(3, F) →* GL (Fin 4) K := Matrix.SpecialLinearGroup.toGL.comp θ
  have hρinj : Function.Injective ρ := Matrix.SpecialLinearGroup.toGL_injective.comp hθinj
  have hρval : ∀ g, ((ρ g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
      ((θ g : SL(4, K)) : Matrix (Fin 4) (Fin 4) K) := fun g => rfl
  interval_cases ε
  ·
    have hconj : ∀ x, e (α x) = LinearFlag.conjAut 4 K A (e x) := by
      intro x
      rw [hα x, hfa]
      simp
    have hrel : ∀ g, slConjugation 4 K A (θ g) = θ g := by
      have hφ : ((slConjugation 4 K A : MulAut SL(4, K)) : SL(4, K) →* SL(4, K)).comp θ = θ := by
        refine kl3cls_eq_of_central _ _ (fun g => ?_)
        have h1 := hconj ((ePb.symm g : ↥Pb) : S)
        rw [hfix _ (ePb.symm g).2, ← hθ g, LinearFlag.conjAut_proj] at h1
        have h2 := LinearFlag.proj_eq_proj_iff.1 h1
        refine ⟨(θ g)⁻¹ * slConjugation 4 K A (θ g), ?_, by simp⟩
        rw [← LinearFlag.scalars_eq_center]
        exact h2
      intro g
      exact congrArg (fun f : SL(3, F) →* SL(4, K) => f g) hφ
    have hcomm : ∀ g, A * ρ g = ρ g * A := by
      intro g
      apply Units.ext
      have h := congrArg (fun x : SL(4, K) => (x : Matrix (Fin 4) (Fin 4) K)) (hrel g)
      simp only [slConjugation_matrix] at h
      rw [Units.val_mul, Units.val_mul, hρval]
      calc (A : Matrix (Fin 4) (Fin 4) K) * (θ g : Matrix (Fin 4) (Fin 4) K)
          = (A : Matrix (Fin 4) (Fin 4) K) * (θ g : Matrix (Fin 4) (Fin 4) K) *
              (((A⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *
                (A : Matrix (Fin 4) (Fin 4) K)) := by
            rw [Units.inv_mul, Matrix.mul_one]
        _ = ((A : Matrix (Fin 4) (Fin 4) K) * (θ g : Matrix (Fin 4) (Fin 4) K) *
              ((A⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)) *
                (A : Matrix (Fin 4) (Fin 4) K) := by
            simp only [Matrix.mul_assoc]
        _ = (θ g : Matrix (Fin 4) (Fin 4) K) * (A : Matrix (Fin 4) (Fin 4) K) := by rw [h]
    obtain ⟨g, h, hg13, hgne, hhg⟩ := kl3cl_frob F hF
    have hsq : A * A = 1 := by
      refine kl3clc_sq_eq_one hK hcard4 (ρ g) (ρ h) A ?_ ?_ ?_ (hcomm g) (hcomm h)
      · rw [← map_pow, hg13, map_one]
      · intro h1
        exact hgne (hρinj (by rw [h1, map_one]))
      · rw [← map_mul, ← map_pow, ← map_mul, hhg]
    have hconj2 : ∀ y, LinearFlag.conjAut 4 K A (LinearFlag.conjAut 4 K A y) = y := fun y => by
      rw [← MulAut.mul_apply, ← map_mul, hsq, map_one, MulAut.one_apply]
    have hα2 : α ^ 2 = 1 := by
      ext x
      apply e.injective
      rw [pow_two, MulAut.mul_apply, hconj, hconj, hconj2, MulAut.one_apply]
    have hord : orderOf α ∣ 2 := orderOf_dvd_of_pow_eq_one hα2
    have h1 : orderOf α = 1 := by
      have := Nat.le_of_dvd (by norm_num) hord
      obtain ⟨k, hk⟩ := hodd
      omega
    exact orderOf_eq_one_iff.1 h1
  ·
    exfalso
    have hdual : ∀ x, e (α x) = LinearFlag.conjAut 4 K A (LinearFlag.dualAut 4 K (e x)) := by
      intro x
      rw [hα x, hfa]
      simp
    have hrel : ∀ g, slConjugation 4 K A ((θ g)⁻¹.transpose) = θ g := by
      have hφ : ((slConjugation 4 K A * slGraphAut 4 K : MulAut SL(4, K)) :
          SL(4, K) →* SL(4, K)).comp θ = θ := by
        refine kl3cls_eq_of_central _ _ (fun g => ?_)
        have h1 := hdual ((ePb.symm g : ↥Pb) : S)
        rw [hfix _ (ePb.symm g).2, ← hθ g, LinearFlag.dualAut_proj,
          LinearFlag.conjAut_proj] at h1
        have h2 := LinearFlag.proj_eq_proj_iff.1 h1
        refine ⟨(θ g)⁻¹ * (slConjugation 4 K A ((θ g)⁻¹.transpose)), ?_, by simp; rfl⟩
        rw [← LinearFlag.scalars_eq_center]
        exact h2
      intro g
      exact congrArg (fun f : SL(3, F) →* SL(4, K) => f g) hφ
    have : Fintype K := Fintype.ofFinite K
    have hcard : Fintype.card K = 3 := by
      rw [← Nat.card_eq_fintype_card]
      exact hK
    have hchar : CharP K 3 := charP_of_card_eq_prime_pow (p := 3) (f := 1) (by simpa using hcard)
    have hform : ∀ g : SL(3, F),
        ((ρ g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)ᵀ *
          (((A⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K))ᵀ *
          ((ρ g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
          (((A⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K))ᵀ := by
      intro g
      have h := congrArg (fun x : SL(4, K) => (x : Matrix (Fin 4) (Fin 4) K)) (hrel g)
      simp only [slConjugation_matrix, Matrix.SpecialLinearGroup.coe_transpose] at h
      rw [hρval]
      have hNM : (((θ g)⁻¹ : SL(4, K)) : Matrix (Fin 4) (Fin 4) K) *
          ((θ g : SL(4, K)) : Matrix (Fin 4) (Fin 4) K) = 1 := by
        rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one]
      have hAiAv : ((A⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *
          (A : Matrix (Fin 4) (Fin 4) K) = 1 := by
        rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
      have hAvAi : (A : Matrix (Fin 4) (Fin 4) K) *
          ((A⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = 1 := by
        rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
      generalize (((θ g)⁻¹ : SL(4, K)) : Matrix (Fin 4) (Fin 4) K) = N at h hNM
      generalize ((θ g : SL(4, K)) : Matrix (Fin 4) (Fin 4) K) = M at h hNM ⊢
      generalize ((A⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = Ai at h hAiAv hAvAi ⊢
      generalize (A : Matrix (Fin 4) (Fin 4) K) = Av at h hAiAv hAvAi
      have hT : Nᵀ = Ai * M * Av := by
        calc Nᵀ = (Ai * Av) * Nᵀ * (Ai * Av) := by rw [hAiAv, Matrix.one_mul, Matrix.mul_one]
          _ = Ai * (Av * Nᵀ * Ai) * Av := by simp only [Matrix.mul_assoc]
          _ = Ai * M * Av := by rw [h]
      have hN : N = Avᵀ * (Mᵀ * Aiᵀ) := by
        have h1 := congrArg Matrix.transpose hT
        rw [Matrix.transpose_transpose, Matrix.transpose_mul, Matrix.transpose_mul] at h1
        exact h1
      have hAA : Aiᵀ * Avᵀ = 1 := by
        rw [← Matrix.transpose_mul, hAvAi, Matrix.transpose_one]
      calc Mᵀ * Aiᵀ * M = (Aiᵀ * Avᵀ) * (Mᵀ * Aiᵀ * M) := by rw [hAA, Matrix.one_mul]
        _ = Aiᵀ * (Avᵀ * (Mᵀ * Aiᵀ) * M) := by simp only [Matrix.mul_assoc]
        _ = Aiᵀ * (N * M) := by rw [hN]
        _ = Aiᵀ := by rw [hNM, Matrix.mul_one]
    have hJ : ((((A⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K))ᵀ).det ≠ 0 := by
      rw [Matrix.det_transpose]
      exact ((Matrix.isUnit_iff_isUnit_det _).1 (Units.isUnit (A⁻¹))).ne_zero
    have hcs := kl3cl_card_ge_six_sp (K := K) (ι := Fin 4) (F := F) hF ρ hρinj _ hJ hform
    rw [hcard4] at hcs
    omega

theorem kl3cls_exists_E {S : Type} [Group S] [Finite S] (hL : LieModel S .PSL 4 3 1) :
    ∃ E : Subgroup S, CFSG.Open.IsElemAbelian 2 E ∧ 4 < Nat.card E := by
  obtain ⟨-, F, _, _, hcard, ⟨e⟩⟩ := statedClassicalModel_of_lieModel (by norm_num) hL
  have hodd : Odd (Nat.card F) := by rw [hcard]; norm_num
  obtain ⟨E, hE2, hE16⟩ := exists_E16_of_equiv e
    (exists_E16_pauli (CFSG.GH74.GLS.neg_one_ne_one_of_odd_card F hodd) fun i =>
      Subgroup.subset_closure (det_pauli i))
  refine ⟨E, ⟨⟨⟨fun a b => ?_⟩⟩, hE2⟩, by rw [hE16]; norm_num⟩
  apply Subtype.ext
  have ha := hE2 a.1 a.2
  have hb := hE2 b.1 b.2
  have hab := hE2 (a * b).1 (a * b).2
  simp only [Subgroup.coe_mul, pow_two] at ha hb hab
  have hia : (a : S)⁻¹ = a := inv_eq_of_mul_eq_one_right ha
  have hib : (b : S)⁻¹ = b := inv_eq_of_mul_eq_one_right hb
  have h1 : (a : S) * b = ((a : S) * b)⁻¹ := (inv_eq_of_mul_eq_one_right hab).symm
  rw [mul_inv_rev, hia, hib] at h1
  exact h1

theorem kl3SurvL4 (hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels) :
    KL3SurvL4 := by
  intro S _ _ hL F _ _ hF Pb hPb
  obtain ⟨ePb⟩ := hPb
  refine ⟨fun α hodd hfix => ?_, kl3cls_exists_E hL⟩
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := CFSG.RankThree.PartOne.AUTSL.exists_projectiveSL_equiv_of_lieModel hL
  exact kl3cls_alpha_trivial hGA (by simpa using hK) e hF Pb ePb α hodd hfix

end CFSG.GH74.Generic.S1
