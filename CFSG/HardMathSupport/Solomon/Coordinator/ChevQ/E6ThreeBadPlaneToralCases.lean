module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeBadPlaneToralClass
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeBadPlaneToralFrames

public noncomputable section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

open Matrix CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Seitz
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.RankThree.PartOne.KF4 CFSG.RankThree.PartOne.KE
open scoped MatrixGroups

set_option linter.unusedSectionVars false

section Cases

variable
  {K : Type} [Field K]

@[expose] def E6ToralCaseB (ω : Kˣ) : Prop :=
  ω ^ 3 = 1 → ω ≠ 1 →
  ∀ (ρ : Fin 3 → SpecialLinearGroup (Fin 3) K →* ModGL Tag.E6 K)
    (σ : Fin 3 → Fin 3 → Fin 3 → Fin Tag.E6.rank → ℤ),
    (∀ i, IsA2Frame (ρ i) (σ i)) → (∀ i, (ρ i).range = e6LineFactor K i) →
    (∀ i, σ i 0 1 = (e6LinePair i).1) → (∀ i, σ i 1 2 = (e6LinePair i).2) →
    (∀ i, ρ i signedCycSL ∈ monomialSubgroup Tag.E6 K) →
    ∀ (c : Fin Tag.E6.rank → Kˣ) (w : Fin 3 → SpecialLinearGroup (Fin 3) K)
      (d : Fin 3 → Fin 3 → K) (n : Fin 3 → ℕ),
    (∀ i, ((diagGL3 fun j => rootChar c (σ i j 0) : GL (Fin 3) K) :
        Matrix (Fin 3) (Fin 3) K) * (w i : Matrix (Fin 3) (Fin 3) K) =
        diagonal (d i) * signedCycMat ^ n i) →
    (∃ i, ¬ 3 ∣ n i) → (∀ i, 3 ∣ n i → ∃ a b, d i a ≠ d i b) →
    Module.finrank K ↥(LinearMap.ker
        (((rootDiagUnit Tag.E6 c * (ρ 0 (w 0) * ρ 1 (w 1) * ρ 2 (w 2)) : ModGL Tag.E6 K) :
          Module.End K (RootModule Tag.E6 K)) - 1) ⊓
      LinearMap.ker ((rootDiagUnit Tag.E6 (e6LineChar ω) : Module.End K (RootModule Tag.E6 K)) - 1))
      ≤ 11

namespace ToralFrames

variable {ω : Kˣ} (T : ToralFrames K ω)

@[expose] def w (c : Fin Tag.E6.rank → Kˣ) (x z : Fin 3 → SpecialLinearGroup (Fin 3) K) :
    Fin 3 → SpecialLinearGroup (Fin 3) K :=
  fun i => conjSL (T.D i c)⁻¹ (z i) * x i * (z i)⁻¹

theorem coe_D_mul_w (c : Fin Tag.E6.rank → Kˣ) (x z : Fin 3 → SpecialLinearGroup (Fin 3) K)
    (i : Fin 3) :
    ((T.D i c : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
        ((T.w c x z i : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      ((SpecialLinearGroup.toGL (z i) * (T.D i c * SpecialLinearGroup.toGL (x i)) *
        (SpecialLinearGroup.toGL (z i))⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
  rw [← T.D_mul_toGL_w c x z i, Units.val_mul]
  rfl

theorem det_D (c : Fin Tag.E6.rank → Kˣ) (i : Fin 3) :
    GeneralLinearGroup.det (T.D i c) = e6DetChar c i := by
  have h00 : T.σ i 0 0 = 0 := by rw [(T.frame i).eq_sub 0 0, sub_self]
  have h10 : T.σ i 1 0 = -(e6LinePair i).1 := by rw [(T.frame i).neg 0 1, T.h01]
  have h20 : T.σ i 2 0 = -((e6LinePair i).1 + (e6LinePair i).2) := by
    rw [(T.frame i).neg 0 2, ← (T.frame i).add 0 1 2, T.h01, T.h12]
  apply Units.ext
  rw [GeneralLinearGroup.val_det_apply]
  change Matrix.det (Matrix.diagonal fun j => (rootChar c (T.σ i j 0) : K)) = _
  rw [Matrix.det_diagonal, Fin.prod_univ_three, h00, h10, h20, rootChar_zero, e6DetChar,
    Units.val_mul, Units.val_one, one_mul]

theorem det_conj_gamma (c : Fin Tag.E6.rank → Kˣ) (x z : Fin 3 → SpecialLinearGroup (Fin 3) K)
    (i : Fin 3) :
    Matrix.det ((SpecialLinearGroup.toGL (z i) * (T.D i c * SpecialLinearGroup.toGL (x i)) *
        (SpecialLinearGroup.toGL (z i))⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      (e6DetChar c i : K) := by
  rw [← GeneralLinearGroup.val_det_apply, map_mul, map_mul, map_inv, mul_inv_cancel_comm, map_mul,
    T.det_D]
  have h1 : GeneralLinearGroup.det (SpecialLinearGroup.toGL (x i)) = 1 := by
    apply Units.ext
    rw [GeneralLinearGroup.val_det_apply, SpecialLinearGroup.coe_GL_coe_matrix, (x i).2]
    rfl
  rw [h1, mul_one]

theorem conj_mem_torusGroup {c : Fin Tag.E6.rank → Kˣ}
    {x z : Fin 3 → SpecialLinearGroup (Fin 3) K}
    (hcT : rootDiagUnit Tag.E6 c ∈ torusGroup Tag.E6 K) (d : Fin 3 → Fin 3 → K)
    (hdiag : ∀ i, ((SpecialLinearGroup.toGL (z i) * (T.D i c * SpecialLinearGroup.toGL (x i)) *
        (SpecialLinearGroup.toGL (z i))⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
        diagonal (d i)) :
    T.π z * (rootDiagUnit Tag.E6 c * T.π x) * (T.π z)⁻¹ ∈ torusGroup Tag.E6 K := by
  have hoff : ∀ i, ∀ a b : Fin 3, a ≠ b →
      ((T.w c x z i : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) a b = 0 := by
    intro i a b hab
    have h := congrFun (congrFun (T.coe_D_mul_w c x z i) a) b
    rw [hdiag i, Matrix.diagonal_apply_ne _ hab] at h
    have h' : ((Matrix.diagonal fun j => (rootChar c (T.σ i j 0) : K)) *
        ((T.w c x z i : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) a b = 0 := h
    rw [Matrix.diagonal_mul] at h'
    exact (mul_eq_zero.1 h').resolve_left (Units.ne_zero _)
  rw [T.conj_eq]
  refine mul_mem hcT ?_
  rw [T.π_apply]
  exact mul_mem (mul_mem ((T.frame 0).diag _ (hoff 0)) ((T.frame 1).diag _ (hoff 1)))
    ((T.frame 2).diag _ (hoff 2))

end ToralFrames

theorem e6Toral_core {ω : Kˣ} (hw3 : ω ^ 3 = 1) (hw1 : ω ≠ 1) (hB : E6ToralCaseB ω)
    {u : ModGL Tag.E6 K} (huM : u ∈ toralRootGroup Tag.E6 K (e6LineChar ω)) (hu3 : u ^ 3 = 1)
    (hdim : Module.finrank K ↥(LinearMap.ker ((u : Module.End K (RootModule Tag.E6 K)) - 1) ⊓
      LinearMap.ker ((rootDiagUnit Tag.E6 (e6LineChar ω) : Module.End K (RootModule Tag.E6 K)) -
        1)) = 12) :
    ∃ y ∈ toralRootGroup Tag.E6 K (e6LineChar ω), ∃ b : Fin Tag.E6.rank → Kˣ,
      (∀ i, b i ^ 3 = 1) ∧ y * u * y⁻¹ = rootDiagUnit Tag.E6 b := by
  obtain ⟨T⟩ := exists_toralFrames (K := K) hw3 hw1
  obtain ⟨c, x, hcT, rfl⟩ := T.dec u huM
  obtain ⟨t, ht⟩ := exists_cartanChar_eq_of_mem_torusGroup hcT
  have hct : c = cartanChar t :=
    CFSG.LieType.Chevalley.rootDiagUnit_injective (τ := Tag.E6) (K := K) ht
  subst hct
  have hζ : ∃ ζ : K, IsPrimitiveRoot ζ 3 := by
    have h3 : ((ω : Kˣ) : K) ^ 3 = 1 := by rw [← Units.val_pow_eq_pow_val, hw3, Units.val_one]
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have hne : ((ω : Kˣ) : K) ≠ 1 := fun h => hw1 (Units.ext h)
    refine ⟨(ω : K), ?_⟩
    have := orderOf_eq_prime h3 hne
    rw [← this]
    exact IsPrimitiveRoot.orderOf _
  choose α hα using T.exists_cube_scalar hu3
  choose z d n hconj hnc hc0 using fun i => exists_norm_form hζ (hα i)
  have hconjeq : T.π z * (rootDiagUnit Tag.E6 (cartanChar t) * T.π x) * (T.π z)⁻¹ =
      rootDiagUnit Tag.E6 (cartanChar t) * T.π (T.w (cartanChar t) x z) := T.conj_eq _ x z
  have hyM := T.π_mem z
  by_cases hA : ∀ i, ∃ μ : K, μ ^ 3 = α i
  ·
    have hdiag : ∀ i, ((SpecialLinearGroup.toGL (z i) * (T.D i (cartanChar t) *
        SpecialLinearGroup.toGL (x i)) * (SpecialLinearGroup.toGL (z i))⁻¹ : GL (Fin 3) K) :
          Matrix (Fin 3) (Fin 3) K) = diagonal (d i) := fun i => by
      rw [hconj i, hc0 i (hA i), pow_zero, Matrix.mul_one]
    have hT := T.conj_mem_torusGroup hcT d hdiag
    obtain ⟨b, hb⟩ := MonoidHom.mem_range.1 (torusGroup_le_range_rootDiagUnitHom_E6 hT)
    have hb' : rootDiagUnit Tag.E6 b = T.π z * (rootDiagUnit Tag.E6 (cartanChar t) * T.π x) *
        (T.π z)⁻¹ := hb
    refine ⟨T.π z, hyM, b, ?_, hb'.symm⟩
    have h3b : rootDiagUnit Tag.E6 (b ^ 3) = rootDiagUnit Tag.E6 (1 : Fin Tag.E6.rank → Kˣ) := by
      have e : rootDiagUnit Tag.E6 (b ^ 3) = (rootDiagUnit Tag.E6 b : ModGL Tag.E6 K) ^ 3 :=
        map_pow (rootDiagUnitHom Tag.E6 K) b 3
      rw [e, hb', conj_pow, hu3, mul_one, mul_inv_cancel, rootDiagUnit_one]
    intro i
    have := congrFun
      (CFSG.LieType.Chevalley.rootDiagUnit_injective (τ := Tag.E6) (K := K) h3b) i
    simpa using this
  ·
    exfalso
    obtain ⟨j, hj⟩ := not_forall.1 hA
    have hjnc : ∀ μ : K, μ ^ 3 ≠ α j := fun μ hμ => hj ⟨μ, hμ⟩
    obtain ⟨hn3j, hprod⟩ := hnc j hjnc
    have hdet : ∀ i, d i 0 * d i 1 * d i 2 = (e6DetChar (cartanChar t) i : K) := fun i => by
      rw [← T.det_conj_gamma (cartanChar t) x z i, hconj i, Matrix.det_mul, Matrix.det_diagonal,
        Fin.prod_univ_three, det_pow, det_signedCycMat, one_pow, mul_one]
    have hncj : ∀ μ : K, μ ^ 3 ≠ (e6DetChar (cartanChar t) j : K) := fun μ => by
      rw [← hdet j, hprod]
      exact hjnc μ
    have hsc : ∀ i, 3 ∣ n i → ∃ a b, d i a ≠ d i b := by
      intro i _
      by_contra hcon
      have hall : ∀ a b, d i a = d i b := fun a b => by
        by_contra hab
        exact hcon ⟨a, b, hab⟩
      apply e6DetChar_not_cube_spread t hncj i (d i 0)
      rw [← hdet i, hall 1 0, hall 2 0]
      ring
    have hDw : ∀ i, ((diagGL3 fun k => rootChar (cartanChar t) (T.σ i k 0) : GL (Fin 3) K) :
        Matrix (Fin 3) (Fin 3) K) * ((T.w (cartanChar t) x z i : SpecialLinearGroup (Fin 3) K) :
          Matrix (Fin 3) (Fin 3) K) = diagonal (d i) * signedCycMat ^ n i := fun i => by
      rw [← hconj i]
      exact T.coe_D_mul_w (cartanChar t) x z i
    have hbound := hB hw3 hw1 T.ρ T.σ T.frame T.range T.h01 T.h12 T.mono (cartanChar t)
      (T.w (cartanChar t) x z) d n hDw ⟨j, hn3j⟩ hsc
    rw [← T.π_apply, ← hconjeq] at hbound
    obtain ⟨-, hyc⟩ := mem_toralCentralizer.1 (toralRootGroup_le (e6LineChar ω) hyM)
    have hcomm : T.π z * rootDiagUnit Tag.E6 (e6LineChar ω) =
        rootDiagUnit Tag.E6 (e6LineChar ω) * T.π z := by
      calc T.π z * rootDiagUnit Tag.E6 (e6LineChar ω)
          = (rootDiagUnit Tag.E6 (e6LineChar ω) * T.π z *
              (rootDiagUnit Tag.E6 (e6LineChar ω))⁻¹) * rootDiagUnit Tag.E6 (e6LineChar ω) := by
            rw [hyc]
        _ = rootDiagUnit Tag.E6 (e6LineChar ω) * T.π z := by group
    rw [finrank_ker_inf_conj_sub_one (T.π z) _ _ hcomm, hdim] at hbound
    omega

end Cases

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

end
