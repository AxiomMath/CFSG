module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofEndOddLieOInner
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofEndOddLieOPump
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofEndOddLieLCore
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofEndOddLieOSpace

public noncomputable section

namespace CFSG.ComponentClassification.CatLeafProof.EndOddO

open Subgroup Matrix Module CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.OddClassSelector CFSG.ComponentClassification.RestrictedStd
open CFSG.ComponentClassification.FooteLit

variable {K : Type} [Field K] {d : ℕ}

theorem forall_of_eq_eigenspace {V : Type} [AddCommGroup V] [Module K V] {M : Submodule K V}
    {A : V ≃ₗ[K] V} {s : K} (h : M = Module.End.eigenspace A.toLinearMap s) :
    ∀ m ∈ M, A m = s • m := by
  rw [h]
  intro m hm
  exact Module.End.mem_eigenspace_iff.mp hm

theorem ext_false [Finite K] (Q : QuadraticForm K (Fin d → K)) (Z : matrixDerived Q)
    {K₀ : Subgroup (matrixProjectiveDerived Q)}
    (hYK : (liftHat Q K₀).map (matrixProjectiveProjection Q) = K₀)
    (hsol : Group.IsSolvable ↥(centralizer
      ({matrixProjectiveProjection Q Z} : Set (matrixProjectiveDerived Q)) ⊓
        centralizer (K₀ : Set (matrixProjectiveDerived Q))))
    {s : K} {M F : Submodule K (Fin d → K)}
    (hMeig : M = Module.End.eigenspace (matrixLinearEquiv Z.val).toLinearMap s)
    (hFeig : F = Module.End.eigenspace (matrixLinearEquiv Z.val).toLinearMap (-s))
    (hMF : IsCompl M F) (horth : ∀ m ∈ M, ∀ f ∈ F, QuadraticMap.polar Q m f = 0)
    (hYF : ∀ y ∈ (liftHat Q K₀).map (derivedLinear Q), ∀ f ∈ F, y f = f)
    (hYM : ∀ y ∈ (liftHat Q K₀).map (derivedLinear Q), ∀ m ∈ M, y m ∈ M) (hM0 : M ≠ ⊥)
    {L : Subgroup (TauCeti.QuadraticMap.orthogonalGroup (Q.comp F.subtype))}
    (hL : CFSG.IsQuasisimple L) : False := by
  obtain ⟨G, hG, hGO, hGM, hGF⟩ := exists_ext_subgroup hMF horth hL
  obtain ⟨v, hvM, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hM0
  refine false_of_quasisimple_commuting Q Z hYK hsol hG hGO (fun g hg => ?_)
    (fun g hg y hy => ?_) hv0 (fun g hg => hGM g hg v hvM)
  · rw [derivedLinear_eq]
    exact commute_of_eigen hMF (forall_of_eq_eigenspace hMeig) (forall_of_eq_eigenspace hFeig)
      (fun m hm => by rw [hGM g hg m hm]; exact hm) (hGF g hg)
  · exact commute_of_blocks hMF (hGM g hg) (hGF g hg) (hYF _ ⟨y, hy, rfl⟩)
      (hYM _ ⟨y, hy, rfl⟩)

theorem pump_false [Finite K] {ℓ e : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (he : 1 ≤ e)
    (hK : Nat.card K = ℓ ^ e) (hq3 : Nat.card K = 3) (hd : 7 ≤ d)
    {Q : QuadraticForm K (Fin d → K)} (hQ : Q.polarBilin.Nondegenerate) (Z : matrixDerived Q)
    {K₀ D : Subgroup (matrixProjectiveDerived Q)}
    (hcfg : EndOddCore.Config (matrixProjectiveProjection Q Z) K₀ D)
    (hK₀q : CFSG.IsQuasisimple K₀) (hYq : ⁅liftHat Q K₀, liftHat Q K₀⁆ = liftHat Q K₀)
    (hYK : (liftHat Q K₀).map (matrixProjectiveProjection Q) = K₀)
    {s : K} {M F : Submodule K (Fin d → K)} (hs1 : s * s = 1)
    (hMeig : M = Module.End.eigenspace (matrixLinearEquiv Z.val).toLinearMap s)
    (hFeig : F = Module.End.eigenspace (matrixLinearEquiv Z.val).toLinearMap (-s))
    (hMF : IsCompl M F) (horth : ∀ m ∈ M, ∀ f ∈ F, QuadraticMap.polar Q m f = 0)
    (hMnd : (LinearMap.BilinForm.restrict Q.polarBilin M).Nondegenerate)
    (hFnd : (LinearMap.BilinForm.restrict Q.polarBilin F).Nondegenerate)
    (hYF : ∀ y ∈ (liftHat Q K₀).map (derivedLinear Q), ∀ f ∈ F, y f = f)
    (ρ : (liftHat Q K₀).map (derivedLinear Q) →*
      TauCeti.QuadraticMap.orthogonalGroup (Q.comp M.subtype))
    (hρ : ∀ (y : (liftHat Q K₀).map (derivedLinear Q)) (m : M),
      (((ρ y).val m : M) : Fin d → K) = (y : (Fin d → K) ≃ₗ[K] (Fin d → K)) m)
    (hrange : ρ.range = commutator (TauCeti.QuadraticMap.orthogonalGroup (Q.comp M.subtype)))
    (hM4 : finrank K M = 4) (hF4 : finrank K F ≤ 4) : False := by
  classical
  have hodd : Odd (Nat.card K) := by rw [hK]; exact (hℓ.odd_of_ne_two hℓ2).pow
  have : CharP K ℓ :=
    LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic hℓ he hK
  have hk2 : ringChar K ≠ 2 := by rw [ringChar.eq K ℓ]; exact hℓ2
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hk2
  have hz2 : matrixProjectiveProjection Q Z * matrixProjectiveProjection Q Z = 1 := by
    rw [← pow_two, ← hcfg.twoComp.1, pow_orderOf_eq_one]
  obtain ⟨b, hbD, hbord, hbz⟩ := hcfg.exists_involution_ne
  have hbcore := (Subgroup.mem_inf.mp (hcfg.D_le hbD)).2
  have hZK : center K₀ = pPrimeCore 2 K₀ := center_eq_pPrimeCore_of_isSimpleGroup hK₀q hcfg.simple
  have hKK : ⁅K₀, K₀⁆ = K₀ := LocalAnalysis.ComponentInitial.commutator_self_of_isQuasisimple
    ((AssemblyBPredicates.isQuasisimple_iff_native _).2 hK₀q)
  have hbK : ∀ k ∈ K₀, k * b = b * k :=
    commute_of_commutator_mem_center_self hKK (fun k hk => by rw [hZK]; exact hbcore.2 k hk)
  obtain ⟨B, rfl⟩ := matrixProjectiveProjection_surjective Q b
  have hb2 : matrixProjectiveProjection Q B * matrixProjectiveProjection Q B = 1 := by
    rw [← pow_two, ← hbord, pow_orderOf_eq_one]
  have hb1 : matrixProjectiveProjection Q B ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hbord
    exact absurd hbord (by norm_num)
  have hBY : ∀ y ∈ liftHat Q K₀, y * B = B * y := by
    refine commute_of_commutator_mem_center hYq fun y hy => ?_
    apply ker_matrixProjectiveProjection_le Q
    rw [MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv]
    have hyK : matrixProjectiveProjection Q y ∈ K₀ := by
      rw [← hYK]
      exact mem_map_of_mem _ hy
    rw [mul_assoc, hbK _ hyK]
    group
  have hBO : matrixLinearEquiv B.val ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
    TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr
      ((mem_matrixIsometries_iff Q B.val).mp (matrixDerived_le_isometries Q B.2))
  have hBYl : ∀ y ∈ (liftHat Q K₀).map (derivedLinear Q),
      y * matrixLinearEquiv B.val = matrixLinearEquiv B.val * y := by
    rintro _ ⟨y, hy, rfl⟩
    rw [← derivedLinear_eq, ← map_mul, ← map_mul, hBY y hy]
  obtain ⟨hBF, l, hl, hBM⟩ := commutant_block hk2 hMF horth hMnd hFnd (by omega) hYF
    (exists_of_mem_secondDerived ρ hρ hrange) hBO hBYl
  have hl0 : l ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hl
    exact zero_ne_one hl
  have hs0 : s ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hs1
    exact zero_ne_one hs1
  obtain ⟨cB, hcB⟩ := exists_scalar_sq Q B hb2
  have hsqB : ∀ x, matrixLinearEquiv B.val (matrixLinearEquiv B.val x) = (cB : K) • x := by
    intro x
    rw [← LinearEquiv.mul_apply, ← matrixLinearEquiv_mul, hcB]
    exact LocalAnalysis.ComponentInitial.OddOrthogonal.matrixLinearEquiv_scalar cB x
  have hM0 : M ≠ ⊥ := by
    intro h
    rw [h, finrank_bot] at hM4
    exact absurd hM4 (by norm_num)
  obtain ⟨m₀, hm₀M, hm₀⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hM0
  have hcB1 : (cB : K) = 1 := by
    have h1 : matrixLinearEquiv B.val (matrixLinearEquiv B.val m₀) = m₀ := by
      rw [hBM m₀ hm₀M, map_smul, hBM m₀ hm₀M, smul_smul, hl, one_smul]
    rw [hsqB] at h1
    have h3 : ((cB : K) - 1) • m₀ = 0 := by rw [sub_smul, h1, one_smul, sub_self]
    exact sub_eq_zero.mp ((smul_eq_zero.mp h3).resolve_right hm₀)
  have hBB : ∀ v, matrixLinearEquiv B.val (matrixLinearEquiv B.val v) = v := fun v => by
    rw [hsqB, hcB1, one_smul]
  have hne : ∃ f ∈ F, matrixLinearEquiv B.val f ≠ -l • f := by
    by_contra hall
    push Not at hall
    apply hbz
    have hZM := forall_of_eq_eigenspace hMeig
    have hZF := forall_of_eq_eigenspace hFeig
    have hsl : matrixProjectiveProjection Q (B * Z) = 1 := by
      refine proj_eq_one_of_smul Q (B * Z) (Units.mk0 (l * s) (mul_ne_zero hl0 hs0)) fun v => ?_
      obtain ⟨m, f, rfl⟩ := LocalAnalysis.ComponentInitial.exists_add_of_isCompl hMF v
      rw [map_mul, LinearEquiv.mul_apply, derivedLinear_eq, derivedLinear_eq, map_add,
        hZM m m.2, hZF f f.2, map_add, map_smul, map_smul, hBM m m.2, hall f f.2, Units.val_mk0,
        smul_smul, smul_smul, smul_add, neg_mul_neg, mul_comm s l]
    rw [map_mul] at hsl
    calc matrixProjectiveProjection Q B =
        matrixProjectiveProjection Q B *
          (matrixProjectiveProjection Q Z * matrixProjectiveProjection Q Z) := by
          rw [hz2, mul_one]
      _ = matrixProjectiveProjection Q B * matrixProjectiveProjection Q Z *
          matrixProjectiveProjection Q Z := by rw [mul_assoc]
      _ = matrixProjectiveProjection Q Z := by rw [hsl, one_mul]
  obtain ⟨hdl, hdl'⟩ := eigen_dims hMF h2 hl hBM hBF hBB hne
  obtain ⟨Yb, hYb, ⟨φ⟩⟩ := hcfg.pump _ hbD hbord
  obtain ⟨hYbC, hYbq⟩ := isComponentOf_of_isTwoComponentAt hℓ hℓ2 he hK (by omega) hQ B hYb
  have hsb := smallSource_of_quot hYbq φ hcfg.simple hcfg.foote
  obtain ⟨s', Mb, -, hs'1, hMbeig, -, -, -, hMbnd, -, -, ρb, -, hρbc, -, h3b, h4b⟩ :=
    inner_split_data hℓ hℓ2 he hK hd hQ B hb2 hb1 hYbC hsb
  have hQMb : (Q.comp Mb.subtype).polarBilin.Nondegenerate := by
    rw [QuadraticMap.polarBilin_comp]
    exact hMbnd
  obtain ⟨hMb4, -⟩ := eq_commutator_of_three hodd hq3 (Q.comp Mb.subtype) hQMb h3b h4b hρbc
  subst hMbeig
  rcases mul_self_eq_mul_self_iff.mp (hs'1.trans hl.symm) with rfl | rfl
  · omega
  · omega

theorem orth_config_false [Finite K] {ℓ e : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (he : 1 ≤ e)
    (hK : Nat.card K = ℓ ^ e) (hd : 7 ≤ d) {Q : QuadraticForm K (Fin d → K)}
    (hQ : Q.polarBilin.Nondegenerate) {z : matrixProjectiveDerived Q}
    {K₀ D : Subgroup (matrixProjectiveDerived Q)} (hcfg : EndOddCore.Config z K₀ D)
    (hsol : Group.IsSolvable ↥(centralizer ({z} : Set (matrixProjectiveDerived Q)) ⊓
      centralizer (K₀ : Set (matrixProjectiveDerived Q)))) : False := by
  classical
  have hodd : Odd (Nat.card K) := by rw [hK]; exact (hℓ.odd_of_ne_two hℓ2).pow
  obtain ⟨Z, rfl⟩ := matrixProjectiveProjection_surjective Q z
  obtain ⟨hK₀C, hK₀q⟩ :=
    isComponentOf_of_isTwoComponentAt hℓ hℓ2 he hK (by omega) hQ Z hcfg.twoComp
  have hs₀ := smallSource_of_quot hK₀q (MulEquiv.refl _) hcfg.simple hcfg.foote
  have hz2 : matrixProjectiveProjection Q Z * matrixProjectiveProjection Q Z = 1 := by
    rw [← pow_two, ← hcfg.twoComp.1, pow_orderOf_eq_one]
  have hz1 : matrixProjectiveProjection Q Z ≠ 1 := by
    intro h
    have hord := hcfg.twoComp.1
    rw [h, orderOf_one] at hord
    exact absurd hord (by norm_num)
  obtain ⟨hYm, hYK, -⟩ := inner_lift Q Z hz2 hK₀C
  obtain ⟨s, M, F, hs1, hMeig, hFeig, hMF, horth, hMnd, hFnd, hYF, ρ, -, hρc, hρ, h3, h4⟩ :=
    inner_split_data hℓ hℓ2 he hK hd hQ Z hz2 hz1 hK₀C hs₀
  have hdV : finrank K (Fin d → K) = d := Module.finrank_fin_fun K
  have hdMF := Submodule.finrank_add_eq_of_isCompl hMF
  have hQF : (Q.comp F.subtype).polarBilin.Nondegenerate := by
    rw [QuadraticMap.polarBilin_comp]
    exact hFnd
  have hQM : (Q.comp M.subtype).polarBilin.Nondegenerate := by
    rw [QuadraticMap.polarBilin_comp]
    exact hMnd
  have hYM : ∀ y ∈ (liftHat Q K₀).map (derivedLinear Q), ∀ m ∈ M, y m ∈ M := by
    intro y hy m hm
    have h' : y m = (((ρ ⟨y, hy⟩).val ⟨m, hm⟩ : M) : Fin d → K) := (hρ ⟨y, hy⟩ ⟨m, hm⟩).symm
    rw [h']
    exact ((ρ ⟨y, hy⟩).val ⟨m, hm⟩).2
  have hM0 : M ≠ ⊥ := by
    intro h
    rw [h, finrank_bot] at h3
    exact absurd h3 (by norm_num)
  rcases exists_quasisimple_or_three hodd (Q.comp F.subtype) hQF (by omega) with
    ⟨L, hL⟩ | ⟨hq3, hF4⟩
  · exact ext_false Q Z hYK hsol hMeig hFeig hMF horth hYF hYM hM0 hL
  · obtain ⟨hM4, hrange⟩ := eq_commutator_of_three hodd hq3 (Q.comp M.subtype) hQM h3 h4 hρc
    exact pump_false hℓ hℓ2 he hK hq3 hd hQ Z hcfg hK₀q
      (LocalAnalysis.ComponentInitial.commutator_self_of_isQuasisimple hYm.2.2) hYK hs1 hMeig
      hFeig hMF horth hMnd hFnd hYF ρ hρ hrange hM4 hF4

end CFSG.ComponentClassification.CatLeafProof.EndOddO
