module

public import CFSG.ClassicalInvolution.ModelFacts.StandardPairDichotomyExcA2TwFrob
public import CFSG.ClassicalInvolution.ModelFacts.StandardPairDichotomyExcA2E6Cocycle
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate117
public import CFSG.ClassicalInvolution.ModelFacts.StandardPairDichotomyExcA2E6Stab

public section

namespace CFSG.ClassicalInvolution.ModelFacts.Levi

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.AlgebraicGroups CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.Steinberg.TwistedE6 CFSG.LieType.Steinberg.Exceptional

section Descent

variable {k : Type} [Field k]

theorem exists_h1_fixed_conj_TwE6 (p : ℕ) [Fact p.Prime] [CharP k p] [IsAlgClosed k]
    (hp2 : p ≠ 2) {e : ℕ} (he : 1 ≤ e) {δ : Fin (Tag.rank .E6) → ℤ} (hδ : IsPartnerE6 δ)
    (hδρ : permLattice TwistTag.E6.perm δ = δ) {y v : ModGL .E6 k} (hv : v ∈ h1E6 k)
    (hFy : frobTwistGL .E6 k p e (diagramMap TwistTag.E6 k) y = y)
    (hvy : v * y * v⁻¹ = signDiagE6 k δ)
    (hu : frobTwistGL .E6 k p e (diagramMap TwistTag.E6 k) v * v⁻¹ ∈
      parabolicLevi .E6 k JE6) :
    ∃ h ∈ h1E6 k, frobTwistGL .E6 k p e (diagramMap TwistTag.E6 k) h = h ∧
      h * y * h⁻¹ = signDiagE6 k δ := by
  classical
  have hchar : ringChar k ≠ 2 := by rw [ringChar.eq k p]; exact hp2
  have hk2 : (-1 : kˣ) ≠ 1 := fun h =>
    Ring.neg_one_ne_one_of_char_ne_two hchar (by simpa using congrArg Units.val h)
  obtain ⟨c, hc⟩ := exists_unit_pow_ne_one (k := k) 8
  set F := frobTwistGL .E6 k p e (diagramMap TwistTag.E6 k) with hF
  set a' := pairDiagE6 δ c with ha'
  set d := rootDiagUnit .E6 (thetaDiag δ (-1 : kˣ)) with hd
  set db := rootDiagUnit .E6 (thetaDiag thetaE6 c) with hdb
  have hvy' : v * y * v⁻¹ = d := hvy
  have hFd : F d = d := by
    have h := frobTwistGL_diagramMap_rootDiagUnit_of_sign p TwistTag.E6 e (k := k)
      (b := thetaDiag δ (-1 : kˣ)) (thetaDiag_neg_one_sign_E6 δ)
    have h2 : (fun i => thetaDiag δ (-1 : kˣ) (TwistTag.E6.perm.symm i)) =
        thetaDiag δ (-1 : kˣ) := by
      funext i
      simp only [thetaDiag]
      congr 1
      have h1 := iform_permLattice_E6 δ (Pi.single (TwistTag.E6.perm.symm i) 1)
      rw [hδρ, permLattice_single, Equiv.apply_symm_apply] at h1
      exact h1.symm
    exact h.trans (congrArg (rootDiagUnit TwistTag.E6.tag) h2)
  have hker : ∀ σ ∈ kernelRoots (rootCharHom a'), IsRoot .E6 σ ∧ iform thetaE6 σ = 0 ∧
      rootChar (thetaDiag δ (-1 : kˣ)) σ = 1 := by
    intro σ hσ
    obtain ⟨hσr, hσ1⟩ := hσ
    obtain ⟨h1, h2⟩ := iform_eq_zero_of_rootChar_pairDiagE6_eq_one hc hσr hσ1
    exact ⟨hσr, h1, by rw [rootChar_thetaDiag]; exact h2⟩
  set M := torusGroup .E6 k ⊔ rootSpan .E6 k (kernelRoots (rootCharHom a')) with hM
  have hMd : ∀ m ∈ M, m * d * m⁻¹ = d := by
    have hle : M ≤ Subgroup.centralizer {d} := by
      refine sup_le (fun t ht => ?_) ?_
      · exact Subgroup.mem_centralizer_singleton_iff.2
          (rootDiagUnit_mul_comm_of_mem_torusGroup _ ht).symm
      · exact rootSpan_le_centralizer (thetaDiag δ (-1 : kˣ))
          (fun σ hσ => ⟨(hker σ hσ).1, (hker σ hσ).2.2⟩)
    intro m hm
    have := Subgroup.mem_centralizer_singleton_iff.1 (hle hm)
    rw [mul_inv_eq_iff_eq_mul]
    exact this
  have hMJ : M ≤ parabolicLevi .E6 k JE6 := by
    refine sup_le (torusGroup_le_parabolicLevi JE6) ?_
    refine iSup₂_le fun σ hσ => rootSubgroup_le_parabolicLevi' ?_
    exact mem_parabolicRoots_E6 (hker σ hσ).1 (hker σ hσ).2.1
  have hρσ : ∀ σ ∈ kernelRoots (rootCharHom a'), permLattice TwistTag.E6.perm σ ∈
      kernelRoots (rootCharHom a') := by
    intro σ hσ
    rw [kernelRoots_rootCharHom] at hσ ⊢
    refine ⟨IsRoot.permLattice (TwistTag.cartan_perm TwistTag.E6) hσ.1, ?_⟩
    have h1 : (-1 : kˣ) ^ iform δ σ * c ^ iform thetaE6 σ = 1 := by
      have := hσ.2
      rwa [ha', rootChar_pairDiagE6] at this
    have hperm : permLattice TwistTag.E6.perm thetaE6 = thetaE6 := by
      rw [thetaE6_eq_leviE6]
      exact LeviE6.perm_thetaE6
    have e1 : iform δ (permLattice TwistTag.E6.perm σ) = iform δ σ := by
      have := iform_permLattice_E6 δ σ
      rwa [hδρ] at this
    have e2 : iform thetaE6 (permLattice TwistTag.E6.perm σ) = iform thetaE6 σ := by
      have := iform_permLattice_E6 thetaE6 σ
      rwa [hperm] at this
    exact (rootChar_pairDiagE6 δ c _).trans (by convert h1 using 3 <;> assumption)
  have hMS : ∀ g ∈ M, F g ∈ M := fun g hg =>
    frobTwistGL_mem_torus_sup_rootSpan_diagram p TwistTag.E6 e (fun σ hσ => (hker σ hσ).1) hρσ hg
  have hlang : ∀ u ∈ M, ∃ m ∈ M, u = m⁻¹ * F m := by
    intro u hu
    have hM' := isConnectedAlgebraicSubgroup_torus_sup_rootSpan (k := k) (rootCharHom a')
    obtain ⟨hsm, -, -⟩ := hM'.smooth
    exact exists_eq_inv_mul_frobTwistGL p he (diagramMap TwistTag.E6 k) hM' hsm hMS hu
  have hFvM : F v * v⁻¹ ∈ M := by
    set u := F v * v⁻¹ with hudef
    have hF : F v * y * (F v)⁻¹ = d := by
      have := congrArg (F) hvy'
      rw [map_mul, map_mul, map_inv, hFy, hFd] at this
      exact this
    have hud : d * u = u * d := by
      have hy' : v⁻¹ * d * v = y := by rw [← hvy']; group
      have h1 : u * d * u⁻¹ = d := by
        calc u * d * u⁻¹ = F v * (v⁻¹ * d * v) *
              (F v)⁻¹ := by rw [hudef]; group
          _ = d := by rw [hy', hF]
      calc d * u = (u * d * u⁻¹) * u := by rw [h1]
        _ = u * d := by group
    have hub : db * u = u * db := rootDiagUnit_thetaDiag_comm_levi_E6 c hu
    have hmem : u ∈ toralCentralizer .E6 k a' := by
      rw [mem_toralCentralizer]
      refine ⟨parabolicSubgroup_le_adjointGroup _ _ _
        (parabolicLevi_le_parabolicSubgroup JE6 hu), ?_⟩
      have hmul : rootDiagUnit .E6 a' = d * db := rootDiagUnit_mul _ _
      rw [mul_inv_eq_iff_eq_mul, hmul]
      calc d * db * u = d * (db * u) := by group
        _ = d * (u * db) := by rw [hub]
        _ = (d * u) * db := by group
        _ = (u * d) * db := by rw [hud]
        _ = u * (d * db) := by group
    exact toralCentralizer_le_toralRootGroup a'
      (fun w hw => rootCharStabilizer_pairDiag_le_partnerE6 hk2 hδ hc hw) hmem
  obtain ⟨m, hm, hFix, hconj⟩ := exists_fixed_conj (F) hvy' hMd hlang hFvM
  exact ⟨m * v, mul_mem (levi_le_h1E6 (hMJ hm)) hv, hFix, hconj⟩


end Descent

end CFSG.ClassicalInvolution.ModelFacts.Levi
