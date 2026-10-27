module

public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4TorusLang
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4UnFrame

set_option linter.unusedSectionVars false

public section

namespace CFSG.HardMathSupport.Seitz.TrialityOdd.Inner

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley
  CFSG.RankThree.PartOne.KE CFSG.RankThree.PartOne.KGD CFSG.GH74.GLS.Stage2.Bender.Thm1


section Weyl

theorem weyl_commute_of_smul_neg {w₀ : WeylGroup TwistTag.D4.tag}
    (h : ∀ v : Fin TwistTag.D4.tag.rank → ℤ, w₀ • v = -v) (g : WeylGroup TwistTag.D4.tag) :
    g * w₀ = w₀ * g := by
  refine ext_single fun i => ?_
  rw [mul_smul, mul_smul, h, h, smul_neg]

end Weyl

section Involution

variable {K : Type} [Field K] {σ : K ≃+* K} {q : ℕ}

theorem n_conj_opposition_mem_torus {L : Type} [Field L] {n : ModGL TwistTag.D4.tag L}
    (hn : n ∈ monomialSubgroup TwistTag.D4.tag L) :
    n * trialityOpposition L * n⁻¹ * (trialityOpposition L)⁻¹ ∈ torusGroup TwistTag.D4.tag L := by
  set z := trialityOpposition L with hz
  have hzM : z ∈ monomialSubgroup TwistTag.D4.tag L := trialityOpposition_mem_monomialSubgroup
  have hzW := weylQuotientHom_trialityOpposition_smul (K := L)
  set p : monomialSubgroup TwistTag.D4.tag L := ⟨n, hn⟩ * ⟨z, hzM⟩ * (⟨n, hn⟩)⁻¹ * (⟨z, hzM⟩)⁻¹
    with hp
  have hpM : (p : ModGL TwistTag.D4.tag L) = n * z * n⁻¹ * z⁻¹ := rfl
  have h1 : weylQuotientHom TwistTag.D4.tag L p = 1 := by
    have hc := weyl_commute_of_smul_neg (w₀ := weylQuotientHom TwistTag.D4.tag L ⟨z, hzM⟩) hzW
      (weylQuotientHom TwistTag.D4.tag L ⟨n, hn⟩)
    rw [hp]
    simp only [map_mul, map_inv]
    rw [hc]
    group
  have h2 := mapsRootLines_weylQuotientHom (τ := TwistTag.D4.tag) (R := L) p
  rw [h1] at h2
  rw [← hpM]
  exact mem_torusGroup_of_mapsRootLines_one p.2 h2

theorem exists_involution_inverting_torus (hq : 1 ≤ q) (F : D4PhiFrame K σ q (-1)) :
    ∃ s ∈ torusGroup TwistTag.D4.tag (AlgebraicClosure K),
      ∃ w : graphFixedRootGroup TwistTag.D4 K σ.toRingHom,
        triEmb K σ (AlgebraicClosure K) w =
          F.g0 * (s * trialityOpposition (AlgebraicClosure K)) * F.g0⁻¹ ∧
        w * w = 1 ∧
        ∀ y : graphFixedRootGroup TwistTag.D4 K σ.toRingHom,
          F.g0⁻¹ * triEmb K σ (AlgebraicClosure K) y * F.g0 ∈
            twistedTorusOf F.n (twistHom TwistTag.D4 (AlgebraicClosure K) F.Fr) →
          F.g0⁻¹ * triEmb K σ (AlgebraicClosure K) (w * y * w⁻¹) * F.g0 =
            (F.g0⁻¹ * triEmb K σ (AlgebraicClosure K) y * F.g0)⁻¹ := by
  classical
  set L := AlgebraicClosure K with hL
  have : IsAlgClosed L := inferInstance
  set z : ModGL TwistTag.D4.tag L := trialityOpposition L with hz
  set Fh := twistHom TwistTag.D4 L F.Fr with hFh
  have hzM : z ∈ monomialSubgroup TwistTag.D4.tag L := trialityOpposition_mem_monomialSubgroup
  have hzz : z * z = 1 := by
    have := trialityOpposition_sq (K := L)
    rwa [pow_two] at this
  have hz1 : z⁻¹ = z := inv_eq_of_mul_eq_one_right hzz
  have hFz : Fh z = z := twistHom_trialityOpposition F.Fr
  set t' := F.n * z * F.n⁻¹ * z⁻¹ with ht'
  have ht'T : t' ∈ torusGroup TwistTag.D4.tag L := n_conj_opposition_mem_torus F.hn
  obtain ⟨s, hsT, hs⟩ := d4_torus_adjust F.Fr F.hFr F.hn (d4T36M (-1))
    (fun x => by rw [F.hnw]; exact F.hw x) (d4T36M_sub_det_ne_zero (Or.inr rfl) hq)
    (inv_mem ht'T)
  refine ⟨s, hsT, ?_⟩
  set wd := s * z with hwd
  have hnw : F.n * Fh wd * F.n⁻¹ = wd := by
    rw [hwd, map_mul, hFz]
    calc F.n * (Fh s * z) * F.n⁻¹ = (F.n * Fh s * F.n⁻¹) * (F.n * z * F.n⁻¹) := by group
      _ = (s * t'⁻¹) * (t' * z) := by
        rw [hs]
        congr 1
        rw [ht']
        group
      _ = s * z := by group
  set wG := F.g0 * wd * F.g0⁻¹ with hwG
  have hsA : s ∈ adjointGroup TwistTag.D4.tag L := torusGroup_le_adjointGroup' hsT
  have hzA : z ∈ adjointGroup TwistTag.D4.tag L := monomialSubgroup_le_adjointGroup' hzM
  have hwGA : wG ∈ adjointGroup TwistTag.D4.tag L :=
    mul_mem (mul_mem F.hg0C (mul_mem hsA hzA)) (inv_mem F.hg0C)
  have hFwG : Fh wG = wG := by
    rw [hwG, map_mul, map_mul, map_inv, F.hg0]
    calc F.g0 * F.n * Fh wd * (F.g0 * F.n)⁻¹ = F.g0 * (F.n * Fh wd * F.n⁻¹) * F.g0⁻¹ := by group
      _ = _ := by rw [hnw]
  have hrange : Subgroup.zpowers wG ≤ (triEmb K σ L).range := by
    refine F.hperf _ ?_ ?_
    · rw [Subgroup.zpowers_le]
      exact hwGA
    · rintro x ⟨k, rfl⟩
      rw [map_zpow, hFwG]
  obtain ⟨w, hw⟩ := hrange (Subgroup.mem_zpowers wG)
  have hwd2 : wd * wd = 1 := by
    have hzs : z * s * z⁻¹ = s⁻¹ := trialityOpposition_conj_torus hsT
    calc wd * wd = s * (z * s * z⁻¹) * (z * z) := by rw [hwd]; group
      _ = 1 := by rw [hzs, hzz]; group
  refine ⟨w, hw, ?_, fun y hy => ?_⟩
  · apply triEmb_injective (K := K) (σ := σ) (L := L)
    rw [map_mul, hw, map_one]
    calc wG * wG = F.g0 * (wd * wd) * F.g0⁻¹ := by rw [hwG]; group
      _ = 1 := by rw [hwd2]; group
  · have hyT : F.g0⁻¹ * triEmb K σ L y * F.g0 ∈ torusGroup TwistTag.D4.tag L := hy.1
    rw [map_mul, map_mul, map_inv, hw]
    set u := F.g0⁻¹ * triEmb K σ L y * F.g0 with hu
    have hcomm : s * u⁻¹ * s⁻¹ = u⁻¹ := by
      have := torusGroup_comm hsT (inv_mem hyT)
      calc s * u⁻¹ * s⁻¹ = (u⁻¹ * s) * s⁻¹ := by rw [this]
        _ = u⁻¹ := mul_inv_cancel_right _ _
    have hzu : z * u * z⁻¹ = u⁻¹ := trialityOpposition_conj_torus hyT
    have hy' : triEmb K σ L y = F.g0 * u * F.g0⁻¹ := by rw [hu]; group
    rw [hy']
    calc F.g0⁻¹ * (wG * (F.g0 * u * F.g0⁻¹) * wG⁻¹) * F.g0 = wd * u * wd⁻¹ := by
          rw [hwG]; group
      _ = s * (z * u * z⁻¹) * s⁻¹ := by rw [hwd]; group
      _ = u⁻¹ := by rw [hzu, hcomm]

end Involution

end CFSG.HardMathSupport.Seitz.TrialityOdd.Inner
