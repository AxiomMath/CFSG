module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P58bCov
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneBClPSL
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneBCover

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.T1

open CFSG Subgroup Assembly.LowTwoRank Blueprint CFSG.LocalAnalysis.ComponentInitial Matrix
open scoped MatrixGroups

open P58b

theorem noConfig_PSL_four : Harris82Lemma58bNoConfig .PSL 4 := by
  intro X _ _ hX hO p f hp hp2 hm k c t Q hcfg
  have hII := propBHypII_of_config hp hp2 hcfg
  have hc2 : orderOf c = 2 := hcfg.1
  have htZ : t ∉ center X := hcfg.2.2.2.1
  have ht2 : t * t = 1 := by
    have h := pow_orderOf_eq_one t
    rwa [hcfg.2.2.1, pow_two] at h
  have hc1 : c ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hc2
    exact absurd hc2 (by norm_num)
  obtain ⟨F, _, _, hFc, ⟨θ⟩⟩ := LinearCover.exists_mulEquiv_projectiveSL_of_lieModel hm
  have : Fintype F := Fintype.ofFinite F
  have : Fact p.Prime := ⟨hp⟩
  have : CharP F p := charP_of_card_eq_prime_pow (by rwa [← Nat.card_eq_fintype_card])
  have hF : ringChar F ≠ 2 := by rw [ringChar.eq F p]; exact hp2
  have hdet : (-1 : Matrix (Fin 4) (Fin 4) F).det = 1 := by
    rw [det_neg, det_one, Fintype.card_fin]
    norm_num
  set g₀ : SL(4, F) := ⟨-1, hdet⟩ with hg₀
  set β : SL(4, F) →* X ⧸ center X := θ.symm.toMonoidHom.comp (LinearFlag.proj 4 F) with hβ
  refine false_of_cover hX hO hp hp2 hcfg (G := SL(4, F)) (fun E _ _ π hπ hker h2 => ?_) β
    (θ.symm.surjective.comp (LinearFlag.proj_surjective 4 F)) ?_
  · obtain ⟨s, hs, -⟩ :=
      CFSG.LieType.Steinberg.sl_central_two_extension_splitting 3 hF hπ hker h2
    exact ⟨s, hs⟩
  intro α hαs hαβ hker g hg
  have hc : c = α g₀ := Burgoyne.B.burgoynePropBSL4CoverInput F hF X α hαs c hII g₀ rfl
  have hβ1 : ∀ z, β z = 1 → z ∈ LinearFlag.scalars 4 F := by
    intro z hz
    rw [hβ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.map_eq_one_iff] at hz
    exact (QuotientGroup.eq_one_iff z).mp hz
  have hinj : ∀ z, α z = 1 → z = 1 := by
    intro z hz
    obtain ⟨ζ, hζ4, hzζ⟩ := hβ1 z (by rw [← hαβ, hz, map_one])
    have h4 : ((ζ : F) * ζ) * ((ζ : F) * ζ) = 1 := by
      have := congrArg Units.val hζ4
      rw [Units.val_pow_eq_pow_val, Units.val_one] at this
      linear_combination this
    rcases mul_self_eq_one_iff.mp h4 with h2 | h2
    · rcases mul_self_eq_one_iff.mp h2 with h1 | h1
      · apply Subtype.ext
        rw [hzζ, h1, map_one]
        rfl
      · exfalso
        have hz₀ : z = g₀ := by
          apply Subtype.ext
          rw [hzζ, h1, map_neg, map_one]
        exact hc1 (by rw [hc, ← hz₀]; exact hz)
    · exfalso
      have hzz : z * z = g₀ := by
        apply Subtype.ext
        rw [Matrix.SpecialLinearGroup.coe_mul, hzζ, ← map_mul, h2, map_neg, map_one]
      have h1 : α g₀ = 1 := by rw [← hzz, map_mul, hz, one_mul]
      exact hc1 (hc.trans h1)
  have hgg : g * g = 1 := hinj _ (by rw [map_mul, hg, ht2])
  have hns : ∀ c' : Fˣ,
      Matrix.SpecialLinearGroup.toGL g ≠ GeneralLinearGroup.scalar (Fin 4) c' := by
    intro c' hc'
    apply htZ
    have hgm : (g : Matrix (Fin 4) (Fin 4) F) = scalar (Fin 4) (c' : F) := by
      have := congrArg (fun M : GL (Fin 4) F => (M : Matrix (Fin 4) (Fin 4) F)) hc'
      simpa only [Matrix.SpecialLinearGroup.coe_GL_coe_matrix, GeneralLinearGroup.coe_scalar]
        using this
    have hdg := Matrix.SpecialLinearGroup.det_coe g
    rw [hgm, scalar_apply, det_diagonal, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin] at hdg
    have hc4 : c' ^ 4 = 1 := Units.ext (by rw [Units.val_pow_eq_pow_val, hdg, Units.val_one])
    rw [hker]
    refine ⟨g, MonoidHom.mem_ker.mpr ?_, hg⟩
    rw [hβ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.map_eq_one_iff]
    exact (QuotientGroup.eq_one_iff g).mpr ⟨c', hc4, hgm⟩
  have hAA : Matrix.SpecialLinearGroup.toGL g * Matrix.SpecialLinearGroup.toGL g =
      GeneralLinearGroup.scalar (Fin 4) (1 * 1) := by
    rw [← map_mul, hgg, map_one, mul_one, map_one]
  obtain ⟨H, J, a, b, ha, hb, hH⟩ := Burgoyne.PSL.exists_split_normal_form hF hAA hns
  have hNo : Burgoyne.Cl.NoL2At (LinearFlag.conjAut 4 F (Matrix.SpecialLinearGroup.toGL g)) := by
    refine Burgoyne.Cl.NoL2At.of_conj (LinearFlag.conjAut 4 F H) ?_
    have e : LinearFlag.conjAut 4 F H *
        LinearFlag.conjAut 4 F (Matrix.SpecialLinearGroup.toGL g) * (LinearFlag.conjAut 4 F H)⁻¹ =
          LinearFlag.conjAut 4 F (Burgoyne.PSL.signGL F J) := by
      rw [← map_inv, ← map_mul, ← map_mul, hH, map_mul, LinearFlag.conjAut_scalar, one_mul]
    rw [e]
    exact Burgoyne.Cl.noL2At_conj_signGL hF ha hb
  rw [LinearFlag.conjAut_toGL] at hNo
  refine Burgoyne.Cl.NoL2At.of_congr θ ?_
  have e : MulAut.congr θ (MulAut.conj (β g)) = MulAut.conj (LinearFlag.proj 4 F g) :=
    mulAut_congr_conj θ (LinearFlag.proj 4 F g)
  rw [e]
  exact hNo

end CFSG.ComponentClassification.HarrisLit.T1
