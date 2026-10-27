module

public import CFSG.LocalAnalysis.RankFourTheoremC.SignalizerAut.Basic
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3L34Defs
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3L34Proved
import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.S3AmalgamBound.L34Exp3

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC

open CFSG.Open Subgroup

theorem isRankThreeL34_of_linThreeFour {K : Type} [Group K] {d : TauCeti.ValidLieTypeIndex}
    (hd : IsLThreeFourIndex d) (e : K ≃* (TauCeti.CFSGIndex.lie d).Group) :
    CFSG.LocalAnalysis.RankThreeTheoremC.IsRankThreeL34 K := by
  obtain ⟨q, h1, h2, h3⟩ := hd
  obtain ⟨c, hv⟩ := d
  simp only at h1
  subst h1
  exact ⟨q, h2, h3, hv, ⟨e⟩⟩

private theorem isL34Index_of_linThreeFour {d : TauCeti.ValidLieTypeIndex}
    (hd : IsLThreeFourIndex d) : CFSG.AGLEmbeddingD2.IsL34Index d := by
  obtain ⟨q, h1, h2, h3⟩ := hd
  exact ⟨q, h2, h3, h1⟩

theorem center_eq_bot_of_linThreeFour {K : Type} [Group K] {d : TauCeti.ValidLieTypeIndex}
    (hd : IsLThreeFourIndex d) (e : K ≃* (TauCeti.CFSGIndex.lie d).Group) :
    center K = ⊥ := by
  obtain ⟨F, _, hF, ⟨ψ⟩⟩ :=
    CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound.exists_equiv_projectiveSL_of_l34Index
      (isL34Index_of_linThreeFour hd) e
  exact center_eq_bot_of_mulEquiv ψ
    (CFSG.LocalAnalysis.ComponentInitial.LinearThreeFourOuter.center_projectiveSL_three_eq_bot hF)

theorem not_gl83OuterType24_linThreeFour {p : ℕ} {d : TauCeti.ValidLieTypeIndex}
    (hp : p = 3) (hd : IsLThreeFourIndex d) : ¬ GL83OuterType24 p (.lie d) := by
  rintro ⟨d', hi, hcase⟩
  obtain rfl := TauCeti.CFSGIndex.lie.inj hi
  obtain ⟨q, hq, -, -⟩ := hd
  rcases hcase with ⟨-, q', h1, -, -⟩ | ⟨h5, -⟩
  · have h2 := (TauCeti.LieTypeIndex.A.inj (h1.symm.trans hq)).1
    omega
  · omega

theorem weakTI_sylow_linThreeFour {K : Type} [Group K] [Finite K]
    (hL : CFSG.LocalAnalysis.RankThreeTheoremC.IsRankThreeL34 K) (R : Sylow 3 K) :
    WeakTI (R : Subgroup K) := by
  intro g x hx hx1 hxg
  have hT : ((g • R : Sylow 3 K) : Subgroup K) =
      (R : Subgroup K).map (MulAut.conj g).toMonoidHom := by
    rw [Sylow.coe_subgroup_smul]
    rfl
  have hxT : x ∈ ((g • R : Sylow 3 K) : Subgroup K) := by
    rw [hT, Subgroup.mem_map]
    refine ⟨g⁻¹ * x * g, hxg, ?_⟩
    show g * (g⁻¹ * x * g) * g⁻¹ = x
    group
  have hc1 := CFSG.LocalAnalysis.RankThreeTheoremC.kFactL34SylowCentralizer K hL R x hx hx1
  have hc2 := CFSG.LocalAnalysis.RankThreeTheoremC.kFactL34SylowCentralizer K hL (g • R) x hxT hx1
  have hE : (R : Subgroup K) = (R : Subgroup K).map (MulAut.conj g).toMonoidHom :=
    (hc1.symm.trans hc2).trans hT
  have hmem : ∀ y : K, y ∈ (R : Subgroup K) ↔
      y ∈ (R : Subgroup K).map (MulAut.conj g).toMonoidHom := fun y => by
    rw [← hE]
  have key : ∀ h : K, g * h * g⁻¹ ∈ (R : Subgroup K) ↔ h ∈ (R : Subgroup K) := by
    intro h
    rw [hmem (g * h * g⁻¹), Subgroup.mem_map_equiv, MulAut.conj_symm_apply,
      show g⁻¹ * (g * h * g⁻¹) * g = h by group]
  rw [Subgroup.mem_normalizer_iff]
  intro h
  exact (key h).symm

theorem signalizerInnAt_linThreeFour {d : TauCeti.ValidLieTypeIndex}
    (hd : IsLThreeFourIndex d) : SignalizerInnAt 3 (.lie d) := by
  rintro K _ _ ⟨e⟩ B Y hB hBc hY hBY
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨R₀⟩ := (Sylow.nonempty : Nonempty (Sylow 3 K))
  exact centralizes_of_sylow_weakTI Nat.prime_three R₀
    (weakTI_sylow_linThreeFour (isRankThreeL34_of_linThreeFour hd e) R₀) hB hBc
    ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).1 hY) hBY

theorem signalizerAutAt_linThreeFour {p : ℕ} {d : TauCeti.ValidLieTypeIndex} (hp : p = 3)
    (hd : IsLThreeFourIndex d) : SignalizerAutAt p (.lie d) := by
  subst hp
  exact signalizerAutAt_of_signalizerInnAt Nat.prime_three
    (fun _ _ _ ⟨e⟩ => center_eq_bot_of_linThreeFour hd e)
    (not_gl83OuterType24_linThreeFour rfl hd) (signalizerInnAt_linThreeFour hd)

end CFSG.LocalAnalysis.RankFourTheoremC
