module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.G2Three.Sec1Proof.BrNative
public import CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.SmallG23

public section

namespace CFSG.OddStandard.HigherRank.G2Three.Sec1Proof

open CFSG.OddStandard.HigherRank.G2Three.Sec1 CFSG.Blueprint.Chevalley CFSG.LieType.Ree Subgroup
open CFSG.ComponentClassification.LiteratureLocal

@[expose] noncomputable def fixN (α : MulAut NG) : Subgroup NG :=
  α.toMonoidHom.eqLocus (MonoidHom.id NG)

private theorem map_centEl_conj {G : Type} [Group G] {L : Subgroup G} {θ : G} (hθ : θ ∈ L)
    (y : G) :
    (centEl L y).map (MulAut.conj θ).toMonoidHom = centEl L (θ * y * θ⁻¹) := by
  apply le_antisymm
  · rintro x ⟨w, hw, rfl⟩
    have hwL : w ∈ L := hw.1
    have hwC : w * y = y * w := Subgroup.mem_centralizer_singleton_iff.mp hw.2
    refine ⟨?_, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
    · show θ * w * θ⁻¹ ∈ L
      exact L.mul_mem (L.mul_mem hθ hwL) (L.inv_mem hθ)
    · show θ * w * θ⁻¹ * (θ * y * θ⁻¹) = (θ * y * θ⁻¹) * (θ * w * θ⁻¹)
      calc θ * w * θ⁻¹ * (θ * y * θ⁻¹) = θ * (w * y) * θ⁻¹ := by group
        _ = θ * (y * w) * θ⁻¹ := by rw [hwC]
        _ = (θ * y * θ⁻¹) * (θ * w * θ⁻¹) := by group
  · rintro x ⟨hxL, hxC⟩
    have hxC : x * (θ * y * θ⁻¹) = (θ * y * θ⁻¹) * x :=
      Subgroup.mem_centralizer_singleton_iff.mp hxC
    refine ⟨(MulAut.conj θ)⁻¹ x, ⟨?_, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩,
      MulAut.apply_inv_self (M := G) (MulAut.conj θ) x⟩
    · show (MulAut.conj θ)⁻¹ x ∈ L
      rw [MulAut.conj_inv_apply]
      exact L.mul_mem (L.mul_mem (L.inv_mem hθ) hxL) hθ
    · show (MulAut.conj θ)⁻¹ x * y = y * (MulAut.conj θ)⁻¹ x
      change θ⁻¹ * x * θ * y = y * (θ⁻¹ * x * θ)
      calc θ⁻¹ * x * θ * y = θ⁻¹ * (x * (θ * y * θ⁻¹)) * θ := by group
        _ = θ⁻¹ * ((θ * y * θ⁻¹) * x) * θ := by rw [hxC]
        _ = y * (θ⁻¹ * x * θ) := by group

theorem centEl_equiv_conj {G : Type} [Group G] {L : Subgroup G} {θ : G} (hθ : θ ∈ L) (y : G) :
    Nonempty (↥(centEl L (θ * y * θ⁻¹)) ≃* ↥(centEl L y)) := by
  rw [← map_centEl_conj hθ y]
  exact ⟨(Subgroup.equivMapOfInjective (centEl L y) (MulAut.conj θ).toMonoidHom
    (MulAut.conj θ).injective).symm⟩

theorem centEl_inner_phiN :
    centEl (innerAut NG) phiN = (fixN phiN).map (MulAut.conj : NG →* MulAut NG) := by
  ext x
  constructor
  · intro hx
    have hxI : x ∈ innerAut NG := hx.1
    have hxC : x * phiN = phiN * x := Subgroup.mem_centralizer_singleton_iff.mp hx.2
    have hxI' : x ∈ (MulAut.conj : NG →* MulAut NG).range := hxI
    rw [MonoidHom.mem_range] at hxI'
    obtain ⟨g, rfl⟩ := hxI'
    refine Subgroup.mem_map.mpr ⟨g, ?_, rfl⟩
    change phiN g = g
    rw [phiN_mul_conj g] at hxC
    exact (conj_inj_NG (mul_right_cancel hxC)).symm
  · rintro ⟨g, hg, rfl⟩
    have hg' : phiN g = g := hg
    refine ⟨?_, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
    · exact MonoidHom.mem_range.mpr ⟨g, rfl⟩
    · rw [phiN_mul_conj g, hg']

theorem fixN_phiN_equiv :
    Nonempty (↥(fixN phiN) ≃*
      MulAut (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 3))) := by
  have hK : Nat.card (ZMod 3) = 3 := Nat.card_zmod 3
  have hK' : Nat.card (ZMod 3) = 3 ^ (2 * 0 + 1) := by rw [hK]; norm_num
  have hfix : fixN phiN = ReeTag.G2.finiteReeFixedGroup (ZMod 3) 0 := by
    ext g
    change phiN g = g ↔ ReeTag.G2.finiteReeAut (ZMod 3) 0 g = g
    rw [CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.finiteReeAut_zero_eq hK]
  obtain ⟨e1⟩ := (G2_reeGamma_zero_structure (K := ZMod 3) hK').2.1
  have e2 : ↥(ReeTag.G2.finiteReeFixedGroup (ZMod 3) 0) ≃*
      ↥(ReeTag.G2.reeGamma (ZMod 3) 0) :=
    Subgroup.equivMapOfInjective _ ((adjointGroup ReeTag.G2.tag (ZMod 3)).subtype)
      Subtype.val_injective
  exact ⟨(MulEquiv.subgroupCongr hfix).trans
    (e2.trans (e1.trans (mulAutPSL2EquivSemilinearFractional (GaloisField 2 3)).symm))⟩

theorem centEl_phiN_equiv :
    Nonempty (↥(centEl (innerAut NG) phiN) ≃*
      MulAut (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 3))) := by
  obtain ⟨e⟩ := fixN_phiN_equiv
  rw [centEl_inner_phiN]
  exact ⟨(Subgroup.equivMapOfInjective (fixN phiN) (MulAut.conj : NG →* MulAut NG)
    conj_inj_NG).symm.trans e⟩

theorem cent_outer_NG : ∀ τ : MulAut NG, τ ∉ innerAut NG → τ * τ = 1 →
    Nonempty (↥(centEl (innerAut NG) τ) ≃*
      MulAut (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 3))) := by
  intro τ hτ hτ2
  rcases aut_cases_NG τ with ⟨g, hg⟩ | ⟨g, hg⟩
  · rw [hg] at hτ
    exact absurd (MonoidHom.mem_range.mpr ⟨g, rfl⟩) hτ
  · rw [hg] at hτ2 ⊢
    have hα : (MulAut.conj g * phiN) ^ 2 = 1 := by
      rw [pow_two]; exact hτ2
    have hK : Nat.card (ZMod 3) = 3 := Nat.card_zmod 3
    obtain ⟨b, hb⟩ :=
      CFSG.LocalAnalysis.EvenBN.LinearThree.G2Three.exists_conj_eq_conj_mul_phi
        (K := ZMod 3) hK g hα
    obtain ⟨e⟩ := centEl_equiv_conj (L := innerAut NG) (θ := MulAut.conj b)
      (MonoidHom.mem_range.mpr ⟨b, rfl⟩) phiN
    rw [hb] at e
    obtain ⟨e2⟩ := centEl_phiN_equiv
    exact ⟨e.trans e2⟩

end CFSG.OddStandard.HigherRank.G2Three.Sec1Proof
