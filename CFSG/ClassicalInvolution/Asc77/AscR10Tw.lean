module

public import CFSG.ClassicalInvolution.AschTight.Sec6Gen64Main
public import CFSG.ClassicalInvolution.Uniform.UHypOmegaGen

public section

namespace CFSG.ClassicalInvolution.Asc77.T3CII

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Uniform CFSG.ClassicalInvolution.Disconnected.AschTight

variable {Y : Type} [Group Y] [Finite Y] {Λ : Set (Subgroup Y)}

theorem exists_twin_three (hΩ : HypOmegaModU (.sl2 3 1) Λ) {K J : Subgroup Y} {zK zJ : Y}
    (hK : K ∈ Λ) (hv : AViol Λ K J zK zJ) :
    ∃ a ∈ pairNormalizers K J zK zJ, a * zJ * a⁻¹ = zK ∧ conjSub a J ∈ Λ ∧
      IsUniqueInvolution (conjSub a J) zK ∧ conjSub a J ≠ K := by
  have hΩg : HypOmegaGen Λ := hypOmegaGenU_of_modU (MemberType.cert_sl2 3 1) hΩ
  have hInA : InA Λ K J :=
    ⟨hv.star, hv.not_nbr, zK, zJ, hv.hzK, hv.hzJ, fun ⟨g, hg, hgc⟩ => hv.no_conj g hg hgc⟩
  obtain ⟨u, v, r, t, Kstar, ustar, rstar, -, -, -, -, -, -, -, -, -, -, -, hKne, htw,
    ⟨y, hy, hyJ⟩, -⟩ :=
    Sec6Gen.l6_4ThreeGen Y Λ hΩg K hK J hv.mem hInA zK zJ hv.hzK hv.hzJ _ _ rfl rfl
  have hKs : Kstar ∈ twinSet Λ K := by
    rw [htw]
    exact Or.inr rfl
  obtain ⟨z', hz'K, hz'S⟩ := hKs.2
  have hz'eq : z' = zK := hz'K.eq hv.hzK
  subst hz'eq
  have hcj : IsUniqueInvolution (conjSub y J) (y * zJ * y⁻¹) := hv.hzJ.conj y
  rw [hyJ] at hcj
  have hyz : y * zJ * y⁻¹ = z' := (hz'S.eq hcj).symm
  refine ⟨y, hy, hyz, hyJ ▸ hKs.1, ?_, hyJ ▸ hKne⟩
  rw [hyJ]
  exact hz'S

end CFSG.ClassicalInvolution.Asc77.T3CII
