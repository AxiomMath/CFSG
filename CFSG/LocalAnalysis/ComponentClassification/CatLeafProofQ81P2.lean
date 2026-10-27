module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofQ81P2Lemma29
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofQ81P2L4
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofQ81P2U4

public section

namespace CFSG.ComponentClassification.CatLeafProof.Q81P2

open CFSG Subgroup CFSG.ComponentClassification.CatFactsL4U4.OutInv
open CFSG.ComponentClassification.HarrisLit

theorem not_isPGroup_fixSub_of_lieModel {L : Type} [Group L] [Finite L]
    (hL : Blueprint.LieModel L .PSL 4 3 1 ∨ Blueprint.LieModel L .PSU 4 3 1)
    (β : MulAut L) (hβ : β * β = 1) :
    ¬ IsPGroup 2 (↥(fixSub β) ⧸ pPrimeCore 2 ↥(fixSub β)) := by
  obtain ⟨T, hT, h2⟩ := hL.elim (fun h => exists_odd_of_lieModel_psl h β hβ)
    (fun h => exists_odd_of_lieModel_psu h β hβ)
  exact not_isPGroup_fixSub hT h2

theorem not_isPGroup_centralizer_of_normal {M : Type} [Group M] [Finite M] {E : Subgroup M}
    [E.Normal] (hO : pPrimeCore 2 ↥E = ⊥)
    (hm : Blueprint.LieModel (↥E ⧸ center ↥E) .PSL 4 3 1 ∨
      Blueprint.LieModel (↥E ⧸ center ↥E) .PSU 4 3 1)
    {x : M} (hx : x * x = 1) :
    ¬ IsPGroup 2 (↥(centralizer {x}) ⧸ pPrimeCore 2 ↥(centralizer {x})) := by
  intro hP
  have hP' := Q81.isPGroup_quotient_of_le
    (inf_le_right : E ⊓ centralizer {x} ≤ centralizer {x}) hP
  set σ : MulAut ↥E := MulAut.conjNormal x with hσ
  have hσσ : σ * σ = 1 := by rw [hσ, ← map_mul, hx, map_one]
  have hmem : ∀ c : ↥(E ⊓ centralizer {x}),
      Subgroup.inclusion (inf_le_left : E ⊓ centralizer {x} ≤ E) c ∈ fixSub σ := fun c => by
    rw [mem_fixSub]
    apply Subtype.ext
    rw [hσ, MulAut.conjNormal_apply]
    change x * (c : M) * x⁻¹ = c
    rw [← mem_centralizer_singleton_iff.mp c.2.2, mul_inv_cancel_right]
  set ψ : ↥(E ⊓ centralizer {x}) →* ↥(fixSub σ) :=
    (Subgroup.inclusion (inf_le_left : E ⊓ centralizer {x} ≤ E)).codRestrict _ hmem with hψ
  have hψs : Function.Surjective ψ := by
    rintro ⟨l, hl⟩
    have hl' : x * (l : M) * x⁻¹ = l := by
      have h := congrArg Subtype.val (mem_fixSub.mp hl)
      rwa [hσ, MulAut.conjNormal_apply] at h
    have hc : (l : M) * x = x * l := by
      calc (l : M) * x = x * l * x⁻¹ * x := by rw [hl']
        _ = x * l := by group
    exact ⟨⟨l, l.2, mem_centralizer_singleton_iff.mpr hc⟩, rfl⟩
  have hF := isPGroup_fixSub_zStarAut hσσ (Q81.isPGroup_quotient_of_surjective ψ hψs hP')
  have hZE := fusionZStar_eq_center_of_pPrimeCore_eq_bot hO
  have hm' : Blueprint.LieModel (↥E ⧸ Open.fusionZStar ↥E) .PSL 4 3 1 ∨
      Blueprint.LieModel (↥E ⧸ Open.fusionZStar ↥E) .PSU 4 3 1 :=
    hm.imp (GSThmB.OddQuot.lieModel_of_equiv (QuotientGroup.quotientMulEquivOfEq hZE).symm)
      (GSThmB.OddQuot.lieModel_of_equiv (QuotientGroup.quotientMulEquivOfEq hZE).symm)
  exact not_isPGroup_fixSub_of_lieModel hm' (zStarAut σ) (zStarAut_mul_self hσσ) hF

end CFSG.ComponentClassification.CatLeafProof.Q81P2

namespace CFSG.ComponentClassification.HarrisLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer CFSG.ABGLocalTools

variable {X : Type} [Group X] [Finite X] {t : X} {L : Subgroup X}

namespace Standing.Setup42

variable {h : Standing t L 3 4} {S : Subgroup X} {hS : IsSylowOf 2 S (centralizer ({t} : Set X))}
  {w z : X} {hσ : Setup42 h hS w z} {i j : ℕ}

theorem Q81Data.not_isPGroup_centralizer' (hD : Q81Data hσ i j)
    {x : MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)} (hx : x * x = 1) :
    ¬ IsPGroup 2 (↥(centralizer {x}) ⧸ pPrimeCore 2 ↥(centralizer {x})) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hEn : (layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))).Normal := by
    have := LocalCores.layer_characteristic (G := MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))
    infer_instance
  have hO : pPrimeCore 2 (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) = ⊥ :=
    pPrimeCore_quotient_pPrimeCore_eq_bot 2
  exact CatLeafProof.Q81P2.not_isPGroup_centralizer_of_normal
    (pPrimeCore_eq_bot_of_isSubnormal hO hEn.isSubnormal)
    (hD.center_cases.imp And.left And.left) hx

end Standing.Setup42

end CFSG.ComponentClassification.HarrisLit
