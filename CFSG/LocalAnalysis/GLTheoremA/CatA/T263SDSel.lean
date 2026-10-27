module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T263SDGf
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T263SDA5
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T263SDTrans

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T263.SD

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S10
open CFSG.LocalAnalysis.GLTheoremA.T263 CFSG.LocalAnalysis.GLTheoremA.T263.DX
open CFSG.LocalAnalysis.GLTheoremA.KD264Lie
open scoped commutatorElement

@[expose] def SDFamModel (Q : TauCeti.CFSGIndex → Prop) : Prop :=
  ∀ (p : ℕ), p.Prime → p ≠ 2 → ∀ (Ω : Type) [Group Ω] [Finite Ω] (S B B₀ : Subgroup Ω) (hSn : S.Normal),
    CFSG.Open.IsQuasisimple ↥S → GLAPPrimeCore p ↥S = ⊥ → IsChevSimple 2 (↥S ⧸ Subgroup.center ↥S) →
    catalogIs (↥S ⧸ Subgroup.center ↥S) Q →
    (p = 3 → ¬ GLAMarking (↥S) (fun lab _ _ _ _ _ => lab.n = 1)) →
    IsElemAbelian p B → B₀ ≤ B → InnDiagOn p B₀ S →
    ∃ (P : Type) (_ : Group P) (_ : Finite P) (θ : ↥S ⧸ Subgroup.center ↥S ≃* P)
      (inn : MulAut P → Prop),
      (∀ b : ↥B, (b : Ω) ∈ B₀ → inn (kd264Rho (sd_hBN hSn B) θ b)) ∧ FamSel p P inn

theorem sd_selW_of_model
    (hChev : CFSG.LocalAnalysis.GLTheoremA.I142M.Three.ChevCompTypes)
    (hSub : CFSG.LocalAnalysis.GLTheoremA.SubcompField)
    (hLB : ∀ p : ℕ, p.Prime → ∀ (Y : Type) [Group Y] [Finite Y], LBalanceAt Y p)
    {Q : TauCeti.CFSGIndex → Prop} (hM : SDFamModel Q) : T263SelW Q := by
  intro p hp hp2 Ω _ _ hK S B hSn hSq hSp hSc hQ hF2 hSB hΩ hB h4 hT hC B₀ hB₀ hdich hcase T' hT'ne hT'2
    hT'S hBT' hker x hxB₀ hxC hxcomm
  obtain ⟨hBel, hBcard, -⟩ : IsElemAbelian p B ∧ Nat.card ↥B = p ^ GLATwoLocalRank p Ω ∧
      ∃ U : Subgroup Ω, U ≠ ⊥ ∧ IsPGroup 2 U ∧ B ≤ Subgroup.normalizer (U : Set Ω) := id hB
  have hB₀B : B₀ ≤ B := hB₀.1
  have hInn : InnDiagOn p B₀ S := hB₀.2.1
  obtain ⟨P, _, _, θ, inn, hinn, hF⟩ := hM p hp hp2 Ω S B B₀ hSn hSq hSp hSc hQ hF2 hBel hB₀B hInn
  obtain ⟨J, hJ⟩ := sdCore_of_famSel hChev hp hp2 hSn hSq hSp hSc hBel hB₀B hxB₀ hxC hT'2 hT'S hBT'
    hxcomm θ hinn hF
  have hInnx : InnDiagOn p (Subgroup.zpowers x) S :=
    innDiagOn_mono hInn (Subgroup.zpowers_le.2 hxB₀)
  have hxp : x ^ p = 1 := hBel.2 x (hB₀B hxB₀)
  rcases sd_selComp_or_a5 hSub hp hp2 hSn hSq hF2 hxp hxC hInnx hJ with hsel | ⟨hp3, h60⟩
  · exact Or.inr ⟨J, hsel⟩
  · subst hp3
    refine Or.inl (sd_concl_of_a5 (hLB 3 hp Ω) hK hSn hSq hSp hBel ?_ hB₀B hxB₀ hxC hT'2 hBT' hJ h60)
    rw [hBcard]
    exact Nat.pow_le_pow_right (by norm_num) h4

theorem t263DescSeed_of_model
    (hChev : CFSG.LocalAnalysis.GLTheoremA.I142M.Three.ChevCompTypes)
    (hSub : CFSG.LocalAnalysis.GLTheoremA.SubcompField)
    (hLB : ∀ p : ℕ, p.Prime → ∀ (Y : Type) [Group Y] [Finite Y], LBalanceAt Y p)
    {Q : TauCeti.CFSGIndex → Prop} (hM : SDFamModel Q) : T263DescSeed Q :=
  t263DescSeed_of_selW (sd_selW_of_model hChev hSub hLB hM)

end CFSG.LocalAnalysis.GLTheoremA.T263.SD

end
