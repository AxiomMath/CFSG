module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Lit2.L2OmModel
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Lit2.L2OmGroup
public import CFSG.RankThree.PerfectCover.HopfCentralCoversFinite
public import CFSG.Assembly.GL83LieDefs

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.OddStandard.HigherRank.G2Three.Sec1 CFSG.RankThree.PerfectCover

theorem l2_pomega_generic {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K] [Finite K]
    (h2 : (2 : K) ≠ 0) {Q : QuadraticForm K (ι → K)} {Q₀ : (ι → K) → K} (hQ₀ : ⇑Q = Q₀)
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) (hd : 10 ≤ Fintype.card ι)
    {S : Type} [Group S] [Finite S]
    (eS : S ≃* CFSG.Open.StatedProj (CFSG.Open.StatedOmega Q₀))
    (hperf : Group.IsPerfect S) {ζ : HopfCover S} (hζk : ζ ∈ hopfMultiplier S)
    (hζ4 : orderOf ζ = 4) (hζg : ∀ u ∈ hopfMultiplier S, ∃ k : ℕ, u = ζ ^ k)
    {H : Type} [Group H] [Finite H] (hH : CFSG.IsQuasisimple H) (ρ : H →* S)
    (hρs : Function.Surjective ρ) (hρk : ρ.ker = center H) (hH2 : IsPGroup 2 ↥(center H))
    {A : Subgroup S} (hE : IsE 4 ↥A) (hP : L2Pauli ρ A)
    (hsyl : IsSylowIn 2 (centIn ⊤ A) A) : False := by
  classical
  haveI : Nonempty ι := Fintype.card_pos_iff.mp (by omega)
  haveI : Finite (HopfCover S) := finite_hopfCover hperf
  haveI : Finite (GL ι K) := Finite.of_injective
    (fun g : GL ι K => ((g : Matrix ι ι K), (g⁻¹ : GL ι K).1))
    (fun a b h => Units.ext (congrArg Prod.fst h))
  let π₀ : ↥(CFSG.Open.StatedOmega Q₀) →* CFSG.Open.StatedProj (CFSG.Open.StatedOmega Q₀) :=
    QuotientGroup.mk' ((CFSG.Open.StatedScalars ι K).subgroupOf (CFSG.Open.StatedOmega Q₀))
  let π : ↥(CFSG.Open.StatedOmega Q₀) →* S := eS.symm.toMonoidHom.comp π₀
  have hπs : Function.Surjective π :=
    eS.symm.surjective.comp (QuotientGroup.mk'_surjective _)
  have hπk : π.ker = (CFSG.Open.StatedScalars ι K).subgroupOf (CFSG.Open.StatedOmega Q₀) := by
    rw [MonoidHom.ker_comp_of_injective π₀ eS.symm.toMonoidHom eS.symm.injective,
      QuotientGroup.ker_mk']
  have hπc : π.ker ≤ Subgroup.center ↥(CFSG.Open.StatedOmega Q₀) := by
    rw [hπk]
    exact CFSG.Open.StatedAPI.statedScalars_subgroupOf_le_center _
  obtain ⟨hu2, hcard⟩ := l2_stated_ker hQ₀ hQ
  let θ := hopfLift π hπs hπc
  have hθ : π.comp θ = hopfCoverMap S := comp_hopfLift π hπs hπc
  haveI : Group.IsPerfect H := hH.1
  let α := hopfLift ρ hρs hρk.le
  have hαs : Function.Surjective α := hopfLift_surjective ρ hρs hρk.le
  have hρα : ρ.comp α = hopfCoverMap S := comp_hopfLift ρ hρs hρk.le
  refine l2_om_group α hαs ρ hρs hρk hH2 hE hP (ζ := ζ) (by rw [hρα]; exact hζk) hζ4
    (by rw [hρα]; exact hζg) ?_ π (fun u hu => hu2 u (by rw [← hπk]; exact hu))
    (fun u hu w => (Subgroup.mem_center_iff.mp (hπc hu) w).symm)
    (by rw [hπk]; exact hcard) θ (hθ.trans hρα.symm) hsyl
    (fun y hy hyc => l2_stated_kl h2 hQ₀ hQ hd y hy hyc)
  intro u hu x
  rw [hρα] at hu
  exact (Subgroup.mem_center_iff.mp (hopfMultiplier_le_center hu) x).symm

end CFSG.OddStandard.HigherRank.YamadaG23
