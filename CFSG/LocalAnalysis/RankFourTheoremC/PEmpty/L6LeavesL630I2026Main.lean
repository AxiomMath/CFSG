module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesL630Defs
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesL630I2026Cent
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesL630I2026Key
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesL630I2026Sp

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L630

open CFSG.Open
open scoped commutatorElement

theorem isInvolvedIn_of_hom {Y K : Type} [Group Y] [Group K] (ι : Y →* K) (N : Subgroup Y)
    [N.Normal] (hker : ι.ker ≤ N) : IsInvolvedIn (Y ⧸ N) K := by
  haveI hN' : (N.map ι.rangeRestrict).Normal :=
    Subgroup.Normal.map ‹_› _ ι.rangeRestrict_surjective
  refine ⟨ι.range, N.map ι.rangeRestrict, hN', ⟨?_⟩⟩
  let f : Y →* ↥ι.range ⧸ N.map ι.rangeRestrict :=
    (QuotientGroup.mk' _).comp ι.rangeRestrict
  have hfs : Function.Surjective f :=
    (QuotientGroup.mk'_surjective _).comp ι.rangeRestrict_surjective
  have hfk : f.ker = N := by
    ext y
    rw [MonoidHom.mem_ker]
    show ((ι.rangeRestrict y : ↥ι.range) : ↥ι.range ⧸ N.map ι.rangeRestrict) = 1 ↔ y ∈ N
    rw [QuotientGroup.eq_one_iff]
    constructor
    · intro h
      obtain ⟨n, hn, hny⟩ := Subgroup.mem_map.mp h
      have h1 : y * n⁻¹ ∈ ι.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv]
        have h2 : ι n = ι y := congrArg Subtype.val hny
        rw [← h2, mul_inv_cancel]
      have h3 := hker h1
      have : y = (y * n⁻¹) * n := by group
      rw [this]
      exact N.mul_mem h3 hn
    · intro h
      exact Subgroup.mem_map_of_mem _ h
  exact (QuotientGroup.quotientKerEquivOfSurjective f hfs).symm.trans
    (QuotientGroup.quotientMulEquivOfEq hfk)

theorem kFactI2026_holds : KFactI2026 := by
  intro q E _ _ hq hq2 hcomm hexp hcard X P S hPX hP5 hSX hST hSP hS
  haveI : Finite (MulAut E) :=
    Finite.of_injective (fun g : MulAut E => (g : E → E))
      (fun g h hgh => MulEquiv.ext (fun x => congrFun hgh x))
  obtain ⟨α, β, γ, δ, z, hpres⟩ := I2026.exists_pres hS
  obtain ⟨hcent, hsz⟩ := I2026.cent_all hq hq2 hcomm hexp hcard hpres
  have hzc : z ∈ Subgroup.center (MulAut E) := (hcent z hpres.z_central).1
  have hC : ∀ g : MulAut E, (∀ s ∈ S, g * s = s * g) → g ∈ Subgroup.center (MulAut E) :=
    fun g hg => (hcent g hg).1
  refine ⟨?_, ?_⟩
  ·
    intro g hg
    exact (hcent g (fun s hs => I2026.commute_core_pcore X g hg s (hST hs))).2
  ·
    intro hN
    have hTX : pCoreOf 2 X ≤ X := pCoreOf_le_self 2 X
    have hPS : ∀ p ∈ P, ∀ s ∈ S, p * s * p⁻¹ ∈ S := by
      intro p hp s hs
      have h1 : ⁅p, s⁆ ∈ ⁅P, S⁆ := Subgroup.commutator_mem_commutator hp hs
      rw [Subgroup.commutator_comm, hSP] at h1
      have h2 : p * s * p⁻¹ = ⁅p, s⁆ * s := by
        rw [commutatorElement_def]
        group
      rw [h2]
      exact S.mul_mem h1 hs
    have hPT : ∀ p ∈ P, ∀ t ∈ pCoreOf 2 X, p * t * p⁻¹ ∈ pCoreOf 2 X := fun p hp t ht =>
      I2026.conj_mem_of_normal_subgroupOf hTX (pCoreOf_subgroupOf_normal 2 X) p (hPX hp) t ht
    have hnc : ¬ ∀ p ∈ P, ∀ s ∈ S, p * s = s * p := by
      intro h
      have hbot : ⁅S, P⁆ ≤ ⊥ := by
        rw [Subgroup.commutator_le]
        intro s hs p hp
        rw [Subgroup.mem_bot, commutatorElement_def, ← h p hp s hs]
        group
      rw [hSP] at hbot
      exact hpres.z_ne (Subgroup.mem_bot.mp (hbot hpres.z_mem))
    have hTS : ∀ t ∈ pCoreOf 2 X, ∃ s ∈ S, s⁻¹ * t ∈ Subgroup.center (MulAut E) :=
      I2026.key_lemma hpres hzc hC hsz (pCoreOf_isPGroup 2 X) hST hP5 hPS hPT hnc
    obtain ⟨ι, hι⟩ := I2026.exists_hom_perm_six hpres hzc hC hsz hST hTS
    exact isInvolvedIn_of_hom ι _ (fun g hg => hι g hg)

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L630
