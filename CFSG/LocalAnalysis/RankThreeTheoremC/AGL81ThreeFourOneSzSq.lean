module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ThreeFourOneDefs
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.JStarElimGeneric
import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsSquareProd
import CFSG.RankThree.PartOne.CTP.SeitzExcModels
import CFSG.RankThree.PartOne.K133.KillBasic
import CFSG.RankThree.PartTwo.KFacts.KP7Suzuki

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TenThirteen

open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)
open CFSG.ComponentClassification.AutL2Facts

variable {A : Type} [Group A]

private theorem suzukiModel_of_sz32 {d : TauCeti.ValidLieTypeIndex} (hd : d.1 = .suzuki 2)
    (hA : Nonempty (A ≃* (TauCeti.CFSGIndex.lie d).Group)) :
    CFSG.Blueprint.SuzukiModel A 2 (2 * 2 + 1) := by
  obtain ⟨d, hv⟩ := d
  have hd' : d = .suzuki 2 := hd
  subst hd'
  exact CFSG.RankThree.PartOne.CTP.suzukiModel_of_isoLie 2 ⟨hv, hA⟩

theorem eq_bot_of_isPGroup_three_sz32
    {d : TauCeti.ValidLieTypeIndex} (hd : d.1 = .suzuki 2)
    (hA : Nonempty (A ≃* (TauCeti.CFSGIndex.lie d).Group)) {W : Subgroup (MulAut A)}
    (hW : IsPGroup 3 W) : W = ⊥ := by
  have hM := suzukiModel_of_sz32 hd hA
  haveI := CFSG.RankThree.PartTwo.KFacts.KP7.finite_of_suzukiModel hM
  have h5 : Nat.card (Outer A) ∣ 2 * 2 + 1 :=
    (CFSG.LieType.Suzuki.Suzuki_model_and_perfect_cover_outer_cyclicity.{0} A 2 _ hM).1.2.1
  have hle : W ≤ inner A :=
    CFSG.RankThree.PartOne.K133.le_inner_of_isPGroup_of_not_dvd_outer Nat.prime_three
      (fun h3 => absurd (h3.trans h5) (by norm_num)) hW
  exact (inf_eq_left.mpr hle).symm.trans
    (CFSG.RankThree.PartTwo.KFacts.KP7.inf_inner_eq_bot hM hW)

private theorem eq_one_of_pow_three_sz32
    {d : TauCeti.ValidLieTypeIndex} (hd : d.1 = .suzuki 2)
    (hA : Nonempty (A ≃* (TauCeti.CFSGIndex.lie d).Group)) {f : MulAut A} {k : ℕ}
    (hf : f ^ 3 ^ k = 1) : f = 1 :=
  Subgroup.zpowers_eq_bot.mp (eq_bot_of_isPGroup_three_sz32 hd hA
    (IsPGroup.of_card_dvd_pow (by rw [Nat.card_zpowers]; exact orderOf_dvd_of_pow_eq_one hf)))

private theorem simpleCentreless_sz32
    {d : TauCeti.ValidLieTypeIndex} (hd : d.1 = .suzuki 2)
    (hA : Nonempty (A ≃* (TauCeti.CFSGIndex.lie d).Group)) : SimpleCentreless A := by
  obtain ⟨-, a, ha, F, _, _, hfa, hF, ⟨e⟩⟩ := suzukiModel_of_sz32 hd hA
  obtain rfl : a = 2 := by omega
  obtain ⟨hfin, -, hsimple⟩ := CFSG.LieType.Ree.suzuki_simple ha hF
  haveI : Finite A := Finite.of_equiv _ e.symm.toEquiv
  haveI : IsSimpleGroup A := e.isSimpleGroup
  have h25 : 5 ^ 2 ∣ Nat.card A := by
    rw [Nat.card_congr e.toEquiv, CFSG.LieType.Ree.suzuki_order hF]
    norm_num
  obtain ⟨x, y, hxy⟩ := CFSG.AGLEmbedding.nonabelian_of_simple_of_sq_dvd Nat.prime_five h25
  have hZ := CFSG.AGLEmbedding.center_bot_of_simple_nonab ⟨x, y, hxy⟩
  refine ⟨fun N _ => IsSimpleGroup.eq_bot_or_eq_top_of_normal N, fun z hz => ?_, ⟨x, ?_⟩⟩
  · have hz' : z ∈ Subgroup.center A := Subgroup.mem_center_iff.mpr fun g => (hz g).symm
    rwa [hZ, Subgroup.mem_bot] at hz'
  · rintro rfl
    exact hxy (by rw [one_mul, mul_one])

theorem eq_bot_of_isPGroup_three_sz32_prod
    {d : TauCeti.ValidLieTypeIndex} (hd : d.1 = .suzuki 2)
    (hA : Nonempty (A ≃* (TauCeti.CFSGIndex.lie d).Group)) {W : Subgroup (MulAut (A × A))}
    (hW : IsPGroup 3 W) : W = ⊥ := by
  haveI := CFSG.RankThree.PartTwo.KFacts.KP7.finite_of_suzukiModel (suzukiModel_of_sz32 hd hA)
  have hS := simpleCentreless_sz32 hd hA
  rw [eq_bot_iff]
  intro φ hφ
  obtain ⟨k, hk⟩ := hW ⟨φ, hφ⟩
  have hk' : φ ^ 3 ^ k = 1 := by simpa using congrArg Subtype.val hk
  have hodd : Odd (orderOf φ) :=
    Odd.of_dvd_nat (Odd.pow ⟨1, rfl⟩) (orderOf_dvd_of_pow_eq_one hk')
  have h1 := hS.presFst_of_odd hodd
  set ψ : presSub A := ⟨φ, ⟨h1, hS.snd_of_fst h1⟩⟩
  have hψ : ψ ^ 3 ^ k = 1 := Subtype.ext (by simpa [ψ] using hk')
  have hfst : fstHom ψ = 1 :=
    eq_one_of_pow_three_sz32 hd hA (k := k) (by rw [← map_pow, hψ, map_one])
  have hsnd : sndHom ψ = 1 :=
    eq_one_of_pow_three_sz32 hd hA (k := k) (by rw [← map_pow, hψ, map_one])
  have hψ1 : ψ = 1 := presSub_ext (by rw [hfst, map_one]) (by rw [hsnd, map_one])
  rw [Subgroup.mem_bot]
  exact congrArg Subtype.val hψ1

theorem signalizerThreeOn_sz32 (p : ℕ)
    {d : TauCeti.ValidLieTypeIndex} (hd : d.1 = .suzuki 2) {K : Type} [Group K] [Finite K]
    (hK : Nonempty (K ≃* (TauCeti.CFSGIndex.lie d).Group)) : SignalizerThreeOn p K :=
  fun _ _ hW _ => eq_bot_of_isPGroup_three_sz32 hd hK hW

theorem signalizerThreeSzSq_holds : SignalizerThreeSzSq := by
  rintro d hd K _ _ ⟨e⟩ T W hW -
  have h := eq_bot_of_isPGroup_three_sz32_prod hd ⟨MulEquiv.refl _⟩
    (hW.map (MulAut.congr e).toMonoidHom)
  exact (Subgroup.map_eq_bot_iff_of_injective W (MulAut.congr e).injective).1 h

end CFSG.LocalAnalysis.RankThreeTheoremC.TenThirteen
