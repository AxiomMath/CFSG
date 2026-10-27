module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R166TwA5Eight4
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R166SUBlocks3
public import CFSG.LocalAnalysis.EvenBN.Common.RadicalRank

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F

namespace TwA5Eight

open CFSG.Open CFSG.ClassicalGroups.UnitaryFlag CFSG.SeitzReduction.UnitaryPilot
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.EvenBN.Common
open scoped commutatorElement

variable {F : Type} [Field F] (h : UnitaryFieldData 2 3 F)

theorem twA5Hom_mem_normalizer_lineRadical (x : twA5Param (F := F)) :
    twA5Hom h x ∈ Subgroup.normalizer (unitaryLineRadical h : Set (unitarySU 2 3 F 6)) := by
  rw [twA5Hom_apply]
  unfold twA5Diag
  exact diagSU_mem_normalizer_unitaryLineRadical h _ _ rfl

noncomputable def twA5S : Subgroup (unitaryPSU h 6) :=
  (unitaryLineRadical h).map (unitaryProj h 6)

theorem twA5S_isPGroup : IsPGroup 2 (twA5S h) :=
  (unitaryLineRadical_isPGroup h).map (unitaryProj h 6)

theorem twA5S_le_blockSU_five : twA5S h ≤ blockSU h suFiveIndex :=
  Subgroup.map_mono (unitaryLineRadical_le_unitaryBlock h)

theorem twA5Bar_le_normalizer_S :
    (twA5Hom h).range.map (unitaryProj h 6) ≤
      Subgroup.normalizer (twA5S h : Set (unitaryPSU h 6)) := by
  have hB : (twA5Hom h).range ≤
      Subgroup.normalizer (unitaryLineRadical h : Set (unitarySU 2 3 F 6)) := by
    rintro _ ⟨x, rfl⟩
    exact twA5Hom_mem_normalizer_lineRadical h x
  exact (Subgroup.map_mono hB).trans (Subgroup.le_normalizer_map (unitaryProj h 6))

theorem twA5Hom_mem_form (x : twA5Param (F := F)) :
    ∃ (d : Fin 6 → F) (hd : ∀ i, h.norm (d i) = 1) (hdet : ∏ i, d i = 1) (n : ℕ),
      twA5Hom h x = diagSU h d hd hdet ∧ d 0 = d 1 ∧ d 0 = ((twA5Lambda (F := F) : Fˣ) : F) ^ n := by
  obtain ⟨n, hn⟩ := mem_zpowers_lambda_nat (by
    rw [zpowers_lambda_eq_roots h]
    exact (mem_rootsOfUnity (M := F) 9 x.1.1).mpr (mem_twA5Param.mp x.2).1)
  refine ⟨twA5Entries (F := F) x.1.1 x.1.2.1 x.1.2.2.1 x.1.2.2.2,
    twA5Entries_norm h x.1.1 x.1.2.1 x.1.2.2.1 x.1.2.2.2
      (norm_eq_one_of_pow_nine h (coe_pow_eq_one (mem_twA5Param.mp x.2).1))
      (norm_eq_one_of_pow_three h (coe_pow_eq_one (mem_twA5Param.mp x.2).2.1))
      (norm_eq_one_of_pow_three h (coe_pow_eq_one (mem_twA5Param.mp x.2).2.2.1))
      (norm_eq_one_of_pow_three h (coe_pow_eq_one (mem_twA5Param.mp x.2).2.2.2)),
    twA5Entries_prod (F := F) x.1.1 x.1.2.1 x.1.2.2.1 x.1.2.2.2, n, ?_, rfl, ?_⟩
  · rw [twA5Hom_apply]
    unfold twA5Diag
    rfl
  · have hn' : ((x.1.1 : Fˣ) : F) = (((twA5Lambda (F := F) : Fˣ)) : F) ^ n := by
      simpa using congrArg (fun u : Fˣ => (u : F)) hn
    simpa [twA5Entries] using hn' 

theorem twA5_centralizer_lift {b : unitarySU 2 3 F 6}
    (hb : (unitaryProj h 6) b ∈ Subgroup.centralizer (twA5S h : Set (unitaryPSU h 6))) :
    b ∈ Subgroup.centralizer (unitaryLineRadical h : Set (unitarySU 2 3 F 6)) := by
  let Z : Subgroup (unitarySU 2 3 F 6) := unitaryScalars h 6
  have hZA : Z ≤ Subgroup.centralizer (unitaryLineRadical h : Set (unitarySU 2 3 F 6)) := by
    intro z hz
    rw [Subgroup.mem_centralizer_iff]
    intro s _
    exact Subgroup.mem_center_iff.mp (unitaryScalars_le_center h 6 hz) s
  have hxA : ∀ s ∈ unitaryLineRadical h, ⁅b, s⁆ ∈ Z := by
    intro s hs
    have hcomm : (unitaryProj h 6) b * (unitaryProj h 6) s =
        (unitaryProj h 6) s * (unitaryProj h 6) b :=
      ((Subgroup.mem_centralizer_iff.1 hb) ((unitaryProj h 6) s)
        (Subgroup.mem_map_of_mem _ hs)).symm
    have h1 : (unitaryProj h 6) ⁅b, s⁆ = 1 := by
      rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm.mpr hcomm]
    have hmem : ⁅b, s⁆ ∈ (unitaryProj h 6).ker := MonoidHom.mem_ker.mpr h1
    rwa [ker_unitaryProj] at hmem
  let f : unitaryLineRadical h →* Z := commutatorElementHom b hZA hxA
  haveI : Finite F := Nat.finite_of_card_ne_zero (by rw [twA5_card_F h]; norm_num)
  haveI : IsPGroup 2 (unitaryLineRadical h) := unitaryLineRadical_isPGroup h
  haveI : Finite (unitaryLineRadical h) := Subtype.finite
  let f' : unitaryLineRadical h →* f.range :=
    f.codRestrict f.range (fun x => ⟨x, rfl⟩)
  have hsurj : Function.Surjective f' := by
    intro y
    obtain ⟨x, hx⟩ := y.2
    exact ⟨x, Subtype.ext hx⟩
  haveI : Finite f.range := Finite.of_surjective f' hsurj
  have himg : IsPGroup 2 f.range := IsPGroup.of_surjective (unitaryLineRadical_isPGroup h) f' hsurj
  have hdvd : Nat.card f.range ∣ 3 := by
    have hle : f.range ≤ ⊤ := le_top
    have := Subgroup.card_dvd_of_le hle
    simpa [Z, card_unitaryScalars_six h] using this
  obtain ⟨n, hn⟩ := IsPGroup.exists_card_eq himg
  have hcard1 : Nat.card f.range = 1 := by
    have hle : 2 ^ n ≤ 3 := hn ▸ Nat.le_of_dvd (by norm_num) hdvd
    have hnle : n ≤ 1 := by
      by_contra h
      have h2 : 2 ≤ n := by omega
      have h4 : 4 ≤ 2 ^ n := by
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) h2
      omega
    interval_cases n <;> simp_all
  have hbot : f.range = ⊥ := Subgroup.card_eq_one.mp hcard1
  rw [Subgroup.mem_centralizer_iff]
  intro s hs
  have hfs : f ⟨s, hs⟩ = 1 := by
    have hmem : f ⟨s, hs⟩ ∈ f.range := ⟨⟨s, hs⟩, rfl⟩
    rw [hbot] at hmem
    exact Subgroup.mem_bot.mp hmem
  have hcomm : ⁅b, s⁆ = 1 := by
    have hval : ((f ⟨s, hs⟩ : Z) : unitarySU 2 3 F 6) = ⁅b, s⁆ := by
      simp only [f, commutatorElementHom_apply]
    rw [← hval, hfs, OneMemClass.coe_one]
  exact (commutatorElement_eq_one_iff_mul_comm.mp hcomm).symm

theorem twA5Bar_inf_centralizer_eq_zpowers :
    (twA5Hom h).range.map (unitaryProj h 6) ⊓
        Subgroup.centralizer (twA5S h : Set (unitaryPSU h 6)) =
      Subgroup.zpowers (twA5X h) := by
  apply le_antisymm
  · intro c hc
    obtain ⟨hcb, hcc⟩ := hc
    obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.1 hcb
    have hbcent : b ∈ Subgroup.centralizer (unitaryLineRadical h : Set (unitarySU 2 3 F 6)) :=
      twA5_centralizer_lift h hcc
    have hmem := map_unitaryProj_inf_centralizer_le_zpowers h (norm_twA5Lambda h)
      (B := (twA5Hom h).range) (fun A hA => by
        obtain ⟨x, rfl⟩ := MonoidHom.mem_range.1 hA
        exact twA5Hom_mem_form h x)
      (Subgroup.mem_map_of_mem _ (show b ∈ (twA5Hom h).range ⊓
          Subgroup.centralizer (unitaryLineRadical h : Set (unitarySU 2 3 F 6)) from
        ⟨hb, hbcent⟩))
    rwa [← twA5X_eq_proj_diagFiveLast h] at hmem
  · refine Subgroup.zpowers_le.mpr ⟨twA5X_mem_B h, ?_⟩
    change twA5X h ∈ Subgroup.centralizer (twA5S h : Set (unitaryPSU h 6))
    rw [Subgroup.mem_centralizer_iff]
    intro t ht
    obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.1 ht
    have hU : twA5S h ≤
        Subgroup.centralizer ({unitaryProj h 6 (diagFiveLast h
          ((twA5Lambda (F := F) : Fˣ) : F) (norm_twA5Lambda h))} : Set (unitaryPSU h 6)) := by
      rw [twA5S, centralizer_unitaryProj_diagFiveLast h (norm_twA5Lambda h)
        (pow_six_twA5Lambda_ne_one h)]
      exact Subgroup.map_mono ((unitaryLineRadical_le_unitaryBlock h).trans
        (unitaryBlock_le_unitaryBlockDiag h suFiveIndex))
    have hcomm : (unitaryProj h 6) u *
        unitaryProj h 6 (diagFiveLast h ((twA5Lambda (F := F) : Fˣ) : F) (norm_twA5Lambda h)) =
        unitaryProj h 6 (diagFiveLast h ((twA5Lambda (F := F) : Fˣ) : F) (norm_twA5Lambda h)) *
          (unitaryProj h 6) u :=
      ((Subgroup.mem_centralizer_iff.1 (hU (Subgroup.mem_map_of_mem _ hu))) _
        (by simp)).symm
    simpa [twA5X_eq_proj_diagFiveLast h] using hcomm

theorem twA5_eight :
    ∃ S : Subgroup (unitaryPSU h 6), S ≤ blockSU h suFiveIndex ∧ IsPGroup 2 S ∧
      (twA5Hom h).range.map (unitaryProj h 6) ≤
        Subgroup.normalizer (S : Set (unitaryPSU h 6)) ∧
      (twA5Hom h).range.map (unitaryProj h 6) ⊓
        Subgroup.centralizer (S : Set (unitaryPSU h 6)) = Subgroup.zpowers (twA5X h) :=
  ⟨twA5S h, twA5S_le_blockSU_five h, twA5S_isPGroup h,
    twA5Bar_le_normalizer_S h, twA5Bar_inf_centralizer_eq_zpowers h⟩

end TwA5Eight

end CFSG.LocalAnalysis.GLTheoremA.Y10F
