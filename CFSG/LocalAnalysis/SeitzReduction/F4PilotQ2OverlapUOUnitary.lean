module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotQ2OverlapUOCover
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2UnitaryCTAlign

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.F4Pilot

open Subgroup Matrix CFSG.Assembly.LowTwoRank CFSG.LieType.Universal
  CFSG.LieType.Universal.Symplectic.SpExtras CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.SeitzReduction.SymplecticPilot (nsTorusSp nsElt complSp complSpEquiv ctuEmbed ctuBlock
  ctuEmbed_mem_ctuBlock_iff spBlock_compl_singleton coe_complSpEquiv_apply ctuBlockEquiv
  ctuCoord ctuPlanes mem_ctuBlock ctuCoord_mem_ctuPlanes ctuBlockIdx ctuBlockIdx_ctuCoord
  mat_ctuBlockEquiv)
open CFSG.LieType.Universal.Unitary (SU)
open CFSG.LieType.BorelTits (unitaryInvolution)
open CFSG.Quasithin (perfectCore)

section Iota

variable {K F : Type} [Field K] [Field F] [CharP K 2] {ε : ℕ} {σ : F ≃+* F} {ι : K →+* F}

@[expose] noncomputable def twoUniIota (hε : ε ≤ 1) (hι : ∀ c, σ (ι c) = ι c) :
    StatedSp 3 K →* ctuBlock σ ε ({3} : Finset (Fin 4)) :=
  ((ctuEmbed ε hε σ ι hι).comp ((complSp K (3 : Fin 4)).subtype.comp
    (complSpEquiv (K := K) (3 : Fin 4)).toMonoidHom)).codRestrict _ fun g =>
      (ctuEmbed_mem_ctuBlock_iff (hε := hε) (hι := hι)).2 (by
        rw [spBlock_compl_singleton]
        exact (complSpEquiv (K := K) (3 : Fin 4) g).2)

theorem coe_twoUniIota (hε : ε ≤ 1) (hι : ∀ c, σ (ι c) = ι c) (g : StatedSp 3 K) :
    ((twoUniIota hε hι g : ctuBlock σ ε ({3} : Finset (Fin 4))) : SU σ (2 * 4 + ε)) =
      ctuEmbed ε hε σ ι hι (spEmbed (3 : Fin 4).succAbove Fin.succAbove_right_injective g) := by
  rw [← coe_complSpEquiv_apply]
  rfl

theorem coe_twoUniIota_nsElt (hε : ε ≤ 1) (hι : ∀ c, σ (ι c) = ι c) :
    ((twoUniIota hε hι (nsElt (0 : Fin 3)) : ctuBlock σ ε ({3} : Finset (Fin 4))) :
      SU σ (2 * 4 + ε)) = ctuEmbed ε hε σ ι hι (nsElt (K := K) (0 : Fin 4)) := by
  rw [coe_twoUniIota, CFSG.SeitzReduction.SymplecticPilot.nsElt, spEmbed_longBlock]
  rfl

theorem coe_twoUniIota_elt_positiveLong (hε : ε ≤ 1) (hι : ∀ c, σ (ι c) = ι c) (c : K) :
    ((twoUniIota hε hι (elt (.positiveLong 1) c) : ctuBlock σ ε ({3} : Finset (Fin 4))) :
      SU σ (2 * 4 + ε)) = ctuEmbed ε hε σ ι hι (elt (.positiveLong (1 : Fin 4)) c) := by
  rw [coe_twoUniIota, CFSG.SeitzReduction.SymplecticPilot.spEmbed_elt_positiveLong]
  rfl

theorem coe_twoUniIota_elt_positiveSum (hε : ε ≤ 1) (hι : ∀ c, σ (ι c) = ι c) (c : K) :
    ((twoUniIota hε hι (elt (.positiveSum 1 2 (by decide)) c) :
      ctuBlock σ ε ({3} : Finset (Fin 4))) : SU σ (2 * 4 + ε)) =
      ctuEmbed ε hε σ ι hι (elt (.positiveSum (1 : Fin 4) 2 (by decide)) c) := by
  rw [coe_twoUniIota, spEmbed_elt_positiveSum_of_lt _ (by decide) (by decide)]
  rfl

end Iota

section Levi

variable {K F : Type} [Field K] [Field F] [CharP K 2] [Finite F] [CharP F 2] {ε : ℕ}
  {ι : K →+* F}

theorem card_compl_three_zero : (({3, 0} : Finset (Fin 4))ᶜ).card = 2 := by
  rw [Finset.card_compl, Fintype.card_fin, Finset.card_pair (by decide : (3 : Fin 4) ≠ 0)]

theorem map_subtype_map_twoUniIota_nsTorusSp (hε : ε ≤ 1)
    (hι : ∀ c, unitaryInvolution F 2 1 (ι c) = ι c) :
    ((nsTorusSp K (0 : Fin 3)).map (twoUniIota hε hι)).map
        (ctuBlock (unitaryInvolution F 2 1) ε ({3} : Finset (Fin 4))).subtype =
      (nsTorusSp K (0 : Fin 4)).map (ctuEmbed ε hε (unitaryInvolution F 2 1) ι hι) := by
  rw [Subgroup.map_map, CFSG.SeitzReduction.SymplecticPilot.nsTorusSp,
    CFSG.SeitzReduction.SymplecticPilot.nsTorusSp, MonoidHom.map_zpowers, MonoidHom.map_zpowers,
    MonoidHom.comp_apply, coe_subtype, coe_twoUniIota_nsElt]

theorem map_centralizerPerfectCore_twoUniIota (hF : Nat.card F = (2 ^ 1) ^ 2) (hε : ε ≤ 1)
    (hι : ∀ c, unitaryInvolution F 2 1 (ι c) = ι c) :
    (centralizerPerfectCore ((nsTorusSp K (0 : Fin 3)).map (twoUniIota hε hι))).map
        (ctuBlock (unitaryInvolution F 2 1) ε ({3} : Finset (Fin 4))).subtype =
      ctuBlock (unitaryInvolution F 2 1) ε ({3, 0} : Finset (Fin 4)) := by
  rw [centralizerPerfectCore, CFSG.Quasithin.map_perfectCore, map_subtype_centralizer_eq_inf,
    map_subtype_map_twoUniIota_nsTorusSp]
  exact CFSG.SeitzReduction.SymplecticPilot.perfectCore_ctuBlock_inf_centralizer_nsTorus hF hε hι
    (by rw [card_compl_three_zero]; omega) (by rw [card_compl_three_zero]; omega)

theorem mem_centralizerPerfectCore_twoUniIota_iff (hF : Nat.card F = (2 ^ 1) ^ 2) (hε : ε ≤ 1)
    (hι : ∀ c, unitaryInvolution F 2 1 (ι c) = ι c)
    (x : ctuBlock (unitaryInvolution F 2 1) ε ({3} : Finset (Fin 4))) :
    x ∈ centralizerPerfectCore ((nsTorusSp K (0 : Fin 3)).map (twoUniIota hε hι)) ↔
      (x : SU (unitaryInvolution F 2 1) (2 * 4 + ε)) ∈
        ctuBlock (unitaryInvolution F 2 1) ε ({3, 0} : Finset (Fin 4)) := by
  rw [← map_centralizerPerfectCore_twoUniIota hF hε hι]
  constructor
  · intro hx
    exact ⟨x, hx, rfl⟩
  · rintro ⟨y, hy, hyx⟩
    rwa [← Subtype.ext hyx]

end Levi

section Piece

variable {K F : Type} [Field K] [Field F] [CharP K 2] [Finite F] [CharP F 2] {ε : ℕ}
  {ι : K →+* F}

theorem map_twoUniIota_rootGroupL_le (hF : Nat.card F = (2 ^ 1) ^ 2) (hε : ε ≤ 1)
    (hι : ∀ c, unitaryInvolution F 2 1 (ι c) = ι c) :
    (Symplectic.rootGroup 3 K twoOverlapRootL).map (twoUniIota hε hι) ≤
      centralizerPerfectCore ((nsTorusSp K (0 : Fin 3)).map (twoUniIota hε hι)) := by
  rintro _ ⟨g, hg, rfl⟩
  obtain ⟨c, rfl⟩ := (mem_rootGroup_iff stdVec_positiveLong_one).1 hg
  rw [mem_centralizerPerfectCore_twoUniIota_iff hF hε hι, coe_twoUniIota_elt_positiveLong]
  exact (ctuEmbed_mem_ctuBlock_iff (hε := hε) (hι := hι)).2
    (CFSG.SeitzReduction.SymplecticPilot.elt_positiveLong_mem_spBlock (by decide) c)

theorem map_twoUniIota_rootGroupS_le (hF : Nat.card F = (2 ^ 1) ^ 2) (hε : ε ≤ 1)
    (hι : ∀ c, unitaryInvolution F 2 1 (ι c) = ι c) :
    (Symplectic.rootGroup 3 K twoOverlapRootS).map (twoUniIota hε hι) ≤
      centralizerPerfectCore ((nsTorusSp K (0 : Fin 3)).map (twoUniIota hε hι)) := by
  rintro _ ⟨g, hg, rfl⟩
  obtain ⟨c, rfl⟩ := (mem_rootGroup_iff stdVec_positiveSum_one_two).1 hg
  rw [mem_centralizerPerfectCore_twoUniIota_iff hF hε hι, coe_twoUniIota_elt_positiveSum]
  exact (ctuEmbed_mem_ctuBlock_iff (hε := hε) (hι := hι)).2
    (CFSG.SeitzReduction.SymplecticPilot.elt_positiveSum_mem_spBlock (by decide) (by decide)
      (by decide) c)

theorem planeOf_sumMap {m n : ℕ} (σ : Fin m → Fin n) (u : Fin m ⊕ Fin m) :
    CFSG.SeitzReduction.SymplecticPilot.planeOf (Sum.map σ σ u) =
      σ (CFSG.SeitzReduction.SymplecticPilot.planeOf u) := by
  rcases u with u | u <;> rfl

theorem ctuBlockIdx_mem_ctuPlanes_three_zero {a : Fin (2 * 3 + ε)}
    (ha : a ∈ ctuPlanes ε ({0} : Finset (Fin 3))) :
    ctuBlockIdx 3 ε (3 : Fin 4) a ∈ ctuPlanes ε ({3, 0} : Finset (Fin 4)) := by
  obtain ⟨w, rfl⟩ := (ctuCoord 3 ε).surjective a
  rw [ctuCoord_mem_ctuPlanes] at ha
  rw [ctuBlockIdx_ctuCoord, ctuCoord_mem_ctuPlanes]
  rcases w with u | i
  · change CFSG.SeitzReduction.SymplecticPilot.planeOf u ∈ ({0} : Finset (Fin 3)) at ha
    change CFSG.SeitzReduction.SymplecticPilot.planeOf (Sum.map (3 : Fin 4).succAbove
      (3 : Fin 4).succAbove u) ∈ ({3, 0} : Finset (Fin 4))
    rw [planeOf_sumMap, Finset.mem_singleton.1 ha]
    decide
  · exact absurd ha (CFSG.SeitzReduction.SymplecticPilot.not_inPlanes_inr _ i)

theorem centralizerPerfectCore_twoUniIota_inf_center (hF : Nat.card F = (2 ^ 1) ^ 2)
    (hε : ε ≤ 1) (hι : ∀ c, unitaryInvolution F 2 1 (ι c) = ι c) :
    centralizerPerfectCore ((nsTorusSp K (0 : Fin 3)).map (twoUniIota hε hι)) ⊓
      center (ctuBlock (unitaryInvolution F 2 1) ε ({3} : Finset (Fin 4))) = ⊥ := by
  rw [eq_bot_iff]
  intro z hz
  obtain ⟨hzO, hzc⟩ := Subgroup.mem_inf.1 hz
  rw [mem_centralizerPerfectCore_twoUniIota_iff hF hε hι] at hzO
  set β := ctuBlockEquiv (unitaryInvolution F 2 1) hε (3 : Fin (3 + 1)) with hβ
  have hβc : β z ∈ center (SU (unitaryInvolution F 2 1) (2 * 3 + ε)) := by
    rw [mem_center_iff]
    intro y
    obtain ⟨y', rfl⟩ := β.surjective y
    rw [← map_mul, ← map_mul, mem_center_iff.1 hzc y']
  have hβR : β z ∈ ctuBlock (unitaryInvolution F 2 1) ε ({0} : Finset (Fin 3)) := by
    rw [mem_ctuBlock]
    intro a b hab
    have h1 := congrFun (congrFun (mat_ctuBlockEquiv hε (3 : Fin (3 + 1)) z) a) b
    rw [CFSG.LieType.Universal.Unitary.SUExtras.mat_apply,
      CFSG.LieType.Universal.Unitary.SUExtras.mat_apply, submatrix_apply] at h1
    rw [h1, mem_ctuBlock.1 hzO _ _ (hab.imp ctuBlockIdx_mem_ctuPlanes_three_zero
      ctuBlockIdx_mem_ctuPlanes_three_zero), Matrix.one_apply, Matrix.one_apply]
    simp only [(CFSG.SeitzReduction.SymplecticPilot.ctuBlockIdx_injective (ε := ε)
      (3 : Fin 4)).eq_iff]
  have h1 := CFSG.SeitzReduction.SymplecticPilot.eq_one_of_mem_center_of_mem_ctuBlock hF
    (by omega) (fun h => by have := congrArg Prod.fst h; simp at this; omega)
    (Finset.mem_singleton_self (0 : Fin 3)) hβc hβR
  rw [mem_bot]
  exact β.injective (h1.trans (map_one β).symm)

end Piece

section Values

variable {K F : Type} [Field K] [Field F] [CharP K 2] [Finite F] [CharP F 2]

noncomputable abbrev twoUniTransvection {ε : ℕ} (hε : ε ≤ 1) (ι : K →+* F)
    (hι : ∀ c, unitaryInvolution F 2 1 (ι c) = ι c) : SU (unitaryInvolution F 2 1) (2 * 4 + ε) :=
  ctuEmbed ε hε (unitaryInvolution F 2 1) ι hι (elt (.positiveLong (1 : Fin 4)) 1)

noncomputable abbrev twoUniRankTwo {ε : ℕ} (hε : ε ≤ 1) (ι : K →+* F)
    (hι : ∀ c, unitaryInvolution F 2 1 (ι c) = ι c) : SU (unitaryInvolution F 2 1) (2 * 4 + ε) :=
  ctuEmbed ε hε (unitaryInvolution F 2 1) ι hι (elt (.positiveSum (1 : Fin 4) 2 (by decide)) 1)

@[expose] def TwoUniBlockValues (κ : Sp6Kind) {ε : ℕ} (hε : ε ≤ 1) (ι : K →+* F)
    (hι : ∀ c, unitaryInvolution F 2 1 (ι c) = ι c) : Prop :=
  Nat.card (ctuBlock (unitaryInvolution F 2 1) ε ({3, 0} : Finset (Fin 4))) =
      twoDiagPieceOrder κ ∧
    Nat.card (centralizer ({twoUniTransvection hε ι hι} :
        Set (SU (unitaryInvolution F 2 1) (2 * 4 + ε))) ⊓
        ctuBlock (unitaryInvolution F 2 1) ε ({3, 0} : Finset (Fin 4)) :
          Subgroup (SU (unitaryInvolution F 2 1) (2 * 4 + ε))) = twoOverlapInvOrderL κ ∧
    Nat.card (centralizer ({twoUniRankTwo hε ι hι} :
        Set (SU (unitaryInvolution F 2 1) (2 * 4 + ε))) ⊓
        ctuBlock (unitaryInvolution F 2 1) ε ({3, 0} : Finset (Fin 4)) :
          Subgroup (SU (unitaryInvolution F 2 1) (2 * 4 + ε))) = twoOverlapInvOrderS κ

theorem twoGraphCoverModel_twoUniIota {κ : Sp6Kind} (hK : Nat.card K = 2)
    (hF : Nat.card F = (2 ^ 1) ^ 2) {ε : ℕ} (hε : ε ≤ 1) {ι : K →+* F}
    (hι : ∀ c, unitaryInvolution F 2 1 (ι c) = ι c) (hV : TwoUniBlockValues κ hε ι hι) :
    TwoGraphCoverModel κ K (ctuBlock (unitaryInvolution F 2 1) ε ({3} : Finset (Fin 4)))
      (twoUniIota hε hι) := by
  obtain ⟨hV1, hV2, hV3⟩ := hV
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; norm_num)
  have hO := map_centralizerPerfectCore_twoUniIota (K := K) hF hε hι
  have hinj := (ctuBlock (unitaryInvolution F 2 1) ε ({3} : Finset (Fin 4))).subtype_injective
  refine ⟨⟨?_, fun _ => ⟨?_, ?_⟩⟩, centralizerPerfectCore_twoUniIota_inf_center hF hε hι,
    map_twoUniIota_rootGroupL_le hF hε hι, map_twoUniIota_rootGroupS_le hF hε hι⟩
  · rw [← Subgroup.card_map_of_injective hinj, hO, hV1]
  · rw [← Subgroup.card_map_of_injective hinj, ← centralizer_map_inf_map_of_injective hinj, hO,
      Subgroup.map_map, centralizer_map_rootGroup_eq hK _ stdVec_positiveLong_one,
      MonoidHom.comp_apply, coe_subtype, coe_twoUniIota_elt_positiveLong]
    exact hV2
  · rw [← Subgroup.card_map_of_injective hinj, ← centralizer_map_inf_map_of_injective hinj, hO,
      Subgroup.map_map, centralizer_map_rootGroup_eq hK _ stdVec_positiveSum_one_two,
      MonoidHom.comp_apply, coe_subtype, coe_twoUniIota_elt_positiveSum]
    exact hV3

end Values

end CFSG.SeitzReduction.F4Pilot
