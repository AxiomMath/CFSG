module

public import CFSG.GH74.Generic.BProg.B3.S3PumpKey
public import CFSG.GH74.Generic.S45.LDiagMain
public import CFSG.GH74.Generic.BProg.B2.TwoA7Geo
public import Certificates.Kernel.ThCent.Leaves

public section

namespace CFSG.GH74.Generic.BProg.B3

namespace S3Pump304

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.Generic CFSG.GH74.Generic.S3 CFSG.GH74.Generic.S45
  CFSG.GH74.Generic.BProg CFSG.GH74.Generic.BProg.B3.S3Fusion CFSG.Blueprint CFSG.ABGLocalTools
  CFSG.Assembly.LowTwoRank CFSG.GH74.L5U5 Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem eq_of_imgBar_eq {x : G} {J K : Subgroup G}
    (hJ : IsPCompIn 2 (centralizer ({x} : Set G)) J)
    (hK : IsPCompIn 2 (centralizer ({x} : Set G)) K)
    (he : S3.imgBar x J = S3.imgBar x K) : J = K := by
  have h := CFSG.ComponentClassification.OddKernelTwoComponents.lift_unique
    (TwoThin.barMk ↥(centralizer ({x} : Set G))) TwoThin.barMk_surjective TwoThin.odd_card_ker_barMk
    (J.subgroupOf (centralizer ({x} : Set G))) (K.subgroupOf (centralizer ({x} : Set G)))
    (TwoThin.isPCompIn_two_iff.mp hJ).2 (TwoThin.isPCompIn_two_iff.mp hK).2 he
  have h3 := Subgroup.subgroupOf_inj.1 h
  rwa [inf_of_le_left hJ.1, inf_of_le_left hK.1] at h3

theorem layer_C_eq {x : G} {K : Subgroup G} (hK : IsPCompIn 2 (centralizer ({x} : Set G)) K)
    (hkey : ∀ P : Subgroup (CentralizerBar x), P ≤ centralizer
      ((S3.imgBar x K : Subgroup (CentralizerBar x)) : Set (CentralizerBar x)) →
        ⁅P, P⁆ = P → P = ⊥) :
    pLayerOf 2 (centralizer ({x} : Set G)) = K := by
  refine le_antisymm (sSup_le fun J hJ => ?_) (le_sSup hK)
  by_cases hJK : J = K
  · exact hJK.le
  · exfalso
    have hJc := isComponent_imgBar hJ
    have hKc := isComponent_imgBar hK
    have hne : S3.imgBar x J ≠ S3.imgBar x K := fun e => hJK (eq_of_imgBar_eq hJ hK e)
    have hJC : S3.imgBar x J ≤ centralizer
        ((S3.imgBar x K : Subgroup (CentralizerBar x)) : Set (CentralizerBar x)) := by
      intro a ha
      rw [Subgroup.mem_centralizer_iff]
      intro k hk
      exact S45.comm_of_ne_components hKc hJc (Ne.symm hne) k hk a ha
    have hperf : ⁅S3.imgBar x J, S3.imgBar x J⁆ = S3.imgBar x J :=
      Subgroup.isPerfect_iff.1 hJc.1.1
    have hbot := hkey _ hJC hperf
    obtain ⟨a, b, hab⟩ := S45.exists_noncomm_of_isQuasisimple hJc.1
    have h1 : ∀ z ∈ S3.imgBar x J, z = 1 := fun z hz => by
      rw [hbot] at hz
      exact Subgroup.mem_bot.1 hz
    apply hab
    apply Subtype.ext
    simp [h1 a a.2, h1 b b.2]

theorem pLayer_U_eq {x y : G} {K : Subgroup G} (hy : orderOf y = 2)
    (hK : IsPCompIn 2 (centralizer ({x} : Set G)) K) (hyC : y ∈ centralizer ({x} : Set G))
    (hlayer : pLayerOf 2 (centralizer ({x} : Set G)) = K) :
    pLayerOf 2 (centralizer ({x} : Set G) ⊓ centralizer ({y} : Set G)) =
      pLayerOf 2 (K ⊓ centralizer ({y} : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine le_antisymm ?_ ?_
  ·
    have hU : zpowers y ≤ centralizer ({x} : Set G) := Subgroup.zpowers_le.2 hyC
    have h1 := B2.SD.TwoA7Geo.pLayerOf_inf_centralizer_le_two hU
      (B1.isPGroup_two_zpowers_of_orderOf hy)
    have hcen : centralizer ({x} : Set G) ⊓ centralizer ((zpowers y : Subgroup G) : Set G) =
        centralizer ({x} : Set G) ⊓ centralizer ({y} : Set G) := by
      ext g
      rw [Subgroup.mem_inf, Subgroup.mem_inf]
      constructor
      · rintro ⟨h2, h3⟩
        refine ⟨h2, ?_⟩
        rw [Subgroup.mem_centralizer_iff] at h3 ⊢
        intro h hh
        rw [Set.mem_singleton_iff.1 hh]
        exact h3 y (Subgroup.mem_zpowers y)
      · rintro ⟨h2, h3⟩
        refine ⟨h2, ?_⟩
        rw [Subgroup.mem_centralizer_iff] at h3 ⊢
        intro h hh
        obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 (SetLike.mem_coe.1 hh)
        have hcy : y * g = g * y := h3 y (Set.mem_singleton y)
        exact (Commute.zpow_left (show Commute y g from hcy) k).eq
    rw [hcen, hlayer] at h1
    refine sSup_le fun J hJ => ?_
    have hJK : J ≤ K := le_trans (le_sSup hJ) h1
    have hJy : J ≤ centralizer ({y} : Set G) := hJ.1.trans inf_le_right
    exact le_sSup (Lemma212Aux.isPCompIn_of_le hJ (le_inf hJK hJy) (inf_le_inf_right _ hK.1))
  ·
    have hsub := B1.isSubnormal_subgroupOf_inf (S := centralizer ({y} : Set G))
      (B1.isSubnormal_of_isPCompIn hK)
    exact sSup_le fun L hL =>
      le_sSup (B1.isPCompIn_of_isSubnormal 2 (inf_le_inf_right _ hK.1) hsub hL)

theorem prop304_of_F {x y : G} {K A T : Subgroup G} (h : Setup30 G x K A y) (hT : IsZT x y T)
    (hF : Prop301Concl x y T) :
    pLayerOf 2 (centralizer ({x} : Set G)) = K ∧
      pLayerOf 2 (centralizer ({x} : Set G) ⊓ centralizer ({y} : Set G)) = Ly K y := by
  have hcfg := cfg_of_setup30 h hT
  obtain ⟨⟨n, hn, hnx⟩, -⟩ := hF
  have hnT : n ∈ normalizer (T : Set G) := (Subgroup.mem_inf.1 hn).1
  have hny : n * y * n⁻¹ = y := by
    have := mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 hn).2
    rw [this]
    group
  have hlayer : pLayerOf 2 (centralizer ({x} : Set G)) = K :=
    layer_C_eq hcfg.hK fun P hPC hP =>
      S3PumpKey.Cfg.perfect_C_eq_bot hcfg hnT hnx hny hPC hP
  exact ⟨hlayer, (pLayer_U_eq hcfg.hy hcfg.hK hcfg.hyC hlayer)⟩

end S3Pump304

end CFSG.GH74.Generic.BProg.B3
