module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y6F61
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y6Frat
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y6Quo
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y6Trans

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1 CFSG.GH74.GLS
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem y6_card_map_mul_card_ker {X C K : Subgroup G} {Q : Type*} [Group Q] (hCX : C ≤ X)
    (hKC : K ≤ C) (ψ : ↥X →* Q) (hker : ψ.ker = K.subgroupOf X) :
    Nat.card ↥((C.subgroupOf X).map ψ) * Nat.card ↥K = Nat.card ↥C := by
  have hrange : (ψ.domRestrict (C.subgroupOf X)).range = (C.subgroupOf X).map ψ :=
    MonoidHom.domRestrict_range (C.subgroupOf X) ψ
  have hkerf : (ψ.domRestrict (C.subgroupOf X)).ker = ψ.ker.subgroupOf (C.subgroupOf X) := rfl
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup
    (ψ.domRestrict (C.subgroupOf X)).ker
  have h2 : Nat.card (↥(C.subgroupOf X) ⧸ (ψ.domRestrict (C.subgroupOf X)).ker) =
      Nat.card ↥(ψ.domRestrict (C.subgroupOf X)).range :=
    Nat.card_congr (QuotientGroup.quotientKerEquivRange (ψ.domRestrict (C.subgroupOf X))).toEquiv
  have h3 : Nat.card ↥(ψ.domRestrict (C.subgroupOf X)).ker = Nat.card ↥K := by
    have hle : K.subgroupOf X ≤ C.subgroupOf X := fun x hx => hKC hx
    rw [hkerf, hker]
    exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv).trans
      (Nat.card_congr (Subgroup.subgroupOfEquivOfLe (hKC.trans hCX)).toEquiv)
  have h4 : Nat.card ↥(C.subgroupOf X) = Nat.card ↥C :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hCX).toEquiv
  rw [← hrange, ← h3, ← h2, ← h4]
  exact h1.symm

theorem y6_four123 (c : Ctx6 G L) (hH : F33Hyp c.s c.e) (hF : c.toCtx5.Facts5)
    (hRT : c.s.R ≠ c.s.T) : c.Four1 ∧ c.Four2 ∧ c.Four3 := by
  have cfg := c.y6cfg hH
  obtain ⟨ψ, hker, hK, hCY, hXC, hA6, -, h720⟩ := y6_main c hH hF
  have hNC1 := y6_NC1_eq c hH hF
  have hNC0 := y6_NC0_eq c hH hF
  have hF61 := y6_fact61 c hH hF
  have hKpN : centralizerSection (AV1 c.e) (V1 c.e) ≤ normalizer (AV1 c.e : Set G) :=
    fun x hx => hx.1
  have hKpV : centralizerSection (AV1 c.e) (V1 c.e) ≤ normalizer (V1 c.e : Set G) :=
    fun x hx => hx.2.1
  have hNAV_le : normalizer (C1 c.e : Set G) ≤ normalizer (AV1 c.e : Set G) := hF61.2.1
  have hNAVV : normalizer (AV1 c.e : Set G) ≤ normalizer (V1 c.e : Set G) := hF61.2.2.1
  have hC1Kp : C1 c.e ≤ centralizerSection (AV1 c.e) (V1 c.e) := y6_C1_le_Kp cfg
  have hKpX : centralizerSection (AV1 c.e) (V1 c.e) ⊓ y6X c = C1 c.e := by
    refine le_antisymm ?_ (le_inf hC1Kp (le_inf Subgroup.le_normalizer (y6_C1_le_N_V cfg)))
    intro x hx
    obtain ⟨hxKp, hxX⟩ := Subgroup.mem_inf.mp hx
    have hxAV : ∀ w ∈ c.s.fr.A ⊔ V1 c.e, ⁅w, x⁆ ∈ V1 c.e := hxKp.2.2
    have hxK : x ∈ y6K c :=
      y6_trans cfg (Subgroup.mem_inf.mp hxX).1 (Subgroup.mem_inf.mp hxX).2 hxAV
    rw [hK] at hxK
    exact hxK
  have hC1p : IsPGroup 2 ↥(C1 c.e) := by
    have h128 : Nat.card ↥(C1 c.e) = 2 ^ 7 := by
      have h := y6_card_C1 cfg
      rw [show (2 : ℕ) ^ 7 = 128 by norm_num]
      exact h
    exact IsPGroup.of_card h128
  have hsyl : IsSylowIn 2 (centralizerSection (AV1 c.e) (V1 c.e)) (C1 c.e) := by
    refine ⟨hC1Kp, hC1p, y6_sylow_of_self_normalizing hC1Kp hC1p ?_⟩
    intro x hxKp hxN
    have hxX : x ∈ y6X c := Subgroup.mem_inf.mpr ⟨hxN, hKpV hxKp⟩
    have hmem := Subgroup.mem_inf.mpr ⟨hxKp, hxX⟩
    rwa [hKpX] at hmem
  have hnormKp : ((centralizerSection (AV1 c.e) (V1 c.e)).subgroupOf
      (normalizer (AV1 c.e : Set G))).Normal :=
    y6_centSec_normal le_rfl hNAVV
  have hNAV : normalizer (AV1 c.e : Set G) =
      normalizer (C1 c.e : Set G) ⊔ centralizerSection (AV1 c.e) (V1 c.e) := by
    refine le_antisymm ?_ (sup_le hNAV_le hKpN)
    exact (y6_frattini hKpN hnormKp hC1Kp hC1p hsyl.2.2).trans
      (sup_le_sup_right inf_le_left _)
  have hψsurj : Function.Surjective ψ := by
    have hrange : ψ.range = ⊤ := by
      refine Subgroup.eq_top_of_card_eq _ ?_
      rw [h720 hRT, Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
      decide
    exact MonoidHom.range_eq_top.mp hrange
  have hkerKp : ψ.ker = (centralizerSection (AV1 c.e) (V1 c.e)).subgroupOf (y6X c) := by
    rw [hker, hK, ← hKpX]
    exact Subgroup.inf_subgroupOf_right _ _
  have hsup : normalizer (AV1 c.e : Set G) =
      y6X c ⊔ centralizerSection (AV1 c.e) (V1 c.e) := by
    rw [hNAV, hNC1]
  have hXN : y6X c ≤ normalizer (AV1 c.e : Set G) := by
    rw [← hNC1]
    exact hNAV_le
  obtain ⟨φ, hφsurj, hφker, -⟩ :=
    y6_quot_of_sup hKpN hnormKp hXN hsup ψ hψsurj hkerKp
  have hCle : y6C c ≤ y6X c := inf_le_left
  have hC1C : C1 c.e ≤ y6C c := by
    have hKX : y6K c ≤ y6X c := fun x hx => Subgroup.mem_inf.mpr ⟨hx.1, hx.2.1⟩
    rw [← hK]
    exact le_inf hKX (y6_K_le_NC0 cfg)
  have hker' : ψ.ker = (C1 c.e).subgroupOf (y6X c) := by rw [hker, hK]
  have h72 : Nat.card ↥(((y6C c).subgroupOf (y6X c)).map ψ) = 72 := by
    have h := y6_card_map_mul_card_ker hCle hC1C ψ hker'
    have hY36 : Nat.card ↥(y6Y c) = 36 * Nat.card ↥(C1 c.e) := (y6_card_Y_m c.toCtx5 hH).2 hRT
    have hpos : 0 < Nat.card ↥(C1 c.e) := Nat.card_pos
    have h' : Nat.card ↥(((y6C c).subgroupOf (y6X c)).map ψ) * Nat.card ↥(C1 c.e) =
        72 * Nat.card ↥(C1 c.e) := by
      rw [h, hCY, hY36]
      ring
    exact Nat.eq_of_mul_eq_mul_right hpos h'
  obtain ⟨ψ', hψ'surj, hψ'ker⟩ := y6_quotIso_blockStab hCle ψ hkerKp h72
  have hNK : normalizer (AV1 c.e : Set G) ≤
      normalizer ((centralizerSection (AV1 c.e) (V1 c.e) : Subgroup G) : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKpN).mp hnormKp
  have hN'le : normalizer (C0 c.e : Set G) ⊔ centralizerSection (AV1 c.e) (V1 c.e) ≤
      normalizer (AV1 c.e : Set G) := by
    refine sup_le ?_ hKpN
    rw [hNC0]
    exact (hCle.trans hXN)
  have hnormN' : ((centralizerSection (AV1 c.e) (V1 c.e)).subgroupOf
      (normalizer (C0 c.e : Set G) ⊔ centralizerSection (AV1 c.e) (V1 c.e))).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_right).mpr (hN'le.trans hNK)
  have hsup' : normalizer (C0 c.e : Set G) ⊔ centralizerSection (AV1 c.e) (V1 c.e) =
      y6C c ⊔ centralizerSection (AV1 c.e) (V1 c.e) := by rw [hNC0]
  have hCN' : y6C c ≤ normalizer (C0 c.e : Set G) ⊔ centralizerSection (AV1 c.e) (V1 c.e) := by
    rw [hsup']
    exact le_sup_left
  obtain ⟨φ', hφ'surj, hφ'ker, -⟩ :=
    y6_quot_of_sup le_sup_right hnormN' hCN' hsup' ψ' hψ'surj hψ'ker
  refine ⟨⟨hKpN, φ, hφsurj, hφker⟩, ⟨hsyl, hNAV⟩, ⟨le_sup_right, φ', hφ'surj, hφ'ker⟩⟩

end CFSG.OddStandard.HigherRank.YamadaG23
