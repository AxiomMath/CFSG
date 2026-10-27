module

public import CFSG.GH74.Generic.BProg.B3.S3T3H
public import CFSG.GH74.Generic.BProg.B3.S3T3L
public import CFSG.GH74.Generic.BProg.B3.S3Sec29H1
public import CFSG.GH74.Generic.BProg.B3.S3Ctx29K26
public import Certificates.Kernel.ThCent.Leaves
public import CFSG.GH74.GLS.Bg.Iii2.L41Comp
public import CFSG.GH74.Generic.BProg.B3.S3Boot293
public import CFSG.GH74.Generic.BProg.B3.S3BootObs52
public import CFSG.GH74.Generic.BProg.B3.S3BootSym7
public import CFSG.GH74.Generic.BProg.B3.S3Rk2Rank
public import CFSG.GH74.Generic.BProg.B3.S3Sec29C5
public import CFSG.GH74.Generic.S45.LUniLift
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitKG
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitPSL
public import CFSG.RankThree.PartOne.KC.UnitaryCrossPrimeOrbits
public import CFSG.Sporadic.Th.Max3.Packet
public import CFSG.Sporadic.Th.Max3.Quotient
public import Certificates.Certificate10091Base

public section

namespace CFSG.GH74.Generic.BProg.B3

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.Generic CFSG.GH74.Generic.BProg CFSG.Blueprint
  CFSG.Assembly.LowTwoRank CFSG.LocalCores CFSG.ClassicalInvolution.Balance Subgroup
  CFSG.ABGLocalTools
open scoped commutatorElement

namespace S3T3

variable {G : Type} [Group G] [Finite G]

theorem exists_Bstar {x y : G} {K A B Q J : Subgroup G} (hB : H29 G x K A B Q y)
    (hJ : IsPCompIn 2 (centralizer ({y} : Set G)) J) (hJA7 : IsA7Bar J)
    (hBN : B ≤ normalizer (J : Set G)) (e : kBar J ≃* alternatingGroup (Fin 7))
    {F₀ F₁ : Subgroup (Equiv.Perm (Fin 7))} (hF : ImageF0F1 B J e F₀ F₁) :
    ∃ Bs : Subgroup G, CFSG.IsElementaryAbelian 2 ↥Bs ∧ Nat.card ↥Bs = 16 ∧ x ∈ Bs ∧ y ∈ Bs ∧
      Bs ≤ centralizer ({x} : Set G) ∧ Bs ≤ centralizer ({y} : Set G) ∧
      Bs ≤ normalizer (J : Set G) ∧ Bs ≤ K ⊔ CxK x K ∧ 4 ≤ Nat.card ↥(Bs ⊓ cSec K) ∧
      ∀ R : Subgroup (Equiv.Perm (Fin 7)),
        R ≤ (Bs.subgroupOf (normalizer (J : Set G))).map (GLS.Th2.Obs.a7Act J e) →
          ¬ GLS.Th2.Obs.IsRootFour R := by
  classical
  obtain ⟨hF₀, hF₁, hFeq⟩ := hF
  set φ := GLS.Th2.Obs.a7Act J e with hφ
  set F : Subgroup (Equiv.Perm (Fin 7)) := (B.subgroupOf (normalizer (J : Set G))).map φ
    with hFdef
  obtain ⟨hAB, hxB, hBCx, hBel, -, -, hBeq⟩ := hB.ext
  obtain ⟨hBc, hBsq⟩ := C3.Layer1.Back.forall_of_isElementaryAbelian hBel
  obtain ⟨hyA, hyK⟩ := Subgroup.mem_inf.1 hB.y_mem
  have hyB : y ∈ B := hAB hyA
  have hB16 : Nat.card ↥B = 16 := by
    rw [C3.Layer1.Back.card_eq_two_pow_pRank hBel, hB.rankB]
    norm_num
  have hx2 : orderOf x = 2 := hB.circ.1.1.1.1
  have hKc : IsPCompIn 2 (centralizer ({x} : Set G)) K := hB.circ.1.1.1.2.2
  have hZ := B1.PilotS3.center_trivial_of_shape3 hKc hB.shape.qShape3
  have hBy : B ≤ centralizer ({y} : Set G) := fun g hg =>
    mem_centralizer_singleton_iff.mpr (hBc g hg y hyB)
  have hxC : x ∈ CxK x K :=
    Subgroup.mem_inf.2 ⟨mem_centralizer_singleton_iff.2 rfl,
      S3Ctx29.mem_cSec_of_le_centralizer hKc.1⟩
  have hφx : φ ⟨x, hBN hxB⟩ ∈ F := ⟨⟨x, hBN hxB⟩, hxB, rfl⟩
  obtain ⟨u, huA, hu2, hu1, F', hF'F, hF'2, hxF', -, hF'u, huF', hnoR⟩ :=
    lemma2911 hF₀ hF₁ hFeq hφx
  have huF : u ∉ F := by
    intro huF
    have hc : ∀ f ∈ F', f * u = u * f := hF'u
    have hcard := S3Sec29H.card_sup_zpowers hu2 huF' hc
    have heq : F' ⊔ zpowers u = F :=
      Subgroup.eq_of_le_of_card_ge (sup_le hF'F (zpowers_le.2 huF)) (by omega)
    have hF₀F : F₀ ≤ F := by
      rw [hFeq]
      exact le_sup_left
    exact hnoR F₀ (by rw [heq]; exact hF₀F) hF₀
  set B' : Subgroup G := S3Sec29H1.pre hBN e F' with hB'def
  have hB'B : B' ≤ B := S3Sec29H1.pre_le hBN e F'
  have hB'2 : 2 * Nat.card ↥B' = Nat.card ↥B := by
    refine S3Sec29H1.two_mul_card_pre hBN e ?_ ?_
    · rw [S3Sec29H1.range_bAct]
      exact hF'F
    · rw [S3Sec29H1.range_bAct]
      exact hF'2
  have hxB' : x ∈ B' := S3Sec29H1.mem_pre.2 ⟨hxB, hxF'⟩
  have hyJ : φ ⟨y, hBN hyB⟩ = 1 := by
    rw [hφ, GLS.Th2.Obs.a7Act_eq_one_iff, GLS.Th2.Obs.barAct_eq_one_iff]
    exact S3Ctx29.mem_cSec_of_le_centralizer hJ.1
  have hyB' : y ∈ B' := S3Sec29H1.mem_pre.2 ⟨hyB, by rw [hyJ]; exact one_mem _⟩
  have hB'el : CFSG.IsElementaryAbelian 2 ↥B' := Th2Sig6.isElementaryAbelian_of_le hBel hB'B
  obtain ⟨v, hvJ, hv2, hv1, hvc, hφv⟩ := S3Sec29H1.exists_v e (hB'B.trans hBN)
    (CFSG.IsElementaryAbelian.isPGroup 2 ↥B') huA hu2 hu1
    (fun p hp => hF'u _ (S3Sec29H1.mem_pre.1 hp).2)
  have hvB : v ∉ B := by
    intro hvB
    apply huF
    rw [← hφv]
    exact ⟨⟨v, hBN hvB⟩, hvB, rfl⟩
  have hvB' : v ∉ B' := fun h => hvB (hB'B h)
  have hvy : v * y = y * v := (Subgroup.mem_centralizer_singleton_iff.1 (hJ.1 hvJ))
  have hvx : v * x = x * v := (hvc x hxB').symm
  obtain ⟨E, hEK, hAE, -, -, -, hyE⟩ := H29.exists_E hB
  have hy1 : y ≠ 1 := by
    intro h1
    have := hB.y_ord
    rw [h1, orderOf_one] at this
    omega
  obtain ⟨hI, -, hSL, -⟩ := k26_proved G x K A E y hB.circ.1.2.2 hB.shape.qShape3 hB.src hEK hAE
    hyE hy1
  have hyx : y ∈ centralizer ({x} : Set G) := hBCx hyB
  have hLJ : Ly29 K y ≤ cSec J := le_cSec_of_dih hx2 hKc hyx hJ (Or.inl hJA7) hI hSL
  have hvxC : v ∈ centralizer ({x} : Set G) := mem_centralizer_singleton_iff.2 hvx
  have hvK : v ∈ normalizer (K : Set G) :=
    S3Sec29C.mem_normalizer_of_comm hKc hZ hyK hB.y_ord hvxC hvy
  have hvL : v ∈ normalizer ((Ly29 K y : Subgroup G) : Set G) :=
    S3Ctx29Layer.mem_normalizer_pLayerOf_of_mem_normalizer
      (TwoThin.mem_normalizer_inf hvK (Subgroup.le_normalizer (hJ.1 hvJ)))
  have hvLc : v ∈ cSec (Ly29 K y) := mem_cSec_of_le_cSec hLJ hvJ hvL
  have hv' := S3Sec29C.unique_involution hKc hB.shape.qShape3 hyK hB.y_ord
    (P := zpowers v) (zpowers_le.2 hvxC) (zpowers_le.2 hvK)
    (S3Sec29C.fixesLayer_of_cSec hKc hB.y_ord (zpowers_le.2 hvxC) (zpowers_le.2 hvLc))
    v (mem_zpowers v) (by rw [hv2]; exact one_mem _)
  have hy2 : y * y = 1 := hBsq y hyB
  have hyi : y⁻¹ = y := inv_eq_of_mul_eq_one_right hy2
  obtain ⟨v', hv'C, hv'eq⟩ : ∃ v' : G, v' ∈ CxK x K ∧ (v' = v ∨ v' = v * y) := by
    rcases hv' with h | h
    · exact ⟨v, Subgroup.mem_inf.2 ⟨hvxC, h⟩, Or.inl rfl⟩
    · rw [hyi] at h
      exact ⟨v * y, Subgroup.mem_inf.2 ⟨mul_mem hvxC hyx, h⟩, Or.inr rfl⟩
  have hcv : ∀ h ∈ B', h * v = v * h := hvc
  refine ⟨B' ⊔ zpowers v, S3Sec29H.isElementaryAbelian_sup_zpowers hB'el hv2 hcv, ?_,
    Subgroup.mem_sup_left hxB', Subgroup.mem_sup_left hyB', ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [S3Sec29H.card_sup_zpowers hv2 hvB' hcv, hB'2, hB16]
  · exact sup_le (hB'B.trans hBCx) (zpowers_le.2 hvxC)
  · exact sup_le (hB'B.trans hBy) (zpowers_le.2 (hJ.1 hvJ))
  · exact sup_le (hB'B.trans hBN) (zpowers_le.2 (Subgroup.le_normalizer hvJ))
  ·
    have hBKC : B ≤ K ⊔ CxK x K := by
      rw [hBeq, hAE]
      refine sup_le (sup_le (hEK.trans le_sup_left) (zpowers_le.2 (Subgroup.mem_sup_right hxC)))
        (hB.B0_le_C.trans le_sup_right)
    refine sup_le (hB'B.trans hBKC) (zpowers_le.2 ?_)
    rcases hv'eq with rfl | rfl
    · exact Subgroup.mem_sup_right hv'C
    · have : v = v * y * y := by rw [mul_assoc, hy2, mul_one]
      rw [this]
      exact mul_mem (Subgroup.mem_sup_right hv'C) (Subgroup.mem_sup_left hyK)
  ·
    have hv'B : v' ∈ B' ⊔ zpowers v := by
      rcases hv'eq with rfl | rfl
      · exact Subgroup.mem_sup_right (mem_zpowers _)
      · exact mul_mem (Subgroup.mem_sup_right (mem_zpowers _)) (Subgroup.mem_sup_left hyB')
    have hv'2 : v' * v' = 1 := by
      rcases hv'eq with rfl | rfl
      · exact hv2
      · calc v * y * (v * y) = v * (y * v) * y := by group
          _ = v * (v * y) * y := by rw [hvy]
          _ = (v * v) * (y * y) := by group
          _ = 1 := by rw [hv2, hy2, one_mul]
    have hv'x : v' ∉ zpowers x := by
      intro h
      have hv'BB : v' ∈ B := zpowers_le.2 hxB h
      rcases hv'eq with rfl | rfl
      · exact hvB hv'BB
      · apply hvB
        have := B.mul_mem hv'BB hyB
        rwa [mul_assoc, hy2, mul_one] at this
    have hxv' : ∀ h ∈ zpowers x, h * v' = v' * h := by
      intro h hh
      obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hh
      exact (Commute.zpow_left (show Commute x v' from
        (Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 hv'C).1).symm) i).eq
    have hcard := S3Sec29H.card_sup_zpowers hv'2 hv'x hxv'
    rw [Nat.card_zpowers, hx2] at hcard
    have hle : zpowers x ⊔ zpowers v' ≤ (B' ⊔ zpowers v) ⊓ cSec K :=
      sup_le (zpowers_le.2 (Subgroup.mem_inf.2 ⟨Subgroup.mem_sup_left hxB',
        (Subgroup.mem_inf.1 hxC).2⟩))
        (zpowers_le.2 (Subgroup.mem_inf.2 ⟨hv'B, (Subgroup.mem_inf.1 hv'C).2⟩))
    have := Subgroup.card_le_of_le hle
    omega
  ·
    intro R hR
    refine hnoR R (hR.trans ?_)
    rintro _ ⟨m, hm, rfl⟩
    have hmB : (m : G) ∈ B' ⊔ zpowers v := Subgroup.mem_subgroupOf.1 hm
    obtain ⟨h, hh, hmh | hmh⟩ := S3Sec29H.mem_sup_zpowers hv2 hcv hmB
    · obtain ⟨hhB, hhF⟩ := S3Sec29H1.mem_pre.1 hh
      have : m = ⟨h, hBN hhB⟩ := Subtype.ext hmh
      rw [this]
      exact Subgroup.mem_sup_left hhF
    · obtain ⟨hhB, hhF⟩ := S3Sec29H1.mem_pre.1 hh
      have : m = ⟨h, hBN hhB⟩ * ⟨v, Subgroup.le_normalizer hvJ⟩ := Subtype.ext hmh
      rw [this, map_mul, hφv]
      exact mul_mem (Subgroup.mem_sup_left hhF) (Subgroup.mem_sup_right (mem_zpowers u))

end S3T3

end CFSG.GH74.Generic.BProg.B3
