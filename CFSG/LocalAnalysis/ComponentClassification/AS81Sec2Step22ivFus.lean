module

public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec2F0Plane

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.ComponentClassification.AS81

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.RankTwoStandard

variable {G : Type} [Group G] [Finite G]

section Frame

variable {A R : Subgroup G} {g : G} {E F : Subgroup G}

theorem card_le_of_isElemAbelian_le_sup_centralizer (h11 : Step11) (hF : Frame G A A R g E F)
    (hL : TypeL34 (rankTwoQuot A)) (hodd : Odd (Nat.card (center ↥A))) {D : Subgroup G}
    (hD : IsElemAbelian 2 D) (hDAK : D ≤ A ⊔ centralizer (A : Set G)) : Nat.card D ≤ 64 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hstd := hF.base.hyp.standard
  have hNK := AS76b.normalizer_centralizer_eq hstd
  have hR := hF.sylowR
  set K := centralizer (A : Set G) with hK
  have hD2 := isPGroup_two_of_isElemAbelian hD
  have hKN : K ≤ normalizer (A : Set G) := Subgroup.centralizer_le_normalizer _
  have hDNK : D ≤ normalizer (K : Set G) := by
    rw [hNK]
    exact hDAK.trans (sup_le le_normalizer hKN)
  obtain ⟨X, hX, hDX⟩ := AschbacherTheorem3.exists_isSylowOf_le hD2 (le_sup_left : D ≤ D ⊔ K)
  have hR' : IsSylowOf 2 (X ⊓ K) K :=
    hX.inf_of_le_normalizer le_sup_right (sup_le hDNK le_normalizer)
  have hDR' : D ≤ normalizer ((X ⊓ K : Subgroup G) : Set G) := fun d hd =>
    inf_normalizer_le_normalizer_inf ⟨le_normalizer (hDX hd), hDNK hd⟩
  have hDAR' := le_sup_of_le_sup_normalizer hR' hD2 hDR' hDAK
  obtain ⟨c, -, hc⟩ := AschbacherTheorem3.exists_rightConjugate_eq_of_isSylowOf hR' hR
  have hR'4 : Nat.card (X ⊓ K : Subgroup G) = 4 := by rw [← hc, rightConjugate_card, hF.cardR]
  exact card_le_of_isElemAbelian_le_sup_sylow_frame h11 hF hL hodd hR' hR'4 hD hDAR'

variable (h11 : Step11) {d : L34E16Cert}
  (hE16 : RankTwoL3Four.HypII.l34CheckWE16 d = true) (hF : Frame G A A R g E F)
  (hL : TypeL34 (rankTwoQuot A)) (hodd : Odd (Nat.card (center ↥A)))

include h11 hE16 hF hL hodd

theorem card_le_of_le_centralizer_conj {r : G} (hr : r ∈ R) (hr1 : r ≠ 1) (x : G)
    {D : Subgroup G} (hD : IsElemAbelian 2 D)
    (hDC : D ≤ centralizer ({x * r * x⁻¹} : Set G)) : Nat.card D ≤ 64 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hstd := hF.base.hyp.standard
  have hKte := AS76b.tightlyEmbedded_centralizer hstd
  have hNK := AS76b.normalizer_centralizer_eq hstd
  have hR := hF.sylowR
  set D' := rightConjugate D x with hD'
  have hD'e : IsElemAbelian 2 D' := AS76b.isElemAbelian_rightConjugate hD x
  have hcard : Nat.card D' = Nat.card D := rightConjugate_card D x
  have hD'r : ∀ y ∈ D', y * r = r * y := fun y hy => by
    rw [hD', mem_rightConjugate_iff] at hy
    have h1 := mem_centralizer_iff.mp (hDC hy) (x * r * x⁻¹) (Set.mem_singleton _)
    have h2 : x * (r * y) * x⁻¹ = x * (y * r) * x⁻¹ := by
      calc x * (r * y) * x⁻¹ = (x * r * x⁻¹) * (x * y * x⁻¹) := by group
        _ = (x * y * x⁻¹) * (x * r * x⁻¹) := h1
        _ = x * (y * r) * x⁻¹ := by group
    exact (mul_left_cancel (mul_right_cancel h2)).symm
  have hD'N : D' ≤ normalizer (A : Set G) := fun y hy => by
    rw [← hNK]
    exact RankTwoSporadic.mem_normalizer_of_commute_of_tightlyEmbedded hKte (hR.le hr) hr1
      (hF.elemR.2 r hr) (hD'r y hy)
  rw [← hcard]
  by_cases h64 : 16 * Nat.card R ≤ Nat.card D'
  · obtain ⟨e₀⟩ := PSL3Four.nonempty_equiv_of_stated (↥A ⧸ center ↥A) hL
    exact card_le_of_isElemAbelian_le_sup_centralizer h11 hF hL hodd hD'e
      (le_sup_centralizer_of_sixteen_le hE16 hF.quasisimple.1 e₀ hR hD'N hD'e h64)
  · rw [hF.cardR] at h64
    omega

theorem conj_not_mem_of_card_lt {r : G} (hr : r ∈ R) (hr1 : r ≠ 1) (x : G) {D : Subgroup G}
    (hD : IsElemAbelian 2 D) (h64 : 64 < Nat.card D) : x * r * x⁻¹ ∉ D := by
  intro hmem
  have hDC : D ≤ centralizer ({x * r * x⁻¹} : Set G) := fun d hd =>
    mem_centralizer_iff.mpr fun t ht => by
      rw [Set.mem_singleton_iff.mp ht]
      exact congrArg Subtype.val (hD.1.is_comm.comm ⟨_, hmem⟩ ⟨d, hd⟩)
  have := card_le_of_le_centralizer_conj h11 hE16 hF hL hodd hr hr1 x hD hDC
  omega

omit h11 hE16 in
theorem exists_conj_mem_sec2Z {t : G} (htA : t ∈ A) (ht2 : t ^ 2 = 1) (ht1 : t ≠ 1) :
    ∃ b ∈ A, b * t * b⁻¹ ∈ sec2Z A E F := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hq := hF.quasisimple
  obtain ⟨c⟩ := nonempty_l34Cover_of_odd hq hL hodd
  obtain ⟨S, hS, htS⟩ := exists_isSylowOf_mem_centerIn c htA ht2 ht1
  have hRA : R ≤ centralizer (A : Set G) := hF.sylowR.le
  obtain ⟨-, hT₀, -⟩ := sylow_sup_structure hRA hF.sylowR.isPGroup hF.sylow
  obtain ⟨b, hbA, hb⟩ := AschbacherTheorem3.exists_rightConjugate_le_of_isSylowOf hT₀
    hS.isPGroup hS.le
  have hbeq : rightConjugate S b = (E ⊔ F) ⊓ A :=
    eq_of_le_of_card_ge hb (by rw [rightConjugate_card, hS.card_eq, hT₀.card_eq])
  refine ⟨b⁻¹, inv_mem hbA, ?_⟩
  rw [hF.sec2Z_eq, centerIn_inf_eq hF, ← hbeq]
  refine ⟨?_, mem_centralizer_iff.mpr fun s hs => ?_⟩
  · show b⁻¹ * t * b⁻¹⁻¹ ∈ rightConjugate S b
    rw [mem_rightConjugate_iff]
    simpa [mul_assoc] using htS.1
  · have hs' : s ∈ rightConjugate S b := hs
    rw [mem_rightConjugate_iff] at hs'
    have h1 := mem_centralizer_iff.mp htS.2 (b * s * b⁻¹) hs'
    have h2 : b * (s * (b⁻¹ * t * b⁻¹⁻¹)) * b⁻¹ = b * ((b⁻¹ * t * b⁻¹⁻¹) * s) * b⁻¹ := by
      calc b * (s * (b⁻¹ * t * b⁻¹⁻¹)) * b⁻¹ = (b * s * b⁻¹) * t := by group
        _ = t * (b * s * b⁻¹) := h1
        _ = b * ((b⁻¹ * t * b⁻¹⁻¹) * s) * b⁻¹ := by group
    exact mul_left_cancel (mul_right_cancel h2)

theorem conj_not_mem_of_sec2Z_le {D : Subgroup G} (hD : IsElemAbelian 2 D)
    (h64 : 64 < Nat.card D) (hZD : sec2Z A E F ≤ D) {r : G} (hr : r ∈ R) (hr1 : r ≠ 1) (x : G) :
    x * r * x⁻¹ ∉ A := by
  intro hA
  have ht2 : (x * r * x⁻¹) ^ 2 = 1 := by
    have := hF.elemR.2 r hr
    calc (x * r * x⁻¹) ^ 2 = x * (r * r) * x⁻¹ := by rw [sq]; group
      _ = 1 := by rw [← sq, this]; group
  have ht1 : x * r * x⁻¹ ≠ 1 := fun h => hr1 (by
    have := congrArg (fun z => x⁻¹ * z * x) h
    simpa [mul_assoc] using this)
  obtain ⟨b, -, hb⟩ := exists_conj_mem_sec2Z hF hL hodd hA ht2 ht1
  refine conj_not_mem_of_card_lt h11 hE16 hF hL hodd hr hr1 (b * x) hD h64 (hZD ?_)
  have : b * x * r * (b * x)⁻¹ = b * (x * r * x⁻¹) * b⁻¹ := by group
  rw [this]
  exact hb

end Frame

end CFSG.ComponentClassification.AS81
