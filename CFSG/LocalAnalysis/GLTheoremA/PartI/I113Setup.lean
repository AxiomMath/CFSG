module

public import CFSG.HardMathSupport.Solomon.Coordinator.I11_2FullTransport
public import CFSG.HardMathSupport.Solomon.LocalBalance.PartIInputs2
import CFSG.LocalAnalysis.GLTheoremA.PComp
import CFSG.Milestones.OO_odd_order_solvable
public import CFSG.HardMathSupport.Timmesfeld.ComponentBalance.I_11_3_Triple
public import CFSG.LocalAnalysis.GLTheoremA.Basic

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I113

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Timmesfeld.ComponentBalance
  CFSG.HardMathSupport.Solomon.LocalBalance
open scoped commutatorElement

theorem two_dvd_card_of_quasisimple {K : Type*} [Group K] [Finite K]
    (hK : CFSG.Open.IsQuasisimple K) : 2 ∣ Nat.card K := by
  by_contra h
  have hodd : Odd (Nat.card K) := Nat.odd_iff.2 (Nat.two_dvd_ne_zero.1 h)
  have : Group.IsSolvable K := CFSG.Milestones.odd_order_solvable hodd
  have : Nontrivial K := isQuasisimple_nontrivial hK
  have : Group.IsPerfect K := ⟨hK.1⟩
  exact Group.IsPerfect.not_isSolvable K ‹_›

theorem card_le_nine_of_pRank {L : Type} [Group L] [Finite L]
    (h : CFSG.Open.pRank 3 (⊤ : Subgroup (MulAut L)) ≤ 2) :
    ∀ E : Subgroup (MulAut L), IsElemAbelian 3 E → Nat.card E ≤ 9 := by
  intro E hE
  obtain ⟨k, hk⟩ := exists_card_eq_pow_of_isElemAbelian Nat.prime_three hE
  have h1 : k ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (MulAut L)) :=
    CFSG.SectionRank.le_pRank Nat.prime_three.one_lt le_top hE hk
  rw [hk]
  calc 3 ^ k ≤ 3 ^ 2 := Nat.pow_le_pow_right (by norm_num) (h1.trans h)
    _ = 9 := by norm_num

theorem isSUThreeTwoPow_of_mulEquiv {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y)
    (h : IsSUThreeTwoPow X) : IsSUThreeTwoPow Y := by
  obtain ⟨F, hF, hfin, n, h1, h2, h3, hc, ⟨f⟩⟩ := h
  exact ⟨F, hF, hfin, n, h1, h2, h3, hc, ⟨e.symm.trans f⟩⟩

variable {G : Type} [Group G] [Finite G]

theorem mk_eq_one_iff {p : ℕ} {X : Subgroup G} {x : G} (hx : x ∈ X) :
    QuotientGroup.mk' (GLAPPrimeCore p ↥X) ⟨x, hx⟩ = 1 ↔ x ∈ GLAPPrimeCoreOf p X := by
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  constructor
  · intro h
    exact ⟨⟨x, hx⟩, h, rfl⟩
  · rintro ⟨y, hy, hyx⟩
    have : y = ⟨x, hx⟩ := Subtype.ext hyx
    exact this ▸ hy

theorem barX_B0_eq {X B K : Subgroup G} (hBX : B ≤ X) (hBel : IsElemAbelian 3 B)
    (hK : GLAPComponent 3 X K) :
    barX 3 X (B ⊓ centModSubgroup 3 K) = t113B0 (barX 3 X B) (barX 3 X K) := by
  have hp3 : Nat.Prime 3 := Nat.prime_three
  set π := QuotientGroup.mk' (GLAPPrimeCore 3 ↥X) with hπ
  have hBel' : IsElemAbelian 3 (barX 3 X B) := isElemAbelian_barX hBel
  have hOK : GLAPPrimeCoreOf 3 K ≤ GLAPPrimeCoreOf 3 X := glaPPrimeCoreOf_le_of_isSubnormal hp3 hK.2.1
  have hcent : barX 3 X (B ⊓ centModSubgroup 3 K) ≤
      Subgroup.centralizer ((barX 3 X K : Subgroup (↥X ⧸ GLAPPrimeCore 3 ↥X)) :
        Set (↥X ⧸ GLAPPrimeCore 3 ↥X)) := by
    refine barX_le_centralizer (p := 3) (C := X) (S := B ⊓ centModSubgroup 3 K) (T := K) ?_
    intro s hs t ht _ _
    have h1 : ⁅t, s⁆ ∈ GLAPPrimeCoreOf 3 K := hs.2.2 t ht
    have h2 : ⁅t, s⁆⁻¹ ∈ GLAPPrimeCoreOf 3 X := Subgroup.inv_mem _ (hOK h1)
    rw [commutatorElement_inv] at h2
    simpa [commutatorElement_def] using h2
  ext z
  constructor
  · intro hz
    have hz' : z ∈ barX 3 X B :=
      i112f_barX_mono (inf_le_left : B ⊓ centModSubgroup 3 K ≤ B) hz
    refine ⟨hz', ?_⟩
    have hM : ∀ m ∈ barX 3 X K, z * m = m * z := fun m hm =>
      (Subgroup.mem_centralizer_iff.1 (hcent hz) m hm).symm
    have hle : t113K (barX 3 X B) (barX 3 X K) ≤ Subgroup.centralizer ({z} : Set _) := by
      refine iSup₂_le fun g hg w hw => ?_
      rw [Subgroup.mem_centralizer_singleton_iff]
      have h1 : Commute z (g * w * g⁻¹) := hM _ (mem_gLBConj.1 hw)
      have h2 : Commute z g := isElemAbelian_commute hBel' hz' hg
      have h3 : Commute z (g⁻¹ * (g * w * g⁻¹) * g) := (h2.inv_right.mul_right h1).mul_right h2
      have e : g⁻¹ * (g * w * g⁻¹) * g = w := by group
      rw [e] at h3
      exact h3.eq.symm
    intro w hw
    exact Subgroup.mem_centralizer_singleton_iff.1 (hle hw)
  · rintro ⟨hzB, hzC⟩
    obtain ⟨b, hb, rfl⟩ := hzB
    have hbB : (b : G) ∈ B := Subgroup.mem_subgroupOf.1 hb
    have hMK : barX 3 X K ≤ t113K (barX 3 X B) (barX 3 X K) := by
      have := le_iSup₂_of_le (f := fun (g : ↥X ⧸ GLAPPrimeCore 3 ↥X) (_ : g ∈ barX 3 X B) =>
        GLBConj g (barX 3 X K)) 1 (barX 3 X B).one_mem (by rw [gLBConj_one])
      exact this
    have hcM : ∀ m ∈ barX 3 X K, m * π b = π b * m := fun m hm =>
      Subgroup.mem_centralizer_iff.1 (Subgroup.mem_centralizer_iff.1 hzC |> fun h => by
        exact Subgroup.mem_centralizer_iff.2 fun h' hh' => h h' (hMK hh')) m hm
    have hnorm : (b : G) ∈ Subgroup.normalizer (K : Set G) := by
      have h1 : π b ∈ Subgroup.normalizer ((barX 3 X K : Subgroup (↥X ⧸ GLAPPrimeCore 3 ↥X)) :
          Set (↥X ⧸ GLAPPrimeCore 3 ↥X)) :=
        Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.2 hcM)
      have h2 : b ∈ (Subgroup.normalizer (K : Set G)).subgroupOf X := by
        rw [← i112f_comap_normalizer_barX hK]
        exact h1
      exact Subgroup.mem_subgroupOf.1 h2
    have hcm : (b : G) ∈ centModSubgroup 3 K := by
      refine ⟨hnorm, fun l hl => ?_⟩
      have hlX : l ∈ X := hK.1 hl
      have hl1 : ⁅l, (b : G)⁆ ∈ K := by
        have h1 : (b : G) * l⁻¹ * (b : G)⁻¹ ∈ K :=
          (Subgroup.mem_normalizer_iff.1 hnorm l⁻¹).1 (Subgroup.inv_mem _ hl)
        have := K.mul_mem hl h1
        simpa [commutatorElement_def, mul_assoc] using this
      have hlbX : ⁅l, (b : G)⁆ ∈ X := by
        rw [commutatorElement_def]
        exact X.mul_mem (X.mul_mem (X.mul_mem hlX b.2) (X.inv_mem hlX)) (X.inv_mem b.2)
      have hl2 : ⁅l, (b : G)⁆ ∈ GLAPPrimeCoreOf 3 X := by
        rw [← mk_eq_one_iff hlbX]
        have hcomm : π ⟨l, hlX⟩ * π b = π b * π ⟨l, hlX⟩ :=
          hcM (π ⟨l, hlX⟩) ⟨⟨l, hlX⟩, Subgroup.mem_subgroupOf.2 hl, rfl⟩
        have e : (⟨⁅l, (b : G)⁆, hlbX⟩ : ↥X) = ⟨l, hlX⟩ * b * ⟨l, hlX⟩⁻¹ * b⁻¹ :=
          Subtype.ext (by simp [commutatorElement_def])
        rw [e, map_mul, map_mul, map_mul, map_inv, map_inv, hcomm, ← hπ]
        group
      have hl3 : ⁅l, (b : G)⁆ ∈ K ⊓ GLAPPrimeCoreOf 3 X := ⟨hl1, hl2⟩
      rwa [glaPPrimeCoreOf_inf_eq_of_isSubnormal hp3 hK.2.1] at hl3
    exact ⟨b, Subgroup.mem_subgroupOf.2 ⟨hbB, hcm⟩, rfl⟩

end CFSG.LocalAnalysis.GLTheoremA.I113
