module

public import CFSG.ClassicalInvolution.SmallCases.NDB5dWC
public import CFSG.ClassicalInvolution.SmallCases.NDB5dSp2
public import CFSG.ClassicalInvolution.SmallCases.NDB5Main
import CFSG.ClassicalInvolution.ModelFacts.LinearAutFrame
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate76
public import Certificates.Certificate77
public import Certificates.Certificate78
public import Certificates.Certificate79
public import Certificates.Certificate80
public import Certificates.Certificate81
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate115
public import Certificates.Certificate116
public import Certificates.Certificate117
public import Certificates.Certificate118
public import Certificates.Certificate119
public import Certificates.Certificate120
public import Certificates.Certificate121
public import Certificates.Certificate122
public import Certificates.Certificate123

public section

namespace CFSG.ClassicalInvolution.NDB.WC

open CFSG.Open CFSG.ComponentClassification CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Balance.Bootstrap CFSG.ClassicalInvolution.Asc77.ExactLayer
open CFSG.RankThreeCoreUniqueness.Helpers (perfectResidualOf)
open scoped MatrixGroups

local notation "𝒞" => Generic.CoreAssembly.conjClass

variable {G : Type} [Group G] [Finite G]

theorem inf_oddCoreIn_le {F : Type} [Field F] [Finite F] (h2 : (2 : F) ≠ 0)
    (h4 : 4 ≤ Nat.card F) {s z : G} {L : Subgroup G}
    (hL : L ≤ Subgroup.centralizer ({z} : Set G) ⊓ Subgroup.centralizer ({s} : Set G))
    {φ : SL(2, F) →* OddQuot z} (hφ : Function.Injective φ) (himg : modOdd z L = φ.range) :
    L ⊓ oddCoreIn (Subgroup.centralizer ({s} : Set G)) ≤
      oddCoreIn (Subgroup.centralizer ({z} : Set G)) := by
  set Cs := Subgroup.centralizer ({s} : Set G) with hCs
  set Cz := Subgroup.centralizer ({z} : Set G) with hCz
  set N := L ⊓ oddCoreIn Cs with hN
  set P := (modOdd z N).comap φ with hP
  have hNL : modOdd z N ≤ φ.range := himg ▸ Bootstrap.modOdd_mono inf_le_left
  have hPn : P.Normal := by
    refine ⟨fun y hy g => ?_⟩
    have hgL : φ g ∈ modOdd z L := by
      rw [himg]
      exact ⟨g, rfl⟩
    obtain ⟨⟨l, hlC⟩, hl, hlg⟩ := hgL
    obtain ⟨⟨n, hnC⟩, hn, hny⟩ := hy
    have hlL : l ∈ L := hl
    have hnN : n ∈ N := hn
    have hls : l ∈ Cs := (hL hlL).2
    have hmem : l * n * l⁻¹ ∈ N :=
      ⟨L.mul_mem (L.mul_mem hlL hnN.1) (L.inv_mem hlL), conj_mem_oddCoreIn hls hnN.2⟩
    show φ (g * y * g⁻¹) ∈ modOdd z N
    rw [map_mul, map_mul, map_inv, ← hlg, ← hny]
    refine ⟨⟨l, hlC⟩ * ⟨n, hnC⟩ * ⟨l, hlC⟩⁻¹, hmem, ?_⟩
    rw [map_mul, map_mul, map_inv]
  have hNz : N ≤ Cz := inf_le_left.trans (hL.trans inf_le_left)
  have hPodd : Odd (Nat.card P) := by
    have e : Nat.card P = Nat.card (modOdd z N) := by
      rw [← Subgroup.card_map_of_injective (K := P) hφ, Subgroup.map_comap_eq_self hNL]
    rw [e]
    have hc1 : Nat.card (modOdd z N) ∣ Nat.card (N.subgroupOf Cz) := Subgroup.card_map_dvd _ _
    have hc2 : Nat.card (N.subgroupOf Cz) = Nat.card N :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNz).toEquiv
    have hc3 : Nat.card N ∣ Nat.card (oddCoreIn Cs) := Subgroup.card_dvd_of_le inf_le_right
    exact Odd.of_dvd_nat (Odd.of_dvd_nat (odd_card_oddCoreIn Cs) hc3) (hc2 ▸ hc1)
  have hPbot : P = ⊥ := by
    have hle : P ≤ classicalInvolutionOddCore SL(2, F) := le_sSup ⟨hPn, hPodd⟩
    rw [ModelFacts.LinearAut.oddCore_sl2_eq_bot h2 h4] at hle
    exact le_bot_iff.mp hle
  have hNbot : modOdd z N = ⊥ := by
    rw [← Subgroup.map_comap_eq_self hNL, ← hP, hPbot, Subgroup.map_bot]
  intro x hx
  have hxC : x ∈ Cz := hNz hx
  have h1 : oddQuotMk z ⟨x, hxC⟩ ∈ modOdd z N := oddQuotMk_mem_modOdd hx hxC
  rw [hNbot, Subgroup.mem_bot] at h1
  exact ⟨⟨x, hxC⟩, oddQuotMk_eq_one_iff.mp h1, rfl⟩

variable {p f : ℕ} [Fact p.Prime] [IsSimpleGroup G]

theorem weak_closure_of_vertexLayer_core {K : Subgroup G} {z : G} (hS : SettingCore p f K z)
    {K₁ K₂ K₃ : Subgroup G} {z₁ z₂ z₃ t₁ t₂ t₃ w₁ w₂ : G}
    (hax : PSpAxis p f (𝒞 K) K₁ K₂ K₃ z₁ z₂ z₃ t₁ t₂ t₃ w₁ w₂) {L₁ : Subgroup G}
    (hL₁ : IsVertexLayer p f (𝒞 K) K₁ K₂ K₃ z₁ z₂ z₃ t₁ t₂ t₃ L₁) {h : G}
    (hh : h ∈ Subgroup.centralizer ({t₁ * t₂ * t₃} : Set G))
    (hR : ∀ x ∈ modOdd (t₁ * t₂ * t₃) (conjSub h L₁), ∀ y ∈ modOdd (t₁ * t₂ * t₃) L₁,
      x * y = y * x) :
    modOdd (t₁ * t₂ * t₃) (conjSub h L₁) = modOdd (t₁ * t₂ * t₃) L₁ := by
  obtain ⟨hN₁, D₁, i₀, i₁, R₂, R₃, r₂, r₃, ι, VL⟩ := hL₁
  have hp2 := hS.odd
  have hq := hS.five
  set C₁ : Asc77.XCtx p f (𝒞 K) z₁ := ⟨K₁, hax.mem₁,
    ConnectedA2.isUniqueInvolution_of_isClassicalMember hp2 hq hax.cls₁,
    Cover.hypOmegaMod hS.nonabelian hp2 hq hS.member hS.below, hp2, hq, D₁⟩ with hC₁
  have hi₁ : ¬ (C₁.D.tag i₁ = .PSL ∧ C₁.D.rank i₁ = 2) := fun h1 => by
    have h2 := h1.1
    rw [show C₁.D.tag i₁ = .PSp from VL.tag] at h2
    exact absurd h2 (by decide)
  have hi₀ : C₁.D.tag i₀ = .PSL ∧ C₁.D.rank i₀ = 2 := by
    obtain ⟨j, hj, -⟩ := C₁.exists_A1_of_K
    rcases eq_or_eq_of_card_two VL.card VL.ne j with rfl | rfl
    · exact hj
    · exact absurd hj hi₁
  have hz₁ : z₁ = t₁ * t₁ := hax.sq₁.symm
  have hcz : ∀ x : G, x * t₁ = t₁ * x → x ∈ Subgroup.centralizer ({z₁} : Set G) := fun x hx => by
    rw [Subgroup.mem_centralizer_singleton_iff, hz₁]
    calc x * (t₁ * t₁) = t₁ * x * t₁ := by rw [← mul_assoc, hx]
      _ = t₁ * t₁ * x := by rw [mul_assoc, hx, ← mul_assoc]
  have ht₁z := hcz t₁ rfl
  have ht₂z := hcz t₂ hax.ct₁₂.symm
  have ht₃z := hcz t₃ hax.ct₁₃.symm
  have hs : t₁ * t₂ * t₃ ∈ Subgroup.centralizer ({z₁} : Set G) :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ ht₁z ht₂z) ht₃z
  have hvC : t₂ * t₃ ∈ Subgroup.centralizer ({z₁} : Set G) := Subgroup.mul_mem _ ht₂z ht₃z
  have hsv : t₁ * t₂ * t₃ = t₂ * t₃ * t₁ := by
    rw [hax.ct₁₂, mul_assoc t₂ t₁ t₃, hax.ct₁₃, ← mul_assoc]
  have hv : oddQuotMk z₁ ⟨t₂ * t₃, hvC⟩ ∈ (C₁.psi i₁).range := ⟨r₂ * r₃, (VL.tau hvC).symm⟩
  have he : D₁.exp i₁ = f := by
    rcases D₁.exp_eq i₁ with h1 | ⟨h1, -⟩
    · exact h1
    · rw [VL.tag] at h1
      exact absurd h1 (by decide)
  have h2' : (2 : GaloisField p (D₁.exp i₁)) ≠ 0 := ModelFacts.two_ne_zero_galoisField _ hp2
  have h4'' : 4 ≤ p ^ D₁.exp i₁ := by rw [he]; omega
  have h4' : 4 ≤ Nat.card (GaloisField p (D₁.exp i₁)) := by
    rw [GaloisField.card p _ (by rintro h0; rw [h0] at h4''; simp at h4'')]
    exact h4''
  have hLO := inf_oddCoreIn_le h2' h4' VL.le (φ := (secComponentHom hN₁ D₁ i₁).comp ι)
    (VL.inj₁.comp VL.ι_inj) (by rw [VL.img, MonoidHom.range_comp])
  have hSp : ∀ x ∈ (C₁.psi i₁).range, x * x = 1 →
      x * oddQuotMk z₁ ⟨t₂ * t₃, hvC⟩ = oddQuotMk z₁ ⟨t₂ * t₃, hvC⟩ * x →
        (∀ y ∈ modOdd z₁ L₁, x * y = y * x) →
          x = 1 ∨ x = oddQuotMk z₁ ⟨z₁, Asc77.XCtx.hzC z₁⟩ := by
    rintro _ ⟨y, rfl⟩ hy2 hyv hyL
    have hinj : Function.Injective (C₁.psi i₁) := VL.inj₁
    have hy2' : y * y = 1 := hinj (by rw [map_mul, map_one]; exact hy2)
    have e' : C₁.psi i₁ (r₂ * r₃) = oddQuotMk z₁ ⟨t₂ * t₃, hvC⟩ := (VL.tau hvC).symm
    have hyu : y * (r₂ * r₃) = r₂ * r₃ * y := hinj (by
      rw [map_mul (C₁.psi i₁) y (r₂ * r₃), map_mul (C₁.psi i₁) (r₂ * r₃) y, e']
      exact hyv)
    have hyc : ∀ w ∈ perfectResidualOf (Subgroup.centralizer
        ({r₂ * r₃} : Set (compModel D₁ i₁).K)), y * w = w * y := by
      rw [VL.ι_range]
      rintro _ ⟨B, rfl⟩
      apply hinj
      rw [map_mul, map_mul]
      exact hyL _ (by rw [VL.img]; exact ⟨ι B, ⟨B, rfl⟩, rfl⟩)
    have hz₂C : z₂ ∈ Subgroup.centralizer ({z₁} : Set G) := by
      rw [← hax.sq₂]
      exact Subgroup.mul_mem _ ht₂z ht₂z
    have hz₃C : z₃ ∈ Subgroup.centralizer ({z₁} : Set G) := by
      rw [← hax.sq₃]
      exact Subgroup.mul_mem _ ht₃z ht₃z
    have hne1 : ∀ {r : (compModel D₁ i₁).K} {w : G} (hw : w ∈ Subgroup.centralizer ({z₁} : Set G)),
        w * w = 1 → secComponentHom hN₁ D₁ i₁ r = oddQuotMk z₁ ⟨w, hw⟩ → w ≠ 1 → r ≠ 1 := by
      intro r w hw hw2 hrw hw1 hr1
      rw [hr1, map_one] at hrw
      exact hw1 (congrArg Subtype.val (eq_one_of_oddQuotMk_eq_one
        (show (⟨w, hw⟩ : Subgroup.centralizer ({z₁} : Set G)) * ⟨w, hw⟩ = 1 from Subtype.ext hw2)
        hrw.symm))
    have hz₂1 : z₂ ≠ 1 := fun h1 => by
      have := hax.cls₂.orderOf_eq_two
      rw [h1, orderOf_one] at this
      exact absurd this (by decide)
    have hz₃1 : z₃ ≠ 1 := fun h1 => by
      have := hax.cls₃.orderOf_eq_two
      rw [h1, orderOf_one] at this
      exact absurd this (by decide)
    have hx1 := hne1 hz₂C hax.cls₂.isCentralInvolution.sq (VL.sq₂ hz₂C) hz₂1
    have hx'1 := hne1 hz₃C hax.cls₃.isCentralInvolution.sq (VL.sq₃ hz₃C) hz₃1
    have hsq : r₂ * r₂ * (r₂ * r₂)⁻¹ ∈ Subgroup.center (compModel D₁ i₁).K := by
      rw [mul_inv_cancel]
      exact Subgroup.one_mem _
    have hsq' : r₃ * r₃ * (r₃ * r₃)⁻¹ ∈ Subgroup.center (compModel D₁ i₁).K := by
      rw [mul_inv_cancel]
      exact Subgroup.one_mem _
    rcases Sp.eq_of_centralizes_model hp2 (D₁.tag i₁) (D₁.rank i₁) (D₁.exp i₁) VL.tag VL.rank
      (D₁.admissible i₁) h4'' VL.fund₂ VL.fund₃ VL.ne₂₃ (Subgroup.mul_mem _ VL.mem₂ VL.mem₂)
      VL.cen₂ hx1 (Subgroup.mul_mem _ VL.mem₃ VL.mem₃) VL.cen₃ hx'1 VL.same VL.mem₂ VL.mem₃ hsq
      hsq' hy2' hyu hyc with h1 | h1
    · left
      rw [h1, map_one]
    · right
      have hz₁2 : z₁ * z₁ = 1 := hax.cls₁.isCentralInvolution.sq
      rw [h1, map_mul, map_inv]
      show secComponentHom hN₁ D₁ i₁ (r₂ * r₂) * (secComponentHom hN₁ D₁ i₁ (r₃ * r₃))⁻¹ = _
      rw [VL.sq₂ hz₂C, VL.sq₃ hz₃C, ← map_inv, ← map_mul]
      congr 1
      apply Subtype.ext
      show z₂ * z₃⁻¹ = z₁
      rw [← hax.prod]
      calc z₂ * (z₁ * z₂)⁻¹ = z₁⁻¹ := by group
        _ = z₁ := (eq_inv_of_mul_eq_one_left hz₁2).symm
  exact weak_closure hS.nonabelian hp2 hq hS.below C₁ VL.card VL.ne hi₀ hi₁ VL.range₀ hs hax.ht₁
    hax.sq₁ hvC hsv hv VL.le VL.normal (Subgroup.isPerfect_iff.mp VL.perfect) VL.mem hLO hSp hh hR

end CFSG.ClassicalInvolution.NDB.WC
