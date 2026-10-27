module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinPerp23ThreeZStar

public section

set_option linter.unusedSectionVars false

namespace CFSG.CGT.PushingUpLit.SolKNA.R4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Asc77.Thompson
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc
open CFSG.ClassicalInvolution.Balance
open CFSG.ClassicalInvolution.Balance.Bootstrap (trivialOnQuot)
open scoped commutatorElement

namespace Perp22Wyl

section Lift


variable {r : ℕ} {Y : Type} [Group Y] [Finite Y] {Ω : Set (Subgroup Y)} {W : Subgroup Y}

theorem exists_lift_to_D (hr : 4 ≤ r) (hΩ : HypOmegaGen Ω)
    (h2all : ∀ M ∈ Ω, IsPGroup 2 (↥M ⧸ classicalInvolutionOddCore ↥M))
    (hq : ∀ M ∈ Ω, ∀ P : Subgroup Y, IsSylow2In P M →
      Nonempty (↥P ≃* QuaternionGroup (2 ^ (r - 2))))
    (hA : ∀ M ∈ Ω, AEmpty Ω M)
    (h16 : ∀ J ∈ Ω, ∀ P : Subgroup Y, IsSylow2In P J → 16 ≤ Nat.card P)
    (hW : W ∈ WSet Ω) (hc : ∀ x ∈ W, ∀ y ∈ W, x * y = y * x) {a : Y} (ha2 : a * a = 1)
    (ha1 : a ≠ 1) (haW : a ∈ W) (ρ : Rep Ω W) {z : Y} (hz : IsUniqueInvolution ρ.K z)
    (hzC : z ∈ Subgroup.centralizer ({a} : Set Y)) (hρtq : a ∈ trivialOnQuot ρ.K)
    (hρa : ρ.R ≤ Subgroup.centralizer ({a} : Set Y))
    (hin : TightInO2 (centBarMk a hzC)) :
    ∀ c ∈ Subgroup.centralizer ({a} : Set Y),
      ∃ o ∈ oddCoreIn (Subgroup.centralizer ({a} : Set Y)), ∃ P : Subgroup Y,
        P ∈ DSet Ω W ∧ IsSylow2In P (conjSub (o * c) ρ.K) := by
  classical
  set C : Subgroup Y := Subgroup.centralizer ({a} : Set Y) with hCdef
  have hc2 : IsPGroup 2 (Subgroup.zpowers a) := isPGroup_zpowers_of_mul_self_eq_one ha2 ha1
  have hKtq : ρ.K ∈ Q3NL.tqMembers3 Ω a := ⟨ρ.hK, hρtq⟩
  obtain ⟨hRWK, hUmem, hcyc, -, hcardR⟩ :=
    Q3CL.Thompson.inf_W_of_mem_D hΩ hW ρ.hR ρ.hK ρ.hRK
  have hW2 : IsPGroup 2 W := isPGroup_of_mem_WSet hW
  set U₁ : Subgroup Y := ρ.R ⊓ W with hU₁def
  have hUc : IsCyclic ↥U₁ := hcyc
  have hUP : U₁ ≤ ρ.R := inf_le_left
  have hUi : U₁.relIndex ρ.R = 2 := Sec7.relIndex_eq_two_of_card hUP hcardR
  have hU₁C : U₁ ≤ C := hUP.trans hρa
  have hUK : U₁ ≤ ρ.K := hUP.trans ρ.hRK.1
  have hU₁mem : U₁ ∈ USet Ω := by rw [hRWK]; exact hUmem
  have hU₁2 : IsPGroup 2 ↥U₁ := Sec6Gen.isPGroup_of_mem_USet hΩ hU₁mem
  have hWC : W ≤ C := fun w hw => Subgroup.mem_centralizer_singleton_iff.mpr (hc w hw a haW)
  obtain ⟨Q, hQn, hQ2, hUQ⟩ := Perp23.Three.exists_normal_two_group_U hr hΩ hc2 h2all hq hA hKtq hz
    hzC hin ρ.hRK hρa hUP hUc hUi
  obtain ⟨T, hWT, hT2, hTlift⟩ := Perp23.Three.exists_two_group_lift hQn hQ2 hW2 hWC
  intro c hcC
  have hVC : conjSub c U₁ ≤ C := Perp23.Three.conjSub_le_centralizer hcC hU₁C
  have hV2 : IsPGroup 2 ↥(conjSub c U₁) := Perp23.Three.isPGroup_conjSub' hU₁2 c
  have hVQ : ∀ (v : Y) (hv : v ∈ conjSub c U₁), centBarMk a (hVC hv) ∈ Q := by
    intro v hv
    have hv' : c⁻¹ * v * c ∈ U₁ := mem_conjSub_iff.mp hv
    have h1 := hUQ _ hv'
    have h2 := hQn.conj_mem _ h1 (centBarMk a hcC)
    have e : centBarMk a hcC * centBarMk a (hρa (hUP hv')) * (centBarMk a hcC)⁻¹ =
        centBarMk a (hVC hv) := by
      rw [Perp23.Three.centBarMk_inv hcC, Perp23.Three.centBarMk_mul, Perp23.Three.centBarMk_mul]
      exact Perp23.Three.centBarMk_congr _ _ (by group)
    rwa [e] at h2
  obtain ⟨o, ho, hoV⟩ := hTlift (conjSub c U₁) hVC hV2 hVQ
  have hoC : o ∈ C := oddCoreIn_le C ho
  set g : Y := o * c with hg
  have hgC : g ∈ C := C.mul_mem hoC hcC
  have hUβT : conjSub g U₁ ≤ T := by
    have e : conjSub g U₁ = conjSub o (conjSub c U₁) := conjSub_mul o c U₁
    rw [e]; exact hoV
  set J : Subgroup Y := conjSub g ρ.K with hJdef
  have hJΩ : J ∈ Ω := hΩ.conjInvariant g _ ρ.hK
  have hUβmem : conjSub g U₁ ∈ USet Ω := USet.conj hΩ.conjInvariant hU₁mem g
  have hUβJ : conjSub g U₁ ≤ J := conjSub_mono hUK
  obtain ⟨S₁, hTS⟩ := hT2.exists_le_sylow
  have hWS : W ≤ (S₁ : Subgroup Y) := hWT.trans hTS
  obtain ⟨-, -, -, -, -, -, -, -, hUβ4⟩ := Sec6Gen.exists_data_of_mem_USet hΩ hUβmem
  have hUβ2 : IsPGroup 2 ↥(conjSub g U₁) := Perp23.Three.isPGroup_conjSub' hU₁2 g
  have hcard : 2 < Nat.card ↥(J ⊓ (S₁ : Subgroup Y)) := by
    have := Subgroup.card_le_of_le (le_inf hUβJ (hUβT.trans hTS))
    omega
  have hJW : J ⊓ W ∈ USet Ω := WTool.inf_mem_USet_of_card hΩ hW hWS hJΩ hcard
  have hUβeq : conjSub g U₁ = J ⊓ W :=
    WTool.eq_of_mem_USet_of_isPGroup hΩ h16 hJΩ hT2 hUβmem hJW hUβJ inf_le_left hUβT
      (inf_le_right.trans hWT)
  have hUβW : conjSub g U₁ ≤ W := hUβeq ▸ inf_le_right
  have hwJ : ∀ w ∈ W, conjSub w J = J := by
    intro w hw
    have h1 : conjSub w J ∈ Ω := hΩ.conjInvariant w J hJΩ
    have h2 : conjSub g U₁ ≤ conjSub w J := by
      intro u hu
      have hcomm : w * u * w⁻¹ = u := by rw [hc w hw u (hUβW hu)]; group
      rw [← hcomm]
      exact conj_mem_conjSub (hUβJ hu)
    exact Sec6Gen.eq_of_le_of_le hΩ h1 hJΩ hUβ2 hUβ4 h2 hUβJ
  set Q' : Subgroup Y := conjSub g ρ.R with hQ'def
  have hQ'J : IsSylow2In Q' J := ρ.hRK.conj g
  have hQ'C : Q' ≤ C := Perp23.Three.conjSub_le_centralizer hgC hρa
  have hUβQ' : conjSub g U₁ ≤ Q' := conjSub_mono hUP
  have hUβnorm : ∀ x ∈ Q', ∀ u ∈ conjSub g U₁, x * u * x⁻¹ ∈ conjSub g U₁ := by
    intro x hx u hu
    rw [mem_conjSub_iff] at hx hu ⊢
    have h1 := Perp23.Three.conj_mem_of_relIndex_two hUP hUi hx hu
    have e : g⁻¹ * (x * u * x⁻¹) * g = (g⁻¹ * x * g) * (g⁻¹ * u * g) * (g⁻¹ * x * g)⁻¹ := by group
    rw [e]; exact h1
  have hRJ : Q' ≤ J ⊓ C := le_inf hQ'J.1 hQ'C
  have hQ'JC : IsSylow2In Q' (J ⊓ C) :=
    ⟨hRJ, hQ'J.2.1, fun V hV hV2 hQV => hQ'J.2.2 V (hV.trans inf_le_left) hV2 hQV⟩
  obtain ⟨P, hPJ', hP2, hPmax, hUβP, hWP⟩ := Perp23.Three.exists_sylow_normalized_by_two_group
    (W := W) (J := J ⊓ C) (U := conjSub g U₁) (R := Q') hW2
    (fun w hw x hx => by
      refine Subgroup.mem_inf.mpr ⟨?_, C.mul_mem (C.mul_mem (hWC hw) hx.2) (C.inv_mem (hWC hw))⟩
      have := conj_mem_conjSub (n := w) hx.1
      rwa [hwJ w hw] at this)
    (fun w hw x hx => by rw [hc w hw x (hUβW hx)]; group)
    hRJ hQ'J.2.1 hQ'JC.2.2 hUβQ' hUβnorm
  have hPsyl' : IsSylow2In P (J ⊓ C) := ⟨hPJ', hP2, hPmax⟩
  have hPJ : IsSylow2In P J :=
    Perp23.Three.isSylow2In_of_natCard_le hQ'J (hPJ'.trans inf_le_left) hP2
      (hPsyl'.natCard_eq hQ'JC).symm.le
  have hWN : W ≤ Subgroup.normalizer (P : Set Y) := by
    intro w hw
    rw [Subgroup.mem_normalizer_iff]
    intro x
    refine ⟨fun hx => hWP w hw x hx, fun hx => ?_⟩
    have := hWP w⁻¹ (W.inv_mem hw) _ hx
    simpa [mul_assoc] using this
  have hPW2 : IsPGroup 2 ↥(P ⊔ W) := hP2.to_sup_of_normal_left' hW2 hWN
  have hPN : P ≤ Subgroup.normalizer (W : Set Y) :=
    le_sup_left.trans (WTool.le_normalizer_of_le_isPGroup hΩ h16 hW hPW2 le_sup_right)
  exact ⟨o, ho, P, ⟨mem_RSet_of_isSylow2In hJΩ hPJ, hPN⟩, hPJ⟩

end Lift

end Perp22Wyl

end CFSG.CGT.PushingUpLit.SolKNA.R4
