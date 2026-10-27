module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3A6jA
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23FusN
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinMuPf2P23
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23ExU21
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23ExU30
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23FusLie
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23Pf14Narrow
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R56Zstar
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23RE78
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23WAe5
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23WEW
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23WOrd1
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23WOrd2
public import CFSG.ClassicalInvolution.Q3.TL4AE286Link

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.A6NoWt1

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Disconnected
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinEdge
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinVtx
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinFrameTgt
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Q3.Q3NL
open CFSG.ClassicalInvolution.Q3.Q3CH CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6S
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.A6jA
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf6
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinCentRes
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf12
open CFSG.ClassicalInvolution.Asc77.Thompson CFSG.ClassicalInvolution.Uniform
open CFSG.ClassicalInvolution.Q3.TC.Thin CFSG.ClassicalInvolution.Q3.AE

variable {n : ℕ}


local notation "Ω[" R "]" => CoreAssembly.conjClass (tightCore R)

section Datum

variable {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  {K K' K₃ : Subgroup Y} {u₁ u₂ u₃ : Y} {K₄ W : Subgroup Y}

theorem exists_cent_conj_twin (H : AE6Hyp n R S t K K' K₃ u₁ u₂ u₃ K₄ W) {J₁ : Subgroup Y}
    (hJ₁ : J₁ ∈ twinSet Ω[R] K) :
    ∃ g ∈ Subgroup.centralizer ({t} : Set Y), conjSub g J₁ = K₃ := by
  have hd := H.ex.1.datum
  have hK₃ : K₃ ∈ twinSet Ω[R] K := hd.hK₃
  obtain ⟨m₁, -, hm₁⟩ := A6jB.exists_M_conj_of_twin H hJ₁
  obtain ⟨m₂, -, hm₂⟩ := A6jB.exists_M_conj_of_twin H hK₃
  refine ⟨m₂ * m₁⁻¹, ?_, by rw [conjSub_mul, ← hm₁, conjSub_inv_conjSub, hm₂]⟩
  have h1 := A6jB.isUniqueInvolution_conjSub (isUniqueInvolution_of_mem_twinSet hd.hz hJ₁)
    (m₂ * m₁⁻¹)
  rw [conjSub_mul, ← hm₁, conjSub_inv_conjSub, hm₂] at h1
  have h2 : (m₂ * m₁⁻¹) * t * (m₂ * m₁⁻¹)⁻¹ = t :=
    h1.eq (isUniqueInvolution_of_mem_twinSet hd.hz hK₃)
  rw [Subgroup.mem_centralizer_singleton_iff]
  calc m₂ * m₁⁻¹ * t = (m₂ * m₁⁻¹) * t * (m₂ * m₁⁻¹)⁻¹ * (m₂ * m₁⁻¹) := by group
    _ = t * (m₂ * m₁⁻¹) := by rw [h2]

theorem cent_of_ae6 (H : AE6Hyp n R S t K K' K₃ u₁ u₂ u₃ K₄ W)
    {J₁ J₄ : Subgroup Y} (hJ₁ : J₁ ∈ twinSet Ω[R] K) (hJ₄ : J₄ ∈ twinSet Ω[R] K) (h14 : J₁ ≠ J₄)
    (h1K : J₁ ≠ K) (h1K' : J₁ ≠ K') (h4K : J₄ ≠ K) (h4K' : J₄ ≠ K') {x : Y}
    (hxodd : Odd (orderOf x)) (hxK : ∀ p ∈ K, x * p = p * x) (hxK' : ∀ p ∈ K', x * p = p * x)
    (hx₄ : ∀ p ∈ J₄, x * p = p * x) (hx₁ : ∀ q ∈ J₁, x * q * x⁻¹ ∈ J₁) :
    ∀ q ∈ J₁, x * q = q * x := by
  have hStd := H.ex.1
  have hd := hStd.datum
  have hC := CoreData.of_S hStd.perp.core
  have hΩ : HypOmegaGen Ω[R] := hC.hyp
  have h2g : ∀ J ∈ Ω[R], IsPGroup 2 ↥J := H.ex.2.2.2.1
  have h2 : ∀ M ∈ Ω[R], IsPGroup 2 (↥M ⧸ classicalInvolutionOddCore ↥M) :=
    TwinADescent3.isPGroup_two_quotient_conjClass
      (TwinEdge.isPGroup_two_quotient_of_le (tightCore_le R) hC.datum.twoGroup)
  have hKV : K ∈ twinSet Ω[R] K := mem_twinSet_self hd.mem hd.hz
  have hK'V : K' ∈ twinSet Ω[R] K := hd.hK'
  have hcent : ∀ J ∈ twinSet Ω[R] K, J ≠ K → J ≠ K' →
      J ≤ Subgroup.centralizer ({u₁ * u₂} : Set Y) := by
    intro J hJ hJK hJK' q hq
    rw [Subgroup.mem_centralizer_singleton_iff]
    have e1 := A6jA.twin_comm H hKV hJ (Ne.symm hJK) u₁ hd.hu₁.1 q hq
    have e2 := A6jA.twin_comm H hK'V hJ (Ne.symm hJK') u₂ hd.hu₂.1 q hq
    calc q * (u₁ * u₂) = (q * u₁) * u₂ := by group
      _ = u₁ * (q * u₂) := by rw [← e1]; group
      _ = u₁ * u₂ * q := by rw [← e2]; group
  have hsyl : ∀ J ∈ Ω[R], IsSylow2In J J := fun J hJ =>
    ⟨le_rfl, h2g J hJ, fun V' hV'K _ hKV' => le_antisymm hV'K hKV'⟩
  have htq : ∀ J ∈ twinSet Ω[R] K, J ≠ K → J ≠ K' →
      J ∈ tqMembers3 (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂) := fun J hJ hJK hJK' =>
    ⟨hJ.1, TwinADescent3.mem_tq_of_sylCent hΩ h2 hJ.1 ⟨J, hsyl J hJ.1, hcent J hJ hJK hJK'⟩⟩
  have hT : TwinPerp23.Fus.LayerTwins Y R (u₁ * u₂) J₁ J₄ J₁ J₄ t :=
    { hc2 := hd.sq_12
      hc1 := hd.mul_ne_one
      hJ := htq J₁ hJ₁ h1K h1K'
      hJ' := htq J₄ hJ₄ h4K h4K'
      hne := h14
      hw := isUniqueInvolution_of_mem_twinSet hd.hz hJ₁
      hw' := isUniqueInvolution_of_mem_twinSet hd.hz hJ₄
      hQ := hsyl J₁ hJ₁.1
      hQ' := hsyl J₄ hJ₄.1
      hQc := hcent J₁ hJ₁ h1K h1K'
      hQ'c := hcent J₄ hJ₄ h4K h4K'
      hcomm := A6jA.twin_comm H hJ₁ hJ₄ h14 }
  have hxc : x ∈ Subgroup.centralizer ({u₁ * u₂} : Set Y) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    have e1 := hxK u₁ hd.hu₁.1
    have e2 := hxK' u₂ hd.hu₂.1
    calc x * (u₁ * u₂) = (x * u₁) * u₂ := by group
      _ = u₁ * (x * u₂) := by rw [e1]; group
      _ = u₁ * u₂ * x := by rw [e2]; group
  obtain ⟨I⟩ := H.ae6
  exact TwinPerp23.Fus.nside_ae hStd.perp hT (Or.inr rfl) I hxc hxodd hx₁ hx₄

end Datum

theorem v3AE6NoWt1_proved : V3AE6NoWt1 n := by
  intro Y _ _ R S t K K' K₃ u₁ u₂ u₃ K₄ W a₁ a₂ a₃ a₄ y H fr c hcC hc3 hcN hcard
  classical
  have hStd := H.ex.1
  have hd := hStd.datum
  have hF := H.ex.2.1
  have hinv := conjInvariant_conjClass (tightCore R)
  have hKV : K ∈ twinSet Ω[R] K := mem_twinSet_self hd.mem hd.hz
  have hK₄V : K₄ ∈ twinSet Ω[R] K := hF.1
  obtain ⟨J₁, hJ₁eq⟩ := Set.ncard_eq_one.mp hcard
  have hJ₁mem : J₁ ∈ {J | J ∈ twinSet Ω[R] K ∧ ∃ p ∈ J, c * p * c⁻¹ ≠ p} := by
    rw [hJ₁eq]
    exact rfl
  obtain ⟨hJ₁V, p₁, hp₁, hp₁ne⟩ := hJ₁mem
  have htriv : ∀ J ∈ twinSet Ω[R] K, J ≠ J₁ → ∀ p ∈ J, c * p * c⁻¹ = p := by
    intro J hJ hJne p hp
    by_contra hne
    have hmem : J ∈ {J | J ∈ twinSet Ω[R] K ∧ ∃ p ∈ J, c * p * c⁻¹ ≠ p} := ⟨hJ, p, hp, hne⟩
    rw [hJ₁eq] at hmem
    exact hJne hmem
  obtain ⟨g, hgC, hgJ₁⟩ := exists_cent_conj_twin H hJ₁V
  have hgt : g * t * g⁻¹ = t := by
    rw [Subgroup.mem_centralizer_singleton_iff] at hgC
    rw [hgC, mul_inv_cancel_right]
  have hconjV : ∀ (h : Y), h * t * h⁻¹ = t → ∀ J ∈ twinSet Ω[R] K,
      conjSub h J ∈ twinSet Ω[R] K := by
    intro h hht J hJ
    refine ⟨hinv h J hJ.1, t, hd.hz, ?_⟩
    have h1 := A6jB.isUniqueInvolution_conjSub (isUniqueInvolution_of_mem_twinSet hd.hz hJ) h
    rwa [hht] at h1
  have hgit : g⁻¹ * t * g⁻¹⁻¹ = t := by
    have h1 : g⁻¹ * (g * t * g⁻¹) * g = t := by group
    rw [hgt] at h1
    rw [inv_inv]
    exact h1
  set x := g * c * g⁻¹ with hxdef
  have hxtriv : ∀ J ∈ twinSet Ω[R] K, J ≠ K₃ → ∀ p ∈ J, x * p = p * x := by
    intro J hJ hJne p hp
    have hJ' : conjSub g⁻¹ J ∈ twinSet Ω[R] K := hconjV g⁻¹ hgit J hJ
    have hJ'ne : conjSub g⁻¹ J ≠ J₁ := by
      intro h
      apply hJne
      rw [← hgJ₁, ← h, conjSub_conjSub_inv]
    have hp' : g⁻¹ * p * g⁻¹⁻¹ ∈ conjSub g⁻¹ J := conj_mem_conjSub hp
    have h1 := htriv _ hJ' hJ'ne _ hp'
    rw [inv_inv] at h1
    calc x * p = g * (c * (g⁻¹ * p * g) * c⁻¹) * g⁻¹ * x := by rw [hxdef]; group
      _ = g * (g⁻¹ * p * g) * g⁻¹ * x := by rw [h1]
      _ = p * x := by group
  have hxN : ∀ q ∈ K₃, x * q * x⁻¹ ∈ K₃ := by
    intro q hq
    have hJ₁N := hcN J₁ hJ₁V
    have hq' : g⁻¹ * q * g⁻¹⁻¹ ∈ J₁ := by
      have := conj_mem_conjSub (n := g⁻¹) hq
      rwa [← hgJ₁, conjSub_inv_conjSub] at this
    rw [inv_inv] at hq'
    have h1 : c * (g⁻¹ * q * g) * c⁻¹ ∈ J₁ :=
      (Subgroup.mem_normalizer_iff.mp hJ₁N _).mp hq'
    have h2 : g * (c * (g⁻¹ * q * g) * c⁻¹) * g⁻¹ ∈ K₃ := by
      rw [← hgJ₁]
      exact conj_mem_conjSub h1
    have e : x * q * x⁻¹ = g * (c * (g⁻¹ * q * g) * c⁻¹) * g⁻¹ := by rw [hxdef]; group
    rw [e]
    exact h2
  have hxodd : Odd (orderOf x) := by
    have hord : orderOf x = orderOf c := by
      rw [hxdef, ← MulAut.conj_apply]
      exact orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective c
    rw [hord]
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card).mp hc3
    rw [Nat.card_zpowers] at hk
    rw [hk]
    exact Odd.pow (by decide)
  have hK₃K : K₃ ≠ K := hd.hK₃K
  have hK₃K' : K₃ ≠ K' := hd.hK₃K'
  have hK₄K : K₄ ≠ K := hF.2.1
  have hK₄K' : K₄ ≠ K' := hF.2.2.1
  have hK₄K₃ : K₄ ≠ K₃ := hF.2.2.2.1
  have hcK₃ := cent_of_ae6 H hd.hK₃ hK₄V hK₄K₃.symm hK₃K hK₃K' hK₄K hK₄K' hxodd
    (hxtriv K hKV hK₃K.symm) (hxtriv K' hd.hK' hK₃K'.symm) (hxtriv K₄ hK₄V hK₄K₃) hxN
  apply hp₁ne
  have hq : g * p₁ * g⁻¹ ∈ K₃ := by
    rw [← hgJ₁]
    exact conj_mem_conjSub hp₁
  have h1 := hcK₃ _ hq
  rw [hxdef] at h1
  have h2 : g * (c * p₁) * g⁻¹ = g * (p₁ * c) * g⁻¹ := by
    calc g * (c * p₁) * g⁻¹ = g * c * g⁻¹ * (g * p₁ * g⁻¹) := by group
      _ = g * p₁ * g⁻¹ * (g * c * g⁻¹) := h1
      _ = g * (p₁ * c) * g⁻¹ := by group
  have h3 : c * p₁ = p₁ * c := mul_left_cancel (mul_right_cancel h2)
  rw [h3, mul_inv_cancel_right]

theorem v3AE6OmegaHA_of_models (hQ8 : AE6ModelQ8)
    (hSmall : AE6ModelSmall) (hFW : AE6ModelFW) (hF : AE6ModelF) (hC1 : AE6ModelC1')
    (hC2 : AE6ModelC2) (hC3 : AE6ModelC3) : V3AE6OmegaHA n :=
  v3AE6OmegaHA_of hQ8 hSmall hFW hF hC1 hC2 hC3 v3AE6NoWt1_proved

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.A6NoWt1
