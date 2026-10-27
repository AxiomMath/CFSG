module

public import CFSG.ClassicalInvolution.SmallCases.NDB5dWC1
import CFSG.ClassicalInvolution.Asc77.WP3SCUNGa
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
import CFSG.ClassicalInvolution.Asc77.WP3ChainVRank3
import CFSG.ClassicalInvolution.Asc77.WP3ChainVToral

public section

namespace CFSG.ClassicalInvolution.NDB.WC

open CFSG.Open CFSG.ComponentClassification CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Balance.Bootstrap CFSG.ClassicalInvolution.Asc77.ExactLayer

local notation "𝒞" => Generic.CoreAssembly.conjClass

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] [IsSimpleGroup G]

theorem weak_closure (hnab : ∃ x y : G, x * y ≠ y * x) (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f)
    (hBelow : CITBelowU p f (Nat.card G)) {K₀ : Subgroup G} {z₁ : G}
    (C₁ : Asc77.XCtx p f (𝒞 K₀) z₁)
    (hcard : C₁.D.card = 2) {i₀ i₁ : Fin C₁.D.card} (hi₀₁ : i₀ ≠ i₁)
    (hi₀ : C₁.D.tag i₀ = .PSL ∧ C₁.D.rank i₀ = 2)
    (hi₁ : ¬ (C₁.D.tag i₁ = .PSL ∧ C₁.D.rank i₁ = 2))
    (hK₀ : modOdd z₁ C₁.K = (C₁.psi i₀).range)
    {s t₁ v : G} (hs : s ∈ Subgroup.centralizer ({z₁} : Set G)) (ht₁ : t₁ ∈ C₁.K)
    (ht₁₁ : t₁ * t₁ = z₁) (hvC : v ∈ Subgroup.centralizer ({z₁} : Set G)) (hsv : s = v * t₁)
    (hv : oddQuotMk z₁ ⟨v, hvC⟩ ∈ (C₁.psi i₁).range)
    {L₁ : Subgroup G}
    (hL₁ : L₁ ≤ Subgroup.centralizer ({z₁} : Set G) ⊓ Subgroup.centralizer ({s} : Set G))
    (hL₁n : ∀ g ∈ Subgroup.centralizer ({z₁} : Set G) ⊓ Subgroup.centralizer ({s} : Set G),
      conjSub g L₁ = L₁)
    (hL₁p : ⁅L₁, L₁⁆ = L₁) (hz₁L : z₁ ∈ L₁)
    (hLO : L₁ ⊓ oddCoreIn (Subgroup.centralizer ({s} : Set G)) ≤
      oddCoreIn (Subgroup.centralizer ({z₁} : Set G)))
    (hSp : ∀ x ∈ (C₁.psi i₁).range, x * x = 1 →
      x * oddQuotMk z₁ ⟨v, hvC⟩ = oddQuotMk z₁ ⟨v, hvC⟩ * x →
        (∀ y ∈ modOdd z₁ L₁, x * y = y * x) →
          x = 1 ∨ x = oddQuotMk z₁ ⟨z₁, Asc77.XCtx.hzC z₁⟩)
    {h : G} (hh : h ∈ Subgroup.centralizer ({s} : Set G))
    (hR : ∀ x ∈ modOdd s (conjSub h L₁), ∀ y ∈ modOdd s L₁, x * y = y * x) :
    modOdd s (conjSub h L₁) = modOdd s L₁ := by
  have hK₁ := C₁.K_cl
  set K₁ := C₁.K with hK₁def
  set Cs := Subgroup.centralizer ({s} : Set G) with hCs
  set Cz := Subgroup.centralizer ({z₁} : Set G) with hCz
  set O := oddCoreIn Cs with hO
  have hOodd : Odd (Nat.card O) := odd_card_oddCoreIn Cs
  have hOs : O ≤ Cs := oddCoreIn_le Cs
  have hz₁s : z₁ ∈ Cs := (hL₁ hz₁L).2
  have hz₁2 : z₁ * z₁ = 1 := hK₁.isCentralInvolution.sq
  have hz₁i : z₁⁻¹ = z₁ := (eq_inv_of_mul_eq_one_left hz₁2).symm
  have hz₁O : ∀ o ∈ O, z₁ * o * z₁ ∈ O := fun o ho => by
    have := conj_mem_oddCoreIn hz₁s ho
    rwa [hz₁i] at this
  have hf : 0 < f := Nat.pos_of_ne_zero (by rintro rfl; simp at hq)
  by_contra hne
  set M := conjSub h L₁ with hM
  have hMs : M ≤ Cs := by
    rintro _ ⟨l, hl, rfl⟩
    exact Cs.mul_mem (Cs.mul_mem hh (hL₁ hl).2) (Cs.inv_mem hh)
  have hcomm : ∀ m ∈ M, m⁻¹ * z₁⁻¹ * m * z₁ ∈ O := fun m hm =>
    comm_mem_oddCoreIn (hMs hm) hz₁s
      (hR _ (oddQuotMk_mem_modOdd hm (hMs hm)) _ (oddQuotMk_mem_modOdd hz₁L hz₁s))
  set u := h * z₁ * h⁻¹ with hu
  have huM : u ∈ M := ⟨z₁, hz₁L, rfl⟩
  have hu2 : u * u = 1 := by
    calc u * u = h * (z₁ * z₁) * h⁻¹ := by rw [hu]; group
      _ = 1 := by rw [hz₁2]; group
  set c := u⁻¹ * z₁⁻¹ * u * z₁ with hc
  have hcO : c ∈ O := hcomm u huM
  have huc : u * c = z₁⁻¹ * u * z₁ := by rw [hc]; group
  have huc2 : u * c * (u * c) = 1 := by
    rw [huc]
    calc z₁⁻¹ * u * z₁ * (z₁⁻¹ * u * z₁) = z₁⁻¹ * (u * u) * z₁ := by group
      _ = 1 := by rw [hu2]; group
  obtain ⟨w₀, hw₀, hw₀u⟩ :=
    inv_conj_of_odd hu2 (Odd.of_dvd_nat hOodd (Subgroup.orderOf_dvd_natCard O hcO)) huc2
  have hw₀O : w₀ ∈ O := (Subgroup.zpowers_le.mpr hcO) hw₀
  have e₀ : z₁ * u * z₁ = w₀⁻¹ * u * w₀ := by
    have := huc.symm.trans hw₀u
    rwa [hz₁i] at this
  have hgu : w₀ * z₁ * u = u * (w₀ * z₁) := by
    calc w₀ * z₁ * u = w₀ * (z₁ * u * z₁) * z₁⁻¹ := by group
      _ = w₀ * (w₀⁻¹ * u * w₀) * z₁⁻¹ := by rw [e₀]
      _ = u * (w₀ * z₁⁻¹) := by group
      _ = u * (w₀ * z₁) := by rw [hz₁i]
  have ho₀O : z₁ * w₀ * z₁ ∈ O := hz₁O w₀ hw₀O
  have hg : z₁ * (z₁ * w₀ * z₁) = w₀ * z₁ := by
    calc z₁ * (z₁ * w₀ * z₁) = (z₁ * z₁) * w₀ * z₁ := by group
      _ = w₀ * z₁ := by rw [hz₁2, one_mul]
  obtain ⟨w, hwO, hwz⟩ := exists_conj_mem_zpowers hOodd hz₁2 hz₁O ho₀O
  rw [hg] at hwz
  have hwzu : w⁻¹ * z₁ * w * u = u * (w⁻¹ * z₁ * w) := by
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hwz
    rw [← hk]
    exact (Commute.zpow_left hgu k).eq
  set u' := w * u * w⁻¹ with hu'
  have hu'z : u' * z₁ = z₁ * u' := by
    calc u' * z₁ = w * (u * (w⁻¹ * z₁ * w)) * w⁻¹ := by rw [hu']; group
      _ = w * (w⁻¹ * z₁ * w * u) * w⁻¹ := by rw [hwzu]
      _ = z₁ * u' := by rw [hu']; group
  set h' := w * h with hh'
  have hh'C : h' ∈ Cs := Cs.mul_mem (hOs hwO) hh
  have hu'h : u' = h' * z₁ * h'⁻¹ := by rw [hu', hu, hh']; group
  have hu'2 : u' * u' = 1 := by
    calc u' * u' = w * (u * u) * w⁻¹ := by rw [hu']; group
      _ = 1 := by rw [hu2]; group
  have hM' : modOdd s (conjSub h' L₁) = modOdd s M := by
    rw [hh', conjSub_mul]
    exact Asc77.modOdd_conjSub_of_mem_oddCoreIn hwO M
  have hu'L : u' ∈ conjSub h' L₁ := by
    rw [hu'h]
    exact ⟨z₁, hz₁L, rfl⟩
  have hu'ne : u' ≠ z₁ := by
    intro heq
    apply hne
    have hh'z : h' ∈ Cz := by
      rw [hCz, Subgroup.mem_centralizer_singleton_iff]
      have e := hu'h.symm.trans heq
      calc h' * z₁ = (h' * z₁ * h'⁻¹) * h' := by group
        _ = z₁ * h' := by rw [e]
    rw [← hM', hL₁n h' ⟨hh'z, hh'C⟩]
  have hMp : ⁅M, M⁆ = M := by
    rw [hM, conjSub, ← Subgroup.map_commutator, hL₁p]
  have hu'C : u' ∈ Cs := by
    rw [hu'h]
    exact Cs.mul_mem (Cs.mul_mem hh'C hz₁s) (Cs.inv_mem hh'C)
  have hu'R : oddQuotMk s ⟨u', hu'C⟩ ∈ modOdd s M := hM' ▸ oddQuotMk_mem_modOdd hu'L hu'C
  have hu'MO : u' ∈ M ⊔ O := by
    rw [hu']
    exact (M ⊔ O).mul_mem ((M ⊔ O).mul_mem (Subgroup.mem_sup_right hwO)
      (Subgroup.mem_sup_left huM)) (Subgroup.mem_sup_right (O.inv_mem hwO))
  exact weak_closure_core hnab hp2 hq hBelow C₁ hcard hi₀₁ hi₀ hi₁ hK₀ hs ht₁ ht₁₁ hvC hsv
    hv hL₁ hL₁n hLO hSp hMs hMp hR hz₁L hu'ne hu'z hu'h hu'C hu'R hu'MO

end CFSG.ClassicalInvolution.NDB.WC
