module

public import CFSG.ClassicalInvolution.SmallCases.NDB5dWC0
import CFSG.ClassicalInvolution.Asc77.WP3SCUNGa
import CFSG.ClassicalInvolution.Asc77.WP3SCSModel
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
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Generic.CoreAssembly
  CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.ClassicalInvolution.Asc77.ExactLayer

local notation "𝒞" => Generic.CoreAssembly.conjClass

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] [IsSimpleGroup G]

theorem weak_closure_core (hnab : ∃ x y : G, x * y ≠ y * x) (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f)
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
    (hLO : L₁ ⊓ oddCoreIn (Subgroup.centralizer ({s} : Set G)) ≤
      oddCoreIn (Subgroup.centralizer ({z₁} : Set G)))
    (hSp : ∀ x ∈ (C₁.psi i₁).range, x * x = 1 →
      x * oddQuotMk z₁ ⟨v, hvC⟩ = oddQuotMk z₁ ⟨v, hvC⟩ * x →
        (∀ y ∈ modOdd z₁ L₁, x * y = y * x) →
          x = 1 ∨ x = oddQuotMk z₁ ⟨z₁, Asc77.XCtx.hzC z₁⟩)
    {M : Subgroup G} (hMs : M ≤ Subgroup.centralizer ({s} : Set G)) (hMp : ⁅M, M⁆ = M)
    (hR : ∀ x ∈ modOdd s M, ∀ y ∈ modOdd s L₁, x * y = y * x) (hz₁L : z₁ ∈ L₁)
    {u h' : G} (hune : u ≠ z₁) (huz : u * z₁ = z₁ * u) (huh : u = h' * z₁ * h'⁻¹)
    (huC : u ∈ Subgroup.centralizer ({s} : Set G)) (huR : oddQuotMk s ⟨u, huC⟩ ∈ modOdd s M)
    (huMO : u ∈ M ⊔ oddCoreIn (Subgroup.centralizer ({s} : Set G))) : False := by
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
  have hu2 : u * u = 1 := by
    rw [huh]
    calc h' * z₁ * h'⁻¹ * (h' * z₁ * h'⁻¹) = h' * (z₁ * z₁) * h'⁻¹ := by group
      _ = 1 := by rw [hz₁2]; group
  have hnorm : ∀ g ∈ Cz, g ∈ Subgroup.normalizer (K₁ : Set G) := fun g hg =>
    mem_normalizer_of_conjSub_eq (conjSub_eq_of_psp C₁ hcard hi₀₁ hK₀ hi₁ hg)
  set X := (M ⊔ O) ⊓ Cz with hX
  have hXs : X ≤ Cs := fun x hx => (sup_le hMs hOs) (Subgroup.mem_inf.mp hx).1
  have huX : u ∈ X := ⟨huMO, Subgroup.mem_centralizer_singleton_iff.mpr huz⟩
  set ψX : X →* OddQuot s := (oddQuotMk s).comp (Subgroup.inclusion hXs) with hψX
  have hRle : modOdd s M ≤ ψX.range := by
    rintro _ ⟨⟨m, hmC⟩, hm, rfl⟩
    have h1 : m⁻¹ * z₁ * m * z₁ ∈ O := by
      have := comm_mem_oddCoreIn hmC hz₁s
        (hR _ ⟨⟨m, hmC⟩, hm, rfl⟩ _ (oddQuotMk_mem_modOdd hz₁L hz₁s))
      rwa [hz₁i] at this
    obtain ⟨w', hw'O, hw'⟩ := exists_mul_mem_centralizer hOodd hz₁2 hz₁O h1
    have hmX : m * w'⁻¹ ∈ X := ⟨(M ⊔ O).mul_mem (Subgroup.mem_sup_left hm)
      (Subgroup.mem_sup_right (O.inv_mem hw'O)), hw'⟩
    refine ⟨⟨m * w'⁻¹, hmX⟩, ?_⟩
    have e : Subgroup.inclusion hXs ⟨m * w'⁻¹, hmX⟩ =
        (⟨m, hmC⟩ : Cs) * ⟨w'⁻¹, hOs (O.inv_mem hw'O)⟩ := rfl
    rw [hψX, MonoidHom.comp_apply, e, map_mul,
      oddQuotMk_eq_one_of_mem_oddCoreIn (O.inv_mem hw'O), mul_one]
  obtain ⟨a', ha'3, ha'⟩ := le_map_derivedSeries ψX hRle (commutator_modOdd hMs hMp) 3 huR
  have hamem : (a' : G)⁻¹ * u ∈ O := by
    have h1 : oddQuotMk s ((Subgroup.inclusion hXs a')⁻¹ * ⟨u, huC⟩) = 1 := by
      have e : oddQuotMk s (Subgroup.inclusion hXs a') = oddQuotMk s ⟨u, huC⟩ := ha'
      rw [map_mul, map_inv, e, inv_mul_cancel]
    exact ⟨_, oddQuotMk_eq_one_iff.mp h1, rfl⟩
  have hct : s * t₁⁻¹ ∈ trivialOnQuot K₁ := by
    have e : s * t₁⁻¹ = v := by rw [hsv]; group
    rw [e]
    refine mem_trivialOnQuot_of_centralizes_modOdd hK₁ (isCanonical_of_isClassicalMember hK₁)
      hvC ?_
    intro y hy
    rw [hK₀] at hy
    obtain ⟨b, rfl⟩ := hy
    obtain ⟨a, ha⟩ := hv
    rw [← ha]
    exact C₁.psi_commute hi₀₁.symm a b
  have hutq : u ∈ trivialOnQuot K₁ :=
    mem_trivialOnQuot_of_derived hp2 hq hK₁ (fun x hx => hnorm x (Subgroup.mem_inf.mp hx).2)
      (hnorm s hs) ht₁ ht₁₁
      hct (fun x hx => (Subgroup.mem_centralizer_singleton_iff.mp (hXs hx)).symm) huX hu2 a'.2
      ha'3 (Odd.of_dvd_nat hOodd (Subgroup.orderOf_dvd_natCard O hamem))
  have hK₁'cl : IsClassicalMember p f (conjSub h' K₁) u := by
    rw [huh]
    exact hK₁.conj h'
  have hmemK : conjSub h' K₁ ∈ 𝒞 K₀ := C₁.hΩ.conjInvariant h' K₁ C₁.hK
  have hcl : 𝒞 (conjSub h' K₁) = 𝒞 K₀ := Cover.conjClass_eq_of_mem hmemK
  obtain ⟨Du⟩ := Cover.nonempty_lieSystem hnab hp2 hq hK₁'cl hBelow
  have hne' : K₁ ≠ conjSub h' K₁ := by
    intro he
    have h1 : IsClassicalMember p f K₁ u := he ▸ hK₁'cl
    exact hune (h1.eq_of_isCentralInvolution hp2 hf hK₁.isCentralInvolution).symm
  have hKtq : K₁ ∈ tqMembers (𝒞 (conjSub h' K₁)) u := ⟨hcl ▸ C₁.hK, hutq⟩
  have hz₁tq : z₁ ∈ trivialOnQuot (conjSub h' K₁) :=
    Cover.mem_trivialOnQuot_K (Cover.toXCtx hnab hp2 hq hK₁'cl hBelow Du) hKtq hK₁ hne'
  have hub := mem_range_of_tq C₁ hcard hi₀₁ hi₀ hK₀ ⟨hmemK, hz₁tq⟩ hK₁'cl hune
  have huCz : u ∈ Cz := Subgroup.mem_centralizer_singleton_iff.mpr huz
  set ub := oddQuotMk z₁ ⟨u, huCz⟩ with hub_def
  have hub' : ub ∈ (C₁.psi i₁).range := hub
  have hub2 : ub * ub = 1 := by
    rw [hub_def, ← map_mul]
    have e : (⟨u, huCz⟩ : Cz) * ⟨u, huCz⟩ = 1 := Subtype.ext hu2
    rw [e, map_one]
  have ht₁C : t₁ ∈ Cz := RouteD.le_centralizer_of_isClassicalMember hK₁ ht₁
  have hubs : ub * oddQuotMk z₁ ⟨s, hs⟩ = oddQuotMk z₁ ⟨s, hs⟩ * ub := by
    rw [hub_def, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp huC)
  have hubt : ub * oddQuotMk z₁ ⟨t₁, ht₁C⟩ = oddQuotMk z₁ ⟨t₁, ht₁C⟩ * ub := by
    have ht : oddQuotMk z₁ ⟨t₁, ht₁C⟩ ∈ (C₁.psi i₀).range := by
      rw [← hK₀]
      exact oddQuotMk_mem_modOdd ht₁ ht₁C
    obtain ⟨a, ha⟩ := hub'
    obtain ⟨b, hb⟩ := ht
    rw [← ha, ← hb]
    exact C₁.psi_commute hi₀₁.symm a b
  have hubv : ub * oddQuotMk z₁ ⟨v, hvC⟩ = oddQuotMk z₁ ⟨v, hvC⟩ * ub := by
    have e : (⟨v, hvC⟩ : Cz) = ⟨s, hs⟩ * (⟨t₁, ht₁C⟩ : Cz)⁻¹ :=
      Subtype.ext (by
        show v = s * t₁⁻¹
        rw [hsv]
        group)
    rw [e, map_mul, map_inv]
    exact (Commute.mul_right hubs (Commute.inv_right hubt)).eq
  have hubL : ∀ y ∈ modOdd z₁ L₁, ub * y = y * ub := by
    rintro _ ⟨⟨l, hlC⟩, hl, rfl⟩
    have hl' : l ∈ L₁ := hl
    have hls : l ∈ Cs := (hL₁ hl').2
    have h1 : u⁻¹ * l⁻¹ * u * l ∈ O :=
      comm_mem_oddCoreIn huC hls (hR _ huR _ (oddQuotMk_mem_modOdd hl' hls))
    have h2 : u⁻¹ * l⁻¹ * u * l ∈ L₁ := by
      have hn := hL₁n u⁻¹ ⟨Cz.inv_mem huCz, Cs.inv_mem huC⟩
      have h3 : u⁻¹ * l⁻¹ * u ∈ L₁ := by
        rw [← hn]
        refine ⟨l⁻¹, L₁.inv_mem hl', ?_⟩
        show u⁻¹ * l⁻¹ * u⁻¹⁻¹ = u⁻¹ * l⁻¹ * u
        rw [inv_inv]
      exact L₁.mul_mem h3 hl'
    exact commute_of_comm_mem_oddCoreIn huCz hlC (hLO ⟨h2, h1⟩)
  rcases hSp ub hub' hub2 hubv hubL with h1 | h1
  · have e := eq_one_of_oddQuotMk_eq_one
      (show (⟨u, huCz⟩ : Cz) * ⟨u, huCz⟩ = 1 from Subtype.ext hu2) h1
    have hu1 : u = 1 := congrArg Subtype.val e
    have hz1 : z₁ = 1 := by
      calc z₁ = h'⁻¹ * (h' * z₁ * h'⁻¹) * h' := by group
        _ = 1 := by rw [← huh, hu1]; group
    have h2 := hK₁.orderOf_eq_two
    rw [hz1, orderOf_one] at h2
    exact absurd h2 (by decide)
  · exact hune (Asc77.eq_of_oddQuotMk_eq' huCz (Asc77.XCtx.hzC z₁) hu2 hz₁2 huz h1)

end CFSG.ClassicalInvolution.NDB.WC
