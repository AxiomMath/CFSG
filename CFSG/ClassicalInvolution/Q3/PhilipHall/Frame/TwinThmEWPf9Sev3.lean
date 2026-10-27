module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmEWPf23Orb4Data
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmEPf9Sev3

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight CFSG.ClassicalInvolution.Q3
open scoped commutatorElement

namespace TwinThmEW
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmE

section Part2
variable [PrintedQuotOdd] [PrintedQuotCent] [PrintedHull]

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {K : Subgroup G} {S : Sylow 2 G}
  {R W H : Subgroup G}

theorem exists_g_hCS {z g t : G} (hSylz : IsSylow2In ((S : Subgroup G) ⊓ Subgroup.centralizer ({z} : Set G))
      (Subgroup.centralizer ({z} : Set G)))
    (ht : t = g * z * g⁻¹) (hzH : Subgroup.centralizer ({z} : Set G) ≤ H) (hg : g ∉ H) :
    ∃ g' : G, g' ∉ H ∧ t = g' * z * g'⁻¹ ∧
      ∀ x ∈ (S : Subgroup G), t * x = x * t → x ∈ conjSub g' (S : Subgroup G) :=
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmE.exists_g_hCS hSylz ht hzH hg

theorem endgame_cases_Q8 (hΩ : HypOmegaGen Ω)
    (hq8 : ∀ M ∈ Ω, ∀ P : Subgroup G, IsSylow2In P M → Nonempty (↥P ≃* QuaternionGroup 2))
    {H : Subgroup G} {t : G}
    (hbad : ∀ M ∈ Ω, IsUniqueInvolution M t → ∀ u ∈ M, orderOf u = 4 → u ∉ H)
    {K₁ : Subgroup G} (hK₁ : K₁ ∈ Ω) (ht : IsUniqueInvolution K₁ t) {S₁ R₁ : Subgroup G}
    (hS₁ : IsPGroup 2 S₁) (hR₁ : IsSylow2In R₁ K₁) (hR₁S : R₁ ≤ S₁) {d₁ d₂ : G}
    (hd₁S : d₁ ∈ S₁) (hd₂S : d₂ ∈ S₁)
    (g₁ : GoodInv H t d₁) (g₂ : GoodInv H t d₂) (g₃ : GoodInv H t (d₁ * d₂))
    (hc : d₁ * d₂ = d₂ * d₁) :
    conjSub d₁ K₁ ≠ K₁ ∧ conjSub d₂ K₁ ≠ K₁ ∧ conjSub (d₁ * d₂) K₁ ≠ K₁ :=
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmE.endgame_cases_Q8 hΩ hq8 hbad hK₁ ht hS₁ hR₁
    hR₁S hd₁S hd₂S g₁ g₂ g₃ hc

@[expose] def E187Orbit4Q8 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (Ω : Set (Subgroup G)) (K : Subgroup G) (S : Sylow 2 G)
    (R W H : Subgroup G), MinCexQ8 Ω K S R W H →
    ∀ z g t d₁ d₂ : G, IsUniqueInvolution K z → z ∈ W → Subgroup.centralizer ({z} : Set G) ≤ H →
      IsSylow2In ((S : Subgroup G) ⊓ Subgroup.centralizer ({z} : Set G))
        (Subgroup.centralizer ({z} : Set G)) → g ∉ H → t = g * z * g⁻¹ → t ∈ (S : Subgroup G) →
      (∀ x ∈ (S : Subgroup G), t * x = x * t → x ∈ conjSub g (S : Subgroup G)) →
      IsSylow2In ((S : Subgroup G) ⊓ Subgroup.centralizer ({t} : Set G))
        (Subgroup.centralizer ({t} : Set G) ⊓ H) →
      GoodInv H t d₁ → GoodInv H t d₂ → GoodInv H t (d₁ * d₂) → d₁ * d₂ = d₂ * d₁ → d₁ ∈ W →
      d₂ ∈ W → D4Shape (S : Subgroup G) t d₁ d₂ →
      conjSub d₁ (conjSub g K) ≠ conjSub g K → conjSub d₂ (conjSub g K) ≠ conjSub g K →
      conjSub (d₁ * d₂) (conjSub g K) ≠ conjSub g K → False

theorem MinCexQ8.part2 (h : E18_6Q8) (h4 : E18_4CQ8) (hO4 : E187Orbit4Q8)
    (c : MinCexQ8 Ω K S R W H) {z : G} (hz : IsUniqueInvolution K z)
    (hzH : Subgroup.centralizer ({z} : Set G) ≤ H) :
    ∀ x : G, x * z * x⁻¹ ∈ H → x ∈ H := by
  have hΩ : HypOmegaGen Ω := c.stand.hyp
  have hA : EtaAbelian Ω := etaAbelian_of_gen hΩ
  have hM : EtaMeet Ω := etaMeet_of_gen hΩ
  have hq8 : ∀ M ∈ Ω, ∀ P : Subgroup G, IsSylow2In P M → Nonempty (↥P ≃* QuaternionGroup 2) :=
    fun M hM => TwinDisc.forall_sylow_iso_of_exists (c.stand.q8 M hM)
  obtain ⟨S', W', c', hSylz⟩ := c.exists_config_sylow_centralizer hz
  have hSH : (S' : Subgroup G) ≤ H := c'.sylow_le hA
  have hzW' : z ∈ W' := by
    obtain ⟨z', hz'K, hz'W, -⟩ := c'.exists_z
    rwa [hz'K.eq hz] at hz'W
  intro g hgt
  by_contra hg
  have hz2' : orderOf (g * z * g⁻¹) = 2 := by
    rw [orderOf_conj_mul_inv_eq]
    exact orderOf_eq_two_of_sq hz.ne_one hz.sq
  have hv : IsPGroup 2 (Subgroup.zpowers (g * z * g⁻¹)) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hz2']; norm_num)
  obtain ⟨h₁, hh₁H, hh₁⟩ := exists_conj_mem_of_sylow_le hSH hgt hv
  obtain ⟨g₁, hg₁⟩ : ∃ g₁, g₁ = h₁⁻¹ * g := ⟨_, rfl⟩
  obtain ⟨t₀, ht₀⟩ : ∃ t, t = g₁ * z * g₁⁻¹ := ⟨_, rfl⟩
  have ht₀S : t₀ ∈ (S' : Subgroup G) := by
    have : t₀ = h₁⁻¹ * (g * z * g⁻¹) * h₁ := by rw [ht₀, hg₁]; group
    rw [this]
    exact hh₁
  have hg₁H : g₁ ∉ H := by
    intro hh
    apply hg
    have : g = h₁ * g₁ := by rw [hg₁]; group
    rw [this]
    exact H.mul_mem hh₁H hh
  obtain ⟨g₃, hg₃H, ht₃S, hCSyl⟩ := exists_good_t hSH hg₁H (ht₀ ▸ ht₀S)
  obtain ⟨t, ht₃⟩ : ∃ t, t = g₃ * z * g₃⁻¹ := ⟨_, rfl⟩
  rw [← ht₃] at ht₃S hCSyl
  obtain ⟨g₂, hg₂H, ht, hCS⟩ := exists_g_hCS hSylz ht₃ hzH hg₃H
  have hgood : GoodFourWD (S' : Subgroup G) H W' t := by
    by_cases hcomm : t * z = z * t
    · exact c'.goodFourD_of_commute hz hzH hg₂H ht ht₃S hcomm
    · exact c'.goodFourD_of_noncommute h h4 hz hzW' hzH hSylz hg₂H ht ht₃S hcomm
  obtain ⟨d₁, d₂, g₁', g₂', g₃', hc, hW₁, hW₂, hshape⟩ := hgood
  have hK₁ : conjSub g₂ K ∈ Ω := hΩ.conjInvariant g₂ K c.stand.mem
  have hK₁t : IsUniqueInvolution (conjSub g₂ K) t := by rw [ht]; exact hz.conj g₂
  have hbad := c'.hbad_of_conj hA hM hz hg₂H
  rw [← ht] at hbad
  obtain ⟨hRR, hRK, hRS⟩ := c'.stand.hR
  have hRsyl : IsSylow2In R K := Sec6Gen.isSylow2In_of_mem_RSet_of_le hΩ c.stand.mem hRR hRK
  have hWS : W' ≤ (S' : Subgroup G) := c'.stand.hW.2.1
  have hdS : ∀ d : G, d ∈ W' → GoodInv H t d → d ∈ conjSub g₂ (S' : Subgroup G) :=
    fun d hd gd => hCS d (hWS hd) gd.comm_t.symm
  obtain ⟨m₁, m₂, m₃⟩ := endgame_cases_Q8 hΩ hq8 hbad hK₁ hK₁t
    (isPGroup_conjSub g₂ S'.isPGroup') (hRsyl.conj g₂) (conjSub_mono hRS) (hdS d₁ hW₁ g₁')
    (hdS d₂ hW₂ g₂') g₁' g₂' g₃' hc
  exact hO4 G Ω K S' R W' H c' z g₂ t d₁ d₂ hz hzW' hzH hSylz hg₂H ht ht₃S hCS hCSyl g₁' g₂' g₃' hc
    hW₁ hW₂ hshape m₁ m₂ m₃

theorem e18_7Q8_of (h : E18_6Q8) (h4 : E18_4CQ8) (hO4 : E187Orbit4Q8) : E18_7Q8 := by
  intro G _ _ Ω K S R W H c a ha1 ha2 haH g hgt
  obtain ⟨z, hz, hzW, hzH⟩ := c.exists_z
  exact c.part1 h h4 hz hzW (c.part2 h h4 hO4 hz hzH) ha2 ha1 haH hgt
end Part2

end TwinThmEW

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
