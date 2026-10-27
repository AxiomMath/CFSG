module

public import CFSG.ClassicalInvolution.Asc77.AscE187B2f
public import CFSG.ClassicalInvolution.Asc77.WP1Logic
public import CFSG.ClassicalInvolution.Asc77.AscE187EndC
public import CFSG.ClassicalInvolution.Asc77.AscE187P1d

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution.Generic

section Main

variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}
  {K : Subgroup G} {S : Sylow 2 G} {R W H : Subgroup G}

theorem E187C.part2_of {S' : Sylow 2 G} {z : G} (hcI : ConjInvariant Ω) (hK : K ∈ Ω)
    (hz : IsUniqueInvolution K z) (hSH : (S' : Subgroup G) ≤ H)
    (hgood : ∀ {g₁ t : G}, g₁ ∉ H → t = g₁ * z * g₁⁻¹ → t ∈ (S' : Subgroup G) → GoodFour H t)
    (hbad : ∀ {g₁ : G}, g₁ ∉ H → ∀ M ∈ Ω, IsUniqueInvolution M (g₁ * z * g₁⁻¹) →
      ∀ u ∈ M, orderOf u = 4 → u ∉ H)
    (hend : ∀ {t : G} {K₁ : Subgroup G} {d₁ d₂ : G},
      (∀ M ∈ Ω, IsUniqueInvolution M t → ∀ u ∈ M, orderOf u = 4 → u ∉ H) → K₁ ∈ Ω →
      IsUniqueInvolution K₁ t → GoodInv H t d₁ → GoodInv H t d₂ → GoodInv H t (d₁ * d₂) →
      d₁ * d₂ = d₂ * d₁ → False) :
    ∀ x : G, x * z * x⁻¹ ∈ H → x ∈ H := by
  intro g hgt
  by_contra hg
  have hz2' : orderOf (g * z * g⁻¹) = 2 := by
    rw [orderOf_conj_mul_inv_eq]
    exact orderOf_eq_two_of_sq hz.ne_one hz.sq
  have hv : IsPGroup 2 (Subgroup.zpowers (g * z * g⁻¹)) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hz2']; norm_num)
  obtain ⟨h₁, hh₁H, hh₁⟩ := exists_conj_mem_of_sylow_le hSH hgt hv
  obtain ⟨g₁, hg₁⟩ : ∃ g₁, g₁ = h₁⁻¹ * g := ⟨_, rfl⟩
  obtain ⟨t, ht⟩ : ∃ t, t = g₁ * z * g₁⁻¹ := ⟨_, rfl⟩
  have htS : t ∈ (S' : Subgroup G) := by
    have : t = h₁⁻¹ * (g * z * g⁻¹) * h₁ := by rw [ht, hg₁]; group
    rw [this]
    exact hh₁
  have hg₁H : g₁ ∉ H := by
    intro hh
    apply hg
    have : g = h₁ * g₁ := by rw [hg₁]; group
    rw [this]
    exact H.mul_mem hh₁H hh
  have hgood' : GoodFour H t := hgood hg₁H ht htS
  obtain ⟨d₁, d₂, g₁', g₂', g₃', hcd⟩ := hgood'
  have hK₁ : conjSub g₁ K ∈ Ω := hcI g₁ K hK
  have hK₁t : IsUniqueInvolution (conjSub g₁ K) t := by rw [ht]; exact hz.conj g₁
  have hbad' := hbad hg₁H
  rw [← ht] at hbad'
  exact hend hbad' hK₁ hK₁t g₁' g₂' g₃' hcd


theorem MinCex.part2 (h : E187Hyps p f) (h4 : E187E4C p f)
    (c : MinCex p f Ω K S R W H) {z : G} (hz : IsUniqueInvolution K z)
    (hzH : Subgroup.centralizer ({z} : Set G) ≤ H) :
    ∀ x : G, x * z * x⁻¹ ∈ H → x ∈ H := by
  have hp : p ≠ 2 := c.stand.odd
  have hq : 5 ≤ p ^ f := c.stand.five
  have hΩ : HypOmegaMod p f Ω := c.stand.hyp
  have hA : EtaAbelian Ω := h.etaAbelian hp hq hΩ
  have hM : EtaMeet Ω := h.etaMeet hp hq hΩ
  obtain ⟨S', W', c', hSylz⟩ := c.exists_config_sylow_centralizer hz
  have hzW' : z ∈ W' := by
    obtain ⟨z', hz'K, hz'W, -⟩ := c'.exists_z
    rwa [hz'K.eq hz] at hz'W
  exact E187C.part2_of hΩ.conjInvariant c.stand.mem hz (c'.sylow_le hA)
    (fun {g₁ t} hg₁H ht htS => by
      by_cases hcomm : t * z = z * t
      · exact c'.goodFour_of_commute h hz hzH hg₁H ht htS hcomm
      · exact c'.goodFour_of_noncommute h h4 hz hzW' hzH hSylz hg₁H ht htS hcomm)
    (fun hg' => c'.hbad_of_conj hA hM hz hg')
    (fun hbad hK₁ ht g₁ g₂ g₃ hcm => endgame_four hp hq hΩ hbad hK₁ ht g₁ g₂ g₃ hcm)

variable (p f) in
theorem e18_7 (h : E187Hyps p f) (h4 : E187E4C p f) : E18_7 p f := by
  intro G _ _ Ω K S R W H c a ha1 ha2 haH g hgt
  obtain ⟨z, hz, hzW, hzH⟩ := c.exists_z
  exact c.part1 h h4 hz hzW (c.part2 h h4 hz hzH) ha2 ha1 haH hgt

variable (p f) in
theorem e18_8z (h : E187Hyps p f) (h4 : E187E4C p f) : E18_8z p f :=
  e18_8z_of_e18_7 p f (e18_7 p f h h4)

end Main

end CFSG.ClassicalInvolution.Asc77
