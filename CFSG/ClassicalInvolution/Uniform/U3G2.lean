module

public import CFSG.ClassicalInvolution.Uniform.U3Witness

public section

namespace CFSG.ClassicalInvolution.Uniform

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77
open scoped MatrixGroups commutatorElement

section TwoMembers

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem false_of_pair_of_conjInvolutions (hΩ : HypOmegaModU (.sl2 p f) Ω) (hex : ExactMembers Ω)
    (hA : ∀ K ∈ Ω, AEmpty Ω K) {M : Type} [Group M] (ψ : M →* G) (hψ : Function.Injective ψ)
    (hinv : ∀ z z' : M, z * z = 1 → z' * z' = 1 → z ≠ 1 → z' ≠ 1 → ∃ h, h * z * h⁻¹ = z')
    {R S : Subgroup M} (hK : R.map ψ ∈ Ω) (hJ : S.map ψ ∈ Ω)
    (hnc : ¬ ∃ g : G, conjSub g (R.map ψ) = S.map ψ) : False := by
  obtain ⟨zK, hzK0⟩ := hΩ.classical _ hK
  obtain ⟨zJ, hzJ0⟩ := hΩ.classical _ hJ
  have hodd : Odd (Nat.card (GaloisField p f)) :=
    odd_natCard_galoisField_of_pos hzK0.admissible.2.1 hzK0.admissible.2.2
  set K := R.map ψ with hKdef
  set J := S.map ψ with hJdef
  have hzK := hzK0.isUniqueInvolution_sl2
  have hzJ := hzJ0.isUniqueInvolution_sl2
  obtain ⟨rR, hrR, hψrR⟩ := hzK.mem
  obtain ⟨rS, hrS, hψrS⟩ := hzJ.mem
  have hrR2 : rR * rR = 1 := hψ (by rw [map_mul, hψrR, map_one, hzK.sq])
  have hrS2 : rS * rS = 1 := hψ (by rw [map_mul, hψrS, map_one, hzJ.sq])
  have hrR1 : rR ≠ 1 := fun h => hzK.ne_one (by rw [← hψrR, h, map_one])
  have hrS1 : rS ≠ 1 := fun h => hzJ.ne_one (by rw [← hψrS, h, map_one])
  obtain ⟨g, hg⟩ := hinv rR rS hrR2 hrS2 hrR1 hrS1
  set K₀ := conjSub (ψ g) K with hK₀def
  have hK₀Ω : K₀ ∈ Ω := hΩ.conjInvariant _ K hK
  have hzK₀ : IsUniqueInvolution K₀ zJ := by
    have h1 := hzK.conj (ψ g)
    have e : ψ g * zK * (ψ g)⁻¹ = zJ := by
      rw [← hψrR, ← hψrS, ← hg]
      simp [map_mul, map_inv]
    rwa [e] at h1
  have hK₀J : K₀ ≠ J := fun h => hnc ⟨ψ g, h⟩
  obtain ⟨hv, hcommv⟩ := hΩ.omega4_commutes hex hK₀Ω hJ hK₀J
  have hdvd2 : 2 ∣ Nat.card ↥(K₀ ⊓ J) := by
    have hmem : zJ ∈ K₀ ⊓ J := ⟨hzK₀.mem, hzJ.mem⟩
    have := Subgroup.orderOf_dvd_natCard (K₀ ⊓ J) hmem
    rwa [hzJ0.orderOf_eq_two] at this
  have hcard0 : Nat.card ↥(K₀ ⊓ J) ≠ 0 := Nat.card_pos.ne'
  have hcomm : Commutes K₀ J := by
    apply hcommv
    have := one_le_padicValNat_of_dvd hcard0 hdvd2
    omega
  obtain ⟨eK⟩ := hzK0.nonempty_equiv_sl2_of_exact (hex K hK)
  obtain ⟨eJ⟩ := hzJ0.nonempty_equiv_sl2_of_exact (hex J hJ)
  obtain ⟨-, -, cK, -, -, -, -, hcKo, -⟩ := sl2_witness hodd eK
  obtain ⟨P, u, j, huP, hidx, hnoncen, hju, hjo, hb⟩ := sl2_witness hodd eJ
  have hsq_eq : ∀ {L : Subgroup G} {w y : G}, IsUniqueInvolution L w → y ∈ L → orderOf y = 4 →
      y ^ 2 = w := by
    intro L w y hw hy hoy
    have h4 : y ^ 2 * y ^ 2 = 1 := by
      rw [← pow_add]
      exact orderOf_dvd_iff_pow_eq_one.mp (by rw [hoy])
    rcases hw.unique (y ^ 2) (L.pow_mem hy 2) h4 with h | h
    · exfalso
      have := orderOf_dvd_of_pow_eq_one h
      rw [hoy] at this
      omega
    · exact h
  have hcK : (cK : G) ^ 2 = zK :=
    hsq_eq hzK cK.2 (by rw [Subgroup.orderOf_coe]; exact hcKo)
  have hj : (j : G) ^ 2 = zJ :=
    hsq_eq hzJ j.2 (by rw [Subgroup.orderOf_coe]; exact hjo)
  obtain ⟨c₀, hc₀R, hψc₀⟩ : (cK : G) ∈ K := cK.2
  obtain ⟨j₀, hj₀S, hψj₀⟩ : (j : G) ∈ J := j.2
  have hc₀sq : c₀ * c₀ = rR := hψ (by rw [map_mul, hψc₀, hψrR, ← sq, hcK])
  have hj₀sq : j₀ * j₀ = rS := hψ (by rw [map_mul, hψj₀, hψrS, ← sq, hj])
  set c₁ : M := g * c₀ * g⁻¹ with hc₁def
  have hc₁sq : c₁ * c₁ = rS := by
    rw [hc₁def, ← hg]
    calc g * c₀ * g⁻¹ * (g * c₀ * g⁻¹) = g * (c₀ * c₀) * g⁻¹ := by group
      _ = g * rR * g⁻¹ := by rw [hc₀sq]
  have hψc₁ : ψ c₁ = ψ g * (cK : G) * (ψ g)⁻¹ := by
    rw [hc₁def, map_mul, map_mul, map_inv, hψc₀]
  have hc₁K₀ : ψ c₁ ∈ K₀ := by
    rw [hψc₁]
    exact conj_mem_conjSub cK.2
  have hc₁S : c₁ * j₀ = j₀ * c₁ := hψ (by
    rw [map_mul ψ c₁ j₀, map_mul ψ j₀ c₁, hψj₀]
    exact hcomm _ hc₁K₀ _ j.2)
  set m₁ : M := j₀ * c₁ with hm₁def
  have hm₁sq : m₁ * m₁ = 1 := by
    calc j₀ * c₁ * (j₀ * c₁) = j₀ * (c₁ * j₀) * c₁ := by group
      _ = j₀ * (j₀ * c₁) * c₁ := by rw [hc₁S]
      _ = (j₀ * j₀) * (c₁ * c₁) := by group
      _ = 1 := by rw [hj₀sq, hc₁sq, hrS2]
  set z₁ : G := (j : G) * ψ c₁ with hz₁def
  have hψm₁ : ψ m₁ = z₁ := by rw [hm₁def, map_mul, hψj₀]
  have hjo' : orderOf (j : G) = 4 := by rw [Subgroup.orderOf_coe]; exact hjo
  have hz₁1 : z₁ ≠ 1 := by
    intro h
    have hjc : (j : G) = (ψ c₁)⁻¹ := eq_inv_of_mul_eq_one_left h
    have hmem : (j : G) ∈ K₀ ⊓ J := ⟨by rw [hjc]; exact K₀.inv_mem hc₁K₀, j.2⟩
    have h4 : 2 ^ 2 ∣ Nat.card ↥(K₀ ⊓ J) := by
      have := Subgroup.orderOf_dvd_natCard (K₀ ⊓ J) hmem
      rwa [hjo'] at this
    have := (padicValNat_dvd_iff_le hcard0).mp h4
    omega
  have hm₁1 : m₁ ≠ 1 := fun h => hz₁1 (by rw [← hψm₁, h, map_one])
  obtain ⟨h, hh⟩ := hinv rR m₁ hrR2 hm₁sq hrR1 hm₁1
  set K' := conjSub (ψ h) K with hK'def
  have hK'Ω : K' ∈ Ω := hΩ.conjInvariant _ K hK
  have hzK' : IsUniqueInvolution K' z₁ := by
    have h1 := hzK.conj (ψ h)
    have e : ψ h * zK * (ψ h)⁻¹ = z₁ := by
      rw [← hψrR, ← hψm₁, ← hh]
      simp [map_mul, map_inv]
    rwa [e] at h1
  have hnc' : ¬ ∃ g' : G, conjSub g' K' = J := by
    rintro ⟨g', hg'⟩
    exact hnc ⟨g' * ψ h, by rw [conjSub_mul]; exact hg'⟩
  have huz : (u : G) * z₁ = z₁ * (u : G) := by
    have hju' : (u : G) * (j : G) = (j : G) * (u : G) := by
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hju
      rw [← hk]
      exact congrArg Subtype.val ((Commute.refl u).zpow_right k).eq
    have huc : (u : G) * ψ c₁ = ψ c₁ * (u : G) := (hcomm _ hc₁K₀ u u.2).symm
    rw [hz₁def]
    calc (u : G) * ((j : G) * ψ c₁) = ((u : G) * (j : G)) * ψ c₁ := by group
      _ = ((j : G) * (u : G)) * ψ c₁ := by rw [hju']
      _ = (j : G) * ((u : G) * ψ c₁) := by group
      _ = (j : G) * (ψ c₁ * (u : G)) := by rw [huc]
      _ = ((j : G) * ψ c₁) * (u : G) := by group
  have hb' : ∀ P' : Sylow 2 ↥J, ∃ x ∈ (P' : Subgroup ↥J), (x : G) * z₁ ≠ z₁ * (x : G) := by
    intro P'
    obtain ⟨x, hxP', hx⟩ := hb P'
    refine ⟨x, hxP', fun hxz => hx ?_⟩
    have hxc : (x : G) * ψ c₁ = ψ c₁ * (x : G) := (hcomm _ hc₁K₀ x x.2).symm
    have h1 : (x : G) * (j : G) * ψ c₁ = (j : G) * (x : G) * ψ c₁ := by
      calc (x : G) * (j : G) * ψ c₁ = (x : G) * ((j : G) * ψ c₁) := by group
        _ = ((j : G) * ψ c₁) * (x : G) := hxz
        _ = (j : G) * (ψ c₁ * (x : G)) := by group
        _ = (j : G) * ((x : G) * ψ c₁) := by rw [hxc]
        _ = (j : G) * (x : G) * ψ c₁ := by group
    exact Subtype.ext (mul_right_cancel h1)
  exact not_aEmpty_of_centralizer_witnessU hΩ hex hK'Ω hJ hnc' hzK' P u huP hidx hnoncen huz hb'
    (hA K' hK'Ω)

end TwoMembers

end CFSG.ClassicalInvolution.Uniform
