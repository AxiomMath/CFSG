module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KDRank3SmallAbs

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KDRank3SmallF12Red

open CFSG.Open CFSG.LocalAnalysis.GLTheoremA KDRank3SmallAbs KDRank3SmallMod

@[expose] def KleinFour3 {G : Type} [Group G] (I : Subgroup G) : Prop :=
  ∀ g₁ g₂ k : G, g₁ ∈ I → g₂ ∈ I → g₁ ^ 2 = 1 → g₂ ^ 2 = 1 → g₁ ≠ 1 → g₂ ≠ 1 → g₁ ≠ g₂ →
    g₁ * g₂ = g₂ * g₁ → k ∈ I → k ^ 3 = 1 → k * g₁ = g₁ * k → k * g₂ = g₂ * k → k = 1

theorem f1_of_f2_klein {G : Type} [Group G] [Finite G] {I E : Subgroup G} {b : G}
    (hE : IsElemAbelian 3 E) (hEcard : Nat.card E = 3 ^ 3)
    (hE0 : Nat.card ↥(E ⊓ I) = 3 ^ 2) (hbE : b ∈ E) (hbI : b ∉ I)
    (hF2 : ∀ W : Subgroup G, IsPGroup 2 W → W ≤ I → E ⊓ I ≤ Subgroup.centralizer (W : Set G) →
      W = ⊥)
    (hK : KleinFour3 I) (W : Subgroup G) (hW : IsPGroup 2 W) (hW0 : W ≠ ⊥) (hWI : W ≤ I)
    (hWb : W ≤ Subgroup.centralizer ({b} : Set G))
    (hN : E ⊓ I ≤ Subgroup.normalizer (W : Set G)) : False := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hc : ∀ w ∈ W, b * w * b⁻¹ = w := fun w hw => by
    have h : b * w = w * b := Subgroup.mem_centralizer_iff.1 (hWb hw) b rfl
    rw [h]
    group
  have hc' : ∀ w ∈ W, b⁻¹ * w * b = w := fun w hw => by
    calc b⁻¹ * w * b = b⁻¹ * (b * w * b⁻¹) * b := by rw [hc w hw]
      _ = w := by group
  have hbN : b ∈ Subgroup.normalizer (W : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      rw [hc h hh]
      exact hh
    · intro hh
      have e1 : h = b * h * b⁻¹ := by
        calc h = b⁻¹ * (b * h * b⁻¹) * b := by group
          _ = b * h * b⁻¹ := hc' _ hh
      rw [e1]
      exact hh
  have hEI : IsElemAbelian 3 (E ⊓ I) := isElemAbelian_mono hE inf_le_left
  have hbZ : Subgroup.zpowers b ≤ E := Subgroup.zpowers_le.2 hbE
  have hb1 : b ≠ 1 := fun h => hbI (h ▸ I.one_mem)
  have hb3 : b ^ 3 = 1 := hE.2 b hbE
  have hbord : orderOf b = 3 := orderOf_eq_prime hb3 hb1
  have hZcard : Nat.card (Subgroup.zpowers b) = 3 := by rw [Nat.card_zpowers, hbord]
  have hZN : Subgroup.zpowers b ≤ Subgroup.normalizer ((E ⊓ I : Subgroup G) : Set G) :=
    le_normalizer_of_comm hE inf_le_left hbZ
  have hprod := card_sup_mul_card_inf_of_le_normalizer (A := E ⊓ I) (B := Subgroup.zpowers b) hZN
  have hinter : Nat.card ↥((E ⊓ I) ⊓ Subgroup.zpowers b) = 1 := by
    have hdvd : Nat.card ↥((E ⊓ I) ⊓ Subgroup.zpowers b) ∣ 3 := by
      rw [← hZcard]
      exact Subgroup.card_dvd_of_le inf_le_right
    rcases (Nat.dvd_prime Nat.prime_three).1 hdvd with h | h
    · exact h
    · exfalso
      have heq : (E ⊓ I) ⊓ Subgroup.zpowers b = Subgroup.zpowers b :=
        Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [hZcard, h])
      have hbmem : b ∈ (E ⊓ I) ⊓ Subgroup.zpowers b := by
        rw [heq]
        exact Subgroup.mem_zpowers b
      exact hbI hbmem.1.2
  have hsup : Nat.card ↥((E ⊓ I) ⊔ Subgroup.zpowers b) = 27 := by
    rw [hinter, hE0, hZcard] at hprod
    norm_num at hprod
    exact hprod
  have hEeq : (E ⊓ I) ⊔ Subgroup.zpowers b = E := by
    apply Subgroup.eq_of_le_of_card_ge (sup_le inf_le_left hbZ)
    rw [hsup, hEcard]
    norm_num
  have hENW : E ≤ Subgroup.normalizer (W : Set G) := by
    rw [← hEeq]
    exact sup_le hN (Subgroup.zpowers_le.2 hbN)
  obtain ⟨x₀, hx₀T, hx₀ne⟩ := exists_ne_one_centralInvol hW hW0
  have hTne : centralInvol W ≠ ⊥ := by
    intro h
    apply hx₀ne
    have : x₀ ∈ (⊥ : Subgroup G) := h ▸ hx₀T
    exact Subgroup.mem_bot.1 this
  have hTinv : ∀ e ∈ E, ∀ x ∈ centralInvol W, e * x * e⁻¹ ∈ centralInvol W := by
    intro e he x hx
    obtain ⟨hxW, hxc, hx2⟩ := mem_centralInvol.1 hx
    have hNe := hENW he
    have hNe' := hENW (E.inv_mem he)
    refine mem_centralInvol.2 ⟨(Subgroup.mem_normalizer_iff.1 hNe x).1 hxW, fun t ht => ?_, ?_⟩
    · have ht' : e⁻¹ * t * e⁻¹⁻¹ ∈ W := (Subgroup.mem_normalizer_iff.1 hNe' t).1 ht
      rw [inv_inv] at ht'
      have hcm := hxc _ ht'
      calc t * (e * x * e⁻¹) = e * (e⁻¹ * t * e * x) * e⁻¹ := by group
        _ = e * (x * (e⁻¹ * t * e)) * e⁻¹ := by rw [hcm]
        _ = e * x * e⁻¹ * t := by group
    · rw [show (e * x * e⁻¹) ^ 2 = e * x ^ 2 * e⁻¹ by simp only [pow_two, mul_assoc,
        inv_mul_cancel_left], hx2]
      simp
  obtain ⟨U, hUT, hUne, hUinv, hUirr⟩ := exists_minimal_invariant hTne hTinv
  have hUel : IsElemAbelian 2 U := isElemAbelian_two_of_le hUT
  have hUW : U ≤ W := fun x hx => (mem_centralInvol.1 (hUT hx)).1
  have hUI : U ≤ I := hUW.trans hWI
  have hU2 : IsPGroup 2 U := isPGroup_of_isElemAbelian hUel
  have hcard := card_centralizer_ge_nine hE hEcard hUel hUne hUinv hUirr
  by_cases hEU : E ≤ Subgroup.centralizer (U : Set G)
  · have hF : U = ⊥ := hF2 U hU2 hUI (inf_le_left.trans hEU)
    exact hUne hF
  · obtain ⟨g, hgE, hgU⟩ := SetLike.not_le_iff_exists.1 hEU
    obtain ⟨u, huU, hu⟩ : ∃ u ∈ U, g * u * g⁻¹ ≠ u := by
      by_contra hcon
      push Not at hcon
      apply hgU
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      have e1 : g * h * g⁻¹ = h := hcon h hh
      calc h * g = (g * h * g⁻¹) * g := by rw [e1]
        _ = g * h := by group
    set C : Subgroup G := E ⊓ Subgroup.centralizer (U : Set G) with hCdef
    have hCE : C ≤ E := inf_le_left
    have hEI' : E ⊓ I ≤ E := inf_le_left
    have hprod2 := card_sup_mul_card_inf_of_le_normalizer (A := C) (B := E ⊓ I)
      (le_normalizer_of_comm hE hCE hEI')
    have hsupC : Nat.card ↥(C ⊔ (E ⊓ I)) ≤ 27 := by
      have h1 := Subgroup.card_le_of_le (sup_le hCE hEI')
      rw [hEcard] at h1
      norm_num at h1
      exact h1
    have hCI : 3 ≤ Nat.card ↥(C ⊓ (E ⊓ I)) := by
      rw [hE0] at hprod2
      by_contra hlt
      push Not at hlt
      have h2 : Nat.card ↥(C ⊔ (E ⊓ I)) * Nat.card ↥(C ⊓ (E ⊓ I)) ≤ 27 * 2 :=
        Nat.mul_le_mul hsupC (by omega)
      omega
    obtain ⟨k, hkCI, hk1⟩ : ∃ k ∈ C ⊓ (E ⊓ I), k ≠ 1 := by
      by_contra hcon
      push Not at hcon
      have hbot : C ⊓ (E ⊓ I) = ⊥ := by
        rw [eq_bot_iff]
        intro x hx
        exact Subgroup.mem_bot.2 (hcon x hx)
      rw [hbot, Subgroup.card_bot] at hCI
      omega
    have hu1 : u ≠ 1 := fun h => hu (by rw [h]; group)
    have hu'U : g * u * g⁻¹ ∈ U := hUinv g hgE u huU
    have hu'1 : g * u * g⁻¹ ≠ 1 := fun h => hu1 (by
      calc u = g⁻¹ * (g * u * g⁻¹) * g := by group
        _ = 1 := by rw [h]; group)
    have hu2 : u ^ 2 = 1 := hUel.2 u huU
    have hu'2 : (g * u * g⁻¹) ^ 2 = 1 := by
      rw [show (g * u * g⁻¹) ^ 2 = g * u ^ 2 * g⁻¹ by simp only [pow_two, mul_assoc,
        inv_mul_cancel_left], hu2]
      simp
    have hcomm : u * (g * u * g⁻¹) = (g * u * g⁻¹) * u :=
      isElemAbelian_commute hUel huU hu'U
    have hkC : k ∈ Subgroup.centralizer (U : Set G) := hkCI.1.2
    have hkE : k ∈ E := hkCI.2.1
    have hkI : k ∈ I := hkCI.2.2
    have hk3 : k ^ 3 = 1 := hE.2 k hkE
    have hku : k * u = u * k := (Subgroup.mem_centralizer_iff.1 hkC u huU).symm
    have hku' : k * (g * u * g⁻¹) = (g * u * g⁻¹) * k :=
      (Subgroup.mem_centralizer_iff.1 hkC _ hu'U).symm
    exact hk1 (hK u (g * u * g⁻¹) k (hUI huU) (hUI hu'U) (hUel.2 u huU) hu'2 hu1 hu'1
      hu.symm hcomm hkI hk3 hku hku')

theorem smallF1_of_f2_klein (S : Type) [Group S] [Finite S] (E : Subgroup (MulAut S))
    (hE : IsElemAbelian 3 E) (hEcard : Nat.card E = 3 ^ 3)
    (hE0 : Nat.card ↥(E ⊓ CFSG.ComponentClassification.OuterAutomorphisms.inner S) = 3 ^ 2)
    (hF2 : SmallF2 S E)
    (hK : KleinFour3 (CFSG.ComponentClassification.OuterAutomorphisms.inner S)) :
    SmallF1 S E := by
  haveI : Finite (MulAut S) := MulEquiv.finite_left
  intro b hbE hbI W hW hW0 hWI hWb hN
  exact f1_of_f2_klein hE hEcard hE0 hbE hbI hF2 hK W hW hW0 hWI hWb hN

end CFSG.LocalAnalysis.GLTheoremA.KDRank3SmallF12Red
