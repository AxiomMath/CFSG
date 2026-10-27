module

public import CFSG.ClassicalInvolution.Q3.TL4StarSecSqrt

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77

variable {X : Type} [Group X] [Finite X] {Φ : Set (Subgroup X)}

omit [Finite X] in
theorem mem_of_isSylow2In_of_central {H P : Subgroup X} (hP : IsSylow2In P H) {c : X}
    (hcH : c ∈ H) (hc : ∀ y ∈ H, c * y = y * c) (hc2 : c * c = 1) : c ∈ P := by
  by_cases hc1 : c = 1
  · rw [hc1]; exact P.one_mem
  have h2 : IsPGroup 2 (Subgroup.zpowers c) :=
    IsPGroup.of_card (n := 1)
      (by rw [Nat.card_zpowers, orderOf_eq_prime (by rw [pow_two]; exact hc2) hc1, pow_one])
  have hN : Subgroup.zpowers c ≤ Subgroup.normalizer (P : Set X) := by
    refine Subgroup.zpowers_le.mpr (Subgroup.centralizer_le_normalizer (P : Set X) ?_)
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact (hc y (hP.1 hy)).symm
  have h3 := hP.2.2 _ (sup_le hP.1 (Subgroup.zpowers_le.mpr hcH))
    (hP.2.1.to_sup_of_normal_left' h2 hN) le_sup_left
  exact h3 ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers c)

omit [Finite X] in
theorem orderOf_map_eq_four {G : Type} [Group G] {ψ : G →* X}
    (hker : ψ.ker ≤ Subgroup.center G) {u : G} (hu4 : orderOf u = 4)
    (huZ : u * u ∉ Subgroup.center G) : orderOf (ψ u) = 4 := by
  have h1 : ¬ ψ u ^ 2 ^ 1 = 1 := by
    rw [pow_one, pow_two, ← map_mul]
    exact fun h => huZ (hker h)
  have h2 : ψ u ^ 2 ^ (1 + 1) = 1 := by
    rw [← map_pow, show 2 ^ (1 + 1) = 4 by norm_num, ← hu4, pow_orderOf_eq_one, map_one]
  simpa using orderOf_eq_prime_pow h1 h2

theorem starNbr_of_pair {G : Type} [Group G] {𝓕 : Set (Subgroup G)} {ψ : G →* X}
    (hker : ψ.ker ≤ Subgroup.center G) (hfund : ∀ L ∈ Φ, ∃ R ∈ 𝓕, IsSylow2In L (R.map ψ))
    (hcls : ∀ R ∈ 𝓕, ∀ R' ∈ 𝓕, ∃ g : X, R'.map ψ = conjSub g (R.map ψ))
    {R₀ R₁ : Subgroup G} (hR₀ : R₀ ∈ 𝓕) (hR₁ : R₁ ∈ 𝓕) {a u x : G} (ha : a ∈ R₀)
    (hac : ∀ y ∈ R₀, a * y = y * a) (ha2 : a * a = 1) (haZ : a ∉ Subgroup.center G)
    (hu : u ∈ R₁) (hx : x ∈ R₁) (hu4 : orderOf u = 4) (hx4 : orderOf x = 4)
    (huZ : u * u ∉ Subgroup.center G) (hxu : x * u * x⁻¹ = u⁻¹) (hua : u * a = a * u)
    (hxa : x * a * x⁻¹ * a⁻¹ ∉ Subgroup.center G) (hR : TypeRFam 3 Φ)
    (htr : ∀ L ∈ Φ, ∀ L' ∈ Φ, ∃ g : X, conjSub g L = L') :
    ∀ L ∈ Φ, ∃ L' ∈ Φ, L' ∈ omegaStarNbr Φ L ∧ L' ∉ omegaNbr Φ L := by
  have hΦ := hR.hyp.conjInvariant
  intro L hL
  obtain ⟨R, hRf, hLR⟩ := hfund L hL
  obtain ⟨g₀, hg₀⟩ := hcls R hRf R₀ hR₀
  have hL₀ : conjSub g₀ L ∈ Φ := hΦ g₀ L hL
  have hL₀R : IsSylow2In (conjSub g₀ L) (R₀.map ψ) := hg₀ ▸ hLR.conj g₀
  have hψa1 : ψ a ≠ 1 := fun h => haZ (hker h)
  have hψa2 : ψ a * ψ a = 1 := by rw [← map_mul, ha2, map_one]
  have hψaL : ψ a ∈ conjSub g₀ L := by
    refine mem_of_isSylow2In_of_central hL₀R (Subgroup.mem_map_of_mem ψ ha) (fun y hy => ?_) hψa2
    obtain ⟨y', hy', rfl⟩ := hy
    rw [← map_mul, ← map_mul, hac y' hy']
  obtain ⟨⟨z, hz⟩, -⟩ := hR.hyp.omega1 _ hL₀
  have hza : ψ a = z := (hz.unique _ hψaL hψa2).resolve_left hψa1
  rw [← hza] at hz
  have hU2 : IsPGroup 2 (Subgroup.zpowers u) :=
    IsPGroup.of_card (n := 2) (by rw [Nat.card_zpowers, hu4]; norm_num)
  have hX2 : IsPGroup 2 (Subgroup.zpowers x) :=
    IsPGroup.of_card (n := 2) (by rw [Nat.card_zpowers, hx4]; norm_num)
  have hXN : Subgroup.zpowers x ≤ Subgroup.normalizer (Subgroup.zpowers u : Set G) := by
    refine Subgroup.zpowers_le.mpr (mem_normalizer_iff_conjSub_eq.mpr ?_)
    rw [AscL62.conjSub_zpowers_eq, hxu, Subgroup.zpowers_inv]
  have hQ2 : IsPGroup 2 ↥(Subgroup.zpowers u ⊔ Subgroup.zpowers x) :=
    hU2.to_sup_of_normal_left' hX2 hXN
  have hQR : Subgroup.zpowers u ⊔ Subgroup.zpowers x ≤ R₁ :=
    sup_le (Subgroup.zpowers_le.mpr hu) (Subgroup.zpowers_le.mpr hx)
  obtain ⟨L₁, hL₁R, hQL⟩ := IsSylow2In.exists_ge (hQ2.map ψ) (Subgroup.map_mono hQR)
  have hψu : ψ u ∈ L₁ := hQL (Subgroup.mem_map_of_mem ψ (Subgroup.mem_sup_left
    (Subgroup.mem_zpowers u)))
  have hψx : ψ x ∈ L₁ := hQL (Subgroup.mem_map_of_mem ψ (Subgroup.mem_sup_right
    (Subgroup.mem_zpowers x)))
  have hL₁ : L₁ ∈ Φ := by
    obtain ⟨g₁, hg₁⟩ := hcls R hRf R₁ hR₁
    have hS : IsSylow2In (conjSub g₁ L) (R₁.map ψ) := hg₁ ▸ hLR.conj g₁
    obtain ⟨c, -, hc⟩ := Disconnected.AschTight.S1916.IsSylow2In.exists_conj hS hL₁R
    rw [← hc, ← conjSub_mul]
    exact hΦ _ L hL
  have hxa' : ψ x * ψ a ≠ ψ a * ψ x := by
    intro h
    apply hxa
    apply hker
    rw [MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv, h]
    group
  have hpair : L₁ ∈ omegaStarNbr Φ (conjSub g₀ L) ∧ L₁ ∉ omegaNbr Φ (conjSub g₀ L) := by
    have hne : L₁ ≠ conjSub g₀ L := by
      intro he
      have hxL : ψ x ∈ conjSub g₀ L := he ▸ hψx
      exact hxa' (hz.commute_of_mem hxL).symm
    have hL₁2 : IsPGroup 2 L₁ := hL₁R.2.1
    have hL₁RS : L₁ ∈ RSet Φ := mem_RSet_of_isSylow2In hL₁ ⟨le_rfl, hL₁2, fun V hV _ hle =>
      le_antisymm hV hle⟩
    have hψu4 := orderOf_map_eq_four hker hu4 huZ
    refine ⟨⟨hL₁, hne, Subgroup.zpowers (ψ u), ⟨L₁, hL₁RS, Subgroup.zpowers_le.mpr hψu,
      inferInstance, ?_⟩, Subgroup.zpowers_le.mpr hψu, ?_⟩, ?_⟩
    · have h1 := Subgroup.relIndex_mul_card (Subgroup.zpowers (ψ u)) L₁
      rw [inf_eq_left.mpr (Subgroup.zpowers_le.mpr hψu), Nat.card_zpowers, hψu4,
        natCard_of_mem_RSet hR hL₁RS] at h1
      omega
    · refine Subgroup.zpowers_le.mpr (hR.tight _ hL₀ _ hz ?_)
      rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul, hua]
    · rintro ⟨-, -, S, hSR, hSL, hSN⟩
      have hS := isSylow2In_of_mem_RSet_le hR hL₁ hSR hSL
      have hSeq : S = L₁ := (hS.2.2 L₁ le_rfl hL₁2 hSL).symm
      rw [hSeq] at hSN
      have h1 := hz.conj_eq (conjSub_eq_of_mem_normalizer (hSN hψx))
      exact hxa' (by
        calc ψ x * ψ a = (ψ x * ψ a * (ψ x)⁻¹) * ψ x := by group
          _ = ψ a * ψ x := by rw [h1])
  exact starNbr_of_exists hΦ htr ⟨_, hL₀, L₁, hpair.1, hpair.2⟩ L hL

end CFSG.ClassicalInvolution.Q3.TL4
