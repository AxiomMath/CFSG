module

public import CFSG.LocalAnalysis.ComponentClassification.ExcSelectorEvenGFE
public import CFSG.GH74.Generic.S45.LExcBase

public noncomputable section

namespace CFSG.ComponentClassification.ExcSelector

open CFSG Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.OuterAutomorphisms (inner)

variable {K : Type} [Field K]

theorem even_field_noSmallQ8 [Finite K] {τ : Tag}
    (hτ : τ = .G2 ∨ τ = .F4 ∨ τ = .E7 ∨ τ = .E8) {e : ℕ} (he : 1 ≤ e)
    (hK : Nat.card K = 2 ^ (2 * e)) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ 2 ^ e)
    {γ : MulAut (adjointGroup τ K)}
    (hγ : ∀ u, (γ u : ModGL τ K) = Units.map (entrywiseHom σ.toRingHom) (u : ModGL τ K))
    {L : Subgroup (adjointGroup τ K)} (hL : Assembly.IsComponentOf L (fixedSubgroup γ))
    : ¬ SmallQ8 L := by
  have : CharP K 2 :=
    LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two
      (by omega) hK
  have hchar : ringChar K = 2 := ringChar.eq K 2
  have hk := card_fixSubfield_of_pow he hK hσ
  have hfix := fixedSubgroup_eq_fixedFieldImage_even (by
    rcases hτ with h | h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr h)))) hchar σ hγ
  rcases hτ with rfl | rfl | rfl | rfl
  · rcases Nat.lt_or_ge e 2 with he2 | he2
    ·
      have he1 : e = 1 := by omega
      subst he1
      have hJC : fixedFieldImage .G2 σ ≤ adjointGroup .G2 K := fun x hx =>
        (fixedFieldImage_le hx).1
      set J := (fixedFieldImage .G2 σ).subgroupOf (adjointGroup .G2 K) with hJ
      have eJ : J ≃* adjointGroup .G2 (fixSubfield σ) :=
        (Subgroup.subgroupOfEquivOfLe hJC).trans (fixedFieldImageEquiv σ).symm
      rw [hfix] at hL
      have hJcard : Nat.card J = 12096 := by
        rw [Nat.card_congr eJ.toEquiv]
        exact card_adjointGroup_G2_two (by rw [hk]; norm_num)
      have hL12 : Nat.card L ∣ 12096 := by
        rw [← hJcard]
        exact Subgroup.card_dvd_of_le hL.1
      exact fun hs => not_q8Order_of_card_dvd hL12
        CFSG.GH74.Generic.S45.ordClosable_12096 hs.2
    · obtain ⟨hs, hn⟩ := adjointGroup_G2_even (by omega) hk he2
      exact not_smallQ8_of_not_smallType (not_smallType_of_fixedFieldImage σ hfix hs hn hL)
  · obtain ⟨hs, hn⟩ := adjointGroup_F4_even he hk
    exact not_smallQ8_of_not_smallType (not_smallType_of_fixedFieldImage σ hfix hs hn hL)
  · obtain ⟨hs, hn⟩ := adjointGroup_E7_even he hk
    exact not_smallQ8_of_not_smallType (not_smallType_of_fixedFieldImage σ hfix hs hn hL)
  · obtain ⟨hs, hn⟩ := adjointGroup_E8_even he hk
    exact not_smallQ8_of_not_smallType (not_smallType_of_fixedFieldImage σ hfix hs hn hL)


theorem even_GFE_noSmallQ8 [Finite K] {τ : Tag} (hτ : τ = .G2 ∨ τ = .F4 ∨ τ = .E7 ∨ τ = .E8)
    {f : ℕ} (hf : 1 ≤ f) (hG2 : τ = .G2 → 2 ≤ f) (hK : Nat.card K = 2 ^ f)
    (β : MulAut (adjointGroup τ K)) (hβ2 : β ^ 2 = 1) (hβ1 : β ≠ 1)
    {L : Subgroup (adjointGroup τ K)} (hL : Assembly.IsComponentOf L (fixedSubgroup β))
    : ¬ SmallQ8 L := by
  have : CharP K 2 :=
    LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two hf hK
  by_cases hin : β ∈ inner (adjointGroup τ K)
  · obtain ⟨c, rfl⟩ := hin
    have hc1 : c ≠ 1 := fun h => hβ1 (by rw [h, map_one])
    have hc2 : c ^ 2 = 1 := by
      apply mulAut_conj_injective_of_center_eq_bot center_adjointGroup_eq_bot
      rw [map_pow, hβ2, map_one]
    exact absurd hL (not_isComponentOf_fixedSubgroup_conj (RootWeightDatum.ordinary τ) hc1 hc2 L)
  rcases hτ with rfl | rfl | hτ
  ·
    rcases UnbalancedCatalog.even_G2_involution_inner_or_canonical_field (hG2 rfl) K hK β
        (orderOf_eq_prime hβ2 hβ1) with h | ⟨⟨e, he⟩, hδ⟩
    · exact absurd h hin
    have he1 : 1 ≤ e := by have := hG2 rfl; omega
    have hK' : Nat.card K = 2 ^ (2 * e) := by rw [hK, he, two_mul]
    set δ := iterateFrobenius K 2 (f / 2) with hδdef
    have hδc : ∀ c, δ c = c ^ 2 ^ (f / 2) := fun c => iterateFrobenius_def 2 (f / 2) c
    obtain ⟨β', ψ, hβ', hψ, -⟩ := hδ δ hδc
    set σ := ringEquivOfFinite δ
    have hσ : ∀ c, σ c = c ^ 2 ^ e := fun c => by
      rw [ringEquivOfFinite_apply, hδc, show f / 2 = e by omega]
    refine not_smallQ8_of_conj hψ (fun L' hL' => ?_) hL
    exact even_field_noSmallQ8 (Or.inl rfl) he1 hK' σ hσ
      (fun u => by rw [hβ' u, toRingHom_ringEquivOfFinite]) hL'
  ·
    have : CharP K ReeTag.F4.prime := inferInstanceAs (CharP K 2)
    obtain ⟨ψ, hψ, heven, hodd, -⟩ := even_F4_all_outer_involutions_canonical hf K hK β hβ2 hin
    refine not_smallQ8_of_conj hψ (fun L' hL' => ?_) hL
    obtain ⟨n, hn | hn⟩ := Nat.even_or_odd' f
    ·
      have hn1 : 1 ≤ n := by omega
      have hK' : Nat.card K = 2 ^ (2 * n) := by rw [hK, hn]
      set δ := iterateFrobenius K 2 n
      have hδc : ∀ c, δ c = c ^ 2 ^ n := fun c => iterateFrobenius_def 2 n c
      set σ := ringEquivOfFinite δ
      exact even_field_noSmallQ8 (τ := .F4) (Or.inr (Or.inl rfl)) hn1 hK' σ
        (fun c => by rw [ringEquivOfFinite_apply, hδc])
        (fun u => by
          have h := (heven n hn).2 δ hδc u
          rw [toRingHom_ringEquivOfFinite]
          exact h) hL'
    ·
      have hK' : Nat.card K = 2 ^ (2 * n + 1) := by rw [hK, hn]
      rw [(hodd n hn).1, fixedSubgroup_finiteReeAut] at hL'
      rcases Nat.eq_zero_or_pos n with rfl | hn1
      · exact not_smallQ8_of_not_smallType
          (not_smallType_of_isComponentOf_reeFixed_tits (by rw [hK']; norm_num) hL')
      · obtain ⟨hs, hns⟩ := reeFixed_F4_simple_not_smallType hn1 hK'
        refine not_smallQ8_of_not_smallType ?_
        rwa [eq_of_isComponentOf_of_isSimpleGroup hL']
  ·
    obtain ⟨hNF, Θ, hΘ, -, hker, hinv⟩ :=
      even_E7_E8_exact_inner_field_automorphism_normal_form hf K hK τ hτ
    obtain ⟨⟨g, σ⟩, hgσ, -⟩ := hNF β
    have hσ : Θ β = σ := hΘ β g σ hgσ
    rcases hinv β hβ2 with h1 | ⟨⟨e, he⟩, hpow⟩
    · have hker' : β ∈ Θ.ker := MonoidHom.mem_ker.2 h1
      rw [hker] at hker'
      exact absurd hker' hin
    have he1 : 1 ≤ e := by omega
    have hK' : Nat.card K = 2 ^ (2 * e) := by rw [hK, he, two_mul]
    have hσe : ∀ c, σ c = c ^ 2 ^ e := fun c => by
      rw [← hσ, hpow c, show f / 2 = e by omega]
    obtain ⟨_, -, hdesc⟩ :=
      (even_exceptional_quadratic_field_graph_field_involution_descent he1 K hK' σ.toRingHom
        hσe).1 τ
    obtain ⟨ψ, hψ, -⟩ := (hdesc g 1).2 β
      (fun u => by rw [hgσ u, rootDiagUnit_one, mul_one, inv_one, mul_one]) (by rw [← sq, hβ2])
    refine not_smallQ8_of_conj (ψ := ψ) (γ := ψ * β * ψ⁻¹) rfl
      (fun L' hL' => ?_) hL
    rcases hτ with rfl | rfl
    · exact even_field_noSmallQ8 (Or.inr (Or.inr (Or.inl rfl))) he1 hK' σ hσe hψ hL'
    · exact even_field_noSmallQ8 (Or.inr (Or.inr (Or.inr rfl))) he1 hK' σ hσe hψ hL'


end CFSG.ComponentClassification.ExcSelector
