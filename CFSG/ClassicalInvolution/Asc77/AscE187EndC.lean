module

public import CFSG.ClassicalInvolution.Asc77.AscE187EndB
public import CFSG.ClassicalInvolution.Asc77.AscE187Img
public import CFSG.ClassicalInvolution.Asc77.AscE187Cop
public import CFSG.ClassicalInvolution.Asc77.AscSixModCent

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution.Generic
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}

theorem goodInv_twMk {H : Subgroup G} {t d : G} (hd : GoodInv H t d) (hC : d ∈ TwC t) :
    GoodInv (twImage t H) (twT t) (twMk t ⟨d, hC⟩) := by
  have hsq : (⟨d, hC⟩ : ↥(TwC t)) * ⟨d, hC⟩ = 1 := Subtype.ext hd.sq
  refine ⟨?_, ?_, twMk_comm t _, ?_⟩
  · exact fun h => not_mem_oddCore_of_sq (⟨d, hC⟩ : ↥(TwC t)) hsq
      (fun h' => hd.ne_one (congrArg Subtype.val h')) ((twMk_eq_one_iff t _).mp h)
  · rw [← map_mul, hsq, map_one]
  · intro x hx
    obtain ⟨y, rfl⟩ := twMk_surjective t x
    rw [Subgroup.mem_centralizer_singleton_iff] at hx
    have hxN : y⁻¹ * (⟨d, hC⟩ * y * (⟨d, hC⟩ : ↥(TwC t))⁻¹) ∈
        classicalInvolutionOddCore ↥(TwC t) := by
      rw [← twMk_eq_one_iff]
      have e : twMk t (y⁻¹ * (⟨d, hC⟩ * y * (⟨d, hC⟩ : ↥(TwC t))⁻¹)) =
          ⁅(twMk t y)⁻¹, twMk t ⟨d, hC⟩⁆ := by
        simp only [commutatorElement_def, map_mul, map_inv]
        group
      rw [e]
      exact commutatorElement_eq_one_iff_mul_comm.mpr
        (Commute.inv_left (show Commute (twMk t y) (twMk t ⟨d, hC⟩) from hx)).eq
    obtain ⟨n, hn, hfix⟩ := exists_mul_mem_centralizer_of_odd
      (CFSG.ComponentClassification.OddCore.odd_card ↥(TwC t)) hsq hxN
    have hyH : ((y * n : ↥(TwC t)) : G) ∈ H := by
      apply hd.cent
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (congrArg Subtype.val hfix).symm
    refine ⟨y * n, Subgroup.mem_subgroupOf.mpr hyH, ?_⟩
    rw [map_mul, (twMk_eq_one_iff t n).mpr hn, mul_one]

theorem E187C.hbad_twImage_of (hc : ConjInvariant Ω) {H : Subgroup G} {t : G}
    (htw : ∀ {M : Subgroup G} (_ : M ∈ Ω) (hMt : IsUniqueInvolution M t),
      ∃ ψ : ↥M →* ↥(twImage t M), Function.Surjective ψ ∧
        ψ.ker = classicalInvolutionOddCore ↥M ∧
        ∀ x : ↥M, ((ψ x : ↥(twImage t M)) : TwQ t) =
          twMk t ⟨(x : G), le_TwC_of_isUniqueInvolution hMt x.2⟩)
    (hbad : ∀ M ∈ Ω, IsUniqueInvolution M t → ∀ u ∈ M, orderOf u = 4 → u ∉ H) :
    ∀ L ∈ twFamily Ω t, IsUniqueInvolution L (twT t) → ∀ ū ∈ L, orderOf ū = 4 →
      ū ∉ twImage t H := by
  rintro _ ⟨M, hM, hMt, rfl⟩ - ū hū hū4 hūH
  obtain ⟨ψ, hψs, hψker, hψapp⟩ := htw hM hMt
  have hb4 : orderOf (⟨ū, hū⟩ : ↥(twImage t M)) = 4 := by
    rw [Subgroup.orderOf_mk]
    exact hū4
  have hb2 : IsPGroup 2 (Subgroup.zpowers (⟨ū, hū⟩ : ↥(twImage t M))) :=
    IsPGroup.of_card (n := 2) (by rw [Nat.card_zpowers, hb4]; norm_num)
  obtain ⟨a, hab, ha2⟩ := exists_isPGroup_zpowers_lift ψ hψs hb2
  have ha4 : orderOf a = 4 := by
    have h1 : ψ (a ^ 4) = 1 := by
      rw [map_pow, hab, ← hb4]
      exact pow_orderOf_eq_one _
    have h2 : a ^ 4 ∈ classicalInvolutionOddCore ↥M := by
      rw [← hψker]
      exact h1
    have h3 : a ^ 4 = 1 :=
      eq_one_of_isPGroup_of_mem_odd (CFSG.ComponentClassification.OddCore.odd_card ↥M) h2
        (ha2.to_le (Subgroup.zpowers_le.mpr (Subgroup.pow_mem _ (Subgroup.mem_zpowers a) 4)))
    have h4 : orderOf a ∣ 4 := orderOf_dvd_of_pow_eq_one h3
    have h5 : 4 ∣ orderOf a := by
      have := orderOf_map_dvd ψ a
      rwa [hab, hb4] at this
    exact Nat.dvd_antisymm h4 h5
  have hMC : M ≤ TwC t := le_TwC_of_isUniqueInvolution hMt
  set u' : ↥(TwC t) := ⟨(a : G), hMC a.2⟩ with hu'
  have hψu : twMk t u' = ū := by
    have := hψapp a
    rw [hab] at this
    exact this.symm
  have hu'4 : orderOf u' = 4 := by
    rw [hu', Subgroup.orderOf_mk, Subgroup.orderOf_coe, ha4]
  obtain ⟨h', hh', hh'ū⟩ := hūH
  have hO : h'⁻¹ * u' ∈ classicalInvolutionOddCore ↥(TwC t) := by
    rw [← twMk_eq_one_iff, map_mul, map_inv, hh'ū, hψu, inv_mul_cancel]
  have hmem : u' ∈ (H.subgroupOf (TwC t)) ⊔ classicalInvolutionOddCore ↥(TwC t) := by
    have := Subgroup.mul_mem_sup hh' hO
    rwa [mul_inv_cancel_left] at this
  have hu'2 : IsPGroup 2 (Subgroup.zpowers u') :=
    IsPGroup.of_card (n := 2) (by rw [Nat.card_zpowers, hu'4]; norm_num)
  obtain ⟨n, hn, hnH⟩ := exists_conj_mem_of_mem_sup_of_odd
    (CFSG.ComponentClassification.OddCore.odd_card ↥(TwC t)) hu'2 hmem
  have hnt : (n : G) * t * (n : G)⁻¹ = t := by
    rw [mem_TwC_iff.mp n.2]
    group
  have hM'Ω : conjSub (n : G) M ∈ Ω := hc _ M hM
  have hM't : IsUniqueInvolution (conjSub (n : G) M) t := by
    have := hMt.conj (n : G)
    rwa [hnt] at this
  have huH : (n : G) * (a : G) * (n : G)⁻¹ ∈ H := Subgroup.mem_subgroupOf.mp hnH
  refine hbad _ hM'Ω hM't ((n : G) * (a : G) * (n : G)⁻¹) (conj_mem_conjSub a.2) ?_ huH
  rw [orderOf_conj_mul_inv_eq, Subgroup.orderOf_coe, ha4]

theorem hbad_twImage (hΩ : HypOmegaMod p f Ω) {H : Subgroup G} {t : G}
    (hbad : ∀ M ∈ Ω, IsUniqueInvolution M t → ∀ u ∈ M, orderOf u = 4 → u ∉ H) :
    ∀ L ∈ twFamily Ω t, IsUniqueInvolution L (twT t) → ∀ ū ∈ L, orderOf ū = 4 →
      ū ∉ twImage t H :=
  E187C.hbad_twImage_of hΩ.conjInvariant (fun hM hMt => exists_twHom hΩ hM hMt) hbad

theorem E187C.endgame_four_of {Ω : Set (Subgroup G)} {H : Subgroup G} {t : G}
    (hexact : ∀ {H' Kb : Subgroup (TwQ t)} {d₁ d₂ : TwQ t},
      (∀ M ∈ twFamily Ω t, IsUniqueInvolution M (twT t) → ∀ u ∈ M, orderOf u = 4 → u ∉ H') →
      Kb ∈ twFamily Ω t → IsUniqueInvolution Kb (twT t) → GoodInv H' (twT t) d₁ →
      GoodInv H' (twT t) d₂ → GoodInv H' (twT t) (d₁ * d₂) → d₁ * d₂ = d₂ * d₁ → False)
    (hbadim : ∀ L ∈ twFamily Ω t, IsUniqueInvolution L (twT t) → ∀ ū ∈ L, orderOf ū = 4 →
      ū ∉ twImage t H)
    {K₁ : Subgroup G} (hK₁ : K₁ ∈ Ω) (ht : IsUniqueInvolution K₁ t) {d₁ d₂ : G}
    (g₁ : GoodInv H t d₁) (g₂ : GoodInv H t d₂) (g₃ : GoodInv H t (d₁ * d₂))
    (hc : d₁ * d₂ = d₂ * d₁) : False := by
  have hC₁ : d₁ ∈ TwC t := mem_TwC_iff.mpr g₁.comm_t
  have hC₂ : d₂ ∈ TwC t := mem_TwC_iff.mpr g₂.comm_t
  have hC₃ : d₁ * d₂ ∈ TwC t := mem_TwC_iff.mpr g₃.comm_t
  have e₃ : twMk t ⟨d₁ * d₂, hC₃⟩ = twMk t ⟨d₁, hC₁⟩ * twMk t ⟨d₂, hC₂⟩ := by
    rw [← map_mul]
    rfl
  have hc' : twMk t ⟨d₁, hC₁⟩ * twMk t ⟨d₂, hC₂⟩ = twMk t ⟨d₂, hC₂⟩ * twMk t ⟨d₁, hC₁⟩ := by
    rw [← map_mul, ← map_mul]
    exact congrArg (twMk t) (Subtype.ext hc)
  refine hexact hbadim (Kb := twImage t K₁) ⟨K₁, hK₁, ht, rfl⟩ (isUniqueInvolution_twImage ht)
    (goodInv_twMk g₁ hC₁) (goodInv_twMk g₂ hC₂) ?_ hc'
  rw [← e₃]
  exact goodInv_twMk g₃ hC₃



theorem endgame_four (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : HypOmegaMod p f Ω) {H : Subgroup G}
    {t : G} (hbad : ∀ M ∈ Ω, IsUniqueInvolution M t → ∀ u ∈ M, orderOf u = 4 → u ∉ H)
    {K₁ : Subgroup G} (hK₁ : K₁ ∈ Ω) (ht : IsUniqueInvolution K₁ t) {d₁ d₂ : G}
    (g₁ : GoodInv H t d₁) (g₂ : GoodInv H t d₂) (g₃ : GoodInv H t (d₁ * d₂))
    (hc : d₁ * d₂ = d₂ * d₁) : False := by
  exact E187C.endgame_four_of
    (fun hb hK ht g₁ g₂ g₃ hc =>
      endgame_four_exact (Ω := twFamily Ω t) hp hq (twFamily_hypOmega hp hq hΩ t) hb hK ht g₁ g₂ g₃
        hc)
    (hbad_twImage hΩ hbad) hK₁ ht g₁ g₂ g₃ hc

end CFSG.ClassicalInvolution.Asc77
