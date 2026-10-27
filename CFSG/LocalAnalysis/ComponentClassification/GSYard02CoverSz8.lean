module

public import CFSG.LocalAnalysis.ComponentClassification.GSYard02CoverGH
public import CFSG.RankThree.SteinbergR3ESuzukiInvolutionCentralizers

public section

namespace CFSG.ComponentClassification.Sol76.Sig.GSYard02

open CFSG Subgroup CFSG.Blueprint

theorem suzuki_sylow_involution_central {K : Type} [Field K]
    [Finite K] [Finite (suzukiGroup 1 K)] (hK : Nat.card K = 2 ^ (2 * 1 + 1))
    (T : Sylow 2 (suzukiGroup 1 K)) :
    ∀ t ∈ (T : Subgroup (suzukiGroup 1 K)), t ^ 2 = 1 →
      ∀ s ∈ (T : Subgroup (suzukiGroup 1 K)), t * s = s * t := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, -, -, -, -, hcent, -⟩ := CFSG.LieType.Ree.suzuki_unipotent_structure hK
  let P₀ : Sylow 2 (suzukiGroup 1 K) :=
    Sylow.ofCard (CFSG.LieType.Ree.suzukiU 1 K) (CFSG.RankThree.card_suzukiU_eq hK)
  obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq (suzukiGroup 1 K) P₀ T
  have hT : ((g • P₀ : Sylow 2 (suzukiGroup 1 K)) : Subgroup (suzukiGroup 1 K)) =
      (CFSG.LieType.Ree.suzukiU 1 K).map (MulAut.conj g).toMonoidHom := rfl
  intro t ht hsq s hs
  rw [hT] at ht hs
  obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp ht
  obtain ⟨v, hv, rfl⟩ := Subgroup.mem_map.mp hs
  have hu2 : u ^ 2 = 1 := by
    have h1 : (MulAut.conj g) (u ^ 2) = 1 := by
      rw [map_pow]
      exact hsq
    exact (MulAut.conj g).injective (h1.trans (map_one _).symm)
  have huv : u * v = v * u :=
    hcent u ((CFSG.ShultStronglyClosedTI.SuzukiLayerKernel.mem_suzukiZ0_iff_sq_eq_one hK).2
      ⟨hu, hu2⟩) v hv
  change g * u * g⁻¹ * (g * v * g⁻¹) = g * v * g⁻¹ * (g * u * g⁻¹)
  have h3 : g * u * g⁻¹ * (g * v * g⁻¹) = g * (u * v) * g⁻¹ := by group
  have h4 : g * v * g⁻¹ * (g * u * g⁻¹) = g * (v * u) * g⁻¹ := by group
  rw [h3, h4, huv]

theorem sylowFourJoined_of_sz8_cover {Q : Type} [Group Q] [Finite Q]
    (hz : center Q ≠ ⊥) (hcard : Nat.card (center Q) ≤ 2) (hr : 3 ≤ CFSG.pRank 2 Q)
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2 ^ (2 * 1 + 1))
    (e : Q ⧸ center Q ≃* suzukiGroup 1 K) : SylowFourJoined Q := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (suzukiGroup 1 K) := Finite.of_equiv (Q ⧸ center Q) e.toEquiv
  have hsup : ∃ E : Subgroup Q, CFSG.IsElementaryAbelian 2 E ∧
      Nat.card E = 2 ^ CFSG.pRank 2 Q := by
    have hne : {r : ℕ | ∃ A : Subgroup Q, CFSG.IsElementaryAbelian 2 A ∧
        Nat.card A = 2 ^ r}.Nonempty := by
      by_contra hem
      rw [Set.not_nonempty_iff_eq_empty] at hem
      have h0 : CFSG.pRank 2 Q = 0 := by
        unfold CFSG.pRank
        rw [hem]
        simp
      omega
    have hbdd : BddAbove {r : ℕ | ∃ A : Subgroup Q, CFSG.IsElementaryAbelian 2 A ∧
        Nat.card A = 2 ^ r} := by
      refine ⟨Nat.card Q, ?_⟩
      rintro r ⟨A, -, hA⟩
      have h1 := Subgroup.card_le_card_group A
      rw [hA] at h1
      exact (Nat.lt_two_pow_self (n := r)).le.trans h1
    unfold CFSG.pRank
    obtain ⟨A, hA, hAc⟩ := Nat.sSup_mem hne hbdd
    exact ⟨A, hA, hAc⟩
  obtain ⟨E, hEel, hEcard⟩ := hsup
  have h8 : 8 ≤ Nat.card E := by
    rw [hEcard]
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ CFSG.pRank 2 Q := Nat.pow_le_pow_right (by norm_num) hr
  have hxx : ∀ x ∈ E, x * x = 1 := fun x hx => by
    rw [← pow_two]
    exact CFSG.elemPow_eq_one_of_isElementaryAbelian (p := 2) x hx
  have hZ2 : ∀ c ∈ center Q, c * c = 1 := by
    have hne1 : Nat.card (center Q) ≠ 1 := fun h => hz (Subgroup.card_eq_one.mp h)
    have hpos : 0 < Nat.card (center Q) := Nat.card_pos
    have h2 : Nat.card (center Q) = 2 := by omega
    intro c hc
    have hdvd := orderOf_dvd_natCard (⟨c, hc⟩ : center Q)
    rw [h2] at hdvd
    have hpow : (⟨c, hc⟩ : center Q) ^ 2 = 1 := orderOf_dvd_iff_pow_eq_one.mp hdvd
    have hc2 : c ^ 2 = 1 := by
      have := congrArg Subtype.val hpow
      simpa using this
    rw [pow_two] at hc2
    exact hc2
  obtain ⟨S₀, hES⟩ : ∃ S₀ : Sylow 2 Q, E ≤ (S₀ : Subgroup Q) :=
    IsPGroup.exists_le_sylow (CFSG.IsElementaryAbelian.isPGroup 2 E)
  let T₁ : Sylow 2 (Q ⧸ center Q) := S₀.mapSurjective (QuotientGroup.mk'_surjective (center Q))
  let T₂ : Sylow 2 (suzukiGroup 1 K) := T₁.mapSurjective (f := e.toMonoidHom) e.surjective
  have hT₂ : (T₂ : Subgroup (suzukiGroup 1 K)) =
      ((S₀ : Subgroup Q).map (QuotientGroup.mk' (center Q))).map e.toMonoidHom := rfl
  have hkey : ∀ s ∈ (S₀ : Subgroup Q), ∀ x ∈ E, ∃ d ∈ center Q, s * x * s⁻¹ = d * x := by
    intro s hs x hx
    refine ⟨s * x * s⁻¹ * x⁻¹, ?_, by group⟩
    have hx2 : x ^ 2 = 1 := by
      rw [pow_two]
      exact hxx x hx
    have hmem₁ : e (QuotientGroup.mk' (center Q) x) ∈ (T₂ : Subgroup (suzukiGroup 1 K)) := by
      rw [hT₂]
      exact Subgroup.mem_map_of_mem _ (Subgroup.mem_map_of_mem _ (hES hx))
    have hmem₂ : e (QuotientGroup.mk' (center Q) s) ∈ (T₂ : Subgroup (suzukiGroup 1 K)) := by
      rw [hT₂]
      exact Subgroup.mem_map_of_mem _ (Subgroup.mem_map_of_mem _ hs)
    have hsq : e (QuotientGroup.mk' (center Q) x) ^ 2 = 1 := by
      rw [← map_pow, ← map_pow, hx2, map_one, map_one]
    have hcomm := suzuki_sylow_involution_central hK T₂ _ hmem₁ hsq _ hmem₂
    have hcomm' : QuotientGroup.mk' (center Q) x * QuotientGroup.mk' (center Q) s =
        QuotientGroup.mk' (center Q) s * QuotientGroup.mk' (center Q) x := by
      apply e.injective
      rw [map_mul, map_mul]
      exact hcomm
    have hone : QuotientGroup.mk' (center Q) (s * x * s⁻¹ * x⁻¹) = 1 := by
      simp only [map_mul, map_inv]
      rw [← hcomm']
      group
    exact (QuotientGroup.eq_one_iff (s * x * s⁻¹ * x⁻¹)).mp hone
  have hconj : ∀ s ∈ (S₀ : Subgroup Q), ∀ a ∈ E ⊔ center Q, s * a * s⁻¹ ∈ E ⊔ center Q := by
    intro s hs a ha
    obtain ⟨x, hx, c, hc, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp ha
    obtain ⟨d, hd, hsx⟩ := hkey s hs x hx
    have hsc : s * c * s⁻¹ = c := by
      rw [(Subgroup.mem_center_iff.mp hc) s]
      group
    have hdx : x * d = d * x := (Subgroup.mem_center_iff.mp hd) x
    rw [Subgroup.mem_sup_of_normal_right]
    refine ⟨x, hx, d * c, mul_mem hd hc, ?_⟩
    calc x * (d * c) = (x * d) * c := by group
      _ = (d * x) * c := by rw [hdx]
      _ = (s * x * s⁻¹) * (s * c * s⁻¹) := by rw [hsx, hsc]
      _ = s * (x * c) * s⁻¹ := by group
  have hSA : (S₀ : Subgroup Q) ≤ normalizer ((E ⊔ center Q : Subgroup Q) : Set Q) := by
    intro s hs
    rw [Subgroup.mem_normalizer_iff]
    intro a
    constructor
    · intro ha
      exact hconj s hs a ha
    · intro ha
      have h := hconj s⁻¹ (inv_mem hs) (s * a * s⁻¹) ha
      have h2 : s⁻¹ * (s * a * s⁻¹) * s⁻¹⁻¹ = a := by group
      rw [h2] at h
      exact h
  have hA2 : ∀ a ∈ E ⊔ center Q, a * a = 1 := by
    intro a ha
    obtain ⟨x, hx, c, hc, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp ha
    have hxc : x * c = c * x := (Subgroup.mem_center_iff.mp hc) x
    calc x * c * (x * c) = x * (c * x) * c := by group
      _ = x * (x * c) * c := by rw [← hxc]
      _ = (x * x) * (c * c) := by group
      _ = 1 := by rw [hxx x hx, hZ2 c hc, mul_one]
  have hA8 : 8 ≤ Nat.card (E ⊔ center Q : Subgroup Q) :=
    h8.trans (Subgroup.card_le_of_le le_sup_left)
  exact sylowFourJoined_of_normal_elemAbelian S₀ hSA hA2 hA8

theorem coverLeafSz8_holds :
    CoverLeafSz8 := by
  intro Q _ _ hQ hLie
  have hcard : Nat.card (center Q) ≤ 2 :=
    ((CFSG.GH74.E2.e2ComponentFacts).sz8_cover Q hQ.1 hQ.2.2.1 hLie).resolve_right
      (fun h => h hQ.2.2.2.2.2)
  rcases hLie with ⟨h, -⟩ | ⟨-, h, -⟩ | ⟨-, h, -⟩ | ⟨-, -, -, a, ha, K, _, _, hf, hK, ⟨e⟩⟩
  · exact absurd h (by decide)
  · exact absurd h (by decide)
  · exact absurd h (by decide)
  · obtain rfl : a = 1 := by omega
    exact sylowFourJoined_of_sz8_cover hQ.2.1 hcard hQ.2.2.2.2.1 (by rw [hK]) e

end CFSG.ComponentClassification.Sol76.Sig.GSYard02
