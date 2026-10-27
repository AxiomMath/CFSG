module

public import CFSG.LocalAnalysis.RankThreeTheoremC.D2PairRes3Auto
import CFSG.LocalAnalysis.AGLEmbedding.LinTwoBorelAux
import CFSG.LocalAnalysis.AGLEmbedding.LinTwoTorus
import CFSG.LocalAnalysis.ComponentInitial.FieldNineAlternatingSix

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.AGLEmbedding CFSG.AGLEmbeddingD2 CFSG.LocalAnalysis.ComponentInitial

theorem exists_unit_sq_ne_intCast :
    ∃ μ : (GaloisField 3 2)ˣ, ∀ k : ℤ, ((μ : GaloisField 3 2)) ^ 2 ≠ (k : GaloisField 3 2) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨μ, hμ⟩ := IsCyclic.exists_generator (α := (GaloisField 3 2)ˣ)
  have hcard : Nat.card (GaloisField 3 2) = 9 := by
    rw [GaloisField.card 3 2 (by norm_num)]
    norm_num
  have hμ8 : orderOf μ = 8 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hμ]
    rw [Nat.card_units, hcard]
  refine ⟨μ, fun k hk => ?_⟩
  have hfrob : ((k : GaloisField 3 2)) ^ 3 = (k : GaloisField 3 2) := by
    have := map_intCast (frobenius (GaloisField 3 2) 3) k
    rwa [frobenius_def] at this
  have h6 : ((μ : GaloisField 3 2)) ^ 6 = ((μ : GaloisField 3 2)) ^ 2 := by
    calc ((μ : GaloisField 3 2)) ^ 6 = (((μ : GaloisField 3 2)) ^ 2) ^ 3 := by ring
      _ = ((μ : GaloisField 3 2)) ^ 2 := by rw [hk, hfrob]
  have h4 : μ ^ 4 = 1 := by
    have h6' : μ ^ 6 = μ ^ 2 := Units.ext (by simpa using h6)
    have : μ ^ 2 * μ ^ 4 = μ ^ 2 * 1 := by rw [← pow_add, mul_one]; exact h6'
    exact mul_left_cancel this
  have := orderOf_dvd_of_pow_eq_one h4
  rw [hμ8] at this
  omega

theorem automizerIrreducible_of_psl2_nine {X : Type} [Group X] [Finite X] {R : Sylow 3 X}
    {A X₀ K : Subgroup X} (h : D2AlmostSimple 3 X R A X₀ K) (e : K ≃* PSL2GF 3 2) :
    AutomizerIrreducible 3 (R : Subgroup X) X₀ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hRA : (R : Subgroup X) = A := (h.sylow_inf_eq_of_psl2 e).2
  have hNA : Subgroup.normalizer (A : Set X) = X₀ := h.normalizer_A_eq_of_psl2 e
  obtain ⟨ψ, hψinj, hψU, hψc⟩ := exists_torus_param_of_mulEquiv_psl2GF h.ne_two (by norm_num) e A
    (h.A_le_of_psl2 e) h.card_A
  obtain ⟨μ, hμ⟩ := exists_unit_sq_ne_intCast
  intro Y hYR hY3
  obtain ⟨c, -, hc⟩ := hψc μ
  have hcN : c ∈ Subgroup.normalizer (A : Set X) := by
    have := mem_normalizer_range_of_torus ψ μ.ne_zero hc
    rwa [hψU] at this
  refine ⟨c, ⟨hNA ▸ hcN, hRA ▸ hcN⟩, fun hcY => ?_⟩
  have hYA : Y ≤ ψ.range := hψU ▸ hRA ▸ hYR
  set Y' : Subgroup (Multiplicative (GaloisField 3 2)) := Y.comap ψ with hY'
  have hYmap : Y'.map ψ = Y := by
    rw [hY', Subgroup.map_comap_eq]
    exact inf_eq_right.mpr hYA
  have hY'3 : Nat.card Y' = 3 := by
    rw [← Subgroup.card_map_of_injective hψinj, hYmap, hY3]
  have hY'ne : Y' ≠ ⊥ := by
    intro hb
    rw [hb, Subgroup.card_bot] at hY'3
    omega
  obtain ⟨⟨a, haY'⟩, ha1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hY'ne
  have ha1' : a ≠ 1 := fun h1 => ha1 (Subtype.ext h1)
  have haY : ψ a ∈ Y := hYmap ▸ Subgroup.mem_map_of_mem ψ haY'
  have hconj :
      ψ (Multiplicative.ofAdd ((μ : GaloisField 3 2) ^ 2 * Multiplicative.toAdd a)) ∈ Y := by
    rw [← hc a]
    exact (Subgroup.mem_normalizer_iff.mp hcY (ψ a)).mp haY
  have hbY' : Multiplicative.ofAdd ((μ : GaloisField 3 2) ^ 2 * Multiplicative.toAdd a) ∈ Y' :=
    hconj
  have hY'cyc : Y' = Subgroup.zpowers a := by
    have hord : orderOf a = 3 := by
      have hdvd : orderOf a ∣ 3 := by
        have h1 := Subgroup.orderOf_dvd_natCard Y' haY'
        rwa [hY'3] at h1
      rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3
      · exact absurd (orderOf_eq_one_iff.mp h1) ha1'
      · exact h3
    refine (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr haY') ?_).symm
    rw [Nat.card_zpowers, hord, hY'3]
  rw [hY'cyc] at hbY'
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hbY'
  have hk' := congrArg Multiplicative.toAdd hk
  rw [toAdd_zpow, toAdd_ofAdd, zsmul_eq_mul] at hk'
  have hx : Multiplicative.toAdd a ≠ 0 := by
    intro h0
    exact ha1' (Multiplicative.toAdd.injective (by simpa using h0))
  exact hμ k (mul_right_cancel₀ hx hk'.symm)

theorem sylowNine_of_psl2_nine {X : Type} [Group X] [Finite X] {R : Sylow 3 X}
    {A X₀ K : Subgroup X} (h : D2AlmostSimple 3 X R A X₀ K) (e : K ≃* PSL2GF 3 2) :
    Nat.card (R : Subgroup X) = 3 ^ 2 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rw [(h.sylow_inf_eq_of_psl2 e).2]
  exact h.card_A

theorem d2AutomizerAt_altSix : D2AutomizerAt (.alternating 6 (by norm_num)) fun p => p = 3 := by
  intro X _ _ p hp3 R A X₀ K hK ⟨e⟩
  subst hp3
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fintype (GaloisField 3 2) := Fintype.ofFinite _
  have hcard : Fintype.card (GaloisField 3 2) = 9 := by
    rw [Fintype.card_eq_nat_card, GaloisField.card 3 2 (by norm_num)]
    norm_num
  obtain ⟨e'⟩ :=
    unique_field_nine_projective_linear_alternating_six_isomorphism (GaloisField 3 2) hcard
  exact automizerIrreducible_of_psl2_nine hK (e.trans e'.symm)

theorem d2SylowNineAt_altSix : D2SylowNineAt (.alternating 6 (by norm_num)) fun p => p = 3 := by
  intro X _ _ p hp3 R A X₀ K hK ⟨e⟩
  subst hp3
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fintype (GaloisField 3 2) := Fintype.ofFinite _
  have hcard : Fintype.card (GaloisField 3 2) = 9 := by
    rw [Fintype.card_eq_nat_card, GaloisField.card 3 2 (by norm_num)]
    norm_num
  obtain ⟨e'⟩ :=
    unique_field_nine_projective_linear_alternating_six_isomorphism (GaloisField 3 2) hcard
  exact sylowNine_of_psl2_nine hK (e.trans e'.symm)

end CFSG.LocalAnalysis.RankThreeTheoremC
