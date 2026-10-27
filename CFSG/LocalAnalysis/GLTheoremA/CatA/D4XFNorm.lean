module

public import CFSG.LocalAnalysis.StandardType.GGSixAutSteinbergTrialityHolds
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeAut
public import CFSG.LocalAnalysis.GLTheoremA.CatA.D4XFIso

public section

namespace CFSG.LocalAnalysis.GLTheoremA.D4XF

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA.S9
  CFSG.ComponentClassification.OuterAutomorphisms

theorem comm_of_card_le_six {G : Type} [Group G] [Finite G] (hG : Nat.card G ≤ 6) {c t : G}
    (hc : orderOf c = 3) (ht : orderOf t = 2) (hct : c * t = t * c) :
    ∀ x y : G, x * y = y * x := by
  have hcomm : Commute c t := hct
  have hg : orderOf (c * t) = 6 := by
    rw [hcomm.orderOf_mul_eq_mul_orderOf_of_coprime (by rw [hc, ht]; norm_num), hc, ht]
  have hle : 6 ≤ Nat.card G := by
    have := Subgroup.card_le_card_group (Subgroup.zpowers (c * t))
    rwa [Nat.card_zpowers, hg] at this
  have htop : Subgroup.zpowers (c * t) = ⊤ := by
    apply Subgroup.eq_top_of_card_eq
    rw [Nat.card_zpowers, hg]
    omega
  intro x y
  have hx : x ∈ Subgroup.zpowers (c * t) := by rw [htop]; exact Subgroup.mem_top x
  have hy : y ∈ Subgroup.zpowers (c * t) := by rw [htop]; exact Subgroup.mem_top y
  obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
  exact ((Commute.refl (c * t)).zpow_zpow m n).eq

theorem comm_of_orderOf_eq_card {G : Type} [Group G] [Finite G] {c : G} (h : orderOf c = Nat.card G) :
    ∀ x y : G, x * y = y * x := by
  have htop : Subgroup.zpowers c = ⊤ := by
    apply Subgroup.eq_top_of_card_eq
    rw [Nat.card_zpowers, h]
  intro x y
  have hx : x ∈ Subgroup.zpowers c := by rw [htop]; exact Subgroup.mem_top x
  have hy : y ∈ Subgroup.zpowers c := by rw [htop]; exact Subgroup.mem_top y
  obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
  exact ((Commute.refl c).zpow_zpow m n).eq

theorem not_comm_of_triality {G : Type} [Group G] {ρ θ : G} (hρ : ρ * ρ = 1) (hrel : ρ * θ * ρ = θ⁻¹)
    (h3 : θ ^ 3 = 1) (h1 : θ ≠ 1) : ¬ ∀ x y : G, x * y = y * x := by
  intro hc
  have h1' : θ * ρ * ρ = θ⁻¹ := by rw [← hc ρ θ]; exact hrel
  rw [mul_assoc, hρ, mul_one] at h1'
  have h2 : θ * θ = 1 := mul_eq_one_iff_eq_inv.2 h1'
  have h4 : θ ^ 3 = θ := by
    calc θ ^ 3 = θ * (θ * θ) := pow_three θ
      _ = θ := by rw [h2, mul_one]
  exact h1 (by rw [← h4, h3])

theorem theta_not_mem_inner_om8 (K₀ : Type) [Field K₀] [Finite K₀] [CharP K₀ 2] :
    (CFSG.StandardType.Triality.theta (K := K₀)) ∉ CFSG.ComponentClassification.OuterAutomorphisms.inner (CFSG.StandardType.Triality.Om8 K₀) := by
  intro hmem
  have h1 := CFSG.StandardType.Triality.theta_pow_mul_mem_inner (K := K₀) 1 (c := 1)
    (Subgroup.one_mem _) (by rw [pow_one, mul_one]; exact hmem)
  have h2 : (CFSG.StandardType.Triality.theta (K := K₀)) = 1 := by
    rw [← pow_one (CFSG.StandardType.Triality.theta (K := K₀))]
    exact h1.1
  apply CFSG.StandardType.Triality.conjAct_ne_theta (K := K₀) 1
  rw [map_one, h2]

theorem d4two_aut_norm_of_out_ne_bot {K : Type} [Group K] [Finite K] (h : catalogIs K S9.isD4two)
    {P S : Subgroup (MulAut K)} (hP : CFSG.Open.IsElemAbelian 3 P) (hPn : ¬ P ≤ inner K)
    (hS2 : IsPGroup 2 S) (hPS : P ≤ Subgroup.normalizer (S : Set (MulAut K)))
    (hT : S.map (QuotientGroup.mk' (inner K) : MulAut K →* MulAut K ⧸ inner K) ≠ ⊥) : False := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Finite (MulAut K) :=
    Finite.of_injective (fun α : MulAut K => (α : K → K)) DFunLike.coe_injective
  have hOut : Nat.card (MulAut K ⧸ inner K) ≤ 6 :=
    CFSG.EvenSmallLie.OmegaEight.card_outer_le_six (statedModel_of_d4two h)
  obtain ⟨-, K₀, _, _, hK₀, ⟨e⟩⟩ := statedModel_of_d4two h
  have hK₀' : Nat.card K₀ = 2 := by rw [hK₀]; norm_num
  haveI : Finite K₀ := Nat.finite_of_card_ne_zero (by omega)
  haveI : Fintype K₀ := Fintype.ofFinite K₀
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP K₀ 2 := charP_of_card_eq_prime_pow (f := 1)
    (by rw [← Nat.card_eq_fintype_card, hK₀']; norm_num)
  have hunits : Nat.card K₀ˣ = 1 := by rw [Nat.card_units, hK₀']
  have hu : Subsingleton K₀ˣ := (Nat.card_eq_one_iff_unique.1 hunits).1
  obtain ⟨Φ⟩ := equiv_triality_of_statedProj hu e
  obtain ⟨θK, hθK⟩ : ∃ θK : MulAut K,
      θK = (MulAut.congr Φ).symm (CFSG.StandardType.Triality.theta (K := K₀)) := ⟨_, rfl⟩
  obtain ⟨ρK, hρK⟩ : ∃ ρK : MulAut K,
      ρK = (MulAut.congr Φ).symm (CFSG.StandardType.AutOm.plusRefl (K := K₀) (n := 4) (by norm_num)) :=
    ⟨_, rfl⟩
  have hθ3 : θK ^ 3 = 1 := by
    rw [hθK, ← map_pow, CFSG.StandardType.Triality.theta_cube, map_one]
  have hρρ : ρK * ρK = 1 := by
    rw [hρK, ← map_mul, CFSG.StandardType.AutOm.plusRefl_mul_self, map_one]
  have hrel : ρK * θK * ρK = θK⁻¹ := by
    rw [hρK, hθK, ← map_mul, ← map_mul, CFSG.StandardType.Triality.plusRefl_theta_plusRefl, map_inv]
  have hθout : θK ∉ inner K := by
    intro hmem
    apply theta_not_mem_inner_om8 K₀
    have hm : (CFSG.StandardType.Triality.theta (K := K₀)) ∈
        (inner K).map (MulAut.congr Φ).toMonoidHom := by
      refine Subgroup.mem_map.2 ⟨θK, hmem, ?_⟩
      rw [hθK]
      exact (MulAut.congr Φ).apply_symm_apply _
    rwa [inner_map_congr Φ] at hm
  let mk : MulAut K →* MulAut K ⧸ inner K := QuotientGroup.mk' (inner K)
  have hnc : ¬ ∀ x y : MulAut K ⧸ inner K, x * y = y * x := by
    apply not_comm_of_triality (ρ := mk ρK) (θ := mk θK)
    · rw [← map_mul, hρρ, map_one]
    · rw [← map_mul, ← map_mul, hrel, map_inv]
    · rw [← map_pow, hθ3, map_one]
    · intro h
      exact hθout ((QuotientGroup.eq_one_iff θK).1 h)
  obtain ⟨α, hαP, hαn⟩ := Set.not_subset.1 hPn
  have hα3 : α ^ 3 = 1 := hP.2 α hαP
  have hαout : mk α ≠ 1 := fun h => hαn ((QuotientGroup.eq_one_iff α).1 h)
  have hordα : orderOf (mk α) = 3 := orderOf_eq_prime (by rw [← map_pow, hα3, map_one]) hαout
  set T : Subgroup (MulAut K ⧸ inner K) := S.map mk with hTdef
  have hT2 : IsPGroup 2 T := hS2.map mk
  have hTα : ∀ x ∈ T, mk α * x * (mk α)⁻¹ ∈ T := by
    intro x hx
    obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.1 hx
    have hαs : α * s * α⁻¹ ∈ S := (Subgroup.mem_normalizer_iff.1 (hPS hαP) s).1 hs
    have : mk α * mk s * (mk α)⁻¹ = mk (α * s * α⁻¹) := by
      rw [map_mul, map_mul, map_inv]
    rw [this]
    exact Subgroup.mem_map_of_mem mk hαs
  have hdiv : Nat.card T ∣ Nat.card (MulAut K ⧸ inner K) := Subgroup.card_subgroup_dvd_card T
  have h3dvd : 3 ∣ Nat.card (MulAut K ⧸ inner K) := hordα ▸ orderOf_dvd_natCard (mk α)
  have hOut6 : Nat.card (MulAut K ⧸ inner K) = 6 := by
    have hpos : 0 < Nat.card (MulAut K ⧸ inner K) := Nat.card_pos
    obtain ⟨m, hm⟩ := h3dvd
    have hm2 : m ≤ 2 := by omega
    interval_cases m
    · omega
    · exfalso
      exact hnc (comm_of_orderOf_eq_card (c := mk α) (by rw [hordα]; omega))
    · omega
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 hT2
  have hT1card : 1 < Nat.card T := (Subgroup.one_lt_card_iff_ne_bot T).2 hT
  have hn1 : n = 1 := by
    have hdiv6 : 2 ^ n ∣ 6 := by
      rw [← hn, ← hOut6]
      exact hdiv
    have hnle : n ≤ 1 := by
      by_contra hcon
      push Not at hcon
      have h4 : 2 ^ 2 ∣ 6 := (pow_dvd_pow 2 hcon).trans hdiv6
      norm_num at h4
    interval_cases n
    · rw [hn] at hT1card
      norm_num at hT1card
    · rfl
  have hTcard : Nat.card T = 2 := by rw [hn, hn1]; norm_num
  obtain ⟨t', ht'⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hT
  have ht2 : (t' : MulAut K ⧸ inner K) ^ 2 = 1 := by
    have hd := orderOf_dvd_natCard t'
    rw [hTcard] at hd
    have : t' ^ 2 = 1 := orderOf_dvd_iff_pow_eq_one.1 hd
    simpa using congrArg Subtype.val this
  set t : MulAut K ⧸ inner K := (t' : MulAut K ⧸ inner K) with htdef
  have ht : t ∈ T := t'.2
  have ht1 : t ≠ 1 := fun h => ht' (Subtype.ext h)
  have hordt : orderOf t = 2 := orderOf_eq_prime ht2 ht1
  have hZT : Subgroup.zpowers t = T :=
    Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 ht) (by rw [Nat.card_zpowers, hordt, hTcard])
  have hTelem : ∀ x ∈ T, x = 1 ∨ x = t := by
    intro x hx
    have hx' : x ∈ Subgroup.zpowers t := by rw [hZT]; exact hx
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx'
    have h2z : t ^ (2 : ℤ) = 1 := by simpa using ht2
    rw [zpow_eq_zpow_emod k h2z]
    have hk : k % 2 = 0 ∨ k % 2 = 1 := by omega
    rcases hk with hk | hk
    · left; rw [hk]; simp
    · right; rw [hk]; simp
  have hconj : mk α * t * (mk α)⁻¹ = t := by
    rcases hTelem _ (hTα t ht) with h | h
    · exfalso
      apply ht1
      calc t = (mk α)⁻¹ * (mk α * t * (mk α)⁻¹) * mk α := by group
        _ = (mk α)⁻¹ * 1 * mk α := by rw [h]
        _ = 1 := by group
    · exact h
  have hcommOut : mk α * t = t * mk α := mul_inv_eq_iff_eq_mul.1 hconj
  exact hnc (comm_of_card_le_six (by omega) hordα hordt hcommOut)

end CFSG.LocalAnalysis.GLTheoremA.D4XF
