module

public import CFSG.GH74.GLS.LU.Local.FiveL66m
public import CFSG.GH74.GLS.LU.Local.FiveS4

public section

open Subgroup CFSG CFSG.GH74.GLS.LU.Local CFSG.GH74.GLS CFSG.GH74.GLS.LU CFSG.Blueprint CFSG.Assembly.LowTwoRank
open scoped MatrixGroups

namespace CFSG.GH74.GLS.LU.Local.Five

section TwoGroups

variable {G : Type} [Group G]

theorem isPGroup_zpowers_of_pow_eq_one {g : G} {k : ℕ} (h : g ^ (2 ^ k) = 1) :
    IsPGroup 2 ↥(zpowers g) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 : orderOf g ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one h
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h1
  exact IsPGroup.of_card (n := j) (by rw [Nat.card_zpowers, hj])

theorem isPGroup_zpowers_of_mem {Q : Subgroup G} (hQ : IsPGroup 2 ↥Q) {n : G} (hn : n ∈ Q) :
    IsPGroup 2 ↥(zpowers n) := by
  obtain ⟨k, hk⟩ := hQ ⟨n, hn⟩
  exact isPGroup_zpowers_of_pow_eq_one (k := k) (by simpa using congrArg Subtype.val hk)

theorem z4z4_card : Nat.card Z4Z4 = 16 := by
  rw [Nat.card_eq_fintype_card]
  decide

end TwoGroups

section NQuot

variable {G : Type} [Group G] [Finite G] {p f : ℕ} {z : G} {S : Sylow 2 G} {K₁ K₂ H : Subgroup G}
  {t u w₁ : G} {Gs : Type} [Group Gs] {z' t' u' : Gs} {S' : Sylow 2 Gs} {K₁' K₂' : Subgroup Gs}
  {ψ : ↥(Cz z) ≃* ↥(Cz z')}

omit [Finite G] in
theorem Hn_normal (hNH : ∀ n ∈ NN z u, cjL n H = H) : (H.subgroupOf (NN z u)).Normal :=
  ⟨fun n hn g => by
    have h1 : (g : G) * n * (g : G)⁻¹ ∈ cjL (g : G) H := mem_cjL_self hn
    rw [hNH g.1 g.2] at h1
    exact h1⟩

omit [Finite G] in
theorem Pn_normal : ((PP z u).subgroupOf (NN z u)).Normal :=
  ⟨fun _ hn g => conj_mem_PP g.2 hn⟩

omit [Finite G] in
theorem H_le_PP (b66 : Five66W z t u K₁ K₂ H w₁) : H ≤ PP z u :=
  fun h hh => mem_PP.mpr (b66.H_cent h hh)

omit [Finite G] in
theorem PP_le_NN : PP z u ≤ NN z u := Subgroup.centralizer_le_normalizer _

theorem ModelPic.N_quot (c : FiveCtx G p f z S K₁ K₂ t u)
    (pic : ModelPic z t u K₁ K₂ c.t_mem_Cz c.u_mem_Cz z' S' K₁' K₂' t' u' ψ)
    (b66 : Five66W z t u K₁ K₂ H w₁) (hNH : ∀ n ∈ NN z u, cjL n H = H) {x : G}
    (hxz : x * z * x⁻¹ = u) (hxu : x * u * x⁻¹ = z * u) :
    ∃ _ : (H.subgroupOf (NN z u)).Normal,
      Nonempty (↥(NN z u) ⧸ H.subgroupOf (NN z u) ≃* Equiv.Perm (Fin 4)) := by
  classical
  have hHn : (H.subgroupOf (NN z u)).Normal := Hn_normal hNH
  refine ⟨hHn, ?_⟩
  have hz2 : z * z = 1 := c.hs.z_sq
  have hu2 : u * u = 1 := c.hs.u_sq
  have hzu : z * u = u * z := c.hs.zu_comm
  have hz1 : z ≠ 1 := c.z_ne_one
  have hu1 : u ≠ 1 := by
    intro h
    have := c.hs.u_ord
    rw [h, orderOf_one] at this
    omega
  have huz : u ≠ z := c.hs.u_ne
  have hwz : w₁ * z * w₁⁻¹ = z := by
    calc w₁ * z * w₁⁻¹ = (z * w₁) * w₁⁻¹ := by rw [c.hc.cz₁ b66.w₁_mem]
      _ = z := by group
  obtain ⟨hPnorm, hPsq⟩ := pic.PP_facts b66
  have hHN : H ≤ NN z u := (H_le_PP b66).trans PP_le_NN
  have hNcard : Nat.card ↥(NN z u) = 384 := by
    rw [card_NN_eq_six_mul_card_PP hz2 hu2 hzu hz1 hu1 huz hwz b66.w₁_u hxz hxu, pic.card_PP]
  have hHcard : Nat.card ↥H = 16 := by
    rw [Nat.card_congr b66.H_iso.some.toEquiv, z4z4_card]
  have hHncard : Nat.card ↥(H.subgroupOf (NN z u)) = 16 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHN).toEquiv, hHcard]
  have hMcard : Nat.card (↥(NN z u) ⧸ H.subgroupOf (NN z u)) = 24 := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (H.subgroupOf (NN z u))
    rw [hNcard, hHncard] at h1
    omega
  let π : ↥(NN z u) →* ↥(NN z u) ⧸ H.subgroupOf (NN z u) := QuotientGroup.mk' _
  have hπs : Function.Surjective π := QuotientGroup.mk_surjective
  have hPn : ((PP z u).subgroupOf (NN z u)).Normal := Pn_normal
  have hVn : (((PP z u).subgroupOf (NN z u)).map π).Normal := Subgroup.Normal.map hPn π hπs
  have hPncard : Nat.card ↥((PP z u).subgroupOf (NN z u)) = 64 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe PP_le_NN).toEquiv, pic.card_PP]
  have hidx : (((PP z u).subgroupOf (NN z u)).map π).index = 6 := by
    have hker : π.ker ≤ (PP z u).subgroupOf (NN z u) := by
      rw [QuotientGroup.ker_mk']
      exact Subgroup.subgroupOf_mono (NN z u) (H_le_PP b66)
    rw [Subgroup.index_map_eq _ hπs hker]
    have := Subgroup.index_mul_card ((PP z u).subgroupOf (NN z u))
    rw [hPncard, hNcard] at this
    omega
  have hVcard : Nat.card ↥(((PP z u).subgroupOf (NN z u)).map π) = 4 := by
    have := Subgroup.index_mul_card (((PP z u).subgroupOf (NN z u)).map π)
    rw [hidx, hMcard] at this
    omega
  have hV2 : ∀ v ∈ ((PP z u).subgroupOf (NN z u)).map π, v * v = 1 := by
    rintro _ ⟨q, hq, rfl⟩
    rw [← map_mul]
    exact (QuotientGroup.eq_one_iff _).mpr (hPsq q.1 hq)
  have hC : ∀ m : ↥(NN z u) ⧸ H.subgroupOf (NN z u),
      (∀ v ∈ ((PP z u).subgroupOf (NN z u)).map π, m * v = v * m) →
        m ∈ ((PP z u).subgroupOf (NN z u)).map π := by
    intro m hm
    obtain ⟨n, rfl⟩ := QuotientGroup.mk_surjective m
    have hcent : CentPH z u H n.1 := by
      intro q hq
      have hqN : q ∈ NN z u := PP_le_NN hq
      have hqV : (QuotientGroup.mk (⟨q, hqN⟩ : ↥(NN z u)) : ↥(NN z u) ⧸ H.subgroupOf (NN z u)) ∈
          ((PP z u).subgroupOf (NN z u)).map π := ⟨⟨q, hqN⟩, hq, rfl⟩
      have hcomm := hm _ hqV
      have h1 : (QuotientGroup.mk (n * ⟨q, hqN⟩ * n⁻¹ * ⟨q, hqN⟩⁻¹ : ↥(NN z u)) :
          ↥(NN z u) ⧸ H.subgroupOf (NN z u)) = 1 := by
        simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
        rw [hcomm]
        group
      have h2 := (QuotientGroup.eq_one_iff (N := H.subgroupOf (NN z u))
        (n * ⟨q, hqN⟩ * n⁻¹ * ⟨q, hqN⟩⁻¹)).mp h1
      exact h2
    have hnP : n.1 ∈ PP z u := pic.centPH_imp_PP c b66 hNH hxz hxu n.2 hcent
    exact ⟨n, hnP, rfl⟩
  exact exists_mulEquiv_perm_four_of_V4 (((PP z u).subgroupOf (NN z u)).map π) hMcard hVcard hV2 hC

end NQuot

section NOrd

variable {G : Type} [Group G] [Finite G] {p f : ℕ} {z : G} {S : Sylow 2 G} {K₁ K₂ H : Subgroup G}
  {t u w₁ : G} {Gs : Type} [Group Gs] {z' t' u' : Gs} {S' : Sylow 2 Gs} {K₁' K₂' : Subgroup Gs}
  {ψ : ↥(Cz z) ≃* ↥(Cz z')}

theorem ModelPic.N_ord (c : FiveCtx G p f z S K₁ K₂ t u)
    (pic : ModelPic z t u K₁ K₂ c.t_mem_Cz c.u_mem_Cz z' S' K₁' K₂' t' u' ψ)
    (b66 : Five66W z t u K₁ K₂ H w₁) {x : G} (hxz : x * z * x⁻¹ = u) (hxu : x * u * x⁻¹ = z * u)
    [(H.subgroupOf (NN z u)).Normal]
    (φ : ↥(NN z u) ⧸ H.subgroupOf (NN z u) ≃* Equiv.Perm (Fin 4)) :
    ∀ n ∈ NN z u, orderOf n = 3 ∨ IsPGroup 2 ↥(zpowers n) := by
  classical
  have hz2 : z * z = 1 := c.hs.z_sq
  have hu2 : u * u = 1 := c.hs.u_sq
  have hzu : z * u = u * z := c.hs.zu_comm
  have hz1 : z ≠ 1 := c.z_ne_one
  have hu1 : u ≠ 1 := by
    intro h
    have := c.hs.u_ord
    rw [h, orderOf_one] at this
    omega
  have huz : u ≠ z := c.hs.u_ne
  have hwz : w₁ * z * w₁⁻¹ = z := by
    calc w₁ * z * w₁⁻¹ = (z * w₁) * w₁⁻¹ := by rw [c.hc.cz₁ b66.w₁_mem]
      _ = z := by group
  have hker := ker_rhoUSharp hz1 hu1
  have hT : Nat.card (USharp z u) = 3 := card_USharp hz2 hu2 hzu hz1 hu1 huz
  have hPtwo : IsPGroup 2 ↥(PP z u) :=
    IsPGroup.of_card (n := 6) (by rw [pic.card_PP]; norm_num)
  have hHcard : Nat.card ↥H = 16 := by
    rw [Nat.card_congr b66.H_iso.some.toEquiv, z4z4_card]
  have hH2 : IsPGroup 2 ↥H := IsPGroup.of_card (n := 4) (by rw [hHcard]; norm_num)
  intro n hn
  by_cases hnP : n ∈ PP z u
  · right
    exact isPGroup_zpowers_of_mem hPtwo hnP
  have hρn : rhoUSharp z u ⟨n, hn⟩ ≠ 1 := by
    intro h
    apply hnP
    have h1 : (⟨n, hn⟩ : ↥(NN z u)) ∈ (rhoUSharp z u).ker := h
    rw [hker] at h1
    exact h1
  rcases perm4_pow_three_or_four (φ (QuotientGroup.mk ⟨n, hn⟩)) with h3 | h4
  ·
    have hn3H : n ^ 3 ∈ H := by
      have h1 : (QuotientGroup.mk (⟨n, hn⟩ ^ 3 : ↥(NN z u)) : ↥(NN z u) ⧸ H.subgroupOf (NN z u)) =
          1 := by
        apply φ.injective
        rw [QuotientGroup.mk_pow, map_pow, map_one]
        exact h3
      have h2 := (QuotientGroup.eq_one_iff (N := H.subgroupOf (NN z u)) (⟨n, hn⟩ ^ 3)).mp h1
      exact h2
    by_cases hn31 : n ^ 3 = 1
    · left
      have hn1 : n ≠ 1 := fun h => hnP (h ▸ (PP z u).one_mem)
      have hdvd : orderOf n ∣ 3 := orderOf_dvd_of_pow_eq_one hn31
      rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
      · exact absurd (orderOf_eq_one_iff.mp h) hn1
      · exact h
    · exfalso
      obtain ⟨a, ha⟩ := (IsPGroup.iff_orderOf.mp hH2) ⟨n ^ 3, hn3H⟩
      have hord : orderOf (n ^ 3) = 2 ^ a := by
        rw [← ha]
        exact (Subgroup.orderOf_mk (n ^ 3) hn3H).symm
      have ha0 : a ≠ 0 := by
        rintro rfl
        rw [pow_zero] at hord
        exact hn31 (orderOf_eq_one_iff.mp hord)
      have h2dvd : 2 ∣ Nat.card ↥(zpowers (n ^ 3)) := by
        rw [Nat.card_zpowers, hord]
        exact dvd_pow_self 2 ha0
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      obtain ⟨y₀, hy₀⟩ := exists_prime_orderOf_dvd_card' 2 h2dvd
      obtain ⟨y, hyz⟩ := y₀
      have hyord : orderOf y = 2 := by
        have := Subgroup.orderOf_coe (⟨y, hyz⟩ : ↥(zpowers (n ^ 3)))
        exact this.trans hy₀
      have hyH : y ∈ H := (Subgroup.zpowers_le.mpr hn3H) hyz
      have hy2 : y * y = 1 := by
        have := pow_orderOf_eq_one y
        rwa [hyord, pow_two] at this
      have hy1 : y ≠ 1 := by
        intro h
        rw [h, orderOf_one] at hyord
        omega
      have hyU : y ∈ UU z u :=
        sq_eq_one_mem_UU hz2 hu2 hzu hz1 hu1 huz b66.z_mem b66.u_mem b66.H_iso y hyH hy2
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hyz
      have hc : Commute n y := by
        rw [← hk]
        exact ((Commute.refl n).pow_right 3).zpow_right k
      have hcomm : n * y * n⁻¹ = y := by rw [hc.eq]; group
      have hρ3 : rhoUSharp z u ⟨n, hn⟩ ^ 3 = 1 := by
        rw [← map_pow]
        have h1 : (⟨n, hn⟩ : ↥(NN z u)) ^ 3 ∈ (rhoUSharp z u).ker := by
          rw [hker]
          exact H_le_PP b66 hn3H
        exact h1
      apply perm3_no_fixed hT hρ3 hρn ⟨y, hyU, hy1⟩
      exact Subtype.ext ((rhoUSharp_apply (⟨n, hn⟩ : ↥(NN z u)) (⟨y, hyU, hy1⟩ : USharp z u)).trans hcomm)
  ·
    right
    have hn4H : n ^ 4 ∈ H := by
      have h1 : (QuotientGroup.mk (⟨n, hn⟩ ^ 4 : ↥(NN z u)) : ↥(NN z u) ⧸ H.subgroupOf (NN z u)) =
          1 := by
        apply φ.injective
        rw [QuotientGroup.mk_pow, map_pow, map_one]
        exact h4
      have h2 := (QuotientGroup.eq_one_iff (N := H.subgroupOf (NN z u)) (⟨n, hn⟩ ^ 4)).mp h1
      exact h2
    obtain ⟨k, hk⟩ := hH2 ⟨n ^ 4, hn4H⟩
    refine isPGroup_zpowers_of_pow_eq_one (k := k + 2) ?_
    have hk' : (n ^ 4) ^ (2 ^ k) = 1 := by simpa using congrArg Subtype.val hk
    calc n ^ (2 ^ (k + 2)) = (n ^ 4) ^ (2 ^ k) := by
          rw [← pow_mul]
          congr 1
          rw [pow_add]
          ring
      _ = 1 := hk'

end NOrd

end CFSG.GH74.GLS.LU.Local.Five
