module

public import CFSG.GH74.Generic.S3.Local

public section

namespace CFSG.GH74.Generic.S3

open CFSG CFSG.GH74 CFSG.GH74.Generic CFSG.Blueprint CFSG.ABGLocalTools CFSG.Assembly.LowTwoRank Subgroup

theorem IsCompC.isQuasisimple {G : Type} [Group G] {I : Subgroup G} {u : G} (h : IsCompC I u) :
    IsQuasisimple ↥I :=
  LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe h.1) h.2.1

theorem IsNormCompC.conj {G : Type} [Group G] {I : Subgroup G} {u : G} (h : IsNormCompC I u) :
    ∀ c ∈ centralizer ({u} : Set G), ∀ i ∈ I, c * i * c⁻¹ ∈ I :=
  normIn_of_normal h.1.1 h.2

theorem IsNormCompC.le_normalizer {G : Type} [Group G] {I : Subgroup G} {u : G}
    (h : IsNormCompC I u) : centralizer ({u} : Set G) ≤ normalizer (I : Set G) := by
  intro c hc
  rw [mem_normalizer_iff]
  intro i
  refine ⟨fun hi => h.conj c hc i hi, fun hi => ?_⟩
  have := h.conj c⁻¹ ((centralizer ({u} : Set G)).inv_mem hc) _ hi
  have e : c⁻¹ * (c * i * c⁻¹) * c⁻¹⁻¹ = i := by group
  rwa [e] at this

theorem card_le_of_isPGroup_le {G : Type} [Group G] [Finite G] {P K S : Subgroup G}
    (hP : IsPGroup 2 ↥P) (hPK : P ≤ K) (hS : IsSylowOf 2 S K) : Nat.card ↥P ≤ Nat.card ↥S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨m, hm⟩ := hP.exists_card_eq
  have hdvd : 2 ^ m ∣ Nat.card ↥K := hm ▸ Subgroup.card_dvd_of_le hPK
  have hle : m ≤ (Nat.card ↥K).factorization 2 :=
    (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two Nat.card_pos.ne').1 hdvd
  rw [hm, hS.card_eq]
  exact Nat.pow_le_pow_right (by norm_num) hle

namespace Nbhd3

variable {G : Type} [Group G] [Finite G] {t t' : StatedLieTag} {p f : ℕ} {x y : G}
  {Iw Iv Ivw T : Subgroup G} (h : Nbhd3 G t t' p f x y Iw Iv Ivw T)

include h

theorem T_le : T ≤ centralizer ({x} : Set G) := h.T_sylow.le

theorem T_pGroup : IsPGroup 2 ↥T := h.T_sylow.isPGroup

theorem Iw_le : Iw ≤ centralizer ({x} : Set G) := h.comp_w.1.1

theorem Iw_conj : ∀ c ∈ centralizer ({x} : Set G), ∀ i ∈ Iw, c * i * c⁻¹ ∈ Iw :=
  normIn_of_normal h.Iw_le h.comp_w.2

theorem T_conj_Iw : ∀ s ∈ T, ∀ i ∈ Iw, s * i * s⁻¹ ∈ Iw := fun s hs i hi =>
  h.Iw_conj s (h.T_le hs) i hi

theorem x_comm_Iw : ∀ i ∈ Iw, i * x = x * i := fun _ hi =>
  mem_centralizer_singleton_iff.1 (h.Iw_le hi)

theorem T_conj_R : ∀ s ∈ T, ∀ r ∈ T ⊓ Iw, s * r * s⁻¹ ∈ T ⊓ Iw := fun s hs r hr =>
  ⟨T.mul_mem (T.mul_mem hs hr.1) (T.inv_mem hs), h.T_conj_Iw s hs r hr.2⟩

theorem T_conj_Q : ∀ s ∈ T, ∀ q ∈ T ⊓ centralizer (Iw : Set G), s * q * s⁻¹ ∈ T ⊓ centralizer (Iw : Set G) := by
  intro s hs q hq
  refine ⟨T.mul_mem (T.mul_mem hs hq.1) (T.inv_mem hs), ?_⟩
  apply mem_centralizer_iff.2
  intro i hi
  have hi' : s⁻¹ * i * s ∈ Iw := by
    have := h.T_conj_Iw s⁻¹ (T.inv_mem hs) i hi
    simpa using this
  have hq' : (s⁻¹ * i * s) * q = q * (s⁻¹ * i * s) := mem_centralizer_iff.1 hq.2 _ hi'
  calc i * (s * q * s⁻¹) = s * ((s⁻¹ * i * s) * q) * s⁻¹ := by group
    _ = s * (q * (s⁻¹ * i * s)) * s⁻¹ := by rw [hq']
    _ = s * q * s⁻¹ * i := by group

theorem centralizer_le_normalizer : centralizer ({x} : Set G) ≤ normalizer (Iw : Set G) := by
  intro c hc
  rw [mem_normalizer_iff]
  intro i
  refine ⟨fun hi => h.Iw_conj c hc i hi, fun hi => ?_⟩
  have := h.Iw_conj c⁻¹ ((centralizer ({x} : Set G)).inv_mem hc) _ hi
  have e : c⁻¹ * (c * i * c⁻¹) * c⁻¹⁻¹ = i := by group
  rwa [e] at this

theorem R_sylow : IsSylowOf 2 (T ⊓ Iw) Iw := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact h.T_sylow.inf_of_le_normalizer h.Iw_le h.centralizer_le_normalizer

theorem x_Q : x ∈ T ⊓ centralizer (Iw : Set G) := by
  refine ⟨h.x_T, ?_⟩
  apply mem_centralizer_iff.2
  intro i hi
  exact h.x_comm_Iw i hi

theorem x_ne_one : x ≠ 1 := fun hx => by
  have := h.x_inv
  rw [hx, orderOf_one] at this
  omega

theorem x_mul_self : x * x = 1 := by
  have := pow_orderOf_eq_one x
  rwa [h.x_inv, pow_two] at this

theorem y_ne_one : y ≠ 1 := fun hy => by
  have := h.y_inv
  rw [hy, orderOf_one] at this
  omega

theorem y_mul_self : y * y = 1 := by
  have := pow_orderOf_eq_one y
  rwa [h.y_inv, pow_two] at this

theorem Q_involution : ∀ a ∈ T ⊓ centralizer (Iw : Set G), a * a = 1 → a = 1 ∨ a = x := by
  have hne : T ⊓ centralizer (Iw : Set G) ≠ ⊥ := fun hb => by
    have := h.x_Q
    rw [hb, Subgroup.mem_bot] at this
    exact h.x_ne_one this
  obtain ⟨z, hz, hzz, hz1, hzu⟩ := unique_involution_of_noCommInv
    (h.T_pGroup.to_inf_left (K := centralizer (Iw : Set G))) hne h.Q_rank
  have hxz : x = z := by
    rcases hzu x h.x_Q h.x_mul_self with h1 | h1
    · exact absurd h1 h.x_ne_one
    · exact h1
  intro a ha haa
  rcases hzu a ha haa with h1 | h1
  · exact Or.inl h1
  · exact Or.inr (h1.trans hxz.symm)

theorem y_comm_T : ∀ s ∈ T, s * y = y * s := by
  intro s hs
  have hRs : s * y * s⁻¹ ∈ T ⊓ Iw := h.T_conj_R s hs y h.y_R
  have hcent : ∀ r ∈ T ⊓ Iw, r * (s * y * s⁻¹) = (s * y * s⁻¹) * r := by
    intro r hr
    have hr' : s⁻¹ * r * s ∈ T ⊓ Iw := by
      have := h.T_conj_R s⁻¹ (T.inv_mem hs) r hr
      simpa using this
    have := h.y_central _ hr'
    calc r * (s * y * s⁻¹) = s * ((s⁻¹ * r * s) * y) * s⁻¹ := by group
      _ = s * (y * (s⁻¹ * r * s)) * s⁻¹ := by rw [this]
      _ = (s * y * s⁻¹) * r := by group
  have hsq : (s * y * s⁻¹) * (s * y * s⁻¹) = 1 := by
    calc (s * y * s⁻¹) * (s * y * s⁻¹) = s * (y * y) * s⁻¹ := by group
      _ = 1 := by rw [h.y_mul_self]; group
  rcases h.y_unique _ hRs hcent hsq with h1 | h1
  · exfalso
    apply h.y_ne_one
    have : y = s⁻¹ * (s * y * s⁻¹) * s := by group
    rw [this, h1]
    group
  · calc s * y = (s * y * s⁻¹) * s := by group
      _ = y * s := by rw [h1]

theorem T_le_vw : T ≤ centralizer ({y * x} : Set G) := by
  intro s hs
  apply mem_centralizer_singleton_iff.2
  have hx : s * x = x * s := mem_centralizer_singleton_iff.1 (h.T_le hs)
  have hy := h.y_comm_T s hs
  calc s * (y * x) = (s * y) * x := by rw [mul_assoc]
    _ = (y * s) * x := by rw [hy]
    _ = y * (s * x) := by rw [mul_assoc]
    _ = y * (x * s) := by rw [hx]
    _ = (y * x) * s := by rw [mul_assoc]

theorem yx_mul_self : (y * x) * (y * x) = 1 := by
  calc (y * x) * (y * x) = y * (x * y) * x := by group
    _ = y * (y * x) * x := by rw [← h.comm]
    _ = (y * y) * (x * x) := by group
    _ = 1 := by rw [h.y_mul_self, h.x_mul_self, one_mul]

theorem yx_ne_one : y * x ≠ 1 := fun hyx => by
  apply h.ne
  have : y = x⁻¹ := mul_eq_one_iff_eq_inv.1 hyx
  rw [this]
  exact inv_eq_of_mul_eq_one_right h.x_mul_self

theorem T_sylow_vw (hclass : B_L3_class) (hsyl : B_L3_sylow) :
    IsSylowOf 2 T (centralizer ({y * x} : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C : Subgroup G := centralizer ({y * x} : Set G) with hC
  obtain ⟨S', hS'⟩ := exists_isSylowOf 2 C
  have hIvwC : Ivw ≤ C := h.comp_vw.1.1
  have hR' : IsSylowOf 2 (S' ⊓ Ivw) Ivw := hS'.inf_of_le_normalizer hIvwC h.comp_vw.le_normalizer
  have hq := h.comp_vw.1.isQuasisimple
  obtain ⟨hcyc, -, -, -⟩ := hsyl G t' p f h.tag' h.prime.1 h.prime.2.1 h.prime.2.2 Ivw hq h.odd_vw
    h.model_vw _ hR'
  have hR'ne : S' ⊓ Ivw ≠ ⊥ := by
    intro hb
    have hcard := hR'.card_eq
    rw [hb, Subgroup.card_bot] at hcard
    have h2 : 2 ∣ Nat.card ↥Ivw := by
      have := Subgroup.orderOf_dvd_natCard Ivw (h.Iv_le_vw h.y_Iv)
      rwa [h.y_inv] at this
    have hpos := Nat.Prime.factorization_pos_of_dvd Nat.prime_two Nat.card_pos.ne' h2
    have : 2 ^ (Nat.card ↥Ivw).factorization 2 = 1 := hcard.symm
    have h2pos : 2 ≤ 2 ^ (Nat.card ↥Ivw).factorization 2 := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ _ := Nat.pow_le_pow_right (by norm_num) hpos
    omega
  obtain ⟨y', hy'R, hy'2, hy'1, hy'c⟩ := exists_central_involution
    (hS'.isPGroup.to_inf_left (K := Ivw)) hR'ne
  have hy'Ivw : y' ∈ Ivw := hy'R.2
  have hy'Z : y' ∈ (S' ⊓ Ivw) ⊓ centralizer ((S' ⊓ Ivw : Subgroup G) : Set G) :=
    ⟨hy'R, mem_centralizer_iff.2 fun r hr => hy'c r hr⟩
  have hconjR : ∀ s ∈ S', ∀ r ∈ S' ⊓ Ivw, s * r * s⁻¹ ∈ S' ⊓ Ivw := fun s hs r hr =>
    ⟨S'.mul_mem (S'.mul_mem hs hr.1) (S'.inv_mem hs),
      h.comp_vw.conj s (hS'.le hs) r hr.2⟩
  have hy'S : ∀ s ∈ S', s * y' * s⁻¹ = y' := by
    intro s hs
    have hw : s * y' * s⁻¹ ∈ S' ⊓ Ivw := hconjR s hs y' hy'R
    have hwc : s * y' * s⁻¹ ∈ (S' ⊓ Ivw) ⊓ centralizer ((S' ⊓ Ivw : Subgroup G) : Set G) := by
      refine ⟨hw, mem_centralizer_iff.2 fun r hr => ?_⟩
      have hr' : s⁻¹ * r * s ∈ S' ⊓ Ivw := by
        have := hconjR s⁻¹ (S'.inv_mem hs) r hr
        simpa using this
      have := hy'c _ hr'
      calc r * (s * y' * s⁻¹) = s * ((s⁻¹ * r * s) * y') * s⁻¹ := by group
        _ = s * (y' * (s⁻¹ * r * s)) * s⁻¹ := by rw [this]
        _ = (s * y' * s⁻¹) * r := by group
    have hw2 : (s * y' * s⁻¹) * (s * y' * s⁻¹) = 1 := by
      calc (s * y' * s⁻¹) * (s * y' * s⁻¹) = s * (y' * y') * s⁻¹ := by group
        _ = 1 := by rw [hy'2]; group
    have hw1 : s * y' * s⁻¹ ≠ 1 := fun h1 => hy'1 (by
      have : y' = s⁻¹ * (s * y' * s⁻¹) * s := by group
      rw [this, h1]; group)
    exact eq_of_involutions_of_cyclic hcyc hwc hy'Z hw1 hy'1 hw2 hy'2
  obtain ⟨g, hg, hgy⟩ := hclass G t' p f h.tag' h.prime.1 h.prime.2.1 h.prime.2.2 Ivw hq h.odd_vw
    h.model_vw y' hy'Ivw y (h.Iv_le_vw h.y_Iv) hy'2 hy'1 h.y_mul_self h.y_ne_one
  have hgC : g ∈ C := hIvwC hg
  let S'' : Subgroup G := S'.map (MulAut.conj g).toMonoidHom
  have hS''le : S'' ≤ C := by
    rintro _ ⟨s, hs, rfl⟩
    exact C.mul_mem (C.mul_mem hgC (hS'.le hs)) (C.inv_mem hgC)
  have hS''card : Nat.card ↥S'' = Nat.card ↥S' :=
    Subgroup.card_map_of_injective (MulAut.conj g).injective
  have hS'' : IsSylowOf 2 S'' C := by
    refine isSylowOf_of_card hS''le ?_
    rw [hS''card]
    exact hS'.card_eq
  have hyS'' : ∀ u ∈ S'', u * y = y * u := by
    rintro _ ⟨s, hs, rfl⟩
    have hcomm : s * y' = y' * s := by
      have := hy'S s hs
      calc s * y' = (s * y' * s⁻¹) * s := by group
        _ = y' * s := by rw [this]
    show (g * s * g⁻¹) * y = y * (g * s * g⁻¹)
    rw [← hgy]
    calc g * s * g⁻¹ * (g * y' * g⁻¹) = g * (s * y') * g⁻¹ := by group
      _ = g * (y' * s) * g⁻¹ := by rw [hcomm]
      _ = g * y' * g⁻¹ * (g * s * g⁻¹) := by group
  have hS''x : S'' ≤ centralizer ({x} : Set G) := by
    intro u hu
    apply mem_centralizer_singleton_iff.2
    have huC : u * (y * x) = (y * x) * u := mem_centralizer_singleton_iff.1 (hS''le hu)
    have huy : u * y⁻¹ = y⁻¹ * u := (show Commute u y from hyS'' u hu).inv_right.eq
    calc u * x = u * (y⁻¹ * (y * x)) := by group
      _ = (u * y⁻¹) * (y * x) := by rw [mul_assoc]
      _ = (y⁻¹ * u) * (y * x) := by rw [huy]
      _ = y⁻¹ * (u * (y * x)) := by rw [mul_assoc]
      _ = y⁻¹ * ((y * x) * u) := by rw [huC]
      _ = x * u := by group
  have h1 : Nat.card ↥S'' ≤ Nat.card ↥T := card_le_of_isPGroup_le hS''.isPGroup hS''x h.T_sylow
  have h2 : Nat.card ↥T ≤ Nat.card ↥S'' := card_le_of_isPGroup_le h.T_pGroup h.T_le_vw hS''
  refine isSylowOf_of_card h.T_le_vw ?_
  have h3 := hS''.card_eq
  omega

end Nbhd3

end CFSG.GH74.Generic.S3
