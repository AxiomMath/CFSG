module

public import CFSG.GH74.GLS.Stage2.Local.P27.P3L4
public import CFSG.GH74.GLS.Stage2.Local.P27.L4Transport

public section

namespace CFSG.GH74.GLS.Stage2.Local.P27

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74

variable {G : Type} [Group G] [Finite G]

theorem exists_sylow_of_isSylowOf_top {S : Subgroup G} (hS : IsSylowOf 2 S ⊤) :
    ∃ Q : Sylow 2 G, (Q : Subgroup G) = S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [isSylowOf_iff] at hS
  obtain ⟨-, hP, hdvd⟩ := hS
  rw [Subgroup.relIndex_top_right] at hdvd
  exact ⟨hP.toSylow hdvd, IsPGroup.toSylow_coe hP hdvd⟩

theorem isCentralInvolution_of_mem_center_sylow {S : Subgroup G} (hS : IsSylowOf 2 S ⊤) {v : G}
    (hv2 : orderOf v = 2) (hvS : v ∈ S) (hvc : ∀ s ∈ S, s * v = v * s) : IsCentralInvolution v := by
  obtain ⟨Q, hQ⟩ := exists_sylow_of_isSylowOf_top hS
  exact ⟨hv2, Q, hQ ▸ hvS, fun s hs => hvc s (hQ ▸ hs)⟩

omit [Finite G] in
theorem mem_of_isSylowOf_of_central {X T : Subgroup G} (hT : IsSylowOf 2 T X) {u : G} (huX : u ∈ X)
    (hu2 : orderOf u = 2) (huc : ∀ x ∈ X, x * u = u * x) : u ∈ T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q, rfl⟩ := hT
  set N : Subgroup ↥X := (zpowers u).subgroupOf X with hN
  have hNn : N.Normal := by
    refine ⟨fun n hn g => ?_⟩
    have hn' : (n : G) ∈ zpowers u := hn
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hn'
    have hgn : (g : G) * (n : G) = (n : G) * (g : G) := by
      rw [← hk]
      exact (Commute.zpow_right (huc (g : G) g.2 : Commute (g : G) u) k).eq
    show ((g * n * g⁻¹ : ↥X) : G) ∈ zpowers u
    have : ((g * n * g⁻¹ : ↥X) : G) = (n : G) := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      calc (g : G) * (n : G) * (g : G)⁻¹ = (n : G) * (g : G) * (g : G)⁻¹ := by rw [hgn]
        _ = (n : G) := by group
    rw [this]
    exact hn'
  have hNp : IsPGroup 2 ↥N := by
    rw [IsPGroup.iff_orderOf]
    intro g
    have hg : (g : G) ∈ zpowers u := g.2
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hg
    have hsq : (g : ↥X) ^ 2 = 1 := by
      apply Subtype.ext
      simp only [SubgroupClass.coe_pow, OneMemClass.coe_one]
      rw [pow_two]
      have h1 : ((g : ↥X) : G) = u ^ k := hk.symm
      rw [h1, ← zpow_add, ← two_mul, zpow_mul]
      have : u ^ (2 : ℤ) = 1 := by
        have := pow_orderOf_eq_one u
        rw [hu2] at this
        exact_mod_cast this
      rw [this, one_zpow]
    have hdvd : orderOf (g : ↥N) ∣ 2 := by
      apply orderOf_dvd_of_pow_eq_one
      apply Subtype.ext
      simpa using hsq
    rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h | h
    · exact ⟨0, by simpa using h⟩
    · exact ⟨1, by simpa using h⟩
  have hNle := IsPGroup.le_sylow_of_normal hNp Q
  have hu' : (⟨u, huX⟩ : ↥X) ∈ N := Subgroup.mem_zpowers u
  exact ⟨⟨u, huX⟩, hNle hu', rfl⟩

theorem isSylowOf_inf_centralizer_of_index_two {S : Subgroup G} {u : G}
    (hS : IsSylowOf 2 S ⊤) (hu2 : orderOf u = 2)
    (hnc : ¬ IsCentralInvolution u)
    (hidx : (S ⊓ centralizer ({u} : Set G)).relIndex S = 2) :
    IsSylowOf 2 (S ⊓ centralizer ({u} : Set G)) (centralizer ({u} : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set X := centralizer ({u} : Set G) with hX
  have huX : u ∈ X := mem_centralizer_iff.2 (fun h hh => by rw [Set.mem_singleton_iff.1 hh])
  have huc : ∀ x ∈ X, x * u = u * x := fun x hx => (mem_centralizer_iff.1 hx u rfl).symm
  obtain ⟨T₀, hT₀⟩ := exists_isSylowOf 2 X
  have huT₀ : u ∈ T₀ := mem_of_isSylowOf_of_central hT₀ huX hu2 huc
  obtain ⟨c, -, hc⟩ := CFSG.ComponentClassification.GHarris.exists_conj_le_of_isSylowOf hS
    (le_top : T₀ ≤ ⊤) hT₀.isPGroup
  set v := c * u * c⁻¹ with hv
  have hvS : v ∈ S := hc u huT₀
  have hv2 : orderOf v = 2 := by
    have := MulEquiv.orderOf_eq (MulAut.conj c) u
    rwa [MulAut.conj_apply, hu2] at this
  have hT₀v : cj c T₀ ≤ S ⊓ centralizer ({v} : Set G) := by
    intro y hy
    obtain ⟨q, hq, rfl⟩ := hy
    refine ⟨hc q hq, mem_centralizer_iff.2 ?_⟩
    intro h hh
    rw [Set.mem_singleton_iff.1 hh]
    have hqX : q ∈ X := hT₀.le hq
    have hq' : q * u = u * q := huc q hqX
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, hv]
    calc c * u * c⁻¹ * (c * q * c⁻¹) = c * (u * q) * c⁻¹ := by group
      _ = c * (q * u) * c⁻¹ := by rw [hq']
      _ = c * q * c⁻¹ * (c * u * c⁻¹) := by group
  have hvnc : ¬ ∀ s ∈ S, s * v = v * s := by
    intro h
    apply hnc
    have hvc : IsCentralInvolution v := isCentralInvolution_of_mem_center_sylow hS hv2 hvS h
    have hconj : IsConj v u := isConj_iff.2 ⟨c⁻¹, by rw [hv]; group⟩
    exact isCentralInvolution_of_isConj_P27 hvc hconj
  have hCv : (S ⊓ centralizer ({v} : Set G)).relIndex S ≠ 1 := by
    intro h1
    rw [Subgroup.relIndex_eq_one] at h1
    apply hvnc
    intro s hs
    exact (mem_centralizer_iff.1 (h1 hs).2 v rfl).symm
  have hCu : 2 * Nat.card ↥(S ⊓ X) = Nat.card ↥S := by
    have h := Subgroup.relIndex_mul_card (S ⊓ X) S
    rwa [hidx, inf_eq_left.2 inf_le_left] at h
  have hCv2 : 2 * Nat.card ↥(S ⊓ centralizer ({v} : Set G)) ≤ Nat.card ↥S := by
    have h := Subgroup.relIndex_mul_card (S ⊓ centralizer ({v} : Set G)) S
    rw [inf_eq_left.2 inf_le_left] at h
    have hpos : 0 < Nat.card ↥S := Nat.card_pos
    have hr0 : (S ⊓ centralizer ({v} : Set G)).relIndex S ≠ 0 := by
      intro h0
      rw [h0, zero_mul] at h
      omega
    have hr2 : 2 ≤ (S ⊓ centralizer ({v} : Set G)).relIndex S := by omega
    calc 2 * Nat.card ↥(S ⊓ centralizer ({v} : Set G))
        ≤ (S ⊓ centralizer ({v} : Set G)).relIndex S * Nat.card ↥(S ⊓ centralizer ({v} : Set G)) :=
          Nat.mul_le_mul_right _ hr2
      _ = Nat.card ↥S := h
  have h1 : Nat.card ↥T₀ ≤ Nat.card ↥(S ⊓ centralizer ({v} : Set G)) := by
    rw [← card_cj c T₀]
    exact Subgroup.card_le_of_le hT₀v
  have h2 : Nat.card ↥(S ⊓ X) ≤ Nat.card ↥T₀ := by
    obtain ⟨k, -, hk⟩ := CFSG.ComponentClassification.GHarris.exists_conj_le_of_isSylowOf hT₀
      (inf_le_right : S ⊓ X ≤ X) hS.isPGroup.to_inf_left
    have : cj k (S ⊓ X) ≤ T₀ := by
      rintro y ⟨a, ha, rfl⟩
      exact hk a ha
    rw [← card_cj k (S ⊓ X)]
    exact Subgroup.card_le_of_le this
  have h3 : Nat.card ↥(S ⊓ X) = Nat.card ↥T₀ := by omega
  exact isSylowOf_of_card inf_le_right (by rw [h3, hT₀.card_eq])

omit [Finite G] in
theorem exists_isSylowOf_ge_of_le' {X A : Subgroup G} (hAX : A ≤ X) (hA : IsPGroup 2 ↥A) :
    ∃ B : Subgroup G, IsSylowOf 2 B X ∧ A ≤ B := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hA' : IsPGroup 2 ↥(A.subgroupOf X) := hA.comap_subtype
  obtain ⟨Q, hQ⟩ := hA'.exists_le_sylow
  refine ⟨(Q : Subgroup X).map X.subtype, ⟨Q, rfl⟩, fun a ha => ?_⟩
  exact ⟨⟨a, hAX ha⟩, hQ ha, rfl⟩

theorem isSylowOf_top_of_central {z : G} {S : Subgroup G} (hz : IsCentralInvolution z)
    (hS : IsSylowOf 2 S (centralizer ({z} : Set G))) : IsSylowOf 2 S ⊤ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, Q, hzQ, hzc⟩ := hz
  have hQC : (Q : Subgroup G) ≤ centralizer ({z} : Set G) := fun q hq =>
    mem_centralizer_iff.2 (fun h hh => by rw [Set.mem_singleton_iff.1 hh]; exact (hzc q hq).symm)
  obtain ⟨c, -, hc⟩ := CFSG.ComponentClassification.GHarris.exists_conj_le_of_isSylowOf hS hQC Q.isPGroup'
  have hQS : cj c (Q : Subgroup G) ≤ S := by
    rintro y ⟨q, hq, rfl⟩
    exact hc q hq
  have h1 : Nat.card ↥(Q : Subgroup G) ≤ Nat.card ↥S := by
    rw [← card_cj c (Q : Subgroup G)]
    exact Subgroup.card_le_of_le hQS
  have h2 : Nat.card ↥S ≤ Nat.card ↥(Q : Subgroup G) := by
    have hQ' : IsSylowOf 2 (Q : Subgroup G) ⊤ := by
      rw [isSylowOf_iff]
      refine ⟨le_top, Q.isPGroup', ?_⟩
      rw [Subgroup.relIndex_top_right]
      exact Q.not_dvd_index
    obtain ⟨k, -, hk⟩ := CFSG.ComponentClassification.GHarris.exists_conj_le_of_isSylowOf hQ'
      (le_top : S ≤ ⊤) hS.isPGroup
    have : cj k S ≤ (Q : Subgroup G) := by
      rintro y ⟨s, hs, rfl⟩
      exact hk s hs
    rw [← card_cj k S]
    exact Subgroup.card_le_of_le this
  have hQeq : Nat.card ↥S = Nat.card ↥(Q : Subgroup G) := le_antisymm h2 h1
  refine isSylowOf_of_card le_top ?_
  rw [hQeq, Sylow.card_eq_multiplicity Q]
  simp

end CFSG.GH74.GLS.Stage2.Local.P27
