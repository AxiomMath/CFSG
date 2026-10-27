module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.GlobLocal
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.GlobSquareFacts
public import CFSG.LocalAnalysis.EvenSporadicStandard.HypOne.SylowFour
public import CFSG.LocalAnalysis.EvenSporadicStandard.HypOne.Generic

public section

namespace CFSG.EvenSporadicStandard.Solomon78

open Subgroup CFSG.EvenSporadicStandard.HypOne

variable {G : Type} [Group G] [Finite G]

theorem card_le_two_pow_of_isPGroup {K H : Subgroup G} (hH : IsPGroup 2 H) (hHK : H ≤ K) :
    Nat.card H ≤ 2 ^ (Nat.card K).factorization 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 hH
  have hdvd : 2 ^ n ∣ Nat.card K := hn ▸ Subgroup.card_dvd_of_le hHK
  have hle : n ≤ (Nat.card K).factorization 2 :=
    (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two Nat.card_pos.ne').1 hdvd
  rw [hn]
  exact Nat.pow_le_pow_right (by norm_num) hle

omit [Finite G] in
theorem isPGroup_two_zpowers {v : G} (hv2 : v * v = 1) : IsPGroup 2 (zpowers v) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2 : orderOf v ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hv2)
  rcases (Nat.dvd_prime Nat.prime_two).1 h2 with h | h
  · exact IsPGroup.of_card (n := 0) (by rw [Nat.card_zpowers, h]; rfl)
  · exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, h]; rfl)

theorem mem_of_commute_sylow {K Q : Subgroup G} (hQK : Q ≤ K)
    (hQ : Nat.card Q = 2 ^ (Nat.card K).factorization 2) {v : G} (hv : v ∈ K)
    (hv2 : v * v = 1) (hc : ∀ q ∈ Q, q * v = v * q) : v ∈ Q := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQp : IsPGroup 2 Q := IsPGroup.of_card hQ
  have hvp := isPGroup_two_zpowers hv2
  have hQc : Q ≤ centralizer (zpowers v : Set G) := by
    intro q hq
    rw [mem_centralizer_iff]
    intro h hh
    obtain ⟨n, rfl⟩ := mem_zpowers_iff.1 hh
    have hcom : Commute v q := (hc q hq).symm
    exact ((hcom.zpow_left n).eq)
  have hQn : Q ≤ normalizer (zpowers v : Set G) :=
    hQc.trans (Subgroup.centralizer_le_normalizer _)
  have hHp : IsPGroup 2 ↥(Q ⊔ zpowers v) := hQp.to_sup_of_normal_right' hvp hQn
  have hHK : Q ⊔ zpowers v ≤ K := sup_le hQK (zpowers_le.2 hv)
  have hcard := card_le_two_pow_of_isPGroup hHp hHK
  have heq : Q = Q ⊔ zpowers v := Subgroup.eq_of_le_of_card_ge le_sup_left (hQ ▸ hcard)
  rw [heq]
  exact (le_sup_right : zpowers v ≤ Q ⊔ zpowers v) (mem_zpowers v)

theorem exists_conj_of_sylow {K Q S : Subgroup G} (hQK : Q ≤ K) (hSK : S ≤ K)
    (hQ : Nat.card Q = 2 ^ (Nat.card K).factorization 2)
    (hS : Nat.card S = 2 ^ (Nat.card K).factorization 2) :
    ∃ c ∈ K, ∀ y : G, y ∈ Q ↔ ∃ s ∈ S, y = c * s * c⁻¹ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let Q' : Sylow 2 K := Sylow.ofCard (Q.subgroupOf K) (by
    rw [← hQ]
    exact Nat.card_congr (subgroupOfEquivOfLe hQK).toEquiv)
  let S' : Sylow 2 K := Sylow.ofCard (S.subgroupOf K) (by
    rw [← hS]
    exact Nat.card_congr (subgroupOfEquivOfLe hSK).toEquiv)
  obtain ⟨x, hx⟩ := MulAction.exists_smul_eq K S' Q'
  have hQ'c : (Q' : Subgroup K) = Q.subgroupOf K := Sylow.coe_ofCard _ _
  have hS'c : (S' : Subgroup K) = S.subgroupOf K := Sylow.coe_ofCard _ _
  refine ⟨x, x.2, fun y => ?_⟩
  constructor
  · intro hy
    have h1 : (⟨y, hQK hy⟩ : K) ∈ (Q' : Subgroup K) := by
      rw [hQ'c]
      exact mem_subgroupOf.2 hy
    rw [← hx, Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists] at h1
    obtain ⟨s, hs, hsy⟩ := h1
    have hsS : (s : G) ∈ S := by
      rw [hS'c] at hs
      exact mem_subgroupOf.1 hs
    refine ⟨s, hsS, ?_⟩
    have e := congrArg Subtype.val hsy
    rw [MulAut.smul_def, MulAut.conj_apply] at e
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at e
    exact e.symm
  · rintro ⟨s, hs, rfl⟩
    have h1 : (⟨s, hSK hs⟩ : K) ∈ (S' : Subgroup K) := by
      rw [hS'c]
      exact mem_subgroupOf.2 hs
    have h2 : (MulAut.conj x • (⟨s, hSK hs⟩ : K)) ∈ ((x • S' : Sylow 2 K) : Subgroup K) := by
      rw [Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists]
      exact ⟨_, h1, rfl⟩
    rw [hx, hQ'c] at h2
    have h3 := mem_subgroupOf.1 h2
    rw [MulAut.smul_def, MulAut.conj_apply] at h3
    simpa using h3

theorem exists_conj_central_mem {K S : Subgroup G} (hSK : S ≤ K)
    (hS : Nat.card S = 2 ^ (Nat.card K).factorization 2) {v : G} (hv : v ∈ K) (hv2 : v * v = 1)
    (hCv : twoAdic K ≤ twoAdic (K ⊓ centralizer ({v} : Set G))) :
    ∃ c ∈ K, c⁻¹ * v * c ∈ S ∧ ∀ s ∈ S, (c⁻¹ * v * c) * s = s * (c⁻¹ * v * c) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C := K ⊓ centralizer ({v} : Set G) with hC
  obtain ⟨P⟩ : Nonempty (Sylow 2 C) := inferInstance
  let Q : Subgroup G := (P : Subgroup C).map C.subtype
  have hQC : Q ≤ C := by
    rintro _ ⟨y, -, rfl⟩
    exact y.2
  have hCK : C ≤ K := inf_le_left
  have heq : (Nat.card C).factorization 2 = (Nat.card K).factorization 2 :=
    le_antisymm (twoAdic_mono hCK) hCv
  have hQcard : Nat.card Q = 2 ^ (Nat.card K).factorization 2 := by
    rw [← heq, ← P.card_eq_multiplicity]
    exact (Nat.card_congr ((P : Subgroup C).equivMapOfInjective C.subtype
      Subtype.coe_injective).toEquiv).symm
  have hQK : Q ≤ K := hQC.trans hCK
  have hQv : ∀ q ∈ Q, q * v = v * q := fun q hq =>
    mem_centralizer_singleton_iff.1 (hQC hq).2
  obtain ⟨c, hcK, hc⟩ := exists_conj_of_sylow hQK hSK hQcard hS
  have hvQ : v ∈ Q := mem_of_commute_sylow hQK hQcard hv hv2 hQv
  obtain ⟨s₀, hs₀, hvs⟩ := (hc v).1 hvQ
  have hconj : c⁻¹ * v * c = s₀ := by rw [hvs]; group
  refine ⟨c, hcK, hconj ▸ hs₀, fun s hs => ?_⟩
  have h1 := hQv (c * s * c⁻¹) ((hc _).2 ⟨s, hs, rfl⟩)
  rw [hconj]
  rw [hvs] at h1
  have h2 : c * (s * s₀) * c⁻¹ = c * (s₀ * s) * c⁻¹ := by
    calc c * (s * s₀) * c⁻¹ = c * s * c⁻¹ * (c * s₀ * c⁻¹) := by group
      _ = c * s₀ * c⁻¹ * (c * s * c⁻¹) := h1
      _ = c * (s₀ * s) * c⁻¹ := by group
  have h3 := mul_left_cancel (mul_right_cancel h2)
  exact h3.symm

theorem not_sq_of_sylow {K S : Subgroup G} (hSK : S ≤ K)
    (hS : Nat.card S = 2 ^ (Nat.card K).factorization 2) {d : G} (hd2 : d * d = 1)
    (hdc : ∀ s ∈ S, s * d = d * s) (hnsq : ∀ s ∈ S, s * s ≠ d) :
    ∀ x ∈ K, x * x ≠ d := by
  intro x hx hxd
  set R := K ⊓ centralizer ({d} : Set G) with hR
  have hSR : S ≤ R := fun s hs =>
    ⟨hSK hs, mem_centralizer_singleton_iff.2 (hdc s hs)⟩
  have hRK : R ≤ K := inf_le_left
  have hSR' : Nat.card S = 2 ^ (Nat.card R).factorization 2 := by
    have h1 : (Nat.card S).factorization 2 ≤ (Nat.card R).factorization 2 :=
      (Nat.factorization_le_iff_dvd Nat.card_pos.ne' Nat.card_pos.ne').2
        (Subgroup.card_dvd_of_le hSR) 2
    have h2 := twoAdic_mono hRK
    unfold twoAdic at h2
    rw [hS]
    have h3 : (2 ^ (Nat.card K).factorization 2).factorization 2 =
        (Nat.card K).factorization 2 := by
      rw [Nat.Prime.factorization_pow Nat.prime_two]
      simp
    rw [hS, h3] at h1
    congr 1
    omega
  have hxR : x ∈ R := by
    refine ⟨hx, mem_centralizer_singleton_iff.2 ?_⟩
    rw [← hxd]
    calc x * (x * x) = (x * x) * x := by group
      _ = _ := rfl
  have hx4 : x ^ 4 = 1 := by
    calc x ^ 4 = (x * x) * (x * x) := by rw [show 4 = 2 + 2 from rfl, pow_add, sq]
      _ = 1 := by rw [hxd, hd2]
  obtain ⟨c, hcR, hcS⟩ := exists_conj_mem_of_card_pow_four hSR hSR' hxR hx4
  apply hnsq _ hcS
  have hcd : c⁻¹ * d * c = d := by
    have := mem_centralizer_singleton_iff.1 hcR.2
    calc c⁻¹ * d * c = c⁻¹ * (d * c) := by group
      _ = c⁻¹ * (c * d) := by rw [this]
      _ = d := by group
  calc c⁻¹ * x * c * (c⁻¹ * x * c) = c⁻¹ * (x * x) * c := by group
    _ = d := by rw [hxd, hcd]

theorem SquareFacts.dichotomy {K S : Subgroup G} {u d v : G} (h : SquareFacts K S u d)
    (hv : v ∈ vMaximal K u) :
    ∃ c ∈ K, (c⁻¹ * v * c = d ∧ ∀ x ∈ K, x * x ≠ v) ∨
      (c⁻¹ * v * c = u * d ∧ ∃ x ∈ K, x * x = v) := by
  obtain ⟨⟨hvK', hvZ, hvo⟩, hvmax⟩ := hv
  have huK : K ⊔ zpowers u = K := sup_eq_left.2 (zpowers_le.2 h.u_mem)
  have hvK : v ∈ K := huK ▸ hvK'
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hv2', hv1⟩ := orderOf_eq_prime_iff.1 hvo
  have hv2 : v * v = 1 := by rw [← pow_two]; exact hv2'
  have hvu : v ≠ u := by
    rintro rfl
    exact hvZ (mem_center_map_iff.2 ⟨h.u_mem, fun k hk => (h.u_central k hk).symm⟩)
  have hdcand : d ∈ vCandidates K u := by
    refine ⟨by rw [huK]; exact h.d_mem, ?_,
      orderOf_eq_prime (by rw [pow_two]; exact h.d_sq) h.d_ne_one⟩
    intro hz
    obtain ⟨-, hzc⟩ := mem_center_map_iff.1 hz
    rcases h.central_inv d h.d_mem h.d_sq hzc with h1 | h1
    · exact h.d_ne_one h1
    · exact h.d_ne_u h1
  have hSd : S ≤ K ⊓ centralizer ({d} : Set G) := fun s hs =>
    ⟨h.S_le hs, mem_centralizer_singleton_iff.2 (h.d_comm s hs)⟩
  have hSa : twoAdic K = twoAdic S := by
    unfold twoAdic
    rw [h.S_card, Nat.Prime.factorization_pow Nat.prime_two]
    simp
  have h2 : twoAdic K ≤ twoAdic (K ⊓ centralizer ({v} : Set G)) :=
    calc twoAdic K = twoAdic S := hSa
      _ ≤ twoAdic (K ⊓ centralizer ({d} : Set G)) := twoAdic_mono hSd
      _ ≤ twoAdic (K ⊓ centralizer ({v} : Set G)) := hvmax d hdcand
  obtain ⟨c, hcK, hcS, hcc⟩ := exists_conj_central_mem h.S_le h.S_card hvK hv2 h2
  have hcu : c⁻¹ * u * c = u := by
    calc c⁻¹ * u * c = c⁻¹ * (u * c) := by group
      _ = c⁻¹ * (c * u) := by rw [(h.u_central c hcK).symm]
      _ = u := by group
  have hv'2 : (c⁻¹ * v * c) * (c⁻¹ * v * c) = 1 := by
    calc (c⁻¹ * v * c) * (c⁻¹ * v * c) = c⁻¹ * (v * v) * c := by group
      _ = 1 := by rw [hv2]; group
  have hv'1 : c⁻¹ * v * c ≠ 1 := by
    intro e
    apply hv1
    calc v = c * (c⁻¹ * v * c) * c⁻¹ := by group
      _ = 1 := by rw [e]; group
  have hv'u : c⁻¹ * v * c ≠ u := by
    intro e
    apply hvu
    calc v = c * (c⁻¹ * v * c) * c⁻¹ := by group
      _ = c * u * c⁻¹ := by rw [e]
      _ = u := by
        calc c * u * c⁻¹ = u * c * c⁻¹ := by rw [h.u_central c hcK]
          _ = u := by group
  rcases h.center_inv _ hcS hv'2 hcc with e | e | e | e
  · exact absurd e hv'1
  · exact absurd e hv'u
  · refine ⟨c, hcK, Or.inl ⟨e, fun x hx hxv => ?_⟩⟩
    refine not_sq_of_sylow h.S_le h.S_card h.d_sq h.d_comm h.d_nonsq (c⁻¹ * x * c)
      (K.mul_mem (K.mul_mem (K.inv_mem hcK) hx) hcK) ?_
    calc c⁻¹ * x * c * (c⁻¹ * x * c) = c⁻¹ * (x * x) * c := by group
      _ = d := by rw [hxv]; exact e
  · refine ⟨c, hcK, Or.inr ⟨e, ?_⟩⟩
    obtain ⟨s, hs, hss⟩ := h.ud_sq
    refine ⟨c * s * c⁻¹, K.mul_mem (K.mul_mem hcK (h.S_le hs)) (K.inv_mem hcK), ?_⟩
    calc c * s * c⁻¹ * (c * s * c⁻¹) = c * (s * s) * c⁻¹ := by group
      _ = c * (u * d) * c⁻¹ := by rw [hss]
      _ = c * (c⁻¹ * v * c) * c⁻¹ := by rw [e]
      _ = v := by group

theorem SquareFacts.exists_conj {K S : Subgroup G} {u d v w : G} (h : SquareFacts K S u d)
    (hv : v ∈ vMaximal K u) (hw : w ∈ vMaximal K u)
    (hsq : (∃ x ∈ K, x * x = v) ↔ (∃ y ∈ K, y * y = w)) : ∃ c ∈ K, c * v * c⁻¹ = w := by
  obtain ⟨c₁, hc₁, h₁⟩ := h.dichotomy hv
  obtain ⟨c₂, hc₂, h₂⟩ := h.dichotomy hw
  have key : ∀ e : G, c₁⁻¹ * v * c₁ = e → c₂⁻¹ * w * c₂ = e →
      (c₂ * c₁⁻¹) * v * (c₂ * c₁⁻¹)⁻¹ = w := by
    intro e e₁ e₂
    calc (c₂ * c₁⁻¹) * v * (c₂ * c₁⁻¹)⁻¹ = c₂ * (c₁⁻¹ * v * c₁) * c₂⁻¹ := by group
      _ = c₂ * (c₂⁻¹ * w * c₂) * c₂⁻¹ := by rw [e₁, e₂]
      _ = w := by group
  have hc : c₂ * c₁⁻¹ ∈ K := K.mul_mem hc₂ (K.inv_mem hc₁)
  rcases h₁ with ⟨e₁, n₁⟩ | ⟨e₁, s₁⟩ <;> rcases h₂ with ⟨e₂, n₂⟩ | ⟨e₂, s₂⟩
  · exact ⟨_, hc, key _ e₁ e₂⟩
  · obtain ⟨x, hx, hxv⟩ := hsq.2 s₂
    exact absurd hxv (n₁ x hx)
  · obtain ⟨x, hx, hxw⟩ := hsq.1 s₁
    exact absurd hxw (n₂ x hx)
  · exact ⟨_, hc, key _ e₁ e₂⟩

theorem exists_lt_of_card_lt {L S : Subgroup G} (hSL : S ≤ L) (hS : IsPGroup 2 S)
    (hlt : Nat.card S < 2 ^ (Nat.card L).factorization 2) :
    ∃ T : Subgroup G, T ≤ L ∧ IsPGroup 2 T ∧ S < T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hS' : IsPGroup 2 (S.subgroupOf L) := hS.of_equiv (subgroupOfEquivOfLe hSL).symm
  obtain ⟨P, hP⟩ := hS'.exists_le_sylow
  let T : Subgroup G := (P : Subgroup L).map L.subtype
  have hTL : T ≤ L := by
    rintro _ ⟨y, -, rfl⟩
    exact y.2
  have hTcard : Nat.card T = 2 ^ (Nat.card L).factorization 2 := by
    rw [← P.card_eq_multiplicity]
    exact (Nat.card_congr ((P : Subgroup L).equivMapOfInjective L.subtype
      Subtype.coe_injective).toEquiv).symm
  have hST : S ≤ T := by
    intro s hs
    exact ⟨⟨s, hSL hs⟩, hP (mem_subgroupOf.2 hs), rfl⟩
  refine ⟨T, hTL, IsPGroup.of_card hTcard, lt_of_le_of_ne hST fun e => ?_⟩
  rw [e, hTcard] at hlt
  exact lt_irrefl _ hlt

omit [Finite G] in
theorem map_conj_eq_of_hyp35 {K : Subgroup G} {u g : G} (h35 : K = componentProduct K u)
    (hg : g ∈ centralizer ({u} : Set G)) : g * u * g⁻¹ = u ∧ K.map (conjHom g) = K := by
  have hug : g * u * g⁻¹ = u := by
    have := mem_centralizer_singleton_iff.1 hg
    rw [this]
    group
  refine ⟨hug, ?_⟩
  have h := componentProduct_conj K u g
  rw [hug, ← h35] at h
  exact h.symm

end CFSG.EvenSporadicStandard.Solomon78
