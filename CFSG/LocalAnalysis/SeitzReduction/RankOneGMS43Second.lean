module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneGMS43Inv
public import CFSG.LocalAnalysis.SeitzReduction.RankOneGMS43Suzuki

public section

namespace CFSG.SeitzReduction.RankOne

open Subgroup CFSG.LocalAnalysis CFSG.ABGLocalTools
open CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.CGT.Timmesfeld75 (Goldschmidt1974)

namespace GMS43

namespace Hyp

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G}
  {T V₁ U₁ : Subgroup G} {y d : G} (h : Hyp L f t T V₁ U₁ y d)
include h

theorem inf_centralizer_le {S : Subgroup G} (hSp : IsPGroup 2 S) (hTS : T ≤ S) :
    S ⊓ centralizer ({t} : Set G) ≤ T := by
  have hXK : S ⊓ centralizer ({t} : Set G) ≤ normalizer ((zpowers t : Subgroup G) : Set G) := by
    rw [normalizer_zpowers_eq_centralizer_of_involution h.setting.orderOf_t]
    exact inf_le_right
  have hcard := Endings.card_le_of_isPGroup h.setting.le_normalizer h.setting.sylow hXK
    (hSp.to_le inf_le_left)
  have hTX : T ≤ S ⊓ centralizer ({t} : Set G) := le_inf hTS h.le_centralizer
  exact (Subgroup.eq_of_le_of_card_ge hTX hcard).ge

theorem mem_sup_of_mul_conj_mem {S : Subgroup G} (hSp : IsPGroup 2 S) (hES : U₁ ⊔ T ≤ S)
    {w : G} (hw : w ∈ S) (hwt : t * (w * t * w⁻¹) ∈ U₁) : w ∈ U₁ ⊔ T := by
  set e := t * (w * t * w⁻¹) with he_def
  have htt := h.t_mul_t
  have hte : t * e = w * t * w⁻¹ := by rw [he_def, ← mul_assoc, htt, one_mul]
  have hinv : t * e * (t * e) = 1 := by
    rw [hte]
    calc w * t * w⁻¹ * (w * t * w⁻¹) = w * (t * t) * w⁻¹ := by group
      _ = 1 := by rw [htt]; group
  have het : e * t = t * e := by
    have h1 : t * e * t = e⁻¹ := by
      have : t * e * t * e = 1 := by rw [← hinv]; group
      exact eq_inv_of_mul_eq_one_left this
    rw [h.inv_eq e hwt] at h1
    calc e * t = t * e * t * t := by rw [h1]
      _ = t * e * (t * t) := by group
      _ = t * e := by rw [htt, mul_one]
  have heU : e ∈ T ⊓ L := by
    rw [← h.result.centralizer_eq]
    exact mem_inf.mpr ⟨hwt, mem_centralizer_singleton_iff.mpr het⟩
  obtain ⟨e₁, he₁, he₁t⟩ := h.result.exists_comm_eq e heU
  have hconj : w * t * w⁻¹ = e₁ * t * e₁⁻¹ := by
    calc w * t * w⁻¹ = e * t := by rw [← hte, het]
      _ = e₁ * t * e₁⁻¹ * t * t := by rw [he₁t]
      _ = e₁ * t * e₁⁻¹ * (t * t) := by group
      _ = e₁ * t * e₁⁻¹ := by rw [htt, mul_one]
  have hc : e₁⁻¹ * w ∈ S ⊓ centralizer ({t} : Set G) := by
    refine mem_inf.mpr ⟨mul_mem (inv_mem (hES (mem_sup_left he₁))) hw, ?_⟩
    rw [mem_centralizer_singleton_iff]
    calc e₁⁻¹ * w * t = e₁⁻¹ * (w * t * w⁻¹) * w := by group
      _ = e₁⁻¹ * (e₁ * t * e₁⁻¹) * w := by rw [hconj]
      _ = t * (e₁⁻¹ * w) := by group
  have hT := h.inf_centralizer_le hSp (le_sup_right.trans hES) hc
  rw [show w = e₁ * (e₁⁻¹ * w) by group]
  exact mul_mem (mem_sup_left he₁) (mem_sup_right hT)

theorem mul_conj_mem_of_mem_sup {w : G} (hw : w ∈ U₁ ⊔ T) : t * (w * t * w⁻¹) ∈ U₁ := by
  obtain ⟨e, he, p, hp, rfl⟩ := Endings.exists_mul_eq_of_mem_sup h.T_le_normalizer hw
  have hpt : p * t = t * p := (mem_centralizer_singleton_iff.mp (h.le_centralizer hp))
  have hte : t * e * t⁻¹ ∈ U₁ := (mem_normalizer_iff.mp h.t_mem_normalizer e).mp he
  have e1 : t * (e * p * t * (e * p)⁻¹) = (t * e * t⁻¹) * (t * t) * e⁻¹ := by
    calc t * (e * p * t * (e * p)⁻¹) = t * e * (p * t) * p⁻¹ * e⁻¹ := by group
      _ = t * e * (t * p) * p⁻¹ * e⁻¹ := by rw [hpt]
      _ = (t * e * t⁻¹) * (t * t) * e⁻¹ := by group
  rw [e1, h.t_mul_t, mul_one]
  exact mul_mem hte (inv_mem he)

theorem card_inf_centralizer_sq_le_of_not_mem {S : Subgroup G} (hSp : IsPGroup 2 S)
    (hSN : S ≤ normalizer (U₁ : Set G)) (hES : U₁ ⊔ T ≤ S) {w : G} (hw : w ∈ S)
    (hw₀ : w ∉ U₁ ⊔ T) :
    Nat.card (U₁ ⊓ centralizer ({w} : Set G) : Subgroup G) ^ 2 ≤ (2 ^ f) ^ 3 := by
  classical
  have hUS : U₁ ≤ S := le_sup_left.trans hES
  have : (U₁.subgroupOf S).Normal := (normal_subgroupOf_iff_le_normalizer hUS).mpr hSN
  set N := U₁.subgroupOf S with hN
  have hQp : IsPGroup 2 (S ⧸ N) := hSp.to_quotient N
  have heq : ∀ a b : S, (a : S ⧸ N) = (b : S ⧸ N) ↔ (a : G)⁻¹ * b ∈ U₁ := fun a b => by
    rw [QuotientGroup.eq, hN, mem_subgroupOf]
    rfl
  have heq1 : ∀ a : S, (a : S ⧸ N) = 1 ↔ (a : G) ∈ U₁ := fun a => by
    rw [QuotientGroup.eq_one_iff, hN, mem_subgroupOf]
  have htS : t ∈ S := hES (mem_sup_right h.mem_T)
  set T' : S := ⟨t, htS⟩ with hT'
  set W' : S := ⟨w, hw⟩ with hW'
  set j : S ⧸ N := (T' : S ⧸ N) with hj
  set j' : S ⧸ N := ((W' * T' * W'⁻¹ : S) : S ⧸ N) with hj'
  have htt' : ((W' * T' * W'⁻¹ : S) : G) = w * t * w⁻¹ := rfl
  have hjj : j * j = 1 := by
    rw [hj, ← QuotientGroup.mk_mul, heq1]
    show t * t ∈ U₁
    rw [h.t_mul_t]
    exact one_mem _
  have hj'j' : j' * j' = 1 := by
    rw [hj', ← QuotientGroup.mk_mul, heq1]
    show w * t * w⁻¹ * (w * t * w⁻¹) ∈ U₁
    rw [show w * t * w⁻¹ * (w * t * w⁻¹) = w * (t * t) * w⁻¹ by group, h.t_mul_t]
    simp
  have hj'1 : j' ≠ 1 := by
    rw [hj', Ne, heq1, htt']
    have := h.not_conj_mem w⁻¹
    rwa [inv_inv] at this
  have hjne : j ≠ j' := by
    intro hjj'
    rw [hj, hj', heq, htt'] at hjj'
    apply hw₀
    refine h.mem_sup_of_mul_conj_mem hSp hES hw ?_
    have := hjj'
    rwa [show (T' : G) = t from rfl, h.t_inv] at this
  obtain ⟨n, hz1, -, hzj, hzt⟩ := exists_pow_central_of_ne hQp hjj hj'j' hj'1 hjne
  set Z : S := (T' * (W' * T' * W'⁻¹)) ^ n with hZ
  have hZbar : (j * j') ^ n = (Z : S ⧸ N) := by
    rw [hj, hj', ← QuotientGroup.mk_mul, ← QuotientGroup.mk_pow]
  rw [hZbar] at hz1 hzj hzt
  set z : G := (Z : G) with hz
  have hzdef : z = (t * (w * t * w⁻¹)) ^ n := by
    rw [hz, hZ, Subgroup.coe_pow]
    rfl
  have hzS₀ : z ∈ U₁ ⊔ T := by
    refine h.mem_sup_of_mul_conj_mem hSp hES Z.2 ?_
    have h1 : ((T' * (Z * T' * Z⁻¹) : S) : S ⧸ N) = 1 := by
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv,
        ← hj, ← hzj, mul_assoc j, mul_inv_cancel, mul_one, hjj]
    exact (heq1 _).mp h1
  have hzV : z ∉ U₁ ⊔ zpowers t := by
    intro hzV
    obtain ⟨e, he, h1 | h1⟩ := Endings.exists_eq_or_eq_mul_of_mem_sup_zpowers h.t_mul_t
      h.zpowers_le_normalizer hzV
    · apply hz1
      rw [heq1]
      show z ∈ U₁
      rw [← h1]
      exact he
    · apply hzt
      rw [heq]
      show z⁻¹ * t ∈ U₁
      rw [← h1, show (e * t)⁻¹ * t = t⁻¹ * e⁻¹ * t⁻¹⁻¹ by group]
      exact (mem_normalizer_iff.mp (inv_mem h.t_mem_normalizer) e⁻¹).mp (inv_mem he)
  have hCU : T ⊓ L ⊓ centralizer ({w} : Set G) ≤ T ⊓ L ⊓ centralizer ({z} : Set G) := by
    intro u hu
    obtain ⟨huU, huw⟩ := mem_inf.mp hu
    have hut : Commute u t :=
      mem_centralizer_singleton_iff.mp (h.le_centralizer (mem_inf.mp huU).1)
    have huw' : Commute u w := mem_centralizer_singleton_iff.mp huw
    have hut' : Commute u (w * t * w⁻¹) := (huw'.mul_right hut).mul_right huw'.inv_right
    refine mem_inf.mpr ⟨huU, mem_centralizer_singleton_iff.mpr ?_⟩
    rw [hzdef]
    exact ((hut.mul_right hut').pow_right n).eq
  have h1 := h.card_inf_centralizer_sq_le hzS₀ hzV
  have h2 := card_le_of_le hCU
  have h3 := h.card_le_card_inf_mul (K := U₁ ⊓ centralizer ({w} : Set G)) (M := T ⊓ L)
    inf_le_left fun k hk => h.result.comm_mem k (mem_inf.mp hk).1
  have h4 : Nat.card (U₁ ⊓ centralizer ({w} : Set G) ⊓ (T ⊓ L) : Subgroup G) ≤
      Nat.card (T ⊓ L ⊓ centralizer ({w} : Set G) : Subgroup G) :=
    card_le_of_le fun x hx => mem_inf.mpr ⟨(mem_inf.mp hx).2, (mem_inf.mp (mem_inf.mp hx).1).2⟩
  rw [h.card_U] at h3
  calc Nat.card (U₁ ⊓ centralizer ({w} : Set G) : Subgroup G) ^ 2
      ≤ (Nat.card (T ⊓ L ⊓ centralizer ({w} : Set G) : Subgroup G) * 2 ^ f) ^ 2 :=
        Nat.pow_le_pow_left (h3.trans (Nat.mul_le_mul_right _ h4)) 2
    _ = Nat.card (T ⊓ L ⊓ centralizer ({w} : Set G) : Subgroup G) ^ 2 * (2 ^ f) ^ 2 := by ring
    _ ≤ Nat.card (T ⊓ L ⊓ centralizer ({z} : Set G) : Subgroup G) ^ 2 * (2 ^ f) ^ 2 :=
        Nat.mul_le_mul_right _ (Nat.pow_le_pow_left h2 2)
    _ ≤ 2 ^ f * (2 ^ f) ^ 2 := Nat.mul_le_mul_right _ h1
    _ = (2 ^ f) ^ 3 := by ring

theorem exists_isSylowOf_le_normalizer :
    ∃ S : Subgroup G, IsSylowOf 2 S (normalizer (U₁ : Set G)) ∧ U₁ ⊔ T ≤ S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set K := normalizer (U₁ : Set G)
  have hP : IsPGroup 2 ((U₁ ⊔ T).subgroupOf K) := h.isPGroup_sup.comap_subtype
  obtain ⟨Q, hQ⟩ := hP.exists_le_sylow
  refine ⟨(Q : Subgroup K).map K.subtype, ⟨Q, rfl⟩, fun x hx => ?_⟩
  exact ⟨⟨x, h.sup_le_normalizer hx⟩, hQ (mem_subgroupOf.mpr hx), rfl⟩

theorem relIndex_sup_eq : U₁.relIndex (U₁ ⊔ T) = (T ⊓ L).relIndex T := by
  have : (U₁.subgroupOf T).Normal := normal_subgroupOf_of_le_normalizer h.T_le_normalizer
  have : (U₁.subgroupOf (T ⊔ U₁)).Normal :=
    normal_subgroupOf_sup_of_le_normalizer h.T_le_normalizer
  have h1 : U₁.relIndex T = U₁.relIndex (T ⊔ U₁) := Nat.card_congr
    (QuotientGroup.quotientInfEquivProdNormalizerQuotient T U₁ h.T_le_normalizer).toEquiv
  rw [sup_comm, ← h1, ← inf_relIndex_right, h.inf_T]

theorem relIndex_U_V : (T ⊓ L).relIndex (T ⊓ L ⊔ zpowers t) = 2 := by
  obtain ⟨-, htt, htU, -, -, -, -, -, -, -, -, -, -, -, hTU, -⟩ :=
    Endings.psl2_ending_facts h.gold h.setting
  have htN : zpowers t ≤ normalizer ((T ⊓ L : Subgroup G) : Set G) := zpowers_le.mpr (hTU h.mem_T)
  apply le_antisymm
  · refine relIndex_le_two_of_mul_mem fun a ha b hb haU hbU => ?_
    obtain ⟨u, hu, rfl | rfl⟩ := Endings.exists_eq_or_eq_mul_of_mem_sup_zpowers htt htN ha
    · exact absurd hu haU
    obtain ⟨u', hu', rfl | rfl⟩ := Endings.exists_eq_or_eq_mul_of_mem_sup_zpowers htt htN hb
    · exact absurd hu' hbU
    have htu : t * u' * t⁻¹ ∈ T ⊓ L := (mem_normalizer_iff.mp (hTU h.mem_T) u').mp hu'
    rw [show u * t * (u' * t) = u * (t * u' * t⁻¹) * (t * t) by group, htt, mul_one]
    exact mul_mem hu htu
  · have h1 : (T ⊓ L).relIndex (T ⊓ L ⊔ zpowers t) ≠ 1 := by
      rw [Ne, relIndex_eq_one]
      exact fun hle => htU (hle (mem_sup_right (mem_zpowers t)))
    have h2 := relIndex_mul_card (T ⊓ L) (T ⊓ L ⊔ zpowers t)
    have h3 : 0 < Nat.card (T ⊓ L ⊔ zpowers t : Subgroup G) := Nat.card_pos
    have h4 : (T ⊓ L).relIndex (T ⊓ L ⊔ zpowers t) ≠ 0 := by
      intro h0
      rw [h0, zero_mul] at h2
      omega
    omega

theorem relIndex_U_T : (T ⊓ L).relIndex T = 2 * (T ⊓ L ⊔ zpowers t).relIndex T := by
  rw [← h.relIndex_U_V, relIndex_mul_relIndex (T ⊓ L) (T ⊓ L ⊔ zpowers t) T le_sup_left
    (sup_le inf_le_left (zpowers_le.mpr h.mem_T))]

theorem relIndex_eq_two_or_four_le (hx : ∃ x ∈ U₁ ⊔ T, x * x = 1 ∧ x ∉ U₁ ⊔ zpowers t) :
    (T ⊓ L ⊔ zpowers t).relIndex T = 2 ∨ 4 ≤ (T ⊓ L ⊔ zpowers t).relIndex T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨x, hx, -, hxV⟩ := hx
  obtain ⟨e, -, p, hp, -, hpV⟩ := h.exists_mul_eq_of_not_mem hx hxV
  have h1 : (T ⊓ L ⊔ zpowers t).relIndex T ≠ 1 := by
    rw [Ne, relIndex_eq_one]
    exact fun hle => hpV (hle hp)
  obtain ⟨a, ha⟩ := (h.isPGroup_sup.to_le (le_sup_right : T ≤ U₁ ⊔ T)).exists_card_eq
  obtain ⟨b, -, hb⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp
    (ha ▸ relIndex_dvd_card (T ⊓ L ⊔ zpowers t) T)
  rw [hb] at h1 ⊢
  rcases b with _ | _ | b
  · exact absurd (pow_zero 2) h1
  · exact Or.inl (pow_one 2)
  · right
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (b + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)

theorem mul_self_mem_of_relIndex_eq_two (hTV : (T ⊓ L ⊔ zpowers t).relIndex T = 2)
    (hx : ∃ x ∈ U₁ ⊔ T, x * x = 1 ∧ x ∉ U₁ ⊔ zpowers t) {w : G} (hw : w ∈ U₁ ⊔ T) :
    w * w ∈ U₁ := by
  obtain ⟨-, htt, -, -, hU2, -, -, -, -, -, -, -, -, -, hTU, -⟩ :=
    Endings.psl2_ending_facts h.gold h.setting
  have htN : zpowers t ≤ normalizer ((T ⊓ L : Subgroup G) : Set G) := zpowers_le.mpr (hTU h.mem_T)
  obtain ⟨x, hx, hxx, hxV⟩ := hx
  obtain ⟨e₀, he₀, τ, hτ, rfl, hτV⟩ := h.exists_mul_eq_of_not_mem hx hxV
  have hτ2 := h.mul_self_mem_of_mul_mul_eq_one he₀ hτ hxx
  have hcommU : ∀ u ∈ T ⊓ L, u * t = t * u := fun u hu =>
    mem_centralizer_singleton_iff.mp (h.le_centralizer (mem_inf.mp hu).1)
  have hvτ : ∀ v ∈ T ⊓ L ⊔ zpowers t, v * (τ * v * τ⁻¹) ∈ T ⊓ L := by
    intro v hv
    have hτt : τ * t = t * τ := mem_centralizer_singleton_iff.mp (h.le_centralizer hτ)
    obtain ⟨u, hu, rfl | rfl⟩ := Endings.exists_eq_or_eq_mul_of_mem_sup_zpowers htt htN hv
    · exact mul_mem hu ((mem_normalizer_iff.mp (hTU hτ) u).mp hu)
    · have hu' : τ * u * τ⁻¹ ∈ T ⊓ L := (mem_normalizer_iff.mp (hTU hτ) u).mp hu
      have e1 : u * t * (τ * (u * t) * τ⁻¹) = u * (τ * u * τ⁻¹) * (t * t) := by
        calc u * t * (τ * (u * t) * τ⁻¹) = u * t * (τ * u * τ⁻¹) * (τ * t * τ⁻¹) := by group
          _ = u * t * (τ * u * τ⁻¹) * t := by rw [hτt]; group
          _ = u * (t * (τ * u * τ⁻¹)) * t := by group
          _ = u * ((τ * u * τ⁻¹) * t) * t := by rw [hcommU _ hu']
          _ = u * (τ * u * τ⁻¹) * (t * t) := by group
      rw [e1, htt, mul_one]
      exact mul_mem hu hu'
  have hpT : ∀ p ∈ T, p * p ∈ T ⊓ L := by
    intro p hp
    by_cases hpV : p ∈ T ⊓ L ⊔ zpowers t
    · obtain ⟨u, hu, rfl | rfl⟩ := Endings.exists_eq_or_eq_mul_of_mem_sup_zpowers htt htN hpV
      · rw [hU2 u hu]
        exact one_mem _
      · rw [show u * t * (u * t) = u * (t * u) * t by group, ← hcommU u hu,
          show u * (u * t) * t = (u * u) * (t * t) by group, hU2 u hu, htt, mul_one]
        exact one_mem _
    · have hmem : (⟨p, hp⟩ : T) * (⟨τ, hτ⟩ : T)⁻¹ ∈ (T ⊓ L ⊔ zpowers t).subgroupOf T := by
        rw [mul_mem_iff_of_index_two hTV, mem_subgroupOf, inv_mem_iff, mem_subgroupOf]
        exact iff_of_false hpV hτV
      rw [mem_subgroupOf] at hmem
      set v := p * τ⁻¹ with hv
      have hv' : (v : G) ∈ T ⊓ L ⊔ zpowers t := hmem
      have e1 : p * p = v * (τ * v * τ⁻¹) * (τ * τ) := by rw [hv]; group
      rw [e1]
      exact mul_mem (hvτ v hv') hτ2
  obtain ⟨e, he, p, hp, rfl⟩ := Endings.exists_mul_eq_of_mem_sup h.T_le_normalizer hw
  have hpe : p * e * p⁻¹ ∈ U₁ := (mem_normalizer_iff.mp (h.T_le_normalizer hp) e).mp he
  rw [show e * p * (e * p) = e * (p * e * p⁻¹) * (p * p) by group]
  exact mul_mem (mul_mem he hpe) (h.U_le (hpT p hp))

end Hyp

end GMS43

end CFSG.SeitzReduction.RankOne
