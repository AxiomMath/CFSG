module

public import CFSG.GroupTheory.ABGLocalTools.CoreLemmas
public import CFSG.CGT.PushingUpLit.LIT.Foote.TightAux
import CFSG.GroupTheory.ElemAbelianClosure

public section

namespace CFSG.CGT.PushingUpLit.LIT.Foote.L54

open CFSG CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem isPGroup_zpowers {y : G} (h2 : ∃ n : ℕ, y ^ 2 ^ n = 1) :
    IsPGroup 2 (Subgroup.zpowers y) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn⟩ := h2
  have : orderOf y ∣ 2 ^ n := orderOf_dvd_of_pow_eq_one hn
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 this
  exact IsPGroup.of_card (n := j) (by rw [Nat.card_zpowers, hj])

theorem exists_mem_normalizer_not_mem {H K : Subgroup G} (hH : IsPGroup 2 H) (hKH : K ≤ H)
    (hne : K ≠ H) : ∃ y ∈ H, y ∈ Subgroup.normalizer (K : Set G) ∧ y ∉ K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Group.IsNilpotent ↥H := hH.isNilpotent
  have hnc : NormalizerCondition ↥H := Group.normalizerCondition_of_isNilpotent (G := ↥H)
  set K' : Subgroup ↥H := K.subgroupOf H with hK'
  have hlt : K' < ⊤ := by
    refine lt_of_le_of_ne le_top fun htop => hne (le_antisymm hKH fun x hx => ?_)
    have : (⟨x, hx⟩ : ↥H) ∈ K' := by rw [htop]; trivial
    exact this
  obtain ⟨y, hyN, hyK⟩ := IsConcreteLE.exists_of_lt (hnc K' hlt)
  refine ⟨y, y.2, ?_, fun hy => hyK hy⟩
  have hsub : y ∈ (Subgroup.normalizer (K : Set G)).subgroupOf H := by
    rw [Subgroup.subgroupOf_normalizer_eq hKH]
    exact hyN
  exact Subgroup.mem_subgroupOf.mp hsub

omit [Finite G] in
theorem exists_isSylowOf_ge {A K : Subgroup G} (hA : IsPGroup 2 A) (hAK : A ≤ K) :
    ∃ S : Subgroup G, IsSylowOf 2 S K ∧ A ≤ S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hA' : IsPGroup 2 (A.subgroupOf K) := hA.comap_subtype
  obtain ⟨Q, hQ⟩ := hA'.exists_le_sylow
  refine ⟨(Q : Subgroup K).map K.subtype, ⟨Q, rfl⟩, fun x hx => ?_⟩
  have hx' : (⟨x, hAK hx⟩ : ↥K) ∈ A.subgroupOf K := hx
  exact ⟨⟨x, hAK hx⟩, hQ hx', rfl⟩

theorem exists_invariant_sylow {X T : Subgroup G} (hT : IsPGroup 2 T)
    (hTX : T ≤ Subgroup.normalizer (X : Set G)) :
    ∃ Q : Subgroup G, IsSylowOf 2 Q X ∧ T ≤ Subgroup.normalizer (Q : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hXT : X ⊔ T ≤ Subgroup.normalizer (X : Set G) :=
    sup_le Subgroup.le_normalizer hTX
  obtain ⟨S, hS, hTS⟩ := exists_isSylowOf_ge hT (le_sup_right : T ≤ X ⊔ T)
  refine ⟨S ⊓ X, hS.inf_of_le_normalizer le_sup_left hXT, fun s hs => ?_⟩
  rw [Subgroup.mem_normalizer_iff]
  intro x
  have hsS : s ∈ S := hTS hs
  have h1 := (Subgroup.mem_normalizer_iff.1 (Subgroup.le_normalizer (H := S) hsS)) x
  have h2 := (Subgroup.mem_normalizer_iff.1 (hTX hs)) x
  simp only [Subgroup.mem_inf]
  rw [h1, h2]

theorem exists_conj_mem_sylow {X Q : Subgroup G} (hQ : IsSylowOf 2 Q X) {a : G} (haX : a ∈ X)
    (ha2 : ∃ n : ℕ, a ^ 2 ^ n = 1) : ∃ x ∈ X, x * a * x⁻¹ ∈ Q := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S, hS, haS⟩ := exists_isSylowOf_ge (isPGroup_zpowers ha2)
    (Subgroup.zpowers_le.2 haX)
  obtain ⟨k, hk, hconj⟩ := hQ.exists_mem_conj hS
  refine ⟨k⁻¹, X.inv_mem hk, ?_⟩
  have := (hconj a).1 (haS (Subgroup.mem_zpowers a))
  simpa using this

theorem exists_involution_of_even {K : Subgroup G} (hK : Even (Nat.card K)) :
    ∃ u ∈ K, u ≠ 1 ∧ u * u = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' (G := ↥K) 2 (even_iff_two_dvd.1 hK)
  refine ⟨(u : G), u.2, fun h => ?_, ?_⟩
  · have : u = 1 := Subtype.ext h
    rw [this, orderOf_one] at hu
    omega
  · have h2 : u ^ 2 = 1 := hu ▸ pow_orderOf_eq_one u
    have := congrArg Subtype.val h2
    simpa [pow_two] using this

theorem exists_involution_of_isPGroup {T : Subgroup G} (hT : IsPGroup 2 T) (h1 : T ≠ ⊥) :
    ∃ u ∈ T, u ≠ 1 ∧ u * u = 1 :=
  (exists_involution_of_even (even_card_of_isPGroup hT h1 le_rfl)).imp fun u hu =>
    ⟨(hu.1 : u ∈ T), hu.2.1, hu.2.2⟩

theorem exists_inf_ne_bot_of_even {T P : Subgroup G} (hT : IsSylowOf 2 T P) {x : G}
    (hx : Even (Nat.card ↥(P ⊓ rightConjugate P x))) :
    ∃ p₁ ∈ P, ∃ p₂ ∈ P, T ⊓ rightConjugate T (p₂ * x * p₁) ≠ ⊥ := by
  obtain ⟨u, hu, hu1, hu2⟩ := exists_involution_of_even hx
  have huP : u ∈ P := (Subgroup.mem_inf.1 hu).1
  have huPx : x * u * x⁻¹ ∈ P := (mem_rightConjugate_iff _ _ _).1 (Subgroup.mem_inf.1 hu).2
  have hu2' : ∃ n : ℕ, u ^ 2 ^ n = 1 := ⟨1, by simpa [pow_two] using hu2⟩
  have hv2 : ∃ n : ℕ, (x * u * x⁻¹) ^ 2 ^ n = 1 :=
    ⟨1, by rw [pow_one, pow_two]; calc x * u * x⁻¹ * (x * u * x⁻¹) = x * (u * u) * x⁻¹ := by group
      _ = 1 := by rw [hu2]; group⟩
  obtain ⟨k, hk, hkT⟩ := exists_conj_mem_sylow hT huP hu2'
  obtain ⟨k₂, hk₂, hk₂T⟩ := exists_conj_mem_sylow hT huPx hv2
  refine ⟨k⁻¹, P.inv_mem hk, k₂, hk₂, fun hbot => ?_⟩
  have hmem : k * u * k⁻¹ ∈ T ⊓ rightConjugate T (k₂ * x * k⁻¹) := by
    refine Subgroup.mem_inf.2 ⟨hkT, ?_⟩
    rw [mem_rightConjugate_iff]
    have e : k₂ * x * k⁻¹ * (k * u * k⁻¹) * (k₂ * x * k⁻¹)⁻¹ = k₂ * (x * u * x⁻¹) * k₂⁻¹ := by
      group
    rw [e]
    exact hk₂T
  rw [hbot, Subgroup.mem_bot] at hmem
  apply hu1
  have : u = k⁻¹ * (k * u * k⁻¹) * k := by group
  rw [this, hmem]
  group

theorem isSylowOf_sup_of_odd {T D : Subgroup G} (hT : IsPGroup 2 T)
    (hTD : T ≤ Subgroup.normalizer (D : Set G)) (hD : Odd (Nat.card D)) :
    IsSylowOf 2 T (T ⊔ D) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [isSylowOf_iff]
  refine ⟨le_sup_left, hT, ?_⟩
  set K := T ⊔ D with hK
  have hDK : D ≤ K := le_sup_right
  have hTK : T ≤ K := le_sup_left
  have hKN : K ≤ Subgroup.normalizer (D : Set G) := sup_le hTD Subgroup.le_normalizer
  have hnorm : (D.subgroupOf K).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hDK).mpr hKN
  have h1 := relIndex_sup_eq_relIndex_of_normal (D.subgroupOf K) (T.subgroupOf K)
  have htop : D.subgroupOf K ⊔ T.subgroupOf K = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hDK hTK, sup_comm, ← hK, Subgroup.subgroupOf_self]
  rw [htop, Subgroup.relIndex_top_right] at h1
  have h2 : (T.subgroupOf K).relIndex (D.subgroupOf K) ∣ Nat.card (D.subgroupOf K) :=
    Subgroup.relIndex_dvd_card _ _
  have h3 : Nat.card (D.subgroupOf K) = Nat.card D :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDK).toEquiv
  intro hdvd
  have hrel : T.relIndex K = (T.subgroupOf K).index := rfl
  rw [hrel, h1] at hdvd
  rw [h3] at h2
  exact (Nat.not_even_iff_odd.2 hD) (even_iff_two_dvd.2 (hdvd.trans h2))

omit [Finite G] in
theorem isElemAbelian_sup {A B : Subgroup G} (hA : CFSG.Open.IsElemAbelian 2 A)
    (hB : CFSG.Open.IsElemAbelian 2 B) (h : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) :
    CFSG.Open.IsElemAbelian 2 (A ⊔ B) := CFSG.Open.IsElemAbelian.sup_of_commute hA hB h

end CFSG.CGT.PushingUpLit.LIT.Foote.L54
