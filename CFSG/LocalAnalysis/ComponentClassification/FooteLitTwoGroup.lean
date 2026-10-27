module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB5bLemma512
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitElemAb
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitLemma41

public section

namespace CFSG.ComponentClassification.FooteLit

open CFSG Subgroup

variable {G : Type} [Group G] [Finite G]

theorem exists_card_eight_of_le_pRank {H : Subgroup G} (h3 : 3 ≤ CFSG.pRank 2 ↥H) :
    ∃ F : Subgroup G, F ≤ H ∧ (∀ x ∈ F, x ^ 2 = 1) ∧ Nat.card F = 8 := by
  have h1 : 3 ≤ CFSG.Open.pRank 2 H := by
    rwa [SectionRank.pRank_eq_open_pRank_top, ← SectionRank.pRank_eq_pRank_top_subgroup] at h3
  obtain ⟨E, hEH, hE, hEcard⟩ := SectionRank.exists_pRank one_lt_two H
  have hE8 : 8 ≤ Nat.card E := by
    rw [hEcard]
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ CFSG.Open.pRank 2 H := Nat.pow_le_pow_right (by norm_num) h1
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨F, hF⟩ := Sylow.exists_subgroup_card_pow_prime (G := E) 2
    (show 2 ^ 3 ∣ Nat.card E by
      rw [hEcard]
      exact pow_dvd_pow 2 (by
        have := h1
        omega))
  refine ⟨F.map E.subtype, (map_subtype_le _).trans hEH, ?_, ?_⟩
  · rintro _ ⟨x, -, rfl⟩
    exact hE.2 x x.2
  · rw [Subgroup.card_map_of_injective E.subtype_injective, hF]
    norm_num

theorem card_inf_centralizer_ne_four (hST : GSThmB.SuzukiTausskyInput) {Q : Subgroup G}
    (hQ : IsPGroup 2 Q) {F : Subgroup G} (hFQ : F ≤ Q) (hF2 : ∀ x ∈ F, x ^ 2 = 1)
    (hF8 : Nat.card F = 8) {x : G} (hxQ : x ∈ Q) (hx : orderOf x = 2) :
    Nat.card ↥(Q ⊓ centralizer ({x} : Set G)) ≠ 4 := by
  intro h4
  have hQ8 : 8 ≤ Nat.card Q := hF8 ▸ Subgroup.card_le_of_le hFQ
  have hx' : orderOf (⟨x, hxQ⟩ : Q) = 2 := by rw [Subgroup.orderOf_mk, hx]
  have hc : Nat.card (centralizer ({(⟨x, hxQ⟩ : Q)} : Set Q)) = 4 := by
    rw [← h4]
    have e : (centralizer ({(⟨x, hxQ⟩ : Q)} : Set Q)).map Q.subtype =
        Q ⊓ centralizer ({x} : Set G) := by
      ext y
      simp only [mem_map, mem_inf, mem_centralizer_singleton_iff]
      constructor
      · rintro ⟨⟨y, hyQ⟩, hy, rfl⟩
        exact ⟨hyQ, congrArg Subtype.val hy⟩
      · rintro ⟨hyQ, hy⟩
        exact ⟨⟨y, hyQ⟩, Subtype.ext hy, rfl⟩
    rw [← e, Subgroup.card_map_of_injective Q.subtype_injective]
  obtain ⟨p, r, -, hp, -, -⟩ := hST Q hQ hQ8 ⟨x, hxQ⟩ hx' hc
  have hind : (zpowers p).index ≤ 2 := by
    have h1 := (zpowers p).card_mul_index
    rw [Nat.card_zpowers, ← hp] at h1
    have hpos : 0 < orderOf p := orderOf_pos p
    have : (zpowers p).index = 2 := by
      have h2 : orderOf p * (zpowers p).index = orderOf p * 2 := by rw [h1]; ring
      exact Nat.eq_of_mul_eq_mul_left hpos h2
    omega
  have hrank := CFSG.LocalAnalysis.ComponentInitial.cyclic_index_two_rank_bound
    (H := zpowers p) inferInstance hind
  have hF : CFSG.Open.IsElemAbelian 2 (F.subgroupOf Q) := by
    refine ⟨⟨⟨fun a b => Subtype.ext (Subtype.ext ?_)⟩⟩, fun a ha => Subtype.ext ?_⟩
    · exact commute_of_sq_eq_one hF2 a.2 b.2
    · rw [SubgroupClass.coe_pow, OneMemClass.coe_one]
      exact hF2 _ ha
  have hFcard : Nat.card (F.subgroupOf Q) = 2 ^ 3 := by
    rw [← Nat.card_congr (subgroupOfEquivOfLe hFQ).symm.toEquiv, hF8]
    norm_num
  have h3 := SectionRank.le_pRank one_lt_two (le_top : F.subgroupOf Q ≤ ⊤) hF hFcard
  rw [← SectionRank.pRank_eq_open_pRank_top] at h3
  omega

omit [Finite G] in
theorem sq_mem_centralizer_of_isKleinFour {U : Subgroup G} (hU : IsKleinFour U) {y : G}
    (hyU : y ∈ normalizer (U : Set G)) (hy : ∃ k : ℕ, orderOf y = 2 ^ k) :
    y ^ 2 ∈ centralizer (U : Set G) := by
  obtain ⟨k, hk⟩ := hy
  rw [mem_centralizer_iff]
  intro u hu
  by_cases hu1 : u = 1
  · rw [hu1, mul_one, one_mul]
  set u' := y * u * y⁻¹ with hu'
  have hu'U : u' ∈ U := (mem_normalizer_iff.mp hyU u).mp hu
  by_cases huu : u' = u
  · have h1 : y * u = u * y := by
      calc y * u = y * u * y⁻¹ * y := by group
        _ = u * y := by rw [← hu', huu]
    calc u * y ^ 2 = u * y * y := by rw [sq, mul_assoc]
      _ = y * u * y := by rw [h1]
      _ = y * (u * y) := by rw [mul_assoc]
      _ = y * (y * u) := by rw [h1]
      _ = y ^ 2 * u := by rw [sq, mul_assoc]
  have hu'1 : u' ≠ 1 := fun h1 => hu1 (by
    calc u = y⁻¹ * (y * u * y⁻¹) * y := by group
      _ = 1 := by rw [← hu', h1]; group)
  set u'' := y * u' * y⁻¹ with hu''
  have hu''U : u'' ∈ U := (mem_normalizer_iff.mp hyU u').mp hu'U
  have hu''u : u'' = u := by
    by_contra hne
    have hne' : u'' ≠ u' := fun h1 => huu (by
      have h2 : y * u' = u' * y := by
        calc y * u' = y * u' * y⁻¹ * y := by group
          _ = u' * y := by rw [← hu'', h1]
      calc u' = y⁻¹ * u' * y := by rw [mul_assoc, ← h2]; group
        _ = u := by rw [hu']; group)
    have hu''1 : u'' ≠ 1 := fun h1 => hu'1 (by
      calc u' = y⁻¹ * (y * u' * y⁻¹) * y := by group
        _ = 1 := by rw [← hu'', h1]; group)
    have hcases := mem_of_isKleinFour hU hu hu'U hu''U hu1 hu'1 (Ne.symm huu)
    rcases hcases with h1 | h1 | h1 | h1
    · exact hu''1 h1
    · exact hne h1
    · exact hne' h1
    ·
      have hcomm : u * u' = u' * u :=
        commute_of_sq_eq_one (fun x hx => sq_eq_one_of_isKleinFour hU hx) hu hu'U
      have h5 := sq_eq_one_of_isKleinFour hU hu'U
      have h3 : y * u'' * y⁻¹ = u := by
        have e1 : y * u'' * y⁻¹ = u' * u'' := by
          calc y * u'' * y⁻¹ = y * (u * u') * y⁻¹ := by rw [h1]
            _ = (y * u * y⁻¹) * (y * u' * y⁻¹) := by group
            _ = u' * u'' := rfl
        rw [e1, h1, ← mul_assoc, ← hcomm, mul_assoc, ← sq, h5, mul_one]
      have h6 : y ^ 3 * u = u * y ^ 3 := by
        have e2 : y ^ 3 * u * (y ^ 3)⁻¹ = u := by
          calc y ^ 3 * u * (y ^ 3)⁻¹ = y * (y * (y * u * y⁻¹) * y⁻¹) * y⁻¹ := by
                rw [show y ^ 3 = y * y * y by rw [pow_succ, pow_succ, pow_one]]; group
            _ = y * u'' * y⁻¹ := rfl
            _ = u := h3
        calc y ^ 3 * u = y ^ 3 * u * (y ^ 3)⁻¹ * y ^ 3 := by rw [inv_mul_cancel_right]
          _ = u * y ^ 3 := by rw [e2]
      have hcop : Nat.Coprime 3 (orderOf y) := by
        rw [hk]
        exact Nat.Coprime.pow_right _ (by norm_num)
      obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime hcop
      have hC : y ^ 3 ∈ centralizer ({u} : Set G) := mem_centralizer_singleton_iff.mpr h6
      have hyu : y * u = u * y := by
        have h7 : (y ^ 3) ^ m ∈ centralizer ({u} : Set G) := pow_mem hC m
        rw [hm] at h7
        exact mem_centralizer_singleton_iff.mp h7
      exact huu (by rw [hu', hyu]; group)
  have h8 : y ^ 2 * u * (y ^ 2)⁻¹ = u := by
    calc y ^ 2 * u * (y ^ 2)⁻¹ = y * (y * u * y⁻¹) * y⁻¹ := by rw [sq]; group
      _ = u := by rw [← hu', ← hu'', hu''u]
  calc u * y ^ 2 = y ^ 2 * u * (y ^ 2)⁻¹ * y ^ 2 := by rw [h8]
    _ = y ^ 2 * u := by rw [inv_mul_cancel_right]

theorem exists_sq_eq_of_unique_involution {X : Subgroup G} (hX : IsPGroup 2 X)
    (h4 : 4 ≤ Nat.card X) {t : G}
    (huniq : ∀ x ∈ X, orderOf x = 2 → x = t) : ∃ y ∈ X, y ^ 2 = t := by
  obtain ⟨y, hyX, hy4⟩ : ∃ y ∈ X, 4 ≤ orderOf y := by
    by_contra hall
    push Not at hall
    have hsq : ∀ x ∈ X, x ^ 2 = 1 := by
      intro x hx
      obtain ⟨n, hn⟩ := hX ⟨x, hx⟩
      have h1 : orderOf x ∣ 2 ^ n := by
        rw [← Subgroup.orderOf_mk x hx]
        exact orderOf_dvd_of_pow_eq_one hn
      obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h1
      have hlt := hall x hx
      have hm1 : m ≤ 1 := by
        by_contra h2
        have : 2 ^ 2 ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) (by omega)
        omega
      rw [← orderOf_dvd_iff_pow_eq_one, hm]
      exact pow_dvd_pow 2 hm1
    obtain ⟨W, hW, hWX⟩ := exists_isKleinFour_le hsq h4
    obtain ⟨a, ha, ha1, hat⟩ := exists_ne_of_isKleinFour hW t
    exact hat (huniq a (hWX ha) (orderOf_eq_prime (sq_eq_one_of_isKleinFour hW ha) ha1))
  obtain ⟨n, hn⟩ := hX ⟨y, hyX⟩
  have hdvd : orderOf y ∣ 2 ^ n := by
    rw [← Subgroup.orderOf_mk y hyX]
    exact orderOf_dvd_of_pow_eq_one hn
  obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  have hm2 : 2 ≤ m := by
    by_contra h2
    have : 2 ^ m ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  refine ⟨y ^ (2 ^ (m - 2)), pow_mem hyX _, ?_⟩
  have hinv : orderOf (y ^ (2 ^ (m - 1))) = 2 := by
    rw [orderOf_pow_of_dvd (pow_pos (by norm_num) _).ne'
      (by rw [hm]; exact pow_dvd_pow 2 (by omega)), hm, Nat.pow_div (by omega) (by norm_num),
      show m - (m - 1) = 1 by omega, pow_one]
  rw [← huniq _ (pow_mem hyX _) hinv, ← pow_mul, ← pow_succ, show m - 2 + 1 = m - 1 by omega]

theorem exists_card_eight_le_sup {F W : Subgroup G} (hF2 : ∀ x ∈ F, x ^ 2 = 1)
    (hF8 : Nat.card F = 8) (hW : IsKleinFour W) (hFW : ∀ f ∈ F, ∀ w ∈ W, f * w = w * f) :
    ∃ A : Subgroup G, (∀ x ∈ A, x ^ 2 = 1) ∧ Nat.card A = 8 ∧ W ≤ A ∧ A ≤ W ⊔ F := by
  obtain ⟨f, hf, hfW⟩ : ∃ f ∈ F, f ∉ W := by
    by_contra hall
    push Not at hall
    have h1 := Subgroup.card_le_of_le (fun x hx => hall x hx : F ≤ W)
    rw [hF8, hW.card_four] at h1
    omega
  obtain ⟨h2, h8⟩ := sup_zpowers_spec hW hfW (hF2 f hf) fun w hw => (hFW f hf w hw).symm
  exact ⟨W ⊔ zpowers f, h2, h8, le_sup_left, sup_le_sup_left (zpowers_le.mpr hf) _⟩

end CFSG.ComponentClassification.FooteLit
