module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TwelveNotLeGraphSymCore

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TwelveNotLe.Sym

open CFSG.Open Subgroup

variable {R : Type*} [Group R]

theorem inv_mul_mem_of_card_le_two_mul [Finite R] {T K : Subgroup R} (hKT : K ≤ T)
    (hcard : Nat.card T ≤ 2 * Nat.card K) {s s' : R} (hs : s ∈ T) (hs' : s' ∈ T)
    (hsK : s ∉ K) (hs'K : s' ∉ K) : s⁻¹ * s' ∈ K := by
  classical
  set K' : Subgroup ↥T := K.subgroupOf T with hK'
  have hKcard : Nat.card K' = Nat.card K :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKT).toEquiv
  have hmul : K'.index * Nat.card K' = Nat.card T := Subgroup.index_mul_card K'
  have hKpos : 0 < Nat.card K := Nat.card_pos
  have hidx_le : K'.index ≤ 2 := by
    by_contra hgt
    push Not at hgt
    have : 3 * Nat.card K ≤ K'.index * Nat.card K' := by
      rw [hKcard]
      exact Nat.mul_le_mul_right _ hgt
    omega
  have hidx_ne : K'.index ≠ 1 := by
    intro h1
    have htop : K' = ⊤ := Subgroup.index_eq_one.1 h1
    apply hsK
    have : (⟨s, hs⟩ : ↥T) ∈ K' := by rw [htop]; trivial
    exact Subgroup.mem_subgroupOf.1 this
  have hidx : K'.index = 2 := by
    have hpos : 0 < K'.index := Nat.pos_of_ne_zero (fun h0 => by
      rw [h0] at hmul
      have : 0 < Nat.card T := Nat.card_pos
      omega)
    omega
  have hq : Nat.card (↥T ⧸ K') = 2 := by
    rw [← Subgroup.index_eq_card]
    exact hidx
  obtain ⟨y, hy, huniq⟩ := (Nat.card_eq_two_iff' ((1 : ↥T) : ↥T ⧸ K')).1 hq
  have hx : ((⟨s, hs⟩ : ↥T) : ↥T ⧸ K') ≠ ((1 : ↥T) : ↥T ⧸ K') := by
    intro h
    rw [QuotientGroup.eq] at h
    apply hsK
    have h' : (⟨s, hs⟩ : ↥T)⁻¹ * 1 ∈ K' := h
    have h'' : (⟨s, hs⟩ : ↥T) ∈ K' := by
      simpa using K'.inv_mem h'
    exact Subgroup.mem_subgroupOf.1 h''
  have hx' : ((⟨s', hs'⟩ : ↥T) : ↥T ⧸ K') ≠ ((1 : ↥T) : ↥T ⧸ K') := by
    intro h
    rw [QuotientGroup.eq] at h
    apply hs'K
    have h' : (⟨s', hs'⟩ : ↥T)⁻¹ * 1 ∈ K' := h
    have h'' : (⟨s', hs'⟩ : ↥T) ∈ K' := by
      simpa using K'.inv_mem h'
    exact Subgroup.mem_subgroupOf.1 h''
  have hxy := (huniq _ hx).trans (huniq _ hx').symm
  rw [QuotientGroup.eq] at hxy
  have h3 : (⟨s, hs⟩ : ↥T)⁻¹ * ⟨s', hs'⟩ ∈ K' := hxy
  exact Subgroup.mem_subgroupOf.1 h3

theorem not_mem_of_normal_two {X H K : Subgroup R} (hX : IsSymThree X) (hXH : X ≤ H)
    (hKH : K ≤ H) (hKn : (K.subgroupOf H).Normal) (hK2 : IsPGroup 2 K) {s : R} (hs : s ∈ X)
    (hs2 : s ^ 2 = 1) (hs1 : s ≠ 1) : s ∉ K := by
  intro hsK
  obtain ⟨a, ha, ha1, ha3, hXa, -, -⟩ := symThree_data hX
  obtain ⟨hinv, -⟩ := hXa s hs hs2 hs1
  have hconj := (Subgroup.normal_subgroupOf_iff hKH).1 hKn
  have h1 : a * s * a⁻¹ ∈ K := hconj s a hsK (hXH ha)
  have h2 : a * s * a⁻¹ = a ^ 2 * s := by
    have e2 : s * a⁻¹ * s⁻¹ = a := by
      have : s * a⁻¹ * s⁻¹ = (s * a * s⁻¹)⁻¹ := by group
      rw [this, hinv, inv_inv]
    calc a * s * a⁻¹ = a * (s * a⁻¹ * s⁻¹) * s := by group
      _ = a ^ 2 * s := by rw [e2, pow_two]
  rw [h2] at h1
  have h3 : a ^ 2 ∈ K := by
    have := K.mul_mem h1 (K.inv_mem hsK)
    simpa using this
  have h4 : a ∈ K := by
    have h5 : (a ^ 2) ^ 2 = a := by
      calc (a ^ 2) ^ 2 = a ^ 3 * a := by group
        _ = a := by rw [ha3, one_mul]
    rw [← h5]
    exact pow_mem h3 2
  refine ha1 (eq_one_of_pow_two_pow_three ?_ ⟨1, by simpa using ha3⟩)
  obtain ⟨i, hi⟩ := hK2 ⟨a, h4⟩
  exact ⟨i, by simpa using congrArg Subtype.val hi⟩

theorem eq_of_two_cosets [Finite R] (hO2 : CFSG.pCore 2 R = ⊥) {X X' H K : Subgroup R}
    (hX : IsSymThree X) (hX' : IsSymThree X') (hXs : IsSubnormal X ⊤) (hXs' : IsSubnormal X' ⊤)
    (hXH : X ≤ H) (hX'H : X' ≤ H) (hKH : K ≤ H) (hKn : (K.subgroupOf H).Normal)
    (hK2 : IsPGroup 2 K) (T : Sylow 2 R) (hKT : K ≤ (T : Subgroup R))
    (hcard : Nat.card (T : Subgroup R) ≤ 2 * Nat.card K) : X = X' := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hO2' := eq_bot_of_subnormal_isPGroup_two hO2
  obtain ⟨s, hsT, hsX, hs2, hs1⟩ := exists_involution_mem_sylow hX hXs T
  obtain ⟨s', hs'T, hs'X', hs'2, hs'1⟩ := exists_involution_mem_sylow hX' hXs' T
  have hsK : s ∉ K := not_mem_of_normal_two hX hXH hKH hKn hK2 hsX hs2 hs1
  have hs'K : s' ∉ K := not_mem_of_normal_two hX' hX'H hKH hKn hK2 hs'X' hs'2 hs'1
  have hk : s⁻¹ * s' ∈ K := inv_mul_mem_of_card_le_two_mul hKT hcard hsT hs'T hsK hs'K
  obtain ⟨a', ha'X', ha1', ha3', hXa', -, -⟩ := symThree_data hX'
  obtain ⟨hinv', -⟩ := hXa' s' hs'X' hs'2 hs'1
  have ha'N : a' ∈ CFSG.pCore 3 R := mem_pCore_three hX' hXs' ha'X' ha3' ha1'
  set k : R := s⁻¹ * s' with hkdef
  have hconj := (Subgroup.normal_subgroupOf_iff hKH).1 hKn
  have hkc : k * a' * k⁻¹ * a'⁻¹ = 1 := by
    refine eq_one_of_pow_two_pow_three ?_ ?_
    · have hmem : k * a' * k⁻¹ * a'⁻¹ ∈ K := by
        have h1 : a' * k⁻¹ * a'⁻¹ ∈ K := hconj k⁻¹ a' (K.inv_mem hk) (hX'H ha'X')
        have := K.mul_mem hk h1
        simpa [mul_assoc] using this
      obtain ⟨i, hi⟩ := hK2 ⟨_, hmem⟩
      exact ⟨i, by simpa using congrArg Subtype.val hi⟩
    · have hmem : k * a' * k⁻¹ * a'⁻¹ ∈ CFSG.pCore 3 R := by
        have h1 : k * a' * k⁻¹ ∈ CFSG.pCore 3 R := CFSG.pCore_normal.conj_mem a' ha'N k
        exact (CFSG.pCore 3 R).mul_mem h1 ((CFSG.pCore 3 R).inv_mem ha'N)
      obtain ⟨j, hj⟩ := (CFSG.pCore_isPGroup (p := 3) (G := R)) ⟨_, hmem⟩
      exact ⟨j, by simpa using congrArg Subtype.val hj⟩
  have hka : k * a' * k⁻¹ = a' := by
    calc k * a' * k⁻¹ = (k * a' * k⁻¹ * a'⁻¹) * a' := by group
      _ = a' := by rw [hkc, one_mul]
  have hsinv : s * a' * s⁻¹ = a'⁻¹ := by
    have hs' : s' = s * k := by
      rw [hkdef]
      group
    calc s * a' * s⁻¹ = s * (k * a' * k⁻¹) * s⁻¹ := by rw [hka]
      _ = s' * a' * s'⁻¹ := by rw [hs']; group
      _ = a'⁻¹ := hinv'
  have ha'X : a' ∈ X := mem_of_inv_involution hX hXs hsX hs2 hs1 ha3' hsinv
  exact eq_of_shared_three hO2' hX hX' hXs hXs' ha'X ha'X' ha3' ha1'

theorem eq_of_card_sylow_le_two [Finite R] (hO2 : CFSG.pCore 2 R = ⊥) {X X' : Subgroup R}
    (hX : IsSymThree X) (hX' : IsSymThree X') (hXs : IsSubnormal X ⊤)
    (hXs' : IsSubnormal X' ⊤) (T : Sylow 2 R) (hT : Nat.card (T : Subgroup R) ≤ 2) : X = X' := by
  refine eq_of_two_cosets hO2 hX hX' hXs hXs' (H := ⊤) (K := ⊥) le_top le_top bot_le ?_ ?_ T
    bot_le ?_
  · rw [Subgroup.bot_subgroupOf]
    infer_instance
  · exact IsPGroup.of_bot
  · simpa using hT

end CFSG.LocalAnalysis.RankThreeTheoremC.TwelveNotLe.Sym
