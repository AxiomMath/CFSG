module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4Inner82A

public section

namespace CFSG.ComponentClassification.CatFactsL4U4

namespace Cover82

open CFSG Subgroup CFSG.ComponentClassification.GSThmB

theorem three_le_pow {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f) : 3 ≤ p ^ f := by
  have : 3 ≤ p := by have := hp.two_le; omega
  calc 3 ≤ p := this
    _ = p ^ 1 := (pow_one p).symm
    _ ≤ p ^ f := Nat.pow_le_pow_right hp.pos hf

theorem le_sq_mul {q : ℕ} (hq : 3 ≤ q) : 720 ≤ q ^ 2 * (q ^ 4 - 1) := by
  have h2 : 9 ≤ q ^ 2 := by nlinarith
  have h4 : 81 ≤ q ^ 4 := by nlinarith
  calc 720 = 9 * 80 := by norm_num
    _ ≤ q ^ 2 * (q ^ 4 - 1) := Nat.mul_le_mul h2 (by omega)

theorem isSec8JType_of_mulEquiv {X X' : Type} [Group X] [Group X'] (e : X ≃* X') {p f : ℕ}
    (h : IsSec8JType X p f) : IsSec8JType X' p f := by
  rcases h with hL | ⟨h1, h2, ⟨eA⟩⟩
  · exact Or.inl (lieModel_of_mulEquiv_ne_zero e (by norm_num) hL)
  · exact Or.inr ⟨h1, h2, ⟨e.symm.trans eA⟩⟩

theorem isSimpleGroup_of_isSec8JType {X : Type} [Group X] {p f : ℕ} (hX : IsSec8JType X p f) :
    IsSimpleGroup X := by
  rcases hX with hL | ⟨-, -, ⟨eA⟩⟩
  · exact GSThmB.isSimpleGroup_of_lieModel_psl_two hL
  · have : IsSimpleGroup (alternatingGroup (Fin 6)) :=
      alternatingGroup.isSimpleGroup (by norm_num [Nat.card_eq_fintype_card])
    exact eA.isSimpleGroup

theorem center_eq_bot_of_simple {X : Type*} [Group X] [IsSimpleGroup X]
    (h : ∃ a b : X, a * b ≠ b * a) : center X = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center X) with hZ | hZ
  · exact hZ
  · obtain ⟨a, b, hab⟩ := h
    exact absurd (mem_center_iff.mp (by rw [hZ]; exact mem_top b) a) hab

theorem center_eq_bot_of_isSec8JType {X : Type} [Group X] [Finite X] {p f : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hf : 1 ≤ f) (hX : IsSec8JType X p f) : center X = ⊥ := by
  have := isSimpleGroup_of_isSec8JType hX
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center X) with hZ | hZ
  · exact hZ
  exfalso
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := X) 5
    (AZ.five_dvd_card_of_isSec8JType hp hp2 hX)
  have hN : (zpowers y).Normal := by
    constructor
    intro n hn g
    have hc : n ∈ center X := by rw [hZ]; exact mem_top n
    rw [mem_center_iff.mp hc g, mul_inv_cancel_right]
    exact hn
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (zpowers y) with h1 | h1
  · have hy1 : y = 1 := by
      have := mem_zpowers y
      rwa [h1, mem_bot] at this
    rw [hy1, orderOf_one] at hy
    norm_num at hy
  · have hc : Nat.card X = 5 := by rw [← hy, ← Nat.card_zpowers, h1, card_top]
    have h2 := AZ.two_mul_card_of_isSec8JType hp hp2 hX
    have h3 := le_sq_mul (three_le_pow hp hp2 hf)
    omega

theorem eq_one_of_mem_pPrimeCore {X : Type*} [Group X] [Finite X] {x : X}
    (hx : x ∈ pPrimeCore 2 X) (h2 : x * x = 1) : x = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcop : Nat.Coprime 2 (Nat.card (pPrimeCore 2 X)) := pPrimeCore_coprime_card
  have h1 : orderOf (⟨x, hx⟩ : pPrimeCore 2 X) ∣ Nat.card (pPrimeCore 2 X) :=
    orderOf_dvd_natCard _
  have h2' : orderOf (⟨x, hx⟩ : pPrimeCore 2 X) ∣ 2 := by
    apply orderOf_dvd_of_pow_eq_one
    apply Subtype.ext
    rw [SubgroupClass.coe_pow, sq]
    exact h2
  have h3 := Nat.dvd_gcd h2' h1
  rw [hcop.gcd_eq_one, Nat.dvd_one, orderOf_eq_one_iff] at h3
  exact congrArg Subtype.val h3

theorem jdata {Y : Type} [Group Y] [Finite Y] {J : Subgroup Y} {p f : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hf : 1 ≤ f) (hJ : IsSec8JType (↥J ⧸ pPrimeCore 2 ↥J) p f) :
    (p ^ f) ^ 2 * ((p ^ f) ^ 4 - 1) ≤ 2 * Nat.card J ∧
      (∃ s : ℕ, s.Prime ∧ s ≠ 2 ∧ s ∣ (p ^ f) ^ 2 + 1 ∧
        s ∣ Nat.card (↥J ⧸ pPrimeCore 2 ↥J) ∧ s ∣ Nat.card J) ∧
      ∀ x ∈ J, (∀ w ∈ J, x * w = w * x) → x * x = 1 → x = 1 := by
  have hZ := center_eq_bot_of_isSec8JType hp hp2 hf hJ
  have hdvd : Nat.card (↥J ⧸ pPrimeCore 2 ↥J) ∣ Nat.card J := Subgroup.card_quotient_dvd_card _
  obtain ⟨s, hs, hs2, hsq, hsJ⟩ := AZ.exists_prime_dvd_card_of_isSec8JType hp hp2 hf hJ
  refine ⟨?_, ⟨s, hs, hs2, hsq, hsJ, hsJ.trans hdvd⟩, ?_⟩
  · rw [← AZ.two_mul_card_of_isSec8JType hp hp2 hJ]
    exact Nat.mul_le_mul_left 2 (Nat.le_of_dvd Nat.card_pos hdvd)
  · intro x hx hc h2
    have hm : (⟨x, hx⟩ : ↥J) = 1 := by
      refine eq_one_of_mem_pPrimeCore ?_ (Subtype.ext h2)
      rw [← QuotientGroup.eq_one_iff, ← mem_bot, ← hZ, mem_center_iff]
      intro g
      obtain ⟨w, rfl⟩ := QuotientGroup.mk_surjective g
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
      congr 1
      exact Subtype.ext (hc w w.2).symm
    exact congrArg Subtype.val hm

theorem exists_orderOf_mk_eq {Y : Type} [Group Y] [Finite Y] {J : Subgroup Y}
    (hZJ : center (↥J ⧸ pPrimeCore 2 ↥J) = ⊥) {s : ℕ} (hs : s.Prime)
    (hsJ : s ∣ Nat.card (↥J ⧸ pPrimeCore 2 ↥J)) :
    ∃ u ∈ J, orderOf (QuotientGroup.mk u : Y ⧸ center Y) = s := by
  have := Fact.mk hs
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥J ⧸ pPrimeCore 2 ↥J) s hsJ
  obtain ⟨m, rfl⟩ := QuotientGroup.mk_surjective x
  set u : Y ⧸ center Y := QuotientGroup.mk (m : Y) with hu
  have hn0 : orderOf u ≠ 0 := (orderOf_pos u).ne'
  have hsn : s ∣ orderOf u := by
    have h1 : (m : Y) ^ orderOf u ∈ center Y := by
      rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow, ← hu, pow_orderOf_eq_one]
    have h2 : (QuotientGroup.mk (m ^ orderOf u) : ↥J ⧸ pPrimeCore 2 ↥J) ∈
        center (↥J ⧸ pPrimeCore 2 ↥J) := by
      rw [mem_center_iff]
      intro g
      obtain ⟨w, rfl⟩ := QuotientGroup.mk_surjective g
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
      congr 1
      apply Subtype.ext
      simp only [Subgroup.coe_mul, SubgroupClass.coe_pow]
      exact mem_center_iff.mp h1 w
    rw [hZJ, mem_bot, QuotientGroup.mk_pow] at h2
    rw [← hx]
    exact orderOf_dvd_of_pow_eq_one h2
  refine ⟨(m : Y) ^ (orderOf u / s), pow_mem m.2 _, ?_⟩
  rw [QuotientGroup.mk_pow, ← hu]
  exact orderOf_pow_orderOf_div hn0 hsn

theorem false_of_central {Y : Type} [Group Y] [Finite Y] {p f : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hf : 1 ≤ f) (hY : IsQuasisimple Y) (htype : IsSec82LType (Y ⧸ center Y) p f)
    (hJ : IsSec8JType (Y ⧸ pPrimeCore 2 Y) p f) : False := by
  have hZJ := center_eq_bot_of_isSec8JType hp hp2 hf hJ
  have h1 : center Y ≤ pPrimeCore 2 Y := by
    intro z hz
    have hmem : (QuotientGroup.mk z : Y ⧸ pPrimeCore 2 Y) ∈ center (Y ⧸ pPrimeCore 2 Y) := by
      rw [mem_center_iff]
      intro g
      obtain ⟨w, rfl⟩ := QuotientGroup.mk_surjective g
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, mem_center_iff.mp hz w]
    rwa [hZJ, mem_bot, QuotientGroup.eq_one_iff] at hmem
  have h2 : pPrimeCore 2 Y ≤ center Y := by
    rcases LieType.CurtisTits.le_center_or_eq_top_of_isQuasisimple hY (pPrimeCore 2 Y) with h | h
    · exact h
    · exfalso
      have hc : Nat.card (Y ⧸ pPrimeCore 2 Y) = 1 := by
        rw [h, ← Subgroup.index_eq_card, Subgroup.index_top]
      have h3 := AZ.two_mul_card_of_isSec8JType hp hp2 hJ
      have h4 := le_sq_mul (three_le_pow hp hp2 hf)
      omega
  exact Inner82.false_of_isSec8JType hp hp2 hf htype hJ
    (QuotientGroup.quotientMulEquivOfEq (le_antisymm h2 h1))

theorem isPComponent_subgroupOf_centralizer {G : Type} [Group G] {Y M : Subgroup G} {y₀ : G}
    (hy₀ : y₀ ∈ Y) (hMC : M ≤ Y ⊓ centralizer ({y₀} : Set G))
    (hM : IsPComponent 2 (M.subgroupOf (Y ⊓ centralizer ({y₀} : Set G)))) :
    IsPComponent 2 ((M.subgroupOf Y).subgroupOf
      (centralizer ({(⟨y₀, hy₀⟩ : ↥Y)} : Set ↥Y))) := by
  set CY : Subgroup ↥Y := centralizer ({(⟨y₀, hy₀⟩ : ↥Y)} : Set ↥Y) with hCY
  set J : Subgroup ↥Y := M.subgroupOf Y with hJ
  have hJC : J ≤ CY := by
    intro x hx
    rw [hCY, mem_centralizer_singleton_iff]
    exact Subtype.ext (mem_centralizer_singleton_iff.mp (hMC (mem_subgroupOf.mp hx)).2)
  let ψ : ↥CY ≃* ↥(CY.map Y.subtype) := CY.equivMapOfInjective Y.subtype Y.subtype_injective
  have hCmap : CY.map Y.subtype = Y ⊓ centralizer ({y₀} : Set G) := by
    ext x
    rw [mem_map, mem_inf, mem_centralizer_singleton_iff]
    constructor
    · rintro ⟨y, hy, rfl⟩
      rw [hCY, mem_centralizer_singleton_iff] at hy
      exact ⟨y.2, congrArg Subtype.val hy⟩
    · rintro ⟨hxY, hx⟩
      refine ⟨⟨x, hxY⟩, ?_, rfl⟩
      rw [hCY, mem_centralizer_singleton_iff]
      exact Subtype.ext hx
  have hMmap : J.map Y.subtype = M := map_subgroupOf_eq_of_le (hMC.trans inf_le_left)
  have key : (J.subgroupOf CY).map ψ.toMonoidHom =
      (J.map Y.subtype).subgroupOf (CY.map Y.subtype) := by
    ext ⟨x, hx⟩
    rw [mem_subgroupOf, mem_map]
    constructor
    · rintro ⟨⟨c, hc⟩, hcM, hceq⟩
      refine ⟨c, hcM, ?_⟩
      exact congrArg Subtype.val hceq
    · rintro ⟨m, hm, rfl⟩
      exact ⟨⟨m, hJC hm⟩, hm, rfl⟩
  have h1 : IsPComponent 2 ((J.map Y.subtype).subgroupOf (CY.map Y.subtype)) := by
    rw [hMmap, hCmap]
    exact hM
  rw [← key] at h1
  have h2 := LocalAnalysis.ComponentInitial.isPComponent_map_of_isPComponent 2 ψ.symm h1
  rwa [Subgroup.map_map, show ψ.symm.toMonoidHom.comp ψ.toMonoidHom = MonoidHom.id _ from by
    ext x; simp, Subgroup.map_id] at h2

end Cover82

end CFSG.ComponentClassification.CatFactsL4U4
