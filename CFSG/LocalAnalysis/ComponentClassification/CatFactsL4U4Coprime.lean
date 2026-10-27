module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4Inner2
public import CFSG.LocalAnalysis.ComponentClassification.GSLitIsoTarget

public section

namespace CFSG.ComponentClassification.CatFactsL4U4

open CFSG Subgroup CFSG.ComponentClassification.GSThmB CFSG.ComponentClassification.UnbalancedLayer

theorem exists_fixed_mul_of_isPGroup_two {G : Type*} [Group G] [Finite G] {A X N : Subgroup G}
    (hA : IsPGroup 2 A) (hNodd : Odd (Nat.card N))
    (hXn : ∀ n ∈ N, ∀ x ∈ X, x * n * x⁻¹ ∈ N) (hAN : ∀ t ∈ A, ∀ n ∈ N, t * n * t⁻¹ ∈ N)
    (hAX : ∀ t ∈ A, ∀ x ∈ X, t * x * t⁻¹ * x⁻¹ ∈ N) {x : G} (hx : x ∈ X) :
    ∃ n ∈ N, ∀ t ∈ A, t * (x * n) * t⁻¹ = x * n := by
  have hmem : ∀ t ∈ A, ∀ n ∈ N, x⁻¹ * (t * (x * n) * t⁻¹) ∈ N := by
    intro t ht n hn
    have h1 : x⁻¹ * (t * x * t⁻¹) ∈ N := by
      have := hXn _ (hAX t ht x hx) x⁻¹ (inv_mem hx)
      convert this using 1
      group
    have h2 := mul_mem h1 (hAN t ht n hn)
    convert h2 using 1
    group
  let : MulAction A N :=
    { smul := fun t n => ⟨x⁻¹ * ((t : G) * (x * n) * (t : G)⁻¹), hmem t t.2 n n.2⟩
      one_smul := fun n => Subtype.ext (by
        change x⁻¹ * ((1 : G) * (x * n) * (1 : G)⁻¹) = n
        group)
      mul_smul := fun t₁ t₂ n => Subtype.ext (by
        change x⁻¹ * (((t₁ : G) * t₂) * (x * n) * ((t₁ : G) * t₂)⁻¹) =
          x⁻¹ * ((t₁ : G) * (x * (x⁻¹ * ((t₂ : G) * (x * n) * (t₂ : G)⁻¹))) * (t₁ : G)⁻¹)
        group) }
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn⟩ := hA.nonempty_fixed_point_of_prime_not_dvd_card N (by
    rw [← even_iff_two_dvd, Nat.not_even_iff_odd]
    exact hNodd)
  refine ⟨n, n.2, fun t ht => ?_⟩
  have h1 := congrArg Subtype.val (MulAction.mem_fixedPoints.mp hn ⟨t, ht⟩)
  change x⁻¹ * (t * (x * n) * t⁻¹) = n at h1
  calc t * (x * n) * t⁻¹ = x * (x⁻¹ * (t * (x * n) * t⁻¹)) := by group
    _ = x * n := by rw [h1]

section Hyp

variable {H : Type} [Group H] [Finite H] (h : Hyp52 H)

theorem exists_orderOf_eq_comm_of_isPGroup (hKa : conjugate h.K h.a = h.K) {A : Subgroup H}
    (hA : IsPGroup 2 A) (hAK : A ≤ h.K) (hAJ : A ≤ coreActionKernel h.J)
    (hAB : A ≤ normalizer (h.B : Set H)) {s : ℕ} (hs : s.Prime)
    (hsJ : s ∣ Nat.card (OddBar h.J)) :
    ∃ y : OddBar h.K, y ∈ imJB h ∧ orderOf y = s ∧
      ∀ (t : H) (ht : t ∈ A), (QuotientGroup.mk ⟨t, hAK ht⟩ : OddBar h.K) * y =
        y * QuotientGroup.mk ⟨t, hAK ht⟩ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := Fact.mk hs
  set JB := GSLit.fixedLayer h.J h.B with hJB
  set O := (pPrimeCore 2 ↥JB).map JB.subtype with hO
  set OJ := (pPrimeCore 2 ↥h.J).map h.J.subtype with hOJ
  have hJBJ : JB ≤ h.J := (GSLit.fixedLayer_le_inf h.J h.B).trans inf_le_left
  obtain ⟨e, -⟩ := exists_oddBar_JB_equiv h
  have hsQ : s ∣ Nat.card (↥JB ⧸ pPrimeCore 2 ↥JB) := by
    rw [Nat.card_congr e.toEquiv]
    exact hsJ
  obtain ⟨w, hw⟩ := exists_prime_orderOf_dvd_card' s hsQ
  obtain ⟨y₀, rfl⟩ := QuotientGroup.mk_surjective w
  have hNodd : Odd (Nat.card O) := by
    rw [hO, Subgroup.card_map_of_injective JB.subtype_injective]
    have := pPrimeCore_coprime_card (p := 2) (G := ↥JB)
    exact Nat.odd_iff.2 (by
      have h2 := Nat.Coprime.symm this
      rw [Nat.coprime_two_right] at h2
      exact Nat.odd_iff.1 h2)
  have hXn : ∀ n ∈ O, ∀ x ∈ JB, x * n * x⁻¹ ∈ O := by
    rintro _ ⟨n, hn, rfl⟩ x hx
    refine ⟨⟨x, hx⟩ * n * ⟨x, hx⟩⁻¹, ?_, rfl⟩
    exact (inferInstance : (pPrimeCore 2 ↥JB).Normal).conj_mem n hn _
  have hAnorm : ∀ t ∈ A, t ∈ normalizer (JB : Set H) := fun t ht =>
    GSLit.mem_normalizer_fixedLayer (mem_coreActionKernel.mp (hAJ ht)).1 (hAB ht)
  have hAN : ∀ t ∈ A, ∀ n ∈ O, t * n * t⁻¹ ∈ O := by
    intro t ht n hn
    have h1 := UnbalancedGS.normalizer_le_normalizer_map_of_characteristic JB (pPrimeCore 2 ↥JB)
      (hAnorm t ht)
    exact (mem_normalizer_iff.mp h1 n).mp hn
  have hOJn : ∀ o ∈ OJ, ∀ j ∈ h.J, j * o * j⁻¹ ∈ OJ := by
    rintro _ ⟨o, ho, rfl⟩ j hj
    refine ⟨⟨j, hj⟩ * o * ⟨j, hj⟩⁻¹, ?_, rfl⟩
    exact (inferInstance : (pPrimeCore 2 ↥h.J).Normal).conj_mem o ho _
  have hAX : ∀ t ∈ A, ∀ x ∈ JB, t * x * t⁻¹ * x⁻¹ ∈ O := by
    intro t ht x hx
    have hxJ : x ∈ h.J := hJBJ hx
    have h1 : x⁻¹ * t * x * t⁻¹ ∈ OJ := by
      have := (mem_coreActionKernel.mp (inv_mem (hAJ ht))).2 x hxJ
      rw [inv_inv] at this
      exact this
    have h2 : t * x * t⁻¹ * x⁻¹ ∈ OJ := by
      have := hOJn _ h1 x hxJ
      convert this using 1
      group
    have h3 : t * x * t⁻¹ * x⁻¹ ∈ JB := by
      have := (mem_normalizer_iff.mp (hAnorm t ht) x).mp hx
      exact mul_mem this (inv_mem hx)
    set M : Subgroup ↥JB := OJ.subgroupOf JB with hM
    have hMn : M.Normal := ⟨fun m hm g => by
      rw [hM, mem_subgroupOf] at hm ⊢
      exact hOJn _ hm g (hJBJ g.2)⟩
    have hMc : Nat.Coprime 2 (Nat.card M) := by
      have h1 : Nat.card M = Nat.card ↥(OJ ⊓ JB) := by
        rw [hM, ← Subgroup.card_map_of_injective JB.subtype_injective,
          Subgroup.subgroupOf_map_subtype]
      have h2 : Nat.card ↥(OJ ⊓ JB) ∣ Nat.card OJ := Subgroup.card_dvd_of_le inf_le_left
      have h3 : Nat.Coprime 2 (Nat.card OJ) := by
        rw [hOJ, Subgroup.card_map_of_injective h.J.subtype_injective]
        exact pPrimeCore_coprime_card
      rw [h1]
      exact Nat.Coprime.coprime_dvd_right h2 h3
    have hMle := le_pPrimeCore_of_normal hMc
    exact ⟨⟨_, h3⟩, hMle (mem_subgroupOf.mpr h2), rfl⟩
  obtain ⟨n, hn, hfix⟩ := exists_fixed_mul_of_isPGroup_two hA hNodd hXn hAN hAX y₀.2
  have hnJB : n ∈ JB := map_subtype_le _ hn
  have hx'JB : (y₀ : H) * n ∈ JB := mul_mem y₀.2 hnJB
  set xbar : OddBar h.K := jbToK h hKa ⟨(y₀ : H) * n, hx'JB⟩ with hxbar
  have hcomm : ∀ (t : H) (ht : t ∈ A), (QuotientGroup.mk ⟨t, hAK ht⟩ : OddBar h.K) * xbar =
      xbar * QuotientGroup.mk ⟨t, hAK ht⟩ := by
    intro t ht
    rw [hxbar, jbToK_apply, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    congr 1
    apply Subtype.ext
    have := hfix t ht
    simp only [Subgroup.coe_mul]
    calc t * ((y₀ : H) * n) = t * ((y₀ : H) * n) * t⁻¹ * t := by group
      _ = (y₀ : H) * n * t := by rw [this]
  have himg : (QuotientGroup.mk (⟨(y₀ : H) * n, hx'JB⟩ : ↥JB) : ↥JB ⧸ pPrimeCore 2 ↥JB) =
      QuotientGroup.mk y₀ := by
    rw [QuotientGroup.eq]
    obtain ⟨n', hn', hn'e⟩ := hn
    have : (y₀⁻¹ * ⟨(y₀ : H) * n, hx'JB⟩ : ↥JB) = n' := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      rw [← hn'e]
      simp
    rw [show (⟨(y₀ : H) * n, hx'JB⟩ : ↥JB)⁻¹ * y₀ = (y₀⁻¹ * ⟨(y₀ : H) * n, hx'JB⟩)⁻¹ by group,
      this]
    exact inv_mem hn'
  have hdvd : s ∣ orderOf xbar := by
    rw [← hw]
    apply orderOf_dvd_of_pow_eq_one
    rw [← himg, ← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    apply ker_jbToK_le h hKa
    rw [MonoidHom.mem_ker, map_pow]
    exact pow_orderOf_eq_one xbar
  obtain ⟨m, hm⟩ := hdvd
  have hm0 : m ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hm
    exact (orderOf_pos xbar).ne' hm
  refine ⟨xbar ^ m, pow_mem (by rw [← range_jbToK h hKa]; exact ⟨_, rfl⟩) m, ?_, ?_⟩
  · rw [orderOf_pow_of_dvd hm0 (by rw [hm]; exact dvd_mul_left m s), hm,
      Nat.mul_div_cancel _ (Nat.pos_of_ne_zero hm0)]
  · intro t ht
    exact ((Commute.pow_right (hcomm t ht) m) : _)

theorem exists_orderOf_eq_comm_of_isPGroup' (hKa : conjugate h.K h.a = h.K) {A : Subgroup H}
    (hA : IsPGroup 2 A) (hAK : A ≤ h.K) (hAJ : A ≤ coreActionKernel h.J)
    (hJs : IsSimpleGroup (OddBar h.J)) (hJ2 : Even (Nat.card (OddBar h.J))) {s : ℕ}
    (hs : s.Prime) (hsJ : s ∣ Nat.card (OddBar h.J)) :
    ∃ y : OddBar h.K, orderOf y = s ∧
      ∀ (t : H) (ht : t ∈ A), (QuotientGroup.mk ⟨t, hAK ht⟩ : OddBar h.K) * y =
        y * QuotientGroup.mk ⟨t, hAK ht⟩ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := Fact.mk hs
  set JB := GSLit.fixedLayer h.J h.B with hJB
  set OJ := (pPrimeCore 2 ↥h.J).map h.J.subtype with hOJ
  set OK := (pPrimeCore 2 ↥h.K).map h.K.subtype with hOK
  have hJBJ : JB ≤ h.J := (GSLit.fixedLayer_le_inf h.J h.B).trans inf_le_left
  have hJBK : JB ≤ h.K := fixedLayer_le_K h hKa
  set X := h.J ⊓ h.K with hX
  set N := OJ ⊓ h.K with hN
  obtain ⟨e, he⟩ := exists_oddBar_JB_equiv h
  have hsQ : s ∣ Nat.card (↥JB ⧸ pPrimeCore 2 ↥JB) := by
    rw [Nat.card_congr e.toEquiv]
    exact hsJ
  obtain ⟨w, hw⟩ := exists_prime_orderOf_dvd_card' s hsQ
  obtain ⟨y₀, rfl⟩ := QuotientGroup.mk_surjective w
  have hOJodd : Odd (Nat.card OJ) := by
    rw [hOJ, Subgroup.card_map_of_injective h.J.subtype_injective]
    have h2 := (pPrimeCore_coprime_card (p := 2) (G := ↥h.J)).symm
    rw [Nat.coprime_two_right] at h2
    exact h2
  have hNodd : Odd (Nat.card N) := by
    have hdvd : Nat.card N ∣ Nat.card OJ := Subgroup.card_dvd_of_le inf_le_left
    obtain ⟨c, hc⟩ := hdvd
    rw [hc] at hOJodd
    exact (Nat.odd_mul.1 hOJodd).1
  have hOJn : ∀ o ∈ OJ, ∀ j ∈ h.J, j * o * j⁻¹ ∈ OJ := by
    rintro _ ⟨o, ho, rfl⟩ j hj
    refine ⟨⟨j, hj⟩ * o * ⟨j, hj⟩⁻¹, ?_, rfl⟩
    exact (inferInstance : (pPrimeCore 2 ↥h.J).Normal).conj_mem o ho _
  have hXn : ∀ n ∈ N, ∀ x ∈ X, x * n * x⁻¹ ∈ N := by
    intro n hn x hx
    rw [hN, Subgroup.mem_inf] at hn ⊢
    rw [hX, Subgroup.mem_inf] at hx
    exact ⟨hOJn n hn.1 x hx.1, mul_mem (mul_mem hx.2 hn.2) (inv_mem hx.2)⟩
  have hAnJ : ∀ t ∈ A, t ∈ normalizer (h.J : Set H) := fun t ht =>
    (mem_coreActionKernel.mp (hAJ ht)).1
  have hAN : ∀ t ∈ A, ∀ n ∈ N, t * n * t⁻¹ ∈ N := by
    intro t ht n hn
    rw [hN, Subgroup.mem_inf] at hn ⊢
    have h1 := UnbalancedGS.normalizer_le_normalizer_map_of_characteristic h.J
      (pPrimeCore 2 ↥h.J) (hAnJ t ht)
    exact ⟨(mem_normalizer_iff.mp h1 n).mp hn.1,
      mul_mem (mul_mem (hAK ht) hn.2) (inv_mem (hAK ht))⟩
  have hAX : ∀ t ∈ A, ∀ x ∈ X, t * x * t⁻¹ * x⁻¹ ∈ N := by
    intro t ht x hx
    rw [hX, Subgroup.mem_inf] at hx
    rw [hN, Subgroup.mem_inf]
    have h1 : x⁻¹ * t * x * t⁻¹ ∈ OJ := by
      have := (mem_coreActionKernel.mp (inv_mem (hAJ ht))).2 x hx.1
      rw [inv_inv] at this
      exact this
    refine ⟨?_, mul_mem (mul_mem (mul_mem (hAK ht) hx.2) (inv_mem (hAK ht))) (inv_mem hx.2)⟩
    have := hOJn _ h1 x hx.1
    convert this using 1
    group
  have hy₀X : (y₀ : H) ∈ X := Subgroup.mem_inf.2 ⟨hJBJ y₀.2, hJBK y₀.2⟩
  obtain ⟨n, hn, hfix⟩ := exists_fixed_mul_of_isPGroup_two hA hNodd hXn hAN hAX hy₀X
  rw [hN, Subgroup.mem_inf] at hn
  set y : H := (y₀ : H) * n with hy
  have hyK : y ∈ h.K := mul_mem (hJBK y₀.2) hn.2
  have hyJ : y ∈ h.J := mul_mem (hJBJ y₀.2) (map_subtype_le _ hn.1)
  set ybar : OddBar h.K := QuotientGroup.mk ⟨y, hyK⟩ with hybar
  have hcomm : ∀ (t : H) (ht : t ∈ A), (QuotientGroup.mk ⟨t, hAK ht⟩ : OddBar h.K) * ybar =
      ybar * QuotientGroup.mk ⟨t, hAK ht⟩ := by
    intro t ht
    rw [hybar, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    congr 1
    apply Subtype.ext
    have := hfix t ht
    simp only [Subgroup.coe_mul]
    calc t * y = t * y * t⁻¹ * t := by group
      _ = y * t := by rw [this]
  set ψ : ↥h.J →* OddBar h.J := QuotientGroup.mk' (pPrimeCore 2 ↥h.J) with hψ
  have hψy : ψ ⟨y, hyJ⟩ = e (QuotientGroup.mk y₀) := by
    rw [he y₀ (hJBJ y₀.2), hψ, QuotientGroup.mk'_apply, QuotientGroup.eq]
    obtain ⟨n', hn', hn'e⟩ := hn.1
    have : ((⟨(y₀ : H), hJBJ y₀.2⟩ : ↥h.J)⁻¹ * ⟨y, hyJ⟩ : ↥h.J) = n' := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, hy]
      rw [← hn'e]
      simp
    rw [show (⟨y, hyJ⟩ : ↥h.J)⁻¹ * ⟨(y₀ : H), hJBJ y₀.2⟩ =
      ((⟨(y₀ : H), hJBJ y₀.2⟩ : ↥h.J)⁻¹ * ⟨y, hyJ⟩)⁻¹ by group, this]
    exact inv_mem hn'
  have hord : orderOf (ψ ⟨y, hyJ⟩) = s := by
    rw [hψy, MulEquiv.orderOf_eq, hw]
  have hψsurj : ∀ u : OddBar h.J, ∃ t : ↥JB, ψ ⟨t, hJBJ t.2⟩ = u := by
    intro u
    obtain ⟨t, ht⟩ := QuotientGroup.mk_surjective (e.symm u)
    refine ⟨t, ?_⟩
    have h1 := he t (hJBJ t.2)
    rw [ht, MulEquiv.apply_symm_apply] at h1
    rw [h1]
    rfl
  set M := ((OK ⊓ h.J).subgroupOf h.J).map ψ with hM
  have hMn : M.Normal := by
    constructor
    rintro _ ⟨m, hm, rfl⟩ u
    obtain ⟨t, rfl⟩ := hψsurj u
    refine ⟨⟨(t : H), hJBJ t.2⟩ * m * ⟨(t : H), hJBJ t.2⟩⁻¹, ?_, by
      rw [map_mul, map_mul, map_inv]⟩
    rw [SetLike.mem_coe, Subgroup.mem_subgroupOf, Subgroup.mem_inf] at hm
    rw [SetLike.mem_coe, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    obtain ⟨hmK, hmJ⟩ := hm
    refine ⟨?_, mul_mem (mul_mem (hJBJ t.2) hmJ) (inv_mem (hJBJ t.2))⟩
    have h1 := UnbalancedGS.normalizer_le_normalizer_map_of_characteristic h.K
      (pPrimeCore 2 ↥h.K) (le_normalizer (hJBK t.2))
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    exact (mem_normalizer_iff.mp h1 _).mp hmK
  have hModd : Odd (Nat.card M) := by
    have h1 : Nat.card M ∣ Nat.card ((OK ⊓ h.J).subgroupOf h.J) :=
      Subgroup.card_map_dvd _ ψ
    have h2 : Nat.card ((OK ⊓ h.J).subgroupOf h.J) ∣ Nat.card OK := by
      rw [← Subgroup.card_map_of_injective h.J.subtype_injective, Subgroup.subgroupOf_map_subtype]
      exact Subgroup.card_dvd_of_le (inf_le_left.trans inf_le_left)
    have h3 : Odd (Nat.card OK) := by
      rw [hOK, Subgroup.card_map_of_injective h.K.subtype_injective]
      have h4 := (pPrimeCore_coprime_card (p := 2) (G := ↥h.K)).symm
      rw [Nat.coprime_two_right] at h4
      exact h4
    obtain ⟨c, hc⟩ := h1.trans h2
    rw [hc] at h3
    exact (Nat.odd_mul.1 h3).1
  have hMbot : M = ⊥ := by
    rcases hMn.eq_bot_or_eq_top with hb | ht
    · exact hb
    · exfalso
      rw [ht, Subgroup.card_top] at hModd
      exact (Nat.not_even_iff_odd.2 hModd) hJ2
  have hdvd : s ∣ orderOf ybar := by
    rw [← hord]
    apply orderOf_dvd_of_pow_eq_one
    have h1 : ybar ^ orderOf ybar = 1 := pow_orderOf_eq_one ybar
    rw [hybar, ← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff] at h1
    have hmem : ((⟨y, hyJ⟩ : ↥h.J) ^ orderOf ybar) ∈ (OK ⊓ h.J).subgroupOf h.J := by
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
      refine ⟨⟨_, h1, ?_⟩, pow_mem hyJ _⟩
      simp [hybar]
    have h2 : ψ ((⟨y, hyJ⟩ : ↥h.J) ^ orderOf ybar) ∈ M := ⟨_, hmem, rfl⟩
    rw [hMbot, Subgroup.mem_bot, map_pow] at h2
    exact h2
  obtain ⟨m, hm⟩ := hdvd
  have hm0 : m ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hm
    exact (orderOf_pos ybar).ne' hm
  refine ⟨ybar ^ m, ?_, fun t ht => (Commute.pow_right (hcomm t ht) m : _)⟩
  rw [orderOf_pow_of_dvd hm0 (by rw [hm]; exact dvd_mul_left m s), hm,
    Nat.mul_div_cancel _ (Nat.pos_of_ne_zero hm0)]

end Hyp

end CFSG.ComponentClassification.CatFactsL4U4
