module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4InnerHW
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4Fusion

public section

namespace CFSG.ComponentClassification.CatFactsL4U4HW

open CFSG Subgroup CFSG.ComponentClassification.GSThmB CFSG.Assembly.LowTwoRank
  CFSG.LocalAnalysis.ComponentInitial CFSG.ComponentClassification.UnbalancedLayer

open CFSG.ComponentClassification.CatFactsL4U4
  (exists_fixed_mul_of_isPGroup_two exists_conj_of_mul_odd not_mem_of_orderOf_eq_two
    exists_conj_L4 exists_conj_U4)

section Hyp

variable {H : Type} [Group H] [Finite H] (h : Hyp52W H)

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

theorem cfRow516InnerFusionHW : CFRow516InnerFusionHW := by
  intro H _ _ h hrow hin z hzD hzS hz2 a₁ ha₁ ha₁2
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKa : conjugate h.K h.a = h.K := by
    obtain ⟨-, -, -, -, -, -, hKa, -⟩ := hrow
    exact hKa
  obtain ⟨hZ, p, f, hp, hp2, hf, hJ, hcase⟩ := inner_structure h hrow hin
  obtain ⟨ℓ, -, hℓZ, hℓ2, hJC, hJp, -, ⟨s, hs, hs2, hsq, hsJbar, hsJ⟩, -⟩ :=
    inner_data h hp hp2 hJ hKa hin
  have := Fact.mk hs
  have hzJB : z ∈ GSLit.fixedLayer h.J h.B := mem_fixedLayer_of_mem_D h hzD hzS hz2
  have hzK : z ∈ h.K := fixedLayer_le_K h hKa hzJB
  have hzJ : z ∈ h.J := (Subgroup.mem_inf.1 hzD).2
  obtain ⟨ha₁P, ha₁K⟩ := Subgroup.mem_inf.1 ha₁
  have ha₁J : a₁ ∈ coreActionKernel h.J := (Subgroup.mem_inf.1 ha₁P).2
  have hOK : Nat.Coprime 2 (Nat.card (pPrimeCore 2 ↥h.K)) := pPrimeCore_coprime_card
  have hOJ : Nat.Coprime 2 (Nat.card (pPrimeCore 2 ↥h.J)) := pPrimeCore_coprime_card
  have hz2' : z * z = 1 := by rw [← pow_two, ← hz2, pow_orderOf_eq_one]
  have ha₁2' : a₁ * a₁ = 1 := by rw [← pow_two, ← ha₁2, pow_orderOf_eq_one]
  set zbar : OddBar h.K := QuotientGroup.mk ⟨z, hzK⟩ with hzbar
  set abar : OddBar h.K := QuotientGroup.mk ⟨a₁, ha₁K⟩ with habar
  have hzbar1 : zbar ≠ 1 := by
    rw [hzbar, Ne, QuotientGroup.eq_one_iff]
    exact not_mem_of_orderOf_eq_two hOK (by rw [Subgroup.orderOf_mk, hz2])
  have habar1 : abar ≠ 1 := by
    rw [habar, Ne, QuotientGroup.eq_one_iff]
    exact not_mem_of_orderOf_eq_two hOK (by rw [Subgroup.orderOf_mk, ha₁2])
  have hzbar2 : zbar * zbar = 1 := by
    rw [hzbar, ← QuotientGroup.mk_mul]
    have : (⟨z, hzK⟩ : h.K) * ⟨z, hzK⟩ = 1 := Subtype.ext hz2'
    rw [this, QuotientGroup.mk_one]
  have habar2 : abar ^ 2 = 1 := by
    rw [habar, ← QuotientGroup.mk_pow, sq]
    have : (⟨a₁, ha₁K⟩ : h.K) * ⟨a₁, ha₁K⟩ = 1 := Subtype.ext ha₁2'
    rw [this, QuotientGroup.mk_one]
  have hzbarJ : zbar ∈ imJB h := ⟨⟨z, hzK⟩, Subgroup.mem_subgroupOf.2 hzJB, rfl⟩
  have hJs : IsSimpleGroup (OddBar h.J) := isSimpleGroup_of_lieModel_psl_two hJ
  have hJ2 : Even (Nat.card (OddBar h.J)) := by
    set zJ : OddBar h.J := QuotientGroup.mk ⟨z, hzJ⟩ with hzJdef
    have hzJ1 : zJ ≠ 1 := by
      rw [hzJdef, Ne, QuotientGroup.eq_one_iff]
      exact not_mem_of_orderOf_eq_two hOJ (by rw [Subgroup.orderOf_mk, hz2])
    have hzJ2 : zJ ^ 2 = 1 := by
      rw [hzJdef, ← QuotientGroup.mk_pow, sq]
      have : (⟨z, hzJ⟩ : h.J) * ⟨z, hzJ⟩ = 1 := Subtype.ext hz2'
      rw [this, QuotientGroup.mk_one]
    have h1 := orderOf_dvd_natCard zJ
    rw [orderOf_eq_prime hzJ2 hzJ1] at h1
    exact even_iff_two_dvd.2 h1
  have hA2 : IsPGroup 2 (zpowers a₁) := by
    apply IsPGroup.of_card (n := 1)
    rw [Nat.card_zpowers, ha₁2, pow_one]
  obtain ⟨y, hy, hyc⟩ := exists_orderOf_eq_comm_of_isPGroup' h hKa hA2 (zpowers_le.2 ha₁K)
    (zpowers_le.2 ha₁J) hJs hJ2 hs hsJbar
  have hay : abar * y = y * abar := hyc a₁ (mem_zpowers a₁)
  obtain ⟨y'', hy''⟩ := exists_prime_orderOf_dvd_card' (G := imJB h) s hsJ
  have hy' : orderOf (y'' : OddBar h.K) = s := by rw [Subgroup.orderOf_coe, hy'']
  have hℓ1 : ℓ ≠ 1 := fun h1 => hℓZ (by rw [h1]; exact one_mem _)
  have hℓ2' : ℓ ^ 2 = 1 := by rw [hZ] at hℓ2; exact Subgroup.mem_bot.1 hℓ2
  have hconj : ∃ g : OddBar h.K, g * abar * g⁻¹ = zbar := by
    have key : ∀ {M : Type} [Group M] (e : OddBar h.K ≃* M),
        (∃ w, w * e abar * w⁻¹ = e zbar) → ∃ g : OddBar h.K, g * abar * g⁻¹ = zbar := by
      intro M _ e ⟨w, hw⟩
      refine ⟨e.symm w, e.injective ?_⟩
      rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply, hw]
    have hJ' : ∀ {M : Type} [Group M] (e : OddBar h.K ≃* M),
        (imJB h).map e.toMonoidHom ≤ Subgroup.centralizer {e ℓ} := by
      intro M _ e
      rintro _ ⟨x, hx, rfl⟩
      rw [Subgroup.mem_centralizer_singleton_iff, MulEquiv.coe_toMonoidHom, ← map_mul, ← map_mul,
        Subgroup.mem_centralizer_singleton_iff.mp (hJC hx)]
    have hJp' : ∀ {M : Type} [Group M] (e : OddBar h.K ≃* M),
        ⁅(imJB h).map e.toMonoidHom, (imJB h).map e.toMonoidHom⁆ = (imJB h).map e.toMonoidHom :=
      fun e => by rw [← Subgroup.map_commutator, hJp]
    rcases hcase with ⟨hq, F, _, _, hF, ⟨e⟩⟩ | ⟨hq, K', _, hUF, ⟨e⟩⟩
    · have hF' : Fintype.card F % 4 = 3 := by rw [hF]; exact hq
      exact key e (exists_conj_L4 hF' hs hs2 (by rw [hF]; exact hsq) (u := e abar) (y := e y)
        (ℓ' := e ℓ) (z' := e zbar) (y' := e (y'' : OddBar h.K))
        (J' := (imJB h).map e.toMonoidHom)
        (by rw [Ne, MulEquiv.map_eq_one_iff]; exact habar1) (by rw [← map_pow e, habar2, map_one])
        (by rw [MulEquiv.orderOf_eq, hy]) (by rw [← map_mul e, ← map_mul e, hay])
        (by rw [Ne, MulEquiv.map_eq_one_iff]; exact hℓ1) (by rw [← map_pow e, hℓ2', map_one])
        (hJ' e) (hJp' e) ⟨(y'' : OddBar h.K), y''.2, rfl⟩
        (by rw [MulEquiv.orderOf_eq, hy'])
        ⟨zbar, hzbarJ, rfl⟩ (by rw [← map_mul e, hzbar2, map_one])
        (by rw [Ne, MulEquiv.map_eq_one_iff]; exact hzbar1))
    · exact key e (exists_conj_U4 hUF hp2 hq hs hs2 hsq (u := e abar) (y := e y)
        (ℓ' := e ℓ) (z' := e zbar) (y' := e (y'' : OddBar h.K))
        (J' := (imJB h).map e.toMonoidHom)
        (by rw [Ne, MulEquiv.map_eq_one_iff]; exact habar1) (by rw [← map_pow e, habar2, map_one])
        (by rw [MulEquiv.orderOf_eq, hy]) (by rw [← map_mul e, ← map_mul e, hay])
        (by rw [Ne, MulEquiv.map_eq_one_iff]; exact hℓ1) (by rw [← map_pow e, hℓ2', map_one])
        (hJ' e) (hJp' e) ⟨(y'' : OddBar h.K), y''.2, rfl⟩
        (by rw [MulEquiv.orderOf_eq, hy'])
        ⟨zbar, hzbarJ, rfl⟩ (by rw [← map_mul e, hzbar2, map_one])
        (by rw [Ne, MulEquiv.map_eq_one_iff]; exact hzbar1))
  obtain ⟨g, hg⟩ := hconj
  obtain ⟨c₀, rfl⟩ := QuotientGroup.mk_surjective g
  set w : H := (c₀ : H) * a₁ * (c₀ : H)⁻¹ with hw
  have hwK : w ∈ h.K := mul_mem (mul_mem c₀.2 ha₁K) (inv_mem c₀.2)
  have hwz : (QuotientGroup.mk ⟨w, hwK⟩ : OddBar h.K) = zbar := by
    rw [← hg, habar, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    rfl
  have hoO : (⟨z, hzK⟩ : h.K)⁻¹ * ⟨w, hwK⟩ ∈ pPrimeCore 2 ↥h.K := by
    rw [← QuotientGroup.eq]
    exact hwz.symm
  have hoodd : Odd (orderOf (z⁻¹ * w)) := by
    have h1 := orderOf_dvd_natCard (⟨_, hoO⟩ : pPrimeCore 2 ↥h.K)
    rw [Subgroup.orderOf_mk] at h1
    have h2 : orderOf (z⁻¹ * w) = orderOf ((⟨z, hzK⟩ : h.K)⁻¹ * ⟨w, hwK⟩) := by
      rw [← Subgroup.orderOf_coe]
      rfl
    rw [h2]
    have h3 : Odd (Nat.card (pPrimeCore 2 ↥h.K)) := by
      have := hOK.symm
      rwa [Nat.coprime_two_right] at this
    exact Odd.of_dvd_nat h3 h1
  have hw2 : w * w = 1 := by
    rw [hw]
    calc (c₀ : H) * a₁ * (c₀ : H)⁻¹ * ((c₀ : H) * a₁ * (c₀ : H)⁻¹) =
        (c₀ : H) * (a₁ * a₁) * (c₀ : H)⁻¹ := by group
      _ = 1 := by rw [ha₁2', mul_one, mul_inv_cancel]
  obtain ⟨k, hk⟩ := exists_conj_of_mul_odd hz2' hw2 hoodd
  have hoK : z⁻¹ * w ∈ h.K := mul_mem (inv_mem hzK) hwK
  obtain ⟨o, hodef⟩ : ∃ o, o = z⁻¹ * w := ⟨_, rfl⟩
  rw [← hodef] at hk hoK
  refine ⟨(c₀ : H)⁻¹ * o ^ k, mul_mem (inv_mem c₀.2) (pow_mem hoK k), ?_⟩
  calc ((c₀ : H)⁻¹ * o ^ k)⁻¹ * a₁ * ((c₀ : H)⁻¹ * o ^ k) = (o ^ k)⁻¹ * w * o ^ k := by
        rw [hw]; group
    _ = z := by
      rw [← hk]
      group

end CFSG.ComponentClassification.CatFactsL4U4HW
