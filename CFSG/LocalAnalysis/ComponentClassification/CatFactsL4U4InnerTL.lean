module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4TE

public section

namespace CFSG.ComponentClassification.CatFactsL4U4

open CFSG Subgroup CFSG.ComponentClassification.GSThmB CFSG.ComponentClassification.UnbalancedLayer

variable {H : Type} [Group H] [Finite H] {h : Hyp52 H}

theorem conj_eq_one_iff_mem_center {G : Type*} [Group G] (y : G) :
    MulAut.conj y = 1 ↔ y ∈ center G := by
  rw [Subgroup.mem_center_iff]
  constructor
  · intro h1 x
    have := congrArg (fun φ : MulAut G => φ x) h1
    simp only [MulAut.conj_apply, MulAut.one_apply] at this
    calc x * y = y * x * y⁻¹ * y := by rw [this]
      _ = y * x := by group
  · intro h1
    ext x
    simp only [MulAut.conj_apply, MulAut.one_apply]
    rw [← h1 x]
    group

theorem mem_sup_B_of_inner (hKa : conjugate h.K h.a = h.K) (hZ : center (OddBar h.K) = ⊥)
    {t : H} (htW : t ∈ h.W) (ht2 : ∃ n : ℕ, t ^ 2 ^ n = 1) {kb : OddBar h.K}
    (hτ : actW h hKa ⟨t, htW⟩ = MulAut.conj kb) : t ∈ h.K ⊔ h.B := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn⟩ := ht2
  have hkb2 : kb ^ 2 ^ n = 1 := by
    have h1 : MulAut.conj (kb ^ 2 ^ n) = 1 := by
      rw [map_pow, ← hτ, ← map_pow]
      have : (⟨t, htW⟩ : h.W) ^ 2 ^ n = 1 := Subtype.ext (by simpa using hn)
      rw [this, map_one]
    rw [conj_eq_one_iff_mem_center, hZ, mem_bot] at h1
    exact h1
  obtain ⟨k₀, rfl⟩ := QuotientGroup.mk_surjective kb
  set O : Subgroup H := (pPrimeCore 2 h.K).map h.K.subtype with hO
  have hk₀W : (k₀ : H) ∈ h.W := K_le_W h k₀.2
  have hmodO : ∀ (i j : ℤ), (t ^ i) * ((k₀ : H) ^ j) * (t ^ i)⁻¹ * ((k₀ : H) ^ j)⁻¹ ∈ O := by
    intro i j
    have h1 : actW h hKa (⟨t, htW⟩ ^ i) ((k₀ ^ j : h.K) : OddBar h.K) =
        ((k₀ ^ j : h.K) : OddBar h.K) := by
      rw [map_zpow, hτ, ← map_zpow, MulAut.conj_apply, QuotientGroup.mk_zpow]
      group
    rw [actW_apply_mk] at h1
    set x : h.K := ⟨((⟨t, htW⟩ ^ i : h.W) : H) * ((k₀ ^ j : h.K) : H) *
      ((⟨t, htW⟩ ^ i : h.W) : H)⁻¹, (mem_normalizer_iff.mp (W_le_normalizer_K h hKa
        (⟨t, htW⟩ ^ i : h.W).2) _).mp (k₀ ^ j).2⟩ with hx
    have h2 : (QuotientGroup.mk (x * (k₀ ^ j)⁻¹) : OddBar h.K) = 1 := by
      rw [QuotientGroup.mk_mul, h1, QuotientGroup.mk_inv, mul_inv_cancel]
    refine ⟨x * (k₀ ^ j)⁻¹, (QuotientGroup.eq_one_iff _).1 h2, ?_⟩
    simp only [hx, subtype_apply, Subgroup.coe_mul, Subgroup.coe_inv, SubgroupClass.coe_zpow]
  have hOodd : Odd (Nat.card O) := by
    rw [hO, card_map_of_injective h.K.subtype_injective]
    have h4 := (pPrimeCore_coprime_card (p := 2) (G := ↥h.K)).symm
    rw [Nat.coprime_two_right] at h4
    exact h4
  have hKN := W_le_normalizer_K h hKa
  have hON : ∀ y ∈ normalizer (h.K : Set H), ∀ o ∈ O, y * o * y⁻¹ ∈ O := by
    intro y hy o ho
    have h1 := UnbalancedGS.normalizer_le_normalizer_map_of_characteristic h.K
      (pPrimeCore 2 h.K) hy
    exact (mem_normalizer_iff.mp h1 o).mp ho
  have hA : IsPGroup 2 (zpowers t) := by
    rintro ⟨y, hy⟩
    obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp hy
    refine ⟨n, Subtype.ext ?_⟩
    rw [SubgroupClass.coe_pow, OneMemClass.coe_one, ← zpow_natCast, ← zpow_mul, mul_comm,
      zpow_mul, zpow_natCast, hn, one_zpow]
  obtain ⟨o, hoO, hfix⟩ := exists_fixed_mul_of_isPGroup_two (X := zpowers (k₀ : H)) hA hOodd
    (fun o ho x hx => by
      obtain ⟨j, rfl⟩ := mem_zpowers_iff.mp hx
      exact hON _ (le_normalizer (zpow_mem k₀.2 j)) o ho)
    (fun t' ht' o ho => by
      obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp ht'
      exact hON _ (hKN (zpow_mem htW i)) o ho)
    (fun t' ht' x hx => by
      obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp ht'
      obtain ⟨j, rfl⟩ := mem_zpowers_iff.mp hx
      exact hmodO i j)
    (mem_zpowers _)
  have hoK : o ∈ h.K := map_subtype_le _ hoO
  set k₁ : H := (k₀ : H) * o with hk₁
  have hk₁K : k₁ ∈ h.K := mul_mem k₀.2 hoK
  have htk₁ : t * k₁ = k₁ * t := by
    have := hfix t (mem_zpowers t)
    calc t * k₁ = t * k₁ * t⁻¹ * t := by group
      _ = k₁ * t := by rw [this]
  have hk₁bar : (QuotientGroup.mk ⟨k₁, hk₁K⟩ : OddBar h.K) = QuotientGroup.mk k₀ := by
    rw [QuotientGroup.eq]
    obtain ⟨o', ho', hoe⟩ := hoO
    have : (⟨k₁, hk₁K⟩ : h.K)⁻¹ * k₀ = o'⁻¹ := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, hk₁]
      rw [← hoe]
      simp
    rw [this]
    exact inv_mem ho'
  set c : h.K := ⟨k₁, hk₁K⟩ with hc
  obtain ⟨c₁, hc₁, c₂, hc₂, hce, hc₁o, m, hc₂m⟩ := exists_odd_mul_twoPow c (orderOf_pos _)
  have hc₁bar : (QuotientGroup.mk c₁ : OddBar h.K) = 1 := by
    obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp hc₁
    have h1 : ((QuotientGroup.mk (c ^ i) : OddBar h.K)) ^ 2 ^ n = 1 := by
      rw [QuotientGroup.mk_zpow, hk₁bar, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul,
        zpow_natCast, hkb2, one_zpow]
    have h2 : orderOf (QuotientGroup.mk (c ^ i) : OddBar h.K) ∣ orderOf (c ^ i) :=
      orderOf_map_dvd (QuotientGroup.mk' (pPrimeCore 2 h.K)) _
    have h3 := orderOf_dvd_of_pow_eq_one h1
    have hcop : Nat.Coprime (2 ^ n) (orderOf (c ^ i)) :=
      Nat.Coprime.pow_left _ (Nat.coprime_two_left.2 hc₁o)
    have h4 : Nat.Coprime (orderOf (QuotientGroup.mk (c ^ i) : OddBar h.K))
        (orderOf (QuotientGroup.mk (c ^ i) : OddBar h.K)) :=
      Nat.Coprime.coprime_dvd_left h3 (Nat.Coprime.coprime_dvd_right h2 hcop)
    exact orderOf_eq_one_iff.1 ((Nat.coprime_self _).1 h4)
  have hc₂bar : (QuotientGroup.mk c₂ : OddBar h.K) = QuotientGroup.mk k₀ := by
    rw [← hk₁bar, hce, QuotientGroup.mk_mul, hc₁bar, one_mul]
  have htc₂ : t * (c₂ : H) = (c₂ : H) * t := by
    obtain ⟨j, rfl⟩ := mem_zpowers_iff.mp hc₂
    have : Commute t k₁ := htk₁
    exact (this.zpow_right j).eq
  have hc₂W : (c₂ : H) ∈ h.W := K_le_W h c₂.2
  set n₀ : H := t * (c₂ : H)⁻¹ with hn₀
  have hn₀W : n₀ ∈ h.W := mul_mem htW (inv_mem hc₂W)
  have hn₀2 : n₀ ^ 2 ^ (n + m) = 1 := by
    have hcomm : Commute t (c₂ : H)⁻¹ := (Commute.inv_right htc₂)
    rw [hn₀, hcomm.mul_pow, pow_add, pow_mul, hn, one_pow, one_mul, inv_pow, mul_comm, pow_mul,
      ← SubgroupClass.coe_pow, hc₂m, OneMemClass.coe_one, one_pow, inv_one]
  have hn₀act : actW h hKa ⟨n₀, hn₀W⟩ = 1 := by
    have : (⟨n₀, hn₀W⟩ : h.W) = ⟨t, htW⟩ * (⟨c₂, hc₂W⟩ : h.W)⁻¹ := rfl
    rw [this, map_mul, map_inv, hτ, actW_of_mem_K h hKa c₂, hc₂bar, mul_inv_cancel]
  have hn₀K : n₀ ∈ coreActionKernel h.K :=
    mem_coreActionKernel_of_oddBarConj_eq_one (g := ⟨n₀, hKN hn₀W⟩) hn₀act
  have hn₀B := mem_B_of_mem_coreActionKernel' h hKa hn₀W hn₀K ⟨n + m, hn₀2⟩
  have : t = (c₂ : H) * n₀ := by
    rw [hn₀, ← mul_assoc, ← htc₂, mul_assoc, mul_inv_cancel, mul_one]
  rw [this]
  exact mul_mem (mem_sup_left c₂.2) (mem_sup_right hn₀B)

theorem commutator_mem_pPrimeCore_JB {t : H} (htB : t ∈ normalizer (h.B : Set H))
    (htJ : t ∈ coreActionKernel h.J) {x : H} (hx : x ∈ GSLit.fixedLayer h.J h.B) :
    t * x * t⁻¹ ∈ GSLit.fixedLayer h.J h.B ∧
      t * x * t⁻¹ * x⁻¹ ∈ (pPrimeCore 2 ↥(GSLit.fixedLayer h.J h.B)).map
        (GSLit.fixedLayer h.J h.B).subtype := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set JB := GSLit.fixedLayer h.J h.B with hJB
  set OJ := (pPrimeCore 2 ↥h.J).map h.J.subtype with hOJ
  have hJBJ : JB ≤ h.J := (GSLit.fixedLayer_le_inf h.J h.B).trans inf_le_left
  have htN : t ∈ normalizer (JB : Set H) :=
    GSLit.mem_normalizer_fixedLayer (mem_coreActionKernel.mp htJ).1 htB
  have hOJn : ∀ o ∈ OJ, ∀ j ∈ h.J, j * o * j⁻¹ ∈ OJ := by
    rintro _ ⟨o, ho, rfl⟩ j hj
    refine ⟨⟨j, hj⟩ * o * ⟨j, hj⟩⁻¹, ?_, rfl⟩
    exact (inferInstance : (pPrimeCore 2 ↥h.J).Normal).conj_mem o ho _
  have hxJ : x ∈ h.J := hJBJ hx
  have h1 : x⁻¹ * t * x * t⁻¹ ∈ OJ := by
    have := (mem_coreActionKernel.mp (inv_mem htJ)).2 x hxJ
    rw [inv_inv] at this
    exact this
  have h2 : t * x * t⁻¹ * x⁻¹ ∈ OJ := by
    have := hOJn _ h1 x hxJ
    convert this using 1
    group
  have h3 : t * x * t⁻¹ ∈ JB := (mem_normalizer_iff.mp htN x).mp hx
  have h4 : t * x * t⁻¹ * x⁻¹ ∈ JB := mul_mem h3 (inv_mem hx)
  refine ⟨h3, ?_⟩
  set M : Subgroup ↥JB := OJ.subgroupOf JB with hM
  have hMn : M.Normal := ⟨fun m hm g => by
    rw [hM, mem_subgroupOf] at hm ⊢
    exact hOJn _ hm g (hJBJ g.2)⟩
  have hMc : Nat.Coprime 2 (Nat.card M) := by
    have h5 : Nat.card M = Nat.card ↥(OJ ⊓ JB) := by
      rw [hM, ← Subgroup.card_map_of_injective JB.subtype_injective,
        Subgroup.subgroupOf_map_subtype]
    have h6 : Nat.card ↥(OJ ⊓ JB) ∣ Nat.card OJ := Subgroup.card_dvd_of_le inf_le_left
    have h7 : Nat.Coprime 2 (Nat.card OJ) := by
      rw [hOJ, Subgroup.card_map_of_injective h.J.subtype_injective]
      exact pPrimeCore_coprime_card
    rw [h5]
    exact Nat.Coprime.coprime_dvd_right h6 h7
  have hMle := le_pPrimeCore_of_normal hMc
  exact ⟨⟨_, h4⟩, hMle (mem_subgroupOf.mpr h2), rfl⟩

theorem map_pPrimeCore_eq_bot (hKa : conjugate h.K h.a = h.K)
    (hcard : Nat.card (imJB h) ≤ Nat.card (OddBar h.J)) :
    (pPrimeCore 2 ↥(GSLit.fixedLayer h.J h.B)).map (jbToK h hKa) = ⊥ := by
  set JB := GSLit.fixedLayer h.J h.B with hJB
  set f := jbToK h hKa with hf
  set O := pPrimeCore 2 ↥JB with hO
  have hk := Subgroup.card_ker_mul_card_range f
  rw [range_jbToK] at hk
  set f' := f.comp O.subtype with hf'
  have hk' := Subgroup.card_ker_mul_card_range f'
  have hrange : f'.range = O.map f := by rw [hf', MonoidHom.range_comp, Subgroup.range_subtype]
  rw [hrange] at hk'
  have hker : Nat.card f'.ker = Nat.card f.ker := by
    have hle : f.ker ≤ O := ker_jbToK_le h hKa
    have : f'.ker.map O.subtype = f.ker := by
      rw [hf', ← MonoidHom.comap_ker, Subgroup.map_comap_eq, Subgroup.range_subtype,
        inf_of_le_right hle]
    rw [← this, Subgroup.card_map_of_injective O.subtype_injective]
  rw [hker] at hk'
  obtain ⟨e, -⟩ := exists_oddBar_JB_equiv h
  have hq : Nat.card JB = Nat.card (OddBar h.J) * Nat.card O := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup O, Nat.card_congr e.toEquiv]
  have hpos : 0 < Nat.card f.ker := Nat.card_pos
  have hJpos : 0 < Nat.card (OddBar h.J) := Nat.card_pos
  have hmain : Nat.card (imJB h) = Nat.card (OddBar h.J) * Nat.card (O.map f) := by
    apply Nat.eq_of_mul_eq_mul_left hpos
    rw [hk, hq, ← hk']
    ring
  have h1 : Nat.card (O.map f) ≤ 1 := by
    by_contra hlt
    push Not at hlt
    have : Nat.card (OddBar h.J) * 2 ≤ Nat.card (OddBar h.J) * Nat.card (O.map f) :=
      Nat.mul_le_mul_left _ hlt
    omega
  exact (Subgroup.card_le_one_iff_eq_bot _).1 h1

theorem actW_fixes_imJB (hKa : conjugate h.K h.a = h.K)
    (hO : (pPrimeCore 2 ↥(GSLit.fixedLayer h.J h.B)).map (jbToK h hKa) = ⊥) {t : H}
    (htW : t ∈ h.W) (htJ : t ∈ coreActionKernel h.J) :
    ∀ y ∈ imJB h, actW h hKa ⟨t, htW⟩ y = y := by
  intro y hy
  rw [← range_jbToK h hKa] at hy
  obtain ⟨j, rfl⟩ := hy
  obtain ⟨h1, h2⟩ := commutator_mem_pPrimeCore_JB htW htJ j.2
  obtain ⟨o, ho, hoe⟩ := h2
  have ho1 : jbToK h hKa o = 1 := by
    have : jbToK h hKa o ∈ (pPrimeCore 2 ↥(GSLit.fixedLayer h.J h.B)).map (jbToK h hKa) :=
      ⟨o, ho, rfl⟩
    rw [hO, mem_bot] at this
    exact this
  have hj' : (⟨t * j * t⁻¹, h1⟩ : ↥(GSLit.fixedLayer h.J h.B)) = o * j := by
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    rw [show (o : H) = t * j * t⁻¹ * (j : H)⁻¹ from hoe]
    group
  have h3 : actW h hKa ⟨t, htW⟩ (jbToK h hKa j) = jbToK h hKa ⟨t * j * t⁻¹, h1⟩ := by
    rw [jbToK_apply, jbToK_apply, actW_apply_mk]
  rw [h3, hj', map_mul, ho1, one_mul]

end CFSG.ComponentClassification.CatFactsL4U4
