module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4IdxA

public section

namespace CFSG.ComponentClassification.CatFactsL4U4

namespace IdxKa

open CFSG Subgroup CFSG.ComponentClassification.GSThmB CFSG.ComponentClassification.UnbalancedLayer
open scoped commutatorElement

variable {G : Type*} [Group G]

theorem conjugate_mul (L : Subgroup G) (g g' : G) :
    conjugate L (g * g') = conjugate (conjugate L g) g' := by
  rw [conjugate, conjugate, conjugate, map_map]
  congr 1
  ext x
  simp [mul_assoc]

theorem conjugate_one (L : Subgroup G) : conjugate L 1 = L := by
  ext x
  simp [conjugate]

theorem exists_mul_of_mem_sup {K L : Subgroup G} (hL : L ≤ normalizer (K : Set G)) {x : G}
    (hx : x ∈ K ⊔ L) : ∃ k ∈ K, ∃ l ∈ L, k * l = x := by
  have hKN : K ≤ normalizer (K : Set G) := le_normalizer
  have hxN : x ∈ normalizer (K : Set G) := (sup_le hKN hL) hx
  have h1 : (K ⊔ L).subgroupOf (normalizer (K : Set G)) =
      K.subgroupOf (normalizer (K : Set G)) ⊔ L.subgroupOf (normalizer (K : Set G)) := by
    apply map_injective (normalizer (K : Set G)).subtype_injective
    rw [Subgroup.map_sup, map_subgroupOf_eq_of_le (sup_le hKN hL), map_subgroupOf_eq_of_le hKN,
      map_subgroupOf_eq_of_le hL]
  have h2 : (⟨x, hxN⟩ : ↥(normalizer (K : Set G))) ∈
      ((K.subgroupOf (normalizer (K : Set G)) ⊔
        L.subgroupOf (normalizer (K : Set G)) : Subgroup _) : Set _) := by
    rw [SetLike.mem_coe, ← h1]
    exact hx
  have : (K.subgroupOf (normalizer (K : Set G))).Normal := normal_in_normalizer
  rw [normal_mul] at h2
  obtain ⟨k, hk, c, hc, hkc⟩ := h2
  exact ⟨k, hk, c, hc, congrArg Subtype.val hkc⟩

variable {H : Type} [Group H] [Finite H] (h : Hyp52 H)

theorem isPComponent_Ka :
    conjugate h.K h.a ≤ h.W ∧ IsPComponent 2 ((conjugate h.K h.a).subgroupOf h.W) :=
  OddQuot.isPComponent_conjugate_subgroupOf h.a_mem_normalizer h.isPComponent_K.1
    h.isPComponent_K.2

theorem sup_facts :
    h.K ⊔ conjugate h.K h.a ≤ normalizer (h.K : Set H) ∧
      h.K ⊔ conjugate h.K h.a ≤ normalizer (conjugate h.K h.a : Set H) ∧
      oddCoreIn h.K ≤ oddCoreIn (h.K ⊔ conjugate h.K h.a) ∧
      oddCoreIn (conjugate h.K h.a) ≤ oddCoreIn (h.K ⊔ conjugate h.K h.a) :=
  B5a.pComponent_sup_facts h.isPComponent_K.1 (isPComponent_Ka h).1 h.isPComponent_K.2
    (isPComponent_Ka h).2

theorem mem_kernel_V {u : H} (hu : u ∈ coreActionKernel h.K) (hua : u * h.a = h.a * u) :
    u ∈ coreActionKernel h.V := by
  obtain ⟨-, -, hO1, hO2⟩ := sup_facts h
  have hu' : h.a⁻¹ * u * h.a ∈ coreActionKernel (conjugate h.K h.a) :=
    B5a.conj_mem_coreActionKernel_conjugate hu h.a
  rw [show h.a⁻¹ * u * h.a = u by rw [mul_assoc, hua, inv_mul_cancel_left]] at hu'
  have := B5a.mem_coreActionKernel_sup hO1 hO2 hu hu'
  rwa [h.layer_eq_K] at this

theorem conjugate_eq_or {w : H} (hw : w ∈ h.W) :
    conjugate h.K w = h.K ∨ conjugate h.K w = conjugate h.K h.a := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hne
  push Not at hne
  obtain ⟨hne1, hne2⟩ := hne
  obtain ⟨hMW, hMc⟩ := OddQuot.isPComponent_conjugate_subgroupOf hw h.isPComponent_K.1
    h.isPComponent_K.2
  obtain ⟨hKaW, hKac⟩ := isPComponent_Ka h
  obtain ⟨-, -, hO1, hO2⟩ := sup_facts h
  have hM1 : conjugate h.K w ≤ coreActionKernel h.K :=
    B5a.le_coreActionKernel_of_ne h.isPComponent_K.1 hMW h.isPComponent_K.2 hMc (Ne.symm hne1)
  have hM2 : conjugate h.K w ≤ coreActionKernel (conjugate h.K h.a) :=
    B5a.le_coreActionKernel_of_ne hKaW hMW hKac hMc (Ne.symm hne2)
  have hMV : conjugate h.K w ≤ coreActionKernel h.V := fun m hm => by
    have := B5a.mem_coreActionKernel_sup hO1 hO2 (hM1 hm) (hM2 hm)
    rwa [h.layer_eq_K] at this
  have hMV' : conjugate h.K w ≤ h.V := by
    intro m hm
    rw [conjugate, mem_map] at hm
    obtain ⟨k, hk, rfl⟩ := hm
    have hwV : w⁻¹ ∈ normalizer (h.V : Set H) := OddQuot.le_normalizer_layerIn h.W (inv_mem hw)
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    have := (mem_normalizer_iff.mp hwV k).mp (Hyp52.K_le_V (h := h) hk)
    simpa using this
  have hperf : ⁅conjugate h.K w, conjugate h.K w⁆ = conjugate h.K w :=
    Subgroup.isPerfect_iff.mp (B5a.isPerfect_of_isPComponent_subgroupOf hMW hMc)
  have hMO : conjugate h.K w ≤ oddCoreIn h.V := by
    rw [← hperf, commutator_le]
    intro x hx y hy
    have h1 := (mem_coreActionKernel.mp (hMV (inv_mem hy))).2 x⁻¹ (inv_mem (hMV' hx))
    rw [inv_inv, inv_inv] at h1
    rw [commutatorElement_def]
    exact h1
  have hq := ((CatalogueBPrimeJoin.pComponent_subgroupOf_iff 2 _ _ hMW).mp hMc).2.2
  have hcop : Nat.Coprime 2 (Nat.card (conjugate h.K w)) := by
    have h1 := card_dvd_of_le hMO
    have h2 : Nat.Coprime 2 (Nat.card (oddCoreIn h.V)) := by
      rw [oddCoreIn, card_map_of_injective (subtype_injective _)]
      exact pPrimeCore_coprime_card
    exact h2.coprime_dvd_right h1
  have htop : pPrimeCore 2 ↥(conjugate h.K w) = ⊤ := by
    apply eq_top_iff.mpr
    have : (⊤ : Subgroup ↥(conjugate h.K w)).Normal := inferInstance
    exact le_pPrimeCore_of_normal (by rwa [card_top])
  set Q := ↥(conjugate h.K w) ⧸ pPrimeCore 2 ↥(conjugate h.K w) with hQ
  have hsub : Subsingleton Q := by
    constructor
    intro x y
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective y
    rw [QuotientGroup.eq, htop]
    exact mem_top _
  obtain ⟨-, hs, -⟩ := hq
  have : Nontrivial (Q ⧸ center Q) := IsSimpleGroup.toNontrivial
  obtain ⟨x, y, hxy⟩ := exists_pair_ne (Q ⧸ center Q)
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective x
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective y
  exact hxy (by rw [Subsingleton.elim x y])

omit [Finite H] in
theorem conj_apply_eq {Y : Type*} [Group Y] (φ : MulAut Y) (x : Y) :
    MulAut.conj (φ x) = φ * MulAut.conj x * φ⁻¹ := by
  ext y
  simp [MulAut.mul_apply, MulAut.conj_apply]

omit [Finite H] in
theorem eq_one_of_comm_conj {Y : Type*} [Group Y] (hY : Group.IsPerfect Y) {φ : MulAut Y}
    (hφ : ∀ x : Y, φ * MulAut.conj x = MulAut.conj x * φ) : φ = 1 := by
  apply GH74.KGroups.inducedHom_injective hY
  rw [map_one]
  ext x
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective x
  rw [GH74.KGroups.inducedHom_mk, MulAut.one_apply, eq_comm, QuotientGroup.eq]
  rw [mem_center_iff]
  intro y
  have h1 : MulAut.conj (φ x) = MulAut.conj x := by
    rw [conj_apply_eq, hφ x, mul_inv_cancel_right]
  have h2 := congrArg (fun f : MulAut Y => f y) h1
  simp only [MulAut.conj_apply] at h2
  calc y * (x⁻¹ * φ x) = x⁻¹ * (x * y * x⁻¹) * φ x := by group
    _ = x⁻¹ * (φ x * y * (φ x)⁻¹) * φ x := by rw [h2]
    _ = x⁻¹ * φ x * y := by group

omit [Finite H] in
theorem card_range_conj {Y : Type*} [Group Y] :
    Nat.card (MulAut.conj : Y →* MulAut Y).range = Nat.card (Y ⧸ center Y) := by
  have hker : (MulAut.conj : Y →* MulAut Y).ker = center Y := by
    ext x
    rw [MonoidHom.mem_ker, mem_center_iff]
    constructor
    · intro hx y
      have := congrArg (fun f : MulAut Y => f y) hx
      simp only [MulAut.conj_apply, MulAut.one_apply] at this
      calc y * x = x * y * x⁻¹ * x := by rw [this]
        _ = x * y := by group
    · intro hx
      ext y
      simp only [MulAut.conj_apply, MulAut.one_apply]
      rw [← hx y, mul_inv_cancel_right]
  exact (Nat.card_congr ((QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivRange _)).toEquiv).symm

theorem T_le_of_ne (hKa : conjugate h.K h.a ≠ h.K) (hZJ : center (OddBar h.J) = ⊥)
    (hcard : Nat.card (ZStarBar h.K) = Nat.card (OddBar h.J)) : h.T ≤ zpowers h.a ⊔ h.B := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro t ht
  have ha2 : h.a * h.a = 1 := by rw [← pow_two, ← h.orderOf_a, pow_orderOf_eq_one]
  have haT : h.a ∈ h.T := mem_inf.mpr ⟨mem_inf.mpr ⟨h.a_mem_S, h.a_mem_normalizer⟩, h.a_mem_P⟩
  have htW := Idx.mem_W_of_mem_T h ht
  obtain ⟨u, huT, huK, hut⟩ : ∃ u ∈ h.T, conjugate h.K u = h.K ∧ (u = t ∨ u = t * h.a) := by
    rcases conjugate_eq_or h htW with h1 | h1
    · exact ⟨t, ht, h1, Or.inl rfl⟩
    · refine ⟨t * h.a, mul_mem ht haT, ?_, Or.inr rfl⟩
      rw [conjugate_mul, h1, ← conjugate_mul, ha2, conjugate_one]
  suffices hu : u ∈ h.B by
    rcases hut with rfl | rfl
    · exact mem_sup_right hu
    · have e : t = t * h.a * h.a⁻¹ := by group
      rw [e]
      exact mul_mem (mem_sup_right hu) (inv_mem (mem_sup_left (mem_zpowers _)))
  have huW := Idx.mem_W_of_mem_T h huT
  have huN : u ∈ normalizer (h.K : Set H) := mem_normalizer_of_conjugate_eq huK
  have hua : u * h.a = h.a * u := h.comm_a (Idx.mem_S_of_mem_T h huT)
  set Y := GSLit.fixedLayer h.J (Idx.E h t) with hY
  have hYV : Y ≤ h.V := (Idx.fixedLayer_E_le h ht).trans (B5a.fixedLayer_le_V h)
  obtain ⟨hVK, -, -, -⟩ := sup_facts h
  have hVK' : h.V ≤ normalizer (h.K : Set H) := by
    have e : h.V = h.K ⊔ conjugate h.K h.a := h.layer_eq_K.symm
    rw [e]
    exact hVK
  have hKaN : conjugate h.K h.a ≤ normalizer (h.K : Set H) := le_sup_right.trans hVK
  have hYN : Y ≤ normalizer (h.K : Set H) := hYV.trans hVK'
  have hYa : ∀ y ∈ Y, y * h.a = h.a * y := fun y hy =>
    mem_centralizer_singleton_iff.mp (h.J_le (mem_inf.mp ((GSLit.fixedLayer_le_inf h.J _) hy)).1)
  have hYt : ∀ y ∈ Y, t * y = y * t := fun y hy =>
    mem_centralizer_iff.mp (mem_inf.mp ((GSLit.fixedLayer_le_inf h.J _) hy)).2 t
      (mem_sup_left (mem_zpowers t))
  have hYu : ∀ y ∈ Y, u * y = y * u := by
    intro y hy
    rcases hut with rfl | rfl
    · exact hYt y hy
    · rw [mul_assoc, ← hYa y hy, ← mul_assoc, hYt y hy, mul_assoc]
  set ρ : ↥Y →* MulAut (OddBar h.K) := (oddBarConj h.K).comp (inclusion hYN) with hρ
  have hKaK : conjugate h.K h.a ≤ coreActionKernel h.K :=
    B5a.le_coreActionKernel_of_ne h.isPComponent_K.1 (isPComponent_Ka h).1 h.isPComponent_K.2
      (isPComponent_Ka h).2 (Ne.symm hKa)
  have hρinn : ρ.range ≤ (MulAut.conj : OddBar h.K →* MulAut (OddBar h.K)).range := by
    rintro _ ⟨y, rfl⟩
    have hyV : (y : H) ∈ h.K ⊔ conjugate h.K h.a := by rw [h.layer_eq_K]; exact hYV y.2
    obtain ⟨k, hk, k', hk', hkk'⟩ := exists_mul_of_mem_sup hKaN hyV
    refine ⟨(QuotientGroup.mk ⟨k, hk⟩ : OddBar h.K), ?_⟩
    have e1 : (inclusion hYN y : ↥(normalizer (h.K : Set H))) =
        ⟨k, le_normalizer hk⟩ * ⟨k', hKaN hk'⟩ := Subtype.ext hkk'.symm
    rw [hρ, MonoidHom.comp_apply, e1, map_mul,
      oddBarConj_eq_one_of_mem_coreActionKernel' (g := ⟨k', hKaN hk'⟩) (hKaK hk'), mul_one,
      oddBarConj_mk_eq_conj h.K hk]
  set φ := oddBarConj h.K ⟨u, huN⟩ with hφ
  have hφρ : ∀ y : ↥Y, φ * ρ y = ρ y * φ := by
    intro y
    rw [hφ, hρ, MonoidHom.comp_apply, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hYu y y.2)
  obtain ⟨e⟩ := Idx.nonempty_equiv_E h ht
  have hOVY : (oddCoreIn h.V).comap Y.subtype ≤ pPrimeCore 2 ↥Y := by
    have hn : ((oddCoreIn h.V).comap Y.subtype).Normal := by
      refine ⟨fun x hx g => ?_⟩
      rw [mem_comap] at hx ⊢
      have h1 := B5a.conj_mem_oddCoreIn hx (hYV (inv_mem g.2))
      simpa only [coe_mul, coe_inv, inv_inv, subtype_apply] using h1
    have hc : Nat.Coprime 2 (Nat.card ((oddCoreIn h.V).comap Y.subtype)) := by
      have h1 : Nat.card ((oddCoreIn h.V).comap Y.subtype) ∣ Nat.card (oddCoreIn h.V) := by
        rw [← card_map_of_injective Y.subtype_injective]
        exact card_dvd_of_le (map_comap_le _ _)
      have h2 : Nat.Coprime 2 (Nat.card (oddCoreIn h.V)) := by
        rw [oddCoreIn, card_map_of_injective (subtype_injective _)]
        exact pPrimeCore_coprime_card
      exact h2.coprime_dvd_right h1
    exact le_pPrimeCore_of_normal hc
  have hker : ρ.ker ≤ pPrimeCore 2 ↥Y := by
    intro y hy
    have hy1 : (y : H) ∈ coreActionKernel h.K :=
      mem_coreActionKernel_of_oddBarConj_eq_one (g := inclusion hYN y) hy
    have hyV : (y : H) ∈ coreActionKernel h.V := mem_kernel_V h hy1 (hYa y y.2)
    have hcen : (QuotientGroup.mk y : ↥Y ⧸ pPrimeCore 2 ↥Y) ∈ center (↥Y ⧸ pPrimeCore 2 ↥Y) := by
      rw [mem_center_iff]
      intro w
      obtain ⟨y', rfl⟩ := QuotientGroup.mk_surjective w
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
      apply hOVY
      rw [mem_comap]
      have h1 := inv_mem ((mem_coreActionKernel.mp hyV).2 (y' : H) (hYV y'.2))
      convert h1 using 1
      · rfl
      · rw [map_mul, map_inv, map_mul, map_mul]
        simp only [Subgroup.coe_subtype]
        group
    have hcen' : e (QuotientGroup.mk y) ∈ center (OddBar h.J) := by
      rw [mem_center_iff]
      intro w
      obtain ⟨w', rfl⟩ := e.surjective w
      rw [← map_mul, ← map_mul, (mem_center_iff.mp hcen) w']
    rw [hZJ, mem_bot, MulEquiv.map_eq_one_iff, QuotientGroup.eq_one_iff] at hcen'
    exact hcen'
  have hcardρ : Nat.card (OddBar h.J) ≤ Nat.card ρ.range := by
    rw [← Nat.card_congr e.toEquiv,
      ← Nat.card_congr (QuotientGroup.quotientKerEquivRange ρ).toEquiv]
    refine Nat.card_le_card_of_surjective
      (QuotientGroup.map _ _ (MonoidHom.id _) hker) fun y => ?_
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
    exact ⟨QuotientGroup.mk x, rfl⟩
  have hinn : ρ.range = (MulAut.conj : OddBar h.K →* MulAut (OddBar h.K)).range := by
    apply eq_of_le_of_card_ge hρinn
    obtain ⟨eZ⟩ := nonempty_quotient_center_equiv_zStarBar h.K
    rw [card_range_conj, Nat.card_congr eZ.toEquiv, hcard]
    exact hcardρ
  have hφ1 : φ = 1 := by
    apply eq_one_of_comm_conj h.isQuasisimple_K.1
    intro x
    have hx : MulAut.conj x ∈ ρ.range := by rw [hinn]; exact ⟨x, rfl⟩
    obtain ⟨y, hy⟩ := hx
    rw [← hy]
    exact hφρ y
  have hu1 : u ∈ coreActionKernel h.K := mem_coreActionKernel_of_oddBarConj_eq_one hφ1
  have huV : u ∈ coreActionKernel h.V := mem_kernel_V h hu1 hua
  obtain ⟨k, hk⟩ := h.orderOf_eq_two_pow_of_mem_S (Idx.mem_S_of_mem_T h huT)
  exact Idx.mem_B_of_V h huW huV ⟨k, by rw [← hk, pow_orderOf_eq_one]⟩

end IdxKa

end CFSG.ComponentClassification.CatFactsL4U4
