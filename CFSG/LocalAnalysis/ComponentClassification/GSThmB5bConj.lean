module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog5Small

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer

variable {H : Type} [Group H]

theorem conjugate_inf (X Y : Subgroup H) (g : H) :
    conjugate (X ⊓ Y) g = conjugate X g ⊓ conjugate Y g := by
  ext y
  simp only [mem_conjugate_iff, mem_inf]

theorem conjugate_centralizer' (X : Subgroup H) (g : H) :
    conjugate (centralizer (X : Set H)) g = centralizer (conjugate X g : Set H) := by
  ext y
  rw [mem_conjugate_iff, mem_centralizer_iff, mem_centralizer_iff]
  constructor
  · intro hy x hx
    rw [SetLike.mem_coe, mem_conjugate_iff] at hx
    have := hy _ hx
    calc x * y = g⁻¹ * ((g * x * g⁻¹) * (g * y * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * y * g⁻¹) * (g * x * g⁻¹)) * g := by rw [this]
      _ = y * x := by group
  · intro hy x hx
    have hx' : g⁻¹ * x * g ∈ (conjugate X g : Set H) := by
      rw [SetLike.mem_coe, mem_conjugate_iff, show g * (g⁻¹ * x * g) * g⁻¹ = x by group]
      exact hx
    have := hy _ hx'
    calc x * (g * y * g⁻¹) = g * ((g⁻¹ * x * g) * y) * g⁻¹ := by group
      _ = g * (y * (g⁻¹ * x * g)) * g⁻¹ := by rw [this]
      _ = g * y * g⁻¹ * x := by group

theorem conjugate_centralizer_singleton (a g : H) :
    conjugate (centralizer ({a} : Set H)) g = centralizer ({g⁻¹ * a * g} : Set H) := by
  ext y
  rw [mem_conjugate_iff, mem_centralizer_singleton_iff, mem_centralizer_singleton_iff]
  constructor
  · intro hy
    calc y * (g⁻¹ * a * g) = g⁻¹ * ((g * y * g⁻¹) * a) * g := by group
      _ = g⁻¹ * (a * (g * y * g⁻¹)) * g := by rw [hy]
      _ = g⁻¹ * a * g * y := by group
  · intro hy
    calc g * y * g⁻¹ * a = g * (y * (g⁻¹ * a * g)) * g⁻¹ := by group
      _ = g * (g⁻¹ * a * g * y) * g⁻¹ := by rw [hy]
      _ = a * (g * y * g⁻¹) := by group

theorem conjugate_normalizer (X : Subgroup H) (g : H) :
    conjugate (normalizer (X : Set H)) g = normalizer (conjugate X g : Set H) := by
  ext y
  rw [mem_conjugate_iff]
  constructor
  · intro hy
    apply mem_normalizer_of_conjugate_eq
    rw [conjugate_conjugate, show g * y = (g * y * g⁻¹) * g by group, ← conjugate_conjugate,
      conjugate_eq_of_mem_normalizer hy]
  · intro hy
    apply mem_normalizer_of_conjugate_eq
    have h1 := conjugate_eq_of_mem_normalizer hy
    have : conjugate X (g * y * g⁻¹) = conjugate (conjugate (conjugate X g) y) g⁻¹ := by
      rw [conjugate_conjugate, conjugate_conjugate]
      congr 1
      group
    rw [this, h1, conjugate_conjugate_inv]

theorem conjugate_zpowers' (a g : H) : conjugate (zpowers a) g = zpowers (g⁻¹ * a * g) := by
  rw [conjugate, MonoidHom.map_zpowers]
  congr 1
  simp

theorem conjugate_oddCore (X : Subgroup H) (g : H) :
    conjugate ((pPrimeCore 2 X).map X.subtype) g =
      (pPrimeCore 2 (conjugate X g)).map (conjugate X g).subtype :=
  GSLit.map_map_pPrimeCore (MulAut.conj g⁻¹) X

theorem conjugate_coreActionKernel (X : Subgroup H) (g : H) :
    conjugate (coreActionKernel X) g = coreActionKernel (conjugate X g) := by
  ext y
  rw [mem_conjugate_iff, mem_coreActionKernel, mem_coreActionKernel, ← conjugate_oddCore,
    ← conjugate_normalizer, mem_conjugate_iff]
  constructor
  · rintro ⟨hN, hc⟩
    refine ⟨hN, fun j hj => ?_⟩
    rw [mem_conjugate_iff] at hj ⊢
    have := hc _ hj
    convert this using 1
    group
  · rintro ⟨hN, hc⟩
    refine ⟨hN, fun j hj => ?_⟩
    have hj' : g⁻¹ * j * g ∈ conjugate X g := by
      rw [mem_conjugate_iff, show g * (g⁻¹ * j * g) * g⁻¹ = j by group]
      exact hj
    have := hc _ hj'
    rw [mem_conjugate_iff] at this
    convert this using 1
    group

theorem exists_conj_of_inv_mul {G : Type*} [Group G] {s t : G} (hs : s * s = 1)
    (ht : t * t = 1)
    (hodd : Odd (orderOf (s⁻¹ * t))) : ∃ w ∈ zpowers (s⁻¹ * t), w⁻¹ * s * w = t := by
  set u := s⁻¹ * t with hu
  obtain ⟨k, hk⟩ := hodd
  have hsi : s⁻¹ = s := inv_eq_of_mul_eq_one_right hs
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  have hinv : s⁻¹ * u * s⁻¹⁻¹ = u⁻¹ := by
    rw [hu, inv_inv, mul_inv_rev, inv_inv, hti, hsi]
    calc s * (s * t) * s = (s * s) * t * s := by group
      _ = t * s := by rw [hs, one_mul]
  have hpow : s⁻¹ * u ^ (k + 1) * s = (u ^ (k + 1))⁻¹ := by
    have := conj_pow (a := s⁻¹) (b := u) (i := k + 1)
    rw [hinv, inv_inv, inv_pow] at this
    exact this.symm
  have hu1 : u ^ (2 * k + 1) = 1 := by rw [← hk, pow_orderOf_eq_one]
  refine ⟨u ^ (k + 1), pow_mem (mem_zpowers u) _, ?_⟩
  calc (u ^ (k + 1))⁻¹ * s * u ^ (k + 1)
      = s * (s⁻¹ * u ^ (k + 1) * s)⁻¹ * u ^ (k + 1) := by group
    _ = s * (u ^ (k + 1) * u ^ (k + 1)) := by rw [hpow, inv_inv, mul_assoc]
    _ = s * (u ^ (2 * k + 1) * u) := by rw [← pow_add, ← pow_succ]; ring_nf
    _ = t := by rw [hu1, one_mul, hu]; group

theorem involutions_conj_of_quotient {Y : Type*} [Group Y] [Finite Y]
    (hY : ∀ s t : Y ⧸ pPrimeCore 2 Y, orderOf s = 2 → orderOf t = 2 → ∃ g, g⁻¹ * s * g = t)
    {s t : Y} (hs : orderOf s = 2) (ht : orderOf t = 2) : ∃ g : Y, g⁻¹ * s * g = t := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hodd := CFSG.pPrimeCore_coprime_card (p := 2) (G := Y)
  have hnot : ∀ y : Y, orderOf y = 2 → y ∉ pPrimeCore 2 Y := by
    intro y hy hyO
    have hdvd : orderOf (⟨y, hyO⟩ : pPrimeCore 2 Y) ∣ Nat.card (pPrimeCore 2 Y) :=
      orderOf_dvd_natCard _
    rw [Subgroup.orderOf_mk, hy] at hdvd
    exact absurd (Nat.Coprime.coprime_dvd_right hdvd hodd) (by norm_num)
  have hbar : ∀ y : Y, orderOf y = 2 → orderOf (QuotientGroup.mk y : Y ⧸ pPrimeCore 2 Y) = 2 := by
    intro y hy
    apply orderOf_eq_prime
    · rw [← QuotientGroup.mk_pow, ← hy, pow_orderOf_eq_one, QuotientGroup.mk_one]
    · intro h1
      exact hnot y hy ((QuotientGroup.eq_one_iff y).mp h1)
  obtain ⟨gb, hgb⟩ := hY _ _ (hbar s hs) (hbar t ht)
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective gb
  set s' := g⁻¹ * s * g with hs'
  have hs'2 : orderOf s' = 2 := by
    rw [hs', show g⁻¹ * s * g = (MulAut.conj g⁻¹) s by rw [MulAut.conj_apply, inv_inv],
      MulEquiv.orderOf_eq, hs]
  have hmem : s'⁻¹ * t ∈ pPrimeCore 2 Y := by
    rw [← QuotientGroup.eq]
    rw [hs']
    simpa [QuotientGroup.mk_mul, QuotientGroup.mk_inv] using hgb
  have hss : s' * s' = 1 := by rw [← pow_two, ← hs'2, pow_orderOf_eq_one]
  have htt : t * t = 1 := by rw [← pow_two, ← ht, pow_orderOf_eq_one]
  have hodd' : Odd (orderOf (s'⁻¹ * t)) := by
    have hdvd : orderOf (⟨_, hmem⟩ : pPrimeCore 2 Y) ∣ Nat.card (pPrimeCore 2 Y) :=
      orderOf_dvd_natCard _
    rw [Subgroup.orderOf_mk] at hdvd
    have h2 := Nat.Coprime.coprime_dvd_right hdvd hodd
    rw [Nat.coprime_two_left] at h2
    exact h2
  obtain ⟨w, -, hw⟩ := exists_conj_of_inv_mul hss htt hodd'
  exact ⟨g * w, by rw [← hw, hs']; group⟩

theorem lieModel_psl_two_of_mulEquiv {G G' : Type} [Group G] [Group G'] (e : G ≃* G')
    {p f : ℕ} (h : Blueprint.LieModel G .PSL 2 p f) : Blueprint.LieModel G' .PSL 2 p f :=
  CFSG.Blueprint.LieModel.of_mulEquiv e h

theorem isSmallAltOrL2_of_mulEquiv {G G' : Type} [Group G] [Group G'] (e : G ≃* G')
    (h : IsSmallAltOrL2 G) : IsSmallAltOrL2 G' := by
  rcases h with ⟨n, hn, ⟨e'⟩⟩ | ⟨p, f, hp, hp2, hf, h5, hL⟩
  · exact Or.inl ⟨n, hn, ⟨e.symm.trans e'⟩⟩
  · exact Or.inr ⟨p, f, hp, hp2, hf, h5, lieModel_psl_two_of_mulEquiv e hL⟩

variable [Finite H]

theorem sylow_conjugate {S Y : Subgroup H} (hSY : S ≤ Y)
    (hS : ∃ R : Sylow 2 ↥Y, (R : Subgroup Y) = S.subgroupOf Y) (g : H) :
    conjugate S g ≤ conjugate Y g ∧ ∃ R : Sylow 2 ↥(conjugate Y g),
      (R : Subgroup _) = (conjugate S g).subgroupOf (conjugate Y g) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨R, hR⟩ := hS
  refine ⟨map_mono hSY, ?_⟩
  let e : Y ≃* conjugate Y g := Y.equivMapOfInjective (MulAut.conj g⁻¹).toMonoidHom
    (MulAut.conj g⁻¹).injective
  refine ⟨Sylow.mapSurjective (f := e.toMonoidHom) e.surjective R, ?_⟩
  show (R : Subgroup Y).map e.toMonoidHom = _
  rw [hR]
  ext ⟨y, hy⟩
  simp only [mem_map, mem_subgroupOf, MulEquiv.coe_toMonoidHom]
  constructor
  · rintro ⟨⟨z, hzY⟩, hzS, hze⟩
    have := congrArg Subtype.val hze
    simp only [e] at this
    rw [← this]
    exact mem_map_of_mem _ hzS
  · intro hyS
    obtain ⟨z, hzS, rfl⟩ := mem_map.mp hyS
    exact ⟨⟨z, hSY hzS⟩, hzS, Subtype.ext rfl⟩

theorem sylow_of_card_eq {S R Y : Subgroup H} (hSY : S ≤ Y)
    (hS : ∃ P : Sylow 2 ↥Y, (P : Subgroup Y) = S.subgroupOf Y) (hRY : R ≤ Y)
    (hR : IsPGroup 2 R) (hc : Nat.card R = Nat.card S) :
    ∃ P : Sylow 2 ↥Y, (P : Subgroup Y) = R.subgroupOf Y := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, hP⟩ := hS
  obtain ⟨Q, hQ⟩ := (hR.comap_subtype (K := Y)).exists_le_sylow
  have hcR : Nat.card (R.subgroupOf Y) = Nat.card R := by
    rw [← Subgroup.card_map_of_injective Y.subtype_injective, subgroupOf_map_subtype,
      inf_of_le_left hRY]
  have hcS : Nat.card (S.subgroupOf Y) = Nat.card S := by
    rw [← Subgroup.card_map_of_injective Y.subtype_injective, subgroupOf_map_subtype,
      inf_of_le_left hSY]
  have hPQ : Nat.card (Q : Subgroup Y) = Nat.card (P : Subgroup Y) := by
    rw [Sylow.card_eq_multiplicity, Sylow.card_eq_multiplicity]
  refine ⟨Q, (Subgroup.eq_of_le_of_card_ge hQ ?_).symm⟩
  show Nat.card (Q : Subgroup Y) ≤ Nat.card (R.subgroupOf Y)
  rw [hPQ, hP, hcS, hcR, hc]

theorem exists_conjugate_eq_of_sylow {S₁ S₂ Y : Subgroup H} (h1 : S₁ ≤ Y)
    (hS₁ : ∃ P : Sylow 2 ↥Y, (P : Subgroup Y) = S₁.subgroupOf Y) (h2 : S₂ ≤ Y)
    (hS₂ : ∃ P : Sylow 2 ↥Y, (P : Subgroup Y) = S₂.subgroupOf Y) :
    ∃ c ∈ Y, conjugate S₁ c = S₂ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P₁, hP₁⟩ := hS₁
  obtain ⟨P₂, hP₂⟩ := hS₂
  have hS2 : IsPGroup 2 S₁ := by
    have := P₁.isPGroup'.map Y.subtype
    rwa [hP₁, subgroupOf_map_subtype, inf_of_le_left h1] at this
  obtain ⟨c, hc, hle⟩ := exists_conjugate_le_of_sylow ⟨P₂, hP₂⟩ h1 hS2
  refine ⟨c, hc, Subgroup.eq_of_le_of_card_ge hle ?_⟩
  have hcard : Nat.card (conjugate S₁ c) = Nat.card S₁ :=
    card_map_of_injective (MulAut.conj c⁻¹).injective
  have hPP : Nat.card (P₁ : Subgroup Y) = Nat.card (P₂ : Subgroup Y) := by
    rw [Sylow.card_eq_multiplicity, Sylow.card_eq_multiplicity]
  have hc1 : Nat.card (S₁.subgroupOf Y) = Nat.card S₁ := by
    rw [← Subgroup.card_map_of_injective Y.subtype_injective, subgroupOf_map_subtype,
      inf_of_le_left h1]
  have hc2 : Nat.card (S₂.subgroupOf Y) = Nat.card S₂ := by
    rw [← Subgroup.card_map_of_injective Y.subtype_injective, subgroupOf_map_subtype,
      inf_of_le_left h2]
  rw [hcard, ← hc1, ← hP₁, hPP, hP₂, hc2]

end CFSG.ComponentClassification.GSThmB
