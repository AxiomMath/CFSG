module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog516
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB5bLemma514
public import CFSG.Walter.Bender1970.S2.Involutions

public section

namespace CFSG.ComponentClassification.CatFactsL4U4

open CFSG Subgroup CFSG.ComponentClassification.GSThmB CFSG.Assembly.LowTwoRank
open scoped commutatorElement

theorem map_centralizerCore516 {Y Z : Type*} [Group Y] [Group Z] [Finite Y] [Finite Z]
    (e : Y ≃* Z) (q : ℕ) (ℓ : Y) :
    (centralizerCore516 q ℓ).map e.toMonoidHom = centralizerCore516 q (e ℓ) := by
  have hC : (centralizer ({ℓ} : Set Y)).map e.toMonoidHom = centralizer {e ℓ} := by
    ext z
    rw [mem_map, mem_centralizer_singleton_iff]
    constructor
    · rintro ⟨y, hy, rfl⟩
      rw [mem_centralizer_singleton_iff] at hy
      rw [MulEquiv.coe_toMonoidHom, ← map_mul, ← map_mul, hy]
    · intro hz
      refine ⟨e.symm z, ?_, by rw [MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply]⟩
      rw [mem_centralizer_singleton_iff]
      apply e.injective
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply, hz]
  unfold centralizerCore516
  split_ifs with hq
  · rw [MonoidHom.map_closure]
    congr 1
    ext z
    constructor
    · rintro ⟨y, ⟨hy, hyo⟩, rfl⟩
      refine ⟨?_, by rwa [MulEquiv.coe_toMonoidHom, MulEquiv.orderOf_eq]⟩
      rw [← hC]
      exact ⟨y, hy, rfl⟩
    · rintro ⟨hz, hzo⟩
      rw [← hC] at hz
      obtain ⟨y, hy, rfl⟩ := hz
      exact ⟨y, ⟨hy, by rwa [MulEquiv.coe_toMonoidHom, MulEquiv.orderOf_eq] at hzo⟩, rfl⟩
  · rw [Quasithin.map_perfectCore, hC]

@[expose] def InnerPSpAt {Y : Type} [Group Y] (q p f : ℕ) (ℓ : Y) : Prop :=
  pPrimeCore 2 ↥(centralizerCore516 q ℓ) = ⊥ ∧
    ∀ ε : MulAut Y, ε ^ 2 = 1 → ε ≠ 1 → ε ≠ MulAut.conj ℓ →
      ε * MulAut.conj ℓ = MulAut.conj ℓ * ε → (∀ y ∈ centralizerCore516 q ℓ, ε y = y) →
        ∃ M : Subgroup Y, (∀ y ∈ M, ε y = y) ∧ Blueprint.LieModel ↥M .PSp 2 p f

theorem congr_conj' {Y Z : Type*} [Group Y] [Group Z] (e : Y ≃* Z) (y : Y) :
    MulAut.congr e (MulAut.conj y) = MulAut.conj (e y) := by
  ext x
  simp [MulAut.congr_apply]

theorem InnerPSpAt.of_equiv {Y Z : Type} [Group Y] [Group Z] [Finite Y] [Finite Z] (e : Y ≃* Z)
    {q p f : ℕ} {ℓ : Y} (h : InnerPSpAt q p f (e ℓ)) : InnerPSpAt q p f ℓ := by
  obtain ⟨h1, h2⟩ := h
  have hN := map_centralizerCore516 e q ℓ
  refine ⟨?_, fun ε hε2 hε1 hεℓ hεc hεN => ?_⟩
  · let e' : ↥(centralizerCore516 q ℓ) ≃* ↥(centralizerCore516 q (e ℓ)) :=
      (e.subgroupMap _).trans (MulEquiv.subgroupCongr hN)
    rw [← pPrimeCore_map_iso 2 e'.symm, h1, Subgroup.map_bot]
  · set ε' := MulAut.congr e ε with hε'
    have hε'e : ∀ y, ε' (e y) = e (ε y) := fun y => by
      change e (ε (e.symm (e y))) = e (ε y)
      rw [MulEquiv.symm_apply_apply]
    have hcl : MulAut.congr e (MulAut.conj ℓ) = MulAut.conj (e ℓ) := congr_conj' e ℓ
    obtain ⟨M', hM'fix, hM'⟩ := h2 ε' (by rw [hε', ← map_pow, hε2, map_one])
      (by rw [hε', Ne, MulEquiv.map_eq_one_iff]; exact hε1)
      (by rw [hε', ← hcl, Ne, (MulAut.congr e).injective.eq_iff]; exact hεℓ)
      (by rw [hε', ← hcl, ← map_mul, ← map_mul, hεc])
      (by
        intro y hy
        rw [← hN] at hy
        obtain ⟨x, hx, rfl⟩ := hy
        rw [MulEquiv.coe_toMonoidHom, hε'e, hεN x hx])
    refine ⟨M'.map e.symm.toMonoidHom, ?_,
      lieModel_of_mulEquiv_ne_zero (e.symm.subgroupMap M') (by norm_num) hM'⟩
    rintro _ ⟨m, hm, rfl⟩
    apply e.injective
    rw [MulEquiv.coe_toMonoidHom, ← hε'e, MulEquiv.apply_symm_apply, hM'fix m hm]

theorem normal_closure_of_conj {Y : Type*} [Group Y] {S : Set Y}
    (hS : ∀ g : Y, ∀ s ∈ S, g * s * g⁻¹ ∈ S) : (closure S).Normal := by
  refine ⟨fun n hn g => ?_⟩
  induction hn using Subgroup.closure_induction with
  | mem x hx => exact subset_closure (hS g x hx)
  | one => simp
  | mul x y _ _ hx hy =>
    have : g * (x * y) * g⁻¹ = (g * x * g⁻¹) * (g * y * g⁻¹) := by group
    rw [this]
    exact mul_mem hx hy
  | inv x _ hx =>
    have : g * x⁻¹ * g⁻¹ = (g * x * g⁻¹)⁻¹ := by group
    rw [this]
    exact inv_mem hx

theorem centralizerCore516_one {Y : Type} [Group Y] [Finite Y] [IsSimpleGroup Y]
    (hab : ∃ a b : Y, a * b ≠ b * a) {y₀ : Y} (hy₀ : y₀ ≠ 1) (hy₀o : Odd (orderOf y₀)) (q : ℕ) :
    centralizerCore516 q (1 : Y) = ⊤ := by
  have hC : centralizer ({1} : Set Y) = ⊤ := by
    ext y
    simp [mem_centralizer_singleton_iff]
  unfold centralizerCore516
  split_ifs with hq
  · set S : Set Y := {y : Y | y ∈ centralizer ({1} : Set Y) ∧ Odd (orderOf y)} with hS
    have hn : (closure S).Normal := normal_closure_of_conj fun g s hs => by
      refine ⟨by rw [hC]; exact mem_top _, ?_⟩
      have : orderOf (g * s * g⁻¹) = orderOf s := by
        rw [← MulAut.conj_apply, MulEquiv.orderOf_eq]
      rw [this]
      exact hs.2
    rcases hn.eq_bot_or_eq_top with h | h
    · exfalso
      apply hy₀
      have : y₀ ∈ closure S := subset_closure ⟨by rw [hC]; exact mem_top _, hy₀o⟩
      rwa [h, mem_bot] at this
    · exact h
  · rw [hC]
    apply Quasithin.perfectCore_eq_self_of_perfect
    have hn : Subgroup.Normal (⁅(⊤ : Subgroup Y), (⊤ : Subgroup Y)⁆) := inferInstance
    rcases hn.eq_bot_or_eq_top with h | h
    · exfalso
      obtain ⟨a, b, hab⟩ := hab
      apply hab
      have : ⁅a, b⁆ ∈ ⁅(⊤ : Subgroup Y), ⊤⁆ := commutator_mem_commutator (mem_top a) (mem_top b)
      rw [h, mem_bot, commutatorElement_eq_one_iff_mul_comm] at this
      exact this
    · exact h

theorem innerPSpAt_one {Y : Type} [Group Y] [Finite Y] [IsSimpleGroup Y]
    (hab : ∃ a b : Y, a * b ≠ b * a) {y₀ : Y} (hy₀ : y₀ ≠ 1) (hy₀o : Odd (orderOf y₀))
    (q p f : ℕ) : InnerPSpAt q p f (1 : Y) := by
  have hN := centralizerCore516_one hab hy₀ hy₀o q
  refine ⟨?_, fun ε _ hε1 _ _ hεN => ?_⟩
  · rw [← pPrimeCore_map_iso 2 ((MulEquiv.subgroupCongr hN).trans Subgroup.topEquiv).symm,
      Walter.pPrimeCore_eq_bot_of_isSimpleGroup hab, Subgroup.map_bot]
  · exfalso
    apply hε1
    ext y
    exact hεN y (by rw [hN]; exact mem_top y)

theorem pPrimeCore_centralizerCore516_eq_bot {Y : Type} [Group Y] [Finite Y] {q : ℕ} {ℓ : Y}
    {S : Subgroup Y} (hS : S ≤ centralizer {ℓ}) (hNS : centralizerCore516 q ℓ ≤ S)
    (hodd : ∀ R : Subgroup Y, R ≤ S → (∀ g ∈ S, ∀ r ∈ R, g * r * g⁻¹ ∈ R) →
      Odd (Nat.card R) → R = ⊥) :
    pPrimeCore 2 ↥(centralizerCore516 q ℓ) = ⊥ := by
  set N := centralizerCore516 q ℓ with hNdef
  set R₀ := pPrimeCore 2 ↥N with hR₀
  set R := R₀.map N.subtype with hR
  have hRN : R ≤ N := by
    rintro _ ⟨x, -, rfl⟩
    exact x.2
  have hconj : ∀ g ∈ S, ∀ r ∈ R, g * r * g⁻¹ ∈ R := by
    intro g hg r hr
    have hgℓ : g * ℓ * g⁻¹ = ℓ := by
      rw [mem_centralizer_singleton_iff.mp (hS hg), mul_inv_cancel_right]
    have hNg : N.map (MulAut.conj g).toMonoidHom = N := by
      rw [hNdef, map_centralizerCore516, MulAut.conj_apply, hgℓ]
    let σ : ↥N ≃* ↥N := ((MulAut.conj g).subgroupMap N).trans (MulEquiv.subgroupCongr hNg)
    have hσ : ∀ x : ↥N, (σ x : Y) = g * x * g⁻¹ := fun x => rfl
    have hR₀σ := pPrimeCore_map_iso 2 σ
    obtain ⟨x, hx, rfl⟩ := hr
    rw [← hR₀] at hR₀σ
    have : σ x ∈ R₀ := by
      rw [← hR₀σ]
      exact ⟨x, hx, rfl⟩
    exact ⟨σ x, this, by rw [Subgroup.coe_subtype, hσ]⟩
  have hcard : Nat.card R = Nat.card R₀ := card_map_of_injective N.subtype_injective
  have hodd' : Odd (Nat.card R) := by
    rw [hcard]
    have hcop : Nat.Coprime 2 (Nat.card R₀) := pPrimeCore_coprime_card
    rcases Nat.even_or_odd (Nat.card R₀) with he | ho
    · exact absurd (Nat.Coprime.coprime_dvd_right (even_iff_two_dvd.1 he) hcop) (by norm_num)
    · exact ho
  have hR1 := hodd R (hRN.trans hNS) hconj hodd'
  rw [hR, Subgroup.map_eq_bot_iff_of_injective _ N.subtype_injective] at hR1
  exact hR1

theorem eq_bot_of_le_simple {Y : Type} [Group Y] [Finite Y] {S : Subgroup Y}
    [IsSimpleGroup ↥S] (hS : Even (Nat.card S)) (R : Subgroup Y) (hRS : R ≤ S)
    (hR : ∀ g ∈ S, ∀ r ∈ R, g * r * g⁻¹ ∈ R) (hodd : Odd (Nat.card R)) : R = ⊥ := by
  have hn : (R.subgroupOf S).Normal :=
    ⟨fun n hn g => by
      rw [mem_subgroupOf] at hn ⊢
      exact hR g g.2 n hn⟩
  rcases hn.eq_bot_or_eq_top with h | h
  · rw [subgroupOf_eq_bot] at h
    exact disjoint_self.mp (h.mono_right hRS)
  · exfalso
    rw [subgroupOf_eq_top] at h
    have : R = S := le_antisymm hRS h
    rw [this] at hodd
    exact (Nat.not_even_iff_odd.mpr hodd) hS

theorem lieModel_range_of_ker {G : Type} [Group G] {F : Type} [Field F] [Finite F] {p f : ℕ}
    (hp : p.Prime) (hf : 1 ≤ f) (hF : Nat.card F = p ^ f) (h2 : p ^ f ≠ 2)
    (φ : StatedSp 2 F →* G)
    (hker : φ.ker = (StatedScalars (Fin 2 ⊕ Fin 2) F).subgroupOf (StatedSp 2 F)) :
    Blueprint.LieModel ↥φ.range .PSp 2 p f :=
  Or.inl ⟨by decide, ⟨hp, hf, le_refl 2, fun h => h2 (Prod.mk.inj h).2⟩, F, inferInstance,
    inferInstance, hF,
    ⟨(QuotientGroup.quotientKerEquivRange φ).symm.trans (QuotientGroup.quotientMulEquivOfEq hker)⟩⟩

end CFSG.ComponentClassification.CatFactsL4U4
