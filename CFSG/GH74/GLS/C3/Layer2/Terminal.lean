module

public import CFSG.GH74.GLS.C3.Layer2.LocalBasic

public section

namespace CFSG.GH74.GLS

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS.C3.Layer2
open scoped commutatorElement

private def terminalKlein : Subgroup (Equiv.Perm (Fin 4)) where
  carrier := {σ | σ = 1 ∨ σ = Equiv.swap 0 1 * Equiv.swap 2 3 ∨
    σ = Equiv.swap 0 2 * Equiv.swap 1 3 ∨ σ = Equiv.swap 0 3 * Equiv.swap 1 2}
  mul_mem' := by
    intro a b ha hb
    rcases ha with rfl | rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl | rfl <;> decide
  one_mem' := Or.inl rfl
  inv_mem' := by
    intro a ha
    rcases ha with rfl | rfl | rfl | rfl <;> decide

private theorem terminalKlein_card : Nat.card terminalKlein = 4 := by
  classical
  have h : ∀ σ : Equiv.Perm (Fin 4), σ ∈ terminalKlein ↔ σ ∈ ({1, Equiv.swap 0 1 * Equiv.swap 2 3,
      Equiv.swap 0 2 * Equiv.swap 1 3, Equiv.swap 0 3 * Equiv.swap 1 2} :
        Finset (Equiv.Perm (Fin 4))) := by
    intro σ
    simp only [Finset.mem_insert, Finset.mem_singleton]
    exact Iff.rfl
  rw [Nat.card_congr (Equiv.subtypeEquivRight h), Nat.card_eq_finsetCard]
  decide

private theorem terminalKlein_isElementaryAbelian : IsElementaryAbelian 2 terminalKlein := by
  refine { toIsMulCommutative := ⟨⟨fun a b => ?_⟩⟩, exponent_dvd_p := ?_ }
  · obtain ⟨a, ha⟩ := a
    obtain ⟨b, hb⟩ := b
    apply Subtype.ext
    rcases ha with rfl | rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl | rfl <;> decide
  · refine Monoid.exponent_dvd_iff_forall_pow_eq_one.2 ?_
    intro σ
    obtain ⟨σ, hσ⟩ := σ
    apply Subtype.ext
    rcases hσ with rfl | rfl | rfl | rfl <;> decide

private theorem terminalKlein_sign : ∀ σ ∈ terminalKlein, Equiv.Perm.sign σ = 1 := by
  intro σ hσ
  rcases hσ with rfl | rfl | rfl | rfl <;> decide

private theorem alternatingGroup_exists_klein {n : ℕ} (hn : 4 ≤ n) :
    ∃ V : Subgroup (alternatingGroup (Fin n)), Nat.card V = 4 ∧ IsElementaryAbelian 2 V := by
  have : IsElementaryAbelian 2 terminalKlein := terminalKlein_isElementaryAbelian
  set φ := Equiv.Perm.viaEmbeddingHom (Fin.castLEEmb hn) with hφ
  have hle : terminalKlein.map φ ≤ alternatingGroup (Fin n) := by
    rintro _ ⟨σ, hσ, rfl⟩
    rw [Equiv.Perm.mem_alternatingGroup, hφ, Equiv.Perm.viaEmbeddingHom_apply,
      Equiv.Perm.viaEmbedding, Equiv.Perm.sign_extendDomain]
    exact terminalKlein_sign σ hσ
  have : IsElementaryAbelian 2 (terminalKlein.map φ) := IsElementaryAbelian.map φ
  refine ⟨(terminalKlein.map φ).subgroupOf (alternatingGroup (Fin n)), ?_,
    isElementaryAbelian_subgroupOf hle⟩
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv,
    Subgroup.card_map_of_injective (Equiv.Perm.viaEmbeddingHom_injective _), terminalKlein_card]

private theorem center_eq_bot_of_mulEquiv {A B : Type*} [Group A] [Group B] (e : A ≃* B)
    (hB : center B = ⊥) : center A = ⊥ := by
  rw [eq_bot_iff]
  intro z hz
  have hez : e z ∈ center B := by
    rw [Subgroup.mem_center_iff]
    intro b
    obtain ⟨c, rfl⟩ := e.surjective b
    rw [← map_mul, ← map_mul, (Subgroup.mem_center_iff.1 hz) c]
  rw [hB, Subgroup.mem_bot] at hez
  rw [Subgroup.mem_bot]
  exact e.injective (hez.trans (map_one e).symm)

private theorem isPComponent_two_of_normal {X : Type*} [Group X] [Finite X] {L : Subgroup X}
    (hLn : L.Normal) (hL : IsQuasisimple L) (hZ : center L = ⊥) (h2 : 2 ∣ Nat.card L) :
    IsPComponent 2 L := by
  have hcore : L ⊓ pPrimeCore 2 X = ⊥ := by
    have hN : ((pPrimeCore 2 X).subgroupOf L).Normal := Subgroup.Normal.subgroupOf inferInstance L
    rcases CFSG.LocalCores.quasisimple_normal_subgroups hL hN with htop | hcen
    · exfalso
      have hle : L ≤ pPrimeCore 2 X := fun l hl => by
        have : (⟨l, hl⟩ : L) ∈ (pPrimeCore 2 X).subgroupOf L := htop ▸ Subgroup.mem_top _
        exact this
      have hcop : Nat.Coprime 2 (Nat.card (pPrimeCore 2 X)) := pPrimeCore_coprime_card
      exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).1 hcop
        (h2.trans (Subgroup.card_dvd_of_le hle))
    · rw [hZ] at hcen
      rw [eq_bot_iff]
      rintro y ⟨hyL, hyO⟩
      have hy : (⟨y, hyL⟩ : L) ∈ (pPrimeCore 2 X).subgroupOf L := hyO
      have hy1 := hcen hy
      rw [Subgroup.mem_bot] at hy1 ⊢
      exact congrArg Subtype.val hy1
  set π := QuotientGroup.mk' (pPrimeCore 2 X) with hπ
  have hinj : ∀ a ∈ L, ∀ b ∈ L, π a = π b → a = b := by
    intro a ha b hb hab
    have h1 : a⁻¹ * b ∈ pPrimeCore 2 X := QuotientGroup.eq.mp hab
    have h2 : a⁻¹ * b ∈ L ⊓ pPrimeCore 2 X := Subgroup.mem_inf.2 ⟨mul_mem (inv_mem ha) hb, h1⟩
    rw [hcore, Subgroup.mem_bot, inv_mul_eq_one] at h2
    exact h2
  refine ⟨L.map π, ⟨?_, ?_⟩, hLn.isSubnormal, rfl, ?_⟩
  · have hφ : Function.Injective (π.comp L.subtype) := fun a b hab =>
      Subtype.ext (hinj a a.2 b b.2 hab)
    have hr : (π.comp L.subtype).range = L.map π := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype]
    exact CFSG.LocalCores.isQuasisimple_of_mulEquiv
      ((MonoidHom.ofInjective hφ).trans (MulEquiv.subgroupCongr hr)) hL
  · exact (hLn.map π (QuotientGroup.mk'_surjective _)).isSubnormal
  · intro J hJL _ hJmap
    apply (lt_iff_le_not_ge.1 hJL).2
    intro l hl
    have hl' : π l ∈ J.map π := hJmap ▸ ⟨l, hl, rfl⟩
    obtain ⟨j, hj, hjl⟩ := hl'
    rw [← hinj j (hJL.le hj) l hl hjl]
    exact hj

private theorem mem_centralizerSection_bot_iff {G : Type*} [Group G] {K : Subgroup G} {c : G} :
    c ∈ centralizerSection K ⊥ ↔ ∀ k ∈ K, k * c = c * k := by
  refine ⟨fun ⟨_, _, hk⟩ k hk' => ?_, fun hc' => ?_⟩
  · have := hk k hk'
    rw [Subgroup.mem_bot] at this
    exact commutatorElement_eq_one_iff_mul_comm.1 this
  · have hfix : ∀ k' ∈ K, c * k' * c⁻¹ = k' := fun k' hk' => by
      rw [← hc' k' hk']; group
    have hfix' : ∀ k' ∈ K, c⁻¹ * k' * c = k' := fun k' hk' => by
      rw [mul_assoc, hc' k' hk', ← mul_assoc]; simp
    refine ⟨?_, ?_, fun k hk => ?_⟩
    · rw [mem_normalizer_iff]
      intro k
      refine ⟨fun hk => by rw [hfix k hk]; exact hk, fun hk' => ?_⟩
      have h1 := hfix' _ hk'
      have h2 : c⁻¹ * (c * k * c⁻¹) * c = k := by group
      rw [h2] at h1
      rw [h1]; exact hk'
    · rw [mem_normalizer_iff]
      intro k
      simp [Subgroup.mem_bot]
    · rw [Subgroup.mem_bot]
      exact commutatorElement_eq_one_iff_mul_comm.2 (hc' k hk)

private theorem le_pRank_of_card_le {H : Type*} [Group H] [Finite H] (A : Subgroup H)
    [IsElementaryAbelian 2 A] {k : ℕ} (hk : 2 ^ k ≤ Nat.card A) : k ≤ pRank 2 H := by
  obtain ⟨r, hr⟩ := IsPGroup.iff_card.mp (IsElementaryAbelian.isPGroup 2 A)
  have hle : r ≤ pRank 2 H := by
    refine le_csSup ⟨Nat.card H, ?_⟩ ⟨A, inferInstance, hr⟩
    rintro s ⟨B, -, hB⟩
    calc s ≤ 2 ^ s := (Nat.lt_pow_self (by norm_num)).le
      _ = Nat.card B := hB.symm
      _ ≤ Nat.card H := Subgroup.card_le_card_group B
  rw [hr] at hk
  exact ((Nat.pow_le_pow_iff_right (by norm_num)).1 hk).trans hle

private theorem card_le_two_mul_card {G : Type*} [Group G] [Finite G] {R R₀ : Subgroup G}
    (h : ∀ r ∈ R, ∀ s ∈ R, r ∉ R₀ → s ∉ R₀ → r⁻¹ * s ∈ R₀) :
    Nat.card R ≤ 2 * Nat.card R₀ := by
  classical
  by_cases hex : ∃ r₀ ∈ R, r₀ ∉ R₀
  · obtain ⟨r₀, hr₀R, hr₀⟩ := hex
    let f : R → R₀ ⊕ R₀ := fun r =>
      if hr : (r : G) ∈ R₀ then Sum.inl ⟨r, hr⟩ else Sum.inr ⟨r₀⁻¹ * r, h r₀ hr₀R r r.2 hr₀ hr⟩
    have hf : Function.Injective f := by
      intro u v huv
      by_cases hu : (u : G) ∈ R₀ <;> by_cases hv : (v : G) ∈ R₀ <;>
        simp only [f, hu, hv, dite_true, dite_false, reduceCtorEq, Sum.inl.injEq, Sum.inr.injEq,
          Subtype.mk.injEq] at huv
      · exact Subtype.ext huv
      · exact Subtype.ext (mul_left_cancel huv)
    have := Nat.card_le_card_of_injective f hf
    rwa [Nat.card_sum, ← two_mul] at this
  · push Not at hex
    have hle : R ≤ R₀ := hex
    have := Subgroup.card_le_of_le hle
    omega

private theorem two_mul_card_le_card {G : Type*} [Group G] [Finite G] {A H : Subgroup G}
    (hAH : A ≤ H) {t : G} (htH : t ∈ H) (htA : t ∉ A) : 2 * Nat.card A ≤ Nat.card H := by
  classical
  let f : A ⊕ A → H := fun z => match z with
    | Sum.inl y => ⟨y, hAH y.2⟩
    | Sum.inr y => ⟨t * y, mul_mem htH (hAH y.2)⟩
  have hf : Function.Injective f := by
    rintro (u | u) (v | v) huv <;> simp only [f, Subtype.mk.injEq] at huv
    · rw [Subtype.ext huv]
    · exfalso
      apply htA
      have : t = u * (v : G)⁻¹ := by rw [huv]; group
      rw [this]
      exact mul_mem u.2 (inv_mem v.2)
    · exfalso
      apply htA
      have : t = v * (u : G)⁻¹ := by rw [← huv]; group
      rw [this]
      exact mul_mem v.2 (inv_mem u.2)
    · rw [Subtype.ext (mul_left_cancel huv)]
  have := Nat.card_le_card_of_injective f hf
  rwa [Nat.card_sum, ← two_mul] at this

private theorem eq_of_card_eq_four {G : Type*} [Group G] {Q : Subgroup G} (hQ : Nat.card Q = 4)
    {a b c d : G} (ha : a ∈ Q) (hb : b ∈ Q) (hc : c ∈ Q) (hd : d ∈ Q)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    {y : G} (hy : y ∈ Q) : y = a ∨ y = b ∨ y = c ∨ y = d := by
  classical
  have : Finite Q := Nat.finite_of_card_ne_zero (by rw [hQ]; norm_num)
  by_contra hne
  simp only [not_or] at hne
  obtain ⟨h1, h2, h3, h4⟩ := hne
  have hsub : ∀ z ∈ ({y, a, b, c, d} : Finset G), z ∈ Q := by
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl | rfl | rfl | rfl <;> assumption
  have hcard : ({y, a, b, c, d} : Finset G).card = 5 := by
    rw [Finset.card_insert_of_notMem (by simp [h1, h2, h3, h4]),
      Finset.card_insert_of_notMem (by simp [hab, hac, had]),
      Finset.card_insert_of_notMem (by simp [hbc, hbd]), Finset.card_pair hcd]
  have hle := Nat.card_le_card_of_injective
    (fun z : ({y, a, b, c, d} : Finset G) => (⟨z.1, hsub z.1 z.2⟩ : Q))
    (fun z w hzw => Subtype.ext (Subtype.mk.inj hzw))
  rw [Nat.card_eq_finsetCard, hcard, hQ] at hle
  omega

private theorem exists_conj_mem_of_isSylowOf {G : Type*} [Group G] [Finite G] {p : ℕ}
    [Fact p.Prime] {P K X : Subgroup G} (hP : IsSylowOf p P K) (hXK : X ≤ K) (hX : IsPGroup p X) :
    ∃ k ∈ K, ∀ y ∈ X, k⁻¹ * y * k ∈ P := by
  obtain ⟨Q, rfl⟩ := hP
  obtain ⟨Q', hQ'⟩ := (hX.comap_subtype (K := K)).exists_le_sylow
  obtain ⟨c, rfl⟩ := MulAction.exists_smul_eq K Q Q'
  refine ⟨c, c.2, fun y hy => ?_⟩
  have hy' : (⟨y, hXK hy⟩ : K) ∈ ((c • Q : Sylow p K) : Subgroup K) := hQ' hy
  rw [Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hy'
  exact ⟨_, hy', by simp [MulAut.inv_apply]⟩

private theorem pLayerOf_two_le {G : Type*} [Group G] (H : Subgroup G) :
    pLayerOf 2 H ≤ H := by
  unfold pLayerOf
  exact sSup_le fun _ hL => hL.1

variable {G : Type} [Group G] [Finite G] {n : ℕ} {x : G} {K T Q S : Subgroup G} {a : G}

namespace IsAConfig

private theorem center_K (h : IsAConfig n x K T Q S a) (hn : 5 ≤ n) : center K = ⊥ := by
  obtain ⟨e⟩ := h.K_equiv_alt
  exact center_eq_bot_of_mulEquiv e (alternatingGroup.center_eq_bot (by simp; omega))

private theorem eq_one_of_central (h : IsAConfig n x K T Q S a) (hn : 5 ≤ n) {y : G}
    (hyK : y ∈ K) (hy : ∀ k ∈ K, k * y = y * k) : y = 1 := by
  have hc : (⟨y, hyK⟩ : K) ∈ center K := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (hy g g.2)
  rw [h.center_K hn, Subgroup.mem_bot] at hc
  exact congrArg Subtype.val hc

private theorem exists_klein (h : IsAConfig n x K T Q S a) (hn : 5 ≤ n) :
    ∃ E : Subgroup G, E ≤ K ∧ Nat.card E = 4 ∧ IsElementaryAbelian 2 E := by
  obtain ⟨e⟩ := h.K_equiv_alt
  obtain ⟨V, hV4, hVel⟩ := alternatingGroup_exists_klein (n := n) (by omega)
  let f : alternatingGroup (Fin n) →* G := K.subtype.comp e.symm.toMonoidHom
  have hf : Function.Injective f := K.subtype_injective.comp e.symm.injective
  refine ⟨V.map f, ?_, ?_, IsElementaryAbelian.map f⟩
  · rintro _ ⟨v, -, rfl⟩
    exact (e.symm v).2
  · rw [Subgroup.card_map_of_injective hf, hV4]

private theorem isQuasisimple_K (h : IsAConfig n x K T Q S a) : IsQuasisimple K := by
  obtain ⟨-, ⟨hKC, hKcomp⟩, -⟩ := h.terminal
  exact CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hKC) hKcomp.1

private theorem two_dvd_card_K (h : IsAConfig n x K T Q S a) : 2 ∣ Nat.card K := by
  obtain ⟨-, -, h2, -⟩ := h.terminal
  exact h2

private theorem orderOf_eq_two (h : IsAConfig n x K T Q S a) {q : G} (hqQ : q ∈ Q)
    (hq1 : q ≠ 1) : orderOf q = 2 :=
  orderOf_eq_prime (h.Q_sq hqQ) hq1

private theorem mem_centralizer_K (h : IsAConfig n x K T Q S a) {q : G} (hqQ : q ∈ Q) :
    q ∈ centralizer (K : Set G) :=
  mem_centralizer_iff.2 ((h.mem_Q_iff q).1 hqQ).2

private theorem isCompIn_centralizer (h : IsAConfig n x K T Q S a) {q : G} (hqQ : q ∈ Q)
    (hq1 : q ≠ 1) : IsCompIn (centralizer ({q} : Set G)) K := by
  obtain ⟨-, -, -, hy⟩ := h.terminal
  exact hy q (h.orderOf_eq_two hqQ hq1) (h.mem_centralizer_K hqQ)

private theorem conj_mem_K (h : IsAConfig n x K T Q S a) (hn : 5 ≤ n) (hG4 : pRank 2 G ≤ 4)
    {q : G} (hqQ : q ∈ Q) (hq1 : q ≠ 1) {r : G} (hr : r ∈ centralizer ({q} : Set G)) :
    ∀ k ∈ K, r * k * r⁻¹ ∈ K := by
  obtain ⟨hKC1, hKcomp⟩ := h.isCompIn_centralizer hqQ hq1
  set C₁ := centralizer ({q} : Set G) with hC₁
  set r' : C₁ := ⟨r, hr⟩ with hr'
  have hL' : IsComponent ((K.subgroupOf C₁).map (MulAut.conj r').toMonoidHom) :=
    CFSG.LocalCores.isComponent_map_mulEquiv (MulAut.conj r') hKcomp
  rcases CFSG.LocalCores.distinct_components_commute hKcomp hL' with heq | hcomm
  · intro k hk
    have hmem : (MulAut.conj r').toMonoidHom ⟨k, hKC1 hk⟩ ∈
        (K.subgroupOf C₁).map (MulAut.conj r').toMonoidHom :=
      Subgroup.mem_map_of_mem _ (show (⟨k, hKC1 hk⟩ : C₁) ∈ K.subgroupOf C₁ from hk)
    rw [← heq] at hmem
    exact hmem
  exfalso
  have hcomm' : ∀ k ∈ K, ∀ k₀ ∈ K, k * (r * k₀ * r⁻¹) = (r * k₀ * r⁻¹) * k := by
    intro k hk k₀ hk₀
    have hmem : ⁅(⟨k, hKC1 hk⟩ : C₁), (MulAut.conj r').toMonoidHom ⟨k₀, hKC1 hk₀⟩⁆ ∈
        ⁅K.subgroupOf C₁, (K.subgroupOf C₁).map (MulAut.conj r').toMonoidHom⁆ :=
      Subgroup.commutator_mem_commutator (show (⟨k, hKC1 hk⟩ : C₁) ∈ K.subgroupOf C₁ from hk)
        (Subgroup.mem_map_of_mem _ (show (⟨k₀, hKC1 hk₀⟩ : C₁) ∈ K.subgroupOf C₁ from hk₀))
    rw [hcomm, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hmem
    have := congrArg Subtype.val hmem
    simpa [MulAut.conj_apply, hr'] using this
  have hrq : Commute r q := mem_centralizer_singleton_iff.1 hr
  have hKq : ∀ k ∈ K, Commute k q := fun k hk => ((h.mem_Q_iff q).1 hqQ).2 k hk
  have hqK' : ∀ k ∈ K, Commute (r * k * r⁻¹) q := fun k hk =>
    (hrq.mul_left (hKq k hk)).mul_left hrq.inv_left
  have hZK' : ∀ k ∈ K, (∀ k₀ ∈ K, (r * k₀ * r⁻¹) * (r * k * r⁻¹) = (r * k * r⁻¹) * (r * k₀ * r⁻¹)) →
      r * k * r⁻¹ = 1 := by
    intro k hk hc
    have hk1 : k = 1 := h.eq_one_of_central hn hk fun k₀ hk₀ => by
      have := hc k₀ hk₀
      have h2 : r * (k₀ * k) * r⁻¹ = r * (k * k₀) * r⁻¹ := by
        calc r * (k₀ * k) * r⁻¹ = (r * k₀ * r⁻¹) * (r * k * r⁻¹) := by group
          _ = (r * k * r⁻¹) * (r * k₀ * r⁻¹) := this
          _ = r * (k * k₀) * r⁻¹ := by group
      simpa using h2
    rw [hk1]; group
  obtain ⟨E₁, hE₁K, hE₁4, hE₁el⟩ := h.exists_klein hn
  set E₂ := E₁.map (MulAut.conj r).toMonoidHom with hE₂
  have hE₂el : IsElementaryAbelian 2 E₂ := IsElementaryAbelian.map _
  have hE₂4 : Nat.card E₂ = 4 := by
    rw [hE₂, Subgroup.card_map_of_injective (MulAut.conj r).injective, hE₁4]
  have hmemE₂ : ∀ y ∈ E₂, ∃ k ∈ K, y = r * k * r⁻¹ := by
    rintro _ ⟨k, hk, rfl⟩
    exact ⟨k, hE₁K hk, by simp [MulAut.conj_apply]⟩
  have hq2 : q ^ 2 = 1 := h.Q_sq hqQ
  have hzel : IsElementaryAbelian 2 (zpowers q) := IsElementaryAbelian.zpowers_of_pow_eq_one hq2
  have hz2 : Nat.card (zpowers q) = 2 := by
    rw [Nat.card_zpowers, h.orderOf_eq_two hqQ hq1]
  have hqE₂ : zpowers q ≤ centralizer (E₂ : Set G) := by
    rw [zpowers_le, mem_centralizer_iff]
    intro y hy
    obtain ⟨k, hk, rfl⟩ := hmemE₂ y hy
    exact (hqK' k hk).eq
  set B := E₂ ⊔ zpowers q with hB
  have hBel : IsElementaryAbelian 2 B := IsElementaryAbelian.sup_of_le_centralizer hqE₂
  have hBK : B ≤ centralizer (K : Set G) := by
    refine sup_le ?_ (zpowers_le.2 (h.mem_centralizer_K hqQ))
    intro y hy
    rw [mem_centralizer_iff]
    intro k hk
    obtain ⟨k₀, hk₀, rfl⟩ := hmemE₂ y hy
    exact hcomm' k hk k₀ hk₀
  have hBE₁ : B ≤ centralizer (E₁ : Set G) := hBK.trans (Subgroup.centralizer_le hE₁K)
  set W := E₁ ⊔ B with hW
  have hWel : IsElementaryAbelian 2 W := IsElementaryAbelian.sup_of_le_centralizer hBE₁
  have hinf₁ : E₂ ⊓ zpowers q = ⊥ := by
    rw [eq_bot_iff]
    rintro y ⟨hyE, hyq⟩
    obtain ⟨k, hk, rfl⟩ := hmemE₂ y hyE
    rw [Subgroup.mem_bot]
    refine hZK' k hk fun k₀ hk₀ => ?_
    have hc : r * k * r⁻¹ ∈ centralizer ({r * k₀ * r⁻¹} : Set G) := by
      have hqc : q ∈ centralizer ({r * k₀ * r⁻¹} : Set G) :=
        mem_centralizer_singleton_iff.2 (hqK' k₀ hk₀).eq.symm
      exact (zpowers_le.2 hqc) hyq
    exact (mem_centralizer_singleton_iff.1 hc).symm
  have hinf₂ : E₁ ⊓ B = ⊥ := by
    rw [eq_bot_iff]
    rintro y ⟨hyE, hyB⟩
    rw [Subgroup.mem_bot]
    exact h.eq_one_of_central hn (hE₁K hyE) fun k hk => mem_centralizer_iff.1 (hBK hyB) k hk
  have hcB := card_mul_card_le_inf_mul_of_comm E₂ (zpowers q) B le_sup_left le_sup_right
    (fun v hv w hw => setLike_mul_comm hv hw)
  rw [hinf₁, Subgroup.card_bot, one_mul, hE₂4, hz2] at hcB
  have hcW := card_mul_card_le_inf_mul_of_comm E₁ B W le_sup_left le_sup_right
    (fun v hv w hw => setLike_mul_comm hv hw)
  rw [hinf₂, Subgroup.card_bot, one_mul, hE₁4] at hcW
  have hWle := card_elemAb_le_pow_pRank W
  have hpow : 2 ^ pRank 2 G ≤ 2 ^ 4 := Nat.pow_le_pow_right (by norm_num) hG4
  omega

private theorem C_le_normalizer (h : IsAConfig n x K T Q S a) (hn : 5 ≤ n)
    (hG4 : pRank 2 G ≤ 4) {q : G} (hqQ : q ∈ Q) (hq1 : q ≠ 1) :
    centralizer ({q} : Set G) ≤ normalizer (K : Set G) := by
  intro c hc
  rw [mem_normalizer_iff]
  intro k
  refine ⟨fun hk => h.conj_mem_K hn hG4 hqQ hq1 hc k hk, fun hk => ?_⟩
  have := h.conj_mem_K hn hG4 hqQ hq1 (inv_mem hc) _ hk
  simpa [mul_assoc] using this

private theorem isPCompIn_self (h : IsAConfig n x K T Q S a) (hn : 5 ≤ n) : IsPCompIn 2 K K := by
  refine ⟨le_rfl, ?_⟩
  rw [Subgroup.subgroupOf_self]
  refine isPComponent_two_of_normal inferInstance ?_ ?_ ?_
  · exact CFSG.LocalCores.isQuasisimple_of_mulEquiv Subgroup.topEquiv.symm h.isQuasisimple_K
  · exact center_eq_bot_of_mulEquiv Subgroup.topEquiv (h.center_K hn)
  · rw [Nat.card_congr Subgroup.topEquiv.toEquiv]
    exact h.two_dvd_card_K

private theorem isPCompIn_centralizer (h : IsAConfig n x K T Q S a) (hn : 5 ≤ n)
    {q : G} (hqQ : q ∈ Q) (hq1 : q ≠ 1)
    (hN : centralizer ({q} : Set G) ≤ normalizer (K : Set G)) :
    IsPCompIn 2 (centralizer ({q} : Set G)) K := by
  obtain ⟨hKC1, hKcomp⟩ := h.isCompIn_centralizer hqQ hq1
  refine ⟨hKC1, isPComponent_two_of_normal ?_ hKcomp.1 ?_ ?_⟩
  · exact (Subgroup.normal_subgroupOf_iff_le_normalizer hKC1).mpr hN
  · exact center_eq_bot_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hKC1) (h.center_K hn)
  · rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKC1).toEquiv]
    exact h.two_dvd_card_K

private theorem pLayerOf_K (h : IsAConfig n x K T Q S a) (hn : 5 ≤ n) : pLayerOf 2 K = K := by
  refine le_antisymm (pLayerOf_two_le K) ?_
  unfold pLayerOf
  exact le_sSup (h.isPCompIn_self hn)

private theorem pumpUp_K (h : IsAConfig n x K T Q S a) (hn : 5 ≤ n)
    {q : G} (hqQ : q ∈ Q) (hq1 : q ≠ 1)
    (hN : centralizer ({q} : Set G) ≤ normalizer (K : Set G)) : pumpUp 2 K q = K := by
  have hKC1 : K ≤ centralizer ({q} : Set G) := (h.isCompIn_centralizer hqQ hq1).1
  unfold pumpUp
  rw [inf_eq_left.2 hKC1, h.pLayerOf_K hn]
  apply le_antisymm
  · refine iSup₂_le fun g hg => ?_
    rintro _ ⟨k, hk, rfl⟩
    simpa [MulAut.conj_apply] using
      (Subgroup.mem_normalizer_iff.1 (hN (pLayerOf_two_le _ hg)) k).1 hk
  · intro k hk
    exact le_iSup₂ (f := fun g _ => K.map (MulAut.conj g).toMonoidHom) (1 : G) (one_mem _)
      ⟨k, hk, by simp⟩

private theorem isILo_q (h : IsAConfig n x K T Q S a) (hn : 5 ≤ n)
    {q : G} (hqQ : q ∈ Q) (hq1 : q ≠ 1)
    (hN : centralizer ({q} : Set G) ≤ normalizer (K : Set G)) : IsILo 2 q K := by
  have hKq := h.isPCompIn_centralizer hn hqQ hq1 hN
  refine ⟨h.orderOf_eq_two hqQ hq1, ?_, hKq⟩
  have h3 : oBound 2 = 3 := by unfold oBound; simp
  rw [h3]
  obtain ⟨E₁, hE₁K, hE₁4, hE₁el⟩ := h.exists_klein hn
  have hzel : IsElementaryAbelian 2 (zpowers q) :=
    IsElementaryAbelian.zpowers_of_pow_eq_one (h.Q_sq hqQ)
  have hqK : zpowers q ≤ centralizer (K : Set G) := zpowers_le.2 (h.mem_centralizer_K hqQ)
  have hqE : zpowers q ≤ centralizer (E₁ : Set G) := hqK.trans (Subgroup.centralizer_le hE₁K)
  set D := E₁ ⊔ zpowers q with hD
  have hDel : IsElementaryAbelian 2 D := IsElementaryAbelian.sup_of_le_centralizer hqE
  have hDC : D ≤ centralizer ({q} : Set G) :=
    sup_le (hE₁K.trans hKq.1) (zpowers_le.2 (mem_centralizer_singleton_iff.2 rfl))
  have hinf : E₁ ⊓ zpowers q = ⊥ := by
    rw [eq_bot_iff]
    rintro y ⟨hyE, hyq⟩
    rw [Subgroup.mem_bot]
    exact h.eq_one_of_central hn (hE₁K hyE) fun k hk => mem_centralizer_iff.1 (hqK hyq) k hk
  have hcard := card_mul_card_le_inf_mul_of_comm E₁ (zpowers q) D le_sup_left le_sup_right
    (fun v hv w hw => setLike_mul_comm hv hw)
  rw [hinf, Subgroup.card_bot, one_mul, hE₁4, Nat.card_zpowers, h.orderOf_eq_two hqQ hq1] at hcard
  have : IsElementaryAbelian 2 (D.subgroupOf (centralizer ({q} : Set G))) :=
    isElementaryAbelian_subgroupOf hDC
  refine le_pRank_of_card_le (D.subgroupOf (centralizer ({q} : Set G))) ?_
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDC).toEquiv]
  omega

private theorem isSylowOf_centralizer (h : IsAConfig n x K T Q S a) (hn : 5 ≤ n)
    {q : G} (hqQ : q ∈ Q) (hq1 : q ≠ 1)
    (hN : centralizer ({q} : Set G) ≤ normalizer (K : Set G)) :
    IsSylowOf 2 Q (centralizer ({q} : Set G) ⊓ centralizerSection K ⊥) := by
  have hqCxK : q ∈ CxK x K := h.Q_le_CxK hqQ
  unfold CxK at hqCxK
  have hpump : PumpUpLT 2 x K q K := by
    obtain ⟨hILo, -, -⟩ := h.twoTerminal
    refine ⟨hILo, h.isILo_q hn hqQ hq1 hN, h.T_le_C (h.Q_le_T hqQ),
      (Subgroup.mem_inf.1 hqCxK).2, ?_⟩
    rw [h.pumpUp_K hn hqQ hq1 hN]
    exact h.isPCompIn_self hn
  obtain ⟨-, -, hii⟩ := h.twoTerminal
  have := hii Q h.sylowQ q K hpump hqQ (fun r hr => h.Q_comm hqQ hr)
  rwa [h.pPrimeCoreOf_K] at this

theorem factorization_centralizer_le_of_normal (h : IsAConfig n x K T Q S a) (hn : 5 ≤ n)
    (hnt : ∃ t ∈ T, ∃ q ∈ Q, t * q ≠ q * t)
    {q : G} (hqQ : q ∈ Q) (hq1 : q ≠ 1)
    (hN : centralizer ({q} : Set G) ≤ normalizer (K : Set G)) :
    (Nat.card ↥(centralizer ({q} : Set G))).factorization 2 ≤
      (Nat.card ↥(centralizer ({x} : Set G))).factorization 2 := by
  by_cases hqx : q = x
  · rw [hqx]
  set C₁ := centralizer ({q} : Set G) with hC₁
  set Cx := centralizer ({x} : Set G) with hCx
  have hA := h.isSylowOf_centralizer hn hqQ hq1 hN
  have hQC1 : Q ≤ C₁ := hA.le.trans inf_le_left
  obtain ⟨P, hP⟩ := (hA.isPGroup.comap_subtype (K := C₁)).exists_le_sylow
  set R := (P : Subgroup C₁).map C₁.subtype with hR
  have hRsyl : IsSylowOf 2 R C₁ := ⟨P, rfl⟩
  have hQR : Q ≤ R := fun y hy =>
    ⟨⟨y, hQC1 hy⟩, hP (show (⟨y, hQC1 hy⟩ : C₁) ∈ Q.comap C₁.subtype from hy), rfl⟩
  have hRA : R ⊓ (C₁ ⊓ centralizerSection K ⊥) = Q :=
    hA.eq_of_le (le_inf hQR hA.le) inf_le_right (hRsyl.isPGroup.to_le inf_le_left)
  have hxQ := h.x_mem_Q
  have hconj : ∀ r ∈ R, r * x * r⁻¹ ∈ Q := by
    intro r hr
    have hrC : r ∈ C₁ := hRsyl.le hr
    rw [← hRA]
    refine Subgroup.mem_inf.2 ⟨mul_mem (mul_mem hr (hQR hxQ)) (inv_mem hr),
      Subgroup.mem_inf.2 ⟨mul_mem (mul_mem hrC (hQC1 hxQ)) (inv_mem hrC), ?_⟩⟩
    rw [mem_centralizerSection_bot_iff]
    intro k hk
    have hk' : r⁻¹ * k * r ∈ K := by
      have := (Subgroup.mem_normalizer_iff.1 (hN (inv_mem hrC)) k).1 hk
      simpa using this
    have hxk := ((h.mem_Q_iff x).1 hxQ).2 _ hk'
    calc k * (r * x * r⁻¹) = r * ((r⁻¹ * k * r) * x) * r⁻¹ := by group
      _ = r * (x * (r⁻¹ * k * r)) * r⁻¹ := by rw [hxk]
      _ = r * x * r⁻¹ * k := by group
  have hx1 : x ≠ 1 := h.x_ne_one
  have hxx : x * x = 1 := by rw [← sq]; exact h.x_sq
  have hQ4 := h.card_Q
  have hfour : ∀ {u : G}, u ∈ Q → u ≠ 1 → u ≠ x → ∀ y ∈ Q, y = 1 ∨ y = x ∨ y = u ∨ y = x * u := by
    intro u huQ hu1 hux y hy
    refine eq_of_card_eq_four hQ4 (one_mem _) hxQ huQ (mul_mem hxQ huQ) hx1.symm (Ne.symm hu1)
      ?_ (Ne.symm hux) ?_ ?_ hy
    · intro hxu
      apply hux
      have : u = x⁻¹ := eq_inv_of_mul_eq_one_right hxu.symm
      rw [this, inv_eq_of_mul_eq_one_right hxx]
    · intro hxu
      exact hu1 (mul_eq_left.1 hxu.symm)
    · intro hxu
      exact hx1 (mul_eq_right.1 hxu.symm)
  set R₀ := R ⊓ Cx with hR₀
  have hmemR₀ : ∀ r ∈ R, r ∉ R₀ → r * x * r⁻¹ = x * q := by
    intro r hr hr₀
    have hrC : r ∈ C₁ := hRsyl.le hr
    have hrq : r * q = q * r := mem_centralizer_singleton_iff.1 hrC
    rcases hfour hqQ hq1 hqx (r * x * r⁻¹) (hconj r hr) with h1 | h1 | h1 | h1
    · exfalso
      apply hx1
      have : r * x * r⁻¹ = r * 1 * r⁻¹ := by rw [h1]; group
      simpa using this
    · exfalso
      apply hr₀
      refine Subgroup.mem_inf.2 ⟨hr, mem_centralizer_singleton_iff.2 ?_⟩
      calc r * x = r * x * r⁻¹ * r := by group
        _ = x * r := by rw [h1]
    · exfalso
      apply hqx
      calc q = r⁻¹ * (r * x * r⁻¹) * r := by rw [h1, mul_assoc, ← hrq]; group
        _ = x := by group
    · exact h1
  have hR : Nat.card R ≤ 2 * Nat.card R₀ := by
    refine card_le_two_mul_card fun r hr s hs hr₀ hs₀ => Subgroup.mem_inf.2
      ⟨mul_mem (inv_mem hr) hs, mem_centralizer_singleton_iff.2 ?_⟩
    have h1 := hmemR₀ r hr hr₀
    have h2 := hmemR₀ s hs hs₀
    calc r⁻¹ * s * x = r⁻¹ * (s * x * s⁻¹) * s := by group
      _ = r⁻¹ * (r * x * r⁻¹) * s := by rw [h1, h2]
      _ = x * (r⁻¹ * s) := by group
  have hR₀Cx : R₀ ≤ Cx := inf_le_right
  obtain ⟨c, hc, hcT⟩ := exists_conj_mem_of_isSylowOf h.sylowT hR₀Cx
    (hRsyl.isPGroup.to_le inf_le_left)
  set q' := c⁻¹ * q * c with hq'
  have hq'Q : q' ∈ Q := by
    simpa using h.Q_normal c⁻¹ (inv_mem hc) q hqQ
  have hcx : c * x = x * c := mem_centralizer_singleton_iff.1 hc
  have hq'1 : q' ≠ 1 := by
    intro h1
    apply hq1
    calc q = c * q' * c⁻¹ := by rw [hq']; group
      _ = 1 := by rw [h1]; group
  have hq'x : q' ≠ x := by
    intro h1
    apply hqx
    calc q = c * q' * c⁻¹ := by rw [hq']; group
      _ = c * x * c⁻¹ := by rw [h1]
      _ = x := by rw [hcx]; group
  have hR₀T : Nat.card R₀ ≤ Nat.card ↥(T ⊓ centralizer ({q'} : Set G)) := by
    have hle : R₀.map (MulAut.conj c⁻¹).toMonoidHom ≤ T ⊓ centralizer ({q'} : Set G) := by
      rintro _ ⟨y, hy, rfl⟩
      have hyq : y * q = q * y :=
        mem_centralizer_singleton_iff.1 (hRsyl.le (Subgroup.mem_inf.1 hy).1)
      refine Subgroup.mem_inf.2 ⟨by simpa [MulAut.conj_apply] using hcT y hy,
        mem_centralizer_singleton_iff.2 ?_⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv, hq']
      calc c⁻¹ * y * c * (c⁻¹ * q * c) = c⁻¹ * (y * q) * c := by group
        _ = c⁻¹ * (q * y) * c := by rw [hyq]
        _ = c⁻¹ * q * c * (c⁻¹ * y * c) := by group
    have := Subgroup.card_le_of_le hle
    rwa [Subgroup.card_map_of_injective (MulAut.conj c⁻¹).injective] at this
  have hTq' : 2 * Nat.card ↥(T ⊓ centralizer ({q'} : Set G)) ≤ Nat.card T := by
    obtain ⟨t, htT, q₀, hq₀Q, htq₀⟩ := hnt
    refine two_mul_card_le_card inf_le_left htT fun htC => ?_
    have htq' : t * q' = q' * t := mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 htC).2
    have htx : t * x = x * t := mem_centralizer_singleton_iff.1 (h.T_le_C htT)
    apply htq₀
    rcases hfour hq'Q hq'1 hq'x q₀ hq₀Q with rfl | rfl | rfl | rfl
    · group
    · exact htx
    · exact htq'
    · calc t * (x * q') = x * (t * q') := by rw [← mul_assoc, htx, mul_assoc]
        _ = x * q' * t := by rw [htq', mul_assoc x q' t]
  have hRT : Nat.card R ≤ Nat.card T := by omega
  rw [hRsyl.card_eq, h.sylowT.card_eq] at hRT
  exact (Nat.pow_le_pow_iff_right (by norm_num)).1 hRT


end IsAConfig

theorem IsAConfig.factorization_centralizer_le (h : IsAConfig n x K T Q S a) (hn : 5 ≤ n)
    (hG4 : pRank 2 G ≤ 4) (hnt : ∃ t ∈ T, ∃ q ∈ Q, t * q ≠ q * t) :
    ∀ q ∈ Q, q ≠ 1 → (Nat.card ↥(centralizer ({q} : Set G))).factorization 2 ≤
      (Nat.card ↥(centralizer ({x} : Set G))).factorization 2 := by
  intro q hqQ hq1
  exact h.factorization_centralizer_le_of_normal hn hnt hqQ hq1
    (h.C_le_normalizer hn hG4 hqQ hq1)

end CFSG.GH74.GLS
