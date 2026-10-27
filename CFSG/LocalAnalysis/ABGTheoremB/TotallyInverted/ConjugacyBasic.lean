module

public import CFSG.LocalAnalysis.ABGTheoremB.TotallyInverted.Statements
public import CFSG.CharacterTheory.Wreathed.InvertedOddCyclingLiftSupport
public import CFSG.GroupTheory.ABGLocalTools.OddInvolution
public import CFSG.LocalAnalysis.ABGTheoremB.SettingAPI

public section

namespace CFSG.ABGTheoremB.TotallyInverted.Conjugacy

open CFSG.ABGLocalTools CFSG.QuasiDihedralFusion
open scoped Pointwise

variable {G : Type} [Group G]

theorem mem_conjSub_iff {g y : G} {X : Subgroup G} : y ∈ conjSub g X ↔ g⁻¹ * y * g ∈ X := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    have : g⁻¹ * (g * x * g⁻¹) * g = x := by group
    simpa [conjSub, MulAut.conj_apply] using this.symm ▸ hx
  · intro h
    exact ⟨g⁻¹ * y * g, h, by simp [MulAut.conj_apply]; group⟩

theorem conj_mem_conjSub {g x : G} {X : Subgroup G} (hx : x ∈ X) : g * x * g⁻¹ ∈ conjSub g X :=
  mem_conjSub_iff.mpr (by simpa [mul_assoc] using hx)

theorem conjSub_one (X : Subgroup G) : conjSub 1 X = X := by
  ext y
  simp [mem_conjSub_iff]

theorem conjSub_conjSub (g h : G) (X : Subgroup G) :
    conjSub g (conjSub h X) = conjSub (g * h) X := by
  ext y
  simp only [mem_conjSub_iff]
  rw [show h⁻¹ * (g⁻¹ * y * g) * h = (g * h)⁻¹ * y * (g * h) by group]

theorem conjSub_inv_conjSub (g : G) (X : Subgroup G) : conjSub g⁻¹ (conjSub g X) = X := by
  rw [conjSub_conjSub, inv_mul_cancel, conjSub_one]

theorem conjSub_conjSub_inv (g : G) (X : Subgroup G) : conjSub g (conjSub g⁻¹ X) = X := by
  rw [conjSub_conjSub, mul_inv_cancel, conjSub_one]

theorem conjSub_mono {g : G} {X Y : Subgroup G} (h : X ≤ Y) : conjSub g X ≤ conjSub g Y :=
  Subgroup.map_mono h

theorem conjSub_le_conjSub_iff {g : G} {X Y : Subgroup G} : conjSub g X ≤ conjSub g Y ↔ X ≤ Y :=
  ⟨fun h => by simpa [conjSub_inv_conjSub] using conjSub_mono (g := g⁻¹) h, conjSub_mono⟩

theorem conjSub_injective (g : G) : Function.Injective (conjSub g) := fun X Y h => by
  rw [← conjSub_inv_conjSub g X, h, conjSub_inv_conjSub]

theorem conjSub_inf (g : G) (X Y : Subgroup G) :
    conjSub g (X ⊓ Y) = conjSub g X ⊓ conjSub g Y :=
  Subgroup.map_inf_eq X Y _ (MulAut.conj g).injective

theorem conjSub_sup (g : G) (X Y : Subgroup G) :
    conjSub g (X ⊔ Y) = conjSub g X ⊔ conjSub g Y :=
  Subgroup.map_sup X Y _

theorem conjSub_bot (g : G) : conjSub g (⊥ : Subgroup G) = ⊥ :=
  Subgroup.map_bot _

theorem conjSub_top (g : G) : conjSub g (⊤ : Subgroup G) = ⊤ := by
  ext y
  simp [mem_conjSub_iff]

theorem conjSub_eq_bot_iff {g : G} {X : Subgroup G} : conjSub g X = ⊥ ↔ X = ⊥ := by
  constructor
  · intro h
    exact conjSub_injective g (h.trans (conjSub_bot g).symm)
  · rintro rfl
    exact conjSub_bot g

theorem card_conjSub (g : G) (X : Subgroup G) : Nat.card (conjSub g X) = Nat.card X :=
  Subgroup.card_map_of_injective (MulAut.conj g).injective

theorem isPGroup_conjSub {p : ℕ} {X : Subgroup G} (hX : IsPGroup p X) (g : G) :
    IsPGroup p (conjSub g X) :=
  hX.map _

theorem conjSub_eq_self_iff {g : G} {X : Subgroup G} :
    conjSub g X = X ↔ g ∈ Subgroup.normalizer (X : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  constructor
  · intro h y
    constructor
    · intro hy
      rw [← h]
      exact conj_mem_conjSub hy
    · intro hy
      rw [← h, mem_conjSub_iff] at hy
      simpa [mul_assoc] using hy
  · intro h
    ext y
    rw [mem_conjSub_iff, h (g⁻¹ * y * g)]
    simp [mul_assoc]

theorem conjSub_eq_self_of_mem {g : G} {X : Subgroup G} (hg : g ∈ X) : conjSub g X = X :=
  conjSub_eq_self_iff.mpr (Subgroup.le_normalizer hg)

theorem conjSub_le_of_mem {g : G} {X H : Subgroup G} (hg : g ∈ H) (hX : X ≤ H) :
    conjSub g X ≤ H :=
  conjSub_eq_self_of_mem hg ▸ conjSub_mono hX

theorem normalizer_conjSub (g : G) (X : Subgroup G) :
    Subgroup.normalizer (conjSub g X : Set G) = conjSub g (Subgroup.normalizer (X : Set G)) := by
  ext y
  rw [← conjSub_eq_self_iff, mem_conjSub_iff, ← conjSub_eq_self_iff, conjSub_conjSub]
  constructor
  · intro h
    rw [show g⁻¹ * y * g = g⁻¹ * (y * g) by group, ← conjSub_conjSub, h, conjSub_inv_conjSub]
  · intro h
    rw [show y * g = g * (g⁻¹ * y * g) by group, ← conjSub_conjSub, h]

theorem mem_normalizer_sup {g : G} {A B : Subgroup G} (hA : g ∈ Subgroup.normalizer (A : Set G))
    (hB : g ∈ Subgroup.normalizer (B : Set G)) :
    g ∈ Subgroup.normalizer ((A ⊔ B : Subgroup G) : Set G) := by
  rw [← conjSub_eq_self_iff, conjSub_sup, conjSub_eq_self_iff.mpr hA, conjSub_eq_self_iff.mpr hB]

theorem le_normalizer_conjSub {g : G} {C X : Subgroup G}
    (hg : g ∈ Subgroup.normalizer (C : Set G)) (hC : C ≤ Subgroup.normalizer (X : Set G)) :
    C ≤ Subgroup.normalizer (conjSub g X : Set G) := by
  rw [normalizer_conjSub, ← conjSub_eq_self_iff.mpr hg]
  exact conjSub_mono hC

theorem conjSub_centralizer_singleton (g t : G) :
    conjSub g (Subgroup.centralizer ({t} : Set G)) =
      Subgroup.centralizer ({g * t * g⁻¹} : Set G) := by
  ext y
  rw [mem_conjSub_iff, Subgroup.mem_centralizer_singleton_iff,
    Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    calc y * (g * t * g⁻¹) = g * (g⁻¹ * y * g * t) * g⁻¹ := by group
      _ = g * (t * (g⁻¹ * y * g)) * g⁻¹ := by rw [h]
      _ = g * t * g⁻¹ * y := by group
  · intro h
    calc g⁻¹ * y * g * t = g⁻¹ * (y * (g * t * g⁻¹)) * g := by group
      _ = g⁻¹ * (g * t * g⁻¹ * y) * g := by rw [h]
      _ = t * (g⁻¹ * y * g) := by group

theorem conjSub_pCoreIn (p : ℕ) (g : G) (H : Subgroup G) :
    conjSub g (pCoreIn p H) = pCoreIn p (conjSub g H) := by
  set f : G →* G := (MulAut.conj g).toMonoidHom
  have hf : Function.Injective f := (MulAut.conj g).injective
  set e : H ≃* conjSub g H := H.equivMapOfInjective f hf
  have hcomm : (conjSub g H).subtype.comp e.toMonoidHom = f.comp H.subtype := by
    ext h
    rfl
  rw [pCoreIn, pCoreIn, ← CFSG.pCore_map_iso p e, Subgroup.map_map, hcomm, conjSub,
    Subgroup.map_map]

theorem mem_normalizer_of_conj_mem [Finite G] {g : G} {X : Subgroup G}
    (h : ∀ x ∈ X, g * x * g⁻¹ ∈ X) : g ∈ Subgroup.normalizer (X : Set G) := by
  rw [← conjSub_eq_self_iff]
  refine Subgroup.eq_of_le_of_card_ge ?_ (by rw [card_conjSub])
  rintro _ ⟨x, hx, rfl⟩
  exact h x hx

theorem isSylowOf_conjSub [Finite G] {p : ℕ} [Fact p.Prime] {P K : Subgroup G}
    (h : IsSylowOf p P K) (g : G) : IsSylowOf p (conjSub g P) (conjSub g K) :=
  isSylowOf_of_card (conjSub_mono h.le) (by rw [card_conjSub, card_conjSub, h.card_eq])

theorem exists_conjSub_eq_of_isSylowOf [Finite G] {p : ℕ} [Fact p.Prime] {P Q K : Subgroup G}
    (hP : IsSylowOf p P K) (hQ : IsSylowOf p Q K) : ∃ k ∈ K, conjSub k P = Q := by
  obtain ⟨S₁, rfl⟩ := hP
  obtain ⟨S₂, rfl⟩ := hQ
  obtain ⟨k, rfl⟩ := MulAction.exists_smul_eq K S₁ S₂
  refine ⟨k, k.2, ?_⟩
  ext y
  rw [mem_conjSub_iff]
  simp only [Subgroup.mem_map, Sylow.coe_subgroup_smul,
    Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
  constructor
  · rintro ⟨u, hu, hu'⟩
    refine ⟨k * u * k⁻¹, ?_, ?_⟩
    · simpa [MulAut.smul_def, mul_assoc] using hu
    · simp only [Subgroup.subtype_apply, Subgroup.coe_mul, Subgroup.coe_inv] at hu' ⊢
      rw [hu']
      group
  · rintro ⟨u, hu, rfl⟩
    refine ⟨_, hu, ?_⟩
    simp [MulAut.smul_def]

theorem subset_normalizer_mul [Finite G] {p : ℕ} [Fact p.Prime] {R O H : Subgroup G}
    (hR : IsSylowOf p R O) (hHO : H ≤ Subgroup.normalizer (O : Set G)) :
    (H : Set G) ⊆ (Subgroup.normalizer (R : Set G) : Set G) * (O : Set G) := by
  intro h hh
  have hO : conjSub h O = O := conjSub_eq_self_iff.mpr (hHO hh)
  have hR' : IsSylowOf p (conjSub h R) O := hO ▸ isSylowOf_conjSub hR h
  obtain ⟨o, ho, hoR⟩ := exists_conjSub_eq_of_isSylowOf hR' hR
  have hn : o * h ∈ Subgroup.normalizer (R : Set G) := by
    rw [← conjSub_eq_self_iff, ← conjSub_conjSub, hoR]
  have ho' : h⁻¹ * o⁻¹ * h ∈ O := by
    have := (Subgroup.mem_normalizer_iff.mp (hHO (Subgroup.inv_mem _ hh)) o⁻¹).mp (O.inv_mem ho)
    simpa using this
  exact ⟨o * h, hn, h⁻¹ * o⁻¹ * h, ho', by group⟩

theorem exists_le_mem_maximals [Finite G] {𝓢 : Set (Subgroup G)} {X : Subgroup G}
    (hX : X ∈ 𝓢) : ∃ Y ∈ maximals 𝓢, X ≤ Y := by
  obtain ⟨Y, hXY, hY⟩ := (Set.toFinite 𝓢).exists_le_maximal hX
  exact ⟨Y, ⟨hY.1, fun R hR hYR => le_antisymm (hY.2 hR hYR) hYR⟩, hXY⟩

theorem mem_maximals_of_subset {𝓢 𝓣 : Set (Subgroup G)} (h : 𝓢 ⊆ 𝓣) {X : Subgroup G}
    (hX : X ∈ maximals 𝓣) (hX𝓢 : X ∈ 𝓢) : X ∈ maximals 𝓢 :=
  ⟨hX𝓢, fun R hR hXR => hX.2 R (h hR) hXR⟩

theorem lt_inf_normalizer [Finite G] {p : ℕ} [Fact p.Prime] {Y V : Subgroup G}
    (hV : IsPGroup p V) (hYV : Y < V) : Y < V ⊓ Subgroup.normalizer (Y : Set G) := by
  have hnil : Group.IsNilpotent V := hV.isNilpotent
  have hlt : Y.subgroupOf V < ⊤ := by
    rw [lt_top_iff_ne_top]
    intro htop
    apply hYV.ne
    apply le_antisymm hYV.le
    intro x hx
    have : (⟨x, hx⟩ : V) ∈ Y.subgroupOf V := htop ▸ Subgroup.mem_top _
    exact this
  have hnorm := Group.normalizerCondition_of_isNilpotent (G := V) _ hlt
  rw [← Subgroup.subgroupOf_normalizer_eq hYV.le] at hnorm
  obtain ⟨⟨n, hnV⟩, hnN, hnY⟩ := IsConcreteLE.exists_of_lt hnorm
  refine lt_of_le_of_ne (le_inf hYV.le Subgroup.le_normalizer) fun h => hnY ?_
  have : n ∈ V ⊓ Subgroup.normalizer (Y : Set G) := ⟨hnV, hnN⟩
  rw [← h] at this
  exact this

theorem odd_card_of_isPGroup [Finite G] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {X : Subgroup G}
    (hX : IsPGroup p X) : Odd (Nat.card X) := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hX
  rw [hn]
  exact (hp.odd_of_ne_two hp2).pow

theorem odd_orderOf_of_mem {X : Subgroup G} (hX : Odd (Nat.card X)) {u : G} (hu : u ∈ X) :
    Odd (orderOf u) :=
  hX.of_dvd_nat (Subgroup.orderOf_dvd_natCard X hu)

theorem mem_of_sq_mem {u : G} {X : Subgroup G} (hu : Odd (orderOf u)) (h : u ^ 2 ∈ X) :
    u ∈ X := by
  obtain ⟨m, hm⟩ := hu
  have : (u ^ 2) ^ (m + 1) = u := by
    rw [← pow_mul, show 2 * (m + 1) = orderOf u + 1 by omega, pow_succ, pow_orderOf_eq_one,
      one_mul]
  rw [← this]
  exact X.pow_mem h _

theorem eq_one_of_conj_eq_inv_of_commute {t u : G} (hu : Odd (orderOf u))
    (hinv : t * u * t⁻¹ = u⁻¹) (hcomm : t * u = u * t) : u = 1 := by
  have h1 : u = u⁻¹ := by rw [← hinv, hcomm, mul_assoc, mul_inv_cancel, mul_one]
  have h2 : u ^ 2 = 1 := by
    rw [pow_two]
    nth_rewrite 2 [h1]
    exact mul_inv_cancel u
  have := mem_of_sq_mem (X := ⊥) hu (by rw [h2]; exact Subgroup.one_mem _)
  exact Subgroup.mem_bot.mp this

theorem mul_comm_of_le_normalizer {C X : Subgroup G}
    (h : C ≤ Subgroup.normalizer (X : Set G)) : (X : Set G) * C = C * X := by
  rw [← Subgroup.coe_mul_of_right_le_normalizer_left X C h,
    ← Subgroup.coe_mul_of_left_le_normalizer_right C X h, sup_comm]

theorem mul_comm_inf_of_le {C U H : Subgroup G} (hC : C ≤ H)
    (hU : (U : Set G) * C = C * U) :
    ((U ⊓ H : Subgroup G) : Set G) * C = C * ((U ⊓ H : Subgroup G) : Set G) := by
  have h1 : ((U ⊓ H : Subgroup G) : Set G) * C = ((U : Set G) * C) ∩ H := by
    ext g
    constructor
    · rintro ⟨u, hu, c, hc, rfl⟩
      exact ⟨⟨u, hu.1, c, hc, rfl⟩, H.mul_mem hu.2 (hC hc)⟩
    · rintro ⟨⟨u, hu, c, hc, rfl⟩, hg⟩
      refine ⟨u, ⟨hu, ?_⟩, c, hc, rfl⟩
      have := H.mul_mem hg (H.inv_mem (hC hc))
      simpa using this
  have h2 : (C : Set G) * ((U ⊓ H : Subgroup G) : Set G) = ((C : Set G) * U) ∩ H := by
    ext g
    constructor
    · rintro ⟨c, hc, u, hu, rfl⟩
      exact ⟨⟨c, hc, u, hu.1, rfl⟩, H.mul_mem (hC hc) hu.2⟩
    · rintro ⟨⟨c, hc, u, hu, rfl⟩, hg⟩
      refine ⟨c, hc, u, ⟨hu, ?_⟩, rfl⟩
      have := H.mul_mem (H.inv_mem (hC hc)) hg
      simpa using this
  rw [h1, h2, hU]

theorem mul_comm_sup_of_le {P X C : Subgroup G} (hPC : P ≤ C)
    (hCX : C ≤ Subgroup.normalizer (X : Set G)) :
    ((P ⊔ X : Subgroup G) : Set G) * C = C * ((P ⊔ X : Subgroup G) : Set G) := by
  rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ (hPC.trans hCX), mul_assoc,
    mul_comm_of_le_normalizer hCX, ← mul_assoc, coe_mul_coe_of_le' hPC, ← mul_assoc,
    coe_mul_coe_of_le hPC]

theorem isPGroup_pCoreIn (p : ℕ) (H : Subgroup G) : IsPGroup p (pCoreIn p H) :=
  CFSG.pCore_isPGroup.map H.subtype

theorem le_normalizer_pCoreIn (p : ℕ) (H : Subgroup G) :
    H ≤ Subgroup.normalizer (pCoreIn p H : Set G) :=
  CFSG.ABGTheoremB.le_normalizer_map_subtype H (CFSG.pCore p H)

theorem le_pCoreIn {p : ℕ} {X H : Subgroup G} (hXH : X ≤ H)
    (hnorm : H ≤ Subgroup.normalizer (X : Set G)) (hX : IsPGroup p X) : X ≤ pCoreIn p H := by
  have hnormal : (X.subgroupOf H).Normal := by
    constructor
    intro a ha h
    exact (Subgroup.mem_normalizer_iff.mp (hnorm h.property) a).mp ha
  have hle : X.subgroupOf H ≤ CFSG.pCore p H := le_sSup ⟨hnormal, hX.comap_subtype⟩
  intro k hk
  exact ⟨⟨k, hXH hk⟩, hle hk, rfl⟩

theorem three_dvd_relIndex {G' : Type*} [Group G'] [Finite G'] {C N : Subgroup G'}
    [(C.subgroupOf N).Normal] {g : G'} (hgN : g ∈ N) (hgC : g ∉ C) {k : ℕ}
    (hg : g ^ 3 ^ k = 1) : 3 ∣ C.relIndex N := by
  set x : N ⧸ C.subgroupOf N := ((⟨g, hgN⟩ : N) : N ⧸ C.subgroupOf N)
  have hx1 : x ≠ 1 := by
    rw [Ne, QuotientGroup.eq_one_iff]
    exact hgC
  have hx : x ^ 3 ^ k = 1 := by
    rw [← QuotientGroup.mk_pow]
    have : (⟨g, hgN⟩ : N) ^ 3 ^ k = 1 := Subtype.ext (by simpa using hg)
    rw [this, QuotientGroup.mk_one]
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp (orderOf_dvd_of_pow_eq_one hx)
  have hj0 : j ≠ 0 := by
    rintro rfl
    exact hx1 (orderOf_eq_one_iff.mp (by simpa using hj))
  have hdvd : orderOf x ∣ C.relIndex N := by
    rw [Subgroup.relIndex, Subgroup.index_eq_card]
    exact orderOf_dvd_natCard x
  rw [hj] at hdvd
  exact (dvd_pow_self 3 hj0).trans hdvd

section Setting

variable [Finite G] {σ : Setting G}

theorem x_ne_one (hσ : σ.IsValid) : σ.x ≠ 1 := fun h => by
  have := hσ.x_order
  rw [h, orderOf_one] at this
  omega

theorem x₂_ne_one (hσ : σ.IsValid) : σ.x₂ ≠ 1 := fun h => by
  have := hσ.x₂_order
  rw [h, orderOf_one] at this
  omega

theorem x_mul_x (hσ : σ.IsValid) : σ.x * σ.x = 1 := by
  rw [← pow_two, ← hσ.x_order, pow_orderOf_eq_one]

theorem x₂_mul_x₂ (hσ : σ.IsValid) : σ.x₂ * σ.x₂ = 1 := by
  rw [← pow_two, ← hσ.x₂_order, pow_orderOf_eq_one]

omit [Finite G] in
private theorem eq_one_or_eq_of_mem_zpowers {x g : G} (hx : orderOf x = 2)
    (hg : g ∈ Subgroup.zpowers x) : g = 1 ∨ g = x := by
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
  rw [← zpow_mod_orderOf, hx]
  rcases Int.emod_two_eq_zero_or_one i with h | h <;> rw [show ((2 : ℕ) : ℤ) = 2 from rfl, h]
  · exact Or.inl (zpow_zero x)
  · exact Or.inr (zpow_one x)

theorem isKleinFour_T (hσ : σ.IsValid) : IsKleinFour σ.T := by
  refine CFSG.Wreathed.isKleinFour_closure_pair hσ.x_order hσ.x₂_order hσ.commute ?_
  rw [Subgroup.disjoint_def]
  intro g h1 h2
  rcases eq_one_or_eq_of_mem_zpowers hσ.x_order h1 with h | rfl
  · exact h
  rcases eq_one_or_eq_of_mem_zpowers hσ.x₂_order h2 with h | h
  · exact h
  · exact absurd h hσ.x_ne_x₂

omit [Finite G] in
theorem xs_mem_T (i : Fin 3) : σ.xs i ∈ σ.T := by
  fin_cases i
  · exact σ.x_mem_T
  · exact σ.x₂_mem_T
  · exact σ.T.mul_mem σ.x_mem_T σ.x₂_mem_T

theorem xs_ne_one (hσ : σ.IsValid) (i : Fin 3) : σ.xs i ≠ 1 := by
  fin_cases i
  · exact x_ne_one hσ
  · exact x₂_ne_one hσ
  · intro h
    apply hσ.x_ne_x₂
    have h' : σ.x * σ.x₂ = 1 := h
    calc σ.x = σ.x * (σ.x₂ * σ.x₂) := by rw [x₂_mul_x₂ hσ, mul_one]
      _ = σ.x₂ := by rw [← mul_assoc, h', one_mul]

theorem xs_injective (hσ : σ.IsValid) : Function.Injective σ.xs := by
  intro i j h
  have h12 := hσ.x_ne_x₂
  have h1 := x_ne_one hσ
  have h2 := x₂_ne_one hσ
  fin_cases i <;> fin_cases j <;> simp only [Setting.xs, Setting.x₃] at h <;>
    first
    | rfl
    | exact absurd h h12
    | exact absurd h.symm h12
    | exact absurd (by simpa using h) h2
    | exact absurd (by simpa using h.symm) h2
    | exact absurd (by simpa using congrArg (· * σ.x₂⁻¹) h) h1
    | exact absurd (by simpa using (congrArg (· * σ.x₂⁻¹) h).symm) h1

omit [Finite G] in
theorem C_le_Ns (i : Fin 3) : σ.C ≤ σ.Ns i :=
  Subgroup.centralizer_le (Set.singleton_subset_iff.mpr (xs_mem_T i))

omit [Finite G] in
theorem comm_of_mem_C {c t : G} (hc : c ∈ σ.C) (ht : t ∈ σ.T) : t * c = c * t :=
  Subgroup.mem_centralizer_iff.mp hc t ht

omit [Finite G] in
private theorem comm_iff_conj {a u : G} : a * u = u * a ↔ a * u * a⁻¹ = u := by
  rw [mul_inv_eq_iff_eq_mul]

omit [Finite G] in
theorem comp_zero_eq (U : Subgroup G) : comp σ U 0 = fourInverted U σ.x σ.x₂ := by
  ext u
  simp only [comp, fourInverted, Set.mem_ofPred_eq]
  rw [comm_iff_conj]
  rfl

omit [Finite G] in
theorem comp_one_eq (U : Subgroup G) : comp σ U 1 = fourInverted U σ.x₂ σ.x := by
  ext u
  simp only [comp, fourInverted, Set.mem_ofPred_eq, show (1 : Fin 3) + 1 = 2 from rfl]
  rw [comm_iff_conj]
  have key : σ.x₂ * u * σ.x₂⁻¹ = u →
      (σ.xs 2 * u * (σ.xs 2)⁻¹ = σ.x * u * σ.x⁻¹) := by
    intro h
    change σ.x * σ.x₂ * u * (σ.x * σ.x₂)⁻¹ = σ.x * u * σ.x⁻¹
    calc σ.x * σ.x₂ * u * (σ.x * σ.x₂)⁻¹ = σ.x * (σ.x₂ * u * σ.x₂⁻¹) * σ.x⁻¹ := by group
      _ = σ.x * u * σ.x⁻¹ := by rw [h]
  constructor
  · rintro ⟨hu, h1, h2⟩
    exact ⟨hu, h1, by rw [← key h1]; exact h2⟩
  · rintro ⟨hu, h1, h2⟩
    exact ⟨hu, h1, by rw [key h1]; exact h2⟩

omit [Finite G] in
theorem comp_two_eq (U : Subgroup G) : comp σ U 2 = fourInverted U (σ.x * σ.x₂) σ.x := by
  ext u
  simp only [comp, fourInverted, Set.mem_ofPred_eq]
  rw [comm_iff_conj]
  rfl

theorem coe_eq_mul_comp (hσ : σ.IsValid) {U : Subgroup G} (hU : Odd (Nat.card U))
    (hTU : σ.T ≤ Subgroup.normalizer (U : Set G)) :
    (U : Set G) =
      ((U ⊓ σ.C : Subgroup G) : Set G) * comp σ U 0 * comp σ U 1 * comp σ U 2 := by
  have := isKleinFour_T hσ
  rw [comp_zero_eq, comp_one_eq, comp_two_eq]
  exact (four_group_T_decomposition hU hTU σ.x_mem_T σ.x₂_mem_T (x_ne_one hσ) (x₂_ne_one hσ)
    hσ.x_ne_x₂).2

omit [Finite G] in
theorem comp_mono {U V : Subgroup G} (h : U ≤ V) (i : Fin 3) : comp σ U i ⊆ comp σ V i :=
  fun _ hu => ⟨h hu.1, hu.2⟩

omit [Finite G] in
theorem conj_x_of_mem_comp_one {U : Subgroup G} {u : G} (hu : u ∈ comp σ U 1) :
    σ.x * u * σ.x⁻¹ = u⁻¹ := by
  obtain ⟨-, h1, h2⟩ := hu
  have h3 : σ.x₂ * u * σ.x₂⁻¹ = u := by
    have h1' : σ.x₂ * u = u * σ.x₂ := h1
    rw [h1', mul_inv_cancel_right]
  have h2' : σ.x * σ.x₂ * u * (σ.x * σ.x₂)⁻¹ = u⁻¹ := h2
  calc σ.x * u * σ.x⁻¹ = σ.x * (σ.x₂ * u * σ.x₂⁻¹) * σ.x⁻¹ := by rw [h3]
    _ = σ.x * σ.x₂ * u * (σ.x * σ.x₂)⁻¹ := by group
    _ = u⁻¹ := h2'

omit [Finite G] in
theorem conj_x_of_mem_comp_two {U : Subgroup G} {u : G} (hu : u ∈ comp σ U 2) :
    σ.x * u * σ.x⁻¹ = u⁻¹ :=
  hu.2.2

omit [Finite G] in
theorem mul_four_subset {A₀ A₁ A₂ A₃ : Set G} {B : Subgroup G} (h₀ : A₀ ⊆ B) (h₁ : A₁ ⊆ B)
    (h₂ : A₂ ⊆ B) (h₃ : A₃ ⊆ B) : A₀ * A₁ * A₂ * A₃ ⊆ B := by
  rintro _ ⟨_, ⟨_, ⟨a, ha, b, hb, rfl⟩, c, hc, rfl⟩, d, hd, rfl⟩
  exact B.mul_mem (B.mul_mem (B.mul_mem (h₀ ha) (h₁ hb)) (h₂ hc)) (h₃ hd)

theorem le_of_comp_subset (hσ : σ.IsValid) {U B : Subgroup G} (hU : Odd (Nat.card U))
    (hTU : σ.T ≤ Subgroup.normalizer (U : Set G)) (hUC : U ⊓ σ.C = ⊥)
    (hcomp : ∀ i, comp σ U i ⊆ B) : U ≤ B := by
  intro u hu
  have hu' : u ∈ (U : Set G) := hu
  rw [coe_eq_mul_comp hσ hU hTU, hUC] at hu'
  exact mul_four_subset (by simp) (hcomp 0) (hcomp 1) (hcomp 2) hu'

theorem exists_inf_Ns_ne_bot (hσ : σ.IsValid) {U : Subgroup G} (hU : Odd (Nat.card U))
    (hTU : σ.T ≤ Subgroup.normalizer (U : Set G)) (hU1 : U ≠ ⊥) :
    ∃ j : Fin 3, U ⊓ σ.Ns j ≠ ⊥ := by
  have := isKleinFour_T hσ
  by_contra hcon
  have hcon' : ∀ j : Fin 3, U ⊓ σ.Ns j = ⊥ := fun j => by
    by_contra h
    exact hcon ⟨j, h⟩
  apply hU1
  have h := four_group_odd_eq_mul_centralizers hU hTU (xs_mem_T 0) (xs_mem_T 1) (xs_mem_T 2)
    (xs_ne_one hσ 0) (xs_ne_one hσ 1) (xs_ne_one hσ 2)
    (fun h => by simpa using xs_injective hσ h) (fun h => by simpa using xs_injective hσ h)
    (fun h => by simpa using xs_injective hσ h)
  have h0 := hcon' 0
  have h1 := hcon' 1
  have h2 := hcon' 2
  simp only [Setting.Ns] at h0 h1 h2
  rw [h0, h1, h2] at h
  rw [eq_bot_iff]
  intro u hu
  have hu' : u ∈ (U : Set G) := hu
  rw [h] at hu'
  obtain ⟨_, ⟨a, ha, b, hb, rfl⟩, c, hc, rfl⟩ := hu'
  simp only [SetLike.mem_coe, Subgroup.mem_bot] at ha hb hc
  simp [ha, hb, hc]

theorem inf_T_eq_bot (hσ : σ.IsValid) {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) {X : Subgroup G}
    (hX : IsPGroup r X) : X ⊓ σ.T = ⊥ := by
  have : Fact r.Prime := ⟨hr⟩
  apply (Subgroup.disjoint_of_coprime_natCard _).eq_bot
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hX
  rw [hn, (isKleinFour_T hσ).card_four, show (4 : ℕ) = 2 ^ 2 by norm_num]
  exact Nat.Coprime.pow n 2 (Nat.coprime_two_right.mpr (hr.odd_of_ne_two hr2))

theorem normalizer_T_le_M : Subgroup.normalizer (σ.T : Set G) ≤ σ.M := by
  intro g hg
  apply mem_normalizer_of_conj_mem
  intro c hc
  rw [Setting.C, Subgroup.mem_centralizer_iff]
  intro t ht
  have ht' : g⁻¹ * t * g ∈ σ.T := by
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hg) t).mp ht
    simpa using this
  have hct := comm_of_mem_C hc ht'
  calc t * (g * c * g⁻¹) = g * ((g⁻¹ * t * g) * c) * g⁻¹ := by group
    _ = g * (c * (g⁻¹ * t * g)) * g⁻¹ := by rw [hct]
    _ = g * c * g⁻¹ * t := by group

omit [Finite G] in
theorem C_le_M : σ.C ≤ σ.M := Subgroup.le_normalizer

theorem D_le_M : σ.D ≤ σ.M := inf_le_right.trans normalizer_T_le_M

end Setting

section Signalizers

theorem signalizers_mono {H H' X : Subgroup G} {p : ℕ} (h : H ≤ H') :
    signalizers H X p ⊆ signalizers H' X p :=
  fun _ hR => ⟨hR.1.trans h, hR.2⟩

theorem signalizersPerm_mono {H H' X Y : Subgroup G} {p : ℕ} (h : H ≤ H') :
    signalizersPerm H X Y p ⊆ signalizersPerm H' X Y p :=
  fun _ hR => ⟨signalizers_mono h hR.1, hR.2⟩

theorem mem_signalizersPerm_of_mem_signalizers {H T C R : Subgroup G} {p : ℕ} (hTC : T ≤ C)
    (hR : R ∈ signalizers H C p) : R ∈ signalizersPerm H T C p :=
  ⟨⟨hR.1, hR.2.1, hTC.trans hR.2.2.1,
      eq_bot_iff.mpr ((inf_le_inf_left R hTC).trans hR.2.2.2.le)⟩,
    mul_comm_of_le_normalizer hR.2.2.1⟩

theorem conjSub_mem_signalizers {H C R : Subgroup G} {p : ℕ} {g : G}
    (hgH : conjSub g H = H) (hgC : g ∈ Subgroup.normalizer (C : Set G))
    (hR : R ∈ signalizers H C p) : conjSub g R ∈ signalizers H C p := by
  refine ⟨hgH ▸ conjSub_mono hR.1, isPGroup_conjSub hR.2.1 g,
    le_normalizer_conjSub hgC hR.2.2.1, ?_⟩
  rw [← conjSub_eq_self_iff.mpr hgC, ← conjSub_inf, hR.2.2.2, conjSub_bot]

private theorem conjSub_inv_eq {g : G} {H : Subgroup G} (hgH : conjSub g H = H) :
    conjSub g⁻¹ H = H :=
  calc conjSub g⁻¹ H = conjSub g⁻¹ (conjSub g H) := by rw [hgH]
    _ = H := conjSub_inv_conjSub g H

theorem conjSub_mem_maximals_signalizers {H C R : Subgroup G} {p : ℕ} {g : G}
    (hgH : conjSub g H = H) (hgC : g ∈ Subgroup.normalizer (C : Set G))
    (hR : R ∈ maximals (signalizers H C p)) : conjSub g R ∈ maximals (signalizers H C p) := by
  refine ⟨conjSub_mem_signalizers hgH hgC hR.1, fun R' hR' hle => ?_⟩
  have h1 := conjSub_mem_signalizers (conjSub_inv_eq hgH) (Subgroup.inv_mem _ hgC) hR'
  have h2 : R ≤ conjSub g⁻¹ R' :=
    (conjSub_le_conjSub_iff (g := g)).mp (by rw [conjSub_conjSub_inv]; exact hle)
  rw [← hR.2 _ h1 h2, conjSub_conjSub_inv]

end Signalizers

section Data

variable [Finite G] {σ : Setting G} {r : ℕ}

theorem mem_normalizer_T_of {g : G} (h1 : g * σ.x * g⁻¹ ∈ σ.T) (h2 : g * σ.x₂ * g⁻¹ ∈ σ.T) :
    g ∈ Subgroup.normalizer (σ.T : Set G) := by
  apply mem_normalizer_of_conj_mem
  have hle : Subgroup.closure ({σ.x, σ.x₂} : Set G) ≤ σ.T.comap (MulAut.conj g).toMonoidHom := by
    rw [Subgroup.closure_le]
    intro y hy
    rcases hy with rfl | rfl
    · simpa using h1
    · simpa using h2
  intro t ht
  simpa using hle ht

theorem a_mem_normalizer_T (Δ : Data σ r) : Δ.a ∈ Subgroup.normalizer (σ.T : Set G) :=
  mem_normalizer_T_of (by rw [show σ.x = σ.xs 0 from rfl, Δ.a_cycle 0]; exact xs_mem_T _)
    (by rw [show σ.x₂ = σ.xs 1 from rfl, Δ.a_cycle 1]; exact xs_mem_T _)

theorem conjSub_a_Ns (Δ : Data σ r) (i : Fin 3) : conjSub Δ.a (σ.Ns i) = σ.Ns (i + 1) := by
  simp only [Setting.Ns]
  rw [conjSub_centralizer_singleton, Δ.a_cycle i]

theorem d_conj_x₃ (hσ : σ.IsValid) (Δ : Data σ r) : Δ.d * σ.x₃ * Δ.d⁻¹ = σ.x₂ :=
  calc Δ.d * σ.x₃ * Δ.d⁻¹ = (Δ.d * σ.x * Δ.d⁻¹) * (Δ.d * σ.x₂ * Δ.d⁻¹) := by
        rw [Setting.x₃]; group
    _ = σ.x * (σ.x * σ.x₂) := by rw [Δ.d_x, Δ.d_x₂]; rfl
    _ = σ.x₂ := by rw [← mul_assoc, x_mul_x hσ, one_mul]

theorem conjSub_d_Ps_zero (Δ : Data σ r) : conjSub Δ.d (σ.Ps r 0) = σ.Ps r 0 := by
  simp only [Setting.Ps, Setting.Ns]
  rw [conjSub_pCoreIn, conjSub_centralizer_singleton]
  exact congrArg _ (congrArg _ (congrArg _ Δ.d_x))

theorem conjSub_d_Ps_one (Δ : Data σ r) : conjSub Δ.d (σ.Ps r 1) = σ.Ps r 2 := by
  simp only [Setting.Ps, Setting.Ns]
  rw [conjSub_pCoreIn, conjSub_centralizer_singleton]
  exact congrArg _ (congrArg _ (congrArg _ Δ.d_x₂))

theorem conjSub_d_Ps_two (hσ : σ.IsValid) (Δ : Data σ r) :
    conjSub Δ.d (σ.Ps r 2) = σ.Ps r 1 := by
  simp only [Setting.Ps, Setting.Ns]
  rw [conjSub_pCoreIn, conjSub_centralizer_singleton]
  exact congrArg _ (congrArg _ (congrArg _ (d_conj_x₃ hσ Δ)))

omit [Finite G] in
theorem C_le_normalizer_Ps (i : Fin 3) : σ.C ≤ Subgroup.normalizer (σ.Ps r i : Set G) :=
  (C_le_Ns i).trans (le_normalizer_pCoreIn r _)

omit [Finite G] in
theorem conjSub_Ps_of_mem {g : G} {i : Fin 3} (hg : g ∈ σ.Ns i) :
    conjSub g (σ.Ps r i) = σ.Ps r i :=
  conjSub_eq_self_iff.mpr (le_normalizer_pCoreIn r _ hg)

omit [Finite G] in
theorem isPGroup_Ps (i : Fin 3) : IsPGroup r (σ.Ps r i) := isPGroup_pCoreIn r _

theorem odd_card_Ps (Δ : Data σ r) (i : Fin 3) : Odd (Nat.card (σ.Ps r i)) :=
  odd_card_of_isPGroup Δ.prime Δ.ne_two (isPGroup_Ps i)

private theorem succ_ne_self (i : Fin 3) : i + 1 ≠ i := by
  fin_cases i <;> decide

theorem Ps_inf_C (Δ : Data σ r) (i : Fin 3) : σ.Ps r i ⊓ σ.C = ⊥ := by
  rw [eq_bot_iff]
  rintro u ⟨hu, huC⟩
  rw [Subgroup.mem_bot]
  exact eq_one_of_conj_eq_inv_of_commute (odd_orderOf_of_mem (odd_card_Ps Δ i) hu)
    (Δ.P_inverted i (i + 1) (succ_ne_self i) u hu) (comm_of_mem_C huC (xs_mem_T _))

theorem Ps_mem_signalizers (Δ : Data σ r) (i : Fin 3) : σ.Ps r i ∈ signalizers ⊤ σ.C r :=
  ⟨le_top, isPGroup_Ps i, C_le_normalizer_Ps i, Ps_inf_C Δ i⟩

theorem Ps_ne_bot (Δ : Data σ r) : σ.Ps r 0 ≠ ⊥ := by
  have : Fact r.Prime := ⟨Δ.prime⟩
  intro h
  have hcard := Δ.P_sylow.card_eq
  rw [h, Subgroup.card_bot] at hcard
  have h0 : (Nat.card σ.ON).factorization r = 0 := by
    by_contra h0
    have : 1 < r ^ (Nat.card σ.ON).factorization r := Nat.one_lt_pow h0 Δ.prime.one_lt
    omega
  rw [Nat.factorization_eq_zero_iff] at h0
  rcases h0 with h0 | h0 | h0
  · exact h0 Δ.prime
  · exact h0 Δ.dvd
  · exact Nat.card_pos.ne' h0

theorem Ps_subset_comp (Δ : Data σ r) {U : Subgroup G} (i : Fin 3) (h : σ.Ps r i ≤ U) :
    (σ.Ps r i : Set G) ⊆ comp σ U i := fun u hu =>
  ⟨h hu, (Subgroup.mem_centralizer_singleton_iff.mp (Δ.P_centralized i hu)).symm,
    Δ.P_inverted i (i + 1) (succ_ne_self i) u hu⟩

end Data

end CFSG.ABGTheoremB.TotallyInverted.Conjugacy
