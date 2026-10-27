module

public import CFSG.GH74.Uniqueness.SU.KI1r3Normal
public import CFSG.GH74.Uniqueness.SU.KI1r3Act
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Hall.Basic

public section

namespace CFSG.GH74.Uniqueness.SU.K.R3

open Subgroup CFSG CFSG.GH74.Uniqueness.SU
open scoped commutatorElement

variable {H : Type} [Group H] [Finite H]

theorem exists_normal_elemAb {Q : Subgroup H} (hQn : Q.Normal) (hQ : IsPGroup 2 Q) (hne : Q ≠ ⊥) :
    ∃ A : Subgroup H, A.Normal ∧ Open.IsElemAbelian 2 A ∧ A ≠ ⊥ ∧ A ≤ Q := by
  let A : Subgroup H :=
    { carrier := {a | a ∈ Q ∧ (∀ q ∈ Q, a * q = q * a) ∧ a * a = 1}
      one_mem' := ⟨Q.one_mem, fun q _ => by simp, by simp⟩
      mul_mem' := by
        rintro a b ⟨haQ, hac, ha2⟩ ⟨hbQ, hbc, hb2⟩
        refine ⟨Q.mul_mem haQ hbQ, fun q hq => ?_, ?_⟩
        · rw [mul_assoc, hbc q hq, ← mul_assoc, hac q hq, mul_assoc]
        · calc a * b * (a * b) = a * (b * a) * b := by group
            _ = a * (a * b) * b := by rw [hbc a haQ]
            _ = (a * a) * (b * b) := by group
            _ = 1 := by rw [ha2, hb2]; group
      inv_mem' := by
        rintro a ⟨haQ, hac, ha2⟩
        have hinv : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha2
        rw [hinv]
        exact ⟨haQ, hac, ha2⟩ }
  have hAmem : ∀ a, a ∈ A ↔ a ∈ Q ∧ (∀ q ∈ Q, a * q = q * a) ∧ a * a = 1 := fun a => Iff.rfl
  refine ⟨A, ?_, ?_, ?_, fun a ha => ((hAmem a).mp ha).1⟩
  · refine ⟨fun a ha g => ?_⟩
    obtain ⟨haQ, hac, ha2⟩ := (hAmem a).mp ha
    rw [hAmem]
    refine ⟨hQn.conj_mem a haQ g, fun q hq => ?_, ?_⟩
    · have hq' : g⁻¹ * q * g ∈ Q := by
        have := hQn.conj_mem q hq g⁻¹
        simpa using this
      have := hac _ hq'
      calc g * a * g⁻¹ * q = g * (a * (g⁻¹ * q * g)) * g⁻¹ := by group
        _ = g * ((g⁻¹ * q * g) * a) * g⁻¹ := by rw [this]
        _ = q * (g * a * g⁻¹) := by group
    · calc g * a * g⁻¹ * (g * a * g⁻¹) = g * (a * a) * g⁻¹ := by group
        _ = 1 := by rw [ha2]; group
  · rw [SU1.isElemAbelian_iff]
    refine ⟨fun a ha b hb => ?_, fun a ha => ?_⟩
    · exact ((hAmem a).mp ha).2.1 b ((hAmem b).mp hb).1
    · rw [pow_two]; exact ((hAmem a).mp ha).2.2
  ·
    have hQnt : Nontrivial Q := (Subgroup.nontrivial_iff_ne_bot Q).mpr hne
    have hZ : Nontrivial (Subgroup.center Q) := IsPGroup.center_nontrivial hQ
    obtain ⟨z, hz1⟩ := exists_ne (1 : Subgroup.center Q)
    set z₀ : Q := (z : Q) with hz₀
    have hz₀1 : z₀ ≠ 1 := fun h => hz1 (Subtype.ext h)
    obtain ⟨j, hj⟩ := (IsPGroup.iff_orderOf.mp hQ) z₀
    have hj1 : j ≠ 0 := by
      rintro rfl
      exact hz₀1 (orderOf_eq_one_iff.mp (by simpa using hj))
    have hord : orderOf z₀ ≠ 0 := by rw [hj]; positivity
    have h2dvd : 2 ∣ orderOf z₀ := by
      rw [hj]; exact dvd_pow_self 2 hj1
    set w : Q := z₀ ^ (orderOf z₀ / 2) with hw
    have hwo : orderOf w = 2 := orderOf_pow_orderOf_div hord h2dvd
    have hw2 : w * w = 1 := by
      have : w ^ 2 = 1 := hwo ▸ pow_orderOf_eq_one w
      rwa [pow_two] at this
    have hwc : w ∈ Subgroup.center Q := Subgroup.pow_mem _ z.2 _
    have hw1 : w ≠ 1 := by
      intro h; rw [h, orderOf_one] at hwo; omega
    intro hbot
    have hwA : (w : H) ∈ A := by
      rw [hAmem]
      refine ⟨w.2, fun q hq => ?_, ?_⟩
      · have := Subgroup.mem_center_iff.mp hwc ⟨q, hq⟩
        exact congrArg Subtype.val this.symm
      · exact congrArg Subtype.val hw2
    have : (w : H) ∈ (⊥ : Subgroup H) := hbot ▸ hwA
    rw [Subgroup.mem_bot] at this
    exact hw1 (Subtype.ext this)


theorem perm3_two_group_aux (σ τ : Equiv.Perm (Fin 3)) :
    ¬ (σ * σ = 1 ∧ τ * τ = 1 ∧ σ ≠ 1 ∧ τ ≠ 1 ∧ (σ⁻¹ * τ) * (σ⁻¹ * τ) = 1 ∧ σ ≠ τ) := by
  revert σ τ
  decide

theorem perm3_two_group (σ τ : Equiv.Perm (Fin 3)) :
    σ * σ = 1 → τ * τ = 1 → σ ≠ 1 → τ ≠ 1 → (σ⁻¹ * τ) * (σ⁻¹ * τ) = 1 → σ = τ := by
  intro h1 h2 h3 h4 h5
  by_contra h6
  exact perm3_two_group_aux σ τ ⟨h1, h2, h3, h4, h5, h6⟩

theorem perm3_two_group' {α : Type*} [Fintype α] [DecidableEq α] (hα : Fintype.card α = 3)
    (σ τ : Equiv.Perm α) :
    σ * σ = 1 → τ * τ = 1 → σ ≠ 1 → τ ≠ 1 → (σ⁻¹ * τ) * (σ⁻¹ * τ) = 1 → σ = τ := by
  let e : α ≃ Fin 3 := Fintype.equivFinOfCardEq hα
  let φ : Equiv.Perm α ≃* Equiv.Perm (Fin 3) := Equiv.permCongrHom e
  intro h1 h2 h3 h4 h5
  apply φ.injective
  apply perm3_two_group
  · rw [← map_mul, h1, map_one]
  · rw [← map_mul, h2, map_one]
  · exact fun h => h3 (φ.injective (by rw [h, map_one]))
  · exact fun h => h4 (φ.injective (by rw [h, map_one]))
  · rw [← map_inv, ← map_mul, ← map_mul, h5, map_one]

theorem actPerm_sq {A : Subgroup H} [A.Normal] (hcard : Nat.card A = 4) {t : H}
    (ht : ∃ k : ℕ, orderOf t = 2 ^ k) : actPerm A t * actPerm A t = 1 := by
  classical
  let : Fintype {a : A // a ≠ 1} := Fintype.ofFinite _
  have h3 : Fintype.card {a : A // a ≠ 1} = 3 := by
    rw [← Nat.card_eq_fintype_card]; exact card_nonidentity A hcard
  obtain ⟨k, hk⟩ := ht
  have h1 : orderOf (actPerm A t) ∣ 2 ^ k := hk ▸ orderOf_map_dvd _ t
  have hcardPerm : Nat.card (Equiv.Perm {a : A // a ≠ 1}) = 6 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_perm, h3]; rfl
  have h2 : orderOf (actPerm A t) ∣ 6 := hcardPerm ▸ orderOf_dvd_natCard _
  have h5 : orderOf (actPerm A t) ∣ 2 := by
    obtain ⟨i, hi, hord⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h1
    rw [hord] at h2 ⊢
    by_cases hi2 : 2 ≤ i
    · exfalso
      have h4 : 2 ^ 2 ∣ 2 ^ i := pow_dvd_pow 2 hi2
      have := h4.trans h2
      omega
    · have : i ≤ 1 := by omega
      calc 2 ^ i ∣ 2 ^ 1 := pow_dvd_pow 2 this
        _ = 2 := by norm_num
  have : actPerm A t ^ 2 = 1 := orderOf_dvd_iff_pow_eq_one.mp h5
  rwa [pow_two] at this

omit [Finite H] in
theorem exists_orderOf_eq_two_pow {T : Subgroup H} (hT : IsPGroup 2 T) {t : H} (ht : t ∈ T) :
    ∃ k : ℕ, orderOf t = 2 ^ k := by
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hT) ⟨t, ht⟩
  exact ⟨k, by rw [← hk]; exact (Subgroup.orderOf_mk t ht).symm⟩

theorem actPerm_eq_of_two_group {A : Subgroup H} [A.Normal] (hcard : Nat.card A = 4)
    {T : Subgroup H} (hT : IsPGroup 2 T) {t₁ t₂ : H} (h₁ : t₁ ∈ T) (h₂ : t₂ ∈ T)
    (n₁ : actPerm A t₁ ≠ 1) (n₂ : actPerm A t₂ ≠ 1) : actPerm A t₁ = actPerm A t₂ := by
  classical
  let : Fintype {a : A // a ≠ 1} := Fintype.ofFinite _
  have h3 : Fintype.card {a : A // a ≠ 1} = 3 := by
    rw [← Nat.card_eq_fintype_card]; exact card_nonidentity A hcard
  have s1 := actPerm_sq hcard (exists_orderOf_eq_two_pow hT h₁)
  have s2 := actPerm_sq hcard (exists_orderOf_eq_two_pow hT h₂)
  have s12 := actPerm_sq hcard (exists_orderOf_eq_two_pow hT (T.mul_mem (T.inv_mem h₁) h₂))
  refine perm3_two_group' h3 _ _ s1 s2 n₁ n₂ ?_
  rw [← map_inv, ← map_mul]
  exact s12

omit [Finite H] in
theorem actPerm_eq_one_iff {A : Subgroup H} [A.Normal] (t : H) :
    actPerm A t = 1 ↔ ∀ a ∈ A, t * a * t⁻¹ = a := by
  constructor
  · intro h a ha
    by_cases ha1 : a = 1
    · rw [ha1]; group
    · have hne : (⟨a, ha⟩ : A) ≠ 1 := fun h' => ha1 (congrArg Subtype.val h')
      have h5 : (((actPerm A t ⟨⟨a, ha⟩, hne⟩ : {a : A // a ≠ 1}) : A) : H) = t * a * t⁻¹ :=
        actPerm_apply A t ⟨a, ha⟩ hne
      rw [h] at h5
      exact h5.symm
  · intro h
    ext ⟨⟨a, ha⟩, hne⟩
    have h5 : (((actPerm A t ⟨⟨a, ha⟩, hne⟩ : {a : A // a ≠ 1}) : A) : H) = t * a * t⁻¹ :=
      actPerm_apply A t ⟨a, ha⟩ hne
    rw [h5]
    exact h a ha

omit [Finite H] in
theorem mem_centralizer_iff_actPerm {A : Subgroup H} [A.Normal] (t : H) :
    t ∈ centralizer (A : Set H) ↔ actPerm A t = 1 := by
  rw [actPerm_eq_one_iff, Subgroup.mem_centralizer_iff]
  constructor
  · intro h a ha
    have := h a ha
    calc t * a * t⁻¹ = a * t * t⁻¹ := by rw [← this]
      _ = a := by group
  · intro h a ha
    have := h a ha
    calc a * t = t * a * t⁻¹ * t := by rw [this]
      _ = t * a := by group

theorem sylow_eq_sup {A : Subgroup H} [A.Normal] (hcard : Nat.card A = 4) {T : Subgroup H}
    (hT : IsPGroup 2 T) {x : H} (hxT : x ∈ T) (hxA : ∃ a ∈ A, x * a * x⁻¹ ≠ a) :
    T = (T ⊓ centralizer (A : Set H)) ⊔ zpowers x := by
  have hx1 : actPerm A x ≠ 1 := by
    rw [Ne, actPerm_eq_one_iff]
    push Not
    exact hxA
  apply le_antisymm
  · intro t ht
    by_cases ht1 : actPerm A t = 1
    · exact Subgroup.mem_sup_left ⟨ht, (mem_centralizer_iff_actPerm t).mpr ht1⟩
    · have heq := actPerm_eq_of_two_group hcard hT hxT ht hx1 ht1
      have hc : x⁻¹ * t ∈ centralizer (A : Set H) := by
        rw [mem_centralizer_iff_actPerm, map_mul, map_inv, heq, inv_mul_cancel]
      have hT' : x⁻¹ * t ∈ T := T.mul_mem (T.inv_mem hxT) ht
      have : t = x * (x⁻¹ * t) := by group
      rw [this]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_right (mem_zpowers x))
        (Subgroup.mem_sup_left ⟨hT', hc⟩)
  · exact sup_le inf_le_left (Subgroup.zpowers_le.mpr hxT)

theorem frattini_cent {A : Subgroup H} [A.Normal] (T : Sylow 2 H) (g : H) :
    ∃ n ∈ normalizer (((T : Subgroup H) ⊓ centralizer (A : Set H) : Subgroup H) : Set H),
      ∃ c ∈ centralizer (A : Set H), g = n * c := by
  have : (centralizer (A : Set H)).Normal := inferInstance
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let PK : Sylow 2 (centralizer (A : Set H)) :=
    CFSG.BenderSuzuki.External.hallSylowSubgroupOfNormal T (centralizer (A : Set H))
  have hPK : (PK : Subgroup (centralizer (A : Set H))).map (centralizer (A : Set H)).subtype =
      (T : Subgroup H) ⊓ centralizer (A : Set H) := by
    rw [show (PK : Subgroup (centralizer (A : Set H))) =
      (T : Subgroup H).comap (centralizer (A : Set H)).subtype from
        CFSG.BenderSuzuki.External.hallSylowSubgroupOfNormal_coe T _]
    rw [Subgroup.comap_subtype, Subgroup.subgroupOf_map_subtype, inf_comm]
  have hfr : normalizer (((T : Subgroup H) ⊓ centralizer (A : Set H) : Subgroup H) : Set H) ⊔
      centralizer (A : Set H) = ⊤ := by
    simpa [hPK] using
      (Sylow.normalizer_sup_eq_top (G := H) (N := centralizer (A : Set H)) PK)
  have hg : g ∈ normalizer (((T : Subgroup H) ⊓ centralizer (A : Set H) : Subgroup H) : Set H) ⊔
      centralizer (A : Set H) := by rw [hfr]; trivial
  obtain ⟨n, hn, c, hc, hnc⟩ := Subgroup.mem_sup_of_normal_right.mp hg
  exact ⟨n, hn, c, hc, hnc.symm⟩

omit [Finite H] in
theorem mem_normalizer_inf {A : Subgroup H} [A.Normal] {T : Subgroup H} {t : H} (ht : t ∈ T) :
    t ∈ normalizer ((T ⊓ centralizer (A : Set H) : Subgroup H) : Set H) := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  have hC : (centralizer (A : Set H)).Normal := inferInstance
  constructor
  · intro hh
    exact ⟨T.mul_mem (T.mul_mem ht hh.1) (T.inv_mem ht), hC.conj_mem h hh.2 t⟩
  · intro hh
    have h1 : h = t⁻¹ * (t * h * t⁻¹) * t := by group
    rw [h1]
    exact ⟨T.mul_mem (T.mul_mem (T.inv_mem ht) hh.1) ht, by
      have := hC.conj_mem _ hh.2 t⁻¹
      simpa using this⟩

theorem exists_y {A : Subgroup H} [A.Normal] (hcen : Subgroup.center H = ⊥)
    (hcard : Nat.card A = 4) (T : Sylow 2 H) {x : H} (hx : x * x = 1) (hxT : x ∈ (T : Subgroup H))
    (hxA : ∃ a ∈ A, x * a * x⁻¹ ≠ a) :
    ∃ y : H, y ∈ normalizer (((T : Subgroup H) ⊓ centralizer (A : Set H) : Subgroup H) : Set H) ∧
      IsPGroup 3 (zpowers y) ∧ x * y * x⁻¹ = y⁻¹ ∧ ∀ a ∈ A, a ≠ 1 → y * a * y⁻¹ ≠ a := by
  obtain ⟨g₀, hg₀⟩ := exists_fpf_element A hcen hcard
  obtain ⟨n, hn, c, hc, hnc⟩ := frattini_cent (A := A) T g₀
  have hfpf : ∀ a ∈ A, a ≠ 1 → n * a * n⁻¹ ≠ a := by
    intro a ha ha1 h
    apply hg₀ a ha ha1
    have hcomm : ∀ b ∈ A, c * b * c⁻¹ = b := fun b hb => by
      have := Subgroup.mem_centralizer_iff.mp hc b hb
      calc c * b * c⁻¹ = b * c * c⁻¹ := by rw [← this]
        _ = b := by group
    have hnA : n * a * n⁻¹ ∈ A := Subgroup.Normal.conj_mem inferInstance a ha n
    rw [hnc]
    calc n * c * a * (n * c)⁻¹ = n * (c * a * c⁻¹) * n⁻¹ := by group
      _ = n * a * n⁻¹ := by rw [hcomm a ha]
      _ = a := h
  have hxN := mem_normalizer_inf (A := A) hxT
  set ρ : H := x * (n⁻¹ * x * n) with hρdef
  have hρN : ρ ∈ normalizer (((T : Subgroup H) ⊓ centralizer (A : Set H) : Subgroup H) : Set H) :=
    Subgroup.mul_mem _ hxN (Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hn) hxN) hn)
  have hxρ : x * ρ * x⁻¹ = ρ⁻¹ := by
    have hxi : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx
    rw [hρdef, hxi]
    have hx' : (n⁻¹ * x * n) * (n⁻¹ * x * n) = 1 := by
      calc n⁻¹ * x * n * (n⁻¹ * x * n) = n⁻¹ * (x * x) * n := by group
        _ = 1 := by rw [hx]; group
    calc x * (x * (n⁻¹ * x * n)) * x = (x * x) * (n⁻¹ * x * n) * x := by group
      _ = (n⁻¹ * x * n) * x := by rw [hx]; group
      _ = (x * (n⁻¹ * x * n))⁻¹ := by
        rw [mul_inv_rev]
        have : (n⁻¹ * x * n)⁻¹ = n⁻¹ * x * n := inv_eq_of_mul_eq_one_right hx'
        rw [this, hxi]
  have hrho : ∀ k : ℕ, ¬ 3 ∣ k → ∀ a ∈ A, a ≠ 1 → ρ ^ k * a * (ρ ^ k)⁻¹ ≠ a :=
    rho_fpf A hcard x n hx hxA hfpf
  have hA1 : ∃ a ∈ A, a ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have : A = ⊥ := by
      rw [Subgroup.eq_bot_iff_forall]
      exact hcon
    rw [this, Subgroup.card_bot] at hcard
    omega
  obtain ⟨a₁, ha₁, ha₁1⟩ := hA1
  have hm0 : orderOf ρ ≠ 0 := (orderOf_pos ρ).ne'
  have h3m : 3 ∣ orderOf ρ := by
    by_contra h3
    apply hrho (orderOf ρ) h3 a₁ ha₁ ha₁1
    rw [pow_orderOf_eq_one]; group
  set v : ℕ := (orderOf ρ).factorization 3 with hv
  have h3v : 3 ^ v ∣ orderOf ρ := Nat.ordProj_dvd _ _
  have hcop : ¬ 3 ∣ orderOf ρ / 3 ^ v := Nat.not_dvd_ordCompl Nat.prime_three hm0
  refine ⟨ρ ^ (orderOf ρ / 3 ^ v), Subgroup.pow_mem _ hρN _, ?_, ?_, ?_⟩
  · apply IsPGroup.of_card (n := v)
    rw [Nat.card_zpowers]
    exact orderOf_pow_orderOf_div hm0 h3v
  · rw [← conj_pow, hxρ, inv_pow]
  · exact hrho _ hcop

omit [Finite H] in
theorem mul_self_eq_one_of_orderOf_two {u : H} (h : orderOf u = 2) : u * u = 1 := by
  have : u ^ 2 = 1 := h ▸ pow_orderOf_eq_one u
  rwa [pow_two] at this

theorem exists_fixed_involution {X : Subgroup H} (hX : IsPGroup 2 X) (hne : X ≠ ⊥) {x : H}
    (hx : x * x = 1) (hxX : ∀ s ∈ X, x * s * x⁻¹ ∈ X) :
    ∃ u ∈ X, u ≠ 1 ∧ u * u = 1 ∧ x * u * x⁻¹ = u := by
  classical
  have hxi : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx
  let σ : Equiv.Perm X :=
    { toFun := fun s => ⟨x * s * x⁻¹, hxX s s.2⟩
      invFun := fun s => ⟨x * s * x⁻¹, hxX s s.2⟩
      left_inv := fun s => by
        apply Subtype.ext
        change x * (x * (s : H) * x⁻¹) * x⁻¹ = s
        calc x * (x * (s : H) * x⁻¹) * x⁻¹ = (x * x) * (s : H) * (x * x)⁻¹ := by group
          _ = s := by rw [hx]; group
      right_inv := fun s => by
        apply Subtype.ext
        change x * (x * (s : H) * x⁻¹) * x⁻¹ = s
        calc x * (x * (s : H) * x⁻¹) * x⁻¹ = (x * x) * (s : H) * (x * x)⁻¹ := by group
          _ = s := by rw [hx]; group }
  have hσ : σ ^ 2 ^ 1 = 1 := by
    ext s
    change x * (x * (s : H) * x⁻¹) * x⁻¹ = s
    calc x * (x * (s : H) * x⁻¹) * x⁻¹ = (x * x) * (s : H) * (x * x)⁻¹ := by group
      _ = s := by rw [hx]; group
  let : Fintype X := Fintype.ofFinite X
  have hcard : 2 ∣ Fintype.card X := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hX
    have hn0 : n ≠ 0 := by
      rintro rfl
      apply hne
      rw [Subgroup.eq_bot_iff_card]
      simpa using hn
    rw [← Nat.card_eq_fintype_card, hn]
    exact dvd_pow_self 2 hn0
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨b, hb, hb1⟩ := Equiv.Perm.exists_fixed_point_of_prime' hcard hσ
    (a := (1 : X)) (by apply Subtype.ext; change x * 1 * x⁻¹ = 1; group)
  have hbfix : x * (b : H) * x⁻¹ = b := congrArg Subtype.val hb
  have hb1' : (b : H) ≠ 1 := fun h => hb1 (Subtype.ext h)
  obtain ⟨k, hk⟩ := exists_orderOf_eq_two_pow hX b.2
  have hk0 : k ≠ 0 := by
    rintro rfl
    exact hb1' (orderOf_eq_one_iff.mp (by simpa using hk))
  have hord : orderOf (b : H) ≠ 0 := (orderOf_pos _).ne'
  have h2dvd : 2 ∣ orderOf (b : H) := by rw [hk]; exact dvd_pow_self 2 hk0
  set u : H := (b : H) ^ (orderOf (b : H) / 2) with hu
  have huo : orderOf u = 2 := orderOf_pow_orderOf_div hord h2dvd
  refine ⟨u, Subgroup.pow_mem _ b.2 _, ?_, mul_self_eq_one_of_orderOf_two huo, ?_⟩
  · intro h; rw [h, orderOf_one] at huo; omega
  · rw [hu, ← conj_pow, hbfix]

end CFSG.GH74.Uniqueness.SU.K.R3
