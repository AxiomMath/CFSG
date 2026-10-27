module

public import CFSG.LocalAnalysis.ComponentClassification.GMS78Lemma313

public section

namespace CFSG.ComponentClassification.GMS78

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.RankTwoStandard

variable {G : Type} [Group G] [Finite G]

namespace Lemma313

variable {L T : Subgroup G} {q : ℕ}

omit [Finite G] in
theorem normalizer_le (h313 : Lemma313 L T q) :
    normalizer (gmsV L T : Set G) ≤ normalizer (gmsA L T : Set G) := by
  intro n hn
  have hc : ∀ g ∈ normalizer (gmsV L T : Set G), ∀ a ∈ gmsA L T, g * a * g⁻¹ ∈ gmsA L T :=
    fun g hg a ha => h313.stronglyClosed a ha g ((mem_normalizer_iff.mp hg a).mp (mem_sup_left ha))
  exact mem_normalizer_of_conj_mem (hc n hn) (fun a ha => by simpa using hc n⁻¹ (inv_mem hn) a ha)

omit [Finite G] in
theorem inf_gmsA_eq_bot (h313 : Lemma313 L T q) {Q : Subgroup G} (hQ : Q ∈ gmsDelta L T) :
    Q ⊓ gmsA L T = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨hxQ, hxA⟩ := mem_inf.mp hx
  by_contra hx1
  exact ((h313.cover x (hQ.2 hxQ)).mpr ⟨Q, hQ, hxQ, hx1⟩) hxA

end Lemma313

namespace Sec3

variable {L T : Subgroup G} {q : ℕ}

omit [Finite G] in
theorem card_of_mem_delta {Q : Subgroup G} (hQ : Q ∈ gmsDelta L T) :
    Nat.card Q = Nat.card (T ⊓ centralizer (L : Set G) : Subgroup G) := by
  obtain ⟨⟨x, rfl⟩, -⟩ := hQ
  exact rightConjugate_card _ _

omit [Finite G] in
theorem rightConjugate_mem_delta {Q : Subgroup G} (hQ : Q ∈ gmsDelta L T) {n : G}
    (hn : n ∈ normalizer (gmsV L T : Set G)) : rightConjugate Q n ∈ gmsDelta L T := by
  obtain ⟨⟨x, rfl⟩, hQV⟩ := hQ
  refine ⟨⟨x * n, (rightConjugate_mul _ _ _).symm⟩, ?_⟩
  calc rightConjugate (rightConjugate (T ⊓ centralizer (L : Set G)) x) n ≤
        rightConjugate (gmsV L T) n := map_mono hQV
    _ = gmsV L T := (rightConjugate_eq_self_iff _ _).mpr hn

theorem _root_.CFSG.ComponentClassification.GMS78.Lemma313.exists_mul_mem
    (h313 : Lemma313 L T q) (hX : Facts L T q) (h : Sec3 G L T) (hF : Foundation)
    {Q : Subgroup G} (hQ : Q ∈ gmsDelta L T) {v : G} (hv : v ∈ gmsV L T) :
    ∃ a ∈ gmsA L T, a * v ∈ Q := by
  obtain ⟨hVc, hVel, -, -, -⟩ := hX.vFacts h hF
  obtain ⟨hA₁c, -, -⟩ := hX.sylow h
  have hcomm : ∀ x ∈ gmsV L T, ∀ y ∈ gmsV L T, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hVel.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hAN : gmsA L T ≤ normalizer (Q : Set G) := fun a ha =>
    Subgroup.centralizer_le_normalizer _ (mem_centralizer_iff.mpr fun d hd =>
      hcomm d (hQ.2 hd) a (mem_sup_left ha))
  have h1 := CFSG.Walter.W67.card_sup_mul_card_inf_of_le_normalizer hAN
  rw [h313.inf_gmsA_eq_bot hQ, card_bot, mul_one, sup_comm, card_of_mem_delta hQ, hA₁c] at h1
  have hle : gmsA L T ⊔ Q ≤ gmsV L T := sup_le le_sup_left hQ.2
  have heq : gmsA L T ⊔ Q = gmsV L T := eq_of_le_of_card_ge hle (by rw [h1, hVc, mul_comm])
  rw [← heq] at hv
  obtain ⟨a, ha, d, hd, rfl⟩ := CFSG.Goldschmidt.G37.mem_sup_of_le_normalizer hAN hv
  exact ⟨a⁻¹, inv_mem ha, by simpa using hd⟩

omit [Finite G] in
theorem mem_delta_T₀ : T ⊓ centralizer (L : Set G) ∈ gmsDelta L T :=
  ⟨⟨1, rightConjugate_one _⟩, le_sup_right⟩

structure IsTorus (L T : Subgroup G) (y : G) : Prop where
  mem : y ∈ L ⊓ normalizer ((T ⊓ L : Subgroup G) : Set G)
  odd : Odd (orderOf y)
  trans : ∀ a ∈ gmsA L T, ∀ b ∈ gmsA L T, a ≠ 1 → b ≠ 1 → ∃ m : ℕ, (y ^ m)⁻¹ * a * y ^ m = b
  conj : ∀ w ∈ normalizer (L : Set G) ⊓ normalizer (gmsV L T : Set G),
    w⁻¹ * y * w ∈ zpowers y ⊔ centralizer (gmsV L T : Set G)

theorem Facts.exists_isTorus (hX : Facts L T q) (h : Sec3 G L T) : ∃ y, IsTorus L T y := by
  obtain ⟨y, hy, hyodd, htrans, hconj⟩ := hX.exists_torus_conj h
  exact ⟨y, ⟨hy, hyodd, htrans, hconj⟩⟩

namespace IsTorus

variable {y : G}

omit [Finite G] in
theorem commute (hy : IsTorus L T y) {t : G} (ht : t ∈ T ⊓ centralizer (L : Set G)) :
    y * t = t * y :=
  mem_centralizer_iff.mp (mem_inf.mp ht).2 y (mem_inf.mp hy.mem).1

omit [Finite G] in
theorem mem_normalizer (hy : IsTorus L T y) : y ∈ normalizer (gmsV L T : Set G) :=
  inf_normalizer_le_normalizer hy.mem

omit [Finite G] in
theorem mem_normalizer_gmsA (hy : IsTorus L T y) : y ∈ normalizer (gmsA L T : Set G) := by
  obtain ⟨-, hyN⟩ := mem_inf.mp hy.mem
  refine mem_normalizer_of_conj_mem (fun a ha => ?_) (fun a ha => ?_)
  · refine mem_inf.mpr ⟨(mem_normalizer_iff.mp hyN a).mp (mem_inf.mp ha).1,
      mem_centralizer_iff.mpr fun p hp => ?_⟩
    have hp' : y⁻¹ * p * y ∈ T ⊓ L := by simpa using (mem_normalizer_iff.mp (inv_mem hyN) p).mp hp
    have h1 : y⁻¹ * p * y * a = a * (y⁻¹ * p * y) := mem_centralizer_iff.mp (mem_inf.mp ha).2 _ hp'
    calc p * (y * a * y⁻¹) = y * (y⁻¹ * p * y * a) * y⁻¹ := by group
      _ = y * (a * (y⁻¹ * p * y)) * y⁻¹ := by rw [h1]
      _ = y * a * y⁻¹ * p := by group
  · refine mem_inf.mpr ⟨by simpa using (mem_normalizer_iff.mp (inv_mem hyN) a).mp (mem_inf.mp ha).1,
      mem_centralizer_iff.mpr fun p hp => ?_⟩
    have hp' : y * p * y⁻¹ ∈ T ⊓ L := (mem_normalizer_iff.mp hyN p).mp hp
    have h1 : y * p * y⁻¹ * a = a * (y * p * y⁻¹) := mem_centralizer_iff.mp (mem_inf.mp ha).2 _ hp'
    calc p * (y⁻¹ * a * y) = y⁻¹ * (y * p * y⁻¹ * a) * y := by group
      _ = y⁻¹ * (a * (y * p * y⁻¹)) * y := by rw [h1]
      _ = y⁻¹ * a * y * p := by group

omit [Finite G] in
theorem eq_of_conj_eq (hy : IsTorus L T y) {k : ℤ} {a : G} (ha : a ∈ gmsA L T) (ha1 : a ≠ 1)
    (hk : y ^ k * a * (y ^ k)⁻¹ = a) {b : G} (hb : b ∈ gmsA L T) : y ^ k * b * (y ^ k)⁻¹ = b := by
  by_cases hb1 : b = 1
  · rw [hb1]
    group
  obtain ⟨m, hm⟩ := hy.trans a ha b hb ha1 hb1
  rw [← hm]
  have hc : y ^ k * (y ^ m)⁻¹ = (y ^ m)⁻¹ * y ^ k := by
    rw [← zpow_natCast, ← zpow_neg, ← zpow_add, ← zpow_add, add_comm]
  have hc' : y ^ m * (y ^ k)⁻¹ = (y ^ k)⁻¹ * y ^ m := by
    rw [← zpow_natCast, ← zpow_neg, ← zpow_add, ← zpow_add, add_comm]
  calc y ^ k * ((y ^ m)⁻¹ * a * y ^ m) * (y ^ k)⁻¹
      = (y ^ k * (y ^ m)⁻¹) * a * (y ^ m * (y ^ k)⁻¹) := by group
    _ = (y ^ m)⁻¹ * (y ^ k * a * (y ^ k)⁻¹) * y ^ m := by rw [hc, hc']; group
    _ = (y ^ m)⁻¹ * a * y ^ m := by rw [hk]

@[expose] noncomputable def aut (hy : IsTorus L T y) : MulAut (gmsA L T) :=
  (gmsA L T).normalizerMonoidHom ⟨y, hy.mem_normalizer_gmsA⟩

omit [Finite G] in
theorem aut_zpow_apply (hy : IsTorus L T y) (k : ℤ) (b : gmsA L T) :
    ((hy.aut ^ k) b : G) = y ^ k * b * (y ^ k)⁻¹ := by
  rw [aut, ← map_zpow, normalizerMonoidHom_apply_apply_coe]
  rfl

omit [Finite G] in
theorem aut_pow_apply (hy : IsTorus L T y) (k : ℕ) (b : gmsA L T) :
    ((hy.aut ^ k) b : G) = y ^ k * b * (y ^ k)⁻¹ := by
  have := hy.aut_zpow_apply (k : ℤ) b
  simpa using this

theorem orderOf_aut (hy : IsTorus L T y) (hX : Facts L T q) (h : Sec3 G L T) :
    orderOf hy.aut = q - 1 := by
  classical
  obtain ⟨hA₁c, -, -⟩ := hX.sylow h
  have hq := hX.four_le
  obtain ⟨a₀, ha₀, ha₀1⟩ : ∃ a ∈ gmsA L T, a ≠ 1 := by
    have h1 : 1 < Nat.card (gmsA L T) := by rw [hA₁c]; omega
    obtain ⟨⟨a, ha⟩, ha1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp
      ((Subgroup.one_lt_card_iff_ne_bot _).mp h1)
    exact ⟨a, ha, fun h1 => ha1 (Subtype.ext h1)⟩
  set Y := zpowers hy.aut with hY
  set b₀ : gmsA L T := ⟨a₀, ha₀⟩ with hb₀
  have hb₀1 : b₀ ≠ 1 := fun h1 => ha₀1 (congrArg Subtype.val h1)
  have horb : MulAction.orbit Y b₀ = {b | b ≠ 1} := by
    ext b
    simp only [Set.mem_ofPred_eq]
    constructor
    · rintro ⟨g, rfl⟩ h1
      apply hb₀1
      have : (g : MulAut (gmsA L T)) b₀ = (g : MulAut (gmsA L T)) 1 := by
        rw [map_one]
        exact h1
      exact (g : MulAut (gmsA L T)).injective this
    · intro hb1
      obtain ⟨m, hm⟩ := hy.trans a₀ ha₀ b b.2 ha₀1 (fun h1 => hb1 (Subtype.ext h1))
      refine ⟨⟨hy.aut ^ (-(m : ℤ)), zpow_mem (mem_zpowers _) _⟩, Subtype.ext ?_⟩
      change ((hy.aut ^ (-(m : ℤ))) b₀ : G) = b
      rw [hy.aut_zpow_apply, ← hm, zpow_neg, inv_inv, zpow_natCast]
  have hstab : MulAction.stabilizer Y b₀ = ⊥ := by
    rw [eq_bot_iff]
    rintro ⟨g, hg⟩ hgs
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hg
    have hk : y ^ k * a₀ * (y ^ k)⁻¹ = a₀ :=
      calc y ^ k * a₀ * (y ^ k)⁻¹ = ((hy.aut ^ k) b₀ : G) := (hy.aut_zpow_apply k b₀).symm
        _ = a₀ := congrArg Subtype.val (MulAction.mem_stabilizer_iff.mp hgs)
    rw [mem_bot]
    apply Subtype.ext
    apply MulEquiv.ext
    intro b
    apply Subtype.ext
    change ((hy.aut ^ k) b : G) = b
    rw [hy.aut_zpow_apply]
    exact hy.eq_of_conj_eq ha₀ ha₀1 hk b.2
  have h1 := MulAction.index_stabilizer Y b₀
  rw [horb, hstab, index_bot] at h1
  have h2 : ({b : gmsA L T | b ≠ 1} : Set (gmsA L T)).ncard = q - 1 := by
    have : ({b : gmsA L T | b ≠ 1} : Set (gmsA L T)) = Set.univ \ {1} := by
      ext b
      simp
    rw [this, Set.ncard_sdiff_singleton_of_mem (Set.mem_univ _), Set.ncard_univ, hA₁c]
  rw [← Nat.card_zpowers, h1, h2]

omit [Finite G] in
theorem aut_inv_pow_apply (hy : IsTorus L T y) (k : ℕ) (b : gmsA L T) :
    (((hy.aut ^ k)⁻¹) b : G) = (y ^ k)⁻¹ * b * y ^ k := by
  have := hy.aut_zpow_apply (-(k : ℤ)) b
  rw [zpow_neg, zpow_natCast, zpow_neg, zpow_natCast, inv_inv] at this
  exact this

omit [Finite G] in
theorem aut_pow_eq_of_inv_conj_eq (hy : IsTorus L T y) {A B : ℕ} {a : G} (ha : a ∈ gmsA L T)
    (ha1 : a ≠ 1) (h : (y ^ A)⁻¹ * a * y ^ A = (y ^ B)⁻¹ * a * y ^ B) :
    hy.aut ^ A = hy.aut ^ B := by
  have hk : y ^ ((B : ℤ) - A) * a * (y ^ ((B : ℤ) - A))⁻¹ = a := by
    rw [zpow_sub, zpow_natCast, zpow_natCast]
    calc y ^ B * (y ^ A)⁻¹ * a * (y ^ B * (y ^ A)⁻¹)⁻¹
        = y ^ B * ((y ^ A)⁻¹ * a * y ^ A) * (y ^ B)⁻¹ := by group
      _ = y ^ B * ((y ^ B)⁻¹ * a * y ^ B) * (y ^ B)⁻¹ := by rw [h]
      _ = a := by group
  have h1 : hy.aut ^ ((B : ℤ) - A) = 1 := by
    apply MulEquiv.ext
    intro b
    apply Subtype.ext
    change ((hy.aut ^ ((B : ℤ) - A)) b : G) = b
    rw [hy.aut_zpow_apply]
    exact hy.eq_of_conj_eq ha ha1 hk b.2
  rw [zpow_sub, zpow_natCast, zpow_natCast, mul_inv_eq_one] at h1
  exact h1.symm

omit [Finite G] in
theorem inv_conj_eq_of_aut_pow_eq (hy : IsTorus L T y) {A B : ℕ} (h : hy.aut ^ A = hy.aut ^ B)
    {a : G} (ha : a ∈ gmsA L T) : (y ^ A)⁻¹ * a * y ^ A = (y ^ B)⁻¹ * a * y ^ B := by
  have h1 := congrArg (fun φ : MulAut (gmsA L T) => ((φ⁻¹ ⟨a, ha⟩ : gmsA L T) : G)) h
  simp only [hy.aut_inv_pow_apply] at h1
  exact h1

omit [Finite G] in
theorem aut_pow_eq_one_iff (hy : IsTorus L T y) (k : ℕ) :
    hy.aut ^ k = 1 ↔ ∀ b ∈ gmsA L T, y ^ k * b * (y ^ k)⁻¹ = b := by
  constructor
  · intro h b hb
    have := congrArg (fun φ : MulAut (gmsA L T) => ((φ ⟨b, hb⟩ : gmsA L T) : G)) h
    simp only [hy.aut_pow_apply] at this
    exact this
  · intro h
    apply MulEquiv.ext
    intro b
    apply Subtype.ext
    change ((hy.aut ^ k) b : G) = b
    rw [hy.aut_pow_apply]
    exact h b b.2

theorem aut_pow_eq_one_of_normalizer (hy : IsTorus L T y) (h313 : Lemma313 L T q)
    (h : Sec3 G L T) {Q : Subgroup G} (hQ : Q ∈ gmsDelta L T)
    (hQT : Q ≠ T ⊓ centralizer (L : Set G)) {k : ℕ}
    (hk : y ^ k ∈ normalizer (Q : Set G)) : hy.aut ^ k = 1 := by
  have hQ1 : Q ≠ ⊥ := by
    intro hb
    apply h.T₀_ne_bot
    have h1 := card_of_mem_delta hQ
    rw [hb, card_bot] at h1
    exact card_eq_one.mp h1.symm
  obtain ⟨⟨d, hdQ⟩, hd1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hQ1
  have hd1' : d ≠ 1 := fun h1 => hd1 (Subtype.ext h1)
  have hA₁N : gmsA L T ≤ normalizer ((T ⊓ centralizer (L : Set G) : Subgroup G) : Set G) :=
    fun a ha => (le_centralizer_iff.mp
      (show T ⊓ centralizer (L : Set G) ≤ centralizer ((T ⊓ L : Subgroup G) : Set G) from
        fun t ht => mem_centralizer_iff.mpr fun x hx =>
          mem_centralizer_iff.mp (mem_inf.mp ht).2 x (mem_inf.mp hx).2)).trans
      (Subgroup.centralizer_le_normalizer _) (mem_inf.mp ha).1
  obtain ⟨a, ha, t, ht, rfl⟩ := CFSG.Goldschmidt.G37.mem_sup_of_le_normalizer hA₁N (hQ.2 hdQ)
  have hQT₀ := h313.inf_eq_bot Q hQ _ mem_delta_T₀ hQT
  have ha1 : a ≠ 1 := by
    intro h1
    rw [h1, one_mul] at hdQ hd1'
    have : t ∈ Q ⊓ (T ⊓ centralizer (L : Set G)) := mem_inf.mpr ⟨hdQ, ht⟩
    rw [hQT₀, mem_bot] at this
    exact hd1' this
  have hyt : y ^ k * t = t * y ^ k := (Commute.pow_left (hy.commute ht) k)
  have hconj : y ^ k * (a * t) * (y ^ k)⁻¹ ∈ Q := (mem_normalizer_iff.mp hk _).mp hdQ
  have hya : y ^ k * a * (y ^ k)⁻¹ ∈ gmsA L T :=
    (mem_normalizer_iff.mp (pow_mem hy.mem_normalizer_gmsA k) a).mp ha
  have h1 : y ^ k * a * (y ^ k)⁻¹ * a⁻¹ ∈ Q ⊓ gmsA L T := by
    refine mem_inf.mpr ⟨?_, mul_mem hya (inv_mem ha)⟩
    have : y ^ k * a * (y ^ k)⁻¹ * a⁻¹ = (y ^ k * (a * t) * (y ^ k)⁻¹) * (a * t)⁻¹ := by
      calc y ^ k * a * (y ^ k)⁻¹ * a⁻¹ = y ^ k * a * (y ^ k)⁻¹ * (t * t⁻¹) * a⁻¹ := by group
        _ = y ^ k * a * ((y ^ k)⁻¹ * t) * t⁻¹ * a⁻¹ := by group
        _ = y ^ k * a * (t * (y ^ k)⁻¹) * t⁻¹ * a⁻¹ := by
            rw [show (y ^ k)⁻¹ * t = t * (y ^ k)⁻¹ by
              calc (y ^ k)⁻¹ * t = (y ^ k)⁻¹ * (t * y ^ k) * (y ^ k)⁻¹ := by group
                _ = (y ^ k)⁻¹ * (y ^ k * t) * (y ^ k)⁻¹ := by rw [hyt]
                _ = t * (y ^ k)⁻¹ := by group]
        _ = (y ^ k * (a * t) * (y ^ k)⁻¹) * (a * t)⁻¹ := by group
    rw [this]
    exact mul_mem hconj (inv_mem hdQ)
  rw [h313.inf_gmsA_eq_bot hQ, mem_bot, mul_inv_eq_one] at h1
  refine (hy.aut_pow_eq_one_iff k).mpr fun b hb => ?_
  have := hy.eq_of_conj_eq (k := (k : ℤ)) ha ha1 (by rw [zpow_natCast]; exact h1) hb
  rwa [zpow_natCast] at this

theorem exists_pow_eq (hy : IsTorus L T y) (h313 : Lemma313 L T q) (hX : Facts L T q)
    (h : Sec3 G L T) {Q Q' : Subgroup G} (hQ : Q ∈ gmsDelta L T)
    (hQT : Q ≠ T ⊓ centralizer (L : Set G)) (hQ' : Q' ∈ gmsDelta L T)
    (hQ'T : Q' ≠ T ⊓ centralizer (L : Set G)) : ∃ k : ℕ, rightConjugate Q (y ^ k) = Q' := by
  classical
  have hord := hy.orderOf_aut hX h
  have hq := hX.four_le
  set D := gmsDelta L T \ {T ⊓ centralizer (L : Set G)} with hDdef
  set f : ℕ → Subgroup G := fun k => rightConjugate Q (y ^ k) with hf
  have hT₀N : ∀ k : ℕ, (y ^ k)⁻¹ ∈ normalizer ((T ⊓ centralizer (L : Set G) : Subgroup G) :
      Set G) := fun k => inv_mem (Subgroup.centralizer_le_normalizer _
        (mem_centralizer_iff.mpr fun t ht => (Commute.pow_left (hy.commute ht) k).symm))
  have hfD : ∀ k, f k ∈ D := by
    intro k
    refine ⟨rightConjugate_mem_delta hQ (pow_mem hy.mem_normalizer k), fun hk => hQT ?_⟩
    have hk' : rightConjugate Q (y ^ k) = T ⊓ centralizer (L : Set G) := hk
    have := congrArg (fun X => rightConjugate X (y ^ k)⁻¹) hk'
    simp only [rightConjugate_mul, mul_inv_cancel, rightConjugate_one] at this
    rw [this]
    exact (rightConjugate_eq_self_iff _ _).mpr (hT₀N k)
  have hinj : Set.InjOn f (Finset.range (q - 1) : Set ℕ) := by
    intro i hi j hj hij
    simp only [Finset.coe_range, Set.mem_Iio] at hi hj
    by_contra hne
    have key : ∀ a b : ℕ, a < b → b < q - 1 → f a = f b → False := by
      intro a b hab hb hfab
      have hfa : f a ∈ gmsDelta L T := (hfD a).1
      have hfaT : f a ≠ T ⊓ centralizer (L : Set G) := fun h1 => (hfD a).2 h1
      have hnorm : y ^ (b - a) ∈ normalizer ((f a : Subgroup G) : Set G) := by
        rw [← rightConjugate_eq_self_iff]
        change rightConjugate (rightConjugate Q (y ^ a)) (y ^ (b - a)) = rightConjugate Q (y ^ a)
        rw [rightConjugate_mul, ← pow_add, Nat.add_sub_cancel' hab.le]
        exact hfab.symm
      have h1 := hy.aut_pow_eq_one_of_normalizer h313 h hfa hfaT hnorm
      rw [← orderOf_dvd_iff_pow_eq_one, hord] at h1
      have := Nat.le_of_dvd (by omega) h1
      omega
    rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
    · exact key i j hlt hj hij
    · exact key j i hlt hi hij.symm
  have hcardD : D.ncard = q - 1 := by
    rw [hDdef, Set.ncard_sdiff_singleton_of_mem mem_delta_T₀, ← Nat.card_coe_set_eq, h313.card_eq]
  have himg : f '' (Finset.range (q - 1) : Set ℕ) = D := by
    apply Set.eq_of_subset_of_ncard_le
    · rintro _ ⟨k, -, rfl⟩
      exact hfD k
    · rw [hinj.ncard_image, Set.ncard_coe_finset, Finset.card_range, hcardD]
    · exact Set.toFinite D
  have hQ'D : Q' ∈ D := ⟨hQ', hQ'T⟩
  rw [← himg] at hQ'D
  obtain ⟨k, -, hk⟩ := hQ'D
  exact ⟨k, hk⟩

theorem exists_conj_eq (hy : IsTorus L T y) (h313 : Lemma313 L T q) (hX : Facts L T q)
    (h : Sec3 G L T) {Q₁ : Subgroup G} (hQ₁ : Q₁ ∈ gmsDelta L T)
    (hQ₁T : Q₁ ≠ T ⊓ centralizer (L : Set G)) {x : G}
    (hxV : x ∈ normalizer (gmsV L T : Set G))
    (hxT₀ : ∀ t ∈ T ⊓ centralizer (L : Set G), x * t = t * x) (i : ℕ) :
    ∃ j : ℕ, ∀ w ∈ gmsA L T, ∀ t ∈ T ⊓ centralizer (L : Set G), w * t ∈ Q₁ →
      x * ((y ^ i)⁻¹ * w * y ^ i) * x⁻¹ = (y ^ j)⁻¹ * w * y ^ j := by
  set T₀ := T ⊓ centralizer (L : Set G) with hT₀def
  have hxT₀N : x ∈ normalizer (T₀ : Set G) :=
    Subgroup.centralizer_le_normalizer _ (mem_centralizer_iff.mpr fun t ht => (hxT₀ t ht).symm)
  set Qi := rightConjugate Q₁ (y ^ i) with hQi
  have hQiΔ : Qi ∈ gmsDelta L T := rightConjugate_mem_delta hQ₁ (pow_mem hy.mem_normalizer i)
  have hT₀N : ∀ k : ℕ, (y ^ k)⁻¹ ∈ normalizer (T₀ : Set G) := fun k =>
    inv_mem (Subgroup.centralizer_le_normalizer _
      (mem_centralizer_iff.mpr fun t ht => (Commute.pow_left (hy.commute ht) k).symm))
  have hQiT : Qi ≠ T₀ := by
    intro h1
    apply hQ₁T
    have := congrArg (fun X => rightConjugate X (y ^ i)⁻¹) h1
    simp only [hQi, rightConjugate_mul, mul_inv_cancel, rightConjugate_one] at this
    rw [this]
    exact (rightConjugate_eq_self_iff _ _).mpr (hT₀N i)
  set Q' := rightConjugate Qi x⁻¹ with hQ'
  have hQ'Δ : Q' ∈ gmsDelta L T := rightConjugate_mem_delta hQiΔ (inv_mem hxV)
  have hQ'T : Q' ≠ T₀ := by
    intro h1
    apply hQiT
    have := congrArg (fun X => rightConjugate X x) h1
    simp only [hQ', rightConjugate_mul, inv_mul_cancel, rightConjugate_one] at this
    rw [this]
    exact (rightConjugate_eq_self_iff _ _).mpr hxT₀N
  obtain ⟨j, hj⟩ := hy.exists_pow_eq h313 hX h hQ₁ hQ₁T hQ'Δ hQ'T
  refine ⟨j, fun w hw t ht hwt => ?_⟩
  have hyit : (y ^ i)⁻¹ * t * y ^ i = t := by
    rw [show (y ^ i)⁻¹ * t * y ^ i = (y ^ i)⁻¹ * (t * y ^ i) by group,
      ← (Commute.pow_left (hy.commute ht) i), inv_mul_cancel_left]
  have hyjt : (y ^ j)⁻¹ * t * y ^ j = t := by
    rw [show (y ^ j)⁻¹ * t * y ^ j = (y ^ j)⁻¹ * (t * y ^ j) by group,
      ← (Commute.pow_left (hy.commute ht) j), inv_mul_cancel_left]
  have hxt : x * t * x⁻¹ = t := by rw [hxT₀ t ht, mul_inv_cancel_right]
  have h1 : x * ((y ^ i)⁻¹ * (w * t) * y ^ i) * x⁻¹ ∈ Q' := by
    rw [hQ', mem_rightConjugate_iff, inv_inv]
    have : x⁻¹ * (x * ((y ^ i)⁻¹ * (w * t) * y ^ i) * x⁻¹) * x =
        (y ^ i)⁻¹ * (w * t) * y ^ i := by group
    rw [this, hQi, mem_rightConjugate_iff]
    simpa [mul_assoc] using hwt
  have h2 : (y ^ j)⁻¹ * (w * t) * y ^ j ∈ Q' := by
    rw [← hj, mem_rightConjugate_iff]
    simpa [mul_assoc] using hwt
  have hu : x * ((y ^ i)⁻¹ * w * y ^ i) * x⁻¹ ∈ gmsA L T := by
    have hA := h313.normalizer_le hxV
    exact (mem_normalizer_iff.mp hA _).mp
      ((mem_normalizer_iff.mp (inv_mem (pow_mem hy.mem_normalizer_gmsA i)) w).mp hw |>
        fun h' => by simpa using h')
  have hu' : (y ^ j)⁻¹ * w * y ^ j ∈ gmsA L T := by
    simpa using (mem_normalizer_iff.mp (inv_mem (pow_mem hy.mem_normalizer_gmsA j)) w).mp hw
  have e1 : x * ((y ^ i)⁻¹ * (w * t) * y ^ i) * x⁻¹ = (x * ((y ^ i)⁻¹ * w * y ^ i) * x⁻¹) * t := by
    calc x * ((y ^ i)⁻¹ * (w * t) * y ^ i) * x⁻¹
        = x * ((y ^ i)⁻¹ * w * y ^ i) * x⁻¹ * (x * ((y ^ i)⁻¹ * t * y ^ i) * x⁻¹) := by group
      _ = _ := by rw [hyit, hxt]
  have e2 : (y ^ j)⁻¹ * (w * t) * y ^ j = ((y ^ j)⁻¹ * w * y ^ j) * t := by
    calc (y ^ j)⁻¹ * (w * t) * y ^ j = ((y ^ j)⁻¹ * w * y ^ j) * ((y ^ j)⁻¹ * t * y ^ j) := by
          group
      _ = _ := by rw [hyjt]
  rw [e1] at h1
  rw [e2] at h2
  have h3 : (x * ((y ^ i)⁻¹ * w * y ^ i) * x⁻¹) * ((y ^ j)⁻¹ * w * y ^ j)⁻¹ ∈
      Q' ⊓ gmsA L T := by
    refine mem_inf.mpr ⟨?_, mul_mem hu (inv_mem hu')⟩
    have := mul_mem h1 (inv_mem h2)
    simpa [mul_assoc] using this
  rw [h313.inf_gmsA_eq_bot hQ'Δ, mem_bot, mul_inv_eq_one] at h3
  exact h3

theorem exists_aut_eq_of_prime
    (hy : IsTorus L T y) (h313 : Lemma313 L T q) (hX : Facts L T q) (h : Sec3 G L T)
    (hF : Foundation) (hp : (q - 1).Prime) {x : G} (hxV : x ∈ normalizer (gmsV L T : Set G))
    (hxT₀ : ∀ t ∈ T ⊓ centralizer (L : Set G), x * t = t * x) :
    ∃ e : ℕ, ∀ a ∈ gmsA L T, x * a * x⁻¹ = (y ^ e)⁻¹ * a * y ^ e := by
  classical
  set T₀ := T ⊓ centralizer (L : Set G) with hT₀def
  have hord := hy.orderOf_aut hX h
  obtain ⟨-, hVel, -, -, -⟩ := hX.vFacts h hF
  obtain ⟨h₀, -, hD, hDK⟩ := h.exists_conj hF
  obtain ⟨hDV, -⟩ := hX.exists_mul_mem h hF hD hDK
  set Q₁ := rightConjugate T₀ h₀ with hQ₁def
  have hQ₁ : Q₁ ∈ gmsDelta L T := ⟨⟨h₀, rfl⟩, hDV⟩
  have hQ₁T : Q₁ ≠ T₀ := by
    intro h1
    have h2 : T₀ ⊓ centralizer (L : Set G) = T₀ := inf_eq_left.mpr inf_le_right
    rw [h1, h2] at hDK
    exact h.T₀_ne_bot hDK
  have hQT₀ := h313.inf_eq_bot Q₁ hQ₁ T₀ mem_delta_T₀ hQ₁T
  have hcardQ₁ : 4 ≤ Nat.card Q₁ := by
    rw [card_of_mem_delta hQ₁]
    obtain ⟨E, hE, -, hE4⟩ := h.exists_four_le
    rw [← hE4]
    exact card_le_of_le hE
  obtain ⟨d₁, hd₁, hd₁1⟩ : ∃ d ∈ Q₁, d ≠ 1 := by
    have h1 : 1 < Nat.card Q₁ := by omega
    obtain ⟨⟨d, hd⟩, hd1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp
      ((Subgroup.one_lt_card_iff_ne_bot _).mp h1)
    exact ⟨d, hd, fun h1 => hd1 (Subtype.ext h1)⟩
  obtain ⟨d₂, hd₂, hd₂z⟩ : ∃ d ∈ Q₁, d ∉ zpowers d₁ := by
    by_contra hall
    push Not at hall
    have h1 := card_le_of_le (show Q₁ ≤ zpowers d₁ from hall)
    rw [Nat.card_zpowers, orderOf_eq_prime (hVel.2 d₁ (hQ₁.2 hd₁)) hd₁1] at h1
    omega
  have hd₂1 : d₂ ≠ 1 := fun h1 => hd₂z (h1 ▸ one_mem _)
  have hd₁₂ : d₂ ≠ d₁ := fun h1 => hd₂z (h1 ▸ mem_zpowers d₁)
  have hA₁N : gmsA L T ≤ normalizer (T₀ : Set G) := fun a ha =>
    (le_centralizer_iff.mp
      (show T₀ ≤ centralizer ((T ⊓ L : Subgroup G) : Set G) from
        fun t ht => mem_centralizer_iff.mpr fun x hx =>
          mem_centralizer_iff.mp (mem_inf.mp ht).2 x (mem_inf.mp hx).2)).trans
      (Subgroup.centralizer_le_normalizer _) (mem_inf.mp ha).1
  obtain ⟨w₁, hw₁, t₁, ht₁, hwt₁⟩ := CFSG.Goldschmidt.G37.mem_sup_of_le_normalizer hA₁N (hQ₁.2 hd₁)
  obtain ⟨w₂, hw₂, t₂, ht₂, hwt₂⟩ := CFSG.Goldschmidt.G37.mem_sup_of_le_normalizer hA₁N (hQ₁.2 hd₂)
  have hw₁1 : w₁ ≠ 1 := by
    intro h1
    rw [h1, one_mul] at hwt₁
    have : d₁ ∈ Q₁ ⊓ T₀ := mem_inf.mpr ⟨hd₁, hwt₁ ▸ ht₁⟩
    rw [hQT₀, mem_bot] at this
    exact hd₁1 this
  have hw₂1 : w₂ ≠ 1 := by
    intro h1
    rw [h1, one_mul] at hwt₂
    have : d₂ ∈ Q₁ ⊓ T₀ := mem_inf.mpr ⟨hd₂, hwt₂ ▸ ht₂⟩
    rw [hQT₀, mem_bot] at this
    exact hd₂1 this
  have hw₁₂ : w₁ ≠ w₂ := by
    intro h1
    apply hd₁₂
    have hw₂L : w₂ ∈ L := (mem_inf.mp (mem_inf.mp hw₂).1).2
    have htt : t₂ * t₁⁻¹ ∈ T₀ := mul_mem ht₂ (inv_mem ht₁)
    have hc : w₂ * (t₂ * t₁⁻¹) = t₂ * t₁⁻¹ * w₂ := mem_centralizer_iff.mp (mem_inf.mp htt).2 w₂ hw₂L
    have h2 : d₂ * d₁⁻¹ ∈ Q₁ ⊓ T₀ := by
      refine mem_inf.mpr ⟨mul_mem hd₂ (inv_mem hd₁), ?_⟩
      rw [← hwt₁, ← hwt₂, h1]
      have : w₂ * t₂ * (w₂ * t₁)⁻¹ = t₂ * t₁⁻¹ := by
        calc w₂ * t₂ * (w₂ * t₁)⁻¹ = w₂ * (t₂ * t₁⁻¹) * w₂⁻¹ := by group
          _ = t₂ * t₁⁻¹ := by rw [hc, mul_inv_cancel_right]
      rw [this]
      exact htt
    rw [hQT₀, mem_bot, mul_inv_eq_one] at h2
    exact h2
  obtain ⟨k, hk⟩ := hy.trans w₁ hw₁ w₂ hw₂ hw₁1 hw₂1
  have hkp : ¬ (q - 1) ∣ k := by
    intro hdvd
    have h1 : hy.aut ^ k = 1 := by
      rw [← orderOf_dvd_iff_pow_eq_one, hord]
      exact hdvd
    have h2 := hy.inv_conj_eq_of_aut_pow_eq (A := k) (B := 0) (by rw [h1, pow_zero]) hw₁
    rw [pow_zero, inv_one, one_mul, mul_one] at h2
    exact hw₁₂ (h2.symm.trans hk)
  choose σ hσ using fun i => hy.exists_conj_eq h313 hX h hQ₁ hQ₁T hxV hxT₀ i
  set e := σ 0 with he
  have hind : ∀ m : ℕ, hy.aut ^ σ (m * k) = hy.aut ^ (e + m * k) := by
    intro m
    induction m with
    | zero => simp [he]
    | succ m ih =>
      have hc : (y ^ (m * k))⁻¹ * w₂ * y ^ (m * k) =
          (y ^ ((m + 1) * k))⁻¹ * w₁ * y ^ ((m + 1) * k) := by
        rw [← hk]
        group
      have e1 := hσ (m * k) w₂ hw₂ t₂ ht₂ (hwt₂ ▸ hd₂)
      have e2 := hσ ((m + 1) * k) w₁ hw₁ t₁ ht₁ (hwt₁ ▸ hd₁)
      rw [hc] at e1
      rw [e1, hy.inv_conj_eq_of_aut_pow_eq ih hw₂, ← hk] at e2
      have e4 : (y ^ (e + (m + 1) * k))⁻¹ * w₁ * y ^ (e + (m + 1) * k) =
          (y ^ σ ((m + 1) * k))⁻¹ * w₁ * y ^ σ ((m + 1) * k) := by
        rw [← e2]
        group
      exact (hy.aut_pow_eq_of_inv_conj_eq hw₁ hw₁1 e4).symm
  have hF' : ∀ m : ℕ, x * ((y ^ (m * k))⁻¹ * w₁ * y ^ (m * k)) * x⁻¹ =
      (y ^ e)⁻¹ * ((y ^ (m * k))⁻¹ * w₁ * y ^ (m * k)) * y ^ e := by
    intro m
    rw [hσ (m * k) w₁ hw₁ t₁ ht₁ (hwt₁ ▸ hd₁), hy.inv_conj_eq_of_aut_pow_eq (hind m) hw₁]
    group
  have : Fact (q - 1).Prime := ⟨hp⟩
  refine ⟨e, fun a ha => ?_⟩
  by_cases ha1 : a = 1
  · rw [ha1]
    group
  obtain ⟨r, hr⟩ := hy.trans w₁ hw₁ a ha hw₁1 ha1
  have hk0 : (k : ZMod (q - 1)) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    exact hkp
  set m := ((r : ZMod (q - 1)) * (k : ZMod (q - 1))⁻¹).val with hm
  have hmk : hy.aut ^ (m * k) = hy.aut ^ r := by
    rw [pow_eq_pow_iff_modEq, hord, ← ZMod.natCast_eq_natCast_iff, Nat.cast_mul, hm,
      ZMod.natCast_zmod_val, mul_assoc, inv_mul_cancel₀ hk0, mul_one]
  rw [← hr, ← hy.inv_conj_eq_of_aut_pow_eq hmk hw₁]
  exact hF' m

end IsTorus

end Sec3

end CFSG.ComponentClassification.GMS78
