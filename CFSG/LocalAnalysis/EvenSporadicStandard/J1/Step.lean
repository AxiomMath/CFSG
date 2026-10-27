module

public import CFSG.LocalAnalysis.EvenSporadicStandard.J1.Sigma
public import CFSG.LocalAnalysis.EvenSporadicStandard.J1.Stage
public import CFSG.LocalAnalysis.EvenSporadicStandard.J1.Fusion

public section

namespace CFSG.EvenSporadicStandard.J1Std

open Subgroup

variable {G : Type} [Group G] [Finite G]

theorem cosets_exhaust {A : Type*} [Group A] [Finite A] (hA : ∀ a b : A, a * b = b * a)
    (σ : MulAut A) (hσ : σ ^ 7 = 1) (hfree : ∀ a : A, σ a = a → a = 1)
    (hcard : Nat.card {a : A // a * a = 1} = 8) {l₀ : A} (hl₀ : ¬ ∃ m : A, l₀ = m * m) :
    ∀ l : A, (∃ m : A, l = m * m) ∨ ∃ (i : ℕ) (m : A), l = (σ ^ i) l₀ * (m * m) := by
  classical
  let sq : A →* A := MonoidHom.mk' (fun a => a * a) fun a b => by
    calc a * b * (a * b) = a * (b * a) * b := by group
      _ = a * (a * b) * b := by rw [hA b a]
      _ = a * a * (b * b) := by group
  let P : Subgroup A := sq.range
  have hPmem : ∀ a, a ∈ P ↔ ∃ m, a = m * m := by
    intro a
    constructor
    · rintro ⟨m, rfl⟩
      exact ⟨m, rfl⟩
    · rintro ⟨m, rfl⟩
      exact ⟨m, rfl⟩
  have hPn : P.Normal :=
    ⟨fun n hn g => by rw [hA g n, mul_assoc, mul_inv_cancel, mul_one]; exact hn⟩
  have hker : Nat.card sq.ker = 8 := by
    rw [← hcard]
    exact Nat.card_congr (Equiv.subtypeEquivRight fun a => by simp [sq])
  have hindex : P.index = 8 := by
    have h1 := Subgroup.card_ker_mul_card_range sq
    have h2 := Subgroup.index_mul_card (H := P)
    have hpos : 0 < Nat.card P := Nat.card_pos
    rw [hker] at h1
    have : P.index * Nat.card P = 8 * Nat.card P := by rw [h2, ← h1]
    exact Nat.eq_of_mul_eq_mul_right hpos this
  have hcardQ : Nat.card (A ⧸ P) = 8 := by rw [← Subgroup.index_eq_card, hindex]
  have hσP : P.map σ.toMonoidHom = P := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      obtain ⟨m, rfl⟩ := (hPmem y).1 hy
      exact (hPmem _).2 ⟨σ m, by simp⟩
    · intro hx
      obtain ⟨m, rfl⟩ := (hPmem x).1 hx
      exact ⟨σ.symm m * σ.symm m, (hPmem _).2 ⟨_, rfl⟩, by simp⟩
  let σ' : MulAut (A ⧸ P) := QuotientGroup.congr P P σ hσP
  have hσ'mk : ∀ a : A, σ' (a : A ⧸ P) = ((σ a : A) : A ⧸ P) := fun a => rfl
  have hpow : ∀ (n : ℕ) (a : A), (σ' ^ n) (a : A ⧸ P) = (((σ ^ n) a : A) : A ⧸ P) := by
    intro n
    induction n with
    | zero => intro a; rfl
    | succ n ih =>
      intro a
      rw [pow_succ', MulAut.mul_apply, ih, hσ'mk, pow_succ', MulAut.mul_apply]
  have hσ'7 : σ' ^ 7 = 1 := by
    ext q
    induction q using QuotientGroup.induction_on with
    | H a =>
      rw [hpow, hσ]
      rfl
  have hfree' : ∀ q : A ⧸ P, q ≠ 1 → σ' q ≠ q := by
    intro q hq hfix
    induction q using QuotientGroup.induction_on with
    | H a =>
      rw [hσ'mk, QuotientGroup.eq] at hfix
      have ha : ∃ b : A, σ a * a⁻¹ = b * b := by
        obtain ⟨b, hb⟩ := (hPmem _).1 hfix
        refine ⟨b⁻¹, ?_⟩
        have h2 : σ a * a⁻¹ = ((σ a)⁻¹ * a)⁻¹ := by
          rw [mul_inv_rev, inv_inv, hA]
        rw [h2, hb]
        simp [mul_inv_rev]
      obtain ⟨c, hc⟩ := mem_sq_of_sigma_fixed hA σ hσ hfree ha
      exact hq ((QuotientGroup.eq_one_iff a).2 ((hPmem a).2 ⟨c, hc⟩))
  have hne : σ' ≠ 1 := by
    intro h1
    have : ∃ q : A ⧸ P, q ≠ 1 := by
      by_contra hcon
      push Not at hcon
      have : Nat.card (A ⧸ P) = 1 := by
        rw [Nat.card_eq_one_iff_unique]
        exact ⟨⟨fun a b => (hcon a).trans (hcon b).symm⟩, ⟨1⟩⟩
      omega
    obtain ⟨q, hq⟩ := this
    exact hfree' q hq (by rw [h1]; rfl)
  have : Fact (Nat.Prime 7) := ⟨Nat.prime_seven⟩
  have hord : orderOf σ' = 7 := orderOf_eq_prime hσ'7 hne
  obtain ⟨-, htrans⟩ := orbit_of_prime_order hcardQ σ' hord
  intro l
  by_cases hl : (l : A ⧸ P) = 1
  · left
    exact (hPmem l).1 ((QuotientGroup.eq_one_iff l).1 hl)
  · right
    have hl₀' : (l₀ : A ⧸ P) ≠ 1 := fun h =>
      hl₀ ((hPmem l₀).1 ((QuotientGroup.eq_one_iff l₀).1 h))
    obtain ⟨i, hi⟩ := htrans _ _ hl₀' hl
    rw [hpow] at hi
    obtain ⟨m, hm⟩ := (hPmem _).1 (QuotientGroup.eq.1 hi)
    refine ⟨i, m, ?_⟩
    calc l = (σ ^ i) l₀ * (((σ ^ i) l₀)⁻¹ * l) := by group
      _ = (σ ^ i) l₀ * (m * m) := by rw [← hm]

theorem coset_fixed_of_small_index {R : Type*} [Group R] [Finite R] {S : Subgroup R}
    (hidx : S.index ≤ 6) (σ : MulAut R) (hσ : σ ^ 7 = 1) (hS : S.map σ.toMonoidHom = S) (r : R) :
    σ r * r⁻¹ ∈ S := by
  classical
  have hSσ : ∀ x, x ∈ S → σ x ∈ S := fun x hx => by
    rw [← hS]
    exact Subgroup.mem_map_of_mem _ hx
  have : Fintype R := Fintype.ofFinite R
  let f : Function.End (R ⧸ S) := Quotient.map' σ fun a b hab => by
    rw [QuotientGroup.leftRel_apply] at hab ⊢
    have := hSσ _ hab
    simpa using this
  have hf1 : ∀ a : R, f (a : R ⧸ S) = ((σ a : R) : R ⧸ S) := fun a => rfl
  have hf : ∀ (n : ℕ) (a : R), (f ^ n) (a : R ⧸ S) = (((σ ^ n) a : R) : R ⧸ S) := by
    intro n
    induction n with
    | zero => intro a; rfl
    | succ n ih =>
      intro a
      have : (f ^ (n + 1)) (a : R ⧸ S) = (f ^ n) (f (a : R ⧸ S)) := by
        rw [pow_succ]; rfl
      rw [this, hf1, ih, pow_succ, MulAut.mul_apply]
  have hf7 : f ^ 7 ^ 1 = 1 := by
    have : ∀ x : R ⧸ S, (f ^ 7 ^ 1) x = x := by
      intro x
      induction x using Quotient.inductionOn' with
      | h a =>
        have := hf (7 ^ 1) a
        rw [pow_one] at this ⊢
        rw [hσ] at this
        exact this
    exact funext this
  have : Fact (Nat.Prime 7) := ⟨Nat.prime_seven⟩
  have hmod := Equiv.Perm.card_fixedPoints_modEq (p := 7) (n := 1) (α := R ⧸ S) hf7
  have hcard : Fintype.card (R ⧸ S) = S.index := by
    rw [Subgroup.index_eq_card, Nat.card_eq_fintype_card]
  have hle : Fintype.card f.fixedPoints ≤ Fintype.card (R ⧸ S) := Fintype.card_subtype_le _
  have heq : Fintype.card f.fixedPoints = Fintype.card (R ⧸ S) :=
    Nat.ModEq.eq_of_lt_of_lt hmod.symm (by omega) (by omega)
  have hall : ∀ x : R ⧸ S, f x = x := by
    intro x
    have h1 : (Set.toFinset f.fixedPoints).card = Fintype.card (R ⧸ S) := by
      rw [Set.toFinset_card, heq]
    have h2 := Finset.eq_univ_of_card _ h1
    have : x ∈ Set.toFinset f.fixedPoints := by rw [h2]; exact Finset.mem_univ x
    have h4 : x ∈ f.fixedPoints := Set.mem_toFinset.1 this
    exact h4
  have h3 := hall ((r⁻¹ : R) : R ⧸ S)
  rw [hf1, QuotientGroup.eq] at h3
  simpa using h3

omit [Finite G] in
theorem card_eq_card_conj_mul {M : Subgroup G} (z : G) :
    Nat.card M = Nat.card {x : G // ∃ m ∈ M, x = m * z * m⁻¹} *
      Nat.card ↥(centralizer ({z} : Set G) ⊓ M) := by
  have h1 := Subgroup.relIndex_mul_card (H := centralizer ({z} : Set G)) (K := M)
  have key : (centralizer ({z} : Set G)).relIndex M =
      Nat.card {x : G // ∃ m ∈ M, x = m * z * m⁻¹} := by
    rw [← MulAction.stabilizer_comap_conj_eq_centralizer_singleton, Subgroup.relIndex_comap,
      Subgroup.relIndex, MulAction.stabilizer_subgroupOf, MulAction.index_stabilizer,
      ← Nat.card_coe_set_eq]
    apply Nat.card_congr
    refine Equiv.subtypeEquivRight fun x => ?_
    simp only [MulAction.mem_orbit_iff, Subtype.exists, Subgroup.mem_map]
    constructor
    · rintro ⟨a, ⟨m, hm, rfl⟩, hx⟩
      exact ⟨m, hm, by rw [← hx]; rfl⟩
    · rintro ⟨m, hm, rfl⟩
      exact ⟨MulAut.conj m, ⟨m, hm, rfl⟩, rfl⟩
  rw [key] at h1
  exact h1.symm

omit [Finite G] in
theorem normalizerMonoidHom_pow_apply {K : Subgroup G} {σ : G} (hσ : σ ∈ normalizer (K : Set G))
    (i : ℕ) (a : K) :
    ((K.normalizerMonoidHom ⟨σ, hσ⟩ ^ i) a : G) = σ ^ i * a * (σ ^ i)⁻¹ := by
  rw [← map_pow]
  rfl

namespace Stage

variable {H : Setting G} {S Λ : Subgroup G} (h : Stage H S Λ)

include h in
theorem mul_z_eq {m : G} (hm : m ∈ Λ) : m * H.z = H.z * m⁻¹ := by
  have h1 := h.z_inv (inv_mem hm)
  rw [inv_inv] at h1
  calc m * H.z = (H.z * m⁻¹ * H.z) * H.z := by rw [h1]
    _ = H.z * m⁻¹ * (H.z * H.z) := by group
    _ = H.z * m⁻¹ := by rw [H.z_mul_self, mul_one]

include h in
theorem conj_Λ_zl {s l : G} (hs : s ∈ Λ) :
    s * (H.z * l) * s⁻¹ = H.z * (s⁻¹ * l * s⁻¹) :=
  calc s * (H.z * l) * s⁻¹ = (s * H.z) * l * s⁻¹ := by group
    _ = (H.z * s⁻¹) * l * s⁻¹ := by rw [h.mul_z_eq hs]
    _ = H.z * (s⁻¹ * l * s⁻¹) := by group

include h in
theorem conj_zl {s l : G} (hs : s ∈ S) (hl : l ∈ Λ) :
    ∃ m ∈ Λ, s * (H.z * l) * s⁻¹ = H.z * l * (m * m) := by
  rcases h.cover s hs with hsΛ | hsz
  · refine ⟨s⁻¹, inv_mem hsΛ, ?_⟩
    rw [h.conj_Λ_zl hsΛ, h.comm (inv_mem hsΛ) hl]
    group
  · obtain ⟨t, htΛ, rfl⟩ : ∃ t ∈ Λ, s = t * H.z :=
      ⟨s * H.z, hsz, by rw [mul_assoc, H.z_mul_self, mul_one]⟩
    refine ⟨l⁻¹ * t⁻¹, mul_mem (inv_mem hl) (inv_mem htΛ), ?_⟩
    have e1 : (t * H.z)⁻¹ = H.z * t⁻¹ := by rw [mul_inv_rev, H.z_inv]
    have e2 : (t * l * t) * H.z = H.z * (t * l * t)⁻¹ :=
      h.mul_z_eq (mul_mem (mul_mem htΛ hl) htΛ)
    calc t * H.z * (H.z * l) * (t * H.z)⁻¹ = t * (H.z * H.z) * l * (H.z * t⁻¹) := by
          rw [e1]; group
      _ = t * l * (H.z * t⁻¹) := by rw [H.z_mul_self, mul_one]
      _ = t * l * (t * H.z) := by rw [h.mul_z_eq htΛ]
      _ = (t * l * t) * H.z := by group
      _ = H.z * (t * l * t)⁻¹ := e2
      _ = H.z * l * (l⁻¹ * t⁻¹ * (l⁻¹ * t⁻¹)) := by group

include h in
theorem sq_conj_zl {l m : G} (hl : l ∈ Λ) (hm : m ∈ Λ) :
    ∃ s ∈ S, s * (H.z * l) * s⁻¹ = H.z * l * (m * m) := by
  refine ⟨m⁻¹, h.le (inv_mem hm), ?_⟩
  rw [h.conj_Λ_zl (inv_mem hm), inv_inv, h.comm hm hl]
  group

include h in
theorem z_mul_mem_Λ {x : G} (hx : x ∈ S) (hxΛ : x ∉ Λ) : H.z * x ∈ Λ := by
  have := h.mul_inv_mem_Λ h.z_mem h.z_not_mem hx hxΛ
  rwa [H.z_inv] at this

include h in
theorem N_conj_z_mem {n : G} (hn : n ∈ normalizer (S : Set G)) :
    n * H.z * n⁻¹ ∈ S ∧ n * H.z * n⁻¹ ∉ Λ :=
  h.N_conj_mem hn h.z_mem h.z_not_mem

include h in
theorem exists_move (hS : 2 ∣ S.index) :
    ∃ n ∈ normalizer (S : Set G), ∀ s ∈ S, n * H.z * n⁻¹ ≠ s * H.z * s⁻¹ := by
  by_contra hcon
  push Not at hcon
  refine not_two_dvd_index_of_invariant h.pgroup (fun P hP hPC hVP => ?_) hcon hS
  rw [h.centralizer_S] at hVP
  have := Subgroup.eq_of_le_of_card_ge hVP (by rw [H.card_V]; exact (H.star hP hPC).1)
  rw [← this]
  exact h.V_le

include h in
theorem exists_sigma_aut {σ : G} (hσ : σ ∈ H.NL) (h7 : orderOf σ = 7) :
    ∃ φ : MulAut Λ, φ ^ 7 = 1 ∧ (∀ a : Λ, φ a = a → a = 1) ∧
      ∀ (i : ℕ) (a : Λ), ((φ ^ i) a : G) = σ ^ i * a * (σ ^ i)⁻¹ := by
  have hσΛ : σ ∈ normalizer (Λ : Set G) := h.B_Λ (H.NL_le_B hσ)
  have hpow := normalizerMonoidHom_pow_apply hσΛ
  have hσ7 : σ ^ 7 = 1 := by rw [← h7]; exact pow_orderOf_eq_one σ
  refine ⟨Λ.normalizerMonoidHom ⟨σ, hσΛ⟩, ?_, ?_, hpow⟩
  · ext a
    have := hpow 7 a
    rw [hσ7] at this
    simpa using this
  · intro a ha
    by_contra hne
    obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.1 h.pgroup ⟨a.1, h.le a.2⟩
    rw [Subgroup.orderOf_mk] at hk
    have hk1 : k ≠ 0 := by
      rintro rfl
      exact hne (Subtype.ext (orderOf_eq_one_iff.1 hk))
    have hbΛ : a.1 ^ (2 ^ (k - 1)) ∈ Λ := Subgroup.pow_mem Λ a.2 _
    have hbsq : a.1 ^ (2 ^ (k - 1)) * a.1 ^ (2 ^ (k - 1)) = 1 := by
      rw [← pow_add, ← two_mul, ← pow_succ', Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.2 hk1),
        ← hk]
      exact pow_orderOf_eq_one _
    have hb1 : a.1 ^ (2 ^ (k - 1)) ≠ 1 := by
      refine pow_ne_one_of_lt_orderOf (by positivity) ?_
      rw [hk]
      exact Nat.pow_lt_pow_right (by norm_num) (by omega)
    have hσb : σ * a.1 ^ (2 ^ (k - 1)) * σ⁻¹ = a.1 ^ (2 ^ (k - 1)) := by
      have : σ * a.1 * σ⁻¹ = a.1 := congrArg Subtype.val ha
      rw [← conj_pow, this]
    exact (H.sigma_orbit hσ h7).1 _ (h.mem_E_of_sq hbΛ hbsq) hb1 hσb

include h in
theorem card_sq_eq_one : Nat.card {a : Λ // a * a = 1} = 8 := by
  rw [← H.card_E]
  refine Nat.card_congr ⟨fun a => ⟨a.1.1, h.mem_E_of_sq a.1.2 (congrArg Subtype.val a.2)⟩,
    fun e => ⟨⟨e.1, h.E_le e.2⟩, Subtype.ext (H.sq_E e.1 e.2)⟩, fun a => rfl, fun e => rfl⟩

include h in
theorem conj_N_eq (hS : 2 ∣ S.index) {x : G} (hx : x ∈ S) (hxΛ : x ∉ Λ) :
    ∃ n ∈ normalizer (S : Set G), x = n * H.z * n⁻¹ := by
  obtain ⟨n₀, hn₀, hmove⟩ := h.exists_move hS
  obtain ⟨hx₀S, hx₀Λ⟩ := h.N_conj_z_mem hn₀
  obtain ⟨σ, hσ, h7⟩ := H.exists_sigma
  have hσN : σ ∈ normalizer (S : Set G) := h.B_S (H.NL_le_B hσ)
  have hσz : σ * H.z = H.z * σ := H.comm_z (H.mem_NL_iff.1 hσ).1
  obtain ⟨φ, hφ7, hφfree, hφpow⟩ := h.exists_sigma_aut hσ h7
  have hz2 : ∀ i : ℕ, σ ^ i * H.z = H.z * σ ^ i := fun i => Commute.pow_left hσz i
  have hl₀Λ : H.z * (n₀ * H.z * n₀⁻¹) ∈ Λ := h.z_mul_mem_Λ hx₀S hx₀Λ
  have hl₀sq : ¬ ∃ m : Λ, (⟨_, hl₀Λ⟩ : Λ) = m * m := by
    rintro ⟨m, hm⟩
    obtain ⟨s, hs, hseq⟩ := h.sq_conj_zl (one_mem Λ) m.2
    apply hmove s hs
    have : H.z * (n₀ * H.z * n₀⁻¹) = m.1 * m.1 := congrArg Subtype.val hm
    calc n₀ * H.z * n₀⁻¹ = H.z * (H.z * (n₀ * H.z * n₀⁻¹)) := by
          rw [← mul_assoc, H.z_mul_self, one_mul]
      _ = H.z * (m.1 * m.1) := by rw [this]
      _ = s * H.z * s⁻¹ := by simpa using hseq.symm
  have key : ∀ l ∈ Λ, ∃ n ∈ normalizer (S : Set G), H.z * l = n * H.z * n⁻¹ := by
    intro l hl
    rcases cosets_exhaust (fun a b => Subtype.ext (h.comm a.2 b.2)) φ hφ7 hφfree
      h.card_sq_eq_one hl₀sq ⟨l, hl⟩ with ⟨m, hm⟩ | ⟨i, m, hm⟩
    · obtain ⟨s, hs, hseq⟩ := h.sq_conj_zl (one_mem Λ) m.2
      refine ⟨s, le_normalizer hs, ?_⟩
      have : l = m.1 * m.1 := congrArg Subtype.val hm
      rw [this]
      simpa using hseq.symm
    · set L' : Λ := (φ ^ i) ⟨_, hl₀Λ⟩ with hL'
      have hL'val : (L' : G) = σ ^ i * (H.z * (n₀ * H.z * n₀⁻¹)) * (σ ^ i)⁻¹ := hφpow i _
      have hlval : l = (L' : G) * (m.1 * m.1) := congrArg Subtype.val hm
      obtain ⟨s, hs, hseq⟩ := h.sq_conj_zl L'.2 m.2
      have hzL : H.z * (L' : G) = (σ ^ i * n₀) * H.z * (σ ^ i * n₀)⁻¹ := by
        rw [hL'val]
        have hc := hz2 i
        calc H.z * (σ ^ i * (H.z * (n₀ * H.z * n₀⁻¹)) * (σ ^ i)⁻¹)
            = (H.z * σ ^ i) * (H.z * (n₀ * H.z * n₀⁻¹)) * (σ ^ i)⁻¹ := by group
          _ = (σ ^ i * H.z) * (H.z * (n₀ * H.z * n₀⁻¹)) * (σ ^ i)⁻¹ := by rw [hc]
          _ = σ ^ i * (H.z * H.z) * (n₀ * H.z * n₀⁻¹) * (σ ^ i)⁻¹ := by group
          _ = (σ ^ i * n₀) * H.z * (σ ^ i * n₀)⁻¹ := by rw [H.z_mul_self]; group
      refine ⟨s * (σ ^ i * n₀), mul_mem (le_normalizer hs) (mul_mem (pow_mem hσN i) hn₀), ?_⟩
      calc H.z * l = H.z * (L' : G) * (m.1 * m.1) := by rw [hlval, mul_assoc]
        _ = s * (H.z * (L' : G)) * s⁻¹ := hseq.symm
        _ = s * ((σ ^ i * n₀) * H.z * (σ ^ i * n₀)⁻¹) * s⁻¹ := by rw [hzL]
        _ = s * (σ ^ i * n₀) * H.z * (s * (σ ^ i * n₀))⁻¹ := by group
  obtain ⟨n, hn, hnx⟩ := key (H.z * x) (h.z_mul_mem_Λ hx hxΛ)
  exact ⟨n, hn, by rw [← hnx, ← mul_assoc, H.z_mul_self, one_mul]⟩

include h in
theorem centralizer_N : centralizer ({H.z} : Set G) ⊓ normalizer (S : Set G) = H.B := by
  refine le_antisymm (fun n ⟨hnC, hnN⟩ => ?_) (le_inf H.B_le_centralizer h.B_S)
  refine H.mem_B_def.2 ⟨mem_normalizer_iff.2 fun v => ?_, hnC⟩
  rw [← h.centralizer_S]
  have hC := mem_normalizer_iff.1 (le_normalizer hnC : n ∈ normalizer
    ((centralizer ({H.z} : Set G) : Subgroup G) : Set G)) v
  have hN := mem_normalizer_iff.1 hnN v
  exact and_congr hC hN

include h in
theorem card_N (hS : 2 ∣ S.index) :
    Nat.card (normalizer (S : Set G) : Subgroup G) = 336 * Nat.card Λ := by
  have h1 := card_eq_card_conj_mul (M := (normalizer (S : Set G) : Subgroup G)) H.z
  rw [h.centralizer_N, H.card_B] at h1
  have h2 : Nat.card {x : G // ∃ m ∈ (normalizer (S : Set G) : Subgroup G),
      x = m * H.z * m⁻¹} = Nat.card Λ := by
    refine Nat.card_congr ⟨fun x => ⟨H.z * x.1, ?_⟩, fun l => ⟨H.z * l.1, ?_⟩, ?_, ?_⟩
    · obtain ⟨m, hm, hx⟩ := x.2
      obtain ⟨hS', hΛ'⟩ := h.N_conj_z_mem hm
      rw [hx]
      exact h.z_mul_mem_Λ hS' hΛ'
    · obtain ⟨hzS, hzΛ⟩ := h.z_mul_mem l.2
      exact h.conj_N_eq hS hzS hzΛ
    · intro x
      apply Subtype.ext
      show H.z * (H.z * x.1) = x.1
      rw [← mul_assoc, H.z_mul_self, one_mul]
    · intro l
      apply Subtype.ext
      show H.z * (H.z * l.1) = l.1
      rw [← mul_assoc, H.z_mul_self, one_mul]
  rw [h2] at h1
  rw [h1, mul_comm]

end Stage

end CFSG.EvenSporadicStandard.J1Std
