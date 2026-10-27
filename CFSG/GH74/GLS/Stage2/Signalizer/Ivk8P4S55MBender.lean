module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55MN1
public import CFSG.LocalAnalysis.ComponentClassification.Asc76BenderFactsBasic

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Subgroup CFSG CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.Asc76X
  CFSG.ComponentClassification.AschbacherToolkit.Bender CFSG.GH74.GLS.Stage2.Signalizer.Odd87

section Lemma

variable {L : Type} [Group L] [Finite L]

omit [Finite L] in
theorem eq_one_of_mem_two_of_mem_odd {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {P X : Subgroup L}
    (hP : IsPGroup 2 ↥P) (hX : IsPGroup p ↥X) {g : L} (hgP : g ∈ P) (hgX : g ∈ X) : g = 1 := by
  obtain ⟨a, ha⟩ := (IsPGroup.iff_orderOf.mp hX) ⟨g, hgX⟩
  obtain ⟨b, hb⟩ := (IsPGroup.iff_orderOf.mp hP) ⟨g, hgP⟩
  rw [Subgroup.orderOf_mk] at ha hb
  have h0 : a = 0 := by
    by_contra h
    have h1 : p ∣ orderOf g := by
      rw [ha]
      exact dvd_pow_self p h
    rw [hb] at h1
    exact hp2 ((Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) Nat.prime_two).1
      ((Fact.out : p.Prime).dvd_of_dvd_pow h1))
  rw [h0, pow_zero] at ha
  exact orderOf_eq_one_iff.1 ha

theorem mem_sylow_of_forall_commute
    (hL : CFSG.BenderSuzuki.IsBenderGroup L) (hZ : center L = ⊥) (P : Sylow 2 L) {g : L}
    (hg : ∀ s ∈ (P : Subgroup L), g * s = s * g) : g ∈ (P : Subgroup L) := by
  obtain ⟨c, hcP, -, hc⟩ := exists_eq_conj_of_forall_apply_eq hL P (MulAut.conj g) fun x hx => by
    rw [MulAut.conj_apply, hg x hx]
    group
  have hall : ∀ x : L, g * x * g⁻¹ = c * x * c⁻¹ := fun x => by
    have := congrArg (fun φ : MulAut L => φ x) hc
    simpa [MulAut.conj_apply] using this
  have hmem : g⁻¹ * c ∈ center L := by
    rw [Subgroup.mem_center_iff]
    intro x
    calc x * (g⁻¹ * c) = g⁻¹ * (g * x * g⁻¹) * c := by group
      _ = g⁻¹ * (c * x * c⁻¹) * c := by rw [hall x]
      _ = g⁻¹ * c * x := by group
  rw [hZ, Subgroup.mem_bot, inv_mul_eq_one] at hmem
  rw [hmem]
  exact hcP

theorem eq_bot_of_normalized_by_sylow [IsSimpleGroup L]
    {q k : ℕ} (hB : fusionBenderBorel L q k) (hq : 2 ≤ q) (hk : 2 ≤ k)
    (hL : CFSG.BenderSuzuki.IsBenderGroup L)
    (hcard : ∀ P : Sylow 2 L, Nat.card (Sylow 2 L) = Nat.card (P : Subgroup L) + 1)
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (P : Sylow 2 L) {X : Subgroup L} (hX : IsPGroup p ↥X)
    (hnorm : ∀ s ∈ (P : Subgroup L), ∀ x ∈ X, s * x * s⁻¹ ∈ X) : X = ⊥ := by
  have hZ : center L = ⊥ := center_eq_bot_of_fusionBenderBorel hB hq hk
  have hP2 : IsPGroup 2 ↥(P : Subgroup L) := P.isPGroup'
  have hPne : (P : Subgroup L) ≠ ⊥ := by
    intro h
    have h1 := (benderBorel_sylowCenter hB P).2.2.2
    rw [h, Subgroup.card_bot] at h1
    have : 1 < q ^ k := Nat.one_lt_pow (by omega) (by omega)
    omega
  have hXP : ∀ g, g ∈ X → g ∈ (P : Subgroup L) → g = 1 := fun g hgX hgP =>
    eq_one_of_mem_two_of_mem_odd hp2 hP2 hX hgP hgX
  have hPnorm : (P : Subgroup L) ≤ normalizer (X : Set L) := by
    intro s hs
    rw [Subgroup.mem_normalizer_iff]
    intro x
    refine ⟨fun hx => hnorm s hs x hx, fun hx => ?_⟩
    have h1 := hnorm s⁻¹ ((P : Subgroup L).inv_mem hs) _ hx
    have e : s⁻¹ * (s * x * s⁻¹) * s⁻¹⁻¹ = x := by group
    rw [e] at h1
    exact h1
  set H : Subgroup L := X ⊔ (P : Subgroup L) with hH
  by_cases hcase : ∃ T : Sylow 2 L, T ≠ P ∧ (T : Subgroup L) ≤ H
  ·
    obtain ⟨T, hTP, hTH⟩ := hcase
    have hall : ∀ S : Sylow 2 L, (S : Subgroup L) ≤ H := by
      intro S
      by_cases hSP : S = P
      · rw [hSP]
        exact le_sup_right
      · obtain ⟨r, hrP, hrT⟩ := exists_mem_smul_eq_of_fusionBenderBorel hB (hcard P) hTP hSP
        have hrH : r ∈ H := (le_sup_right : (P : Subgroup L) ≤ H) hrP
        rw [← hrT]
        exact Sylow.smul_le hTH ⟨r, hrH⟩
    have hN : normalClosure ((P : Subgroup L) : Set L) ≤ H := by
      rw [normalClosure, Subgroup.closure_le]
      intro x hx
      rw [Group.mem_conjugatesOfSet_iff] at hx
      obtain ⟨a, haP, hax⟩ := hx
      obtain ⟨c, hc⟩ := isConj_iff.1 hax
      refine hall (c • P) ?_
      rw [Sylow.coe_subgroup_smul]
      exact (Subgroup.mem_smul_pointwise_iff_exists _ _ _).2
        ⟨a, haP, by rw [MulAut.smul_def, MulAut.conj_apply]; exact hc⟩
    have hNtop : normalClosure ((P : Subgroup L) : Set L) = ⊤ := by
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
        (normalClosure ((P : Subgroup L) : Set L)) with h | h
      · exact absurd (eq_bot_iff.2 (h ▸ Subgroup.le_normalClosure)) hPne
      · exact h
    have hHtop : H = ⊤ := top_le_iff.1 (hNtop ▸ hN)
    have hXn : X.Normal := by
      refine Subgroup.normalizer_eq_top_iff.1 (top_le_iff.1 ?_)
      rw [← hHtop]
      exact sup_le (Subgroup.le_normalizer) hPnorm
    have := hXn
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal X with h | h
    · exact h
    · exfalso
      refine hPne (eq_bot_iff.2 fun g hg => ?_)
      exact Subgroup.mem_bot.2 (hXP g (h ▸ Subgroup.mem_top g) hg)
  ·
    push Not at hcase
    have hHnorm : ∀ h ∈ H, ∀ s ∈ (P : Subgroup L), h * s * h⁻¹ ∈ (P : Subgroup L) := by
      intro h hh s hs
      have hle : ((h • P : Sylow 2 L) : Subgroup L) ≤ H :=
        Sylow.smul_le (le_sup_right : (P : Subgroup L) ≤ H) ⟨h, hh⟩
      have heq : h • P = P := by
        by_contra hne
        exact hcase _ hne hle
      have hmem : h ∈ normalizer ((P : Subgroup L) : Set L) :=
        Sylow.smul_eq_iff_mem_normalizer.1 heq
      exact (Subgroup.mem_normalizer_iff.1 hmem s).1 hs
    have hcomm : ∀ x ∈ X, ∀ s ∈ (P : Subgroup L), x * s = s * x := by
      intro x hxX s hsP
      have hxH : x ∈ H := (le_sup_left : X ≤ H) hxX
      have h1 : x * s * x⁻¹ ∈ (P : Subgroup L) := hHnorm x hxH s hsP
      have h2 : x * s * x⁻¹ * s⁻¹ ∈ (P : Subgroup L) :=
        (P : Subgroup L).mul_mem h1 ((P : Subgroup L).inv_mem hsP)
      have h3 : x * s * x⁻¹ * s⁻¹ ∈ X := by
        have := X.mul_mem hxX (hnorm s hsP x⁻¹ (X.inv_mem hxX))
        simpa [mul_assoc] using this
      have h4 : x * s * x⁻¹ * s⁻¹ = 1 := hXP _ h3 h2
      exact mul_inv_eq_iff_eq_mul.1 (mul_inv_eq_one.1 h4)
    refine (Subgroup.eq_bot_iff_forall X).2 fun x hx => ?_
    exact hXP x hx (mem_sylow_of_forall_commute hL hZ P fun s hs => hcomm x hx s hs)

end Lemma

theorem exists_sylow_of_isSylowOf_top {Y : Type*} [Group Y] [Finite Y] {R : Subgroup Y}
    (hR : IsSylowOf 2 R ⊤) : ∃ S : Sylow 2 Y, (S : Subgroup Y) = R := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := hR.card_eq
  rw [Subgroup.card_top] at h
  exact ⟨Sylow.ofCard R h, Sylow.coe_ofCard _ _⟩

theorem mem_innSub_of_pow_coprime {Y : Type} [Group Y] {φ : MulAut Y} {n : ℕ} (hφ : φ ^ n = 1)
    (hcop : Nat.Coprime n (Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer Y))) :
    φ ∈ innSub Y := by
  open CFSG.ComponentClassification.OuterAutomorphisms in
  have h1 : (QuotientGroup.mk φ : Outer Y) ^ n = 1 := by
    rw [← QuotientGroup.mk_pow, hφ, QuotientGroup.mk_one]
  open CFSG.ComponentClassification.OuterAutomorphisms in
  have h2 : orderOf (QuotientGroup.mk φ : Outer Y) ∣ n := orderOf_dvd_of_pow_eq_one h1
  open CFSG.ComponentClassification.OuterAutomorphisms in
  have h3 : orderOf (QuotientGroup.mk φ : Outer Y) ∣ Nat.card (Outer Y) := orderOf_dvd_natCard _
  open CFSG.ComponentClassification.OuterAutomorphisms in
  have h4 : orderOf (QuotientGroup.mk φ : Outer Y) = 1 :=
    Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left h2 hcop) h3
  rw [orderOf_eq_one_iff, QuotientGroup.eq_one_iff] at h4
  exact h4

theorem noN1_of_bender_inner {Y : Type} [Group Y] [Finite Y]
    [IsSimpleGroup Y] {q k : ℕ} (hB : fusionBenderBorel Y q k) (hq : 2 ≤ q) (hk : 2 ≤ k)
    (hL : CFSG.BenderSuzuki.IsBenderGroup Y)
    (hcard : ∀ P : Sylow 2 Y, Nat.card (Sylow 2 Y) = Nat.card (P : Subgroup Y) + 1)
    {b : MulAut Y} (hb : b ∈ innSub Y) {p : ℕ} {R₀ : Subgroup Y} : ¬ N1Config Y p b R₀ := by
  intro h
  have hZ : center Y = ⊥ := center_eq_bot_of_fusionBenderBorel hB hq hk
  obtain ⟨P, W, hP, hWp, hWne, hPW⟩ := pCfg_of_n1_of_mem_inner hZ hb h
  obtain ⟨hp, hp2, -⟩ := h
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨S, hS⟩ := exists_sylow_of_isSylowOf_top hP
  refine hWne (eq_bot_of_normalized_by_sylow hB hq hk hL hcard hp2 S hWp ?_)
  intro s hs x hx
  rw [hS] at hs
  exact (Subgroup.mem_normalizer_iff.1 (hPW hs) x).1 hx

theorem aut_mul_conj_mul_inv {Y : Type*} [Group Y] (b : MulAut Y) (y : Y) :
    b * MulAut.conj y * b⁻¹ = MulAut.conj (b y) := by
  ext z
  simp [MulAut.conj_apply]

theorem noN1_of_bender_coprime {Y : Type} [Group Y] [Finite Y]
    (hL : CFSG.BenderSuzuki.IsBenderGroup Y) (hZ : center Y = ⊥) {p : ℕ} {b : MulAut Y}
    {R₀ : Subgroup Y} (hp : ¬ p ∣ Nat.card Y) : ¬ N1Config Y p b R₀ := by
  intro h
  obtain ⟨hpp, hp2, hbo, hR, hX⟩ := h
  have : Fact p.Prime := ⟨hpp⟩
  have hinj : Function.Injective (MulAut.conj : Y →* MulAut Y) :=
    conj_injective_of_center_bot hZ
  set X : Subgroup (MulAut Y) := closure {c' : MulAut Y | ∃ r ∈ R₀,
    c' = MulAut.conj r * b * (MulAut.conj r)⁻¹} with hXdef
  have hbX : b ∈ X := Subgroup.subset_closure ⟨1, one_mem _, by simp⟩
  have hfix : ∀ r ∈ R₀, b r = r := by
    intro r hr
    have hgen : MulAut.conj r * b * (MulAut.conj r)⁻¹ ∈ X := Subgroup.subset_closure ⟨r, hr, rfl⟩
    have hu : MulAut.conj r * b * (MulAut.conj r)⁻¹ * b⁻¹ ∈ X := X.mul_mem hgen (X.inv_mem hbX)
    have hueq : MulAut.conj r * b * (MulAut.conj r)⁻¹ * b⁻¹ = MulAut.conj (r * b r⁻¹) := by
      have h1 := aut_mul_conj_mul_inv b r⁻¹
      calc MulAut.conj r * b * (MulAut.conj r)⁻¹ * b⁻¹
          = MulAut.conj r * (b * MulAut.conj r⁻¹ * b⁻¹) := by rw [map_inv]; group
        _ = MulAut.conj r * MulAut.conj (b r⁻¹) := by rw [h1]
        _ = MulAut.conj (r * b r⁻¹) := (map_mul _ _ _).symm
    obtain ⟨n, hn⟩ := (IsPGroup.iff_orderOf.mp hX) ⟨_, hu⟩
    rw [Subgroup.orderOf_mk, hueq] at hn
    have hord : orderOf (MulAut.conj (r * b r⁻¹)) = orderOf (r * b r⁻¹) :=
      orderOf_injective _ hinj _
    have hdvd : orderOf (r * b r⁻¹) ∣ Nat.card Y := orderOf_dvd_natCard _
    rw [hord] at hn
    have hn0 : n = 0 := by
      by_contra hn0
      rw [hn] at hdvd
      exact hp ((dvd_pow_self p hn0).trans hdvd)
    rw [hn0, pow_zero, orderOf_eq_one_iff] at hn
    rw [map_inv] at hn
    exact (mul_inv_eq_one.1 hn).symm
  obtain ⟨S, hS⟩ := exists_sylow_of_isSylowOf_top hR
  obtain ⟨c, -, -, hc⟩ := exists_eq_conj_of_forall_apply_eq hL S b fun x hx =>
    hfix x (hS ▸ hx)
  have hord : orderOf b = orderOf c := by
    rw [hc]
    exact orderOf_injective _ hinj _
  apply hp
  rw [← hbo, hord]
  exact orderOf_dvd_natCard c

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
