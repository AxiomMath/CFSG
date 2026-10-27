module

public import CFSG.GH74.GLS.C3.Prop121.FinCent
public import CFSG.GH74.GLS.C3.Prop121.CentKFin
public import CFSG.GH74.GLS.C3.Prop121.Coord
public import CFSG.GH74.GLS.C3.Prop121.FnFacts
public import CFSG.GH74.GLS.C3.Prop121.MooreBasic
public import CFSG.GH74.GLS.C3.Prop121.TU

public section

namespace CFSG.GH74.GLS.C3.Prop121

open Subgroup Equiv Perm CFSG.GH74.GLS CFSG.GH74.GLS.C3.Layer2.Model

section Config

variable {G : Type} [Group G] [Finite G] {n : ℕ} {x : G} {K T Q S : Subgroup G} {a : G}

omit [Finite G] in
theorem Q_facts {t u g : G} (hS : Stage3Loc n x K Q t u g) :
    ∃ y₀ ∈ Q, y₀ ≠ 1 ∧ y₀ ≠ x ∧ (∀ q ∈ Q, q = 1 ∨ q = x ∨ q = y₀ ∨ q = x * y₀) ∧
      y₀ * y₀ = 1 ∧ x * x = 1 ∧ x * y₀ = y₀ * x ∧ t * t * t = 1 ∧ t ≠ 1 ∧
      (t * x * t⁻¹ = y₀ ∨ t * x * t⁻¹ = x * y₀) ∧
      (t * y₀ * t⁻¹ = x ∨ t * y₀ * t⁻¹ = y₀ ∨ t * y₀ * t⁻¹ = x * y₀) ∧ t * x * t⁻¹ ≠ x := by
  obtain ⟨y₀, hy₀Q, hy₀1, hy₀x⟩ := TU.exists_y hS.Q_card (x := x)
  have hQall := TU.Q_four hS.Q_card hS.Q_sq hS.x_mem hy₀Q hS.x_ne hy₀1 hy₀x
  have hx2 : x * x = 1 := by rw [← sq]; exact hS.x_sq
  have hy2 : y₀ * y₀ = 1 := by rw [← sq]; exact hS.Q_sq y₀ hy₀Q
  have hxy : x * y₀ = y₀ * x := hS.Q_comm x hS.x_mem y₀ hy₀Q
  have ht3 : t ^ 3 = 1 := by
    have := pow_orderOf_eq_one t
    rwa [hS.t_order] at this
  have ht3' : t * t * t = 1 := (pow_three' t).symm.trans ht3
  have ht1 : t ≠ 1 := by
    intro h1
    have := hS.t_order
    rw [h1, orderOf_one] at this
    omega
  have htx : t * x * t⁻¹ ∈ Q := hS.t_norm_Q x hS.x_mem
  have htx1 : t * x * t⁻¹ ≠ 1 := by
    intro h1
    apply hS.x_ne
    calc x = t⁻¹ * (t * x * t⁻¹) * t := by group
      _ = 1 := by rw [h1]; group
  have htxx : t * x * t⁻¹ ≠ x := by
    intro h1
    have hc : t * x = x * t := by
      calc t * x = (t * x * t⁻¹) * t := by group
        _ = x * t := by rw [h1]
    have h3 : (t * x) ^ 3 = 1 := hS.tx_cube
    have h4 : (t * x) ^ 3 = x := by
      rw [Commute.mul_pow (show Commute t x from hc), ht3, one_mul]
      calc x ^ 3 = x ^ 2 * x := pow_succ x 2
        _ = x := by rw [hS.x_sq, one_mul]
    exact hS.x_ne (h4.symm.trans h3)
  have hty : t * y₀ * t⁻¹ ∈ Q := hS.t_norm_Q y₀ hy₀Q
  have hty1 : t * y₀ * t⁻¹ ≠ 1 := by
    intro h1
    apply hy₀1
    calc y₀ = t⁻¹ * (t * y₀ * t⁻¹) * t := by group
      _ = 1 := by rw [h1]; group
  refine ⟨y₀, hy₀Q, hy₀1, hy₀x, hQall, hy2, hx2, hxy, ht3', ht1, ?_, ?_, htxx⟩
  · rcases hQall (t * x * t⁻¹) htx with h1 | h1 | h1 | h1
    · exact absurd h1 htx1
    · exact absurd h1 htxx
    · exact Or.inl h1
    · exact Or.inr h1
  · rcases hQall (t * y₀ * t⁻¹) hty with h1 | h1 | h1 | h1
    · exact absurd h1 hty1
    · exact Or.inl h1
    · exact Or.inr (Or.inl h1)
    · exact Or.inr (Or.inr h1)

omit [Finite G] in
theorem centralizer_Q_t {t u g : G} (hS : Stage3Loc n x K Q t u g) :
    ∀ q ∈ Q, t * q = q * t → q = 1 := by
  obtain ⟨y₀, hy₀Q, hy₀1, hy₀x, hQall, hy2, hx2, hxy, ht3', ht1, hp, hs, htxx⟩ := Q_facts hS
  have ht2 : ¬ (t * t * x * t⁻¹ * t⁻¹ = x) := by
    intro h2
    apply htxx
    have h3 : t * t * x = x * (t * t) := by
      calc t * t * x = (t * t * x * t⁻¹ * t⁻¹) * (t * t) := by group
        _ = x * (t * t) := by rw [h2]
    have e : t = (t * t) * (t * t) := by
      calc t = t * (t * t * t) := by rw [ht3', mul_one]
        _ = (t * t) * (t * t) := by group
    have h4 : t * x = x * t := by
      calc t * x = ((t * t) * (t * t)) * x := by rw [← e]
        _ = (t * t) * ((t * t) * x) := by group
        _ = (t * t) * (x * (t * t)) := by rw [h3]
        _ = ((t * t) * x) * (t * t) := by group
        _ = (x * (t * t)) * (t * t) := by rw [h3]
        _ = x * ((t * t) * (t * t)) := by group
        _ = x * t := by rw [← e]
    calc t * x * t⁻¹ = (x * t) * t⁻¹ := by rw [h4]
      _ = x := by group
  intro q hq hqt
  rcases hQall q hq with hq1 | hqx | hqy | hqxy
  · exact hq1
  · exfalso
    apply htxx
    rw [hqx] at hqt
    calc t * x * t⁻¹ = (x * t) * t⁻¹ := by rw [hqt]
      _ = x := by group
  · exfalso
    rw [hqy] at hqt
    have hty : t * y₀ * t⁻¹ = y₀ := by
      calc t * y₀ * t⁻¹ = (y₀ * t) * t⁻¹ := by rw [hqt]
        _ = y₀ := by group
    rcases hp with hp | hp
    · apply hy₀x
      have h1 : t * x * t⁻¹ = t * y₀ * t⁻¹ := by rw [hp, hty]
      have h2 : x = y₀ := by
        calc x = t⁻¹ * (t * x * t⁻¹) * t := by group
          _ = t⁻¹ * (t * y₀ * t⁻¹) * t := by rw [h1]
          _ = y₀ := by group
      exact h2.symm
    · apply ht2
      calc t * t * x * t⁻¹ * t⁻¹ = t * (t * x * t⁻¹) * t⁻¹ := by group
        _ = t * (x * y₀) * t⁻¹ := by rw [hp]
        _ = (t * x * t⁻¹) * (t * y₀ * t⁻¹) := by group
        _ = (x * y₀) * y₀ := by rw [hp, hty]
        _ = x := by rw [mul_assoc, hy2, mul_one]
  · exfalso
    rw [hqxy] at hqt
    have hty : t * x * t⁻¹ * (t * y₀ * t⁻¹) = x * y₀ := by
      calc t * x * t⁻¹ * (t * y₀ * t⁻¹) = t * (x * y₀) * t⁻¹ := by group
        _ = (x * y₀ * t) * t⁻¹ := by rw [hqt]
        _ = x * y₀ := by group
    rcases hp with hp | hp
    · rw [hp] at hty
      have h1 : t * y₀ * t⁻¹ = x := by
        calc t * y₀ * t⁻¹ = y₀⁻¹ * (y₀ * (t * y₀ * t⁻¹)) := by group
          _ = y₀⁻¹ * (x * y₀) := by rw [hty]
          _ = y₀⁻¹ * (y₀ * x) := by rw [hxy]
          _ = x := by group
      apply ht2
      calc t * t * x * t⁻¹ * t⁻¹ = t * (t * x * t⁻¹) * t⁻¹ := by group
        _ = t * y₀ * t⁻¹ := by rw [hp]
        _ = x := h1
    · rw [hp] at hty
      apply hy₀1
      have h1 : t * y₀ * t⁻¹ = 1 := by
        calc t * y₀ * t⁻¹ = (x * y₀)⁻¹ * ((x * y₀) * (t * y₀ * t⁻¹)) := by group
          _ = (x * y₀)⁻¹ * (x * y₀) := by rw [hty]
          _ = 1 := by group
      calc y₀ = t⁻¹ * (t * y₀ * t⁻¹) * t := by group
        _ = 1 := by rw [h1]; group

theorem conj_mem_K_of_centralizer_K (hn : n = 5 ∨ n = 6 ∨ n = 7) (hG4 : pRank 2 G ≤ 4)
    (h : IsAConfig n x K T Q S a) (hF : FnFacts n) {t u g : G} (hS : Stage3Loc n x K Q t u g) :
    ∀ r : G, (∀ k ∈ K, r * k = k * r) → g * r * g⁻¹ ∈ K := by
  intro r hr
  have hginv : g⁻¹ = g := sq_eq_one_inv hS.g_sq
  let cg : G ≃* G := MulAut.conj g
  have hcg : ∀ z : G, cg z = g * z * g⁻¹ := fun z => rfl
  have hcgcg : ∀ z : G, cg (cg z) = z := by
    intro z
    rw [hcg, hcg]
    have hg2 : g * g = 1 := by rw [← sq]; exact hS.g_sq
    calc g * (g * z * g⁻¹) * g⁻¹ = (g * g) * z * (g⁻¹ * g⁻¹) := by group
      _ = z := by
        have h1 : g⁻¹ * g⁻¹ = 1 := by rw [hginv]; exact hg2
        rw [hg2, h1]; group
  have hr'Q : ∀ q ∈ Q, cg r * q = q * cg r := by
    intro q hq
    have hk : cg q ∈ K := hS.g_Q q hq
    have h1 : r * cg q = cg q * r := hr _ hk
    have h2 := congrArg cg h1
    rw [map_mul, map_mul, hcgcg] at h2
    exact h2
  have hr't : cg r * t = t * cg r := by
    have h1 : r * cg t = cg t * r := hr _ hS.gt_K
    have h2 := congrArg cg h1
    rw [map_mul, map_mul, hcgcg] at h2
    exact h2
  obtain ⟨k, hk, q', hq', hkq⟩ := centralizer_Q_eq hn hG4 h hF (cg r)
    (fun q hq => hr'Q q hq)
  have hq't : t * q' = q' * t := by
    have h1 : k * q' * t = t * (k * q') := by rw [← hkq]; exact hr't
    have h2 : t * k = k * t := hS.t_comm_K k hk
    have h3 : k * (q' * t) = k * (t * q') := by
      calc k * (q' * t) = k * q' * t := by group
        _ = t * (k * q') := h1
        _ = (t * k) * q' := by group
        _ = (k * t) * q' := by rw [h2]
        _ = k * (t * q') := by group
    exact (mul_left_cancel h3).symm
  have hq'1 : q' = 1 := centralizer_Q_t hS q' hq' hq't
  rw [hq'1, mul_one] at hkq
  show cg r ∈ K
  rw [hkq]
  exact hk

theorem centralizer_K_inf_x
    (hn : n = 5 ∨ n = 6 ∨ n = 7) (hG4 : pRank 2 G ≤ 4)
    (h : IsAConfig n x K T Q S a) :
    ∀ c : G, c * x = x * c → (∀ k ∈ K, c * k = k * c) → c ∈ Q := by
  classical
  obtain ⟨ι, -, hι2⟩ := exists_coord hn hG4 h
  intro c hcx hck
  have hcC : c ∈ centralizer ({x} : Set G) := mem_centralizer_singleton_iff.2 hcx
  have hρ : ((ι ⟨c, hcC⟩ : Fgrp n) : Amb n).1 = 1 := by
    refine eq_one_of_comm_alt hn _ (fun α hα => ?_)
    have hmem : ((α, 1) : Amb n) ∈ Fgrp n :=
      ⟨by simp, by simp [hα]⟩
    obtain ⟨kk, hkk⟩ := ι.surjective ⟨(α, 1), hmem⟩
    have hkk' : ((ι kk : Fgrp n) : Amb n) = (α, 1) := by rw [hkk]
    have hkK : (kk : G) ∈ K := (K_iff hn h hι2 kk).2 (by rw [hkk']; exact ⟨hα, rfl⟩)
    have h1 : (⟨c, hcC⟩ : ↥(centralizer ({x} : Set G))) * kk = kk * ⟨c, hcC⟩ :=
      Subtype.ext (hck _ hkK)
    have h2 := congrArg (fun z : ↥(centralizer ({x} : Set G)) => ((ι z : Fgrp n) : Amb n).1) h1
    simp only [map_mul, Subgroup.coe_mul, Prod.fst_mul, hkk'] at h2
    exact h2
  exact (hι2 ⟨c, hcC⟩).1 hρ

omit [Finite G] in
theorem exists_psi (eK : ↥K ≃* alternatingGroup (Fin n)) {g : G}
    (hD : ∀ r : G, (∀ k ∈ K, r * k = k * r) → g * r * g⁻¹ ∈ K) :
    ∃ φ : ↥(centralizer (K : Set G)) →* Perm (Fin n), Function.Injective φ ∧
      ∀ r, sign (φ r) = 1 := by
  let ψ0 : ↥(centralizer (K : Set G)) →* ↥K :=
    { toFun := fun r => ⟨g * (r : G) * g⁻¹,
        hD r.1 (fun k hk => (Subgroup.mem_centralizer_iff.1 r.2 k hk).symm)⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by simp only [Subgroup.coe_mul]; group) }
  refine ⟨(alternatingGroup (Fin n)).subtype.comp (eK.toMonoidHom.comp ψ0), ?_, ?_⟩
  · intro r₁ r₂ hr
    have h1 : eK (ψ0 r₁) = eK (ψ0 r₂) := Subtype.ext hr
    have h2 : ψ0 r₁ = ψ0 r₂ := eK.injective h1
    have h3 : g * (r₁ : G) * g⁻¹ = g * (r₂ : G) * g⁻¹ := congrArg Subtype.val h2
    exact Subtype.ext (by simpa using h3)
  · intro r
    exact mem_alternatingGroup.1 (eK (ψ0 r)).2

theorem centralizer_K_inf_centralizer_t
    (hC : pRank 2 G ≤ 4) (hn : n = 5 ∨ n = 6)
    (h : IsAConfig n x K T Q S a) {t u g : G} (hS : Stage3Loc n x K Q t u g) :
    ∀ r : G, (∀ k ∈ K, r * k = k * r) → r * t = t * r → r ∈ zpowers t := by
  classical
  have hn' : n = 5 ∨ n = 6 ∨ n = 7 := by omega
  have hG4 : pRank 2 G ≤ 4 := hC
  have hF := fnFacts n hn'
  obtain ⟨eK⟩ := hS.K_alt
  have hD := conj_mem_K_of_centralizer_K hn' hG4 h hF hS
  obtain ⟨φ, hφinj, hφsign⟩ := exists_psi eK hD
  intro r hr hrt
  have hrD : r ∈ centralizer (K : Set G) :=
    Subgroup.mem_centralizer_iff.2 (fun k hk => (hr k hk).symm)
  have htD : t ∈ centralizer (K : Set G) :=
    Subgroup.mem_centralizer_iff.2 (fun k hk => (hS.t_comm_K k hk).symm)
  obtain ⟨y₀, hy₀Q, hy₀1, hy₀x, hQall, hy2, hx2, hxy, ht3', ht1, hp, hs, htxx⟩ := Q_facts hS
  let R : ↥(centralizer (K : Set G)) := ⟨r, hrD⟩
  let T' : ↥(centralizer (K : Set G)) := ⟨t, htD⟩
  have hT3 : T' * T' * T' = 1 := Subtype.ext ht3'
  have hT1 : T' ≠ 1 := fun h1 => ht1 (congrArg Subtype.val h1)
  have hRT : R * T' = T' * R := Subtype.ext hrt
  have hφτ : φ T' * φ T' * φ T' = 1 ∧ φ T' ≠ 1 :=
    ⟨by rw [← map_mul, ← map_mul, hT3, map_one],
      fun h1 => hT1 (hφinj (h1.trans (map_one φ).symm))⟩
  have hφbτ : φ R * φ T' = φ T' * φ R := by rw [← map_mul, ← map_mul, hRT]
  rcases hn with rfl | rfl
  · rcases finite_cent_five hφτ (hφsign R) hφbτ with h1 | h1 | h1
    · have : R = 1 := hφinj (h1.trans (map_one φ).symm)
      have h2 : r = 1 := congrArg Subtype.val this
      rw [h2]; exact one_mem _
    · have : R = T' := hφinj h1
      have h2 : r = t := congrArg Subtype.val this
      rw [h2]; exact mem_zpowers t
    · have : R = T'⁻¹ := hφinj (h1.trans (map_inv φ T').symm)
      have h2 : r = t⁻¹ := congrArg Subtype.val this
      rw [h2]; exact inv_mem (mem_zpowers t)
  · by_contra hnot
    have hr1 : r ≠ 1 := fun h1 => hnot (by rw [h1]; exact one_mem _)
    have hrt1 : r ≠ t := fun h1 => hnot (by rw [h1]; exact mem_zpowers t)
    have hrt2 : r ≠ t⁻¹ := fun h1 => hnot (by rw [h1]; exact inv_mem (mem_zpowers t))
    have hxD : x ∈ centralizer (K : Set G) :=
      Subgroup.mem_centralizer_iff.2 (fun k hk => hS.K_comm_Q k hk x hS.x_mem)
    have hyD : y₀ ∈ centralizer (K : Set G) :=
      Subgroup.mem_centralizer_iff.2 (fun k hk => hS.K_comm_Q k hk y₀ hy₀Q)
    let X : ↥(centralizer (K : Set G)) := ⟨x, hxD⟩
    let Y : ↥(centralizer (K : Set G)) := ⟨y₀, hyD⟩
    have hXX : X * X = 1 := Subtype.ext hx2
    have hYY : Y * Y = 1 := Subtype.ext hy2
    have hXY : X * Y = Y * X := Subtype.ext hxy
    have hX1 : X ≠ 1 := fun h1 => hS.x_ne (congrArg Subtype.val h1)
    have hY1 : Y ≠ 1 := fun h1 => hy₀1 (congrArg Subtype.val h1)
    have hXYne : X ≠ Y := fun h1 => hy₀x (congrArg Subtype.val h1).symm
    have hφX : φ X * φ X = 1 ∧ φ X ≠ 1 ∧ sign (φ X) = 1 :=
      ⟨by rw [← map_mul, hXX, map_one],
        fun h1 => hX1 (hφinj (h1.trans (map_one φ).symm)), hφsign X⟩
    have hφY : φ Y * φ Y = 1 ∧ φ Y ≠ 1 ∧ sign (φ Y) = 1 :=
      ⟨by rw [← map_mul, hYY, map_one],
        fun h1 => hY1 (hφinj (h1.trans (map_one φ).symm)), hφsign Y⟩
    have hφXY : φ X * φ Y = φ Y * φ X ∧ φ X ≠ φ Y :=
      ⟨by rw [← map_mul, ← map_mul, hXY], fun h1 => hXYne (hφinj h1)⟩
    have hφa : φ T' * φ X * (φ T')⁻¹ = φ Y ∨ φ T' * φ X * (φ T')⁻¹ = φ X * φ Y := by
      have e : φ T' * φ X * (φ T')⁻¹ = φ (T' * X * T'⁻¹) := by rw [map_mul, map_mul, map_inv]
      rcases hp with h1 | h1
      · left; rw [e]; congr 1; exact Subtype.ext h1
      · right; rw [e, ← map_mul]; congr 1; exact Subtype.ext h1
    have hφb : φ T' * φ Y * (φ T')⁻¹ = φ X ∨ φ T' * φ Y * (φ T')⁻¹ = φ Y ∨
        φ T' * φ Y * (φ T')⁻¹ = φ X * φ Y := by
      have e : φ T' * φ Y * (φ T')⁻¹ = φ (T' * Y * T'⁻¹) := by rw [map_mul, map_mul, map_inv]
      rcases hs with h1 | h1 | h1
      · left; rw [e]; congr 1; exact Subtype.ext h1
      · right; left; rw [e]; congr 1; exact Subtype.ext h1
      · right; right; rw [e, ← map_mul]; congr 1; exact Subtype.ext h1
    have hRne : φ R ≠ 1 ∧ φ R ≠ φ T' ∧ φ R ≠ (φ T')⁻¹ :=
      ⟨fun h1 => hr1 (congrArg Subtype.val (hφinj (h1.trans (map_one φ).symm))),
        fun h1 => hrt1 (congrArg Subtype.val (hφinj h1)),
        fun h1 => hrt2 (congrArg Subtype.val (hφinj (h1.trans (map_inv φ T').symm)))⟩
    have key : ∀ C : ↥(centralizer (K : Set G)),
        goodW (φ X) (φ Y) (φ C) = true → False := by
      intro C hC'
      have hg := of_decide_eq_true hC'
      obtain ⟨hgc, hg1, hg2, hg3, hg4⟩ := hg
      have h1 : C * X = X * C := hφinj (by rw [map_mul, map_mul]; exact hgc)
      have hCx : (C : G) * x = x * (C : G) := congrArg Subtype.val h1
      have hCQ : (C : G) ∈ Q :=
        centralizer_K_inf_x hn' hG4 h (C : G) hCx
          (fun k hk => (Subgroup.mem_centralizer_iff.1 C.2 k hk).symm)
      rcases hQall (C : G) hCQ with h2 | h2 | h2 | h2
      · exact hg1 (by rw [show C = 1 from Subtype.ext h2, map_one])
      · exact hg2 (by rw [show C = X from Subtype.ext h2])
      · exact hg3 (by rw [show C = Y from Subtype.ext h2])
      · exact hg4 (by rw [show C = X * Y from Subtype.ext h2, map_mul])
    rcases finite_cent_six hφX hφY hφXY hφτ hφa hφb (hφsign R) hφbτ hRne.1 hRne.2.1 hRne.2.2 with
      h1 | h1 | h1
    · apply key (R * Y * R⁻¹ * X * Y * R)
      simpa only [map_mul, map_inv] using h1
    · apply key (R * X * R⁻¹ * X * R)
      simpa only [map_mul, map_inv] using h1
    · apply key (R * X * Y * R⁻¹ * Y * R)
      simpa only [map_mul, map_inv] using h1

end Config

end CFSG.GH74.GLS.C3.Prop121
