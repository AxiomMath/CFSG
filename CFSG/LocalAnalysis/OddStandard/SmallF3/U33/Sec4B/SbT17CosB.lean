module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbT17Cos

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup

variable {G : Type*} [Group G]

variable [Finite G] {P Q : Subgroup G} {ρ : G}

private lemma mul_comm_of_sq_eq_one {M : Type*} [Group M] {x y : M}
    (hx : x ^ 2 = 1) (hy : y ^ 2 = 1) (hxy : (x * y) ^ 2 = 1) : x * y = y * x := by
  have hx' : x⁻¹ = x := inv_eq_of_mul_eq_one_right (by rwa [pow_two] at hx)
  have hy' : y⁻¹ = y := inv_eq_of_mul_eq_one_right (by rwa [pow_two] at hy)
  calc x * y = (x * y)⁻¹ := (inv_eq_of_mul_eq_one_right (by rwa [pow_two] at hxy)).symm
    _ = y⁻¹ * x⁻¹ := mul_inv_rev x y
    _ = y * x := by rw [hx', hy']

private lemma commutator_mem_Q (h : FpfSetting P Q ρ) {a b : G} (ha : a ∈ P) (hb : b ∈ P) :
    a * b * a⁻¹ * b⁻¹ ∈ Q := by
  classical
  let H : Subgroup ↥P := Q.subgroupOf P
  haveI : H.Normal := normal_subgroupOf h
  have hβ : ∀ z : ↥P ⧸ H, z ^ 2 = 1 := by
    intro z
    obtain ⟨u, rfl⟩ := QuotientGroup.mk'_surjective (N := H) z
    rw [← map_pow]
    show ((u ^ 2 : ↥P) : ↥P ⧸ H) = 1
    rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    simpa using h.sq_mem (u : G) u.2
  let u : ↥P := ⟨a * b * a⁻¹ * b⁻¹, by
    exact P.mul_mem (P.mul_mem (P.mul_mem ha hb) (P.inv_mem ha)) (P.inv_mem hb)⟩
  have htu : (↑u : ↥P ⧸ H) = 1 := by
    change QuotientGroup.mk' H u = 1
    have huval : u = (⟨a, ha⟩ : ↥P) * (⟨b, hb⟩ : ↥P) * (⟨a, ha⟩ : ↥P)⁻¹
        * (⟨b, hb⟩ : ↥P)⁻¹ := by
      apply Subtype.ext; rfl
    rw [huval]
    simp only [map_mul, map_inv]
    have hcomm : QuotientGroup.mk' H (⟨a, ha⟩ : ↥P) * QuotientGroup.mk' H (⟨b, hb⟩ : ↥P)
        = QuotientGroup.mk' H (⟨b, hb⟩ : ↥P) * QuotientGroup.mk' H (⟨a, ha⟩ : ↥P) :=
      mul_comm_of_sq_eq_one (hβ _) (hβ _) (hβ _)
    rw [hcomm]
    group
  have hmem : u ∈ H := (QuotientGroup.eq_one_iff u).mp htu
  rwa [Subgroup.mem_subgroupOf] at hmem

private lemma rho2_inv_eq (h : FpfSetting P Q ρ) : (ρ ^ 2)⁻¹ = ρ := by
  have hs3 : ρ * ρ * ρ = 1 := by simpa [pow_succ] using h.rho3
  rw [pow_two]
  exact inv_eq_of_mul_eq_one_right (by simpa [mul_assoc] using hs3)

private lemma mul_coset_comm (h : FpfSetting P Q ρ) {c x q : G} (hx : x ∈ P) (hq : q ∈ Q)
    (hc : c ∈ P) (hcx : c * x = x * c) : c * (x * q) = (x * q) * c := by
  calc c * (x * q) = (c * x) * q := by group
    _ = (x * c) * q := by rw [hcx]
    _ = x * (c * q) := by group
    _ = x * (q * c) := by rw [h.cen c hc q hq]
    _ = (x * q) * c := by group

private lemma commutator_mul_central (h : FpfSetting P Q ρ) {b z q : G}
    (hb : b ∈ P) (hz : z ∈ P) (hq : q ∈ Q) :
    b * (z * q) * b⁻¹ * (z * q)⁻¹ = b * z * b⁻¹ * z⁻¹ := by
  have hqb : q * b⁻¹ = b⁻¹ * q := (h.cen b⁻¹ (P.inv_mem hb) q hq).symm
  calc b * (z * q) * b⁻¹ * (z * q)⁻¹
      = b * z * q * b⁻¹ * (q⁻¹ * z⁻¹) := by rw [mul_inv_rev]; group
    _ = b * z * (q * b⁻¹) * q⁻¹ * z⁻¹ := by group
    _ = b * z * (b⁻¹ * q) * q⁻¹ * z⁻¹ := by rw [hqb]
    _ = b * z * b⁻¹ * z⁻¹ := by group

private lemma comm_rho_self (h : FpfSetting P Q ρ) {a : G} (ha : a ∈ P) (haQ : a ∉ Q) :
    a * (ρ * a * ρ⁻¹) = (ρ * a * ρ⁻¹) * a := by
  have hbP : ρ * a * ρ⁻¹ ∈ P := h.rhoP a ha
  let b : G := ρ * a * ρ⁻¹
  let c : G := a * b * a⁻¹ * b⁻¹
  have hbQ : b ∉ Q := by simpa only [b] using rho_ne_Q h ha haQ
  have hcQ : c ∈ Q := by
    have hmem := commutator_mem_Q h ha hbP
    simpa only [c, b] using hmem
  have hcP : c ∈ P := h.QP hcQ
  have ha2Q : a ^ 2 ∈ Q := h.sq_mem a ha
  have hzP : a * b ∈ P := P.mul_mem ha hbP
  have hzQ : a * b ∉ Q := by
    intro hz
    have hst : a⁻¹ * b ∈ Q := by
      have : a⁻¹ * b = (a ^ 2)⁻¹ * (a * b) := by group
      rw [this]
      exact Q.mul_mem (Q.inv_mem ha2Q) hz
    exact not_stable_rho h ha haQ (by simpa only [b] using hst)
  have hzaQ : a⁻¹ * (a * b) ∉ Q := by
    have : a⁻¹ * (a * b) = b := by group
    rw [this]
    exact hbQ
  have hzbQ : b⁻¹ * (a * b) ∉ Q := by
    intro hq
    apply haQ
    have hq'' : b * (b⁻¹ * (a * b)) * b⁻¹ = b⁻¹ * (a * b) := by
      rw [h.cen b hbP (b⁻¹ * (a * b)) hq]
      group
    have hq' : a = b * (b⁻¹ * (a * b)) * b⁻¹ := by group
    rw [hq', hq'']
    exact hq
  rcases h.cover ha haQ hzP with hq0 | hq1 | hq2 | hq3
  · exact absurd hq0 hzQ
  · exact absurd hq1 hzaQ
  · exact absurd hq2 hzbQ
  · have hq3' : (ρ * b * ρ⁻¹)⁻¹ * (a * b) ∈ Q := by
      have heq : ρ * b * ρ⁻¹ = ρ ^ 2 * a * (ρ ^ 2)⁻¹ := by
        simp only [b, pow_two, mul_inv_rev]; group
      rwa [← heq] at hq3
    obtain ⟨q, hqQ, hzq⟩ : ∃ q ∈ Q, a * b = (ρ * b * ρ⁻¹) * q :=
      ⟨(ρ * b * ρ⁻¹)⁻¹ * (a * b), hq3', by group⟩
    have hb2eq : ρ * b * ρ⁻¹ = a * b * q⁻¹ := by rw [hzq]; group
    have hbb2 : b * (ρ * b * ρ⁻¹) * b⁻¹ * (ρ * b * ρ⁻¹)⁻¹ = c⁻¹ := by
      rw [hb2eq]
      rw [commutator_mul_central h hbP (P.mul_mem ha hbP) (Q.inv_mem hqQ)]
      rw [show b * (a * b) * b⁻¹ * (a * b)⁻¹ = b * a * b⁻¹ * a⁻¹ by group]
      rw [show b * a * b⁻¹ * a⁻¹ = c⁻¹ by simp only [c]; group]
    have hconjc : ρ * c * ρ⁻¹ = b * (ρ * b * ρ⁻¹) * b⁻¹ * (ρ * b * ρ⁻¹)⁻¹ := by
      simp only [c, b]
      group
    have hc_inv : ρ * c * ρ⁻¹ = c⁻¹ := by rw [hconjc, hbb2]
    have hs3 : ρ * ρ * ρ = 1 := by simpa [pow_succ] using h.rho3
    have h2 : ρ * (ρ * c * ρ⁻¹) * ρ⁻¹ = c := by
      have hR : ρ * c⁻¹ * ρ⁻¹ = c := by
        have : ρ * c⁻¹ * ρ⁻¹ = (ρ * c * ρ⁻¹)⁻¹ := by group
        rw [this, hc_inv, inv_inv]
      have hcongr := congrArg (fun t => ρ * t * ρ⁻¹) hc_inv
      rwa [hR] at hcongr
    have h3 : ρ * (ρ * (ρ * c * ρ⁻¹) * ρ⁻¹) * ρ⁻¹ = c := by
      have heq : ρ * (ρ * (ρ * c * ρ⁻¹) * ρ⁻¹) * ρ⁻¹
          = (ρ * ρ * ρ) * c * (ρ * ρ * ρ)⁻¹ := by group
      rw [heq, hs3]
      group
    have hc_eq_inv : c⁻¹ = c := by
      have hcongr := congrArg (fun t => ρ * t * ρ⁻¹) h2
      rw [h3, hc_inv] at hcongr
      exact hcongr.symm
    have hfixc : ρ * c * ρ⁻¹ = c := by rw [hc_inv, hc_eq_inv]
    have hc1 : c = 1 := h.fix c hcP hfixc
    have hab : a * b = c * (b * a) := by simp only [c]; group
    rw [hab, hc1, one_mul]

private lemma comm_rho2_self (h : FpfSetting P Q ρ) {a : G} (ha : a ∈ P) (haQ : a ∉ Q) :
    a * (ρ ^ 2 * a * (ρ ^ 2)⁻¹) = (ρ ^ 2 * a * (ρ ^ 2)⁻¹) * a := by
  have hbP : ρ ^ 2 * a * (ρ ^ 2)⁻¹ ∈ P := rho2_normalizes_P h a ha
  have hbQ : ρ ^ 2 * a * (ρ ^ 2)⁻¹ ∉ Q := rho2_ne_Q h ha haQ
  have hmain := comm_rho_self h hbP hbQ
  have hback : ρ * (ρ ^ 2 * a * (ρ ^ 2)⁻¹) * ρ⁻¹ = a := by
    rw [rho2_inv_eq h]
    group
    simp [h.rho3]
  rw [hback] at hmain
  exact hmain.symm

theorem FpfSetting.comm (h : FpfSetting P Q ρ) : ∀ a ∈ P, ∀ b ∈ P, a * b = b * a := by
  intro a ha b hb
  by_cases haQ : a ∈ Q
  · exact (h.cen b hb a haQ).symm
  by_cases hbQ : b ∈ Q
  · exact h.cen a ha b hbQ
  rcases h.cover ha haQ hb with hbQ' | hcase | hcase | hcase
  · exact absurd hbQ' hbQ
  · obtain ⟨q, hqQ, rfl⟩ : ∃ q ∈ Q, b = a * q := ⟨a⁻¹ * b, hcase, by group⟩
    exact mul_coset_comm h ha hqQ ha rfl
  · obtain ⟨q, hqQ, rfl⟩ : ∃ q ∈ Q, b = (ρ * a * ρ⁻¹) * q :=
      ⟨(ρ * a * ρ⁻¹)⁻¹ * b, hcase, by group⟩
    exact mul_coset_comm h (h.rhoP a ha) hqQ ha (comm_rho_self h ha haQ)
  · obtain ⟨q, hqQ, rfl⟩ : ∃ q ∈ Q, b = (ρ ^ 2 * a * (ρ ^ 2)⁻¹) * q :=
      ⟨(ρ ^ 2 * a * (ρ ^ 2)⁻¹)⁻¹ * b, hcase, by group⟩
    exact mul_coset_comm h (rho2_normalizes_P h a ha) hqQ ha (comm_rho2_self h ha haQ)

private lemma gconj_cancel {g a : G} (hg2 : g * g = 1) : g * (g * a * g⁻¹) * g⁻¹ = a := by
  have heq : g * (g * a * g⁻¹) * g⁻¹ = (g * g) * a * (g * g)⁻¹ := by group
  rw [heq, hg2]
  group

private lemma gconj_rho {g ρ t : G} (hg : g * ρ = ρ * g) :
    g * (ρ * t * ρ⁻¹) * g⁻¹ = ρ * (g * t * g⁻¹) * ρ⁻¹ := by
  have hginv : ρ⁻¹ * g⁻¹ = g⁻¹ * ρ⁻¹ := by rw [← mul_inv_rev, hg, mul_inv_rev]
  calc g * (ρ * t * ρ⁻¹) * g⁻¹ = g * ρ * t * ρ⁻¹ * g⁻¹ := by group
    _ = ρ * g * t * ρ⁻¹ * g⁻¹ := by rw [hg]
    _ = ρ * g * t * (ρ⁻¹ * g⁻¹) := by group
    _ = ρ * g * t * (g⁻¹ * ρ⁻¹) := by rw [hginv]
    _ = ρ * (g * t * g⁻¹) * ρ⁻¹ := by group

private lemma gconj_rho2 {g ρ t : G} (hg : g * ρ = ρ * g) :
    g * (ρ * (ρ * t * ρ⁻¹) * ρ⁻¹) * g⁻¹ = ρ * (ρ * (g * t * g⁻¹) * ρ⁻¹) * ρ⁻¹ := by
  have h1 := gconj_rho (g := g) (ρ := ρ) (t := ρ * t * ρ⁻¹) hg
  have h2 := gconj_rho (g := g) (ρ := ρ) (t := t) hg
  rw [h2] at h1
  exact h1

theorem FpfSetting.trivial_action (h : FpfSetting P Q ρ) {g : G} (hg : g * ρ = ρ * g)
    (hg2 : g * g = 1) (hgP : ∀ x ∈ P, g * x * g⁻¹ ∈ P) (hgQ : ∀ x ∈ Q, g * x * g⁻¹ ∈ Q) :
    ∀ x ∈ P, x⁻¹ * (g * x * g⁻¹) ∈ Q := by
  intro x hx
  by_cases hxQ : x ∈ Q
  · exact Q.mul_mem (Q.inv_mem hxQ) (hgQ x hxQ)
  · have hgxP : g * x * g⁻¹ ∈ P := hgP x hx
    have hgxQ : g * x * g⁻¹ ∉ Q := by
      intro hq
      apply hxQ
      have hgg : g * (g * x * g⁻¹) * g⁻¹ = x := gconj_cancel hg2
      rw [← hgg]
      exact hgQ (g * x * g⁻¹) hq
    rcases h.cover hx hxQ hgxP with hq0 | hq1 | hq2 | hq3
    · exact absurd hq0 hgxQ
    · exact hq1
    · set q : G := (ρ * x * ρ⁻¹)⁻¹ * (g * x * g⁻¹) with hqdef
      have hqQ : q ∈ Q := hq2
      have hgval : g * x * g⁻¹ = (ρ * x * ρ⁻¹) * q := by rw [hqdef]; group
      have ha_eq : x = (ρ * (ρ * x * ρ⁻¹) * ρ⁻¹) * (ρ * q * ρ⁻¹ * (g * q * g⁻¹)) := by
        calc x = g * (g * x * g⁻¹) * g⁻¹ := (gconj_cancel hg2).symm
          _ = g * ((ρ * x * ρ⁻¹) * q) * g⁻¹ := by rw [hgval]
          _ = (g * (ρ * x * ρ⁻¹) * g⁻¹) * (g * q * g⁻¹) := by group
          _ = (ρ * (g * x * g⁻¹) * ρ⁻¹) * (g * q * g⁻¹) := by rw [gconj_rho hg]
          _ = (ρ * ((ρ * x * ρ⁻¹) * q) * ρ⁻¹) * (g * q * g⁻¹) := by rw [hgval]
          _ = (ρ * (ρ * x * ρ⁻¹) * ρ⁻¹) * (ρ * q * ρ⁻¹ * (g * q * g⁻¹)) := by group
      have hconjQ : (ρ * (ρ * x * ρ⁻¹) * ρ⁻¹)⁻¹ * x ∈ Q := by
        have hxA : (ρ * (ρ * x * ρ⁻¹) * ρ⁻¹)⁻¹ * x
            = (ρ * q * ρ⁻¹) * (g * q * g⁻¹) := by
          have := congrArg (fun t => (ρ * (ρ * x * ρ⁻¹) * ρ⁻¹)⁻¹ * t) ha_eq
          rw [this]; group
        rw [hxA]
        exact Q.mul_mem (h.rhoQ q hqQ) (hgQ q hqQ)
      have hcontra : x⁻¹ * (ρ ^ 2 * x * (ρ ^ 2)⁻¹) ∈ Q := by
        have hinv : x⁻¹ * (ρ * (ρ * x * ρ⁻¹) * ρ⁻¹) ∈ Q := by
          simpa [mul_inv_rev] using Q.inv_mem hconjQ
        have heq : ρ * (ρ * x * ρ⁻¹) * ρ⁻¹ = ρ ^ 2 * x * (ρ ^ 2)⁻¹ := by
          simp only [pow_two, mul_inv_rev]; group
        rwa [heq] at hinv
      exact absurd hcontra (not_stable_rho2 h hx hxQ)
    · set q : G := (ρ ^ 2 * x * (ρ ^ 2)⁻¹)⁻¹ * (g * x * g⁻¹) with hqdef
      have hqQ : q ∈ Q := hq3
      have hgval : g * x * g⁻¹ = (ρ ^ 2 * x * (ρ ^ 2)⁻¹) * q := by rw [hqdef]; group
      have heq2 : ρ ^ 2 * x * (ρ ^ 2)⁻¹ = ρ * (ρ * x * ρ⁻¹) * ρ⁻¹ := by
        simp only [pow_two, mul_inv_rev]; group
      have hgAg : g * (ρ ^ 2 * x * (ρ ^ 2)⁻¹) * g⁻¹
          = (ρ * x * ρ⁻¹) * (ρ ^ 2 * q * (ρ ^ 2)⁻¹) := by
        have h4n : ρ ^ (4 : ℕ) = ρ := by
          rw [show (4 : ℕ) = 3 + 1 by norm_num, pow_succ, h.rho3, one_mul]
        have h4 : ρ ^ (4 : ℤ) = ρ := by
          rw [show (4 : ℤ) = ((4 : ℕ) : ℤ) by norm_num, zpow_natCast]
          exact h4n
        have hm2 : ρ ^ (-2 : ℤ) = ρ := by
          rw [show (-2 : ℤ) = -(2 : ℤ) by norm_num, zpow_neg]
          rw [show (2 : ℤ) = ((2 : ℕ) : ℤ) by norm_num, zpow_natCast]
          exact rho2_inv_eq h
        rw [heq2, gconj_rho2 hg, hgval]
        rw [rho2_inv_eq h]
        group
        rw [h4, hm2]
      have ha_eq : x = (ρ * x * ρ⁻¹) * ((ρ ^ 2 * q * (ρ ^ 2)⁻¹) * (g * q * g⁻¹)) := by
        calc x = g * (g * x * g⁻¹) * g⁻¹ := (gconj_cancel hg2).symm
          _ = g * ((ρ ^ 2 * x * (ρ ^ 2)⁻¹) * q) * g⁻¹ := by rw [hgval]
          _ = (g * (ρ ^ 2 * x * (ρ ^ 2)⁻¹) * g⁻¹) * (g * q * g⁻¹) := by group
          _ = ((ρ * x * ρ⁻¹) * (ρ ^ 2 * q * (ρ ^ 2)⁻¹)) * (g * q * g⁻¹) := by rw [hgAg]
          _ = (ρ * x * ρ⁻¹) * ((ρ ^ 2 * q * (ρ ^ 2)⁻¹) * (g * q * g⁻¹)) := by group
      have hconjQ : (ρ * x * ρ⁻¹)⁻¹ * x ∈ Q := by
        have hxA : (ρ * x * ρ⁻¹)⁻¹ * x
            = (ρ ^ 2 * q * (ρ ^ 2)⁻¹) * (g * q * g⁻¹) := by
          have := congrArg (fun t => (ρ * x * ρ⁻¹)⁻¹ * t) ha_eq
          rw [this]; group
        rw [hxA]
        exact Q.mul_mem (rho2_normalizes_Q h q hqQ) (hgQ q hqQ)
      have hcontra : x⁻¹ * (ρ * x * ρ⁻¹) ∈ Q := by
        have hinv : x⁻¹ * (ρ * x * ρ⁻¹) ∈ Q := by
          simpa [mul_inv_rev] using Q.inv_mem hconjQ
        exact hinv
      exact absurd hcontra (not_stable_rho h hx hxQ)

theorem FpfSetting.sup_eq (h : FpfSetting P Q ρ) {C : Subgroup G} (hCP : C ≤ P)
    (hCρ : ∀ x ∈ C, ρ * x * ρ⁻¹ ∈ C) :
    C ≤ Q ∨ ∀ x ∈ P, ∃ c ∈ C, c⁻¹ * x ∈ Q := by
  by_cases hCQ : C ≤ Q
  · exact Or.inl hCQ
  · right
    rw [SetLike.le_def] at hCQ
    push Not at hCQ
    obtain ⟨c, hcC, hcQ⟩ := hCQ
    have hcP : c ∈ P := hCP hcC
    intro x hx
    rcases h.cover hcP hcQ hx with hxQ | hcase | hcase | hcase
    · exact ⟨1, C.one_mem, by simpa using hxQ⟩
    · exact ⟨c, hcC, hcase⟩
    · exact ⟨ρ * c * ρ⁻¹, hCρ c hcC, hcase⟩
    · refine ⟨ρ ^ 2 * c * (ρ ^ 2)⁻¹, ?_, hcase⟩
      have h1 := hCρ c hcC
      have h2 := hCρ (ρ * c * ρ⁻¹) h1
      have heq : ρ * (ρ * c * ρ⁻¹) * ρ⁻¹ = ρ ^ 2 * c * (ρ ^ 2)⁻¹ := by
        simp only [pow_two, mul_inv_rev]; group
      rwa [heq] at h2

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
