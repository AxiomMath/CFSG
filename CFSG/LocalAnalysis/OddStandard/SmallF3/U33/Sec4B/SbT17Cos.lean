module

public import Mathlib.Data.Nat.Totient
public import Mathlib.GroupTheory.Perm.Cycle.Type

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup

variable {G : Type*} [Group G]

structure FpfSetting (P Q : Subgroup G) (ρ : G) : Prop where
  QP : Q ≤ P
  cen : ∀ p ∈ P, ∀ q ∈ Q, p * q = q * p
  rho3 : ρ ^ 3 = 1
  rhoP : ∀ x ∈ P, ρ * x * ρ⁻¹ ∈ P
  rhoQ : ∀ x ∈ Q, ρ * x * ρ⁻¹ ∈ Q
  fix : ∀ x ∈ P, ρ * x * ρ⁻¹ = x → x = 1
  cardQ : Nat.card Q % 3 = 1
  idx : Q.relIndex P = 4

variable [Finite G] {P Q : Subgroup G} {ρ : G}

private lemma rho_inv_eq (h : FpfSetting P Q ρ) : ρ⁻¹ = ρ ^ 2 :=
  inv_eq_of_mul_eq_one_right (by rw [← pow_succ', h.rho3])

lemma rho2_normalizes_P (h : FpfSetting P Q ρ) (x : G) (hx : x ∈ P) :
    ρ ^ 2 * x * (ρ ^ 2)⁻¹ ∈ P := by
  have hid : ρ ^ 2 * x * (ρ ^ 2)⁻¹ = ρ * (ρ * x * ρ⁻¹) * ρ⁻¹ := by
    simp only [pow_two, mul_inv_rev]
    group
  rw [hid]
  exact h.rhoP _ (h.rhoP x hx)

lemma rho2_normalizes_Q (h : FpfSetting P Q ρ) (x : G) (hx : x ∈ Q) :
    ρ ^ 2 * x * (ρ ^ 2)⁻¹ ∈ Q := by
  have hid : ρ ^ 2 * x * (ρ ^ 2)⁻¹ = ρ * (ρ * x * ρ⁻¹) * ρ⁻¹ := by
    simp only [pow_two, mul_inv_rev]
    group
  rw [hid]
  exact h.rhoQ _ (h.rhoQ x hx)

private lemma rho_inv_normalizes_Q (h : FpfSetting P Q ρ) {x : G} (hx : x ∈ Q) :
    ρ⁻¹ * x * (ρ⁻¹)⁻¹ ∈ Q := by
  rw [rho_inv_eq h]
  exact rho2_normalizes_Q h x hx

private lemma rho2_inv_normalizes_Q (h : FpfSetting P Q ρ) {x : G} (hx : x ∈ Q) :
    (ρ ^ 2)⁻¹ * x * ((ρ ^ 2)⁻¹)⁻¹ ∈ Q := by
  have hid : (ρ ^ 2)⁻¹ * x * ((ρ ^ 2)⁻¹)⁻¹
      = ρ⁻¹ * (ρ⁻¹ * x * (ρ⁻¹)⁻¹) * (ρ⁻¹)⁻¹ := by
    simp only [pow_two, mul_inv_rev]
    group
  rw [hid]
  exact rho_inv_normalizes_Q h (rho_inv_normalizes_Q h hx)

private lemma rho2_fix (h : FpfSetting P Q ρ) (x : G) (hx : x ∈ P)
    (hfix : ρ ^ 2 * x * (ρ ^ 2)⁻¹ = x) : x = 1 := by
  apply h.fix x hx
  have h2 : ρ * (ρ ^ 2 * x * (ρ ^ 2)⁻¹) * ρ⁻¹ = ρ * x * ρ⁻¹ :=
    congrArg (fun t => ρ * t * ρ⁻¹) hfix
  have hleft : ρ * (ρ ^ 2 * x * (ρ ^ 2)⁻¹) * ρ⁻¹ = x := by
    have h3 : ρ * (ρ ^ 2 * x * (ρ ^ 2)⁻¹) * ρ⁻¹
        = (ρ * ρ * ρ) * x * (ρ * ρ * ρ)⁻¹ := by
      simp only [pow_two]
      group
    have hs3 : ρ * ρ * ρ = 1 := by simpa [pow_succ] using h.rho3
    rw [h3, hs3]
    group
  rw [hleft] at h2
  exact h2.symm

private lemma rho2_cube (h : FpfSetting P Q ρ) : (ρ ^ 2) ^ 3 = 1 := by
  have : (ρ ^ 2) ^ 3 = (ρ ^ 3) ^ 2 := by group
  rw [this, h.rho3]
  simp

private lemma exists_fixed_point_of_cube {α : Type*} [Fintype α]
    (f : α → α) (hf : ∀ a, f (f (f a)) = a) (hcard : ¬ 3 ∣ Fintype.card α) :
    ∃ a, f a = a := by
  classical
  let fp : Equiv.Perm α := Equiv.ofBijective f (by
    refine ⟨?_, ?_⟩
    · intro a b hab
      have h := congrArg (fun t => f (f t)) hab
      simpa [hf] using h
    · intro b
      exact ⟨f (f b), hf b⟩)
  have hfp3 : fp ^ 3 = 1 := by
    ext a
    change f (f (f a)) = a
    exact hf a
  exact Equiv.Perm.exists_fixed_point_of_prime (p := 3) (n := 1) hcard hfp3

private theorem mem_of_stable_gen (h : FpfSetting P Q ρ) {σ : G}
    (hσ3 : σ ^ 3 = 1) (hσP : ∀ x ∈ P, σ * x * σ⁻¹ ∈ P)
    (hσQ : ∀ x ∈ Q, σ * x * σ⁻¹ ∈ Q)
    (hfixσ : ∀ x ∈ P, σ * x * σ⁻¹ = x → x = 1)
    {x : G} (hx : x ∈ P) (hst : x⁻¹ * (σ * x * σ⁻¹) ∈ Q) : x ∈ Q := by
  classical
  haveI : Fintype G := Fintype.ofFinite G
  let c : G := x⁻¹ * (σ * x * σ⁻¹)
  have hcQ : c ∈ Q := hst
  let f : ↥Q → ↥Q := fun q =>
    ⟨c * σ * (q : G) * σ⁻¹, by
      have hmem : c * (σ * (q : G) * σ⁻¹) ∈ Q := mul_mem hcQ (hσQ (q : G) q.2)
      simpa only [mul_assoc] using hmem⟩
  have hs3 : σ * σ * σ = 1 := by simpa [pow_succ] using hσ3
  have hcube : ∀ q : ↥Q, f (f (f q)) = q := by
    intro q
    apply Subtype.ext
    have ht : c * σ * c * σ * c * σ = 1 := by
      have h2 : c * σ * c * σ * c * σ = x⁻¹ * (σ * σ * σ) * x := by
        show (x⁻¹ * (σ * x * σ⁻¹)) * σ * (x⁻¹ * (σ * x * σ⁻¹)) * σ
            * (x⁻¹ * (σ * x * σ⁻¹)) * σ = x⁻¹ * (σ * σ * σ) * x
        group
      rw [h2, hs3]
      group
    have hi : σ⁻¹ * σ⁻¹ * σ⁻¹ = 1 := by
      have h2 : σ⁻¹ * σ⁻¹ * σ⁻¹ = (σ * σ * σ)⁻¹ := by group
      rw [h2, hs3, inv_one]
    show c * σ * (c * σ * (c * σ * (q : G) * σ⁻¹) * σ⁻¹) * σ⁻¹ = (q : G)
    rw [show c * σ * (c * σ * (c * σ * (q : G) * σ⁻¹) * σ⁻¹) * σ⁻¹
          = (c * σ * c * σ * c * σ) * ((q : G) * (σ⁻¹ * σ⁻¹ * σ⁻¹)) by group]
    rw [ht, hi, mul_one, one_mul]
  have hcard : ¬ 3 ∣ Fintype.card ↥Q := by
    rw [← Nat.card_eq_fintype_card]
    intro hd
    have h0 : Nat.card ↥Q % 3 = 0 := Nat.mod_eq_zero_of_dvd hd
    have h1 : Nat.card ↥Q % 3 = 1 := h.cardQ
    rw [h1] at h0
    exact Nat.one_ne_zero h0
  obtain ⟨q, hqfix⟩ := exists_fixed_point_of_cube f hcube hcard
  have hqG : c * σ * (q : G) * σ⁻¹ = (q : G) := congrArg Subtype.val hqfix
  have hxq : x * (q : G) ∈ P := P.mul_mem hx (h.QP q.2)
  have hfixxq : σ * (x * (q : G)) * σ⁻¹ = x * (q : G) := by
    have hxqeq : x * (q : G) = σ * (x * (q : G)) * σ⁻¹ := by
      calc x * (q : G) = x * (c * σ * (q : G) * σ⁻¹) := by rw [hqG]
        _ = σ * (x * (q : G)) * σ⁻¹ := by
          show x * ((x⁻¹ * (σ * x * σ⁻¹)) * σ * (q : G) * σ⁻¹)
              = σ * (x * (q : G)) * σ⁻¹
          group
    exact hxqeq.symm
  have hxq1 : x * (q : G) = 1 := hfixσ (x * (q : G)) hxq hfixxq
  have hxinv : x = (q : G)⁻¹ := (mul_eq_one_iff_eq_inv.mp hxq1)
  rw [hxinv]
  exact Q.inv_mem q.2

theorem FpfSetting.mem_of_stable (h : FpfSetting P Q ρ) {x : G} (hx : x ∈ P)
    (hst : x⁻¹ * (ρ * x * ρ⁻¹) ∈ Q) : x ∈ Q :=
  mem_of_stable_gen h h.rho3 h.rhoP h.rhoQ h.fix hx hst

lemma normal_subgroupOf (h : FpfSetting P Q ρ) : (Q.subgroupOf P).Normal :=
  ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    change (g : G) * (n : G) * (g : G)⁻¹ ∈ Q
    rw [h.cen (g : G) g.2 (n : G) hn]
    group
    exact hn⟩

private lemma quot_eq_iff (h : FpfSetting P Q ρ) {u v : ↥P} :
    ((u : ↥P) : ↥P ⧸ Q.subgroupOf P) = (v : ↥P) ↔ (u : G)⁻¹ * (v : G) ∈ Q := by
  rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
  rfl

lemma rho_ne_Q (h : FpfSetting P Q ρ) {a : G} (ha : a ∈ P) (haQ : a ∉ Q) :
    ρ * a * ρ⁻¹ ∉ Q := by
  intro hq
  apply haQ
  have hid : a = ρ⁻¹ * (ρ * a * ρ⁻¹) * (ρ⁻¹)⁻¹ := by group
  rw [hid]
  exact rho_inv_normalizes_Q h hq

lemma rho2_ne_Q (h : FpfSetting P Q ρ) {a : G} (ha : a ∈ P) (haQ : a ∉ Q) :
    ρ ^ 2 * a * (ρ ^ 2)⁻¹ ∉ Q := by
  intro hq
  apply haQ
  have hid : a = (ρ ^ 2)⁻¹ * (ρ ^ 2 * a * (ρ ^ 2)⁻¹) * ((ρ ^ 2)⁻¹)⁻¹ := by group
  rw [hid]
  exact rho2_inv_normalizes_Q h hq

lemma not_stable_rho (h : FpfSetting P Q ρ) {a : G} (ha : a ∈ P) (haQ : a ∉ Q) :
    a⁻¹ * (ρ * a * ρ⁻¹) ∉ Q :=
  fun hq => haQ (h.mem_of_stable ha hq)

lemma not_stable_rho2 (h : FpfSetting P Q ρ) {a : G} (ha : a ∈ P) (haQ : a ∉ Q) :
    a⁻¹ * (ρ ^ 2 * a * (ρ ^ 2)⁻¹) ∉ Q :=
  fun hq => haQ (mem_of_stable_gen h (rho2_cube h) (rho2_normalizes_P h)
    (rho2_normalizes_Q h) (rho2_fix h) ha hq)

private lemma not_stable_rho_of_rho (h : FpfSetting P Q ρ) {a : G} (ha : a ∈ P)
    (haQ : a ∉ Q) : (ρ * a * ρ⁻¹)⁻¹ * (ρ ^ 2 * a * (ρ ^ 2)⁻¹) ∉ Q := by
  intro hq
  have hconj := rho_inv_normalizes_Q h hq
  have hid : ρ⁻¹ * ((ρ * a * ρ⁻¹)⁻¹ * (ρ ^ 2 * a * (ρ ^ 2)⁻¹)) * (ρ⁻¹)⁻¹
      = a⁻¹ * (ρ * a * ρ⁻¹) := by group
  rw [hid] at hconj
  exact not_stable_rho h ha haQ hconj

theorem FpfSetting.cover (h : FpfSetting P Q ρ) {a : G} (ha : a ∈ P) (haQ : a ∉ Q)
    {x : G} (hx : x ∈ P) :
    x ∈ Q ∨ a⁻¹ * x ∈ Q ∨ (ρ * a * ρ⁻¹)⁻¹ * x ∈ Q
      ∨ (ρ ^ 2 * a * (ρ ^ 2)⁻¹)⁻¹ * x ∈ Q := by
  classical
  haveI : Fintype G := Fintype.ofFinite G
  let H : Subgroup ↥P := Q.subgroupOf P
  haveI : H.Normal := normal_subgroupOf h
  let β := ↥P ⧸ H
  have hcardβ : Nat.card β = 4 := by
    change Nat.card (↥P ⧸ Q.subgroupOf P) = 4
    rw [← Subgroup.index_eq_card, show (Q.subgroupOf P).index = Q.relIndex P from rfl, h.idx]
  have hcardβ' : Fintype.card β = 4 := by
    rw [← Nat.card_eq_fintype_card]; exact hcardβ
  let p0 : β := (⟨1, P.one_mem⟩ : ↥P)
  let p1 : β := (⟨a, ha⟩ : ↥P)
  let p2 : β := (⟨ρ * a * ρ⁻¹, h.rhoP a ha⟩ : ↥P)
  let p3 : β := (⟨ρ ^ 2 * a * (ρ ^ 2)⁻¹, rho2_normalizes_P h a ha⟩ : ↥P)
  let f : Fin 4 → β := ![p0, p1, p2, p3]
  have h01 : p0 ≠ p1 := by
    intro hh
    exact haQ (by simpa using (quot_eq_iff h).mp hh)
  have h02 : p0 ≠ p2 := by
    intro hh
    exact rho_ne_Q h ha haQ (by simpa using (quot_eq_iff h).mp hh)
  have h03 : p0 ≠ p3 := by
    intro hh
    exact rho2_ne_Q h ha haQ (by simpa using (quot_eq_iff h).mp hh)
  have h12 : p1 ≠ p2 := by
    intro hh
    exact not_stable_rho h ha haQ (by simpa using (quot_eq_iff h).mp hh)
  have h13 : p1 ≠ p3 := by
    intro hh
    exact not_stable_rho2 h ha haQ (by simpa using (quot_eq_iff h).mp hh)
  have h23 : p2 ≠ p3 := by
    intro hh
    exact not_stable_rho_of_rho h ha haQ (by simpa using (quot_eq_iff h).mp hh)
  have hinj : Function.Injective f := by
    intro i j hij
    fin_cases i <;> fin_cases j
    · rfl
    · exact absurd hij h01
    · exact absurd hij h02
    · exact absurd hij h03
    · exact absurd hij.symm h01
    · rfl
    · exact absurd hij h12
    · exact absurd hij h13
    · exact absurd hij.symm h02
    · exact absurd hij.symm h12
    · rfl
    · exact absurd hij h23
    · exact absurd hij.symm h03
    · exact absurd hij.symm h13
    · exact absurd hij.symm h23
    · rfl
  have hbij : Function.Bijective f :=
    (Fintype.bijective_iff_injective_and_card f).mpr
      ⟨hinj, by rw [Fintype.card_fin, hcardβ']⟩
  obtain ⟨i, hi⟩ := hbij.2 (⟨x, hx⟩ : ↥P)
  fin_cases i
  · left
    simpa using (quot_eq_iff h).mp hi
  · right; left
    simpa using (quot_eq_iff h).mp hi
  · right; right; left
    simpa using (quot_eq_iff h).mp hi
  · right; right; right
    simpa using (quot_eq_iff h).mp hi

private lemma pow_four_mem (h : FpfSetting P Q ρ) {x : G} (hx : x ∈ P) : x ^ 4 ∈ Q := by
  haveI : (Q.subgroupOf P).Normal := normal_subgroupOf h
  have hmem := Subgroup.pow_index_mem (Q.subgroupOf P) (⟨x, hx⟩ : ↥P)
  rw [show (Q.subgroupOf P).index = 4 by
    rw [show (Q.subgroupOf P).index = Q.relIndex P from rfl, h.idx]] at hmem
  rw [Subgroup.mem_subgroupOf] at hmem
  simpa using hmem

theorem FpfSetting.sq_mem (h : FpfSetting P Q ρ) : ∀ x ∈ P, x ^ 2 ∈ Q := by
  intro x hx
  by_cases hxQ : x ∈ Q
  · simpa [pow_two] using Q.mul_mem hxQ hxQ
  · have hsq : x ^ 2 ∈ P := by simpa [pow_two] using P.mul_mem hx hx
    have hx4 : x ^ 4 ∈ Q := pow_four_mem h hx
    rcases h.cover hx hxQ hsq with hq | hq | hq | hq
    · exact hq
    · exact absurd (by simpa [pow_two, mul_assoc] using hq) hxQ
    · set r : G := ρ * x * ρ⁻¹ with hr
      have hrP : r ∈ P := h.rhoP x hx
      set q : G := r⁻¹ * x ^ 2 with hqdef
      have hqQ : q ∈ Q := hq
      have hx2 : x ^ 2 = r * q := by rw [hqdef]; group
      have hr2Q : r ^ 2 ∈ Q := by
        have hcomm : r * q = q * r := h.cen r hrP q hqQ
        have h4 : (r * q) ^ 2 = x ^ 4 := by
          rw [show x ^ 4 = (x ^ 2) ^ 2 by group, ← hx2]
        have hsqr : (r * q) ^ 2 = r ^ 2 * q ^ 2 := by
          calc (r * q) ^ 2 = r * (q * r) * q := by rw [pow_two]; group
            _ = r * (r * q) * q := by rw [← hcomm]
            _ = r ^ 2 * q ^ 2 := by rw [pow_two, pow_two]; group
        have hr2eq : r ^ 2 = x ^ 4 * (q ^ 2)⁻¹ := by
          calc r ^ 2 = r ^ 2 * q ^ 2 * (q ^ 2)⁻¹ := by group
            _ = (r * q) ^ 2 * (q ^ 2)⁻¹ := by rw [hsqr]
            _ = x ^ 4 * (q ^ 2)⁻¹ := by rw [h4]
        rw [hr2eq]
        exact Q.mul_mem hx4 (Q.inv_mem (by simpa [pow_two] using Q.mul_mem hqQ hqQ))
      have hr2conj : r ^ 2 = ρ * (x ^ 2) * ρ⁻¹ := by
        simp only [hr, pow_two]; group
      have hc := rho_inv_normalizes_Q h hr2Q
      rw [hr2conj] at hc
      simpa [mul_assoc] using hc
    · set r : G := ρ ^ 2 * x * (ρ ^ 2)⁻¹ with hr
      have hrP : r ∈ P := rho2_normalizes_P h x hx
      set q : G := r⁻¹ * x ^ 2 with hqdef
      have hqQ : q ∈ Q := hq
      have hx2 : x ^ 2 = r * q := by rw [hqdef]; group
      have hr2Q : r ^ 2 ∈ Q := by
        have hcomm : r * q = q * r := h.cen r hrP q hqQ
        have h4 : (r * q) ^ 2 = x ^ 4 := by
          rw [show x ^ 4 = (x ^ 2) ^ 2 by group, ← hx2]
        have hsqr : (r * q) ^ 2 = r ^ 2 * q ^ 2 := by
          calc (r * q) ^ 2 = r * (q * r) * q := by rw [pow_two]; group
            _ = r * (r * q) * q := by rw [← hcomm]
            _ = r ^ 2 * q ^ 2 := by rw [pow_two, pow_two]; group
        have hr2eq : r ^ 2 = x ^ 4 * (q ^ 2)⁻¹ := by
          calc r ^ 2 = r ^ 2 * q ^ 2 * (q ^ 2)⁻¹ := by group
            _ = (r * q) ^ 2 * (q ^ 2)⁻¹ := by rw [hsqr]
            _ = x ^ 4 * (q ^ 2)⁻¹ := by rw [h4]
        rw [hr2eq]
        exact Q.mul_mem hx4 (Q.inv_mem (by simpa [pow_two] using Q.mul_mem hqQ hqQ))
      have hr2conj : r ^ 2 = (ρ ^ 2) * (x ^ 2) * (ρ ^ 2)⁻¹ := by
        simp only [hr, pow_two]; group
      have hc := rho2_inv_normalizes_Q h hr2Q
      rw [hr2conj] at hc
      simpa [mul_assoc] using hc

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
