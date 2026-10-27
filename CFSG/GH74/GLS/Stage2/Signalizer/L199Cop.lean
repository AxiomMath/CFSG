module

public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.L199

open Subgroup
open scoped commutatorElement

section Cop

variable {X : Type*} [Group X]

theorem commutator_pow_orderOf {x a : X} (h : a * ⁅x, a⁆ = ⁅x, a⁆ * a) :
    ⁅x, a⁆ ^ orderOf a = 1 := by
  set y : X := ⁅x, a⁆ with hy
  have h1 : a * x * a⁻¹ = y⁻¹ * x := by
    rw [hy, commutatorElement_def]; group
  have hca : Commute a y := h
  have hk : ∀ k : ℕ, a ^ k * x * (a ^ k)⁻¹ = (y ^ k)⁻¹ * x := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have hc : Commute a ((y ^ k)⁻¹) := (hca.pow_right k).inv_right
      have hw : a * (y ^ k)⁻¹ * a⁻¹ = (y ^ k)⁻¹ := by rw [hc.eq]; group
      calc a ^ (k + 1) * x * (a ^ (k + 1))⁻¹
          = a * (a ^ k * x * (a ^ k)⁻¹) * a⁻¹ := by group
        _ = a * ((y ^ k)⁻¹ * x) * a⁻¹ := by rw [ih]
        _ = (a * (y ^ k)⁻¹ * a⁻¹) * (a * x * a⁻¹) := by group
        _ = (y ^ k)⁻¹ * (y⁻¹ * x) := by rw [hw, h1]
        _ = (y ^ (k + 1))⁻¹ * x := by rw [pow_succ']; group
  have := hk (orderOf a)
  rw [pow_orderOf_eq_one, inv_one, mul_one] at this
  have h2 : (y ^ orderOf a)⁻¹ = 1 := by
    have : (y ^ orderOf a)⁻¹ * x = 1 * x := by rw [← this, one_mul]
    exact mul_right_cancel this
  simpa using h2

theorem eq_one_of_pow_orderOf_eq_one {p r : ℕ} (hp : p.Prime) (hr : r.Prime) (hpr : p ≠ r)
    {P R : Subgroup X} (hP : IsPGroup p P) (hR : IsPGroup r R) {y a : X} (hy : y ∈ P)
    (ha : a ∈ R) (h : y ^ orderOf a = 1) : y = 1 := by
  obtain ⟨k, hk⟩ := hP ⟨y, hy⟩
  obtain ⟨m, hm⟩ := hR ⟨a, ha⟩
  have h1 : orderOf y ∣ p ^ k := orderOf_dvd_of_pow_eq_one (by simpa using congrArg Subtype.val hk)
  have h2 : orderOf a ∣ r ^ m := orderOf_dvd_of_pow_eq_one (by simpa using congrArg Subtype.val hm)
  have h3 : orderOf y ∣ orderOf a := orderOf_dvd_of_pow_eq_one h
  have hcop : Nat.Coprime (p ^ k) (r ^ m) :=
    Nat.Coprime.pow _ _ ((Nat.coprime_primes hp hr).2 hpr)
  have : orderOf y = 1 := Nat.eq_one_of_dvd_coprimes hcop h1 (h3.trans h2)
  exact orderOf_eq_one_iff.1 this

theorem commutator_eq_bot_of_le_centralizer {p r : ℕ} (hp : p.Prime) (hr : r.Prime) (hpr : p ≠ r)
    {P R C : Subgroup X} (hP : IsPGroup p P) (hR : IsPGroup r R)
    (hn : R ≤ normalizer (P : Set X)) (hC : ⁅P, R⁆ ≤ C) (hRC : R ≤ centralizer (C : Set X)) :
    ⁅P, R⁆ = ⊥ := by
  rw [eq_bot_iff, Subgroup.commutator_le]
  intro x hx a ha
  have hyC : ⁅x, a⁆ ∈ C := hC (Subgroup.commutator_mem_commutator hx ha)
  have hyP : ⁅x, a⁆ ∈ P := by
    have h1 : a * x⁻¹ * a⁻¹ ∈ P := (Subgroup.mem_normalizer_iff.1 (hn ha) x⁻¹).1 (P.inv_mem hx)
    have : ⁅x, a⁆ = x * (a * x⁻¹ * a⁻¹) := by rw [commutatorElement_def]; group
    rw [this]
    exact P.mul_mem hx h1
  have hcomm : a * ⁅x, a⁆ = ⁅x, a⁆ * a := ((Subgroup.mem_centralizer_iff.1 (hRC ha)) _ hyC).symm
  have h2 := eq_one_of_pow_orderOf_eq_one hp hr hpr hP hR hyP ha (commutator_pow_orderOf hcomm)
  simp [h2]

theorem eq_one_of_mem_commutator_of_centralizes [Finite X] {p r : ℕ} [hp' : Fact p.Prime]
    [hr' : Fact r.Prime] (hpr : p ≠ r)
    {V R : Subgroup X} [V.Normal] (hV : IsPGroup p V) (hVab : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a)
    (hR : IsPGroup r R) {c : X} (hc : c ∈ ⁅V, R⁆) (hcR : ∀ ρ ∈ R, ρ * c = c * ρ) : c = 1 := by
  classical
  let _ : CommGroup ↥V :=
    { (inferInstance : Group ↥V) with mul_comm := fun a b => Subtype.ext (hVab _ a.2 _ b.2) }
  have _ : Fintype ↥R := Fintype.ofFinite _
  let cj : ↥R → ↥V → ↥V := fun ρ v =>
    ⟨(ρ : X) * v * (ρ : X)⁻¹, Subgroup.Normal.conj_mem inferInstance _ v.2 _⟩
  have cj_mul : ∀ ρ v w, cj ρ (v * w) = cj ρ v * cj ρ w := by
    intro ρ v w
    apply Subtype.ext
    simp only [cj, Subgroup.coe_mul]
    group
  have cj_cj : ∀ ρ σ v, cj ρ (cj σ v) = cj (ρ * σ) v := by
    intro ρ σ v
    apply Subtype.ext
    simp only [cj, Subgroup.coe_mul]
    group
  let nrm : ↥V →* ↥V := MonoidHom.mk' (fun v => ∏ ρ : ↥R, cj ρ v) (by
    intro v w
    simp only [cj_mul]
    exact Finset.prod_mul_distrib)
  have nrm_cj : ∀ σ v, nrm (cj σ v) = nrm v := by
    intro σ v
    show ∏ ρ : ↥R, cj ρ (cj σ v) = ∏ ρ : ↥R, cj ρ v
    exact Fintype.prod_equiv (Equiv.mulRight σ) _ _ (fun ρ => by simp [cj_cj])
  have hle : ⁅V, R⁆ ≤ nrm.ker.map V.subtype := by
    rw [Subgroup.commutator_le]
    intro a ha b hb
    refine ⟨⟨a, ha⟩ * (cj ⟨b, hb⟩ ⟨a, ha⟩)⁻¹, ?_, ?_⟩
    · simp [MonoidHom.mem_ker, nrm_cj]
    · simp only [cj, commutatorElement_def, Subgroup.subtype_apply, Subgroup.coe_mul, Subgroup.coe_inv]
      group
  obtain ⟨v, hv, hvc⟩ := hle hc
  have hv1 : nrm v = 1 := hv
  have hvcj : ∀ ρ : ↥R, cj ρ v = v := by
    intro ρ
    apply Subtype.ext
    have hvc' : (v : X) = c := hvc
    have := hcR ρ ρ.2
    simp only [cj]
    rw [hvc', this]
    group
  have hnrm : nrm v = v ^ Fintype.card ↥R := by
    show ∏ ρ : ↥R, cj ρ v = _
    simp [hvcj]
  rw [hnrm] at hv1
  obtain ⟨m, hm⟩ := hR.exists_card_eq
  obtain ⟨k, hk⟩ := hV v
  have h1 : orderOf v ∣ p ^ k := orderOf_dvd_of_pow_eq_one hk
  have h2 : orderOf v ∣ r ^ m := by
    rw [← hm, Nat.card_eq_fintype_card]
    exact orderOf_dvd_of_pow_eq_one hv1
  have hcop : Nat.Coprime (p ^ k) (r ^ m) :=
    Nat.Coprime.pow _ _ ((Nat.coprime_primes hp'.out hr'.out).2 hpr)
  have : orderOf v = 1 := Nat.eq_one_of_dvd_coprimes hcop h1 h2
  have hv' : v = 1 := orderOf_eq_one_iff.1 this
  rw [← hvc, hv']
  simp

theorem conj_mem_commutator {V R : Subgroup X} [V.Normal] {g : X} (hg : g ∈ normalizer (R : Set X))
    {x : X} (hx : x ∈ ⁅V, R⁆) : g * x * g⁻¹ ∈ ⁅V, R⁆ := by
  have hle : ⁅V, R⁆ ≤ (⁅V, R⁆).comap (MulAut.conj g).toMonoidHom := by
    rw [Subgroup.commutator_le]
    intro a ha b hb
    have h1 : g * a * g⁻¹ ∈ V := Subgroup.Normal.conj_mem inferInstance a ha g
    have h2 : g * b * g⁻¹ ∈ R := (Subgroup.mem_normalizer_iff.1 hg b).1 hb
    have h3 := Subgroup.commutator_mem_commutator h1 h2
    have h4 : g * ⁅a, b⁆ * g⁻¹ = ⁅g * a * g⁻¹, g * b * g⁻¹⁆ := by
      simp only [commutatorElement_def]; group
    simpa [h4] using h3
  simpa using hle hx

theorem abelian_lemma [Finite X] {p r : ℕ} [hp' : Fact p.Prime] [hr' : Fact r.Prime] (hpr : p ≠ r)
    {V R : Subgroup X} [V.Normal] (hV : IsPGroup p V) (hVab : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a)
    (hR : IsPGroup r R) {z : X} (hz : z * z = 1) (hzR : z ∈ normalizer (R : Set X))
    (hcomm : ⁅R, zpowers z⁆ = R)
    (hC : ∀ u ∈ V, u * z = z * u → ∀ ρ ∈ R, u * ρ = ρ * u) : ⁅V, R⁆ = ⊥ := by
  have hzi : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz
  set V₁ : Subgroup X := ⁅V, R⁆ with hV₁
  have hV₁V : V₁ ≤ V := Subgroup.commutator_le_left V R
  have hzV : ∀ x ∈ V, z * x * z⁻¹ ∈ V := fun x hx => Subgroup.Normal.conj_mem inferInstance x hx z
  have hD : ∀ c ∈ V₁, (∀ ρ ∈ R, ρ * c = c * ρ) → c = 1 := fun c hc hcR =>
    eq_one_of_mem_commutator_of_centralizes hpr hV hVab hR hc hcR
  have hF : ∀ v ∈ V₁, z * v * z⁻¹ = v⁻¹ := by
    intro v hv
    have hw : z * v * z⁻¹ ∈ V₁ := conj_mem_commutator hzR hv
    have hu1 : v * (z * v * z⁻¹) ∈ V₁ := V₁.mul_mem hv hw
    have hzw : z * (z * v * z⁻¹) * z⁻¹ = v := by
      rw [hzi]
      calc z * (z * v * z) * z = (z * z) * v * (z * z) := by group
        _ = v := by rw [hz]; group
    have hvw : v * (z * v * z⁻¹) = (z * v * z⁻¹) * v :=
      hVab v (hV₁V hv) _ (hzV v (hV₁V hv))
    have hu_comm : (v * (z * v * z⁻¹)) * z = z * (v * (z * v * z⁻¹)) := by
      have : z * (v * (z * v * z⁻¹)) * z⁻¹ = v * (z * v * z⁻¹) := by
        calc z * (v * (z * v * z⁻¹)) * z⁻¹
            = (z * v * z⁻¹) * (z * (z * v * z⁻¹) * z⁻¹) := by group
          _ = (z * v * z⁻¹) * v := by rw [hzw]
          _ = v * (z * v * z⁻¹) := hvw.symm
      calc (v * (z * v * z⁻¹)) * z = (z * (v * (z * v * z⁻¹)) * z⁻¹) * z := by rw [this]
        _ = z * (v * (z * v * z⁻¹)) := by group
    have hu := hD _ hu1 (fun ρ hρ => (hC _ (hV₁V hu1) hu_comm ρ hρ).symm)
    exact eq_inv_of_mul_eq_one_right hu
  have hG : R ≤ centralizer (V₁ : Set X) := by
    have hle : ⁅R, zpowers z⁆ ≤ R ⊓ centralizer (V₁ : Set X) := by
      rw [Subgroup.commutator_le]
      intro ρ hρ w hw
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hw
      have hk : z ^ k = 1 ∨ z ^ k = z := by
        have h2 : z ^ (2 : ℤ) = 1 := by rw [zpow_two]; exact hz
        obtain ⟨m, hm | hm⟩ := Int.even_or_odd' k
        · left; rw [hm, zpow_mul, h2, one_zpow]
        · right; rw [hm, zpow_add, zpow_mul, h2, one_zpow, one_mul, zpow_one]
      rcases hk with hk | hk
      · rw [hk]; simp
      · rw [hk]
        refine ⟨?_, ?_⟩
        · have h1 : z * ρ⁻¹ * z⁻¹ ∈ R := (Subgroup.mem_normalizer_iff.1 hzR ρ⁻¹).1 (R.inv_mem hρ)
          have : ⁅ρ, z⁆ = ρ * (z * ρ⁻¹ * z⁻¹) := by rw [commutatorElement_def]; group
          rw [this]; exact R.mul_mem hρ h1
        · show ⁅ρ, z⁆ ∈ centralizer (V₁ : Set X)
          rw [Subgroup.mem_centralizer_iff]
          intro v hv
          have hF' : ∀ x ∈ V₁, z * x * z = x⁻¹ := fun x hx => by
            have := hF x hx; rwa [hzi] at this
          have ha : ρ⁻¹ * v * ρ ∈ V₁ := by
            have := conj_mem_commutator (V := V) (R := R) (g := ρ⁻¹)
              (Subgroup.le_normalizer (R.inv_mem hρ)) hv
            simpa using this
          have h1 := hF' _ (V₁.inv_mem ha)
          have h2 := hF' v hv
          have e1 : ⁅ρ, z⁆ = ρ * z * ρ⁻¹ * z := by rw [commutatorElement_def, hzi]
          have e2 : ⁅ρ, z⁆⁻¹ = z * ρ * z * ρ⁻¹ := by
            rw [e1]; simp only [mul_inv_rev, inv_inv, hzi]; group
          have key : ⁅ρ, z⁆ * v * ⁅ρ, z⁆⁻¹ = v := by
            calc ⁅ρ, z⁆ * v * ⁅ρ, z⁆⁻¹ = (ρ * z * ρ⁻¹ * z) * v * (z * ρ * z * ρ⁻¹) := by
                  rw [e2, e1]
              _ = ρ * (z * (ρ⁻¹ * (z * v * z) * ρ) * z) * ρ⁻¹ := by group
              _ = ρ * (z * (ρ⁻¹ * v⁻¹ * ρ) * z) * ρ⁻¹ := by rw [h2]
              _ = ρ * (z * (ρ⁻¹ * v * ρ)⁻¹ * z) * ρ⁻¹ := by group
              _ = ρ * (ρ⁻¹ * v * ρ) * ρ⁻¹ := by rw [h1, inv_inv]
              _ = v := by group
          have : ⁅ρ, z⁆ * v = v * ⁅ρ, z⁆ := by
            calc ⁅ρ, z⁆ * v = (⁅ρ, z⁆ * v * ⁅ρ, z⁆⁻¹) * ⁅ρ, z⁆ := by group
              _ = v * ⁅ρ, z⁆ := by rw [key]
          exact this.symm
    rw [hcomm] at hle
    exact fun ρ hρ => (hle hρ).2
  have hn : R ≤ normalizer (V : Set X) := by
    rw [Subgroup.normalizer_eq_top V]; exact le_top
  exact commutator_eq_bot_of_le_centralizer hp'.out hr'.out hpr hV hR hn le_rfl hG

end Cop

end CFSG.GH74.GLS.Stage2.Signalizer.L199
