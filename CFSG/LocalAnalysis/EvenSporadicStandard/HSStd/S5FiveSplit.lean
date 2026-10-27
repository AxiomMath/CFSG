module

public import CFSG.Permutation.SymmetricCoxeter
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.S5FiveQuot
import CFSG.Mathlib.GroupTheory.PermCommute

public section

namespace CFSG.EvenSporadicStandard.HSStd

open Subgroup Equiv CFSG.Permutation.SymmetricCoxeter

structure IsCentralExtPermFive {E : Type*} [Group E] (φ : E →* Perm (Fin 5)) (z : E) : Prop where
  central : z ∈ center E
  mul_self : z * z = 1
  map_eq_one : φ z = 1
  surjective : Function.Surjective φ
  eq_one_or_eq : ∀ x, φ x = 1 → x = 1 ∨ x = z

section Lifts

variable {E : Type*} [Group E] {φ : E →* Perm (Fin 5)} {z : E}

theorem IsCentralExtPermFive.eq_or_eq_mul (h : IsCentralExtPermFive φ z) {x y : E}
    (hxy : φ x = φ y) : x = y ∨ x = z * y := by
  have h1 : φ (x * y⁻¹) = 1 := by rw [map_mul, map_inv, hxy, mul_inv_cancel]
  rcases h.eq_one_or_eq _ h1 with h2 | h2
  · exact Or.inl (mul_inv_eq_one.1 h2)
  · exact Or.inr (mul_inv_eq_iff_eq_mul.1 h2)

theorem IsCentralExtPermFive.commute (h : IsCentralExtPermFive φ z) (x : E) : Commute z x :=
  (mem_center_iff.1 h.central x).symm

theorem IsCentralExtPermFive.commute_of_eq_or_eq_mul (h : IsCentralExtPermFive φ z)
    {x y x₀ y₀ : E} (h₀ : Commute x₀ y₀) (hx : x = x₀ ∨ x = z * x₀)
    (hy : y = y₀ ∨ y = z * y₀) : Commute x y := by
  have h1 : Commute x₀ (z * y₀) := (h.commute x₀).symm.mul_right h₀
  rcases hx with hx | hx <;> rcases hy with hy | hy <;> rw [hx, hy]
  · exact h₀
  · exact h1
  · exact (h.commute y₀).mul_left h₀
  · exact (h.commute _).mul_left h1

theorem injective_vec_two {i j : Fin 5} (h : i ≠ j) : Function.Injective ![i, j] := by
  intro a b hab
  fin_cases a <;> fin_cases b <;> simp_all

theorem injective_vec_four {i j k l : Fin 5} (hij : i ≠ j) (hik : i ≠ k) (hil : i ≠ l)
    (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l) : Function.Injective ![i, j, k, l] := by
  intro a b hab
  fin_cases a <;> fin_cases b <;> simp_all

theorem map_conj_swap {E : Type*} [Group E] (φ : E →* Perm (Fin 5)) {a e : E} {i j : Fin 5}
    (σ : Perm (Fin 5)) (he : φ e = σ) (hφa : φ a = swap i j) :
    φ (e * a * e⁻¹) = swap (σ i) (σ j) := by
  rw [map_mul, map_mul, map_inv, he, hφa, swap_apply_apply]

theorem IsCentralExtPermFive.exists_involution_lift (h : IsCentralExtPermFive φ z) {a : E}
    (ha : a * a = 1) {i j : Fin 5} (hij : i ≠ j) (hφa : φ a = swap i j) {p q : Fin 5}
    (hpq : p ≠ q) : ∃ t : E, t * t = 1 ∧ φ t = swap p q := by
  obtain ⟨σ, hσ⟩ := Perm.exists_extending_pair ![i, j] ![p, q] (injective_vec_two hij)
    (injective_vec_two hpq)
  obtain ⟨e, he⟩ := h.surjective σ
  have hi : σ i = p := hσ 0
  have hj : σ j = q := hσ 1
  refine ⟨e * a * e⁻¹, ?_, ?_⟩
  · calc e * a * e⁻¹ * (e * a * e⁻¹) = e * (a * a) * e⁻¹ := by group
      _ = 1 := by rw [ha]; group
  · rw [map_conj_swap φ σ he hφa, hi, hj]

theorem IsCentralExtPermFive.mul_comm_of_lifts (h : IsCentralExtPermFive φ z) {a b : E}
    (hab : a * b = b * a) {i j k l : Fin 5} (hij : i ≠ j) (hkl : k ≠ l) (hik : i ≠ k)
    (hil : i ≠ l) (hjk : j ≠ k) (hjl : j ≠ l) (hφa : φ a = swap i j) (hφb : φ b = swap k l)
    {p q r s : Fin 5} (hpq : p ≠ q) (hrs : r ≠ s) (hpr : p ≠ r) (hps : p ≠ s) (hqr : q ≠ r)
    (hqs : q ≠ s) {t u : E} (hφt : φ t = swap p q) (hφu : φ u = swap r s) : t * u = u * t := by
  obtain ⟨σ, hσ⟩ := Perm.exists_extending_pair ![i, j, k, l] ![p, q, r, s]
    (injective_vec_four hij hik hil hjk hjl hkl) (injective_vec_four hpq hpr hps hqr hqs hrs)
  obtain ⟨e, he⟩ := h.surjective σ
  have hi : σ i = p := hσ 0
  have hj : σ j = q := hσ 1
  have hk : σ k = r := hσ 2
  have hl : σ l = s := hσ 3
  have h₀ : Commute (e * a * e⁻¹) (e * b * e⁻¹) := by
    show e * a * e⁻¹ * (e * b * e⁻¹) = e * b * e⁻¹ * (e * a * e⁻¹)
    calc e * a * e⁻¹ * (e * b * e⁻¹) = e * (a * b) * e⁻¹ := by group
      _ = e * (b * a) * e⁻¹ := by rw [hab]
      _ = e * b * e⁻¹ * (e * a * e⁻¹) := by group
  have hφa' : φ (e * a * e⁻¹) = swap p q := by rw [map_conj_swap φ σ he hφa, hi, hj]
  have hφb' : φ (e * b * e⁻¹) = swap r s := by rw [map_conj_swap φ σ he hφb, hk, hl]
  exact (h.commute_of_eq_or_eq_mul h₀ (h.eq_or_eq_mul (hφt.trans hφa'.symm))
    (h.eq_or_eq_mul (hφu.trans hφb'.symm))).eq

theorem IsCentralExtPermFive.exists_braid_lift (h : IsCentralExtPermFive φ z) {t u : E}
    (hu : u * u = 1) {p q r : Fin 5} (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r)
    (hφt : φ t = swap p q) (hφu : φ u = swap q r) :
    ∃ u' : E, u' * u' = 1 ∧ φ u' = swap q r ∧ t * u' * t = u' * t * u' := by
  have hφ : φ (t * u * t) = φ (u * t * u) := by
    rw [map_mul, map_mul, map_mul, map_mul, hφt, hφu]
    exact swap_braid hpq hpr hqr
  rcases h.eq_or_eq_mul hφ with h1 | h1
  · exact ⟨u, hu, hφu, h1⟩
  · have hzu : u * z = z * u := (h.commute u).eq.symm
    have hzt : t * z = z * t := (h.commute t).eq.symm
    have hzut : u * t * z = z * (u * t) := (h.commute (u * t)).eq.symm
    refine ⟨z * u, ?_, ?_, ?_⟩
    · calc z * u * (z * u) = z * (u * z) * u := by simp only [mul_assoc]
        _ = z * z * (u * u) := by rw [hzu]; simp only [mul_assoc]
        _ = 1 := by rw [h.mul_self, hu, mul_one]
    · rw [map_mul, h.map_eq_one, one_mul, hφu]
    · have hL : t * (z * u) * t = u * t * u := by
        calc t * (z * u) * t = t * z * u * t := by simp only [mul_assoc]
          _ = z * t * u * t := by rw [hzt]
          _ = z * (t * u * t) := by simp only [mul_assoc]
          _ = z * (z * (u * t * u)) := by rw [h1]
          _ = z * z * (u * t * u) := (mul_assoc _ _ _).symm
          _ = u * t * u := by rw [h.mul_self, one_mul]
      have hR : z * u * t * (z * u) = u * t * u := by
        calc z * u * t * (z * u) = z * (u * t * z) * u := by simp only [mul_assoc]
          _ = z * (z * (u * t)) * u := by rw [hzut]
          _ = z * z * (u * t * u) := by simp only [mul_assoc]
          _ = u * t * u := by rw [h.mul_self, one_mul]
      exact hL.trans hR.symm

theorem IsCentralExtPermFive.exists_section (h : IsCentralExtPermFive φ z) {a b : E}
    (ha : a * a = 1) (hab : a * b = b * a) {i j k l : Fin 5} (hij : i ≠ j)
    (hkl : k ≠ l) (hik : i ≠ k) (hil : i ≠ l) (hjk : j ≠ k) (hjl : j ≠ l)
    (hφa : φ a = swap i j) (hφb : φ b = swap k l) :
    ∃ s : Perm (Fin 5) →* E, ∀ σ, φ (s σ) = σ := by
  have hlift : ∀ p q : Fin 5, p ≠ q → ∃ t : E, t * t = 1 ∧ φ t = swap p q := fun p q hpq =>
    h.exists_involution_lift ha hij hφa hpq
  obtain ⟨x0, hx0, hφ0⟩ := hlift 0 1 (by decide)
  obtain ⟨y1, hy1, hφy1⟩ := hlift 1 2 (by decide)
  obtain ⟨x1, hx1, hφ1, h01⟩ := h.exists_braid_lift hy1 (p := 0) (q := 1) (r := 2) (by decide)
    (by decide) (by decide) hφ0 hφy1
  obtain ⟨y2, hy2, hφy2⟩ := hlift 2 3 (by decide)
  obtain ⟨x2, hx2, hφ2, h12⟩ := h.exists_braid_lift hy2 (p := 1) (q := 2) (r := 3) (by decide)
    (by decide) (by decide) hφ1 hφy2
  obtain ⟨y3, hy3, hφy3⟩ := hlift 3 4 (by decide)
  obtain ⟨x3, hx3, hφ3, h23⟩ := h.exists_braid_lift hy3 (p := 2) (q := 3) (r := 4) (by decide)
    (by decide) (by decide) hφ2 hφy3
  have hc : ∀ {p q r s : Fin 5} {t u : E}, p ≠ q → r ≠ s → p ≠ r → p ≠ s → q ≠ r → q ≠ s →
      φ t = swap p q → φ u = swap r s → t * u = u * t :=
    fun hpq hrs hpr hps hqr hqs ht hu =>
      h.mul_comm_of_lifts hab hij hkl hik hil hjk hjl hφa hφb hpq hrs hpr hps hqr hqs ht hu
  have hc02 : x0 * x2 = x2 * x0 :=
    hc (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hφ0 hφ2
  have hc03 : x0 * x3 = x3 * x0 :=
    hc (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hφ0 hφ3
  have hc13 : x1 * x3 = x3 * x1 :=
    hc (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hφ1 hφ3
  let x : ℕ → E := fun m =>
    if m = 0 then x0 else if m = 1 then x1 else if m = 2 then x2 else if m = 3 then x3 else 1
  have hx : IsCoxeterA 4 x := by
    refine ⟨fun m hm => ?_, fun m hm => ?_, fun m n hmn hn => ?_⟩
    · interval_cases m <;> simp [x, hx0, hx1, hx2, hx3]
    · have hm' : m < 3 := by omega
      interval_cases m
      · simpa [x] using h01
      · simpa [x] using h12
      · simpa [x] using h23
    · have hcases : (m = 0 ∧ n = 2) ∨ (m = 0 ∧ n = 3) ∨ (m = 1 ∧ n = 3) := by omega
      rcases hcases with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · simpa [x] using hc02
      · simpa [x] using hc03
      · simpa [x] using hc13
  obtain ⟨ψ, hψ⟩ := exists_hom_perm 4 x hx
  refine ⟨ψ, fun σ => ?_⟩
  have hcomp : φ.comp ψ = MonoidHom.id _ := by
    refine MonoidHom.eq_of_eqOn_dense (closure_adjSwap 4) ?_
    rintro _ ⟨m, hm, rfl⟩
    have hm' : m < 4 := hm
    show φ (ψ (adjSwap 4 m)) = adjSwap 4 m
    rw [hψ m hm', adjSwap_of_lt hm']
    interval_cases m
    · simpa [x] using hφ0
    · simpa [x] using hφ1
    · simpa [x] using hφ2
    · simpa [x] using hφ3
  exact DFunLike.congr_fun hcomp σ

end Lifts

set_option linter.unusedVariables false in
theorem exists_mulEquiv_of_central_ext_perm_five
    {E : Type*} [Group E] {z : E} (hzc : z ∈ center E) (hz2 : orderOf z = 2)
    (φ : E →* Perm (Fin 5)) (hφs : Function.Surjective φ)
    (hφk : ∀ x : E, φ x = 1 ↔ x ∈ zpowers z)
    {a b : E} (ha : a * a = 1) (hb : b * b = 1) (hab : a * b = b * a)
    {i j k l : Fin 5} (hij : i ≠ j) (hkl : k ≠ l) (hik : i ≠ k) (hil : i ≠ l) (hjk : j ≠ k)
    (hjl : j ≠ l) (hφa : φ a = swap i j) (hφb : φ b = swap k l) :
    Nonempty (E ≃* Multiplicative (ZMod 2) × Perm (Fin 5)) := by
  have hz2' : z ^ 2 = 1 := orderOf_dvd_iff_pow_eq_one.1 (dvd_of_eq hz2)
  have hzz : z * z = 1 := by rw [← sq]; exact hz2'
  have hφz : φ z = 1 := (hφk z).2 (mem_zpowers z)
  have hext : IsCentralExtPermFive φ z := by
    refine ⟨hzc, hzz, hφz, hφs, fun x hx => ?_⟩
    obtain ⟨n, rfl⟩ := mem_zpowers_iff.1 ((hφk x).1 hx)
    rw [← zpow_mod_orderOf, hz2]
    rcases Int.emod_two_eq_zero_or_one n with h0 | h1
    · left
      simp [h0]
    · right
      simp [h1]
  obtain ⟨s, hs⟩ := hext.exists_section ha hab hij hkl hik hil hjk hjl hφa hφb
  have hcomm : ∀ (c : Multiplicative (ZMod 2)) (σ : Perm (Fin 5)),
      Commute (zmodPowHom 2 z hz2' c) (s σ) := fun c σ => by
    rw [zmodPowHom_apply]
    exact (hext.commute (s σ)).pow_left _
  let Θ := (zmodPowHom 2 z hz2').noncommCoprod s hcomm
  have hinj : Function.Injective Θ := by
    rw [injective_iff_map_eq_one]
    rintro ⟨c, σ⟩ hΘ
    rw [MonoidHom.noncommCoprod_apply] at hΘ
    have hσ : σ = 1 := by
      have := congr_arg φ hΘ
      rwa [map_mul, map_one, hs, zmodPowHom_apply, map_pow, hφz, one_pow, one_mul] at this
    rw [hσ, map_one, mul_one] at hΘ
    exact Prod.ext (zmodPowHom_injective hz2' hz2 (hΘ.trans (map_one _).symm)) hσ
  have hsurj : Function.Surjective Θ := fun e => by
    have hy : φ (e * (s (φ e))⁻¹) = 1 := by rw [map_mul, map_inv, hs, mul_inv_cancel]
    rcases hext.eq_one_or_eq _ hy with h1 | h1
    · refine ⟨(1, φ e), ?_⟩
      rw [MonoidHom.noncommCoprod_apply, map_one, one_mul]
      exact (mul_inv_eq_one.1 h1).symm
    · refine ⟨(Multiplicative.ofAdd ((1 : ℕ) : ZMod 2), φ e), ?_⟩
      rw [MonoidHom.noncommCoprod_apply, zmodPowHom_ofAdd_natCast hz2', pow_one]
      exact (mul_inv_eq_iff_eq_mul.1 h1).symm
  exact ⟨(MulEquiv.ofBijective Θ ⟨hinj, hsurj⟩).symm⟩

theorem exists_mulEquiv_of_central_ext_prod_five
    {Q : Type*} [Group Q] {v r : Q} (hv : v ∈ center Q) (hv2 : orderOf v = 2)
    (hr : r ∈ center Q) (hr5 : orderOf r = 5)
    (ψ : Q →* Multiplicative (ZMod 5) × Perm (Fin 5)) (hψs : Function.Surjective ψ)
    (hψk : ∀ x : Q, ψ x = 1 ↔ x ∈ zpowers v)
    {a b : Q} (ha : a * a = 1) (hb : b * b = 1) (hab : a * b = b * a)
    {i j k l : Fin 5} (hij : i ≠ j) (hkl : k ≠ l) (hik : i ≠ k) (hil : i ≠ l) (hjk : j ≠ k)
    (hjl : j ≠ l) (hψa : (ψ a).2 = swap i j) (hψb : (ψ b).2 = swap k l) :
    Nonempty (Q ≃* Multiplicative (ZMod 2) × Multiplicative (ZMod 5) × Perm (Fin 5)) := by
  have hFact : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  let χ : Q →* Multiplicative (ZMod 5) := (MonoidHom.fst _ _).comp ψ
  let E : Subgroup Q := χ.ker
  have hψv : ψ v = 1 := (hψk v).2 (mem_zpowers v)
  have hinv : ∀ y : Q, y * y = 1 → y ∈ E := fun y hy => by
    have h1 : χ y * χ y = 1 := by rw [← map_mul, hy, map_one]
    have key : ∀ x : Multiplicative (ZMod 5), x * x = 1 → x = 1 := by decide
    exact key _ h1
  have hvE : v ∈ E := by
    show χ v = 1
    simp [χ, hψv]
  let φ' : ↥E →* Perm (Fin 5) := ((MonoidHom.snd _ _).comp ψ).comp E.subtype
  have hzc' : (⟨v, hvE⟩ : ↥E) ∈ center ↥E :=
    mem_center_iff.2 fun g => Subtype.ext (mem_center_iff.1 hv g)
  have hz2' : orderOf (⟨v, hvE⟩ : ↥E) = 2 := by rw [Subgroup.orderOf_mk, hv2]
  have hφs' : Function.Surjective φ' := fun σ => by
    obtain ⟨q, hq⟩ := hψs (1, σ)
    refine ⟨⟨q, ?_⟩, by simp [φ', hq]⟩
    show χ q = 1
    simp [χ, hq]
  have hφk' : ∀ x : ↥E, φ' x = 1 ↔ x ∈ zpowers (⟨v, hvE⟩ : ↥E) := by
    intro x
    constructor
    · intro hx
      have hx1 : ψ (x : Q) = 1 := Prod.ext x.2 hx
      obtain ⟨n, hn⟩ := mem_zpowers_iff.1 ((hψk x).1 hx1)
      exact mem_zpowers_iff.2 ⟨n, Subtype.ext (by simpa using hn)⟩
    · rintro ⟨n, rfl⟩
      show (ψ ((⟨v, hvE⟩ ^ n : ↥E) : Q)).2 = 1
      rw [Subgroup.coe_zpow, map_zpow]
      simp [hψv]
  obtain ⟨eE⟩ := exists_mulEquiv_of_central_ext_perm_five hzc' hz2' φ' hφs' hφk'
    (a := ⟨a, hinv a ha⟩) (b := ⟨b, hinv b hb⟩) (Subtype.ext ha) (Subtype.ext hb)
    (Subtype.ext hab) hij hkl hik hil hjk hjl hψa hψb
  have hr5' : r ^ 5 = 1 := orderOf_dvd_iff_pow_eq_one.1 (dvd_of_eq hr5)
  have hψr2 : (ψ r).2 = 1 := by
    refine CFSG.perm_eq_one_of_forall_commute (by simp) fun σ => ?_
    obtain ⟨q, hq⟩ := hψs (1, σ)
    have := congr_arg (fun y => (ψ y).2) (mem_center_iff.1 hr q)
    simpa [hq] using this.symm
  have hχr : χ r ≠ 1 := by
    intro h1
    have h2 : ψ r = 1 := Prod.ext h1 hψr2
    have h52 : orderOf r ∣ orderOf v := orderOf_dvd_of_mem_zpowers ((hψk r).1 h2)
    rw [hr5, hv2] at h52
    omega
  have hχr5' : χ r ^ 5 = 1 := by rw [← map_pow, hr5', map_one]
  have hχr5 : orderOf (χ r) = 5 := orderOf_eq_prime hχr5' hχr
  have hcomm : ∀ (k : Multiplicative (ZMod 5)) (e : ↥E),
      Commute (zmodPowHom 5 r hr5' k) (E.subtype e) := fun k e => by
    rw [zmodPowHom_apply]
    exact (show Commute r (e : Q) from (mem_center_iff.1 hr (e : Q)).symm).pow_left _
  let Θ := (zmodPowHom 5 r hr5').noncommCoprod E.subtype hcomm
  have hinj : Function.Injective Θ := by
    rw [injective_iff_map_eq_one]
    rintro ⟨k, e⟩ h
    rw [MonoidHom.noncommCoprod_apply] at h
    have h1 : χ (zmodPowHom 5 r hr5' k) = 1 := by
      have := congr_arg χ h
      rwa [map_mul, show χ (E.subtype e) = 1 from e.2, mul_one, map_one] at this
    have hk : k = 1 := by
      refine zmodPowHom_injective hχr5' hχr5 ?_
      rw [map_one, zmodPowHom_apply]
      rwa [zmodPowHom_apply, map_pow] at h1
    rw [hk, map_one, one_mul] at h
    exact Prod.ext hk (Subtype.ext h)
  have hsurj : Function.Surjective Θ := fun q => by
    obtain ⟨m, hm⟩ := exists_pow_eq_multiplicative_zmod_five hχr (χ q)
    refine ⟨(Multiplicative.ofAdd (m : ZMod 5), ⟨(r ^ m)⁻¹ * q, ?_⟩), ?_⟩
    · show χ ((r ^ m)⁻¹ * q) = 1
      rw [map_mul, map_inv, map_pow, hm, inv_mul_cancel]
    · rw [MonoidHom.noncommCoprod_apply, zmodPowHom_ofAdd_natCast hr5']
      simp
  let eQ : Multiplicative (ZMod 5) × ↥E ≃* Q := MulEquiv.ofBijective Θ ⟨hinj, hsurj⟩
  exact ⟨eQ.symm.trans ((MulEquiv.prodCongr (MulEquiv.refl _) eE).trans
    ((MulEquiv.prodAssoc.symm.trans (MulEquiv.prodCongr MulEquiv.prodComm (MulEquiv.refl _))).trans
      MulEquiv.prodAssoc))⟩

end CFSG.EvenSporadicStandard.HSStd
