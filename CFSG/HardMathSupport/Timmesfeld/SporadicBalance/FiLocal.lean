module

public import CFSG.HardMathSupport.Timmesfeld.Coordinator.LocalThreeReduction
public import CFSG.HardMathSupport.Timmesfeld.Proving.GLAPPrimeCoreBasics

public section

namespace CFSG.HardMathSupport.Timmesfeld.SporadicBalance

open CFSG.Open CFSG.HardMathSupport.Timmesfeld.Proving CFSG.HardMathSupport.Timmesfeld.Coordinator

variable {G : Type*} [Group G]

theorem eq_one_or_eq_of_mem_zpowers {x y : G} (hx : x * x = 1) (hy : y ∈ Subgroup.zpowers x) :
    y = 1 ∨ y = x := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
  have h2 : x ^ (2 : ℤ) = 1 := by rw [zpow_two, hx]
  rcases Int.even_or_odd' k with ⟨m, rfl | rfl⟩
  · left
    rw [zpow_mul, h2, one_zpow]
  · right
    rw [zpow_add, zpow_mul, h2, one_zpow, one_mul, zpow_one]

theorem eq_one_of_conj_eq_mul {a b g : G} (hab : a * b = b * a) (ha : a * a = 1)
    (hb : b * b * b = 1) (h : g * b * g⁻¹ = a * b) : a = 1 := by
  have h1 : g * b * g⁻¹ * (g * b * g⁻¹) * (g * b * g⁻¹) = 1 := by
    calc g * b * g⁻¹ * (g * b * g⁻¹) * (g * b * g⁻¹) = g * (b * b * b) * g⁻¹ := by group
      _ = 1 := by rw [hb, mul_one, mul_inv_cancel]
  rw [h] at h1
  have hc : Commute a b := hab
  have hp : (a * b) ^ 3 = a ^ 3 * b ^ 3 := hc.mul_pow 3
  rw [pow_three', pow_three', pow_three'] at hp
  have e1 : a * a * a * (b * b * b) = a := by rw [ha, hb, one_mul, mul_one]
  rw [← e1, ← hp]
  exact h1

theorem conj_mem_gLAPPrimeCoreOf_centralizer {p : ℕ} (g s x : G)
    (hx : x ∈ GLAPPrimeCoreOf p (Subgroup.centralizer ({s} : Set G))) :
    g * x * g⁻¹ ∈ GLAPPrimeCoreOf p (Subgroup.centralizer ({g * s * g⁻¹} : Set G)) := by
  have hψ : Function.Injective (MulAut.conj g : G ≃* G).toMonoidHom :=
    (MulAut.conj g : G ≃* G).injective
  have hmap := map_glaPPrimeCoreOf_of_injective p (MulAut.conj g : G ≃* G).toMonoidHom hψ
    (Subgroup.centralizer ({s} : Set G))
  have hc := map_inf_centralizer_of_injective (MulAut.conj g : G ≃* G).toMonoidHom hψ ⊤ s
  rw [top_inf_eq, Subgroup.map_top_of_surjective _ (MulAut.conj g : G ≃* G).surjective,
    top_inf_eq] at hc
  rw [hc] at hmap
  have hs : (MulAut.conj g : G ≃* G).toMonoidHom s = g * s * g⁻¹ := by
    simp [MulAut.conj_apply]
  rw [hs] at hmap
  rw [← hmap]
  exact Subgroup.mem_map.2 ⟨x, hx, by simp [MulAut.conj_apply]⟩

theorem eq_one_of_mem_gLAPPrimeCoreOf_of_cube [Finite G] {C : Subgroup G} {z : G}
    (hz : z ∈ GLAPPrimeCoreOf 3 C) (h3 : z * z * z = 1) : z = 1 := by
  have hcop := coprime_card_GLAPPrimeCoreOf Nat.prime_three C
  have hdvd : orderOf z ∣ Nat.card (GLAPPrimeCoreOf 3 C) := Subgroup.orderOf_dvd_natCard _ hz
  have h3' : orderOf z ∣ 3 := orderOf_dvd_of_pow_eq_one (by rw [pow_three']; exact h3)
  have h1 : orderOf z ∣ 1 := by
    have := Nat.dvd_gcd h3' hdvd
    rwa [Nat.Coprime.gcd_eq_one hcop] at this
  exact orderOf_eq_one_iff.1 (Nat.dvd_one.1 h1)

theorem gLAPPrimeCoreOf_eq_bot_of_two_fixed [Finite G] {E : Set G} (hE2 : ∀ e ∈ E, e * e = 1)
    (hE1 : ∀ e ∈ E, e ≠ 1)
    (hE3 : ∀ e ∈ E, ∀ f ∈ E, e * f ≠ f * e → e * f * (e * f) * (e * f) = 1)
    (hEc : ∀ e ∈ E, ∀ g : G, g * e * g⁻¹ ∈ E) (s e f : G) (he : e ∈ E) (hf : f ∈ E)
    (hef : e ≠ f) (hes : e * s = s * e) (hfs : f * s = s * f)
    (hloc : ∀ x ∈ E, x * s = s * x → ∀ n ∈ GLAPPrimeCoreOf 3 (Subgroup.centralizer ({s} : Set G)),
      n * x = x * n → n = 1 ∨ n = x) :
    GLAPPrimeCoreOf 3 (Subgroup.centralizer ({s} : Set G)) = ⊥ := by
  set N := GLAPPrimeCoreOf 3 (Subgroup.centralizer ({s} : Set G)) with hN
  have heC : e ∈ Subgroup.centralizer ({s} : Set G) :=
    (Subgroup.mem_centralizer_singleton_iff (g := s)).2 hes
  have hfC : f ∈ Subgroup.centralizer ({s} : Set G) :=
    (Subgroup.mem_centralizer_singleton_iff (g := s)).2 hfs
  have hei : e⁻¹ = e := inv_eq_of_mul_eq_one_right (hE2 e he)
  have hfi : f⁻¹ = f := inv_eq_of_mul_eq_one_right (hE2 f hf)
  have heN : e ∉ N := by
    intro heN
    by_cases hc : e * f = f * e
    · rcases hloc f hf hfs e heN hc with h | h
      · exact hE1 e he h
      · exact hef h
    · have hz : e * (f * e * f⁻¹) ∈ N := N.mul_mem heN (GLAPPrimeCoreOf_conj_mem f hfC e heN)
      have h3 := hE3 e he f hf hc
      have hz3 : e * (f * e * f⁻¹) * (e * (f * e * f⁻¹)) * (e * (f * e * f⁻¹)) = 1 := by
        rw [hfi]
        calc e * (f * e * f) * (e * (f * e * f)) * (e * (f * e * f))
            = e * f * (e * f) * (e * f) * (e * f * (e * f) * (e * f)) := by group
          _ = 1 := by rw [h3, one_mul]
      have h1 := eq_one_of_mem_gLAPPrimeCoreOf_of_cube hz hz3
      rw [hfi] at h1
      have h4 : e * f * (e * f) = 1 := by
        calc e * f * (e * f) = e * (f * e * f) := by group
          _ = 1 := h1
      have h5 : e * f = 1 := by
        have h6 := h3
        rw [h4, one_mul] at h6
        exact h6
      apply hc
      have : e = f := by
        rw [← hfi]
        exact eq_inv_of_mul_eq_one_left h5
      rw [this]
  rw [eq_bot_iff]
  intro n hn
  rw [Subgroup.mem_bot]
  have he'E : n⁻¹ * e * n ∈ E := by simpa using hEc e he n⁻¹
  have hz : e * (n⁻¹ * e * n) ∈ N := by
    have h1 : e * n⁻¹ * e⁻¹ ∈ N := GLAPPrimeCoreOf_conj_mem e heC _ (N.inv_mem hn)
    have h2 : e * (n⁻¹ * e * n) = e * n⁻¹ * e⁻¹ * n := by rw [hei]; group
    rw [h2]
    exact N.mul_mem h1 hn
  have hc : e * (n⁻¹ * e * n) = n⁻¹ * e * n * e := by
    by_contra hc
    have h1 := eq_one_of_mem_gLAPPrimeCoreOf_of_cube hz (hE3 e he _ he'E hc)
    apply hc
    have : n⁻¹ * e * n = e := (eq_inv_of_mul_eq_one_right h1).trans hei
    rw [this]
  have hz1 : e * (n⁻¹ * e * n) = 1 := by
    have hcomm : e * (n⁻¹ * e * n) * e = e * (e * (n⁻¹ * e * n)) := by
      calc e * (n⁻¹ * e * n) * e = e * (n⁻¹ * e * n * e) := by group
        _ = e * (e * (n⁻¹ * e * n)) := by rw [← hc]
    rcases hloc e he hes _ hz hcomm with h | h
    · exact h
    · exfalso
      have h1 : n⁻¹ * e * n = 1 := by
        have := congrArg (e⁻¹ * ·) h
        simpa using this
      exact hE1 _ he'E h1
  have hne : n * e = e * n := by
    have h1 : n⁻¹ * e * n = e := (eq_inv_of_mul_eq_one_right hz1).trans hei
    calc n * e = n * (n⁻¹ * e * n) := by rw [h1]
      _ = e * n := by group
  rcases hloc e he hes n hn hne with h | h
  · exact h
  · exact absurd (h ▸ hn) heN

end CFSG.HardMathSupport.Timmesfeld.SporadicBalance
