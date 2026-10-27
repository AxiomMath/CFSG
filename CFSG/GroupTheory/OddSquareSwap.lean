module

public import CFSG.GroupTheory.OddInversion
import Mathlib.Tactic.IntervalCases

public section

namespace CFSG.OddInversion

variable {G : Type*} [Group G]

theorem card_eq_sq_of_conj_swap {A : Subgroup G} (hA : Odd (Nat.card A)) {e f z : G}
    (he : orderOf e = 2) (heN : e ∈ Subgroup.normalizer (A : Set G))
    (hfN : f ∈ Subgroup.normalizer (A : Set G)) (hz : ∀ v ∈ A, z * v * z⁻¹ = v⁻¹)
    (hzf : z * f = f * z) (hfe : f * e * f⁻¹ = e * z) :
    Nat.card A = Nat.card ↥(A ⊓ Subgroup.centralizer {e}) ^ 2 := by
  classical
  have : Finite A := finite_of_odd_card hA
  have hAfin : (A : Set G).Finite := Set.toFinite _
  set C := A ⊓ Subgroup.centralizer {e} with hC
  have hz' : ∀ v ∈ A, z⁻¹ * v * z = v⁻¹ := by
    intro v hv
    have h := hz _ (A.inv_mem hv)
    rw [inv_inv] at h
    calc z⁻¹ * v * z = z⁻¹ * (z * v⁻¹ * z⁻¹) * z := by rw [h]
      _ = v⁻¹ := by group
  have hfe' : f⁻¹ * e * f = e * z⁻¹ := by
    have h1 : e = f⁻¹ * (e * z) * f := by rw [← hfe]; group
    have h2 : f⁻¹ * (e * z) * f = f⁻¹ * e * f * z := by
      calc f⁻¹ * (e * z) * f = f⁻¹ * e * (z * f) := by group
        _ = f⁻¹ * e * (f * z) := by rw [hzf]
        _ = f⁻¹ * e * f * z := by group
    rw [h2] at h1
    calc f⁻¹ * e * f = f⁻¹ * e * f * z * z⁻¹ := by group
      _ = e * z⁻¹ := by rw [← h1]
  have hmaps : Set.MapsTo (fun v => f * v * f⁻¹) (C : Set G) (invertedSet A e) := by
    intro v hv
    obtain ⟨hvA, hvC⟩ := Subgroup.mem_inf.1 hv
    have hve : v * e = e * v := Subgroup.mem_centralizer_singleton_iff.1 hvC
    refine ⟨conj_mem_of_mem_normalizer hfN hvA, ?_⟩
    have hzv := hz' v hvA
    have hev : e * v⁻¹ * e⁻¹ = v⁻¹ := by
      rw [show e * v⁻¹ * e⁻¹ = (e * v * e⁻¹)⁻¹ by group, ← hve]
      group
    calc e * (f * v * f⁻¹) * e⁻¹ = f * ((f⁻¹ * e * f) * v * (f⁻¹ * e * f)⁻¹) * f⁻¹ := by group
      _ = f * (e * (z⁻¹ * v * z) * e⁻¹) * f⁻¹ := by rw [hfe']; group
      _ = f * (e * v⁻¹ * e⁻¹) * f⁻¹ := by rw [hzv]
      _ = f * v⁻¹ * f⁻¹ := by rw [hev]
      _ = (f * v * f⁻¹)⁻¹ := by group
  have hmaps' : Set.MapsTo (fun w => f⁻¹ * w * f) (invertedSet A e) (C : Set G) := by
    intro w hw
    obtain ⟨hwA, hwe⟩ := hw
    have hfiN : f⁻¹ ∈ Subgroup.normalizer (A : Set G) := Subgroup.inv_mem _ hfN
    have hA' : f⁻¹ * w * f ∈ A := by
      have := conj_mem_of_mem_normalizer hfiN hwA
      rwa [inv_inv] at this
    refine Subgroup.mem_inf.2 ⟨hA', Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
    have hzw := hz w hwA
    have key : e * (f⁻¹ * w * f) * e⁻¹ = f⁻¹ * w * f := by
      calc e * (f⁻¹ * w * f) * e⁻¹ = f⁻¹ * ((f * e * f⁻¹) * w * (f * e * f⁻¹)⁻¹) * f := by group
        _ = f⁻¹ * (e * (z * w * z⁻¹) * e⁻¹) * f := by rw [hfe]; group
        _ = f⁻¹ * (e * w⁻¹ * e⁻¹) * f := by rw [hzw]
        _ = f⁻¹ * (e * w * e⁻¹)⁻¹ * f := by group
        _ = f⁻¹ * w * f := by rw [hwe, inv_inv]
    show (f⁻¹ * w * f) * e = e * (f⁻¹ * w * f)
    calc (f⁻¹ * w * f) * e = (e * (f⁻¹ * w * f) * e⁻¹) * e := by rw [key]
      _ = e * (f⁻¹ * w * f) := by group
  have hinj : Set.InjOn (fun v => f * v * f⁻¹) (C : Set G) :=
    fun v _ w _ h => by simpa using h
  have hinj' : Set.InjOn (fun w => f⁻¹ * w * f) (invertedSet A e) :=
    fun v _ w _ h => by simpa using h
  have hIfin : (invertedSet A e).Finite := hAfin.subset fun d hd => hd.1
  have hCfin : (C : Set G).Finite := hAfin.subset fun d hd => (Subgroup.mem_inf.1 hd).1
  have hle1 := Set.ncard_le_ncard_of_injOn _ (fun v hv => hmaps hv) hinj hIfin
  have hle2 := Set.ncard_le_ncard_of_injOn _ (fun w hw => hmaps' hw) hinj' hCfin
  have hCI : (C : Set G).ncard = (invertedSet A e).ncard := le_antisymm hle1 hle2
  have hbij := fixed_mul_inverted_bijOn hA he heN
  have hprod : (A : Set G).ncard = (C : Set G).ncard * (invertedSet A e).ncard := by
    rw [← hbij.image_eq, hbij.injOn.ncard_image, Set.ncard_prod]
  have hAc : Nat.card A = (A : Set G).ncard := Nat.card_coe_set_eq (A : Set G)
  have hCc : Nat.card C = (C : Set G).ncard := Nat.card_coe_set_eq (C : Set G)
  rw [hAc, hCc, hprod, ← hCI, sq]

theorem normalizer_inf_centralizer {A : Subgroup G} {g e' : G}
    (hgN : g ∈ Subgroup.normalizer (A : Set G)) (hge : g * e' = e' * g) :
    g ∈ Subgroup.normalizer ((A ⊓ Subgroup.centralizer {e'} : Subgroup G) : Set G) := by
  have hge' : g⁻¹ * e' = e' * g⁻¹ := by
    calc g⁻¹ * e' = g⁻¹ * (e' * g) * g⁻¹ := by group
      _ = g⁻¹ * (g * e') * g⁻¹ := by rw [hge]
      _ = e' * g⁻¹ := by group
  rw [Subgroup.mem_normalizer_iff]
  intro v
  constructor
  · intro hv
    obtain ⟨hvA, hvC⟩ := Subgroup.mem_inf.1 hv
    refine Subgroup.mem_inf.2 ⟨conj_mem_of_mem_normalizer hgN hvA,
      Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
    have hve : v * e' = e' * v := Subgroup.mem_centralizer_singleton_iff.1 hvC
    calc g * v * g⁻¹ * e' = g * v * (g⁻¹ * e') := by group
      _ = g * v * (e' * g⁻¹) := by rw [hge']
      _ = g * (v * e') * g⁻¹ := by group
      _ = g * (e' * v) * g⁻¹ := by rw [hve]
      _ = (g * e') * v * g⁻¹ := by group
      _ = (e' * g) * v * g⁻¹ := by rw [hge]
      _ = e' * (g * v * g⁻¹) := by group
  · intro hv
    obtain ⟨hvA, hvC⟩ := Subgroup.mem_inf.1 hv
    have hgiN : g⁻¹ ∈ Subgroup.normalizer (A : Set G) := Subgroup.inv_mem _ hgN
    have hvA' : v ∈ A := by
      have := conj_mem_of_mem_normalizer hgiN hvA
      rwa [show g⁻¹ * (g * v * g⁻¹) * g⁻¹⁻¹ = v by group] at this
    refine Subgroup.mem_inf.2 ⟨hvA', Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
    have hve : g * v * g⁻¹ * e' = e' * (g * v * g⁻¹) :=
      Subgroup.mem_centralizer_singleton_iff.1 hvC
    calc v * e' = g⁻¹ * (g * v * g⁻¹ * (g * e')) := by group
      _ = g⁻¹ * (g * v * g⁻¹ * (e' * g)) := by rw [hge]
      _ = g⁻¹ * ((g * v * g⁻¹ * e') * g) := by group
      _ = g⁻¹ * ((e' * (g * v * g⁻¹)) * g) := by rw [hve]
      _ = g⁻¹ * (e' * g) * v := by group
      _ = g⁻¹ * (g * e') * v := by rw [hge]
      _ = e' * v := by group

theorem card_eq_pow_sixteen {A : Subgroup G} (hA : Odd (Nat.card A)) {z : G} (e f : Fin 4 → G)
    (he : ∀ i, orderOf (e i) = 2) (heN : ∀ i, e i ∈ Subgroup.normalizer (A : Set G))
    (hfN : ∀ i, f i ∈ Subgroup.normalizer (A : Set G)) (hz : ∀ v ∈ A, z * v * z⁻¹ = v⁻¹)
    (hzf : ∀ i, z * f i = f i * z)
    (hee : ∀ i j, e i * e j = e j * e i) (hfe : ∀ i, f i * e i * (f i)⁻¹ = e i * z)
    (hfe' : ∀ i j, i ≠ j → f j * e i = e i * f j) :
    ∃ k : ℕ, Nat.card A = k ^ 16 := by
  set A₁ := A ⊓ Subgroup.centralizer {e 0}
  set A₂ := A₁ ⊓ Subgroup.centralizer {e 1}
  set A₃ := A₂ ⊓ Subgroup.centralizer {e 2}
  set A₄ := A₃ ⊓ Subgroup.centralizer {e 3}
  have hodd : ∀ {B : Subgroup G}, B ≤ A → Odd (Nat.card B) := fun hB =>
    Odd.of_dvd_nat hA (Subgroup.card_dvd_of_le hB)
  have h12 : A₁ ≤ A := inf_le_left
  have h23 : A₂ ≤ A := inf_le_left.trans h12
  have h34 : A₃ ≤ A := inf_le_left.trans h23
  have nA₁ : ∀ g, g ∈ Subgroup.normalizer (A : Set G) → g * e 0 = e 0 * g →
      g ∈ Subgroup.normalizer (A₁ : Set G) := fun g hg hge => normalizer_inf_centralizer hg hge
  have nA₂ : ∀ g, g ∈ Subgroup.normalizer (A : Set G) → g * e 0 = e 0 * g →
      g * e 1 = e 1 * g → g ∈ Subgroup.normalizer (A₂ : Set G) := fun g hg h0 h1 =>
    normalizer_inf_centralizer (nA₁ g hg h0) h1
  have nA₃ : ∀ g, g ∈ Subgroup.normalizer (A : Set G) → g * e 0 = e 0 * g →
      g * e 1 = e 1 * g → g * e 2 = e 2 * g → g ∈ Subgroup.normalizer (A₃ : Set G) :=
    fun g hg h0 h1 h2 => normalizer_inf_centralizer (nA₂ g hg h0 h1) h2
  have s0 := card_eq_sq_of_conj_swap hA (he 0) (heN 0) (hfN 0) hz (hzf 0) (hfe 0)
  have s1 := card_eq_sq_of_conj_swap (hodd h12) (he 1) (nA₁ _ (heN 1) (hee 1 0))
    (nA₁ _ (hfN 1) (hfe' 0 1 (by decide))) (fun v hv => hz v (h12 hv)) (hzf 1) (hfe 1)
  have s2 := card_eq_sq_of_conj_swap (hodd h23) (he 2)
    (nA₂ _ (heN 2) (hee 2 0) (hee 2 1))
    (nA₂ _ (hfN 2) (hfe' 0 2 (by decide)) (hfe' 1 2 (by decide)))
    (fun v hv => hz v (h23 hv)) (hzf 2) (hfe 2)
  have s3 := card_eq_sq_of_conj_swap (hodd h34) (he 3)
    (nA₃ _ (heN 3) (hee 3 0) (hee 3 1) (hee 3 2))
    (nA₃ _ (hfN 3) (hfe' 0 3 (by decide)) (hfe' 1 3 (by decide)) (hfe' 2 3 (by decide)))
    (fun v hv => hz v (h34 hv)) (hzf 3) (hfe 3)
  refine ⟨Nat.card A₄, ?_⟩
  rw [s0, s1, s2, s3]
  ring

theorem eq_one_of_pow_sixteen_dvd {k : ℕ} (h : k ^ 16 ∣ 90745943887872000) : k = 1 := by
  have hk0 : k ≠ 0 := by
    rintro rfl
    norm_num at h
  by_contra hk1
  obtain ⟨p, hp, hpk⟩ := Nat.exists_prime_and_dvd hk1
  have hp16 : p ^ 16 ∣ 90745943887872000 := (pow_dvd_pow_of_dvd hpk 16).trans h
  have hle : p ^ 16 ≤ 90745943887872000 := Nat.le_of_dvd (by norm_num) hp16
  have hp11 : p ≤ 11 := by
    by_contra hlt
    have h12 : 12 ≤ p := by omega
    have : 12 ^ 16 ≤ p ^ 16 := Nat.pow_le_pow_left h12 16
    omega
  clear hle hpk h hk1 hk0
  revert hp hp16
  interval_cases p <;> decide

end CFSG.OddInversion
