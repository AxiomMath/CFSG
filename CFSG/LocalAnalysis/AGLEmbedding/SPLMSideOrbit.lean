module

public import CFSG.Foundations.Basic
import CFSG.GroupTheory.LocalCores.Components
import CFSG.LocalAnalysis.AGLEmbedding.SPLMSideCore

public section

namespace CFSG.AGLEmbedding.SPLMSide

open Subgroup

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem conj_pow_eq_mul_pow {e t : G}
    (hg : t * (e⁻¹ * (t * e * t⁻¹)) = (e⁻¹ * (t * e * t⁻¹)) * t) (n : ℕ) :
    t ^ n * e * (t ^ n)⁻¹ = e * (e⁻¹ * (t * e * t⁻¹)) ^ n := by
  set g := e⁻¹ * (t * e * t⁻¹) with hgdef
  have htg : t * g * t⁻¹ = g := by rw [hg]; group
  have hte : t * e * t⁻¹ = e * g := by rw [hgdef]; group
  induction n with
  | zero => simp
  | succ n ih =>
    calc t ^ (n + 1) * e * (t ^ (n + 1))⁻¹ = t * (t ^ n * e * (t ^ n)⁻¹) * t⁻¹ := by group
      _ = t * (e * g ^ n) * t⁻¹ := by rw [ih]
      _ = (t * e * t⁻¹) * (t * g * t⁻¹) ^ n := by
          rw [conj_pow]; group
      _ = e * g ^ (n + 1) := by rw [hte, htg, pow_succ']; group

omit [Finite G] in
theorem pow_eq_one_of_quadratic {e t : G}
    (hg : t * (e⁻¹ * (t * e * t⁻¹)) = (e⁻¹ * (t * e * t⁻¹)) * t) {m : ℕ} (htm : t ^ m = 1) :
    (e⁻¹ * (t * e * t⁻¹)) ^ m = 1 := by
  have h := conj_pow_eq_mul_pow hg m
  rw [htm] at h
  simp only [one_mul, inv_one, mul_one] at h
  have := congrArg (fun x => e⁻¹ * x) h
  simpa using this.symm

omit [Finite G] in
theorem mem_zpowers_mul_of_coprime {p : ℕ} [Fact p.Prime] {s o : G} (hs : ∃ k : ℕ, s ^ p ^ k = 1)
    (ho : p.Coprime (orderOf o)) (hso : s * o = o * s) : s ∈ zpowers (s * o) := by
  obtain ⟨k, hk⟩ := hs
  have hcop : (orderOf o).Coprime (orderOf s) := by
    have h1 : orderOf s ∣ p ^ k := orderOf_dvd_of_pow_eq_one hk
    exact Nat.Coprime.coprime_dvd_right h1 (Nat.Coprime.pow_right k ho.symm)
  obtain ⟨j, hj⟩ := exists_pow_eq_self_of_coprime hcop
  have hpow : (s * o) ^ orderOf o = s ^ orderOf o := by
    rw [(Commute.mul_pow hso)]
    rw [pow_orderOf_eq_one, mul_one]
  have key : s = (s * o) ^ (orderOf o * j) := by rw [pow_mul, hpow, hj]
  have h := Subgroup.pow_mem _ (Subgroup.mem_zpowers (s * o)) (orderOf o * j)
  rwa [← key] at h

omit [Finite G] in
theorem eq_one_of_pow_of_coprime {p : ℕ} [Fact p.Prime] {o : G} {k : ℕ} (hk : o ^ p ^ k = 1)
    (ho : p.Coprime (orderOf o)) : o = 1 := by
  have h1 : orderOf o ∣ p ^ k := orderOf_dvd_of_pow_eq_one hk
  have h2 : (orderOf o).Coprime (p ^ k) := Nat.Coprime.pow_right k ho.symm
  have : orderOf o = 1 := Nat.Coprime.eq_one_of_dvd h2 h1
  exact orderOf_eq_one_iff.mp this

omit [Finite G] in
theorem le_or_commutator_mem {p : ℕ} [Fact p.Prime] {C T X O N : Subgroup G}
    (hTC : T ≤ C) (hNC : N ≤ C) (hXT : X ≤ T) (hXN : X ≤ N)
    (hT : IsPGroup p T) (hO : p.Coprime (Nat.card O))
    (hNn : ∀ g ∈ C, ∀ n ∈ N, g * n * g⁻¹ ∈ N)
    (hTOn : ∀ g ∈ C, ∀ t ∈ T, ∃ t' ∈ T, ∃ o ∈ O, g * t * g⁻¹ = t' * o)
    (hTX : ∀ t ∈ T, ∀ x ∈ X, t * x = x * t) (hTO : ∀ t ∈ T, ∀ o ∈ O, t * o = o * t)
    {c : G} (hcC : c ∈ C) (hcT : ∀ t ∈ T, c * t * c⁻¹ ∈ T)
    (hirr : ∀ V : Subgroup G, X ≤ V → V ≤ T → (∀ t ∈ T, ∀ v ∈ V, t * v * t⁻¹ ∈ V) →
      (∀ v ∈ V, c * v * c⁻¹ ∈ V) → V = X ∨ V = T) :
    T ≤ N ∨ ∀ e ∈ N, ∀ t ∈ T, e⁻¹ * (t * e * t⁻¹) ∈ X := by
  have hV := hirr (T ⊓ N) (le_inf hXT hXN) inf_le_left
    (fun t ht v hv => ⟨T.mul_mem (T.mul_mem ht hv.1) (T.inv_mem ht), hNn t (hTC ht) v hv.2⟩)
    (fun v hv => ⟨hcT v hv.1, hNn c hcC v hv.2⟩)
  rcases hV with hV | hV
  · right
    intro e he t ht
    have heC : e ∈ C := hNC he
    obtain ⟨t', ht', o, ho, heq⟩ := hTOn e⁻¹ (C.inv_mem heC) t ht
    have hoord : p.Coprime (orderOf o) :=
      Nat.Coprime.coprime_dvd_right (Subgroup.orderOf_dvd_natCard O ho) hO
    set g := e⁻¹ * (t * e * t⁻¹) with hgdef
    have hgN : g ∈ N := N.mul_mem (N.inv_mem he) (hNn t (hTC ht) e he)
    have hs : t' * t⁻¹ ∈ T := T.mul_mem ht' (T.inv_mem ht)
    have hto : t * o * t⁻¹ = o := by rw [hTO t ht o ho]; group
    have hgso : g = (t' * t⁻¹) * o := by
      have h1 : e⁻¹ * t * e = t' * o := by simpa using heq
      calc g = (e⁻¹ * t * e) * t⁻¹ := by rw [hgdef]; group
        _ = t' * o * t⁻¹ := by rw [h1]
        _ = (t' * t⁻¹) * (t * o * t⁻¹) := by group
        _ = (t' * t⁻¹) * o := by rw [hto]
    have hsp : ∃ k : ℕ, (t' * t⁻¹) ^ p ^ k = 1 := by
      obtain ⟨k, hk⟩ := hT ⟨_, hs⟩
      exact ⟨k, by simpa using congrArg Subtype.val hk⟩
    have hso : (t' * t⁻¹) * o = o * (t' * t⁻¹) := hTO _ hs o ho
    have hsN : t' * t⁻¹ ∈ N := by
      have := mem_zpowers_mul_of_coprime hsp hoord hso
      rw [← hgso] at this
      exact (zpowers_le.mpr hgN) this
    have hsX : t' * t⁻¹ ∈ X := by rw [← hV]; exact ⟨hs, hsN⟩
    have htg : t * g = g * t := by
      rw [hgso]
      have h1 := hTX t ht _ hsX
      have h2 := hTO t ht o ho
      calc t * ((t' * t⁻¹) * o) = (t * (t' * t⁻¹)) * o := by group
        _ = ((t' * t⁻¹) * t) * o := by rw [h1]
        _ = (t' * t⁻¹) * (t * o) := by group
        _ = (t' * t⁻¹) * (o * t) := by rw [h2]
        _ = _ := by group
    obtain ⟨k, hk⟩ := hT ⟨t, ht⟩
    have htk : t ^ p ^ k = 1 := by simpa using congrArg Subtype.val hk
    have hgk : g ^ p ^ k = 1 := pow_eq_one_of_quadratic htg htk
    obtain ⟨j, hj⟩ := hsp
    have hok : o ^ p ^ (k + j) = 1 := by
      have h1 : g ^ p ^ (k + j) = 1 := by rw [pow_add, pow_mul, hgk, one_pow]
      rw [hgso, (Commute.mul_pow hso)] at h1
      have h2 : (t' * t⁻¹) ^ p ^ (k + j) = 1 := by
        rw [pow_add, mul_comm, pow_mul, hj, one_pow]
      rw [h2, one_mul] at h1
      exact h1
    have ho1 : o = 1 := eq_one_of_pow_of_coprime hok hoord
    rw [hgso, ho1, mul_one]
    exact hsX
  · left
    rw [← hV]
    exact inf_le_right

omit [Finite G] in
theorem mem_map_conj_iff {Λ : Subgroup G} {g x : G} :
    x ∈ Λ.map (MulAut.conj g).toMonoidHom ↔ g⁻¹ * x * g ∈ Λ := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa [MulAut.conj_apply, mul_assoc] using hy
  · intro hx
    exact ⟨g⁻¹ * x * g, hx, by simp [MulAut.conj_apply, mul_assoc]⟩

omit [Finite G] in
theorem mem_normalizer_of_map_conj_eq {Λ : Subgroup G} {g : G}
    (h : Λ.map (MulAut.conj g).toMonoidHom = Λ) : g ∈ Subgroup.normalizer (Λ : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    rw [← h, mem_map_conj_iff]
    simpa [mul_assoc] using hx
  · intro hx
    rw [← h, mem_map_conj_iff] at hx
    simpa [mul_assoc] using hx

omit [Finite G] in
theorem conj_mem_normalizer {Λ : Subgroup G} {g n : G}
    (hn : n ∈ Subgroup.normalizer ((Λ.map (MulAut.conj g⁻¹).toMonoidHom : Subgroup G) : Set G)) :
    g * n * g⁻¹ ∈ Subgroup.normalizer (Λ : Set G) := by
  rw [Subgroup.mem_normalizer_iff] at hn ⊢
  intro h
  have h1 := hn (g⁻¹ * h * g)
  rw [mem_map_conj_iff, mem_map_conj_iff] at h1
  simp only [inv_inv] at h1
  have e1 : g * (g⁻¹ * h * g) * g⁻¹ = h := by group
  have e2 : g * (n * (g⁻¹ * h * g) * n⁻¹) * g⁻¹ = g * n * g⁻¹ * h * (g * n * g⁻¹)⁻¹ := by group
  rw [e1, e2] at h1
  exact h1

theorem commute_of_ne {Λ Λ' : Subgroup G} (hΛ : CFSG.IsComponent Λ)
    (hΛ' : CFSG.IsComponent Λ') (hne : Λ' ≠ Λ) : ∀ a ∈ Λ, ∀ b ∈ Λ', a * b = b * a := by
  rcases CFSG.LocalCores.distinct_components_commute hΛ hΛ' with h | h
  · exact absurd h.symm hne
  · intro a ha b hb
    have := Subgroup.commutator_eq_bot_iff_le_centralizer.mp h ha
    exact (Subgroup.mem_centralizer_iff.mp this b hb).symm

theorem mem_normalizer_of_mem_component {Λ Λ' : Subgroup G} (hΛ : CFSG.IsComponent Λ)
    (hΛ' : CFSG.IsComponent Λ') {a : G} (ha : a ∈ Λ) :
    a ∈ Subgroup.normalizer (Λ' : Set G) := by
  by_cases h : Λ' = Λ
  · subst h
    exact Subgroup.le_normalizer ha
  · have hc := commute_of_ne hΛ hΛ' h
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      have : a * x * a⁻¹ = x := by rw [hc a ha x hx]; group
      rw [this]; exact hx
    · intro hx
      have hx' : a⁻¹ * (a * x * a⁻¹) * a ∈ Λ' := by
        have h2 := hc a ha _ hx
        have : a⁻¹ * (a * x * a⁻¹) * a = a * x * a⁻¹ := by
          calc a⁻¹ * (a * x * a⁻¹) * a = a⁻¹ * ((a * x * a⁻¹) * a) := by group
            _ = a⁻¹ * (a * (a * x * a⁻¹)) := by rw [h2]
            _ = a * x * a⁻¹ := by group
        rw [this]; exact hx
      simpa [mul_assoc] using hx'

theorem le_normalizer_of_components {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {u : G}
    (hup : u ^ p = 1)
    (hu : ∀ Λ : Subgroup G, CFSG.IsComponent Λ → u ∈ Subgroup.normalizer (Λ : Set G))
    {T X O : Subgroup G} {c : G}
    (hTC : T ≤ Subgroup.centralizer ({u} : Set G)) (hXT : X ≤ T)
    (hT : IsPGroup p T) (hO : p.Coprime (Nat.card O))
    (hTOn : ∀ g ∈ Subgroup.centralizer ({u} : Set G), ∀ t ∈ T,
      ∃ t' ∈ T, ∃ o ∈ O, g * t * g⁻¹ = t' * o)
    (hTX : ∀ t ∈ T, ∀ x ∈ X, t * x = x * t) (hTO : ∀ t ∈ T, ∀ o ∈ O, t * o = o * t)
    (hcC : c ∈ Subgroup.centralizer ({u} : Set G)) (hcT : ∀ t ∈ T, c * t * c⁻¹ ∈ T)
    (hirr : ∀ V : Subgroup G, X ≤ V → V ≤ T → (∀ t ∈ T, ∀ v ∈ V, t * v * t⁻¹ ∈ V) →
      (∀ v ∈ V, c * v * c⁻¹ ∈ V) → V = X ∨ V = T)
    (hXE : ∀ Λ : Subgroup G, CFSG.IsComponent Λ → ∀ x ∈ X, ∀ a ∈ Λ, x * a = a * x)
    (hZX : ∀ Λ : Subgroup G, CFSG.IsComponent Λ → ∀ φ ∈ Λ, (∀ a ∈ Λ, a * φ = φ * a) →
      (∃ k : ℕ, φ ^ p ^ k = 1) → φ ∈ X) :
    ∀ Λ : Subgroup G, CFSG.IsComponent Λ → T ≤ Subgroup.normalizer (Λ : Set G) := by
  classical
  set C := Subgroup.centralizer ({u} : Set G) with hCdef
  let N : Subgroup G := C ⊓ ⨅ (Λ : Subgroup G) (_ : CFSG.IsComponent Λ),
    Subgroup.normalizer (Λ : Set G)
  have hmemN : ∀ g : G, g ∈ N ↔ g ∈ C ∧ ∀ Λ : Subgroup G, CFSG.IsComponent Λ →
      g ∈ Subgroup.normalizer (Λ : Set G) := by
    intro g
    simp only [N, Subgroup.mem_inf, Subgroup.mem_iInf]
  have hNC : N ≤ C := fun g hg => ((hmemN g).mp hg).1
  have hXN : X ≤ N := by
    intro x hx
    refine (hmemN x).mpr ⟨hTC (hXT hx), fun Λ hΛ => ?_⟩
    rw [Subgroup.mem_normalizer_iff]
    intro a
    have hc := hXE Λ hΛ x hx
    constructor
    · intro ha
      have : x * a * x⁻¹ = a := by rw [hc a ha]; group
      rw [this]; exact ha
    · intro ha
      have h1 := hc (x * a * x⁻¹) ha
      have h2 : x * a * x⁻¹ = a := by
        calc x * a * x⁻¹ = x⁻¹ * (x * (x * a * x⁻¹)) := by group
          _ = x⁻¹ * ((x * a * x⁻¹) * x) := by rw [h1]
          _ = a := by group
      rw [← h2]; exact ha
  have hNn : ∀ g ∈ C, ∀ n ∈ N, g * n * g⁻¹ ∈ N := by
    intro g hg n hn
    obtain ⟨hnC, hnN⟩ := (hmemN n).mp hn
    refine (hmemN _).mpr ⟨C.mul_mem (C.mul_mem hg hnC) (C.inv_mem hg), fun Λ hΛ => ?_⟩
    exact conj_mem_normalizer
      (hnN _ (CFSG.LocalCores.isComponent_map_mulEquiv (MulAut.conj g⁻¹) hΛ))
  rcases le_or_commutator_mem (C := C) (N := N) hTC hNC hXT hXN hT hO hNn hTOn hTX hTO
    hcC hcT hirr with hTN | hcomm
  · intro Λ hΛ t ht
    exact ((hmemN t).mp (hTN ht)).2 Λ hΛ
  intro Λ hΛ t ht
  by_contra htΛ
  have htu : t ∈ C := hTC ht
  have hut : u * t = t * u := Subgroup.mem_centralizer_iff.mp htu u (Set.mem_singleton u)
  set Λ₁ := Λ.map (MulAut.conj t).toMonoidHom with hΛ₁
  set Λ₂ := Λ₁.map (MulAut.conj t).toMonoidHom with hΛ₂
  have hc₁ : CFSG.IsComponent Λ₁ := CFSG.LocalCores.isComponent_map_mulEquiv _ hΛ
  have hc₂ : CFSG.IsComponent Λ₂ := CFSG.LocalCores.isComponent_map_mulEquiv _ hc₁
  have hne₁ : Λ₁ ≠ Λ := fun h => htΛ (mem_normalizer_of_map_conj_eq h)
  have hne₂ : Λ₂ ≠ Λ := by
    intro h
    have h2 : t * t ∈ Subgroup.normalizer (Λ : Set G) := by
      apply mem_normalizer_of_map_conj_eq
      ext x
      have e : t⁻¹ * (t⁻¹ * x * t) * t = (t * t)⁻¹ * x * (t * t) := by group
      have e1 : x ∈ Λ₂ ↔ t⁻¹ * x * t ∈ Λ₁ := mem_map_conj_iff
      have e2 : t⁻¹ * x * t ∈ Λ₁ ↔ t⁻¹ * (t⁻¹ * x * t) * t ∈ Λ := mem_map_conj_iff
      rw [mem_map_conj_iff, ← e, ← e2, ← e1, h]
    obtain ⟨k, hk⟩ := hT ⟨t, ht⟩
    have htk : t ^ p ^ k = 1 := by simpa using congrArg Subtype.val hk
    have hodd : (2 : ℕ).Coprime (orderOf t) := by
      have h1 : orderOf t ∣ p ^ k := orderOf_dvd_of_pow_eq_one htk
      have hp2' : (2 : ℕ).Coprime p :=
        (Nat.coprime_primes Nat.prime_two (Fact.out : p.Prime)).mpr (Ne.symm hp2)
      exact Nat.Coprime.coprime_dvd_right h1 (Nat.Coprime.pow_right k hp2')
    obtain ⟨j, hj⟩ := exists_pow_eq_self_of_coprime hodd
    apply htΛ
    rw [← hj, pow_two]
    exact Subgroup.pow_mem _ h2 j
  have hco₁ := commute_of_ne hΛ hc₁ hne₁
  have hco₂ := commute_of_ne hΛ hc₂ hne₂
  refine false_of_moved_component (Z₀ := X) hΛ.1 (hu Λ hΛ) hup hut ?_ ?_
    (fun a ha x hx => (hXE Λ hΛ x hx a ha).symm) ?_ ?_
  · intro a ha b hb
    exact hco₁ a ha _ ⟨b, hb, rfl⟩
  · intro a ha b hb
    exact hco₂ a ha _ ⟨t * b * t⁻¹, ⟨b, hb, rfl⟩, rfl⟩
  · intro a ha b hb hcu
    have heC : a * (t * b * t⁻¹) ∈ C := by
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      rw [Set.mem_singleton_iff] at hx
      subst hx
      exact hcu.symm
    have heN : a * (t * b * t⁻¹) ∈ N := by
      refine (hmemN _).mpr ⟨heC, fun Λ' hΛ' => ?_⟩
      exact Subgroup.mul_mem _ (mem_normalizer_of_mem_component hΛ hΛ' ha)
        (mem_normalizer_of_mem_component hc₁ hΛ' ⟨b, hb, rfl⟩)
    exact hcomm _ heN t ht
  · intro φ hφ hφc hφp
    have hφX := hZX Λ hΛ φ hφ hφc hφp
    refine ⟨(hTX t ht φ hφX).symm, ?_⟩
    exact (Subgroup.mem_centralizer_iff.mp (hTC (hXT hφX)) u (Set.mem_singleton u)).symm

end CFSG.AGLEmbedding.SPLMSide
