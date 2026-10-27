module

public import CFSG.GroupTheory.LocalCores.Layer
public import CFSG.CGT.PushingUpLit.CGT6.Nine7Amb

public section

namespace CFSG.CGT.PushingUpLit.CGT6.Diag.Reduce

open CFSG CFSG.LocalCores
open scoped commutatorElement

section Basic

variable {X : Type} [Group X]

@[expose] def cj (t : X) (K : Subgroup X) : Subgroup X := K.map (MulAut.conj t).toMonoidHom

theorem mem_cj_iff_exists {t : X} {K : Subgroup X} {x : X} :
    x ∈ cj t K ↔ ∃ k ∈ K, x = t * k * t⁻¹ := by
  constructor
  · rintro ⟨k, hk, rfl⟩
    exact ⟨k, hk, by simp [MulAut.conj_apply]⟩
  · rintro ⟨k, hk, rfl⟩
    exact ⟨k, hk, by simp [MulAut.conj_apply]⟩

theorem cj_mul_mem {t : X} {K : Subgroup X} {k : X} (hk : k ∈ K) : t * k * t⁻¹ ∈ cj t K :=
  mem_cj_iff_exists.2 ⟨k, hk, rfl⟩

theorem conjugate_eq_cj {t : X} (ht2 : t * t = 1) (K : Subgroup X) : conjugate K t = cj t K := by
  have : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  simp [conjugate, cj, this]

theorem commutator_zpowers_le (K : Subgroup X) {t : X} (ht2 : t * t = 1) :
    ⁅K, Subgroup.zpowers t⁆ ≤ K ⊔ cj t K := by
  rw [Subgroup.commutator_le]
  intro k hk s hs
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hs
  have ht2' : t ^ (2 : ℤ) = 1 := by rw [zpow_two]; exact ht2
  have hn : t ^ n = 1 ∨ t ^ n = t := by
    have h1 : n = 2 * (n / 2) + n % 2 := (Int.mul_ediv_add_emod n 2).symm
    have h2 : t ^ n = (t ^ (2 : ℤ)) ^ (n / 2) * t ^ (n % 2) := by
      rw [← zpow_mul, ← zpow_add]
      congr 1
    rw [h2, ht2', one_zpow, one_mul]
    rcases Int.emod_two_eq_zero_or_one n with h | h
    · left; rw [h]; simp
    · right; rw [h]; simp
  rcases hn with h | h
  · rw [h]
    simp
  · rw [h]
    have hk' : k⁻¹ ∈ K := K.inv_mem hk
    have h1 : t * k⁻¹ * t⁻¹ ∈ cj t K := cj_mul_mem hk'
    have : ⁅k, t⁆ = k * (t * k⁻¹ * t⁻¹) := by
      simp [commutatorElement_def, mul_assoc]
    rw [this]
    exact Subgroup.mul_mem_sup hk h1

end Basic

section Layer

variable {X : Type} [Group X] [Finite X]

omit [Finite X] in
theorem exists_component_noncomm {Y : Subgroup X} (hYq : IsQuasisimple Y) (hYL : Y ≤ layer X) :
    ∃ K : Subgroup X, IsComponent K ∧ ⁅Y, K⁆ ≠ ⊥ := by
  by_contra h
  push Not at h
  have hle : layer X ≤ Subgroup.centralizer (Y : Set X) := by
    refine sSup_le fun K hK => ?_
    have := h K hK
    rw [Subgroup.commutator_comm] at this
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp this
  have hYC : Y ≤ Subgroup.centralizer (Y : Set X) := hYL.trans hle
  obtain ⟨-, -, a, b, hab⟩ := hYq
  apply hab
  obtain ⟨a', rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨b', rfl⟩ := QuotientGroup.mk_surjective b
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
  congr 1
  apply Subtype.ext
  exact (Subgroup.mem_centralizer_iff.mp (hYC a'.2) b' b'.2).symm

omit [Finite X] in
theorem le_of_centralizes {Y K K' : Subgroup X} (hYp : Group.IsPerfect Y) (hKK' : ⁅K, K'⁆ = ⊥)
    (hY : Y ≤ K ⊔ K') (hYK' : ⁅Y, K'⁆ = ⊥) : Y ≤ K := by
  have hKK'' : ∀ a ∈ K, ∀ b ∈ K', a * b = b * a := fun a ha b hb =>
    (Subgroup.mem_centralizer_iff.mp (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hKK' ha) b
      hb).symm
  refine Nine7.perfect_le_of_le_mul (D := K ⊔ K') (Zc := K' ⊓ Subgroup.centralizer (K' : Set X))
    hYp hY ?_ ?_ ?_
  · exact inf_le_left.trans le_sup_right
  · intro z hz d hd
    obtain ⟨a, ha, b, hb, rfl⟩ := (Nine7.mem_sup_iff_of_comm hKK').1 hd
    have h1 : z * a = a * z := (hKK'' a ha z hz.1).symm
    have h2 : z * b = b * z := (Subgroup.mem_centralizer_iff.mp hz.2 b hb).symm
    calc z * (a * b) = (z * a) * b := by group
      _ = a * (z * b) := by rw [h1]; group
      _ = a * (b * z) := by rw [h2]
      _ = a * b * z := by group
  · intro y hy
    obtain ⟨a, ha, b, hb, rfl⟩ := (Nine7.mem_sup_iff_of_comm hKK').1 (hY hy)
    refine ⟨a, ha, b, ⟨hb, ?_⟩, rfl⟩
    show b ∈ Subgroup.centralizer (K' : Set X)
    rw [Subgroup.mem_centralizer_iff]
    intro c hc
    have h1 : c * (a * b) = (a * b) * c :=
      Subgroup.mem_centralizer_iff.mp (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hYK' hy)
        c hc
    have h2 : c * a = a * c := (hKK'' a ha c hc).symm
    have : a * (c * b) = a * (b * c) := by
      calc a * (c * b) = (a * c) * b := by group
        _ = (c * a) * b := by rw [h2]
        _ = c * (a * b) := by group
        _ = (a * b) * c := h1
        _ = a * (b * c) := by group
    exact mul_left_cancel this

theorem exists_swapped_pair {Y T : Subgroup X} {t : X}
    (hYq : IsQuasisimple Y) (hYL : Y ≤ layer X) (ht2 : t * t = 1)
    (hTY : T ≤ Subgroup.centralizer (Y : Set X)) (hLT : layer X ⊔ T = ⊤)
    (hLY : ∀ N : Subgroup X, (∀ g : X, ∀ y ∈ Y, g * y * g⁻¹ ∈ N) → layer X ≤ N)
    (hdich : ∀ K : Subgroup X, IsComponent K → ⁅Y, K⁆ = ⊥ ∨ Y ≤ K ∨
      (conjugate K t ≠ K ∧ Y ≤ ⁅K, Subgroup.zpowers t⁆))
    (hno : ¬ ∃ K : Subgroup X, IsComponent K ∧ Y ≤ K) :
    ∃ K : Subgroup X, IsComponent K ∧ IsComponent (cj t K) ∧ cj t K ≠ K ∧
      ⁅K, cj t K⁆ = ⊥ ∧ Y ≤ K ⊔ cj t K ∧ layer X = K ⊔ cj t K := by
  obtain ⟨K, hK, hYK⟩ := exists_component_noncomm hYq hYL
  have hK' : IsComponent (cj t K) := isComponent_map_mulEquiv (MulAut.conj t) hK
  set K' := cj t K with hK'def
  rcases hdich K hK with h1 | h2 | ⟨hne, hcomm⟩
  · exact absurd h1 hYK
  · exact absurd ⟨K, hK, h2⟩ hno
  have hne' : K' ≠ K := by
    rw [hK'def, ← conjugate_eq_cj ht2]
    exact hne
  have hKK' : ⁅K, K'⁆ = ⊥ :=
    (distinct_components_commute hK hK').resolve_left fun h => hne' h.symm
  have hYKK' : Y ≤ K ⊔ K' := hcomm.trans (commutator_zpowers_le K ht2)
  have hcases : ∀ K₀ : Subgroup X, IsComponent K₀ → ⁅Y, K₀⁆ ≠ ⊥ → K₀ = K ∨ K₀ = K' := by
    intro K₀ hK₀ hne0
    by_contra hcon
    push Not at hcon
    obtain ⟨hn1, hn2⟩ := hcon
    have c1 : ⁅K, K₀⁆ = ⊥ :=
      (distinct_components_commute hK hK₀).resolve_left fun h => hn1 h.symm
    have c2 : ⁅K', K₀⁆ = ⊥ :=
      (distinct_components_commute hK' hK₀).resolve_left fun h => hn2 h.symm
    apply hne0
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    exact hYKK'.trans (sup_le (Subgroup.commutator_eq_bot_iff_le_centralizer.mp c1)
      (Subgroup.commutator_eq_bot_iff_le_centralizer.mp c2))
  have hYK'ne : ⁅Y, K'⁆ ≠ ⊥ := by
    intro h
    exact hno ⟨K, hK, le_of_centralizes hYq.1 hKK' hYKK' h⟩
  have hperm : ∀ x ∈ T, ∀ K₀ : Subgroup X, IsComponent K₀ → ⁅Y, K₀⁆ ≠ ⊥ →
      cj x K₀ = K ∨ cj x K₀ = K' := by
    intro x hx K₀ hK₀ hne0
    apply hcases (cj x K₀) (isComponent_map_mulEquiv (MulAut.conj x) hK₀)
    intro h
    apply hne0
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer] at h ⊢
    intro y hy
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    have h1 := Subgroup.mem_centralizer_iff.mp (h hy) (x * k * x⁻¹) (cj_mul_mem hk)
    have hxy : y * x = x * y := Subgroup.mem_centralizer_iff.mp (hTY hx) y hy
    have hy' : x * y * x⁻¹ = y := by rw [mul_inv_eq_iff_eq_mul]; exact hxy.symm
    have h2 : x * (k * y) * x⁻¹ = x * (y * k) * x⁻¹ := by
      calc x * (k * y) * x⁻¹ = (x * k * x⁻¹) * (x * y * x⁻¹) := by group
        _ = (x * k * x⁻¹) * y := by rw [hy']
        _ = y * (x * k * x⁻¹) := h1
        _ = (x * y * x⁻¹) * (x * k * x⁻¹) := by rw [hy']
        _ = x * (y * k) * x⁻¹ := by group
    exact mul_left_cancel (mul_right_cancel h2)
  have hcjle : ∀ x ∈ T, cj x (K ⊔ K') ≤ K ⊔ K' := by
    intro x hx
    have e : cj x (K ⊔ K') = cj x K ⊔ cj x K' := Subgroup.map_sup _ _ _
    rw [e]
    have h1 : cj x K ≤ K ⊔ K' := by
      rcases hperm x hx K hK hYK with h | h
      · rw [h]; exact le_sup_left
      · rw [h]; exact le_sup_right
    have h2 : cj x K' ≤ K ⊔ K' := by
      rcases hperm x hx K' hK' hYK'ne with h | h
      · rw [h]; exact le_sup_left
      · rw [h]; exact le_sup_right
    exact sup_le h1 h2
  have hT_norm : T ≤ Subgroup.normalizer ((K ⊔ K' : Subgroup X) : Set X) := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      exact hcjle x hx (cj_mul_mem hh)
    · intro hh
      have h3 := hcjle x⁻¹ (T.inv_mem hx) (cj_mul_mem hh)
      have e : x⁻¹ * (x * h * x⁻¹) * x⁻¹⁻¹ = h := by group
      rwa [e] at h3
  have hlayer_norm : layer X ≤ Subgroup.normalizer ((K ⊔ K' : Subgroup X) : Set X) := by
    refine sSup_le fun K₀ hK₀ => ?_
    by_cases hc : K₀ = K ∨ K₀ = K'
    · rcases hc with rfl | rfl
      · exact le_sup_left.trans Subgroup.le_normalizer
      · exact le_sup_right.trans Subgroup.le_normalizer
    · push Not at hc
      obtain ⟨hn1, hn2⟩ := hc
      have c1 : ⁅K, K₀⁆ = ⊥ :=
        (distinct_components_commute hK hK₀).resolve_left fun h => hn1 h.symm
      have c2 : ⁅K', K₀⁆ = ⊥ :=
        (distinct_components_commute hK' hK₀).resolve_left fun h => hn2 h.symm
      have hKc : K ⊔ K' ≤ Subgroup.centralizer (K₀ : Set X) :=
        sup_le (Subgroup.commutator_eq_bot_iff_le_centralizer.mp c1)
          (Subgroup.commutator_eq_bot_iff_le_centralizer.mp c2)
      have : K₀ ≤ Subgroup.centralizer ((K ⊔ K' : Subgroup X) : Set X) :=
        Subgroup.commutator_eq_bot_iff_le_centralizer.mp (by
          rw [Subgroup.commutator_comm]
          exact Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hKc)
      exact this.trans (Subgroup.centralizer_le_normalizer _)
  have hall : ⊤ ≤ Subgroup.normalizer ((K ⊔ K' : Subgroup X) : Set X) := by
    rw [← hLT]
    exact sup_le hlayer_norm hT_norm
  have hconj : ∀ g : X, ∀ y ∈ Y, g * y * g⁻¹ ∈ K ⊔ K' := by
    intro g y hy
    have hg : g ∈ Subgroup.normalizer ((K ⊔ K' : Subgroup X) : Set X) := hall trivial
    exact (Subgroup.mem_normalizer_iff.mp hg y).mp (hYKK' hy)
  have hle : layer X ≤ K ⊔ K' := hLY _ hconj
  exact ⟨K, hK, hK', hne', hKK', hYKK',
    le_antisymm hle (sup_le (component_le_layer hK) (component_le_layer hK'))⟩

end Layer

end CFSG.CGT.PushingUpLit.CGT6.Diag.Reduce
