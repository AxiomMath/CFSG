module

public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms
public import CFSG.LocalAnalysis.ComponentClassification.StandardRecognitionZStarFourGroup

public section

namespace CFSG.ComponentClassification.StandardRecognition

open Subgroup
open CFSG.ClassicalInvolution (orderOf_conj_eq)
open scoped commutatorElement

variable {G : Type*} [Group G]

private theorem commutatorElement_mul_mul_of_commute {v a w b : G} (hva : Commute v a)
    (hvw : Commute v w) (hvb : Commute v b) (hwa : Commute w a) (hwb : Commute w b) :
    ⁅v * a, w * b⁆ = ⁅a, b⁆ := by
  have hv : Commute v (a * w * b * a⁻¹) :=
    ((hva.mul_right hvw).mul_right hvb).mul_right hva.inv_right
  have hw : Commute w (a * b * a⁻¹ * b⁻¹) :=
    ((hwa.mul_right hwb).mul_right hwa.inv_right).mul_right hwb.inv_right
  rw [commutatorElement_def, commutatorElement_def]
  calc v * a * (w * b) * (v * a)⁻¹ * (w * b)⁻¹
      = v * (a * w * b * a⁻¹) * v⁻¹ * (b⁻¹ * w⁻¹) := by group
    _ = a * w * b * a⁻¹ * v * v⁻¹ * (b⁻¹ * w⁻¹) := by rw [hv.eq]
    _ = a * w * b * a⁻¹ * b⁻¹ * w⁻¹ := by group
    _ = w * (a * b * a⁻¹ * b⁻¹) * w⁻¹ := by rw [← hwa.eq]; group
    _ = a * b * a⁻¹ * b⁻¹ * w * w⁻¹ := by rw [hw.eq]
    _ = a * b * a⁻¹ * b⁻¹ := by group

theorem conj_mem_of_centralizer_le_sup_of_perfect {V A : Subgroup G}
    (hVab : ∀ x ∈ V, ∀ y ∈ V, x * y = y * x) (hAC : A ≤ centralizer (V : Set G))
    (hCVA : centralizer (V : Set G) ≤ V ⊔ A) (hperf : ⁅A, A⁆ = A) {g : G}
    (hg : ∀ c ∈ centralizer (V : Set G), g * c * g⁻¹ ∈ centralizer (V : Set G)) {a : G}
    (ha : a ∈ A) : g * a * g⁻¹ ∈ A := by
  have hcomm : ∀ (v : V) (x : A), Commute (V.subtype v) (A.subtype x) := fun v x =>
    (mem_centralizer_iff.mp (hAC x.2) v v.2)
  have hsplit : ∀ c ∈ V ⊔ A, ∃ v ∈ V, ∃ x ∈ A, v * x = c := by
    intro c hc
    rw [← V.subtype_range, ← A.subtype_range, ← MonoidHom.noncommCoprod_range _ _ hcomm] at hc
    obtain ⟨⟨v, x⟩, rfl⟩ := hc
    exact ⟨v, v.2, x, x.2, rfl⟩
  have hle : ⁅A, A⁆ ≤ A.comap (MulAut.conj g).toMonoidHom := by
    rw [commutator_le]
    intro a₁ ha₁ a₂ ha₂
    rw [mem_comap, MulEquiv.coe_toMonoidHom, map_commutatorElement, MulAut.conj_apply,
      MulAut.conj_apply]
    obtain ⟨v₁, hv₁, x₁, hx₁, h₁⟩ := hsplit _ (hCVA (hg _ (hAC ha₁)))
    obtain ⟨v₂, hv₂, x₂, hx₂, h₂⟩ := hsplit _ (hCVA (hg _ (hAC ha₂)))
    have hc : ∀ {v x : G}, v ∈ V → x ∈ A → Commute v x := fun hv hx =>
      mem_centralizer_iff.mp (hAC hx) _ hv
    rw [← h₁, ← h₂, commutatorElement_mul_mul_of_commute (hc hv₁ hx₁) (hVab _ hv₁ _ hv₂)
      (hc hv₁ hx₂) (hc hv₂ hx₁) (hc hv₂ hx₂)]
    exact hperf ▸ commutator_mem_commutator hx₁ hx₂
  have := hle (hperf.symm ▸ ha)
  rwa [mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at this

private theorem commutator_eq_self_of_perfect {A : Subgroup G} (hA : _root_.commutator A = ⊤) :
    ⁅A, A⁆ = A := by
  rw [← map_subtype_commutator, hA, ← MonoidHom.range_eq_map, subtype_range]

theorem four_group_perfect_factor_forces_internal_fusion [Finite G] {t p : G}
    {K A : Subgroup G} (ht : orderOf t = 2) (hKH : K ≤ centralizer ({t} : Set G)) (htK : t ∈ K)
    (hfus : ∀ g : G, g⁻¹ * t * g ∈ K → g⁻¹ * t * g = t)
    (hext : ∀ x y : G, x ∈ centralizer ({t} : Set G) → x ∉ K → orderOf x = 2 →
      y ∈ centralizer ({t} : Set G) → y ∉ K → orderOf y = 2 →
      ∃ h ∈ centralizer ({t} : Set G), h⁻¹ * x * h = y)
    (hpH : p ∈ centralizer ({t} : Set G)) (hpK : p ∉ K) (hpt : ∃ g : G, g⁻¹ * t * g = p)
    (hAK : A ≤ K) (hAperf : _root_.commutator A = ⊤) (hAeven : Even (Nat.card A))
    (hVA : Subgroup.closure ({t, p} : Set G) ⊔ A =
      centralizer ((Subgroup.closure ({t, p} : Set G) : Subgroup G) : Set G)) : False := by
  obtain ⟨b, hbt, hbp⟩ := exists_swap_of_external_fusion ht htK hfus hext hpH hpK hpt
  obtain ⟨g, hg⟩ := hpt
  obtain ⟨V, hV⟩ : ∃ V : Subgroup G, V = Subgroup.closure ({t, p} : Set G) := ⟨_, rfl⟩
  rw [← hV] at hVA
  have hp2 : orderOf p = 2 := by
    rw [← hg, show g⁻¹ * t * g = g⁻¹ * t * g⁻¹⁻¹ by rw [inv_inv], orderOf_conj_eq, ht]
  have htt : t * t = 1 := (sq t).symm.trans (orderOf_eq_prime_iff.mp ht).1
  have hpp : p * p = 1 := (sq p).symm.trans (orderOf_eq_prime_iff.mp hp2).1
  have htp : t * p = p * t := (mem_centralizer_singleton_iff.mp hpH).symm
  have htV : t ∈ V := hV ▸ subset_closure (by simp)
  have hpV : p ∈ V := hV ▸ subset_closure (by simp)
  have hVab : ∀ x ∈ V, ∀ y ∈ V, x * y = y * x := fun x hx y hy =>
    (commute_and_mul_self_of_mem_closure_pair htt hpp htp (hV ▸ hx) (hV ▸ hy)).1
  have hconj : ∀ {c : G}, c * t * c⁻¹ ∈ V → c * p * c⁻¹ ∈ V → ∀ x ∈ V, c * x * c⁻¹ ∈ V :=
    fun h₁ h₂ x hx => hV ▸ conj_mem_closure_pair_of_conj_mem (hV ▸ h₁) (hV ▸ h₂) (hV ▸ hx)
  have hbinvt : b⁻¹ * t * b⁻¹⁻¹ = p := by
    calc b⁻¹ * t * b⁻¹⁻¹ = b⁻¹ * (b * p * b⁻¹) * b := by rw [hbp, inv_inv]
      _ = p := by group
  have hbinvp : b⁻¹ * p * b⁻¹⁻¹ = t := by
    calc b⁻¹ * p * b⁻¹⁻¹ = b⁻¹ * (b * t * b⁻¹) * b := by rw [hbt, inv_inv]
      _ = t := by group
  have hbC : ∀ c ∈ centralizer (V : Set G), b * c * b⁻¹ ∈ centralizer (V : Set G) := by
    intro c hc
    rw [mem_centralizer_iff]
    intro x hx
    have hx' : b⁻¹ * x * b⁻¹⁻¹ ∈ V := hconj (by rw [hbinvt]; exact hpV)
      (by rw [hbinvp]; exact htV) x hx
    rw [inv_inv] at hx'
    have hcx := mem_centralizer_iff.mp hc _ hx'
    calc x * (b * c * b⁻¹) = b * (b⁻¹ * x * b * c) * b⁻¹ := by group
      _ = b * (c * (b⁻¹ * x * b)) * b⁻¹ := by rw [hcx]
      _ = b * c * b⁻¹ * x := by group
  have hAC : A ≤ centralizer (V : Set G) := hVA ▸ le_sup_right
  have hbA : ∀ a ∈ A, b * a * b⁻¹ ∈ A := fun a ha =>
    conj_mem_of_centralizer_le_sup_of_perfect hVab hAC hVA.ge
      (commutator_eq_self_of_perfect hAperf) hbC ha
  obtain ⟨z₀, hz₀⟩ := exists_prime_orderOf_dvd_card' (G := A) 2 (even_iff_two_dvd.mp hAeven)
  have hz2 : orderOf (z₀ : G) = 2 := by rw [orderOf_coe, hz₀]
  have hzA : (z₀ : G) ∈ A := z₀.2
  obtain ⟨z', hz'⟩ : ∃ z' : G, b * z₀ * b⁻¹ = z' := ⟨_, rfl⟩
  have hz'A : z' ∈ A := hz' ▸ hbA _ hzA
  have hz'2 : orderOf z' = 2 := by rw [← hz', orderOf_conj_eq, hz2]
  have hpz : p * z' = z' * p := mem_centralizer_iff.mp (hAC hz'A) p hpV
  have hpzH : p * z' ∈ centralizer ({t} : Set G) := mul_mem hpH (hKH (hAK hz'A))
  have hpzK : p * z' ∉ K := fun h => hpK (by
    have := mul_mem h (inv_mem (hAK hz'A))
    rwa [mul_inv_cancel_right] at this)
  have hpz2 : orderOf (p * z') = 2 := by
    refine orderOf_eq_prime ?_ fun h => hpK ?_
    · calc (p * z') ^ 2 = p * (z' * p) * z' := by rw [sq]; group
        _ = p * p * (z' * z') := by rw [← hpz]; group
        _ = 1 := by rw [hpp, (sq z').symm.trans (orderOf_eq_prime_iff.mp hz'2).1, one_mul]
    · rw [eq_inv_of_mul_eq_one_left h]
      exact inv_mem (hAK hz'A)
  obtain ⟨h, hhH, hh⟩ := hext _ p hpzH hpzK hpz2 hpH hpK hp2
  have hh' : p * z' = h * p * h⁻¹ := by
    calc p * z' = h * (h⁻¹ * (p * z') * h) * h⁻¹ := by group
      _ = h * p * h⁻¹ := by rw [hh]
  have hconjtz : (g * h⁻¹ * b)⁻¹ * t * (g * h⁻¹ * b) = t * z₀ := by
    calc (g * h⁻¹ * b)⁻¹ * t * (g * h⁻¹ * b) = b⁻¹ * (h * (g⁻¹ * t * g) * h⁻¹) * b := by group
      _ = b⁻¹ * (p * z') * b := by rw [hg, hh']
      _ = b⁻¹ * (b * t * b⁻¹ * (b * z₀ * b⁻¹)) * b := by rw [hbt, hz']
      _ = t * z₀ := by group
  have htz := hfus (g * h⁻¹ * b) (by rw [hconjtz]; exact mul_mem htK (hAK hzA))
  rw [hconjtz] at htz
  exact (orderOf_eq_prime_iff.mp hz2).2 (by simpa using htz)

theorem four_group_action_forces_forbidden_internal_involution_fusion [Finite G] {t p : G}
    {K : Subgroup G} (ht : orderOf t = 2) (hKH : K ≤ centralizer ({t} : Set G)) (htK : t ∈ K)
    (hfus : ∀ g : G, g⁻¹ * t * g ∈ K → g⁻¹ * t * g = t)
    (hext : ∀ x y : G, x ∈ centralizer ({t} : Set G) → x ∉ K → orderOf x = 2 →
      y ∈ centralizer ({t} : Set G) → y ∉ K → orderOf y = 2 →
      ∃ h ∈ centralizer ({t} : Set G), h⁻¹ * x * h = y)
    (hpH : p ∈ centralizer ({t} : Set G)) (hpK : p ∉ K) (hpt : ∃ g : G, g⁻¹ * t * g = p)
    (A : Subgroup G) (hAK : A ≤ K) (hAperf : _root_.commutator A = ⊤)
    (hAeven : Even (Nat.card A)) (_hAout : ¬ 3 ∣ Nat.card (OuterAutomorphisms.Outer A))
    (hVA : Subgroup.closure ({t, p} : Set G) ⊔ A =
      centralizer ((Subgroup.closure ({t, p} : Set G) : Subgroup G) : Set G))
    (_hVAbot : Subgroup.closure ({t, p} : Set G) ⊓ A = ⊥)
    (_hAV : ∀ a ∈ A, ∀ v ∈ Subgroup.closure ({t, p} : Set G), a * v = v * a) : False :=
  four_group_perfect_factor_forces_internal_fusion ht hKH htK hfus hext hpH hpK hpt hAK hAperf
    hAeven hVA

end CFSG.ComponentClassification.StandardRecognition
