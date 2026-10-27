module

public import CFSG.ClassicalInvolution.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.ElementaryAbelian

public section

namespace CFSG.ComponentClassification.StandardRecognition

open Subgroup
open CFSG.ClassicalInvolution (orderOf_conj_eq)

variable {G : Type*} [Group G]

section FourGroup

variable {t p : G}

theorem mem_closure_pair_iff (htt : t * t = 1) (hpp : p * p = 1) (htp : t * p = p * t)
    {x : G} : x ∈ Subgroup.closure ({t, p} : Set G) ↔ x = 1 ∨ x = t ∨ x = p ∨ x = t * p := by
  have htt' : ∀ y, t * (t * y) = y := fun y => by rw [← mul_assoc, htt, one_mul]
  have hpt : p * t = t * p := htp.symm
  have hpt' : ∀ y, p * (t * y) = t * (p * y) := fun y => by rw [← mul_assoc, hpt, mul_assoc]
  constructor
  · intro hx
    induction hx using Subgroup.closure_induction with
    | mem x hx =>
      rcases hx with rfl | rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr (Or.inl rfl))
    | one => exact Or.inl rfl
    | mul x y _ _ hx hy =>
      rcases hx with rfl | rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl | rfl <;>
        simp only [mul_assoc, one_mul, mul_one, htt, hpp, htt', hpt, hpt', true_or, or_true]
    | inv x _ hx =>
      have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
      have hpinv : p⁻¹ = p := inv_eq_of_mul_eq_one_right hpp
      rcases hx with rfl | rfl | rfl | rfl <;>
        simp only [inv_one, htinv, hpinv, mul_inv_rev, hpt, true_or, or_true]
  · rintro (rfl | rfl | rfl | rfl)
    · exact one_mem _
    · exact subset_closure (by simp)
    · exact subset_closure (by simp)
    · exact mul_mem (subset_closure (by simp)) (subset_closure (by simp))

theorem commute_and_mul_self_of_mem_closure_pair (htt : t * t = 1) (hpp : p * p = 1)
    (htp : t * p = p * t) {x y : G} (hx : x ∈ Subgroup.closure ({t, p} : Set G))
    (hy : y ∈ Subgroup.closure ({t, p} : Set G)) : x * y = y * x ∧ x * x = 1 := by
  have htt' : ∀ y, t * (t * y) = y := fun y => by rw [← mul_assoc, htt, one_mul]
  have hpt : p * t = t * p := htp.symm
  have hpt' : ∀ y, p * (t * y) = t * (p * y) := fun y => by rw [← mul_assoc, hpt, mul_assoc]
  rw [mem_closure_pair_iff htt hpp htp] at hx hy
  rcases hx with rfl | rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl | rfl <;>
    simp only [mul_assoc, one_mul, mul_one, htt, hpp, htt', hpt, hpt', and_self]

theorem card_closure_pair_of_involutions (htt : t * t = 1) (hpp : p * p = 1) (htp : t * p = p * t)
    (ht1 : t ≠ 1) (hp1 : p ≠ 1) (hne : t ≠ p) :
    Nat.card (Subgroup.closure ({t, p} : Set G)) = 4 := by
  have hset : ((Subgroup.closure ({t, p} : Set G) : Subgroup G) : Set G) = {1, t, p, t * p} := by
    ext x
    simp only [SetLike.mem_coe, mem_closure_pair_iff htt hpp htp, Set.mem_insert_iff,
      Set.mem_singleton_iff]
  have htp1 : t * p ≠ 1 := fun h => hne (by
    rw [eq_inv_of_mul_eq_one_right h, inv_eq_of_mul_eq_one_right htt])
  change Nat.card ((Subgroup.closure ({t, p} : Set G) : Subgroup G) : Set G) = 4
  rw [Nat.card_coe_set_eq, hset, Set.ncard_insert_of_notMem, Set.ncard_insert_of_notMem,
    Set.ncard_insert_of_notMem, Set.ncard_singleton]
  · simpa using ht1
  · simpa [not_or] using ⟨hne, hp1⟩
  · simpa [not_or, eq_comm] using ⟨ht1, hp1, htp1⟩

theorem isElementaryAbelian_closure_pair (htt : t * t = 1) (hpp : p * p = 1)
    (htp : t * p = p * t) : CFSG.IsElementaryAbelian 2 (Subgroup.closure ({t, p} : Set G)) where
  is_comm := ⟨fun x y => Subtype.ext
    (commute_and_mul_self_of_mem_closure_pair htt hpp htp x.2 y.2).1⟩
  exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun x => Subtype.ext (by
    simpa [sq] using (commute_and_mul_self_of_mem_closure_pair htt hpp htp x.2 x.2).2)

theorem conj_mem_closure_pair_of_conj_mem {g : G}
    (hgt : g * t * g⁻¹ ∈ Subgroup.closure ({t, p} : Set G))
    (hgp : g * p * g⁻¹ ∈ Subgroup.closure ({t, p} : Set G)) {x : G}
    (hx : x ∈ Subgroup.closure ({t, p} : Set G)) :
    g * x * g⁻¹ ∈ Subgroup.closure ({t, p} : Set G) := by
  have hle : Subgroup.closure ({t, p} : Set G) ≤
      (Subgroup.closure ({t, p} : Set G)).comap (MulAut.conj g).toMonoidHom := by
    rw [closure_le]
    rintro y (rfl | rfl)
    · simpa [MulAut.conj_apply] using hgt
    · simpa [MulAut.conj_apply] using hgp
  simpa [MulAut.conj_apply] using hle hx

theorem mem_normalizer_closure_pair_of_conj_mem {g : G}
    (h₁ : g * t * g⁻¹ ∈ Subgroup.closure ({t, p} : Set G))
    (h₂ : g * p * g⁻¹ ∈ Subgroup.closure ({t, p} : Set G))
    (h₃ : g⁻¹ * t * g ∈ Subgroup.closure ({t, p} : Set G))
    (h₄ : g⁻¹ * p * g ∈ Subgroup.closure ({t, p} : Set G)) :
    g ∈ normalizer ((Subgroup.closure ({t, p} : Set G) : Subgroup G) : Set G) := by
  rw [mem_normalizer_iff]
  intro x
  refine ⟨conj_mem_closure_pair_of_conj_mem h₁ h₂, fun hx => ?_⟩
  have := conj_mem_closure_pair_of_conj_mem (g := g⁻¹) (by simpa using h₃) (by simpa using h₄) hx
  simpa [mul_assoc] using this

theorem mulAut_closure_pair_ext (htt : t * t = 1) (hpp : p * p = 1) (htp : t * p = p * t)
    {σ τ : MulAut (Subgroup.closure ({t, p} : Set G))}
    (hσt : σ ⟨t, subset_closure (by simp)⟩ = τ ⟨t, subset_closure (by simp)⟩)
    (hσp : σ ⟨p, subset_closure (by simp)⟩ = τ ⟨p, subset_closure (by simp)⟩) : σ = τ := by
  refine MulEquiv.ext fun ⟨x, hx⟩ => ?_
  rcases (mem_closure_pair_iff htt hpp htp).mp hx with rfl | rfl | rfl | rfl
  · exact (map_one σ).trans (map_one τ).symm
  · exact hσt
  · exact hσp
  · have hsplit : (⟨t * p, hx⟩ : Subgroup.closure ({t, p} : Set G)) =
        ⟨t, subset_closure (by simp)⟩ * ⟨p, subset_closure (by simp)⟩ := rfl
    rw [hsplit, map_mul, map_mul, hσt, hσp]

theorem normalizerMonoidHom_closure_pair_surjective (htt : t * t = 1) (hpp : p * p = 1)
    (htp : t * p = p * t) (ht1 : t ≠ 1) (hp1 : p ≠ 1) (hne : t ≠ p) {a b : G}
    (hat : a * t * a⁻¹ = t) (hap : a * p * a⁻¹ = t * p) (hbt : b * t * b⁻¹ = p)
    (hbp : b * p * b⁻¹ = t) :
    Function.Surjective (Subgroup.closure ({t, p} : Set G)).normalizerMonoidHom := by
  set V := Subgroup.closure ({t, p} : Set G)
  have htV : t ∈ V := subset_closure (by simp)
  have hpV : p ∈ V := subset_closure (by simp)
  have htpV : t * p ∈ V := mul_mem htV hpV
  have hmem : ∀ {x : G}, x ∈ V ↔ x = 1 ∨ x = t ∨ x = p ∨ x = t * p :=
    mem_closure_pair_iff htt hpp htp
  have hia : a⁻¹ * t * a = t := by
    calc a⁻¹ * t * a = a⁻¹ * (a * t * a⁻¹) * a := by rw [hat]
      _ = t := by group
  have hiap : a⁻¹ * p * a = t * p := by
    have h : a⁻¹ * (t * p) * a = p := by rw [← hap]; group
    calc a⁻¹ * p * a = t * (t * (a⁻¹ * p * a)) := by rw [← mul_assoc, htt, one_mul]
      _ = t * (a⁻¹ * t * a * (a⁻¹ * p * a)) := by rw [hia]
      _ = t * (a⁻¹ * (t * p) * a) := by group
      _ = t * p := by rw [h]
  have hibt : b⁻¹ * t * b = p := by
    calc b⁻¹ * t * b = b⁻¹ * (b * p * b⁻¹) * b := by rw [hbp]
      _ = p := by group
  have hibp : b⁻¹ * p * b = t := by
    calc b⁻¹ * p * b = b⁻¹ * (b * t * b⁻¹) * b := by rw [hbt]
      _ = t := by group
  have ha : a ∈ normalizer (V : Set G) := mem_normalizer_closure_pair_of_conj_mem (by rwa [hat])
    (by rwa [hap]) (by rwa [hia]) (by rwa [hiap])
  have hb : b ∈ normalizer (V : Set G) := mem_normalizer_closure_pair_of_conj_mem (by rwa [hbt])
    (by rwa [hbp]) (by rwa [hibt]) (by rwa [hibp])
  set φ := V.normalizerMonoidHom
  have hφ_apply : ∀ (n : normalizer (V : Set G)) (x : G) (hx : x ∈ V),
      ((φ n ⟨x, hx⟩ : V) : G) = n * x * (n : G)⁻¹ := fun n x hx =>
    normalizerMonoidHom_apply_apply_coe V n ⟨x, hx⟩
  have hne1 : ∀ (τ : MulAut V) (x : V), x ≠ 1 → ((τ x : V) : G) ≠ 1 := fun τ x hx h =>
    hx (τ.injective ((Subtype.ext h).trans (map_one τ).symm))
  have hfix : ∀ τ : MulAut V, τ ⟨t, htV⟩ = ⟨t, htV⟩ → τ ∈ φ.range := by
    intro τ hτ
    have hτp1 := hne1 τ ⟨p, hpV⟩ (fun h => hp1 (congrArg Subtype.val h))
    have hτpt : ((τ ⟨p, hpV⟩ : V) : G) ≠ t := fun h => hne
      (congrArg Subtype.val (τ.injective (hτ.trans (Subtype.ext h).symm)))
    rcases hmem.mp (τ ⟨p, hpV⟩).2 with h | h | h | h
    · exact absurd h hτp1
    · exact absurd h hτpt
    · refine ⟨1, mulAut_closure_pair_ext htt hpp htp ?_ ?_⟩
      · rw [map_one, hτ]
        rfl
      · rw [map_one]
        exact (Subtype.ext h).symm
    · refine ⟨⟨a, ha⟩, mulAut_closure_pair_ext htt hpp htp ?_ ?_⟩
      · rw [hτ]
        exact Subtype.ext ((hφ_apply _ t htV).trans hat)
      · exact Subtype.ext ((hφ_apply _ p hpV).trans (hap.trans h.symm))
  intro σ
  obtain ⟨n, hn⟩ : ∃ n : normalizer (V : Set G), φ n ⟨t, htV⟩ = σ ⟨t, htV⟩ := by
    rcases hmem.mp (σ ⟨t, htV⟩).2 with h | h | h | h
    · exact absurd h (hne1 σ ⟨t, htV⟩ fun h' => ht1 (congrArg Subtype.val h'))
    · exact ⟨1, by rw [map_one]; exact (Subtype.ext h).symm⟩
    · exact ⟨⟨b, hb⟩, Subtype.ext ((hφ_apply _ t htV).trans (hbt.trans h.symm))⟩
    · refine ⟨⟨a, ha⟩ * ⟨b, hb⟩, Subtype.ext ((hφ_apply _ t htV).trans ?_)⟩
      change a * b * t * (a * b)⁻¹ = _
      rw [h, ← hap, ← hbt]
      group
  obtain ⟨m, hm⟩ := hfix ((φ n)⁻¹ * σ) (by
    rw [MulAut.mul_apply, ← hn, MulAut.inv_apply_self])
  exact ⟨n * m, by rw [map_mul, hm, mul_inv_cancel_left]⟩

end FourGroup

theorem exists_swap_of_external_fusion {t p : G} {K : Subgroup G} (ht : orderOf t = 2)
    (htK : t ∈ K) (hfus : ∀ g : G, g⁻¹ * t * g ∈ K → g⁻¹ * t * g = t)
    (hext : ∀ x y : G, x ∈ centralizer ({t} : Set G) → x ∉ K → orderOf x = 2 →
      y ∈ centralizer ({t} : Set G) → y ∉ K → orderOf y = 2 →
      ∃ h ∈ centralizer ({t} : Set G), h⁻¹ * x * h = y)
    (hpH : p ∈ centralizer ({t} : Set G)) (hpK : p ∉ K) (hpt : ∃ g : G, g⁻¹ * t * g = p) :
    ∃ b : G, b * t * b⁻¹ = p ∧ b * p * b⁻¹ = t := by
  obtain ⟨g, hg⟩ := hpt
  have hpt' : p * t = t * p := mem_centralizer_singleton_iff.mp hpH
  rw [← hg] at hpt'
  have hyH : g * t * g⁻¹ ∈ centralizer ({t} : Set G) := by
    rw [mem_centralizer_singleton_iff]
    calc g * t * g⁻¹ * t = g * (t * (g⁻¹ * t * g)) * g⁻¹ := by group
      _ = g * (g⁻¹ * t * g * t) * g⁻¹ := by rw [hpt']
      _ = t * (g * t * g⁻¹) := by group
  have hyK : g * t * g⁻¹ ∉ K := by
    intro hyK
    have h := hfus g⁻¹ (by simpa using hyK)
    rw [inv_inv] at h
    apply hpK
    rw [← hg]
    have : g⁻¹ * t * g = t := by
      calc g⁻¹ * t * g = g⁻¹ * (g * t * g⁻¹) * g := by rw [h]
        _ = t := by group
    rw [this]
    exact htK
  have hp2 : orderOf p = 2 := by
    rw [← hg, show g⁻¹ * t * g = g⁻¹ * t * g⁻¹⁻¹ by rw [inv_inv], orderOf_conj_eq, ht]
  have hy2 : orderOf (g * t * g⁻¹) = 2 := by rw [orderOf_conj_eq, ht]
  obtain ⟨h, hhH, hh⟩ := hext p _ hpH hpK hp2 hyH hyK hy2
  have hht : h * t = t * h := mem_centralizer_singleton_iff.mp hhH
  refine ⟨g⁻¹ * h⁻¹, ?_, ?_⟩
  · calc g⁻¹ * h⁻¹ * t * (g⁻¹ * h⁻¹)⁻¹ = g⁻¹ * (h⁻¹ * (t * h)) * g := by group
      _ = g⁻¹ * (h⁻¹ * (h * t)) * g := by rw [hht]
      _ = g⁻¹ * t * g := by group
      _ = p := hg
  · calc g⁻¹ * h⁻¹ * p * (g⁻¹ * h⁻¹)⁻¹ = g⁻¹ * (h⁻¹ * p * h) * g := by group
      _ = g⁻¹ * (g * t * g⁻¹) * g := by rw [hh]
      _ = t := by group

theorem external_involution_fusion_full_four_group_normalizer {t p : G} {K : Subgroup G}
    (ht : orderOf t = 2) (htK : t ∈ K) (hfus : ∀ g : G, g⁻¹ * t * g ∈ K → g⁻¹ * t * g = t)
    (hext : ∀ x y : G, x ∈ centralizer ({t} : Set G) → x ∉ K → orderOf x = 2 →
      y ∈ centralizer ({t} : Set G) → y ∉ K → orderOf y = 2 →
      ∃ h ∈ centralizer ({t} : Set G), h⁻¹ * x * h = y)
    (hpH : p ∈ centralizer ({t} : Set G)) (hpK : p ∉ K) (hpt : ∃ g : G, g⁻¹ * t * g = p) :
    Nat.card (Subgroup.closure ({t, p} : Set G)) = 4 ∧
      CFSG.IsElementaryAbelian 2 (Subgroup.closure ({t, p} : Set G)) ∧
      Function.Surjective (Subgroup.closure ({t, p} : Set G)).normalizerMonoidHom ∧
      ∀ g : normalizer ((Subgroup.closure ({t, p} : Set G) : Subgroup G) : Set G),
        (Subgroup.closure ({t, p} : Set G)).normalizerMonoidHom g = 1 ↔
          (g : G) ∈ centralizer ((Subgroup.closure ({t, p} : Set G) : Subgroup G) : Set G) := by
  obtain ⟨b, hbt, hbp⟩ := exists_swap_of_external_fusion ht htK hfus hext hpH hpK hpt
  obtain ⟨g, hg⟩ := hpt
  have hp2 : orderOf p = 2 := by
    rw [← hg, show g⁻¹ * t * g = g⁻¹ * t * g⁻¹⁻¹ by rw [inv_inv], orderOf_conj_eq, ht]
  have htt : t * t = 1 := (sq t).symm.trans (orderOf_eq_prime_iff.mp ht).1
  have hpp : p * p = 1 := (sq p).symm.trans (orderOf_eq_prime_iff.mp hp2).1
  have htp : t * p = p * t := (mem_centralizer_singleton_iff.mp hpH).symm
  have ht1 := (orderOf_eq_prime_iff.mp ht).2
  have hp1 := (orderOf_eq_prime_iff.mp hp2).2
  have hne : t ≠ p := fun h => hpK (h ▸ htK)
  have htpH : t * p ∈ centralizer ({t} : Set G) :=
    mul_mem (mem_centralizer_singleton_iff.mpr rfl) hpH
  have htpK : t * p ∉ K := fun h => hpK (by simpa using mul_mem (inv_mem htK) h)
  have htp2 : orderOf (t * p) = 2 := by
    refine orderOf_eq_prime ?_ fun h => hne ?_
    · rw [sq]
      exact (commute_and_mul_self_of_mem_closure_pair (x := t * p) (y := t * p) htt hpp htp
        (mul_mem (subset_closure (by simp)) (subset_closure (by simp)))
        (mul_mem (subset_closure (by simp)) (subset_closure (by simp)))).2
    · rw [eq_inv_of_mul_eq_one_right h, inv_eq_of_mul_eq_one_right htt]
  obtain ⟨h, hhH, hh⟩ := hext p (t * p) hpH hpK hp2 htpH htpK htp2
  have hht : h * t = t * h := mem_centralizer_singleton_iff.mp hhH
  refine ⟨card_closure_pair_of_involutions htt hpp htp ht1 hp1 hne,
    isElementaryAbelian_closure_pair htt hpp htp,
    normalizerMonoidHom_closure_pair_surjective htt hpp htp ht1 hp1 hne (a := h⁻¹) ?_ ?_ hbt hbp,
    fun n => ?_⟩
  · calc h⁻¹ * t * h⁻¹⁻¹ = h⁻¹ * (t * h) := by group
      _ = h⁻¹ * (h * t) := by rw [hht]
      _ = t := by group
  · rw [inv_inv, hh]
  · rw [← MonoidHom.mem_ker, normalizerMonoidHom_ker, mem_subgroupOf]

end CFSG.ComponentClassification.StandardRecognition
