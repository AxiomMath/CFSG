module

public import CFSG.ClassicalInvolution.Q3.Q3T8B17M

public section

namespace CFSG.ClassicalInvolution.Q3.TL4.LieZ2

open CFSG.Blueprint CFSG.Sporadic.Mathieu Equiv CFSG.ClassicalInvolution.Q3.Q3T8.Asc77

theorem sup_centralizer_m11SdY_m11SdZY :
    Subgroup.centralizer ({m11SdYElt} : Set ↥NativeSporadic.M11) ⊔
      Subgroup.centralizer ({m11SdZ * m11SdYElt} : Set ↥NativeSporadic.M11) = ⊤ := by
  set W := Subgroup.centralizer ({m11SdYElt} : Set ↥NativeSporadic.M11) ⊔
    Subgroup.centralizer ({m11SdZ * m11SdYElt} : Set ↥NativeSporadic.M11) with hW
  set u₀ := m11Conj [1, 0, 1, 1, 0, 1, 0, 3, 0, 1, 1] with hu₀
  set v₀ := m11Conj [1, 1, 0, 1, 0, 3, 0, 3, 0, 1, 1, 0] with hv₀
  have h1 : u₀ ∈ W := by
    refine Subgroup.mem_sup_left ?_
    rw [Subgroup.mem_centralizer_singleton_iff]
    refine Subtype.ext ?_
    show m11Eval [1, 0, 1, 1, 0, 1, 0, 3, 0, 1, 1] * m11SdY =
      m11SdY * m11Eval [1, 0, 1, 1, 0, 1, 0, 3, 0, 1, 1]
    decide +kernel
  have h2 : v₀ ∈ W := by
    refine Subgroup.mem_sup_right ?_
    rw [Subgroup.mem_centralizer_singleton_iff]
    refine Subtype.ext ?_
    show m11Eval [1, 1, 0, 1, 0, 3, 0, 3, 0, 1, 1, 0] * (m11SdX ^ 4 * m11SdY) =
      m11SdX ^ 4 * m11SdY * m11Eval [1, 1, 0, 1, 0, 3, 0, 3, 0, 1, 1, 0]
    decide +kernel
  have hA : m11a ∈ W := by
    have e : m11a = v₀⁻¹ * u₀ * u₀ * v₀ * u₀ * u₀ * v₀ * v₀ := by
      refine Subtype.ext ?_
      show m11gA = (m11Eval [1, 1, 0, 1, 0, 3, 0, 3, 0, 1, 1, 0])⁻¹ *
        m11Eval [1, 0, 1, 1, 0, 1, 0, 3, 0, 1, 1] * m11Eval [1, 0, 1, 1, 0, 1, 0, 3, 0, 1, 1] *
        m11Eval [1, 1, 0, 1, 0, 3, 0, 3, 0, 1, 1, 0] * m11Eval [1, 0, 1, 1, 0, 1, 0, 3, 0, 1, 1] *
        m11Eval [1, 0, 1, 1, 0, 1, 0, 3, 0, 1, 1] * m11Eval [1, 1, 0, 1, 0, 3, 0, 3, 0, 1, 1, 0] *
        m11Eval [1, 1, 0, 1, 0, 3, 0, 3, 0, 1, 1, 0]
      decide +kernel
    rw [e]
    exact W.mul_mem (W.mul_mem (W.mul_mem (W.mul_mem (W.mul_mem (W.mul_mem (W.mul_mem
      (W.inv_mem h2) h1) h1) h2) h1) h1) h2) h2
  have hB : m11b ∈ W := by
    have e : m11b = v₀ * u₀⁻¹ * v₀ * u₀⁻¹ := by
      refine Subtype.ext ?_
      show m11gB = m11Eval [1, 1, 0, 1, 0, 3, 0, 3, 0, 1, 1, 0] *
        (m11Eval [1, 0, 1, 1, 0, 1, 0, 3, 0, 1, 1])⁻¹ *
        m11Eval [1, 1, 0, 1, 0, 3, 0, 3, 0, 1, 1, 0] * (m11Eval [1, 0, 1, 1, 0, 1, 0, 3, 0, 1, 1])⁻¹
      decide +kernel
    rw [e]
    exact W.mul_mem (W.mul_mem (W.mul_mem h2 (W.inv_mem h1)) h2) (W.inv_mem h1)
  have hcl : Subgroup.closure ({m11a, m11b} : Set ↥NativeSporadic.M11) = ⊤ :=
    closure_pair_eq_top m11_eq _ _
  rw [eq_top_iff, ← hcl, Subgroup.closure_le]
  rintro x (rfl | rfl)
  · exact hA
  · exact hB

theorem m11Sd_pair_conj : ∀ p q : Fin 8 × Fin 2,
    m11SdMap p * m11SdMap p = 1 → m11SdMap p ≠ 1 → m11SdMap q * m11SdMap q = 1 →
    m11SdMap q ≠ 1 → m11SdMap p ≠ m11SdMap q →
    m11SdMap p * m11SdMap q = m11SdMap q * m11SdMap p →
    ∃ k : Fin 8,
      (m11SdX ^ k.val * m11SdMap p * (m11SdX ^ k.val)⁻¹ = m11SdX ^ 4 ∧
        m11SdX ^ k.val * m11SdMap q * (m11SdX ^ k.val)⁻¹ = m11SdY) ∨
      (m11SdX ^ k.val * m11SdMap p * (m11SdX ^ k.val)⁻¹ = m11SdY ∧
        m11SdX ^ k.val * m11SdMap q * (m11SdX ^ k.val)⁻¹ = m11SdX ^ 4) ∨
      (m11SdX ^ k.val * m11SdMap p * (m11SdX ^ k.val)⁻¹ = m11SdY ∧
        m11SdX ^ k.val * m11SdMap q * (m11SdX ^ k.val)⁻¹ = m11SdX ^ 4 * m11SdY) := by
  decide +kernel

theorem sup_centralizer_of_conj {G : Type*} [Group G] {a b s t : G}
    (hab : Subgroup.centralizer ({a} : Set G) ⊔ Subgroup.centralizer ({b} : Set G) = ⊤) (h : G)
    (hs : h * s * h⁻¹ = a) (ht : h * t * h⁻¹ = b) :
    Subgroup.centralizer ({s} : Set G) ⊔ Subgroup.centralizer ({t} : Set G) = ⊤ := by
  have e := sup_centralizer_eq_top_conj hab h⁻¹
  rwa [show h⁻¹ * a * h⁻¹⁻¹ = s by rw [← hs]; group,
    show h⁻¹ * b * h⁻¹⁻¹ = t by rw [← ht]; group] at e

theorem sup_centralizer_eq_top_m11 {u v : ↥NativeSporadic.M11} (hu : orderOf u = 2)
    (hv : orderOf v = 2) (huv : u * v = v * u) (hne : u ≠ v) :
    Subgroup.centralizer ({u} : Set ↥NativeSporadic.M11) ⊔
      Subgroup.centralizer ({v} : Set ↥NativeSporadic.M11) = ⊤ := by
  have hinv : ∀ w : ↥NativeSporadic.M11, orderOf w = 2 → w * w = 1 ∧ w ≠ 1 := fun w hw =>
    ⟨by rw [← sq, ← hw, pow_orderOf_eq_one], fun h => by rw [h, orderOf_one] at hw; omega⟩
  obtain ⟨hu2, hu1⟩ := hinv u hu
  obtain ⟨hv2, hv1⟩ := hinv v hv
  obtain ⟨g, s, t, hsS, htS, hgs, hgt⟩ := exists_conj_pair_mem_m11SdS hu2 hu1 hv2 hv1 hne huv
  have hsu : s = g⁻¹ * u * g := by rw [← hgs]; group
  have htv : t = g⁻¹ * v * g := by rw [← hgt]; group
  have hs2 : s * s = 1 := by
    calc s * s = g⁻¹ * (u * u) * g := by rw [hsu]; group
      _ = 1 := by rw [hu2]; group
  have ht2 : t * t = 1 := by
    calc t * t = g⁻¹ * (v * v) * g := by rw [htv]; group
      _ = 1 := by rw [hv2]; group
  have hs1 : s ≠ 1 := by
    rintro rfl
    exact hu1 (by rw [← hgs]; group)
  have ht1 : t ≠ 1 := by
    rintro rfl
    exact hv1 (by rw [← hgt]; group)
  have hst : s ≠ t := by
    rintro rfl
    exact hne (by rw [← hgs, ← hgt])
  have hcst : s * t = t * s := by
    calc s * t = g⁻¹ * (u * v) * g := by rw [hsu, htv]; group
      _ = g⁻¹ * (v * u) * g := by rw [huv]
      _ = t * s := by rw [hsu, htv]; group
  obtain ⟨p, hp⟩ := exists_m11SdMap_eq_of_mem hsS
  obtain ⟨q, hq⟩ := exists_m11SdMap_eq_of_mem htS
  obtain ⟨k, hk⟩ := m11Sd_pair_conj p q
    (by rw [hp]; simpa using congrArg Subtype.val hs2)
    (by rw [hp]; exact fun h => hs1 (Subtype.ext h))
    (by rw [hq]; simpa using congrArg Subtype.val ht2)
    (by rw [hq]; exact fun h => ht1 (Subtype.ext h))
    (by rw [hp, hq]; exact fun h => hst (Subtype.ext h))
    (by rw [hp, hq]; simpa using congrArg Subtype.val hcst)
  set c : ↥NativeSporadic.M11 := m11SdXElt ^ k.val with hc
  have hconv : ∀ (w w' : ↥NativeSporadic.M11) (r : Fin 8 × Fin 2),
      m11SdMap r = (w : Perm (Fin 11)) →
      m11SdX ^ k.val * m11SdMap r * (m11SdX ^ k.val)⁻¹ = (w' : Perm (Fin 11)) →
        c * w * c⁻¹ = w' := by
    intro w w' r hr hrw
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, hc, SubmonoidClass.coe_pow, ← hr]
    exact hrw
  have hgen : Subgroup.centralizer ({s} : Set ↥NativeSporadic.M11) ⊔
      Subgroup.centralizer ({t} : Set ↥NativeSporadic.M11) = ⊤ := by
    rcases hk with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact sup_centralizer_of_conj sup_centralizer_m11SdZ_m11SdYElt c
        (hconv s m11SdZ p hp h1) (hconv t m11SdYElt q hq h2)
    · refine sup_centralizer_of_conj ?_ c (hconv s m11SdYElt p hp h1) (hconv t m11SdZ q hq h2)
      rw [sup_comm]
      exact sup_centralizer_m11SdZ_m11SdYElt
    · exact sup_centralizer_of_conj sup_centralizer_m11SdY_m11SdZY c
        (hconv s m11SdYElt p hp h1) (hconv t (m11SdZ * m11SdYElt) q hq h2)
  have e := sup_centralizer_eq_top_conj hgen g
  rwa [hgs, hgt] at e

end CFSG.ClassicalInvolution.Q3.TL4.LieZ2
