module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12L126Cm
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12L126U
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12L126Nc
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4L44
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec6Defs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12L126Base
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4L46

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

theorem sec126_D_data [Finite G] {t h : G} {A B V : Subgroup G} (ht2 : t * t = 1) (ht1 : t ≠ 1)
    (hB : Nat.card ↥B = 16) (hV : CFSG.Open.IsElemAbelian 2 V) (hcV : Nat.card ↥V = 2 ^ 8)
    (hVt : ∀ g : G, g⁻¹ * t * g ∉ V)
    (hrank : ∀ F : Subgroup G, F ≤ centralizer ({t} : Set G) → CFSG.Open.IsElemAbelian 2 F →
      Nat.card ↥F ≤ 32 ∧ (Nat.card ↥F = 32 →
        ∃ g ∈ centralizer ({t} : Set G), F = CFSG.conjugate A g))
    (hA1 : conjClassIn ⊤ t ∩ (A : Set G) = cosetSet t B)
    (hsN : h⁻¹ * t * h ∈ normalizer (V : Set G)) :
    ∃ c ∈ centralizer ({h⁻¹ * t * h} : Set G),
      V ⊓ centralizer ({h⁻¹ * t * h} : Set G) = CFSG.conjugate (CFSG.conjugate B h) c ∧
      V ⊓ centralizer ({h⁻¹ * t * h} : Set G) ⊔ zpowers (h⁻¹ * t * h) =
        CFSG.conjugate A (h * c) ∧
      (h * c)⁻¹ * t * (h * c) = h⁻¹ * t * h := by
  set s : G := h⁻¹ * t * h with hs_def
  have hs2 : s * s = 1 := by
    have : s * s = h⁻¹ * (t * t) * h := by rw [hs_def]; group
    rw [this, ht2]
    group
  have hs1 : s ≠ 1 := by
    intro h1
    apply ht1
    have : t = h * s * h⁻¹ := by rw [hs_def]; group
    rw [this, h1]
    group
  have hsord : orderOf s = 2 := orderOf_eq_prime (by rw [pow_two]; exact hs2) hs1
  set D : Subgroup G := V ⊓ centralizer ({s} : Set G) with hD_def
  have hDV : D ≤ V := inf_le_left
  have hsD : s ∉ D := fun hh => hVt h (hDV hh)
  have hsCD : s ∈ centralizer (D : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro d hd
    exact Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hd).2
  have hsND : s ∈ normalizer (D : Set G) := Subgroup.centralizer_le_normalizer _ hsCD
  have hDe : CFSG.Open.IsElemAbelian 2 D := sec126_isElemAbelian_of_le hV hDV
  have hF : CFSG.Open.IsElemAbelian 2 (D ⊔ zpowers s) :=
    sec4_isElemAbelian_sup_zpowers le_rfl hDe hsCD hsord
  have hFc : Nat.card ↥(D ⊔ zpowers s) = 2 * Nat.card ↥D :=
    sec4_card_sup_zpowers le_rfl hsCD hsD hsord
  have hDge : 16 ≤ Nat.card ↥D := by
    have h1 : 2 ^ 8 ≤ Nat.card ↥D ^ 2 := by
      have := sec126_card_le_sq hV hs2 hsN
      rwa [hcV] at this
    by_contra hlt
    have h2 : Nat.card ↥D ^ 2 ≤ 15 ^ 2 := Nat.pow_le_pow_left (by omega) 2
    omega
  have hFC : D ⊔ zpowers s ≤ centralizer ({s} : Set G) := by
    refine sup_le inf_le_right ?_
    rw [Subgroup.zpowers_le]
    exact Subgroup.mem_centralizer_singleton_iff.mpr rfl
  have hF'C : CFSG.conjugate (D ⊔ zpowers s) h⁻¹ ≤ centralizer ({t} : Set G) := by
    intro x hx
    rw [mem_conjugate_iff, inv_inv] at hx
    have hxs := Subgroup.mem_centralizer_singleton_iff.mp (hFC hx)
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h3 : h⁻¹ * (x * t) * h = h⁻¹ * (t * x) * h := by
      calc h⁻¹ * (x * t) * h = h⁻¹ * x * h * s := by rw [hs_def]; group
        _ = s * (h⁻¹ * x * h) := hxs
        _ = h⁻¹ * (t * x) * h := by rw [hs_def]; group
    exact mul_left_cancel (mul_right_cancel h3)
  obtain ⟨hle32, h32⟩ := hrank _ hF'C (sec4_isElemAbelian_conjugate hF h⁻¹)
  rw [sec126_card_conjugate, hFc] at hle32
  have hD16 : Nat.card ↥D = 16 := by omega
  have hF32 : Nat.card ↥(CFSG.conjugate (D ⊔ zpowers s) h⁻¹) = 32 := by
    rw [sec126_card_conjugate, hFc]
    omega
  obtain ⟨g, hgC, hgF⟩ := h32 hF32
  have hFA : D ⊔ zpowers s = CFSG.conjugate A (g * h) := by
    have h0 := sec126_conjugate_inv_cancel (D ⊔ zpowers s) h⁻¹
    rw [hgF, inv_inv, sec126_conjugate_conjugate] at h0
    exact h0.symm
  have hgt : g * t = t * g := Subgroup.mem_centralizer_singleton_iff.mp hgC
  have hgt' : g⁻¹ * t * g = t := by
    calc g⁻¹ * t * g = g⁻¹ * (t * g) := by group
      _ = g⁻¹ * (g * t) := by rw [hgt]
      _ = t := by group
  have hconj : (g * h)⁻¹ * t * (g * h) = s := by
    calc (g * h)⁻¹ * t * (g * h) = h⁻¹ * (g⁻¹ * t * g) * h := by group
      _ = s := by rw [hgt', hs_def]
  have hBD : CFSG.conjugate B (g * h) ≤ D := by
    intro y hy
    rw [mem_conjugate_iff] at hy
    have hmem : t * ((g * h) * y * (g * h)⁻¹) ∈ conjClassIn ⊤ t ∩ (A : Set G) := by
      rw [hA1]
      exact ⟨_, hy, rfl⟩
    obtain ⟨⟨k, -, hk⟩, hkA⟩ := hmem
    have hxF : s * y ∈ D ⊔ zpowers s := by
      rw [hFA, mem_conjugate_iff]
      have : (g * h) * (s * y) * (g * h)⁻¹ = t * ((g * h) * y * (g * h)⁻¹) := by
        rw [← hconj]
        group
      rw [this]
      exact hkA
    have hxnV : s * y ∉ V := by
      have : s * y = (k⁻¹ * (g * h))⁻¹ * t * (k⁻¹ * (g * h)) := by
        calc s * y = (g * h)⁻¹ * (t * ((g * h) * y * (g * h)⁻¹)) * (g * h) := by
              rw [← hconj]
              group
          _ = (g * h)⁻¹ * (k * t * k⁻¹) * (g * h) := by rw [hk]
          _ = (k⁻¹ * (g * h))⁻¹ * t * (k⁻¹ * (g * h)) := by group
      rw [this]
      exact hVt _
    rcases sec126_mem_sup_zpowers hsND hs2 hxF with hxD | ⟨d, hd, hxd⟩
    · exact absurd (hDV hxD) hxnV
    · have hdc : d * s = s * d :=
        Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hd).2
      have hyd : y = d := mul_left_cancel (hxd.trans hdc)
      rw [hyd]
      exact hd
  have hDeq : CFSG.conjugate B (g * h) = D :=
    Subgroup.eq_of_le_of_card_ge hBD (by rw [hD16, sec126_card_conjugate, hB])
  have hhc : h * (h⁻¹ * g * h) = g * h := by group
  refine ⟨h⁻¹ * g * h, ?_, ?_, ?_, ?_⟩
  · rw [Subgroup.mem_centralizer_singleton_iff, hs_def]
    calc h⁻¹ * g * h * (h⁻¹ * t * h) = h⁻¹ * (g * t) * h := by group
      _ = h⁻¹ * (t * g) * h := by rw [hgt]
      _ = h⁻¹ * t * h * (h⁻¹ * g * h) := by group
  · rw [sec126_conjugate_conjugate, hhc]
    exact hDeq.symm
  · rw [hhc]
    exact hFA
  · rw [hhc]
    exact hconj

end CFSG.OddStandard.SmallF3.Omega
