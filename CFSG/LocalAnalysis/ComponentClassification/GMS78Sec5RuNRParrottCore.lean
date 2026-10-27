module

public import CFSG.GroupTheory.ABGLocalTools.CoreLemmas

public section

namespace CFSG.ComponentClassification.GMS78.RuNR

open Subgroup CFSG.ABGLocalTools

variable {G : Type*} [Group G]

theorem exists_isSylowOf_ge_of_le [Finite G] {p : ℕ} [Fact p.Prime] {Q K : Subgroup G}
    (hQK : Q ≤ K) (hQ : IsPGroup p Q) : ∃ P : Subgroup G, IsSylowOf p P K ∧ Q ≤ P := by
  obtain ⟨P, hP⟩ := (hQ.comap_subtype : IsPGroup p (Q.subgroupOf K)).exists_le_sylow
  exact ⟨(P : Subgroup K).map K.subtype, ⟨P, rfl⟩,
    fun x hx => ⟨⟨x, hQK hx⟩, hP (mem_subgroupOf.mpr hx), rfl⟩⟩

theorem isSylowOf_of_maximal [Finite G] {p : ℕ} [Fact p.Prime] {Q K : Subgroup G}
    (hQK : Q ≤ K) (hQ : IsPGroup p Q)
    (hmax : ∀ P : Subgroup G, IsPGroup p P → P ≤ K → Q ≤ P → P = Q) : IsSylowOf p Q K := by
  obtain ⟨P, hP, hQP⟩ := exists_isSylowOf_ge_of_le hQK hQ
  rwa [hmax P hP.isPGroup hP.le hQP] at hP

theorem mem_centralizer_conj {a h x : G} (hx : x ∈ centralizer ({a} : Set G)) :
    h * x * h⁻¹ ∈ centralizer ({h * a * h⁻¹} : Set G) := by
  rw [mem_centralizer_singleton_iff] at hx ⊢
  calc h * x * h⁻¹ * (h * a * h⁻¹) = h * (x * a) * h⁻¹ := by group
    _ = h * (a * x) * h⁻¹ := by rw [hx]
    _ = h * a * h⁻¹ * (h * x * h⁻¹) := by group

theorem false_of_transport [Finite G] {H J S : Subgroup G} (odd : G → Prop)
    (hJn : ∀ h ∈ H, ∀ j ∈ J, h * j * h⁻¹ ∈ J)
    (hodd : ∀ h ∈ H, ∀ y : G, odd (h * y * h⁻¹) ↔ odd y) (hSH : S ≤ H) (hS2 : IsPGroup 2 S)
    {a : G} (hmax : ∀ P : Subgroup G, IsPGroup 2 P → P ≤ H ⊓ centralizer ({a} : Set G) →
      S ⊓ centralizer ({a} : Set G) ≤ P → P = S ⊓ centralizer ({a} : Set G))
    (hF1 : ∀ y ∈ S ⊓ centralizer ({a} : Set G), y ^ 2 ∈ J → y ∉ J → odd y →
      ∃ j ∈ J ⊓ centralizer ({a} : Set G), (y * j) ^ 2 = 1)
    {h : G} (hh : h ∈ H) {u : G} (hu : u ∈ S ⊓ centralizer ({h * a * h⁻¹} : Set G))
    (hu2 : u ^ 2 ∈ J) (huJ : u ∉ J) (huo : odd u)
    (hu3 : ∀ j ∈ J ⊓ centralizer ({h * a * h⁻¹} : Set G), (u * j) ^ 2 ≠ 1) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set K := H ⊓ centralizer ({a} : Set G) with hK
  have hSa : IsSylowOf 2 (S ⊓ centralizer ({a} : Set G)) K :=
    isSylowOf_of_maximal (inf_le_inf_right _ hSH) hS2.to_inf_left hmax
  set Q := (S ⊓ centralizer ({h * a * h⁻¹} : Set G)).map (MulAut.conj h⁻¹).toMonoidHom with hQ
  have hQ2 : IsPGroup 2 Q := hS2.to_inf_left.map _
  have hQK : Q ≤ K := by
    rintro _ ⟨s, hs, rfl⟩
    obtain ⟨hsS, hsc⟩ := mem_inf.mp hs
    refine mem_inf.mpr ⟨?_, ?_⟩
    · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      exact H.mul_mem (H.mul_mem (H.inv_mem hh) (hSH hsS)) (H.inv_mem (H.inv_mem hh))
    · have := mem_centralizer_conj (h := h⁻¹) hsc
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      simpa [mul_assoc] using this
  obtain ⟨P, hP, hQP⟩ := exists_isSylowOf_ge_of_le hQK hQ2
  obtain ⟨k, hkK, hk⟩ := hSa.exists_mem_conj hP
  obtain ⟨hkH, hka⟩ := mem_inf.mp hkK
  set g := h * k with hg
  have hgH : g ∈ H := H.mul_mem hh hkH
  have hconj : ∀ s ∈ S ⊓ centralizer ({h * a * h⁻¹} : Set G), g⁻¹ * s * g ∈
      S ⊓ centralizer ({a} : Set G) := by
    intro s hs
    have h1 : h⁻¹ * s * h ∈ P := hQP ⟨s, hs, by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]⟩
    have h2 := (hk _).mp h1
    rwa [show k⁻¹ * (h⁻¹ * s * h) * k = g⁻¹ * s * g by rw [hg]; group] at h2
  have hga : g * a * g⁻¹ = h * a * h⁻¹ := by
    have hc : k * a = a * k := mem_centralizer_singleton_iff.mp hka
    calc g * a * g⁻¹ = h * (k * a) * k⁻¹ * h⁻¹ := by rw [hg]; group
      _ = h * a * h⁻¹ := by rw [hc]; group
  have hy := hconj u hu
  have hgi : g⁻¹ ∈ H := H.inv_mem hgH
  have hy2 : (g⁻¹ * u * g) ^ 2 ∈ J := by
    have := hJn g⁻¹ hgi _ hu2
    rwa [inv_inv, show g⁻¹ * u ^ 2 * g = (g⁻¹ * u * g) ^ 2 by rw [sq, sq]; group] at this
  have hyJ : g⁻¹ * u * g ∉ J := by
    intro hyJ
    apply huJ
    have := hJn g hgH _ hyJ
    rwa [show g * (g⁻¹ * u * g) * g⁻¹ = u by group] at this
  have hyo : odd (g⁻¹ * u * g) := by
    have := (hodd g⁻¹ hgi u).mpr huo
    rwa [inv_inv] at this
  obtain ⟨j, hj, hj2⟩ := hF1 _ hy hy2 hyJ hyo
  obtain ⟨hjJ, hja⟩ := mem_inf.mp hj
  refine hu3 (g * j * g⁻¹) (mem_inf.mpr ⟨hJn g hgH j hjJ, ?_⟩) ?_
  · rw [← hga]
    exact mem_centralizer_conj hja
  · calc (u * (g * j * g⁻¹)) ^ 2 = g * ((g⁻¹ * u * g) * j) ^ 2 * g⁻¹ := by rw [sq, sq]; group
      _ = 1 := by rw [hj2]; group

end CFSG.ComponentClassification.GMS78.RuNR
