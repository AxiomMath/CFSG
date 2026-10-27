module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.Lemma611H

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.NativeSporadic
open scoped Pointwise

namespace Hyp69

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {z t : G} {T₀ E : Subgroup G}
  {Q : Sylow 2 G} {x β : G} {B : Subgroup G} {S : Subgroup G}
  (h : Hyp69 L z t T₀ E Q x β B S)

include h

theorem z_not_mem_Qs {α : G} (hα : AlphaSpec S z t α) :
    z ∉ Fsub h hα ⊓ centralizer ({α} : Set G) := by
  intro hzQ
  have hαz : α * z = z * α := (mem_centralizer_singleton_iff.1 hzQ.2).symm
  have h2 : z * α = t * (z * α) := by rw [← hα.rel, hαz]
  exact h.t_ne (by simpa using h2.symm)

theorem cent_z_Qs_le_E {α : G} (hα : AlphaSpec S z t α) {q : G}
    (hq : q ∈ Fsub h hα ⊓ centralizer ({α} : Set G)) (hqz : q * z = z * q) : q ∈ E := by
  have hmem : q ∈ E ⊔ zpowers z := by
    rw [← h.CFz_eq hα]
    exact ⟨hq.1, mem_centralizer_singleton_iff.2 hqz⟩
  obtain ⟨e', he', a, ha, hge⟩ := exists_mul_of_mem_sup_of_le_centralizer
    (zpowers_le.2 (h.SC h.zS)) hmem
  rcases mem_zpowers_sq_eq_one h.z_sq ha with h1 | h1
  · rw [hge, h1, mul_one]; exact he'
  · exfalso
    apply h.z_not_mem_Qs hα
    have h2 : e'⁻¹ * q = z := by rw [hge, h1]; group
    have h3 := mul_mem (inv_mem (h.E_le_Qs hα he')) hq
    rwa [h2] at h3

theorem cent_z_conj_mem_U {α : G} (hα : AlphaSpec S z t α) (hF : EFacts611 E t)
    (hWr : ∃ hz : z ∈ centralizer ({β} : Set G),
      WreathAlt ↥(centralizer ({β} : Set G)) (QuotientGroup.mk ⟨z, hz⟩))
    (hBD : BetaData65 E β) {g : G}
    (hg : ∀ q : G, q ∈ Fsub h hα ⊓ centralizer ({α} : Set G) ↔
      g * q * g⁻¹ ∈ Fsub h hα ⊓ centralizer ({α} : Set G))
    (hgz : g * z = z * g) {u : G} (hu : u ∈ S ⊔ E) : g * u * g⁻¹ ∈ S ⊔ E := by
  obtain ⟨hgt, hperm⟩ := h.normalizer_Q_perm_W hα hF hWr hBD hg
  have hα' : g * α * g⁻¹ = α ∨ g * α * g⁻¹ = α * t := by
    rcases hperm with ⟨e, -⟩ | ⟨e, -⟩
    · exact Or.inl e
    · exact Or.inr e
  have hzg : g * z * g⁻¹ = z := by rw [hgz]; group
  have hαS : g * α * g⁻¹ ∈ S := by
    rcases hα' with e | e
    · rw [e]; exact hα.mem
    · rw [e]; exact mul_mem hα.mem h.t_mem_S
  have hgS : ∀ s ∈ S, g * s * g⁻¹ ∈ S := by
    intro s hs
    have e : ∀ a b : G, g * (a * b) * g⁻¹ = (g * a * g⁻¹) * (g * b * g⁻¹) := fun a b => by group
    rcases hα.list s hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · simp
    · rw [hgt]; exact h.t_mem_S
    · rw [hzg]; exact h.zS
    · rw [e, hzg, hgt]; exact mul_mem h.zS h.t_mem_S
    · exact hαS
    · rw [e, hgt]; exact mul_mem hαS h.t_mem_S
    · rw [e, hzg]; exact mul_mem hαS h.zS
    · rw [e, e, hzg, hgt]; exact mul_mem (mul_mem hαS h.zS) h.t_mem_S
  have hgE : ∀ e ∈ E, g * e * g⁻¹ ∈ E := by
    intro e he
    have hgeQ := (hg e).1 (h.E_le_Qs hα he)
    have hez : e * z = z * e := mem_centralizer_iff.1 (h.SC h.zS) e he
    refine h.cent_z_Qs_le_E hα hgeQ ?_
    calc g * e * g⁻¹ * z = g * e * g⁻¹ * (g * z * g⁻¹) := by rw [hzg]
      _ = g * (e * z) * g⁻¹ := by group
      _ = g * (z * e) * g⁻¹ := by rw [hez]
      _ = (g * z * g⁻¹) * (g * e * g⁻¹) := by group
      _ = z * (g * e * g⁻¹) := by rw [hzg]
  obtain ⟨s, hs, e, he, rfl⟩ := exists_mul_of_mem_sup_of_le_centralizer h.E_le_cent_S hu
  have e2 : g * (s * e) * g⁻¹ = (g * s * g⁻¹) * (g * e * g⁻¹) := by group
  rw [e2]
  exact mul_mem (mem_sup_left (hgS s hs)) (mem_sup_right (hgE e he))

theorem cent_z_mem_normalizer {α : G} (hα : AlphaSpec S z t α) (hF : EFacts611 E t)
    (hWr : ∃ hz : z ∈ centralizer ({β} : Set G),
      WreathAlt ↥(centralizer ({β} : Set G)) (QuotientGroup.mk ⟨z, hz⟩))
    (hBD : BetaData65 E β) {g : G}
    (hg : ∀ q : G, q ∈ Fsub h hα ⊓ centralizer ({α} : Set G) ↔
      g * q * g⁻¹ ∈ Fsub h hα ⊓ centralizer ({α} : Set G))
    (hgz : g * z = z * g) : g ∈ normalizer ((S ⊔ E : Subgroup G) : Set G) := by
  rw [mem_normalizer_iff]
  intro u
  refine ⟨fun hu => h.cent_z_conj_mem_U hα hF hWr hBD hg hgz hu, fun hu => ?_⟩
  have hg' : ∀ q : G, q ∈ Fsub h hα ⊓ centralizer ({α} : Set G) ↔
      g⁻¹ * q * g⁻¹⁻¹ ∈ Fsub h hα ⊓ centralizer ({α} : Set G) := fun q => by
    have e := hg (g⁻¹ * q * g)
    rw [show g * (g⁻¹ * q * g) * g⁻¹ = q by group] at e
    rw [inv_inv]
    exact e.symm
  have hgz' : g⁻¹ * z = z * g⁻¹ := by
    calc g⁻¹ * z = g⁻¹ * (z * g) * g⁻¹ := by group
      _ = g⁻¹ * (g * z) * g⁻¹ := by rw [hgz]
      _ = z * g⁻¹ := by group
  have e := h.cent_z_conj_mem_U hα hF hWr hBD hg' hgz' hu
  rwa [show g⁻¹ * (g * u * g⁻¹) * g⁻¹⁻¹ = u by group] at e

theorem normalizer_Q_cent_z_iff {α : G} (hα : AlphaSpec S z t α) (hF : EFacts611 E t)
    (hWr : ∃ hz : z ∈ centralizer ({β} : Set G),
      WreathAlt ↥(centralizer ({β} : Set G)) (QuotientGroup.mk ⟨z, hz⟩))
    (hBD : BetaData65 E β) {g : G} :
    ((∀ q : G, q ∈ Fsub h hα ⊓ centralizer ({α} : Set G) ↔
      g * q * g⁻¹ ∈ Fsub h hα ⊓ centralizer ({α} : Set G)) ∧ g * z = z * g) ↔
      g ∈ (L ⊓ centralizer ({t} : Set G)) ⊔ zpowers z := by
  constructor
  · rintro ⟨hg, hgz⟩
    rw [← h.CMz_eq]
    exact ⟨h.cent_z_mem_normalizer hα hF hWr hBD hg hgz, mem_centralizer_singleton_iff.2 hgz⟩
  · intro hm
    rw [← h.CMz_eq] at hm
    obtain ⟨hmN, hmc⟩ := hm
    refine ⟨fun q => ⟨fun hq => h.QF_normal hα hmN hq, fun hq => ?_⟩,
      mem_centralizer_singleton_iff.1 hmc⟩
    have e := h.QF_normal hα (inv_mem hmN) hq
    rwa [show g⁻¹ * (g * q * g⁻¹) * g⁻¹⁻¹ = q by group] at e

end Hyp69

end CFSG.EvenSporadicStandard.Fin76b
