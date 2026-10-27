module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8KAGen2

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Subgroup CFSG.GH74.GLS.Stage2.Signalizer.Odd87
open scoped commutatorElement

section Cover

variable {S P : Type} [Group S] [Group P]

@[expose] def kaFix (θ : S →* S) : Subgroup S := MonoidHom.eqLocus θ (MonoidHom.id S)

theorem mem_kaFix {θ : S →* S} {h : S} : h ∈ kaFix θ ↔ θ h = h := Iff.rfl

theorem ka_conj_mem_kaFix (θ : S →* S) {g z : S} (hθg : θ g = z * g)
    (hc : ∀ y : S, y * z = z * y) {h : S} (hh : h ∈ kaFix θ) : g * h * g⁻¹ ∈ kaFix θ := by
  rw [mem_kaFix] at hh ⊢
  rw [map_mul, map_mul, map_inv, hθg, hh]
  have h1 : (z * g) * h * (z * g)⁻¹ = z * (g * h * g⁻¹) * z⁻¹ := by group
  rw [h1, ← hc (g * h * g⁻¹)]
  group

theorem ka_cover_mem_normalizer (π : S →* P) (hker : ∀ z ∈ π.ker, ∀ g : S, g * z = z * g)
    (θ : S →* S) {α : MulAut P} (hθα : ∀ g, α (π g) = π (θ g)) {g : S}
    (hg : α (π g) = π g) : g ∈ normalizer (kaFix θ : Set S) := by
  have hz : θ g * g⁻¹ ∈ π.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, ← hθα, hg, mul_inv_cancel]
  set z : S := θ g * g⁻¹ with hzdef
  have hθg : θ g = z * g := by rw [hzdef]; group
  have hc : ∀ y : S, y * z = z * y := fun y => hker z hz y
  have hc' : ∀ y : S, y * z⁻¹ = z⁻¹ * y := by
    intro y
    have := hc y
    calc y * z⁻¹ = z⁻¹ * (z * y) * z⁻¹ := by group
      _ = z⁻¹ * (y * z) * z⁻¹ := by rw [this]
      _ = z⁻¹ * y := by group
  have hθg' : θ (g⁻¹) = z⁻¹ * g⁻¹ := by
    rw [map_inv, hθg, mul_inv_rev]
    exact hc' g⁻¹
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · exact fun hh => ka_conj_mem_kaFix θ hθg hc hh
  · intro hh
    have := ka_conj_mem_kaFix θ hθg' hc' hh
    simpa [mul_assoc] using this

theorem ka_map_mem_normalizer (π : S →* P) {H : Subgroup S} {g : S}
    (hg : g ∈ normalizer (H : Set S)) : π g ∈ normalizer ((H.map π : Subgroup P) : Set P) := by
  have hg1 := Subgroup.mem_normalizer_iff.mp hg
  have hg2 := Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hg)
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · rintro ⟨h, hh, rfl⟩
    exact ⟨g * h * g⁻¹, (hg1 h).mp hh, by rw [map_mul, map_mul, map_inv]⟩
  · rintro ⟨h', hh', hy⟩
    refine ⟨g⁻¹ * h' * g, ?_, ?_⟩
    · have := (hg2 h').mp hh'
      simpa using this
    · rw [map_mul, map_mul, map_inv, hy]
      group

theorem ka_normalizer_commutator {H : Subgroup S} {g : S} (hg : g ∈ normalizer (H : Set S)) :
    g ∈ normalizer ((⁅H, H⁆ : Subgroup S) : Set S) := by
  have hone : ∀ {g : S}, g ∈ normalizer (H : Set S) →
      ∀ k ∈ (⁅H, H⁆ : Subgroup S), g * k * g⁻¹ ∈ (⁅H, H⁆ : Subgroup S) := by
    intro g hg
    have hg1 := Subgroup.mem_normalizer_iff.mp hg
    have hle : (⁅H, H⁆ : Subgroup S) ≤ (⁅H, H⁆ : Subgroup S).comap (MulAut.conj g).toMonoidHom := by
      rw [Subgroup.commutator_le]
      intro a ha b hb
      show (MulAut.conj g).toMonoidHom ⁅a, b⁆ ∈ (⁅H, H⁆ : Subgroup S)
      have h1 : (MulAut.conj g).toMonoidHom ⁅a, b⁆ =
          ⁅g * a * g⁻¹, g * b * g⁻¹⁆ := by
        simp [MulAut.conj_apply, commutatorElement_def]
        group
      rw [h1]
      exact Subgroup.commutator_mem_commutator ((hg1 a).mp ha) ((hg1 b).mp hb)
    intro k hk
    exact hle hk
  rw [Subgroup.mem_normalizer_iff]
  intro k
  constructor
  · exact hone hg k
  · intro hk
    have := hone (Subgroup.inv_mem _ hg) _ hk
    simpa [mul_assoc] using this

theorem ka_cover_normalizer_of (π : S →* P) (hπ : Function.Surjective π)
    (hker : ∀ z ∈ π.ker, ∀ g : S, g * z = z * g) (θ : S →* S) {α : MulAut P}
    (hθα : ∀ g, α (π g) = π (θ g)) {L : Subgroup S}
    (hL : ∀ g ∈ normalizer (kaFix θ : Set S), g ∈ normalizer (L : Set S)) :
    ∀ x ∈ fixSub α, x ∈ normalizer ((L.map π : Subgroup P) : Set P) := by
  intro x hx
  obtain ⟨g, rfl⟩ := hπ x
  exact ka_map_mem_normalizer π (hL g (ka_cover_mem_normalizer π hker θ hθα hx))

theorem ka_cover_map_le (π : S →* P) (θ : S →* S) {α : MulAut P}
    (hθα : ∀ g, α (π g) = π (θ g)) {L : Subgroup S} (hLθ : L ≤ kaFix θ) :
    L.map π ≤ fixSub α := by
  rintro _ ⟨l, hl, rfl⟩
  rw [mem_fixSub, hθα, mem_kaFix.mp (hLθ hl)]

theorem ka_cover_map_perfect (π : S →* P) {L : Subgroup S} (hL : ⁅L, L⁆ = L) :
    ⁅L.map π, L.map π⁆ = L.map π := by
  rw [← Subgroup.map_commutator, hL]

theorem ka_cover_central (π : S →* P) [Finite P] {L : Subgroup S} (hLq : CFSG.IsQuasisimple ↥L) :
    ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ M : Subgroup P, M ≤ L.map π → IsPGroup p ↥M →
      (∀ l ∈ L.map π, l ∈ normalizer (M : Set P)) → ∀ m ∈ M, ∀ l ∈ L.map π, m * l = l * m := by
  intro p hp _ M hML hMp hMn
  have hr : (π.comp L.subtype).range = L.map π := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  have := ka_central_of_quasisimple_image (π.comp L.subtype) hLq hp M (hr ▸ hML) hMp
    (fun l hl => hMn l (hr ▸ hl))
  intro m hm l hl
  exact this m hm l (hr ▸ hl)

theorem ka_all_of_cover [Finite P] (hinj : Function.Injective (MulAut.conj : P →* MulAut P))
    (π : S →* P) (hπ : Function.Surjective π) (hker : ∀ z ∈ π.ker, ∀ g : S, g * z = z * g)
    (θ : S →* S) {α : MulAut P} (hθα : ∀ g, α (π g) = π (θ g)) (L : Subgroup S)
    (hLθ : L ≤ kaFix θ) (hLperf : ⁅L, L⁆ = L)
    (hLn : ∀ g ∈ normalizer (kaFix θ : Set S), g ∈ normalizer (L : Set S))
    (hLq : CFSG.IsQuasisimple ↥L) (hrig : KARigidComm α (L.map π)) : KAAll α :=
  ka_all_of_normal_comm hinj (L.map π) (ka_cover_map_le π θ hθα hLθ) (ka_cover_map_perfect π hLperf)
    (ka_cover_normalizer_of π hπ hker θ hθα hLn) (ka_cover_central π hLq) hrig

end Cover

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
