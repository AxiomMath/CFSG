module

public import CFSG.RankThree.PartTwo.Sec21.Notation

public section

namespace CFSG.AGLEmbeddingD2.Wilson.NormalizerAction

open Subgroup CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec21

variable {G : Type*} [Group G]

theorem normalizer_zpowers_of_conj_mem [Finite G] {g c : G} (h : g * c * g⁻¹ ∈ zpowers c) :
    g ∈ Subgroup.normalizer ((zpowers c : Subgroup G) : Set G) := by
  have hle : (zpowers c).map (MulAut.conj g).toMonoidHom ≤ zpowers c := by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
    have : (MulAut.conj g).toMonoidHom (c ^ n) = (g * c * g⁻¹) ^ n := by
      simp [MulAut.conj_apply, conj_zpow]
    rw [this]
    exact Subgroup.zpow_mem _ h n
  have heq := Subgroup.eq_of_le_of_card_ge hle (by
    rw [Nat.card_congr (Subgroup.equivMapOfInjective _ (MulAut.conj g).toMonoidHom
      (MulAut.conj g).injective).toEquiv])
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    exact hle ⟨x, hx, rfl⟩
  · intro hx
    rw [← heq] at hx
    obtain ⟨y, hy, hyx⟩ := hx
    have : y = x := by
      have h2 : g * y * g⁻¹ = g * x * g⁻¹ := hyx
      simpa using h2
    exact this ▸ hy

set_option maxHeartbeats 1000000 in
theorem isTransvectionOn_of_action {A D E' : Subgroup G} [Finite A]
    (hDA : D ≤ A) (hEA : E' ≤ A) (hcard : Nat.card A ≤ Nat.card ↥(D ⊔ E'))
    (hcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) {t : G}
    (htN : t ∈ Subgroup.normalizer (A : Set G)) {d : G} (hdD : d ∈ D) (hd3 : d ^ 3 = 1)
    (hd1 : d ≠ 1) (htd : t * d * t⁻¹ = d)
    (hD : ∀ δ ∈ D, ∃ n : ℕ, t * δ * t⁻¹ = δ * d ^ n)
    (hD1 : ∃ δ ∈ D, t * δ * t⁻¹ = δ * d) (hE : ∀ ε ∈ E', t * ε * t⁻¹ = ε) :
    IsTransvectionOn (A.normalizerMonoidHom ⟨t, htN⟩) := by
  set φ := A.normalizerMonoidHom ⟨t, htN⟩ with hφ
  have hφapp : ∀ y : A, ((φ y : A) : G) = t * y * t⁻¹ := fun y => rfl
  have hdA : d ∈ A := hDA hdD
  have htA : ∀ y ∈ A, t * y * t⁻¹ ∈ A := fun y hy =>
    (Subgroup.mem_normalizer_iff.1 htN y).1 hy
  let S : Subgroup G :=
    { carrier := {y | y ∈ A ∧ y⁻¹ * (t * y * t⁻¹) ∈ zpowers d}
      one_mem' := ⟨A.one_mem, by simpa using Subgroup.one_mem _⟩
      mul_mem' := by
        rintro y z ⟨hy, hpy⟩ ⟨hz, hpz⟩
        refine ⟨A.mul_mem hy hz, ?_⟩
        have hY := htA y hy
        have hYz : (t * y * t⁻¹) * z⁻¹ = z⁻¹ * (t * y * t⁻¹) :=
          hcomm _ hY _ (A.inv_mem hz)
        have hzy : z⁻¹ * y⁻¹ = y⁻¹ * z⁻¹ := hcomm _ (A.inv_mem hz) _ (A.inv_mem hy)
        have : (y * z)⁻¹ * (t * (y * z) * t⁻¹) =
            (y⁻¹ * (t * y * t⁻¹)) * (z⁻¹ * (t * z * t⁻¹)) := by
          calc (y * z)⁻¹ * (t * (y * z) * t⁻¹)
              = z⁻¹ * y⁻¹ * ((t * y * t⁻¹) * (t * z * t⁻¹)) := by group
            _ = y⁻¹ * z⁻¹ * ((t * y * t⁻¹) * (t * z * t⁻¹)) := by rw [hzy]
            _ = y⁻¹ * (z⁻¹ * (t * y * t⁻¹)) * (t * z * t⁻¹) := by group
            _ = y⁻¹ * ((t * y * t⁻¹) * z⁻¹) * (t * z * t⁻¹) := by rw [hYz]
            _ = _ := by group
        rw [this]
        exact Subgroup.mul_mem _ hpy hpz
      inv_mem' := by
        rintro y ⟨hy, hpy⟩
        refine ⟨A.inv_mem hy, ?_⟩
        have hY := htA y hy
        have hyY : y * (t * y * t⁻¹)⁻¹ = (t * y * t⁻¹)⁻¹ * y := hcomm _ hy _ (A.inv_mem hY)
        have : (y⁻¹)⁻¹ * (t * y⁻¹ * t⁻¹) = (y⁻¹ * (t * y * t⁻¹))⁻¹ := by
          calc (y⁻¹)⁻¹ * (t * y⁻¹ * t⁻¹) = y * (t * y * t⁻¹)⁻¹ := by group
            _ = (t * y * t⁻¹)⁻¹ * y := hyY
            _ = _ := by group
        rw [this]
        exact Subgroup.inv_mem _ hpy }
  have hDS : D ≤ S := by
    intro δ hδ
    obtain ⟨n, hn⟩ := hD δ hδ
    refine ⟨hDA hδ, ?_⟩
    have : δ⁻¹ * (t * δ * t⁻¹) = d ^ n := by rw [hn]; group
    rw [this]
    exact Subgroup.pow_mem _ (Subgroup.mem_zpowers d) n
  have hES : E' ≤ S := by
    intro ε hε
    refine ⟨hEA hε, ?_⟩
    rw [hE ε hε]
    simpa using Subgroup.one_mem _
  have hAle : A ≤ S := by
    have hsup : D ⊔ E' ≤ A := sup_le hDA hEA
    have heq := Subgroup.eq_of_le_of_card_ge hsup hcard
    rw [← heq]
    exact sup_le hDS hES
  set dA : A := ⟨d, hdA⟩ with hdAdef
  have hcomm_eq : commOf φ = zpowers dA := by
    apply le_antisymm
    · rw [commOf, Subgroup.closure_le]
      rintro _ ⟨y, rfl⟩
      obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 (hAle y.2).2
      refine ⟨n, Subtype.ext ?_⟩
      simp only [Subgroup.coe_zpow, Subgroup.coe_mul, Subgroup.coe_inv, hφapp]
      exact hn
    · rw [Subgroup.zpowers_le]
      obtain ⟨δ, hδ, hδt⟩ := hD1
      have := mem_commOf φ ⟨δ, hDA hδ⟩
      have e : ((⟨δ, hDA hδ⟩ : A)⁻¹ * φ ⟨δ, hDA hδ⟩ : A) = dA := by
        apply Subtype.ext
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, hφapp, hδt]
        rw [hdAdef]
        group
      rwa [e] at this
  have hord : orderOf dA = 3 := by
    rw [← Subgroup.orderOf_coe]
    exact orderOf_eq_prime hd3 hd1
  refine ⟨?_, ?_⟩
  · rw [hcomm_eq, Nat.card_zpowers, hord]
  · rw [hcomm_eq, Subgroup.zpowers_le]
    exact Subtype.ext htd

end CFSG.AGLEmbeddingD2.Wilson.NormalizerAction
