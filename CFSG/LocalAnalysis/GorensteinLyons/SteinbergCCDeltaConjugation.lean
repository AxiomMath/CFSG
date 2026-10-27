module

public import CFSG.LocalAnalysis.GorensteinLyons.SteinbergCCConjugate
public import CFSG.Open.GLADefs

public section

namespace CFSG.LocalAnalysis.GorensteinLyons

open Subgroup CFSG.Open

variable {G : Type*} [Group G]

theorem map_glaPPrimeCoreOf {G' : Type*} [Group G'] (p : ℕ) (φ : G ≃* G') (K : Subgroup G) :
    (GLAPPrimeCoreOf p K).map φ.toMonoidHom = GLAPPrimeCoreOf p (K.map φ.toMonoidHom) := by
  unfold GLAPPrimeCoreOf
  rw [map_map]
  set e := K.equivMapOfInjective φ.toMonoidHom φ.injective with he
  have h1 : φ.toMonoidHom.comp K.subtype =
      (K.map φ.toMonoidHom).subtype.comp e.toMonoidHom := by
    ext k
    rfl
  rw [h1, ← map_map]
  congr 1
  exact CFSG.pPrimeCore_map_iso p e

theorem conjugate_glaPPrimeCoreOf_centralizer (p : ℕ) (d g : G) :
    CFSG.conjugate (GLAPPrimeCoreOf p (centralizer {d})) g =
      GLAPPrimeCoreOf p (centralizer {g⁻¹ * d * g}) := by
  unfold CFSG.conjugate
  rw [map_glaPPrimeCoreOf]
  congr 1
  ext y
  rw [mem_map_equiv, MulAut.conj_symm_apply, inv_inv, mem_centralizer_singleton_iff,
    mem_centralizer_singleton_iff]
  constructor
  · intro h
    calc y * (g⁻¹ * d * g) = g⁻¹ * ((g * y * g⁻¹) * d) * g := by group
      _ = g⁻¹ * (d * (g * y * g⁻¹)) * g := by rw [h]
      _ = g⁻¹ * d * g * y := by group
  · intro h
    calc g * y * g⁻¹ * d = g * (y * (g⁻¹ * d * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * d * g) * y) * g⁻¹ := by rw [h]
      _ = d * (g * y * g⁻¹) := by group

theorem mem_glaDelta_iff {p : ℕ} {E : Subgroup G} {x : G} :
    x ∈ GLADelta p E ↔ ∀ d ∈ E, d ≠ 1 → x ∈ GLAPPrimeCoreOf p (centralizer {d}) := by
  simp only [GLADelta, mem_iInf]

theorem delta_conjugation_and_coprime_action [Finite G] {p : ℕ} (hp : p.Prime) (_hp2 : p ≠ 2)
    {D : Subgroup G} (_hD : IsElemAbelian p D) (hDcard : Nat.card D = p ^ 2) :
    GLADelta p D ≤ centralizer (D : Set G) ∧
      ¬ p ∣ Nat.card (GLADelta p D) ∧
      (∀ g : G, CFSG.conjugate (GLADelta p D) g = GLADelta p (CFSG.conjugate D g)) ∧
      (GLADelta p D ≤ normalizer (D : Set G) ∧
        ((GLADelta p D).subgroupOf (normalizer (D : Set G))).Normal) ∧
      ∀ B : Subgroup G, IsElemAbelian p B → D ≤ B →
        B ≤ normalizer (GLADelta p D : Set G) ∧ ⁅GLADelta p D, B⁆ ≤ GLADelta p D ∧
          B ≤ normalizer ((⁅GLADelta p D, B⁆ : Subgroup G) : Set G) ∧
          ¬ p ∣ Nat.card (⁅GLADelta p D, B⁆ : Subgroup G) := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨d₀, hd₀D, hd₀⟩ : ∃ d ∈ D, d ≠ 1 := by
    have h1 : 1 < Nat.card D := by
      rw [hDcard]
      exact Nat.one_lt_pow two_ne_zero hp.one_lt
    have : Nontrivial D := Finite.one_lt_card_iff_nontrivial.mp h1
    obtain ⟨⟨d, hd⟩, hne⟩ := exists_ne (1 : D)
    exact ⟨d, hd, fun h => hne (Subtype.ext h)⟩
  have hΔC : GLADelta p D ≤ centralizer (D : Set G) := by
    intro x hx
    rw [mem_centralizer_iff]
    intro d hd
    by_cases hd1 : d = 1
    · rw [hd1, one_mul, mul_one]
    · have hxC : x ∈ centralizer ({d} : Set G) := map_subtype_le _ (mem_glaDelta_iff.mp hx d hd hd1)
      exact (mem_centralizer_singleton_iff.mp hxC).symm
  have hcop : ∀ K : Subgroup G, Nat.Coprime p (Nat.card (GLAPPrimeCoreOf p K)) := by
    intro K
    unfold GLAPPrimeCoreOf
    rw [card_map_of_injective K.subtype_injective]
    exact CFSG.pPrimeCore_coprime_card
  have hnotdvd : ∀ K : Subgroup G, K ≤ GLADelta p D → ¬ p ∣ Nat.card K := by
    intro K hK hdvd
    have hle : K ≤ GLAPPrimeCoreOf p (centralizer {d₀}) := fun x hx =>
      mem_glaDelta_iff.mp (hK hx) d₀ hd₀D hd₀
    exact (Nat.Prime.coprime_iff_not_dvd hp).mp (hcop _) (hdvd.trans (card_dvd_of_le hle))
  have hconj : ∀ g : G, CFSG.conjugate (GLADelta p D) g = GLADelta p (CFSG.conjugate D g) := by
    intro g
    ext x
    rw [mem_conjugate_iff_conj_mem, mem_glaDelta_iff, mem_glaDelta_iff]
    constructor
    · intro h d' hd' hd'1
      rw [mem_conjugate_iff_conj_mem] at hd'
      have hd1 : g * d' * g⁻¹ ≠ 1 := by
        intro h1
        apply hd'1
        calc d' = g⁻¹ * (g * d' * g⁻¹) * g := by group
          _ = 1 := by rw [h1]; group
      have h2 := h _ hd' hd1
      have htrans := conjugate_glaPPrimeCoreOf_centralizer p (g * d' * g⁻¹) g
      rw [show g⁻¹ * (g * d' * g⁻¹) * g = d' by group] at htrans
      rw [← htrans, mem_conjugate_iff_conj_mem]
      exact h2
    · intro h d hd hd1
      have hd' : g⁻¹ * d * g ∈ CFSG.conjugate D g := by
        rw [mem_conjugate_iff_conj_mem, show g * (g⁻¹ * d * g) * g⁻¹ = d by group]
        exact hd
      have hd'1 : g⁻¹ * d * g ≠ 1 := by
        intro h1
        apply hd1
        calc d = g * (g⁻¹ * d * g) * g⁻¹ := by group
          _ = 1 := by rw [h1]; group
      have h2 := h _ hd' hd'1
      rw [← conjugate_glaPPrimeCoreOf_centralizer, mem_conjugate_iff_conj_mem] at h2
      exact h2
  have hND : normalizer (D : Set G) ≤ normalizer (GLADelta p D : Set G) := by
    intro g hg
    rw [mem_normalizer_iff_conjugate_eq, hconj, mem_normalizer_iff_conjugate_eq.mp hg]
  have hΔN : GLADelta p D ≤ normalizer (D : Set G) := hΔC.trans (centralizer_le_normalizer _)
  refine ⟨hΔC, hnotdvd _ le_rfl, hconj, ⟨hΔN, (normal_subgroupOf_iff_le_normalizer hΔN).mpr hND⟩,
    fun B hB hDB => ?_⟩
  have : IsMulCommutative B := hB.1
  have hBC : B ≤ centralizer (D : Set G) := by
    intro b hb
    rw [mem_centralizer_iff]
    intro d hd
    exact congrArg Subtype.val (mul_comm' (⟨d, hDB hd⟩ : B) ⟨b, hb⟩)
  have hBN : B ≤ normalizer (GLADelta p D : Set G) :=
    hBC.trans ((centralizer_le_normalizer _).trans hND)
  have hcommle : ⁅GLADelta p D, B⁆ ≤ GLADelta p D := by
    rw [commutator_le]
    intro x hx b hb
    rw [commutatorElement_def]
    have h1 : b * x⁻¹ * b⁻¹ ∈ GLADelta p D :=
      (mem_normalizer_iff.mp (hBN hb) x⁻¹).mp (inv_mem hx)
    rw [mul_assoc, mul_assoc, ← mul_assoc b]
    exact mul_mem hx h1
  refine ⟨hBN, hcommle, fun b hb => ?_, hnotdvd _ hcommle⟩
  rw [mem_normalizer_iff_conjugate_eq]
  unfold CFSG.conjugate
  rw [map_commutator]
  have h1 : (GLADelta p D).map (MulAut.conj b⁻¹).toMonoidHom = GLADelta p D :=
    mem_normalizer_iff_conjugate_eq.mp (hBN hb)
  have h2 : B.map (MulAut.conj b⁻¹).toMonoidHom = B :=
    mem_normalizer_iff_conjugate_eq.mp (le_normalizer hb)
  rw [h1, h2]

end CFSG.LocalAnalysis.GorensteinLyons
