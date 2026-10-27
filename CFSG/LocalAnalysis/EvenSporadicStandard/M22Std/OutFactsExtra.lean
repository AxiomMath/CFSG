module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.M22A6
public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.OutFactsUnique

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.M22Std

open Subgroup CFSG.EvenSporadicStandard.M22Std.TabCheck CFSG.Blueprint.NativeSporadic
  CFSG.EvenSporadicStandard.M23Std

theorem aut_mul_conj_mul_inv {Y : Type*} [Group Y] (α : MulAut Y) (x : Y) :
    α * MulAut.conj x * α⁻¹ = MulAut.conj (α x) := by
  ext y
  simp [MulAut.conj_apply]

theorem mem_normalizer_innerImage_iff {Y : Type*} [Group Y] (hinj : Function.Injective
    (MulAut.conj : Y →* MulAut Y)) {F : Subgroup Y} {α : MulAut Y} :
    α ∈ normalizer ((innerImage Y F : Subgroup (MulAut Y)) : Set (MulAut Y)) ↔
      ∀ x, x ∈ F ↔ α x ∈ F := by
  have hmem : ∀ x, MulAut.conj x ∈ innerImage Y F ↔ x ∈ F := fun x =>
    Subgroup.mem_map_iff_mem hinj
  rw [Subgroup.mem_normalizer_iff]
  constructor
  · intro h x
    have := h (MulAut.conj x)
    rwa [hmem, aut_mul_conj_mul_inv, hmem] at this
  · intro h γ
    constructor
    · rintro hγ
      obtain ⟨x, hx, rfl⟩ := hγ
      rw [aut_mul_conj_mul_inv]
      exact ⟨α x, (h x).1 hx, rfl⟩
    · intro hγ
      obtain ⟨f, hf, hfγ⟩ := hγ
      have h1 : γ = α⁻¹ * MulAut.conj f * α := by
        rw [hfγ]
        group
      have h2 : α⁻¹ * MulAut.conj f * α = MulAut.conj (α⁻¹ f) := by
        have := aut_mul_conj_mul_inv α⁻¹ f
        rwa [inv_inv] at this
      refine ⟨α⁻¹ f, ?_, by rw [h1, h2]⟩
      have := (h (α⁻¹ f)).2
      rw [MulAut.apply_inv_self] at this
      exact this hf

section Card


theorem card_normalizer_F1 {F : Subgroup (Carrier .M22)}
    (hF : ∀ x, x ∈ F ↔ x = 1 ∨ x ∈ invs16 1) (D : NData (⊤ : Subgroup (Carrier .M22)) F) :
    Nat.card (normalizer (F : Set (Carrier .M22))) = 5760 := by
  obtain ⟨ψ, hψ, hker⟩ := normQuot_pinned hF D
  have h1 := Subgroup.card_ker_mul_card_range ψ
  have hFN : F ≤ normalizer (F : Set (Carrier .M22)) := Subgroup.le_normalizer
  rw [MonoidHom.range_eq_top_of_surjective ψ hψ, Subgroup.card_top, hker,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hFN).toEquiv, D.F_card,
    nat_card_alternatingGroup, Nat.card_eq_fintype_card (α := Fin 6)] at h1
  rw [← h1]
  simp [Nat.factorial]

variable {F : Subgroup (Carrier .M22)}

theorem betaAut_mem_normalizer (hF : ∀ x, x ∈ F ↔ x = 1 ∨ x ∈ invs16 1) :
    betaAut ∈ normalizer ((innerImage (Carrier .M22) F : Subgroup (MulAut (Carrier .M22))) :
      Set (MulAut (Carrier .M22))) :=
  (mem_normalizer_innerImage_iff conj_injective_m22).2 (s0_normal hF betaAut betaAut_mem_s0)

theorem card_normalizer_innerImage (hF : ∀ x, x ∈ F ↔ x = 1 ∨ x ∈ invs16 1)
    (D : NData (⊤ : Subgroup (Carrier .M22)) F) :
    Nat.card ↥(normalizer ((innerImage (Carrier .M22) F : Subgroup (MulAut (Carrier .M22))) :
      Set (MulAut (Carrier .M22)))) = 11520 := by
  set N : Subgroup (MulAut (Carrier .M22)) :=
    normalizer ((innerImage (Carrier .M22) F : Subgroup (MulAut (Carrier .M22))) :
      Set (MulAut (Carrier .M22))) with hN
  have hNI : innerImage (Carrier .M22) ⊤ ⊓ N =
      (normalizer (F : Set (Carrier .M22))).map MulAut.conj := by
    ext α
    constructor
    · rintro ⟨⟨y, -, rfl⟩, hα⟩
      refine ⟨y, ?_, rfl⟩
      show y ∈ normalizer (F : Set (Carrier .M22))
      rw [Subgroup.mem_normalizer_iff]
      intro x
      have hα' : MulAut.conj y ∈ N := hα
      have := (mem_normalizer_innerImage_iff conj_injective_m22).1 hα' x
      simpa [MulAut.conj_apply] using this
    · rintro ⟨y, hy, rfl⟩
      refine ⟨⟨y, Subgroup.mem_top _, rfl⟩, ?_⟩
      show MulAut.conj y ∈ N
      rw [hN, mem_normalizer_innerImage_iff conj_injective_m22]
      intro x
      have hy' : y ∈ normalizer (F : Set (Carrier .M22)) := hy
      simpa [MulAut.conj_apply] using Subgroup.mem_normalizer_iff.1 hy' x
  have : (innerImage (Carrier .M22) ⊤).Normal := by
    rw [innerImage_top_eq_inner]
    infer_instance
  have hrel : (innerImage (Carrier .M22) ⊤).relIndex N = 2 := by
    have hdvd := Subgroup.relIndex_dvd_index_of_normal (H := innerImage (Carrier .M22) ⊤) (K := N)
    rw [index_innerImage_top] at hdvd
    rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h | h
    · exact absurd (Subgroup.relIndex_eq_one.1 h (betaAut_mem_normalizer hF))
        betaAut_not_inner
    · exact h
  have h := Subgroup.relIndex_mul_card (H := innerImage (Carrier .M22) ⊤) (K := N)
  rw [hrel, hNI, Subgroup.card_map_of_injective conj_injective_m22,
    card_normalizer_F1 hF D] at h
  omega

end Card

end CFSG.EvenSporadicStandard.M22Std
