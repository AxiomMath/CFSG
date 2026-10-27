module

public import CFSG.Foundations.Basic
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherGoldschmidtFour
public import CFSG.LocalAnalysis.ComponentClassification.OddCore

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open CFSG.ComponentClassification
open Subgroup CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.GoldschmidtFour
open scoped commutatorElement

private theorem gy_construction_aux {Y : Type} [Group Y] [Finite Y] {P : Sylow 2 Y}
    {V : Subgroup Y} (hV : GoldschmidtFour.Hyp P V) {u : Y} (huP : u ∈ (P : Subgroup Y))
    (huV : ∃ k : Y, u ∈ rightConjugate V k) :
    ∃ (V₀ V₂ : Subgroup Y) (k g : Y), u ∈ rightConjugate V k ∧
      V₀ = V ⊓ rightConjugate V k ∧ V₀ ≤ V₂ ∧ V₂ ≤ V ∧
      (∀ e : Y, e ∈ V₂ ↔ e ∈ V ∧ e * u * e⁻¹ * u⁻¹ ∈ V₀) ∧
      rightConjugate V₂ g ≤ P ∧ V ⊓ rightConjugate V₂ g = rightConjugate V₀ g := by
  have : Nonempty {k : Y // u ∈ rightConjugate V k} := by
    obtain ⟨k, hk⟩ := huV
    exact ⟨⟨k, hk⟩⟩
  obtain ⟨⟨k, hk⟩, hmax⟩ := Finite.exists_max
    (fun k : {k : Y // u ∈ rightConjugate V k} =>
      Nat.card (V ⊓ rightConjugate V k.1 : Subgroup Y))
  set V' := rightConjugate V k with hV'def
  set V0 := V ⊓ V'
  set V1 := V0 ⊔ Subgroup.zpowers u
  have hu2 : u ^ 2 = 1 := by
    have h := hV.sq_eq_one ((mem_rightConjugate_iff _ _ _).1 hk)
    rw [conj_pow] at h
    have : u ^ 2 = k⁻¹ * (k * u ^ 2 * k⁻¹) * k := by group
    rw [this, h]
    group
  have huN : u ∈ Subgroup.normalizer (V : Set Y) := hV.le_normalizer huP
  have hV'comm : ∀ {a b : Y}, a ∈ V' → b ∈ V' → a * b = b * a := by
    intro a b ha hb
    rw [hV'def, mem_rightConjugate_iff] at ha hb
    have h := hV.comm ha hb
    have h' : k * (a * b) * k⁻¹ = k * (b * a) * k⁻¹ := by
      calc k * (a * b) * k⁻¹ = (k * a * k⁻¹) * (k * b * k⁻¹) := by group
        _ = (k * b * k⁻¹) * (k * a * k⁻¹) := h
        _ = k * (b * a) * k⁻¹ := by group
    simpa using h'
  set ψ := commHom hV.elem.1 huN
  set V2 := (V0.comap ψ).map V.subtype
  have hV2V : V2 ≤ V := by
    rintro _ ⟨e, -, rfl⟩
    exact e.2
  have hV2mem : ∀ {e : Y}, e ∈ V2 → ⁅e, u⁆ ∈ V0 := by
    rintro _ ⟨e, he, rfl⟩
    exact he
  have hV0V : V0 ≤ V := inf_le_left
  have hV0V' : V0 ≤ V' := inf_le_right
  have huV' : u ∈ V' := hk
  have hV1V' : V1 ≤ V' := sup_le hV0V' (Subgroup.zpowers_le.2 huV')
  have hV0V2 : V0 ≤ V2 := by
    intro e he
    refine ⟨⟨e, hV0V he⟩, ?_, rfl⟩
    show ⁅e, u⁆ ∈ V0
    rw [commutatorElement_eq_one_iff_mul_comm.2 (hV'comm (hV0V' he) huV')]
    exact V0.one_mem
  have hV'N1 : V' ≤ Subgroup.normalizer (V1 : Set Y) := by
    intro x hx
    apply mem_normalizer_of_conj_mem
    intro y hy
    rw [hV'comm hx (hV1V' hy), mul_inv_cancel_right]
    exact hy
  have hV2N1 : V2 ≤ Subgroup.normalizer (V1 : Set Y) := by
    intro e he
    have heV := hV2V he
    apply mem_normalizer_of_conj_mem
    have hle : V1 ≤ V1.comap (MulAut.conj e).toMonoidHom := by
      refine sup_le ?_ ?_
      · intro z hz
        show e * z * e⁻¹ ∈ V1
        rw [hV.comm heV (hV0V hz), mul_inv_cancel_right]
        exact Subgroup.mem_sup_left hz
      · rw [Subgroup.zpowers_le]
        show e * u * e⁻¹ ∈ V1
        have h : e * u * e⁻¹ = ⁅e, u⁆ * u := by rw [commutatorElement_def]; group
        rw [h]
        exact V1.mul_mem (Subgroup.mem_sup_left (hV2mem he))
          (Subgroup.mem_sup_right (Subgroup.mem_zpowers u))
    intro y hy
    exact hle hy
  have hV2p : IsPGroup 2 V2 := hV.isPGroup.to_le hV2V
  have hV'p : IsPGroup 2 V' := isPGroup_rightConjugate hV.isPGroup k
  obtain ⟨a, haN, R, hRp, hV'R, hV2R⟩ :=
    exists_conj_le_of_isPGroup hV2p hV'p hV2N1 hV'N1
  have hRN : R ≤ Subgroup.normalizer (V' : Set Y) := hV.le_normalizer_of_isPGroup hRp hV'R
  have hstep : rightConjugate (rightConjugate V2 a) k⁻¹ ≤ Subgroup.normalizer (V : Set Y) := by
    have h := rightConjugate_le_normalizer (hV2R.trans hRN) k⁻¹
    rwa [hV'def, rightConjugate_rightConjugate_inv] at h
  obtain ⟨n, hnN, R', hR'p, hPR', hnR'⟩ := exists_conj_le_of_isPGroup
    (isPGroup_rightConjugate (isPGroup_rightConjugate hV2p a) k⁻¹) P.isPGroup' hstep
    hV.le_normalizer
  have hR'P : R' = P := P.is_maximal' hR'p hPR'
  rw [hR'P, rightConjugate_mul, rightConjugate_mul, ← mul_assoc] at hnR'
  set h := a * k⁻¹ * n with hhdef
  have hV1h : rightConjugate V1 h ≤ V := by
    have h1 : rightConjugate V1 h = rightConjugate (rightConjugate V1 k⁻¹) n := by
      rw [hhdef, ← rightConjugate_mul, ← rightConjugate_mul,
        rightConjugate_of_mem_normalizer haN]
    rw [h1]
    calc rightConjugate (rightConjugate V1 k⁻¹) n
        ≤ rightConjugate (rightConjugate V' k⁻¹) n :=
          rightConjugate_mono (rightConjugate_mono hV1V' _) _
      _ = V := by
          rw [hV'def, rightConjugate_rightConjugate_inv, rightConjugate_of_mem_normalizer hnN]
  have huh : u ∈ rightConjugate V h⁻¹ := by
    rw [mem_rightConjugate_iff, inv_inv]
    exact hV1h (conj_mem_rightConjugate (Subgroup.mem_sup_right (Subgroup.mem_zpowers u)) h)
  have hle : Nat.card (V ⊓ rightConjugate V h⁻¹ : Subgroup Y) ≤ Nat.card V0 :=
    hmax ⟨h⁻¹, huh⟩
  have hcardh : Nat.card (V ⊓ rightConjugate V h : Subgroup Y) =
      Nat.card (V ⊓ rightConjugate V h⁻¹ : Subgroup Y) := by
    rw [← rightConjugate_card (V ⊓ rightConjugate V h⁻¹) h, rightConjugate_inf,
      rightConjugate_inv_rightConjugate, inf_comm]
  have hV0h : rightConjugate V0 h = V ⊓ rightConjugate V h := by
    apply Subgroup.eq_of_le_of_card_ge
    · exact le_inf ((rightConjugate_mono le_sup_left h).trans hV1h)
        (rightConjugate_mono hV0V h)
    · rw [rightConjugate_card, hcardh]
      exact hle
  have hinter : V ⊓ rightConjugate V2 h = rightConjugate V0 h := by
    apply le_antisymm
    · rw [hV0h]
      exact inf_le_inf_left _ (rightConjugate_mono hV2V h)
    · exact le_inf (hV0h ▸ inf_le_left) (rightConjugate_mono hV0V2 h)
  refine ⟨V0, V2, k, h, hk, rfl, hV0V2, hV2V, ?_, hnR', hinter⟩
  intro e
  constructor
  · intro he
    exact ⟨hV2V he, by simpa [commutatorElement_def] using hV2mem he⟩
  · rintro ⟨heV, hec⟩
    refine ⟨⟨e, heV⟩, ?_, rfl⟩
    show ψ ⟨e, heV⟩ ∈ V0
    rw [commHom_apply, commutatorElement_def]
    exact hec

theorem gy_construction {Y : Type} [Group Y] [Finite Y] {P : Sylow 2 Y} {V : Subgroup Y}
    (hV : GoldschmidtFour.Hyp P V) {u : Y} (huP : u ∈ (P : Subgroup Y))
    (huV : ∃ k : Y, u ∈ CFSG.conjugate V k) :
    ∃ (V₀ V₂ : Subgroup Y) (k g : Y), u ∈ CFSG.conjugate V k ∧ V₀ = V ⊓ CFSG.conjugate V k ∧
      V₀ ≤ V₂ ∧ V₂ ≤ V ∧ (∀ e : Y, e ∈ V₂ ↔ e ∈ V ∧ e * u * e⁻¹ * u⁻¹ ∈ V₀) ∧
      CFSG.conjugate V₂ g ≤ P ∧ V ⊓ CFSG.conjugate V₂ g = CFSG.conjugate V₀ g := by
  obtain ⟨V0, V2, k, g, hk, hV0, hV0V2, hV2V, hmem, hg, hinter⟩ :=
    gy_construction_aux hV huP huV
  exact ⟨V0, V2, k, g, hk, hV0, hV0V2, hV2V, hmem, hg, hinter⟩

end CFSG.OddStandard.SmallF3.Omega
