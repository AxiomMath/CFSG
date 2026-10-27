module

public import CFSG.LocalAnalysis.EvenBN.U5.LinLayer
public import CFSG.LocalAnalysis.EvenBN.U5.Sec3ProofNineSylow
import CFSG.LocalAnalysis.EvenBN.U5.LinTwin38

public noncomputable section

namespace CFSG.LocalAnalysis.EvenBN.U5

open Subgroup CFSG.Open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.Blueprint
open CFSG.LocalAnalysis.EvenBN.Common.NormalizerQuotient

namespace Data

variable {G : Type} [Group G] [Finite G] {f : ℕ} {K : Type} [Field K]
  {h : UnitaryFieldData 2 f K} {d : Data G h}

theorem lin_eq_bot (hl : d.LinCtx) {Y : Subgroup (s39a1H d ⧸ s39a1O d)} (hY : IsPGroup 2 Y)
    (hΛY : s39a1Λ d ≤ normalizer (Y : Set (s39a1H d ⧸ s39a1O d))) : Y = ⊥ := by
  have hΛ : s39a1Λ d = CFSG.layer (s39a1H d ⧸ s39a1O d) := (lin_layer_facts hl).2.2
  have hs : IsSimpleGroup (s39a1Λ d) := by
    rw [hΛ]
    exact (lin_layer_facts hl).1
  have hna : ∃ x y : s39a1Λ d, x * y ≠ y * x := by
    rw [hΛ]
    exact lin_layer_nonabelian hl
  have hΛn : (s39a1Λ d).Normal := by
    rw [hΛ]
    haveI : (CFSG.layer (s39a1H d ⧸ s39a1O d)).Characteristic :=
      CFSG.LocalCores.layer_characteristic
    infer_instance
  have hC : centralizer ((s39a1Λ d : Subgroup (s39a1H d ⧸ s39a1O d)) :
      Set (s39a1H d ⧸ s39a1O d)) = ⊥ := by
    rw [hΛ]
    exact lin_centralizer_layer hl
  have hYΛ : Y ⊓ s39a1Λ d = ⊥ := by
    rw [eq_bot_iff]
    rintro c ⟨hcY, hcΛ⟩
    rw [Subgroup.mem_bot]
    exact s39a1_ebn_eq_one (le_refl _) hs hna hY hΛY hcY hcΛ
  have hYC : Y ≤ centralizer (s39a1Λ d : Set (s39a1H d ⧸ s39a1O d)) := by
    intro y hy
    rw [Subgroup.mem_centralizer_iff]
    intro l hl'
    have hA : l * y * l⁻¹ ∈ Y := (mem_set_normalizer_iff.mp (hΛY hl') y).mp hy
    have hB : l * (y * l⁻¹ * y⁻¹) ∈ s39a1Λ d :=
      mul_mem hl' (Subgroup.Normal.conj_mem hΛn l⁻¹ (inv_mem hl') y)
    have hmem : l * y * l⁻¹ * y⁻¹ ∈ Y ⊓ s39a1Λ d := by
      have hY1 : l * y * l⁻¹ * y⁻¹ ∈ Y := mul_mem hA (inv_mem hy)
      have hΛ1 : l * y * l⁻¹ * y⁻¹ ∈ s39a1Λ d := by
        have e : l * y * l⁻¹ * y⁻¹ = l * (y * l⁻¹ * y⁻¹) := by group
        rw [e]
        exact hB
      exact Subgroup.mem_inf.mpr ⟨hY1, hΛ1⟩
    rw [hYΛ, Subgroup.mem_bot, mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at hmem
    exact hmem
  rw [eq_bot_iff]
  intro y hy
  have h1 : y ∈ centralizer (s39a1Λ d : Set (s39a1H d ⧸ s39a1O d)) := hYC hy
  rw [hC, Subgroup.mem_bot] at h1
  exact h1

theorem lin_card_le (hl : d.LinCtx) {X : Subgroup G} (hX : X ≤ d.M₂) (hX2 : IsPGroup 2 X) :
    Nat.card X ≤ (2 ^ f) ^ 6 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q, hQ⟩ := (hX2.comap_subtype (K := d.M₂)).exists_le_sylow
  have hQS : IsSylowOf 2 ((Q : Subgroup d.M₂).map d.M₂.subtype) d.M₂ := ⟨Q, rfl⟩
  have hXQ : X ≤ (Q : Subgroup d.M₂).map d.M₂.subtype := fun x hx =>
    ⟨⟨x, hX hx⟩, hQ hx, rfl⟩
  obtain ⟨R₁, R₂, hrad⟩ := lin_exists_radicals_of_isSylowOf_M₂ hl hQS
  calc Nat.card X ≤ Nat.card ((Q : Subgroup d.M₂).map d.M₂.subtype) :=
        Subgroup.card_le_of_le hXQ
    _ = ((2 ^ f) ^ 2) ^ 3 := hrad.card
    _ = (2 ^ f) ^ 6 := by ring

theorem lin_E_inf_H_eq_bot (hl : d.LinCtx) (hL₂ : d.L₂ = d.E ⊔ d.M₂) :
    d.E ⊓ centralizer (d.I₂ : Set G) = ⊥ := by
  have hE2 : IsPGroup 2 d.E := Hyp.s39a1_isPGroup_E hl.gms hl.hyp
  have hOodd : Odd (Nat.card (s39a1O d)) := GMSK.odd_card_standardComponentOddCore _
  have hMN : d.M₂ ≤ normalizer (d.E : Set G) :=
    (le_sup_right.trans hL₂.symm.le).trans d.L₂_le_normalizer_E
  set Y' : Subgroup (s39a1H d) := d.E.subgroupOf (s39a1H d) with hY'
  have hY'2 : IsPGroup 2 Y' := hE2.comap_subtype
  have hMY : d.M₂.subgroupOf (s39a1H d) ≤ normalizer (Y' : Set (s39a1H d)) := by
    intro m hm
    rw [mem_normalizer_iff]
    intro y
    rw [hY', mem_subgroupOf, mem_subgroupOf, coe_mul, coe_mul, coe_inv]
    exact (mem_normalizer_iff.1 (hMN (mem_subgroupOf.1 hm))) y
  have hYb : Y'.map (s39a1θ d) = ⊥ :=
    lin_eq_bot hl (hY'2.map _) ((map_mono hMY).trans (le_normalizer_map _))
  rw [eq_bot_iff]
  rintro x ⟨hxE, hxH⟩
  rw [mem_bot]
  have hxY : (⟨x, hxH⟩ : s39a1H d) ∈ Y' := mem_subgroupOf.2 hxE
  have h1 : s39a1θ d ⟨x, hxH⟩ = 1 := by
    have : s39a1θ d ⟨x, hxH⟩ ∈ Y'.map (s39a1θ d) := mem_map_of_mem _ hxY
    rwa [hYb, mem_bot] at this
  have hxO : (⟨x, hxH⟩ : s39a1H d) ∈ s39a1O d := (QuotientGroup.eq_one_iff _).1 h1
  obtain ⟨k, hk⟩ := hE2 ⟨x, hxE⟩
  have hk' : (⟨x, hxH⟩ : s39a1H d) ^ 2 ^ k = 1 :=
    Subtype.ext (by simpa using congrArg Subtype.val hk)
  simpa using congrArg Subtype.val (eq_one_of_mem_of_pow_two_pow hOodd hxO hk')

theorem lin_sylow₂ (hl : d.LinCtx) (hL₂ : d.L₂ = d.E ⊔ d.M₂) {S : Subgroup G}
    (hS : IsSylowOf 2 S d.L₂) :
    S ⊓ centralizer (d.I₂ : Set G) = S ⊓ d.M₂ ∧ IsSylowOf 2 (S ⊓ d.M₂) d.M₂ := by
  have hE2 : IsPGroup 2 d.E := Hyp.s39a1_isPGroup_E hl.gms hl.hyp
  have hEH := lin_E_inf_H_eq_bot hl hL₂
  have hMH : d.M₂ ≤ centralizer (d.I₂ : Set G) := s39a1_M₂_le_centralizer d
  have hEM : d.E ⊓ d.M₂ = ⊥ := eq_bot_iff.2 ((inf_le_inf_left _ hMH).trans hEH.le)
  have hMN : d.M₂ ≤ normalizer (d.E : Set G) :=
    (le_sup_right.trans hL₂.symm.le).trans d.L₂_le_normalizer_E
  refine ⟨le_antisymm ?_ (inf_le_inf_left _ hMH),
    s39a1_isSylowOf_inf_of_complement hE2 hL₂ d.L₂_le_normalizer_E hEM hS⟩
  rintro s ⟨hsS, hsH⟩
  refine ⟨hsS, ?_⟩
  have hsL : s ∈ d.E ⊔ d.M₂ := hL₂ ▸ hS.le hsS
  obtain ⟨e, he, m, hm, rfl⟩ := exists_mul_of_mem_sup_of_le_normalizer hMN hsL
  have heH : e ∈ centralizer (d.I₂ : Set G) := by
    have e' : e = e * m * m⁻¹ := by group
    rw [e']
    exact mul_mem hsH (inv_mem (hMH hm))
  have he1 : e = 1 := by
    have : e ∈ d.E ⊓ centralizer (d.I₂ : Set G) := ⟨he, heH⟩
    rwa [hEH, mem_bot] at this
  rw [he1, one_mul]
  exact hm

theorem lin_card_le₅ (hl : d.LinCtx) {X : Subgroup G} (hX : X ≤ d.M₅) (hX2 : IsPGroup 2 X) :
    Nat.card X ≤ (2 ^ f) ^ 6 := by
  obtain ⟨hM₅, -, -⟩ := hl.hyp.s39a1_conj_r
  have hle : X.map (MulAut.conj d.r⁻¹).toMonoidHom ≤ d.M₂ := by
    rintro _ ⟨y, hy, rfl⟩
    rw [hM₅] at hX
    obtain ⟨m, hm, rfl⟩ := hX hy
    simpa [mul_assoc] using hm
  rw [← Subgroup.card_map_of_injective (f := (MulAut.conj d.r⁻¹).toMonoidHom)
    (MulAut.conj d.r⁻¹).injective]
  exact lin_card_le hl hle (hX2.map _)

end Data

end CFSG.LocalAnalysis.EvenBN.U5
