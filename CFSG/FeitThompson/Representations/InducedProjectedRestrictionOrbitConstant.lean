module

public import CFSG.FeitThompson.Representations.DadeSubsetSemidirectProduct
public import CFSG.FeitThompson.Representations.ClassFunctionInnerProductNorms
public import CFSG.FeitThompson.Definitions.NormalInducedCharacterFamily
import CFSG.FeitThompson.Representations.FrobeniusReciprocityClassFunctions
import CFSG.FeitThompson.Representations.ConjugationTransportsDadeSignalizers

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open Pointwise

variable {G : Type*} [Group G]

theorem mem_conjInv_image_iff {c y : G} {S : Set G} :
    y ∈ (fun x => c⁻¹ * x * c) '' S ↔ c * y * c⁻¹ ∈ S := by
  constructor
  · rintro ⟨s, hs, rfl⟩
    rwa [show c * (c⁻¹ * s * c) * c⁻¹ = s by group]
  · intro h
    exact ⟨c * y * c⁻¹, h, by group⟩

theorem normalizer_conjInv_image (c : G) (S : Set G) :
    Subgroup.normalizer ((fun x => c⁻¹ * x * c) '' S)
      = MulAut.conj c⁻¹ • Subgroup.normalizer S := by
  ext x
  rw [mem_conj_smul_iff, Subgroup.mem_set_normalizer_iff, Subgroup.mem_set_normalizer_iff]
  constructor
  · intro hx k
    have h := hx (c⁻¹ * k * c)
    rw [mem_conjInv_image_iff, mem_conjInv_image_iff,
      show c * (c⁻¹ * k * c) * c⁻¹ = k by group,
      show c * (x * (c⁻¹ * k * c) * x⁻¹) * c⁻¹
        = c⁻¹⁻¹ * x * c⁻¹ * k * (c⁻¹⁻¹ * x * c⁻¹)⁻¹ by group] at h
    exact h
  · intro hx h
    rw [mem_conjInv_image_iff, mem_conjInv_image_iff]
    have h2 := hx (c * h * c⁻¹)
    rw [show c⁻¹⁻¹ * x * c⁻¹ * (c * h * c⁻¹) * (c⁻¹⁻¹ * x * c⁻¹)⁻¹ = c * (x * h * x⁻¹) * c⁻¹
      by group] at h2
    exact h2

theorem conjInv_mem_conj_inv_smul_iff {X : Subgroup G} {c z : G} :
    c⁻¹ * z * c ∈ MulAut.conj c⁻¹ • X ↔ z ∈ X := by
  rw [mem_conj_smul_iff, show c⁻¹⁻¹ * (c⁻¹ * z * c) * c⁻¹ = z by group]

theorem indClassFun_eq_of_conj [Fintype G] {K K' : Subgroup G} (c : G)
    (hKK' : ∀ z : G, z ∈ K' ↔ c⁻¹ * z * c ∈ K) (θ : K → ℂ) (θ' : K' → ℂ)
    (hθ : ∀ (x : K) (y : K'), (y : G) = c * (x : G) * c⁻¹ → θ' y = θ x) :
    indClassFun K' θ' = indClassFun K θ := by
  have hmem : ∀ x : G, x ∈ K → c * x * c⁻¹ ∈ K' := fun x hx =>
    (hKK' _).2 (by rwa [show c⁻¹ * (c * x * c⁻¹) * c = x by group])
  have hmem' : ∀ x : G, c * x * c⁻¹ ∈ K' → x ∈ K := fun x hx => by
    have := (hKK' _).1 hx
    rwa [show c⁻¹ * (c * x * c⁻¹) * c = x by group] at this
  have hcard : Nat.card K' = Nat.card K := by
    refine Nat.card_congr ⟨fun y => ⟨c⁻¹ * y * c, (hKK' _).1 y.2⟩,
      fun x => ⟨c * x * c⁻¹, hmem _ x.2⟩, fun y => ?_, fun x => ?_⟩
    · exact Subtype.ext (by group)
    · exact Subtype.ext (by group)
  funext g
  rw [indClassFun_eq_sum_extendByZero, indClassFun_eq_sum_extendByZero, hcard]
  congr 1
  refine (Fintype.sum_equiv (Equiv.mulRight c⁻¹) _ _ fun s => ?_).symm
  have hrw : ((Equiv.mulRight c⁻¹) s)⁻¹ * g * ((Equiv.mulRight c⁻¹) s)
      = c * (s⁻¹ * g * s) * c⁻¹ := by
    simp only [Equiv.coe_mulRight]
    group
  rw [hrw]
  by_cases hs : s⁻¹ * g * s ∈ K
  · rw [extendByZero_apply_coe K θ ⟨_, hs⟩,
      extendByZero_apply_coe K' θ' ⟨_, hmem _ hs⟩, hθ ⟨_, hs⟩ ⟨_, hmem _ hs⟩ rfl]
  · rw [extendByZero_of_notMem K θ hs, extendByZero_of_notMem K' θ' (fun hc => hs (hmem' _ hc))]

variable {L : Subgroup G} {A B : Set G} {H : G → Subgroup G} {l : G}

theorem dadeStab_conjInv_image (hl : l ∈ L) :
    dadeStab L ((fun x => l⁻¹ * x * l) '' B) = MulAut.conj l⁻¹ • dadeStab L B := by
  rw [dadeStab_eq_inf, dadeStab_eq_inf, normalizer_conjInv_image, Subgroup.smul_inf,
    Subgroup.conj_smul_eq_self_of_mem (inv_mem hl)]

namespace IsDadeData

variable [Finite G]

theorem conjInv_image_subset (hD : IsDadeData L A H) (hBA : B ⊆ A) (hl : l ∈ L) :
    (fun x => l⁻¹ * x * l) '' B ⊆ A := by
  rintro y ⟨b, hb, rfl⟩
  simpa using hD.conj_mem (hBA hb) (inv_mem hl)

theorem dadeInter_conjInv_image (hD : IsDadeData L A H) (hBA : B ⊆ A) (hl : l ∈ L) :
    dadeInter H ((fun x => l⁻¹ * x * l) '' B) = MulAut.conj l⁻¹ • dadeInter H B := by
  simpa using (hD.conj_smul_dadeInter hBA (inv_mem hl)).symm

theorem dadeSubsetGroup_conjInv_image (hD : IsDadeData L A H) (hBA : B ⊆ A) (hl : l ∈ L) :
    dadeSubsetGroup H L ((fun x => l⁻¹ * x * l) '' B)
      = MulAut.conj l⁻¹ • dadeSubsetGroup H L B := by
  rw [dadeSubsetGroup_eq_sup, dadeSubsetGroup_eq_sup, Subgroup.smul_sup,
    hD.dadeInter_conjInv_image hBA hl, dadeStab_conjInv_image hl]

theorem indClassFun_dadePullback_conjInv_image [Fintype G] (hD : IsDadeData L A H)
    (hBA : B ⊆ A) (hB : B.Nonempty) (hl : l ∈ L) {f : L → ℂ} (hf : IsClassFun f) :
    indClassFun (dadeSubsetGroup H L ((fun x => l⁻¹ * x * l) '' B))
        (dadePullback (hD.dadeProj (hD.conjInv_image_subset hBA hl) (hB.image _)) f)
      = indClassFun (dadeSubsetGroup H L B) (dadePullback (hD.dadeProj hBA hB) f) := by
  have hB'A : (fun x => l⁻¹ * x * l) '' B ⊆ A := hD.conjInv_image_subset hBA hl
  have hB'ne : ((fun x => l⁻¹ * x * l) '' B).Nonempty := hB.image _
  refine indClassFun_eq_of_conj l⁻¹ ?_ _ _ ?_
  · intro z
    rw [hD.dadeSubsetGroup_conjInv_image hBA hl]
    exact mem_conj_smul_iff
  · intro x y hxy
    obtain ⟨h, hh, u, hu, hx⟩ := (hD.mem_dadeSubsetGroup_iff hBA).1 x.2
    have hh' : l⁻¹ * h * l ∈ dadeInter H ((fun x => l⁻¹ * x * l) '' B) := by
      rw [hD.dadeInter_conjInv_image hBA hl]
      exact conjInv_mem_conj_inv_smul_iff.2 hh
    have hu' : l⁻¹ * u * l ∈ dadeStab L ((fun x => l⁻¹ * x * l) '' B) := by
      rw [dadeStab_conjInv_image hl]
      exact conjInv_mem_conj_inv_smul_iff.2 hu
    have hx' : x = ⟨h * u, (hD.mem_dadeSubsetGroup_iff hBA).2 ⟨h, hh, u, hu, rfl⟩⟩ :=
      Subtype.ext hx.symm
    have hy' : y = ⟨(l⁻¹ * h * l) * (l⁻¹ * u * l),
        (hD.mem_dadeSubsetGroup_iff hB'A).2 ⟨_, hh', _, hu', rfl⟩⟩ := by
      refine Subtype.ext ?_
      rw [hxy, ← hx]
      group
    rw [hx', hy', hD.dadePullback_dadeProj_apply_mul hB'A hB'ne f hh' hu',
      hD.dadePullback_dadeProj_apply_mul hBA hB f hh hu]
    have key : (⟨l⁻¹ * u * l, dadeStab_le_left hu'⟩ : L)
        = (⟨l, hl⟩ : L)⁻¹ * ⟨u, dadeStab_le_left hu⟩ * (⟨l, hl⟩ : L)⁻¹⁻¹ := by
      apply Subtype.ext
      simp
    rw [key, hf.conj]

theorem indClassFun_dadePullback_conjInv_image' [Fintype G] (hD : IsDadeData L A H)
    (hBA : B ⊆ A) (hB : B.Nonempty) (hl : l ∈ L) {f : L → ℂ} (hf : f ∈ classFun L) :
    indClassFun (dadeSubsetGroup H L ((fun x => l⁻¹ * x * l) '' B))
        (dadePullback (hD.dadeProj (hD.conjInv_image_subset hBA hl) (hB.image _)) f)
      = indClassFun (dadeSubsetGroup H L B) (dadePullback (hD.dadeProj hBA hB) f) :=
  hD.indClassFun_dadePullback_conjInv_image hBA hB hl
    (isClassFun_iff.2 fun x g => classFun.apply_conj hf g x)

end IsDadeData

end CFSG.FeitThompson
