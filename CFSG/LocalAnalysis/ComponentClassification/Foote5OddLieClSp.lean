module

public import CFSG.LocalAnalysis.ComponentClassification.Foote5OddLieCoreX
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneSpCent
public import CFSG.ClassicalInvolution.Balance.LayerGenerationTransport

public section

namespace CFSG.ComponentClassification.Foote5.OddLieCore.ClSp

open Matrix CFSG Subgroup CFSG.Assembly.LowTwoRank
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
open CFSG.ComponentClassification.TBLit CFSG.ComponentClassification.Burgoyne.PSL
open CFSG.ComponentClassification.Burgoyne.Proj CFSG.ComponentClassification.Burgoyne.Sp

variable {r : ℕ} {K : Type} [Field K]

abbrev conjProj (r : ℕ) (K : Type) [Field K] :
    StatedSp r K →* MulAut (StatedProj (StatedSp r K)) :=
  (MulAut.conj : StatedProj (StatedSp r K) →* MulAut (StatedProj (StatedSp r K))).comp (proj r K)

theorem conjProj_range_normal : (conjProj r K).range.Normal := by
  have h : (conjProj r K).range =
      (MulAut.conj : StatedProj (StatedSp r K) →* MulAut (StatedProj (StatedSp r K))).range := by
    rw [MonoidHom.range_comp,
      MonoidHom.range_eq_top.mpr (SymplecticHigher.proj_surjective (r := r) (K := K)),
      ← MonoidHom.range_eq_map]
  rw [h]
  exact conj_range_normal

variable {i : MulAut (StatedProj (StatedSp r K))}
  {R : Subgroup (MulAut (StatedProj (StatedSp r K)))}

section Fix

variable [Finite K]
  (hinj : Function.Injective
    (MulAut.conj : StatedProj (StatedSp r K) →* MulAut (StatedProj (StatedSp r K))))
  (hRodd : Odd (Nat.card R)) (hRi : ∀ y ∈ R, y * i = i * y)
  (hRc : ∀ s, i s = s → Odd (orderOf s) → ∀ y ∈ R,
    MulAut.conj s * y * (MulAut.conj s)⁻¹ ∈ R)
include hinj hRodd hRi hRc

theorem fix_of_component (φ : StatedSp r K ≃* StatedSp r K)
    (hφ : ∀ g, i (proj r K g) = proj r K (φ g)) {Q : Subgroup (StatedSp r K)}
    (hQ : Open.IsComponentOf Q (ClassicalInvolution.Balance.fixedGroup φ)) {y}
    (hy : y ∈ R) {g : StatedSp r K} (hg : g ∈ Q) : y (proj r K g) = proj r K g := by
  have hker : (conjProj r K).ker ≤ center (StatedSp r K) := by
    intro x hx
    have h1 : proj r K x = 1 := hinj (by rw [map_one]; exact hx)
    exact scalars_subgroupOf_le_center ((QuotientGroup.eq_one_iff _).1 h1)
  have hδ : ∀ x : StatedSp r K,
      i * conjProj r K (1 * x * 1⁻¹) * i⁻¹ = conjProj r K (1 * φ x * 1⁻¹) := fun x => by
    simp only [one_mul, inv_one, mul_one]
    change i * MulAut.conj (proj r K x) * i⁻¹ = MulAut.conj (proj r K (φ x))
    rw [mul_conj_mul_inv, hφ]
  have hmain := ClassicalInvolution.Balance.isComponentOf_map_centralizer hker 1 i φ hδ hQ
  have e : (conjProj r K).comp (MulAut.conj (1 : StatedSp r K)).toMonoidHom = conjProj r K := by
    ext
    simp
  rw [e] at hmain
  have : (conjProj r K).range.Normal := conjProj_range_normal
  have hRconj : ∀ s ∈ (conjProj r K).range ⊓ centralizer ({i} : Set _), Odd (orderOf s) →
      ∀ y ∈ R, s * y * s⁻¹ ∈ R := by
    rintro _ ⟨⟨x, rfl⟩, hxi⟩ hodd y hy
    have hxi' := mem_centralizer_singleton_iff.1 hxi
    have hfix : i (proj r K x) = proj r K x := by
      apply hinj
      rw [← mul_conj_mul_inv]
      change i * conjProj r K x * i⁻¹ = conjProj r K x
      rw [← hxi', mul_inv_cancel_right]
    have hodd' : Odd (orderOf (proj r K x)) := by
      rwa [← orderOf_injective _ hinj (proj r K x)]
    exact hRc _ hfix hodd' y hy
  have h := commute_of_isComponentOf hRodd hRi hRconj hmain hy ⟨g, hg, rfl⟩
  apply hinj
  rw [← mul_conj_mul_inv]
  change y * conjProj r K g * y⁻¹ = conjProj r K g
  rw [h, mul_inv_cancel_right]

theorem fix_of_normal (φ : StatedSp r K ≃* StatedSp r K)
    (hφ : ∀ g, i (proj r K g) = proj r K (φ g)) {Q : Subgroup (StatedSp r K)}
    (hQF : Q ≤ ClassicalInvolution.Balance.fixedGroup φ)
    (hQn : ∀ f ∈ ClassicalInvolution.Balance.fixedGroup φ, ∀ q ∈ Q, f * q * f⁻¹ ∈ Q)
    (hQq : IsQuasisimple Q) {y} (hy : y ∈ R) {g : StatedSp r K} (hg : g ∈ Q) :
    y (proj r K g) = proj r K g := by
  refine fix_of_component hinj hRodd hRi hRc φ hφ ⟨hQF, ?_, ?_⟩ hy hg
  · refine ClassicalInvolution.isSubnormal_of_normal_subgroupOf hQF ?_
    rw [Subgroup.normal_subgroupOf_iff hQF]
    exact fun q f hq hf => hQn f hf q hq
  · exact ⟨hQq.1.commutator_eq_top, hQq.2.1⟩

theorem fix_of_spCent {A : gsp r K} (hiA : i = conjAut r K A) {Q : Subgroup (StatedSp r K)}
    (hQF : Q ≤ spCent r K A) (hQn : ∀ f ∈ spCent r K A, ∀ q ∈ Q, f * q * f⁻¹ ∈ Q)
    (hQq : IsQuasisimple Q) {y} (hy : y ∈ R) {g : StatedSp r K} (hg : g ∈ Q) :
    y (proj r K g) = proj r K g :=
  fix_of_normal hinj hRodd hRi hRc (conjSp r K A) (fun g => by rw [hiA]; rfl) hQF hQn hQq hy hg

end Fix

theorem commutator_mem
    (hRc : ∀ s, i s = s → Odd (orderOf s) → ∀ y ∈ R,
      MulAut.conj s * y * (MulAut.conj s)⁻¹ ∈ R)
    {x : StatedProj (StatedSp r K)}
    (hx : x ∈ closure {s | i s = s ∧ Odd (orderOf s)}) {y} (hy : y ∈ R) :
    y * MulAut.conj x * y⁻¹ * (MulAut.conj x)⁻¹ ∈ R := by
  have hN : x ∈ (normalizer (R : Set (MulAut (StatedProj (StatedSp r K))))).comap
      (MulAut.conj : StatedProj (StatedSp r K) →* MulAut (StatedProj (StatedSp r K))) := by
    refine (closure_le _).2 (fun s hs => ?_) hx
    rw [SetLike.mem_coe, mem_comap, mem_normalizer_iff]
    intro z
    refine ⟨fun hz => hRc s hs.1 hs.2 z hz, fun hz => ?_⟩
    have h := hRc s⁻¹ (by rw [map_inv, hs.1]) (by rw [orderOf_inv]; exact hs.2) _ hz
    rwa [map_inv, inv_inv, ← mul_assoc, ← mul_assoc, inv_mul_cancel, one_mul,
      mul_assoc, inv_mul_cancel, mul_one] at h
  have h1 : MulAut.conj x * y⁻¹ * (MulAut.conj x)⁻¹ ∈ R :=
    (mem_normalizer_iff.1 (mem_comap.1 hN) y⁻¹).1 (inv_mem hy)
  rw [mul_assoc, mul_assoc, ← mul_assoc (MulAut.conj x)]
  exact mul_mem hy h1

end CFSG.ComponentClassification.Foote5.OddLieCore.ClSp
