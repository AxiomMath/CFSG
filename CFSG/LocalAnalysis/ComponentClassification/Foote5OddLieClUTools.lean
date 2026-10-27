module

public import CFSG.ClassicalInvolution.Balance.LayerGenerationTransport
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneUBlock
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneUModel
public import CFSG.LocalAnalysis.ComponentClassification.Foote5OddLieCoreX

public section

namespace CFSG.ComponentClassification.Foote5.OddLieCore

open Matrix CFSG Subgroup CFSG.Assembly.LowTwoRank
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ComponentClassification.Burgoyne.Proj CFSG.ComponentClassification.Burgoyne.U
open CFSG.ComponentClassification.Burgoyne.PSL (mul_conj_mul_inv conj_range_normal)

@[expose] def ClU.UBlockThreeGen : Prop :=
  ∀ {p f : ℕ} {K : Type} [Field K] (_ : UnitaryFieldData p f K), p ^ f = 3 → ∀ {n : ℕ}
    (x z : Fin n), x ≠ z →
    uBlock p f K {x, z} ≤ closure {g | g ∈ uBlock p f K {x, z} ∧ Odd (orderOf g)}

theorem ClU.commutator_mem {P : Type*} [Group P] {i : MulAut P} {R : Subgroup (MulAut P)}
    (hRc : ∀ s, i s = s → Odd (orderOf s) → ∀ y ∈ R,
      MulAut.conj s * y * (MulAut.conj s)⁻¹ ∈ R)
    {x : P} (hx : x ∈ closure {s | i s = s ∧ Odd (orderOf s)}) {y} (hy : y ∈ R) :
    y * MulAut.conj x * y⁻¹ * (MulAut.conj x)⁻¹ ∈ R := by
  have hN : x ∈ (normalizer (R : Set (MulAut P))).comap (MulAut.conj : P →* MulAut P) := by
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

variable {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K] [Finite K]
  {H : Subgroup (GL ι K)}

theorem ClU.fix_of_lift
    (hinj : Function.Injective (MulAut.conj : StatedProj H →* MulAut (StatedProj H)))
    {i : MulAut (StatedProj H)} {R : Subgroup (MulAut (StatedProj H))}
    (hRodd : Odd (Nat.card R)) (hRi : ∀ y ∈ R, y * i = i * y)
    (hRc : ∀ s, i s = s → Odd (orderOf s) → ∀ y ∈ R,
      MulAut.conj s * y * (MulAut.conj s)⁻¹ ∈ R)
    (φ : H →* H) (hφi : Function.Injective φ) (hφ : ∀ g, i (projH H g) = projH H (φ g))
    {Q : Subgroup H} (hQF : Q ≤ MonoidHom.eqLocus φ (MonoidHom.id H))
    (hQn : ∀ x ∈ MonoidHom.eqLocus φ (MonoidHom.id H), ∀ q ∈ Q, x * q * x⁻¹ ∈ Q)
    (hQq : IsQuasisimple Q) {y} (hy : y ∈ R) {g : H} (hg : g ∈ Q) :
    y (projH H g) = projH H g := by
  set δ : H ≃* H := MulEquiv.ofBijective φ ⟨hφi, Finite.injective_iff_surjective.1 hφi⟩
  have hQF' : Q ≤ ClassicalInvolution.Balance.fixedGroup δ := fun q hq => hQF hq
  have hQ : Open.IsComponentOf Q (ClassicalInvolution.Balance.fixedGroup δ) := by
    refine ⟨hQF', ?_, ⟨hQq.1.commutator_eq_top, hQq.2.1⟩⟩
    refine ClassicalInvolution.isSubnormal_of_normal_subgroupOf hQF' ?_
    rw [Subgroup.normal_subgroupOf_iff hQF']
    exact fun q x hq hx => hQn x hx q hq
  have hker : (conjProjH H).ker ≤ center H := by
    intro x hx
    have h1 : projH H x = 1 := hinj (by rw [map_one]; exact hx)
    exact scalars_subgroupOf_le_center ((QuotientGroup.eq_one_iff _).1 h1)
  have hδ : ∀ x : H, i * conjProjH H (1 * x * 1⁻¹) * i⁻¹ = conjProjH H (1 * δ x * 1⁻¹) :=
    fun x => by
      simp only [one_mul, inv_one, mul_one]
      change i * MulAut.conj (projH H x) * i⁻¹ = MulAut.conj (projH H (φ x))
      rw [mul_conj_mul_inv, hφ]
  have hmain := ClassicalInvolution.Balance.isComponentOf_map_centralizer hker 1 i δ hδ hQ
  have e : (conjProjH H).comp (MulAut.conj (1 : H)).toMonoidHom = conjProjH H := by
    ext
    simp
  rw [e] at hmain
  have : (conjProjH H).range.Normal := by
    have h : (conjProjH H).range = (MulAut.conj : StatedProj H →* MulAut (StatedProj H)).range := by
      rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr projH_surjective,
        ← MonoidHom.range_eq_map]
    rw [h]
    exact conj_range_normal
  have hRconj : ∀ s ∈ (conjProjH H).range ⊓ centralizer ({i} : Set _), Odd (orderOf s) →
      ∀ y ∈ R, s * y * s⁻¹ ∈ R := by
    rintro _ ⟨⟨x, rfl⟩, hxi⟩ hodd y hy
    have hxi' := mem_centralizer_singleton_iff.1 hxi
    have hfix : i (projH H x) = projH H x := by
      apply hinj
      rw [← mul_conj_mul_inv]
      change i * conjProjH H x * i⁻¹ = conjProjH H x
      rw [← hxi', mul_inv_cancel_right]
    have hodd' : Odd (orderOf (projH H x)) := by
      rwa [← orderOf_injective _ hinj (projH H x)]
    exact hRc _ hfix hodd' y hy
  have h := commute_of_isComponentOf hRodd hRi hRconj hmain hy ⟨g, hg, rfl⟩
  apply hinj
  rw [← mul_conj_mul_inv]
  change y * conjProjH H g * y⁻¹ = conjProjH H g
  rw [h, mul_inv_cancel_right]

end CFSG.ComponentClassification.Foote5.OddLieCore
