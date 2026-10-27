module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2Leaves.A2lRowBlock
public import CFSG.ClassicalInvolution.Models.SymplecticPairs.Embed

public section

namespace CFSG.OddStandard.SmallF3.HypA2Leaves

open Subgroup CFSG.ComponentClassification CFSG.Assembly.LowTwoRank Matrix
open CFSG.ClassicalInvolution.Models.SymplecticPairs
  (IsSupp suppGroup ParClosed fixSpace longRootGroup fixing_supported_eq mem_fixSpace mem_suppGroup
    conj_mem_longRootGroup mulVec_diagonal_eq spEmbed mat_spEmbed spEmbedMat_apply_image
    spEmbedMat_apply_of_not_mem)
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_apply mat_injective)
open CFSG.OddStandard.SmallF3.HypA2 (TypU)

variable {F : Type} [Field F] {n : ℕ} {S : Set (Fin n ⊕ Fin n)}

section Diagonal

variable [DecidablePred (· ∈ S)]

theorem a2l_fixSpace_eq (h2 : (2 : F) ≠ 0) {t : StatedSp n F}
    (ht : mat n F t = diagonal fun a => if a ∈ S then (-1 : F) else 1) :
    (fixSpace t : Set (Fin n ⊕ Fin n → F)) = {v | ∀ s ∈ S, v s = 0} := by
  ext v
  rw [SetLike.mem_coe, mem_fixSpace, ht, mulVec_diagonal_eq, Set.mem_setOf_eq]
  constructor
  · intro h s hs
    have := congrFun h s
    simp only [hs, ite_true] at this
    have h' : (2 : F) * v s = 0 := by linear_combination -this
    exact (mul_eq_zero.1 h').resolve_left h2
  · intro h
    funext s
    by_cases hs : s ∈ S
    · simp [hs, h s hs]
    · simp [hs]

theorem a2l_longRootGroup_eq (h2 : (2 : F) ≠ 0) (hS : ParClosed S) {t : StatedSp n F}
    (ht : mat n F t = diagonal fun a => if a ∈ S then (-1 : F) else 1) :
    longRootGroup t = suppGroup S := by
  rw [← fixing_supported_eq hS, longRootGroup, a2l_fixSpace_eq h2 ht]

theorem a2l_mem_suppGroup_of_diag {t : StatedSp n F}
    (ht : mat n F t = diagonal fun a => if a ∈ S then (-1 : F) else 1) : t ∈ suppGroup S := by
  rw [mem_suppGroup]
  intro r s hrs
  rw [ht, diagonal_apply, Matrix.one_apply]
  by_cases h : r = s
  · subst h
    have : r ∉ S := fun hr => hrs ⟨hr, hr⟩
    simp [this]
  · simp [h]

theorem a2l_mul_self_of_diag {t : StatedSp n F}
    (ht : mat n F t = diagonal fun a => if a ∈ S then (-1 : F) else 1) : t * t = 1 := by
  apply mat_injective
  rw [map_mul, map_one, ht, diagonal_mul_diagonal, ← diagonal_one]
  congr 1
  funext a
  by_cases ha : a ∈ S <;> simp [ha]

theorem a2l_ne_one_of_diag (h2 : (2 : F) ≠ 0) {s₀ : Fin n ⊕ Fin n} (hs₀ : s₀ ∈ S)
    {t : StatedSp n F} (ht : mat n F t = diagonal fun a => if a ∈ S then (-1 : F) else 1) :
    t ≠ 1 := by
  intro h1
  have h := congrFun (congrFun (congrArg (mat n F) h1) s₀) s₀
  rw [ht, map_one, diagonal_apply_eq, Matrix.one_apply_eq] at h
  simp only [hs₀, ite_true] at h
  exact h2 (by linear_combination -h)

theorem a2l_commute_of_diag {x t : StatedSp n F} (hx : x ∈ suppGroup S)
    (ht : mat n F t = diagonal fun a => if a ∈ S then (-1 : F) else 1) : x * t = t * x := by
  apply mat_injective
  rw [map_mul, map_mul, ht]
  ext r s
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  by_cases hrs : r ∈ S ∧ s ∈ S
  · obtain ⟨hr, hs⟩ := hrs
    simp only [hr, hs, ite_true]
    ring
  · have hx' : mat n F x r s = (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) r s := hx r s hrs
    rw [hx']
    by_cases h : r = s
    · subst h
      ring
    · rw [Matrix.one_apply_ne h]
      ring

end Diagonal

theorem a2l_eq_one_of_scalar {a : Fin n ⊕ Fin n} (ha : a ∉ S) {x : StatedSp n F}
    (hx : x ∈ suppGroup S)
    (h : QuotientGroup.mk' ((StatedScalars (Fin n ⊕ Fin n) F).subgroupOf (StatedSp n F)) x = 1) :
    x = 1 := by
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf, StatedScalars,
    MonoidHom.mem_range] at h
  obtain ⟨c, hc⟩ := h
  have h1 : mat n F x a a = 1 := by
    have := (mem_suppGroup.1 hx) a a (fun h' => ha h'.1)
    simpa using this
  have h2 : mat n F x a a = (c : F) := by
    rw [mat_apply, ← hc]
    simp [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply]
  have hc1 : c = 1 := Units.ext (h2.symm.trans h1)
  apply Subtype.ext
  rw [← hc, hc1, map_one]
  rfl

theorem a2lDatum_psp_block [Finite F] (h2 : (2 : F) ≠ 0) (hS : ParClosed S)
    {a : Fin n ⊕ Fin n} (ha : a ∉ S) {s₀ : Fin n ⊕ Fin n} (hs₀ : s₀ ∈ S) [DecidablePred (· ∈ S)]
    {t : StatedSp n F} (ht : mat n F t = diagonal fun a => if a ∈ S then (-1 : F) else 1)
    {q₀ : ℕ} (hodd : Odd q₀) (h5 : 5 ≤ q₀) {J N : Subgroup (StatedSp n F)}
    (hJS : J = suppGroup S) (hNJ : N ≤ J) (htN : t ∈ N) (hJq : CFSG.IsQuasisimple ↥J)
    (hN : HarrisLit.IsSLTwoOver q₀ ↥N) (hTU : TypU ↥J) :
    a2lDatum (StatedProj (StatedSp n F)) := by
  have hinj : ∀ x ∈ J, QuotientGroup.mk'
      ((StatedScalars (Fin n ⊕ Fin n) F).subgroupOf (StatedSp n F)) x = 1 → x = 1 :=
    fun x hx h => a2l_eq_one_of_scalar ha (hJS ▸ hx) h
  refine a2lDatum_of_block_normal (QuotientGroup.mk' _) (QuotientGroup.mk'_surjective _)
    (by rw [QuotientGroup.ker_mk']; exact Open.StatedAPI.statedScalars_subgroupOf_le_center _)
    hodd h5 (a2l_mul_self_of_diag ht) ?_ hNJ htN ?_ ?_ hJq hinj hN hTU
  · exact fun h => a2l_ne_one_of_diag h2 hs₀ ht
      (a2l_eq_one_of_scalar ha (a2l_mem_suppGroup_of_diag ht) h)
  · intro x hx
    rw [mem_centralizer_singleton_iff]
    exact a2l_commute_of_diag (hJS ▸ hx) ht
  · intro g hg x hx
    rw [hJS, ← a2l_longRootGroup_eq h2 hS ht] at hx ⊢
    exact conj_mem_longRootGroup (mem_centralizer_singleton_iff.1 hg) hx

theorem a2l_mat_spEmbed_neg {m : ℕ} {σ : Fin m → Fin n} (hσ : Function.Injective σ)
    [DecidablePred (· ∈ Set.range (Sum.map σ σ))] {g : StatedSp m F} (hg : mat m F g = -1) :
    mat n F (spEmbed σ hσ g) =
      diagonal fun a => if a ∈ Set.range (Sum.map σ σ) then (-1 : F) else 1 := by
  have hinj : Function.Injective (Sum.map σ σ : Fin m ⊕ Fin m → Fin n ⊕ Fin n) :=
    Sum.map_injective.2 ⟨hσ, hσ⟩
  ext a b
  rw [mat_spEmbed, diagonal_apply]
  by_cases h : a ∈ Set.range (Sum.map σ σ) ∧ b ∈ Set.range (Sum.map σ σ)
  · obtain ⟨⟨x, rfl⟩, ⟨y, rfl⟩⟩ := h
    rw [spEmbedMat_apply_image hσ, hg]
    by_cases hxy : x = y
    · subst hxy
      simp
    · have : Sum.map σ σ x ≠ Sum.map σ σ y := fun h => hxy (hinj h)
      simp [this, hxy, Matrix.one_apply_ne hxy]
  · rw [spEmbedMat_apply_of_not_mem _ h, Matrix.one_apply]
    by_cases hab : a = b
    · subst hab
      have : a ∉ Set.range (Sum.map σ σ) := fun hr => h ⟨hr, hr⟩
      simp [this]
    · simp [hab]

end CFSG.OddStandard.SmallF3.HypA2Leaves
