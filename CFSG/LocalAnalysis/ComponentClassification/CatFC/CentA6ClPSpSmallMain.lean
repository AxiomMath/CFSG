module

public import CFSG.LocalAnalysis.ComponentClassification.CatFC.CentA6ClPSpSmallClass
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.CentA6ClPSpSmallSwap
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.CentA6ClPSpField

public section

namespace CFSG.ComponentClassification.CatFC.PSpSmall

open Subgroup CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.CatLeaf CFSG.ComponentClassification.CatLeafProof
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.ComponentClassification.Burgoyne.Sp (spCent)
open scoped Matrix

theorem two_mul_card_le_of_notMem {G : Type} [Group G] [Finite G] (R : Subgroup G) {x : G}
    (hx : x ∉ R) : 2 * Nat.card R ≤ Nat.card G := by
  have hR : R ≠ ⊤ := fun h => hx (h ▸ Subgroup.mem_top x)
  have hi : 2 ≤ R.index := by
    have h1 : R.index ≠ 1 := fun h => hR (Subgroup.index_eq_one.1 h)
    have h0 : R.index ≠ 0 := Subgroup.index_ne_zero_of_finite
    omega
  calc 2 * Nat.card R ≤ R.index * Nat.card R := Nat.mul_le_mul_right _ hi
    _ = Nat.card G := by rw [mul_comm]; exact Subgroup.card_mul_index R

section Swap

variable {K : Type} [Field K] [Finite K]

theorem conjAut_swap_fix {A : gsp 2 K} {g : StatedSp 2 K}
    (hgA : ((g : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *
        ((A : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) =
      -(((A : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *
        ((g : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K))) :
    conjAut 2 K A (proj 2 K g) = proj 2 K g := by
  rw [conjAut_proj]
  have hz : conjSp 2 K A g * g⁻¹ ∈ spScalars 2 K := by
    rw [Subgroup.mem_subgroupOf, StatedScalars, MonoidHom.mem_range]
    refine ⟨-1, Units.ext ?_⟩
    have h1 : ((A : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *
        (((A : GL (Fin 2 ⊕ Fin 2) K)⁻¹ : GL (Fin 2 ⊕ Fin 2) K) :
          Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    have h2 : ((g : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *
        (((g : GL (Fin 2 ⊕ Fin 2) K)⁻¹ : GL (Fin 2 ⊕ Fin 2) K) :
          Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    have h3 : ((A : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *
        ((g : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) =
        -(((g : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *
          ((A : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)) := by
      rw [hgA, neg_neg]
    have h4 : ((g : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *
        ((A : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *
        (((A : GL (Fin 2 ⊕ Fin 2) K)⁻¹ : GL (Fin 2 ⊕ Fin 2) K) :
          Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) =
        ((g : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) := by
      rw [Matrix.mul_assoc, h1, Matrix.mul_one]
    rw [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal]
    change (-1 : Kˣ).val • (1 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) =
      ((A : GL (Fin 2 ⊕ Fin 2) K) * (g : GL (Fin 2 ⊕ Fin 2) K) *
        (A : GL (Fin 2 ⊕ Fin 2) K)⁻¹ * (g : GL (Fin 2 ⊕ Fin 2) K)⁻¹ :
          GL (Fin 2 ⊕ Fin 2) K).val
    rw [Units.val_mul, Units.val_mul, Units.val_mul, h3, Matrix.neg_mul, Matrix.neg_mul, h4, h2]
    simp
  have hker : proj 2 K (conjSp 2 K A g * g⁻¹) = 1 := by
    rw [← MonoidHom.mem_ker, ker_proj]
    exact hz
  rw [map_mul, map_inv, mul_inv_eq_one] at hker
  exact hker

theorem conjAut_swap_notMem {A : gsp 2 K} {g : StatedSp 2 K} (h2 : (2 : K) ≠ 0)
    (hgA : ((g : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *
        ((A : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) =
      -(((A : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *
        ((g : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)))
    (hx : conjAut 2 K A (proj 2 K g) = proj 2 K g) :
    (⟨proj 2 K g, hx⟩ : ↥(fixedSubgroup (conjAut 2 K A))) ∉ (spCentFix A).range := by
  rintro ⟨s, hs⟩
  have h1 : proj 2 K (s : StatedSp 2 K) = proj 2 K g := congrArg Subtype.val hs
  have h3 : g⁻¹ * (s : StatedSp 2 K) ∈ (proj 2 K).ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, h1, inv_mul_cancel]
  rw [ker_proj, Subgroup.mem_subgroupOf, StatedScalars, MonoidHom.mem_range] at h3
  obtain ⟨c, hc⟩ := h3
  have hs' : ((s : StatedSp 2 K) : GL (Fin 2 ⊕ Fin 2) K) =
      (g : GL (Fin 2 ⊕ Fin 2) K) * Matrix.GeneralLinearGroup.scalar (Fin 2 ⊕ Fin 2) c := by
    rw [hc]
    simp
  have hsm : (((s : StatedSp 2 K) : GL (Fin 2 ⊕ Fin 2) K) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) =
      (c : K) • ((g : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) := by
    rw [hs', Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
      ← Matrix.smul_one_eq_diagonal, Matrix.mul_smul, Matrix.mul_one]
  have hcomm := Burgoyne.Sp.mem_spCent.1 s.2
  rw [hsm, Matrix.mul_smul, Matrix.smul_mul] at hcomm
  have hMg : ((A : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *
      ((g : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) =
      -(((g : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *
        ((A : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)) := by
    rw [hgA, neg_neg]
  rw [hMg] at hcomm
  have hN0 : ((g : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *
      ((A : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) ≠ 0 := by
    have := Units.ne_zero ((g : GL (Fin 2 ⊕ Fin 2) K) * (A : GL (Fin 2 ⊕ Fin 2) K))
    simpa using this
  have hc0 : (c : K) ≠ 0 := c.ne_zero
  have h2c : ((2 : K) * c) • (((g : GL (Fin 2 ⊕ Fin 2) K) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *
      ((A : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)) = 0 := by
    calc ((2 : K) * c) • (((g : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *
        ((A : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)) =
        (c : K) • (((g : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *
          ((A : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)) -
        (c : K) • (-(((g : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *
          ((A : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K))) := by
          rw [smul_neg, sub_neg_eq_add, ← add_smul]
          congr 1
          ring
      _ = 0 := by rw [hcomm, sub_self]
  exact hN0 ((smul_eq_zero.1 h2c).resolve_left (mul_ne_zero h2 hc0))

end Swap

section Main

variable {K : Type} [Field K] [Finite K]

theorem a6SmallConcl_conjAut {f : ℕ} (hf : f = 1 ∨ f = 2) (hK : Nat.card K = 3 ^ f)
    (A : gsp 2 K) (hA : orderOf (conjAut 2 K A) = 2)
    {D : Subgroup ↥(fixedSubgroup (conjAut 2 K A))} (h : A6Hyp (conjAut 2 K A) D) :
    A6SmallConcl .PSp 2 f (conjAut 2 K A) D := by
  have hf1 : 1 ≤ f := by omega
  have : CharP K 3 := finite_field_prime_power_characteristic Nat.prime_three hf1 hK
  have hchar : ringChar K ≠ 2 := by
    rw [ringChar.eq K 3]
    norm_num
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hchar
  obtain ⟨c, μ, hc0, hAA, hμ, hcl⟩ := inner_classes_sp hf1 hK A hA
  have hle := card_spCent_le_two_mul A
  rcases hf with rfl | rfl
  ·
    rcases hcl with ⟨_, _, h3, _⟩ | ⟨_, _, h3, _⟩ | ⟨hns, hμc, h3, _⟩ | ⟨_, _, h3, _⟩
    · exact absurd (isSolvable_fixed_of_spCent A (h3 rfl)) h.not_solvable
    · exact absurd (isSolvable_fixed_of_spCent A (h3 rfl)) h.not_solvable
    · obtain ⟨hP360, h720⟩ := h3 rfl
      have hnotinner : conjAut 2 K A ∉ (MulAut.conj : StatedProj (StatedSp 2 K) →*
          MulAut (StatedProj (StatedSp 2 K))).range := by
        intro hin
        obtain ⟨l, hl⟩ := exists_sq_of_conjAut_inner hμ hin
        exact hns l (by rw [hl, hμc])
      refine ⟨fun hin => absurd hin hnotinner, fun _ hC720 => ?_⟩
      obtain ⟨g, hgg, hgA⟩ := exists_swap_of_selfAdjoint h2 A hns hAA (by rw [← hμc]; exact hμ)
      have hx := conjAut_swap_fix hgA
      have hxR := conjAut_swap_notMem h2 hgA hx
      obtain ⟨H, hH⟩ := h.exists_map_eq_of_perfect360 (by norm_num) hP360
      have hDR : D ≤ (spCentFix A).range := by
        rw [← hH]
        exact Subgroup.map_le_range _ _
      have hxD : (⟨proj 2 K g, hx⟩ : ↥(fixedSubgroup (conjAut 2 K A))) ∉ D :=
        fun hxD => hxR (hDR hxD)
      have hx1 : (⟨proj 2 K g, hx⟩ : ↥(fixedSubgroup (conjAut 2 K A))) ≠ 1 := fun hx1 =>
        hxR (hx1 ▸ (spCentFix A).range.one_mem)
      have hx2 : (⟨proj 2 K g, hx⟩ : ↥(fixedSubgroup (conjAut 2 K A))) ^ 2 = 1 := by
        apply Subtype.ext
        change (proj 2 K g) ^ 2 = 1
        rw [sq, ← map_mul, hgg, map_one]
      have hord := orderOf_eq_prime hx2 hx1
      have hR2 := two_mul_card_le_of_notMem (spCentFix A).range hxR
      have hcard := card_spCent_le_two_mul_range A
      refine ⟨by omega, Or.inl ⟨_, hord, hxD⟩⟩
    · exact absurd (isSolvable_fixed_of_spCent A (h3 rfl)) h.not_solvable
  ·
    have hK9 : Nat.card K = 9 := by simpa using hK
    haveI := Fintype.ofFinite K
    have hneg1 : IsSquare (-1 : K) :=
      FiniteField.isSquare_neg_one_iff.2 (by rw [← Nat.card_eq_fintype_card, hK9]; norm_num)
    obtain ⟨i, hi⟩ := hneg1
    rcases hcl with ⟨_, _, _, h4⟩ | ⟨hsq, hμc, _, h4⟩ | ⟨_, _, _, h4⟩ | ⟨hns, hμc, _, h4⟩
    ·
      have := h4 rfl
      exact ⟨fun _ => by omega, fun _ hC720 => absurd hC720 (by omega)⟩
    ·
      obtain ⟨l₀, hl₀⟩ := hsq
      have hl00 : l₀ ≠ 0 := fun h0 => hc0 (by rw [← hl₀, h0]; ring)
      have hi0 : i ≠ 0 := fun h0 => by
        have : (-1 : K) = 0 := by rw [hi, h0, mul_zero]
        exact one_ne_zero (neg_eq_zero.1 this)
      have hinner : conjAut 2 K A ∈ (MulAut.conj : StatedProj (StatedSp 2 K) →*
          MulAut (StatedProj (StatedSp 2 K))).range :=
        conjAut_inner_of_sq hμ (l := i * l₀) (by
          rw [hμc, mul_pow, ← hl₀, sq i, ← hi]
          ring) (mul_ne_zero hi0 hl00)
      have hbig := h4 rfl
      refine ⟨fun _ => by omega, fun hout => absurd hinner hout⟩
    ·
      have := h4 rfl
      exact ⟨fun _ => by omega, fun _ hC720 => absurd hC720 (by omega)⟩
    ·
      have hbig := h4 rfl
      refine ⟨fun hin => ?_, fun _ hC720 => ?_⟩
      · obtain ⟨l, hl⟩ := exists_sq_of_conjAut_inner hμ hin
        refine absurd ?_ (hns (i * l))
        rw [mul_pow, sq i, ← hi, hl, hμc]
        ring
      · omega

end Main

theorem a6SmallConcl_psp {f : ℕ} (hf : f = 1 ∨ f = 2) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 3 ^ f) {σ : MulAut (StatedProj (StatedSp 2 K))} (hσ : orderOf σ = 2)
    {D : Subgroup ↥(fixedSubgroup σ)} (h : A6Hyp σ D) : A6SmallConcl .PSp 2 f σ D := by
  have hf1 : 1 ≤ f := by omega
  have : CharP K 3 := finite_field_prime_power_characteristic Nat.prime_three hf1 hK
  have hchar : ringChar K ≠ 2 := by
    rw [ringChar.eq K 3]
    norm_num
  have hσ2 : σ * σ = 1 := by
    have h2 := pow_orderOf_eq_one σ
    rw [hσ] at h2
    rw [← pow_two]
    exact h2
  have hσ1 : σ ≠ 1 := fun h1 => by
    rw [h1, orderOf_one] at hσ
    exact absurd hσ (by norm_num)
  obtain ⟨A, τ, hAσ, hτ2, ⟨d, hd⟩, -, -⟩ :=
    (CatalogueBSymplecticRepresentation.odd_symplectic_automorphism_semilinear_representation
      hchar (le_refl 2)).2.2 σ hσ2 hσ1
  by_cases hτ : τ = 1
  · subst hτ
    rw [map_one, mul_one] at hAσ
    subst hAσ
    exact a6SmallConcl_conjAut hf hK A hσ h
  · exact (a6_field_false (le_refl 2) hf1 hK A τ hAσ hτ2 hτ d hd h).elim

end CFSG.ComponentClassification.CatFC.PSpSmall

namespace CFSG.ComponentClassification.CatFC

open Subgroup CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.CatLeaf CFSG.ComponentClassification.CatLeafProof

theorem oddA6Small_PSp (_hO : LieOrderFormulasInput) : OddA6Small .PSp := by
  apply oddA6Small_of_concrete
  intro S _ _ n p f hp hp2 hadm hm hp3 hshape
  subst hp3
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := nonempty_mulEquiv_psp_of_lieModel' hadm hm
  have hshape' : n = 2 ∧ (f = 1 ∨ f = 2) := by
    unfold A6Shape at hshape
    rcases hshape with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨-, hn, hf⟩ | ⟨-, hn, hf⟩ |
      ⟨h, -⟩ | ⟨h, -⟩
    · cases h
    · cases h
    · cases h
    · cases h
    · cases h
    · exact ⟨hn, Or.inl hf⟩
    · exact ⟨hn, Or.inr hf⟩
    · cases h
    · cases h
  obtain ⟨rfl, hf⟩ := hshape'
  refine ⟨StatedProj (StatedSp 2 K), inferInstance, inferInstance, e, ?_⟩
  intro σ D hσ hD
  exact PSpSmall.a6SmallConcl_psp hf hK hσ hD

end CFSG.ComponentClassification.CatFC
