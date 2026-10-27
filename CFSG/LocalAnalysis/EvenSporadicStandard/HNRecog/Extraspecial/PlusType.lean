module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Extraspecial.Quotient

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.EvenSporadicStandard.HNRecog

open Subgroup Module QuadraticMap CFSG.RankThree.Literature.FSmith CFSG.GroupTheory.WeirSylow

variable {H : Type} [Group H] {Q : Subgroup H} [Module (ZMod 2) (Additive (Abelianization Q))]

private def piAddHom (Q : Subgroup H) : Additive Q →+ Additive (Abelianization Q) :=
  MonoidHom.toAdditive (Abelianization.of : Q →* Abelianization Q)

private theorem piAddHom_apply (Q : Subgroup H) (x : Q) :
    piAddHom Q (Additive.ofMul x) = Additive.ofMul (Abelianization.of x) := rfl

private theorem natCard_toAddSubgroup (S : Subgroup H) :
    Nat.card (S.toAddSubgroup) = Nat.card S :=
  Nat.card_congr
    { toFun := fun x => ⟨Additive.toMul x.1, (Additive.mem_toAddSubgroup S x.1).1 x.2⟩
      invFun := fun x => ⟨Additive.ofMul x.1,
        (Additive.mem_toAddSubgroup S (Additive.ofMul x.1)).2 (by simpa using x.2)⟩
      left_inv := by intro x; ext; simp
      right_inv := by intro x; ext; simp }

private theorem eq_zero_of_mem_elemAbelian [Finite Q] (hE : IsExtraspecialPGroup 2 Q)
    {E : Subgroup H} (hEelem : CFSG.Open.IsElemAbelian 2 E) {q : Q} (hq : (q : H) ∈ E) :
    extraspecialQuadForm hE (Additive.ofMul (Abelianization.of q)) = 0 := by
  have hq2 : q ^ 2 = 1 := Subtype.ext (by simpa using hEelem.2 (q : H) hq)
  rw [extraspecialQuadForm_apply, if_pos hq2]

theorem IsPlusExtraspecial.isPlusType_extraspecialQuadForm {m : ℕ} (h : IsPlusExtraspecial m Q) :
    letI := h.finite
    IsPlusType (extraspecialQuadForm h.isExtraspecialPGroup) := by
  letI := h.finite
  have hE : IsExtraspecialPGroup 2 Q := h.isExtraspecialPGroup
  obtain ⟨E, hEQ, hEelem, hEcard⟩ := h.2.2
  let E' : Subgroup Q := E.comap Q.subtype
  let S : AddSubgroup (Additive Q) := Subgroup.toAddSubgroup E'
  let φ : S →+ Additive (Abelianization Q) := (piAddHom Q).comp S.subtype
  let Etilde : AddSubgroup (Additive (Abelianization Q)) := φ.range
  let W : Submodule (ZMod 2) (Additive (Abelianization Q)) :=
    AddSubgroup.toZModSubmodule (n := 2) Etilde
  have hE'card : Nat.card E' = Nat.card E := by
    have hmap : E'.map Q.subtype = E := by
      rw [show E' = E.comap Q.subtype from rfl]
      exact Subgroup.map_comap_eq_self (by simpa [Subgroup.range_subtype] using hEQ)
    have h1 := Subgroup.card_map_of_injective (K := E') Q.subtype_injective
    rw [hmap] at h1
    exact h1.symm
  have hS : Nat.card S = 2 ^ (m + 1) := by
    rw [show S = Subgroup.toAddSubgroup E' from rfl, natCard_toAddSubgroup, hE'card, hEcard]
  have hW_sing : ∀ x ∈ W, extraspecialQuadForm hE x = 0 := by
    intro x hx
    rw [AddSubgroup.mem_toZModSubmodule] at hx
    change x ∈ φ.range at hx
    obtain ⟨y, rfl⟩ := hx
    change extraspecialQuadForm hE (φ y) = 0
    set q0 : Q := Additive.toMul y.1 with hq0def
    have hq0 : (q0 : H) ∈ E := by
      have h' : Additive.toMul y.1 ∈ E.comap Q.subtype :=
        (Additive.mem_toAddSubgroup E' y.1).1 y.2
      simpa [hq0def] using Subgroup.mem_comap.mp h'
    have hφ : φ y = Additive.ofMul (Abelianization.of q0) := by
      change piAddHom Q (y.1) = _
      rw [show y.1 = Additive.ofMul q0 from (ofMul_toMul y.1).symm]
      exact piAddHom_apply Q q0
    rw [hφ]
    exact eq_zero_of_mem_elemAbelian (Q := Q) (E := E) hE hEelem (q := q0) hq0
  have hW_le_orth : W ≤
      LinearMap.BilinForm.orthogonal (extraspecialQuadForm hE).polarBilin W := by
    intro x hx
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro y hy
    rw [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar]
    rw [hW_sing (y + x) (W.add_mem hy hx), hW_sing y hy, hW_sing x hx]
    ring
  haveI : Module.Finite (ZMod 2) (Additive (Abelianization Q)) := Module.Finite.of_finite
  have hVfin : finrank (ZMod 2) (Additive (Abelianization Q)) = 2 * m := h.finrank_quotient
  have hfin_orth : finrank (ZMod 2)
        (LinearMap.BilinForm.orthogonal (extraspecialQuadForm hE).polarBilin W) =
      finrank (ZMod 2) (Additive (Abelianization Q)) - finrank (ZMod 2) W :=
    LinearMap.BilinForm.finrank_orthogonal (extraspecialQuadForm_nondegenerate hE) W
  have hle_orth : finrank (ZMod 2) W ≤
      finrank (ZMod 2)
        (LinearMap.BilinForm.orthogonal (extraspecialQuadForm hE).polarBilin W) :=
    Submodule.finrank_mono hW_le_orth
  have hWV : finrank (ZMod 2) W ≤ finrank (ZMod 2) (Additive (Abelianization Q)) :=
    Submodule.finrank_le W
  have hWV' : finrank (ZMod 2) W ≤ 2 * m := hVfin ▸ hWV
  have hfin_le : finrank (ZMod 2) W ≤ m := by
    rw [hfin_orth, hVfin] at hle_orth
    have h2 := (Nat.le_sub_iff_add_le hWV').1 hle_orth
    omega
  have hker_le : Nat.card φ.ker ≤ 2 := by
    have hmem : ∀ y : φ.ker, Additive.toMul y.1.1 ∈ Subgroup.center Q := by
      intro y
      have h2 := y.2
      change piAddHom Q (y.1.1) = 0 at h2
      rw [show y.1.1 = Additive.ofMul (Additive.toMul y.1.1) from
        (ofMul_toMul y.1.1).symm] at h2
      rw [piAddHom_apply] at h2
      exact (ofMul_of_eq_zero_iff hE (Additive.toMul y.1.1)).1 h2
    have hinj : Function.Injective
        (fun y : φ.ker => (⟨Additive.toMul y.1.1, hmem y⟩ : Subgroup.center Q)) := by
      intro y z hyz
      have h1 : Additive.toMul y.1.1 = Additive.toMul z.1.1 := by
        simpa using congrArg Subtype.val hyz
      exact Subtype.ext (Subtype.ext (Additive.toMul.injective h1))
    calc Nat.card φ.ker ≤ Nat.card (Subgroup.center Q) :=
          Nat.card_le_card_of_injective _ hinj
      _ = 2 := hE.2.2.2
  have hcard_ker : Nat.card φ.ker * Nat.card Etilde = 2 ^ (m + 1) := by
    have h1 := AddSubgroup.card_ker_mul_card_range φ
    rw [hS] at h1
    exact h1
  have hker_pos : 0 < Nat.card φ.ker := by
    haveI : Nonempty φ.ker := ⟨⟨0, φ.ker.zero_mem⟩⟩
    exact Nat.card_pos
  have hm_le : m ≤ finrank (ZMod 2) W := by
    have hcardW : Nat.card Etilde = 2 ^ finrank (ZMod 2) W := by
      haveI : Module.Finite (ZMod 2) W := Module.Finite.of_finite
      have h := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := W)
      rw [Nat.card_zmod] at h
      exact h
    have hpow : 2 ^ (m + 1) = 2 ^ m * 2 := by rw [pow_succ]
    have hcard_ker' : Nat.card Etilde * Nat.card φ.ker = 2 ^ m * 2 := by
      have h := hcard_ker
      rw [mul_comm] at h
      rwa [hpow] at h
    have hbound : 2 ^ m * Nat.card φ.ker ≤ Nat.card Etilde * Nat.card φ.ker := by
      rw [hcard_ker']
      exact Nat.mul_le_mul_left (2 ^ m) hker_le
    have hlow : 2 ^ m ≤ Nat.card Etilde := Nat.le_of_mul_le_mul_right hbound hker_pos
    have hlow' : 2 ^ m ≤ 2 ^ finrank (ZMod 2) W := hcardW ▸ hlow
    exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).1 hlow'
  have hWfin : finrank (ZMod 2) W = m := le_antisymm hfin_le hm_le
  refine ⟨W, ?_, hW_sing⟩
  rw [hWfin, hVfin]

end CFSG.EvenSporadicStandard.HNRecog
