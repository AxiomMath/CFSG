module

public import CFSG.RankThree.Literature.FSmithForm
public import CFSG.GroupTheory.ExtraspecialCentralizerInnerAut
public import CFSG.GroupTheory.Extraspecial2PG

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GroupTheory

open Subgroup Module QuadraticMap CFSG.RankThree.Literature.FSmith CFSG.Open
open CFSG.LargeExtraspecial.Timmesfeld (IsExtraspecial2)

variable {G : Type} [Group G] [Finite G]

private def piAddHom (Q : Type*) [Group Q] : Additive Q →+ Additive (Abelianization Q) :=
  MonoidHom.toAdditive (Abelianization.of : Q →* Abelianization Q)

private theorem piAddHom_apply (Q : Type*) [Group Q] (x : Q) :
    piAddHom Q (Additive.ofMul x) = Additive.ofMul (Abelianization.of x) := rfl

private theorem natCard_toAddSubgroup {H : Type*} [Group H] (S : Subgroup H) :
    Nat.card (S.toAddSubgroup) = Nat.card S :=
  Nat.card_congr
    { toFun := fun x => ⟨Additive.toMul x.1, (Additive.mem_toAddSubgroup S x.1).1 x.2⟩
      invFun := fun x => ⟨Additive.ofMul x.1,
        (Additive.mem_toAddSubgroup S (Additive.ofMul x.1)).2 (by simp)⟩
      left_inv := by intro x; ext; simp
      right_inv := by intro x; ext; simp }

theorem card_le_two_pow_succ_of_isElemAbelian {J : Subgroup G} (hJ : IsExtraspecial2 J) {n : ℕ}
    (hcard : Nat.card J = 2 ^ (2 * n + 1)) {U : Subgroup G} (hUJ : U ≤ J)
    (hU : IsElemAbelian 2 U) : Nat.card U ≤ 2 ^ (n + 1) := by
  have hE : IsExtraspecialPGroup 2 J := CFSG.IsExtraspecial2.toIsExtraspecialPGroup hJ
  let _inst : Module (ZMod 2) (Additive (Abelianization J)) := extraspecialQuotientModule hE
  have hfin : Finite (Additive (Abelianization J)) := by
    change Finite (J ⧸ _root_.commutator J)
    infer_instance
  have : Module.Finite (ZMod 2) (Additive (Abelianization J)) := Module.Finite.of_finite
  have hVcard : Nat.card (Additive (Abelianization J)) = 2 ^ (2 * n) := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (_root_.commutator J)
    rw [hE.2.1, hE.2.2.2, hcard] at h1
    change Nat.card (J ⧸ _root_.commutator J) = 2 ^ (2 * n)
    rw [hE.2.1]
    have h2 : 2 ^ (2 * n + 1) = 2 ^ (2 * n) * 2 := by rw [pow_succ]
    exact Nat.eq_of_mul_eq_mul_right (by norm_num : 0 < 2) (h1.symm.trans h2)
  have hVfin : finrank (ZMod 2) (Additive (Abelianization J)) = 2 * n := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod] at hVcard
    exact Nat.pow_right_injective le_rfl hVcard
  let U' : Subgroup J := U.subgroupOf J
  let S : AddSubgroup (Additive J) := Subgroup.toAddSubgroup U'
  let φ : S →+ Additive (Abelianization J) := (piAddHom J).comp S.subtype
  let Etilde : AddSubgroup (Additive (Abelianization J)) := φ.range
  let W : Submodule (ZMod 2) (Additive (Abelianization J)) :=
    AddSubgroup.toZModSubmodule (n := 2) Etilde
  have hU'card : Nat.card U' = Nat.card U :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUJ).toEquiv
  have hS : Nat.card S = Nat.card U := by
    rw [show S = Subgroup.toAddSubgroup U' from rfl, natCard_toAddSubgroup, hU'card]
  have hW_sing : ∀ x ∈ W, extraspecialQuadForm hE x = 0 := by
    intro x hx
    rw [AddSubgroup.mem_toZModSubmodule] at hx
    change x ∈ φ.range at hx
    obtain ⟨y, rfl⟩ := hx
    change extraspecialQuadForm hE (φ y) = 0
    set q0 : J := Additive.toMul y.1 with hq0def
    have hq0 : (q0 : G) ∈ U := by
      have h' : Additive.toMul y.1 ∈ U' := (Additive.mem_toAddSubgroup U' y.1).1 y.2
      simpa [hq0def, U', Subgroup.mem_subgroupOf] using h'
    have hφ : φ y = Additive.ofMul (Abelianization.of q0) := by
      change piAddHom J (y.1) = _
      rw [show y.1 = Additive.ofMul q0 from (ofMul_toMul y.1).symm]
      exact piAddHom_apply J q0
    rw [hφ, extraspecialQuadForm_apply]
    have hq2 : q0 ^ 2 = 1 := Subtype.ext (by simpa using hU.2 (q0 : G) hq0)
    rw [if_pos hq2]
  have hW_le_orth : W ≤
      LinearMap.BilinForm.orthogonal (extraspecialQuadForm hE).polarBilin W := by
    intro x hx
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro y hy
    rw [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar]
    rw [hW_sing (y + x) (W.add_mem hy hx), hW_sing y hy, hW_sing x hx]
    ring
  have hfin_orth : finrank (ZMod 2)
        (LinearMap.BilinForm.orthogonal (extraspecialQuadForm hE).polarBilin W) =
      finrank (ZMod 2) (Additive (Abelianization J)) - finrank (ZMod 2) W :=
    LinearMap.BilinForm.finrank_orthogonal (extraspecialQuadForm_nondegenerate hE) W
  have hle_orth : finrank (ZMod 2) W ≤ finrank (ZMod 2)
      (LinearMap.BilinForm.orthogonal (extraspecialQuadForm hE).polarBilin W) :=
    Submodule.finrank_mono hW_le_orth
  have hWV : finrank (ZMod 2) W ≤ finrank (ZMod 2) (Additive (Abelianization J)) :=
    Submodule.finrank_le W
  have hWV' : finrank (ZMod 2) W ≤ 2 * n := hVfin ▸ hWV
  have hfin_le : finrank (ZMod 2) W ≤ n := by
    rw [hfin_orth, hVfin] at hle_orth
    have h2 := (Nat.le_sub_iff_add_le hWV').1 hle_orth
    omega
  have hker_le : Nat.card φ.ker ≤ 2 := by
    have hmem : ∀ y : φ.ker, Additive.toMul y.1.1 ∈ Subgroup.center J := by
      intro y
      have h2 := y.2
      change piAddHom J (y.1.1) = 0 at h2
      rw [show y.1.1 = Additive.ofMul (Additive.toMul y.1.1) from
        (ofMul_toMul y.1.1).symm] at h2
      rw [piAddHom_apply] at h2
      exact (ofMul_of_eq_zero_iff hE (Additive.toMul y.1.1)).1 h2
    have hinj : Function.Injective
        (fun y : φ.ker => (⟨Additive.toMul y.1.1, hmem y⟩ : Subgroup.center J)) := by
      intro y z hyz
      have h1 : Additive.toMul y.1.1 = Additive.toMul z.1.1 := by
        simpa using congrArg Subtype.val hyz
      exact Subtype.ext (Subtype.ext (Additive.toMul.injective h1))
    calc Nat.card φ.ker ≤ Nat.card (Subgroup.center J) :=
          Nat.card_le_card_of_injective _ hinj
      _ = 2 := hE.2.2.2
  have hcard_ker : Nat.card φ.ker * Nat.card Etilde = Nat.card U := by
    have h1 := AddSubgroup.card_ker_mul_card_range φ
    rw [hS] at h1
    exact h1
  have hcardW : Nat.card Etilde = 2 ^ finrank (ZMod 2) W := by
    have : Module.Finite (ZMod 2) W := Module.Finite.of_finite
    have h := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := W)
    rw [Nat.card_zmod] at h
    exact h
  calc Nat.card U = Nat.card φ.ker * Nat.card Etilde := hcard_ker.symm
    _ ≤ 2 * 2 ^ n := by
      rw [hcardW]
      exact Nat.mul_le_mul hker_le (Nat.pow_le_pow_right (by norm_num) hfin_le)
    _ = 2 ^ (n + 1) := by rw [pow_succ]; ring

end CFSG.GroupTheory
