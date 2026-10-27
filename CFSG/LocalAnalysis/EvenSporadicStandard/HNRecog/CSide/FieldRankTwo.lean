module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Extraspecial.Quotient

@[expose] public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog
open Subgroup Module QuadraticMap CFSG.RankThree.Literature.FSmith
open scoped commutatorElement

namespace FieldRankTwoAux

variable {H : Type} [Group H] {Q : Subgroup H}

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

end FieldRankTwoAux

private theorem two_mul_finrank_le_of_totally_isotropic
    {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    {q : QuadraticForm K V} (hnd : ∀ v, (∀ w, polar q v w = 0) → v = 0)
    (W : Submodule K V) (hW : ∀ x ∈ W, ∀ y ∈ W, polar q x y = 0) :
    2 * finrank K W ≤ finrank K V := by
  have hB : (polarBilin q).Nondegenerate :=
    ⟨fun v hv => hnd v fun w => by simpa using hv w,
      fun w hw => hnd w fun v => by rw [polar_comm]; simpa using hw v⟩
  have horth : W ≤ LinearMap.BilinForm.orthogonal (polarBilin q) W := by
    intro x hx
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro y hy
    exact hW y hy x hx
  have hfin : finrank K (LinearMap.BilinForm.orthogonal (polarBilin q) W) =
      finrank K V - finrank K W :=
    LinearMap.BilinForm.finrank_orthogonal hB W
  have hle : finrank K W ≤ finrank K V - finrank K W := by
    rw [← hfin]
    exact Submodule.finrank_mono horth
  have hWV : finrank K W ≤ finrank K V := Submodule.finrank_le W
  omega

private theorem card_le_pow_succ_of_isPlusExtraspecial {C : Type} [Group C] {Q : Subgroup C}
    {m : ℕ} (hQ : IsPlusExtraspecial m Q) {E : Subgroup C} (hEQ : E ≤ Q)
    (hEab : CFSG.Open.IsElemAbelian 2 E) : Nat.card E ≤ 2 ^ (m + 1) := by
  haveI : Finite Q := hQ.finite
  have hQe : IsExtraspecialPGroup 2 Q := hQ.isExtraspecialPGroup
  letI : Module (ZMod 2) (Additive (Abelianization Q)) :=
    CFSG.GroupTheory.extraspecialQuotientModule hQe
  let E' : Subgroup Q := E.comap Q.subtype
  let S : AddSubgroup (Additive Q) := Subgroup.toAddSubgroup E'
  let φ : S →+ Additive (Abelianization Q) := (FieldRankTwoAux.piAddHom Q).comp S.subtype
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
  have hS : Nat.card S = Nat.card E' := FieldRankTwoAux.natCard_toAddSubgroup E'
  have hE'_comm : ∀ u v : E', (u : Q) * (v : Q) = (v : Q) * (u : Q) := by
    intro u v
    have hu : ((u : Q) : C) ∈ E := Subgroup.mem_comap.mp u.2
    have hv : ((v : Q) : C) ∈ E := Subgroup.mem_comap.mp v.2
    have h := hEab.1.is_comm.comm (⟨((u : Q) : C), hu⟩ : E) (⟨((v : Q) : C), hv⟩ : E)
    apply Subtype.ext
    simpa using congrArg (fun z : E => (z : C)) h
  have hker_le : Nat.card φ.ker ≤ 2 := by
    have hmem : ∀ y : φ.ker, Additive.toMul y.1.1 ∈ Subgroup.center Q := by
      intro y
      have h2 := y.2
      change FieldRankTwoAux.piAddHom Q (y.1.1) = 0 at h2
      rw [show y.1.1 = Additive.ofMul (Additive.toMul y.1.1) from
        (ofMul_toMul y.1.1).symm] at h2
      rw [FieldRankTwoAux.piAddHom_apply] at h2
      exact (ofMul_of_eq_zero_iff hQe (Additive.toMul y.1.1)).1 h2
    have hinj : Function.Injective
        (fun y : φ.ker => (⟨Additive.toMul y.1.1, hmem y⟩ : Subgroup.center Q)) := by
      intro y z hyz
      have h1 : Additive.toMul y.1.1 = Additive.toMul z.1.1 := by
        simpa using congrArg Subtype.val hyz
      exact Subtype.ext (Subtype.ext (Additive.toMul.injective h1))
    calc Nat.card φ.ker ≤ Nat.card (Subgroup.center Q) :=
          Nat.card_le_card_of_injective _ hinj
      _ = 2 := hQe.2.2.2
  have hcard_ker : Nat.card φ.ker * Nat.card Etilde = Nat.card S :=
    AddSubgroup.card_ker_mul_card_range φ
  have hW_iso : ∀ x ∈ W, ∀ y ∈ W, polar (extraspecialQuadForm hQe) x y = 0 := by
    intro x hx y hy
    rw [AddSubgroup.mem_toZModSubmodule] at hx hy
    change x ∈ φ.range at hx
    change y ∈ φ.range at hy
    obtain ⟨a, rfl⟩ := hx
    obtain ⟨b, rfl⟩ := hy
    have hfa : φ a =
        Additive.ofMul (Abelianization.of (Additive.toMul a.1)) := by
      change FieldRankTwoAux.piAddHom Q a.1 = _
      rw [show a.1 = Additive.ofMul (Additive.toMul a.1) from (ofMul_toMul a.1).symm]
      exact FieldRankTwoAux.piAddHom_apply Q _
    have hfb : φ b =
        Additive.ofMul (Abelianization.of (Additive.toMul b.1)) := by
      change FieldRankTwoAux.piAddHom Q b.1 = _
      rw [show b.1 = Additive.ofMul (Additive.toMul b.1) from (ofMul_toMul b.1).symm]
      exact FieldRankTwoAux.piAddHom_apply Q _
    rw [hfa, hfb]
    refine (polar_extraspecialQuadForm_eq_zero_iff hQe _ _).2 ?_
    have ha : Additive.toMul a.1 ∈ E' :=
      (Additive.mem_toAddSubgroup E' a.1).1 a.2
    have hb : Additive.toMul b.1 ∈ E' :=
      (Additive.mem_toAddSubgroup E' b.1).1 b.2
    exact hE'_comm ⟨_, ha⟩ ⟨_, hb⟩
  have hnd : ∀ v, (∀ w, polar (extraspecialQuadForm hQe) v w = 0) → v = 0 := by
    intro v hv
    obtain ⟨x, rfl⟩ := exists_ofMul_of v
    rw [ofMul_of_eq_zero_iff hQe, mem_center_iff]
    intro y
    have h := hv (Additive.ofMul (Abelianization.of y))
    exact ((polar_extraspecialQuadForm_eq_zero_iff hQe x y).1 h).symm
  haveI : Module.Finite (ZMod 2) (Additive (Abelianization Q)) := Module.Finite.of_finite
  have hVfin : finrank (ZMod 2) (Additive (Abelianization Q)) = 2 * m := hQ.finrank_quotient
  have hdim : 2 * finrank (ZMod 2) W ≤ finrank (ZMod 2) (Additive (Abelianization Q)) :=
    two_mul_finrank_le_of_totally_isotropic hnd W hW_iso
  have hWfin : finrank (ZMod 2) W ≤ m := by
    rw [hVfin] at hdim
    omega
  have hcardW : Nat.card Etilde = 2 ^ finrank (ZMod 2) W := by
    have h := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := W)
    rw [Nat.card_zmod] at h
    exact h
  calc Nat.card E = Nat.card E' := hE'card.symm
    _ = Nat.card S := hS.symm
    _ = Nat.card φ.ker * Nat.card Etilde := hcard_ker.symm
    _ ≤ 2 * 2 ^ m := by
        refine Nat.mul_le_mul hker_le ?_
        rw [hcardW]
        exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).2 hWfin
    _ = 2 ^ (m + 1) := by rw [pow_succ]; ring

theorem cSide_card_le_of_elemAbelian {C : Type} [Group C] {Q : Subgroup C}
    (hQ : IsPlusExtraspecial 4 Q) {E : Subgroup C} (hEQ : E ≤ Q)
    (hE : CFSG.Open.IsElemAbelian 2 E) : Nat.card E ≤ 2 ^ 5 := by
  have h := card_le_pow_succ_of_isPlusExtraspecial hQ hEQ hE
  simpa using h

theorem cSideFacts_rank_two : ∀ (C : Type) [Group C] (Q : Subgroup C) [Q.Normal],
    IsExtraspecialPlusByA5WrTwoWith C Q → ∀ E : Subgroup C, E ≤ Q →
      CFSG.Open.IsElemAbelian 2 E → Nat.card E ≤ 2 ^ 5 := by
  intro C _ Q _ hE E hEQ hEab
  exact cSide_card_le_of_elemAbelian hE.plus hEQ hEab

end CFSG.EvenSporadicStandard.HNRecog.Section3
